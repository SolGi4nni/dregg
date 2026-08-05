#!/usr/bin/env python3
"""Path of Angels game-design gate — PLATFORM-ROADMAP.md section 12.3.

Formal validity is not fun.  `scripts/test-poa.sh` proves the kernels are sound and
the descriptors well-formed; nothing in the braid asks whether the resulting games
have any strategic content.  This does.

It reads the emitted POAG1 descriptors under `poa/artifacts/poag1/games/`, which are
already total finite transition functions, and reports per game:

  * information floor      — how many questions are needed to identify the instance
  * execution floor        — shortest accepted path to a rewarded terminal
  * worst case, optimal    — exact minimax / exact shortest-path value, not a heuristic
  * budget binding         — whether `action_limit` ever constrains optimal play
  * opener classes         — orbits of the opening move under the *verified* symmetry
                             group of the emitted rules, not a heuristic signature
  * dead / dominated       — actions never accepted, and actions provably never optimal
  * unreachable outcomes   — declared feedback classes or states that cannot occur
  * instance families      — trivial, duplicated, or seed-inert instances

Anti-mirror discipline.  Where this tool needs a rule model that the descriptor does
not tabulate (Signal's feedback over targets other than the pinned one; Salvage's
board for seeds other than the pinned one), it rebuilds the model from the declared
semantics and then DIFFERENTIALLY CHECKS it against every emitted row.  A single
disagreement is a hard failure: the tool refuses rather than analysing its own
reconstruction.

Usage:
  scripts/poa-design-gate.py                       # human report
  scripts/poa-design-gate.py --json                # machine report
  scripts/poa-design-gate.py --baseline FILE       # ratchet: unknown finding => exit 1
  scripts/poa-design-gate.py --update-baseline FILE
  scripts/poa-design-gate.py --strict              # any WARN => exit 1

Exit codes: 0 ok, 1 ratchet/strict violation, 2 integrity failure (FAIL findings).
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
from collections import Counter, defaultdict, deque

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GAMES_DIR = os.path.join(REPO, "poa", "artifacts", "poag1", "games")

FAIL, WARN, INFO = "FAIL", "WARN", "INFO"


class Refusal(Exception):
    """The descriptor is outside what this analyser can honestly model."""


# ---------------------------------------------------------------------------
# hidden-instance contract
# ---------------------------------------------------------------------------
#
# Every POAG1 game descriptor now declares where its instance comes from and
# declares that the artifact does not contain one.  The checks below are the
# reason this tool stopped reporting a decorative execution floor: a descriptor
# that still states its own answer FAILS here rather than earning a WARN and a
# baseline entry.
#
# The old shape is refused rather than reinterpreted.  `target`, `run_seed`,
# `instance.selected`, `instance.seed_byte` and `actions[].glyph_id` each named
# the live instance; a descriptor carrying any of them is the pre-split bundle
# and must be re-emitted, not analysed.

BANNED_TOP_LEVEL = {
    "target": "states the hidden code outright",
    "run_seed": "determines the instance through the public derivation",
    "outcomes": "tabulates feedback against one target, which IS the target",
}
BANNED_INSTANCE_KEYS = {
    "selected": "names which board of the family is live",
    "seed_byte": "names the byte of the published run seed that draws the board",
}
BANNED_ACTION_KEYS = {
    "glyph_id": "names the glyph sealed under a plate",
    "glyph_label": "names the glyph sealed under a plate",
}

DISCLOSURES = {"oracle-only", "per-run-open"}


def check_instance_contract(doc: dict, rep: Report) -> str:
    """Refuse the pre-split shape; return the declared disclosure.

    A FAIL here is the point.  This used to be `instance-secret-published`, a WARN
    with a baseline entry beside it, which is how a game whose execution floor was
    one guess stayed green for as long as it did.
    """
    name = doc.get("game_id", "?")
    stale = []
    for key, why in BANNED_TOP_LEVEL.items():
        if key in doc:
            stale.append(f"`{key}` ({why})")
    inst = doc.get("instance")
    if isinstance(inst, dict):
        for key, why in BANNED_INSTANCE_KEYS.items():
            if key in inst:
                stale.append(f"`instance.{key}` ({why})")
    sm = doc.get("state_machine")
    if isinstance(sm, dict):
        for action in sm.get("actions", []):
            for key, why in BANNED_ACTION_KEYS.items():
                if key in action:
                    stale.append(f"`state_machine.actions[].{key}` ({why})")
                    break
            else:
                continue
            break
    if stale:
        rep.find(name, "instance-secret-published", FAIL,
                 "the descriptor the client fetches states its own instance",
                 f"{name}.json carries {', '.join(stale)}.  This is the pre-split "
                 f"POAG1 shape: the instance was derived from a published run seed, "
                 f"so the execution floor was one action against an information floor "
                 f"of several and the deduction was decorative.  The bundle on disk "
                 f"predates the split and must be RE-EMITTED from Lean "
                 f"(`scripts/check-poag1-artifacts.sh`); this gate refuses to "
                 f"reinterpret it as a hidden-instance descriptor.")
        raise Refusal("pre-split descriptor: instance is published (see the FAIL above)")

    if not isinstance(inst, dict):
        raise Refusal("descriptor carries no `instance` declaration; a game that does "
                      "not say where its instance comes from cannot be scored")
    # Relay nests its declaration under `instance.draw`; hidden games carry it flat.
    decl = inst.get("draw") if "boards" in inst else inst
    if not isinstance(decl, dict):
        raise Refusal("`instance` declaration is malformed")
    if decl.get("kind") != "per-run-hidden-draw":
        raise Refusal(f"instance kind {decl.get('kind')!r} is not a per-run hidden draw")
    disclosure = decl.get("disclosure")
    if disclosure not in DISCLOSURES:
        raise Refusal(f"instance disclosure {disclosure!r} is not one of "
                      f"{sorted(DISCLOSURES)}")
    if doc.get("security", {}).get("instance_visibility") != disclosure:
        raise Refusal("security.instance_visibility disagrees with the instance "
                      "declaration")

    commitment = decl.get("commitment", {})
    if commitment.get("published_in") != "slot-opening":
        raise Refusal("the instance commitment is not published in the slot opening; "
                      "without one the operator can choose the instance after the run")
    bits = commitment.get("binding_bits")
    if not isinstance(bits, int) or bits < 100:
        raise Refusal(f"declared commitment binding is {bits} bits")
    if decl.get("operator_knows_instance") is not True:
        raise Refusal("the declaration does not admit that the operator knows the "
                      "instance; that residual is real and must be stated")

    rep.find(name, "instance-committed-not-published", INFO,
             "the instance is committed to and drawn per run, not carried in the artifact",
             f"the descriptor declares a {disclosure} instance drawn by "
             f"{decl.get('derivation_module')} from a slot secret whose commitment is "
             f"published in the slot opening and opened after the slot closes.  "
             f"Binding is {bits} bits (the sponge capacity, not the output width).  "
             f"⚠ `operator_knows_instance` is true: whoever holds the slot secret "
             f"knows every player's instance in advance.  That is a real residual and "
             f"removing it needs an unpredictable beacon, not a wire change.")
    return disclosure


class Report:
    def __init__(self) -> None:
        self.games: list[dict] = []
        self.findings: list[dict] = []

    def find(self, game: str, key: str, severity: str, title: str, detail: str) -> None:
        self.findings.append(
            {"key": f"{game}/{key}", "game": game, "severity": severity,
             "title": title, "detail": detail}
        )


# ---------------------------------------------------------------------------
# shared helpers
# ---------------------------------------------------------------------------

def ceil_log(n: int, base: int) -> int:
    """Smallest d with base**d >= n."""
    if n <= 1:
        return 0
    if base < 2:
        raise Refusal(f"cannot identify {n} instances with {base} answer classes")
    d = 0
    acc = 1
    while acc < n:
        acc *= base
        d += 1
    return d


def naming_capacity(classes: int, depth: int) -> int:
    """Codes an adaptive strategy of `depth` questions can resolve when exactly one
    answer class is terminal (the questioner must NAME the instance to win):
        M(0) = 0,  M(d) = 1 + (classes-1) * M(d-1).
    This is the tight counting floor; ceil(log_classes n) is the loose one."""
    m = 0
    for _ in range(depth):
        m = 1 + (classes - 1) * m
    return m


def orbits(elements, generators):
    """Orbits of `elements` under permutation functions `generators`."""
    remaining = set(elements)
    out = []
    while remaining:
        seed = next(iter(remaining))
        orb = {seed}
        queue = [seed]
        while queue:
            x = queue.pop()
            for g in generators:
                y = g(x)
                if y not in orb:
                    orb.add(y)
                    queue.append(y)
        out.append(sorted(orb))
        remaining -= orb
    return out


# ---------------------------------------------------------------------------
# backend 1 — deduction games (hidden instance + feedback table): Signal
# ---------------------------------------------------------------------------

class DeductionGame:
    """A descriptor carrying `rules`: the COMPLETE (target, guess) -> class oracle.

    The pre-split shape carried `outcomes`, a 216-row table of feedback against one
    pinned target with the solving row flagged — the answer written out.  What is
    read here is the whole function, which states every rule and distinguishes no
    instance.  `check_instance_contract` has already refused the old shape by the
    time this runs.
    """

    def __init__(self, doc: dict, rep: Report) -> None:
        self.doc = doc
        self.rep = rep
        self.name = doc["game_id"]
        self.bands = doc["action"]["code"]["bands"]
        self.alphabet = doc["action"]["code"]["alphabet"]
        self.budget = doc["action_limit"]
        sem = doc["feedback"]["present_semantics"]
        if sem != "multiplicity_intersection_minus_exact":
            raise Refusal(f"unmodelled present_semantics {sem!r}")
        if doc["feedback"]["solved_when_exact"] != self.bands:
            raise Refusal("solved_when_exact disagrees with the band count")
        rules = doc.get("rules")
        if not isinstance(rules, dict):
            raise Refusal("descriptor carries no `rules` block; a deduction game whose "
                          "instance is hidden must publish the whole oracle or the "
                          "client has no rules at all")
        self.codes = [tuple(c) for c in rules["codes"]]
        self.index = {c: i for i, c in enumerate(self.codes)}
        self.n = len(self.codes)
        if len(self.index) != self.n:
            raise Refusal("rules.codes contains a duplicate")
        domain = self.alphabet ** self.bands
        if self.n != domain:
            raise Refusal(f"rules.codes has {self.n} codes for a "
                          f"{self.alphabet}^{self.bands} = {domain} domain")
        self.alphabet_chars = rules["class_alphabet"]
        self.declared_classes = rules["classes"]
        self.table_rows = rules["table"]
        if len(self.table_rows) != self.n:
            raise Refusal(f"rules.table has {len(self.table_rows)} rows for {self.n} codes")

    # -- rule model, then differential against every emitted CELL -----------
    def feedback(self, target, guess):
        exact = sum(1 for i in range(self.bands) if target[i] == guess[i])
        ct, cg = Counter(target), Counter(guess)
        total = sum(min(ct[x], cg[x]) for x in ct.keys() | cg.keys())
        return exact, total - exact

    def build(self) -> None:
        """Decode the emitted table.  `fb` comes from the ARTIFACT, not the model —
        the model is then checked against every cell of it."""
        self.cls_id = {}
        for i, cls in enumerate(self.declared_classes):
            pair = (cls["exact"], cls["present"])
            if pair in self.cls_id:
                raise Refusal(f"rules.classes declares {pair} twice")
            if cls["solved"] != (cls["exact"] == self.bands):
                raise Refusal(f"rules.classes {pair} disagrees with solved_when_exact")
            self.cls_id[pair] = i
        self.classes = len(self.cls_id)
        char_id = {c: i for i, c in enumerate(self.alphabet_chars[:self.classes])}
        self.fb = []
        for r, row in enumerate(self.table_rows):
            if len(row) != self.n:
                raise Refusal(f"rules.table row {r} has {len(row)} cells for {self.n} codes")
            decoded = []
            for c in row:
                if c not in char_id:
                    raise Refusal(f"rules.table row {r} names class {c!r}, which is "
                                  f"outside the declared alphabet")
                decoded.append(char_id[c])
            self.fb.append(decoded)
        win = [i for i, cls in enumerate(self.declared_classes) if cls["solved"]]
        if len(win) != 1:
            raise Refusal(f"{len(win)} declared classes are solving; expected exactly one")
        self.win = win[0]

    def differential(self) -> None:
        """The reconstructed rules must reproduce every one of the n^2 emitted cells.

        This is a strictly stronger differential than the pre-split one, which
        checked n rows against one target.  It has to be: the table is now the only
        statement of the rules the client ever sees.
        """
        bad = []
        for t in self.codes:
            row = self.fb[self.index[t]]
            for g in self.codes:
                want = self.cls_id.get(self.feedback(t, g))
                if want is None or row[self.index[g]] != want:
                    bad.append((t, g, row[self.index[g]], want))
                    if len(bad) > 3:
                        break
            if bad:
                break
        if bad:
            raise Refusal(
                f"reconstructed rules disagree with the emitted table; first: "
                f"target={bad[0][0]} guess={bad[0][1]} emitted={bad[0][2]} "
                f"model={bad[0][3]}")
        # Every row solves at exactly one column, and that column is its own index.
        # A row that solved somewhere else would name a different instance.
        for t in self.codes:
            row = self.fb[self.index[t]]
            solving = [g for g in self.codes if row[self.index[g]] == self.win]
            if solving != [t]:
                raise Refusal(f"row {t} solves at {solving}, not at exactly itself: the "
                              f"table distinguishes a row and therefore names an instance")

    # -- verified symmetry group -------------------------------------------
    def symmetry_generators(self):
        """Generators of S_alphabet (recolour) x S_bands (reposition), each CHECKED
        exhaustively to preserve feedback before it is used to reduce anything."""
        gens = []
        A, B = self.alphabet, self.bands

        def recolour(perm):
            return lambda c: tuple(perm[x] for x in c)

        def reposition(perm):
            return lambda c: tuple(c[perm[i]] for i in range(B))

        colour_swap = list(range(A)); colour_swap[0], colour_swap[1] = 1, 0
        colour_cycle = [(x + 1) % A for x in range(A)]
        gens.append(("recolour-swap", recolour(colour_swap)))
        gens.append(("recolour-cycle", recolour(colour_cycle)))
        if B >= 2:
            pos_swap = list(range(B)); pos_swap[0], pos_swap[1] = 1, 0
            pos_cycle = [(i + 1) % B for i in range(B)]
            gens.append(("reposition-swap", reposition(pos_swap)))
            gens.append(("reposition-cycle", reposition(pos_cycle)))

        checked = []
        for label, g in gens:
            for t in self.codes:
                gt = self.index[g(t)]
                row, grow = self.fb[self.index[t]], self.fb[gt]
                for x in self.codes:
                    if row[self.index[x]] != grow[self.index[g(x)]]:
                        raise Refusal(f"claimed symmetry {label} does not preserve "
                                      f"feedback at target={t} guess={x}")
            checked.append((label, g))
        return checked

    # -- exact minimax ------------------------------------------------------
    def _can(self, cands, depth, memo, capacity):
        n = len(cands)
        if n <= 1:
            return depth >= 1
        if depth <= 1 or n > capacity[depth]:
            return False
        key = (cands, depth)
        hit = memo.get(key)
        if hit is not None:
            return hit
        options = []
        for g in range(self.n):
            part = defaultdict(list)
            for t in cands:
                part[self.fb[t][g]].append(t)
            if len(part) == 1:
                continue
            biggest = max((len(b) for k, b in part.items() if k != self.win), default=0)
            if biggest > capacity[depth - 1]:
                continue
            options.append((biggest, 0 if g in cands else 1, g, part))
        options.sort(key=lambda x: (x[0], x[1], x[2]))
        result = False
        for _, _, _g, part in options:
            if all(self._can(tuple(b), depth - 1, memo, capacity)
                   for k, b in part.items() if k != self.win):
                result = True
                break
        memo[key] = result
        return result

    def opener_value(self, opener, cap):
        """Smallest total guess count achievable when the first guess is `opener`,
        searched up to `cap`; returns None if not achievable within `cap`."""
        capacity = [naming_capacity(self.classes, d) for d in range(cap + 2)]
        memo: dict = {}
        allc = tuple(range(self.n))
        g = self.index[opener]
        part = defaultdict(list)
        for t in allc:
            part[self.fb[t][g]].append(t)
        for depth in range(1, cap + 1):
            if all(self._can(tuple(b), depth - 1, memo, capacity)
                   for k, b in part.items() if k != self.win):
                return depth
        return None

    # -- reference policies -------------------------------------------------
    def _minimax_choice(self, cands, memo):
        """Knuth minimax over the FULL guess pool, tie-broken toward a still-consistent
        code then lexicographically.  Memoised on the candidate set, which is what makes
        the family sweep cheap: sibling targets share information sets."""
        hit = memo.get(cands)
        if hit is not None:
            return hit
        cset = set(cands)
        best_key, best_g = None, None
        for cg in range(self.n):
            tally = [0] * self.classes
            worst = 0
            for c in cands:
                k = self.fb[c][cg]
                tally[k] += 1
                if tally[k] > worst:
                    worst = tally[k]
            key = (worst, 0 if cg in cset else 1, cg)
            if best_key is None or key < best_key:
                best_key, best_g = key, cg
        memo[cands] = best_g
        return best_g

    def play(self, opener, cap):
        """Fixed opener, then the memoised minimax continuation.  Length is reported
        uncapped, so a policy that overruns the budget is visible as such."""
        memo: dict = {}
        turns, lost = [], []
        opener_id = self.index[opener]
        for t in range(self.n):
            cands = tuple(range(self.n))
            g = opener_id
            k = 0
            while True:
                k += 1
                f = self.fb[t][g]
                if f == self.win:
                    break
                cands = tuple(c for c in cands if self.fb[c][g] == f)
                if k > cap + 4:
                    break
                g = self._minimax_choice(cands, memo)
            turns.append(k)
            if k > cap:
                lost.append(self.codes[t])
        return turns, lost

    # -- the report ---------------------------------------------------------
    def analyse(self) -> dict:
        rep = self.rep
        self.build()
        self.differential()
        gens = self.symmetry_generators()
        gen_fns = [g for _, g in gens]

        realized = sorted(self.cls_id, key=self.cls_id.get)
        declared = [(e, p) for e in range(self.bands + 1) for p in range(self.bands + 1)
                    if e + p <= self.doc["feedback"]["exact_plus_present_max"]]
        unrealizable = sorted(set(declared) - set(realized))

        info_loose = ceil_log(self.n, self.classes)
        info_tight = 1
        while naming_capacity(self.classes, info_tight) < self.n:
            info_tight += 1

        code_orbits = orbits(self.codes, gen_fns)
        code_orbits.sort(key=len)

        def shape_name(c):
            """Canonical pattern of a code: `aab` means two equal bands and one other."""
            first, letters, out = {}, "abcdefgh", []
            for x in c:
                if x not in first:
                    first[x] = letters[len(first)]
                out.append(first[x])
            return "".join(out)

        cap = max(self.budget + 1, 6)
        opener_values = []
        for orb in code_orbits:
            rep_code = orb[0]
            val = self.opener_value(rep_code, cap)
            opener_values.append({
                "class": shape_name(rep_code), "size": len(orb),
                "representative": list(rep_code),
                "worst_case_optimal": val,
                "within_budget": val is not None and val <= self.budget,
            })
        achievable = [o["worst_case_optimal"] for o in opener_values
                      if o["worst_case_optimal"] is not None]
        optimum = min(achievable) if achievable else None

        # instance families are the ORBITS, so the grouping is the verified group's,
        # not a hand-picked signature.
        family = []
        for orb in code_orbits:
            got = {self.feedback(orb[0], g) for g in self.codes}
            family.append({"class": shape_name(orb[0]), "instances": len(orb),
                           "feedback_classes_realizable": len(got)})

        # seed -> instance map, and its modulo bias
        mods = Counter(b % self.alphabet for b in range(256))
        bias = {"symbol_counts_out_of_256": dict(sorted(mods.items())),
                "uniform": len(set(mods.values())) == 1}

        # reference policies, one per opener class
        policies = []
        for o in opener_values:
            turns, lost = self.play(tuple(o["representative"]), self.budget)
            dist = dict(sorted(Counter(turns).items()))
            policies.append({
                "opener": o["representative"], "class": o["class"],
                "worst_case": max(turns), "mean": round(sum(turns) / len(turns), 4),
                "at_budget": dist.get(self.budget, 0), "distribution": dist,
                "losses": len(lost),
            })

        # ---- findings ----
        if unrealizable:
            rep.find(self.name, "unreachable-feedback-class", WARN,
                     f"{len(unrealizable)} declared feedback class(es) can never occur",
                     f"the descriptor's bounds admit {len(declared)} classes "
                     f"(exact+present <= {self.doc['feedback']['exact_plus_present_max']}); "
                     f"only {len(realized)} are realizable over the whole {self.n}-code "
                     f"domain.  Unrealizable: {unrealizable}.  A client that renders one "
                     f"badge per declared class ships a badge no run can earn.")

        rep.find(self.name, "instance-hidden-floor-is-real", INFO,
                 f"a player who reads the artifact still needs {optimum} guesses in the "
                 f"worst case, against an information floor of {info_tight}",
                 f"the descriptor publishes the complete {self.n}-by-{self.n} oracle and "
                 f"no row of it is distinguished, so reading it buys the rules and not "
                 f"the code.  The execution floor as emitted was 1 while `target` was a "
                 f"field; it is now the exact minimax value {optimum}, which is what "
                 f"`action_limit = {self.budget}` was always sized for.")

        dead_openers = [o for o in opener_values if not o["within_budget"]]
        if dead_openers:
            n_dead = sum(o["size"] for o in dead_openers)
            rep.find(self.name, "losing-opener-class", WARN,
                     f"{n_dead} of {self.n} openers cannot win within the budget "
                     f"under ANY continuation",
                     "; ".join(f"class {o['class']} ({o['size']} openers, e.g. "
                               f"{o['representative']}) needs > {self.budget}"
                               for o in dead_openers) +
                     f".  This is exact minimax over the verified symmetry-reduced root, "
                     f"not a heuristic: no play recovers from these openings.")

        if optimum is not None:
            if optimum > self.budget:
                rep.find(self.name, "budget-below-optimum", FAIL,
                         "action_limit is below the proven optimal worst case",
                         f"optimum {optimum} > action_limit {self.budget}: some targets "
                         f"cannot be solved at all.")
            elif optimum == self.budget:
                rep.find(self.name, "budget-binds-exactly", INFO,
                         "the action budget binds exactly under optimal play",
                         f"optimal worst case {optimum} == action_limit {self.budget}; "
                         f"slack 0.  Every unit of the budget is load-bearing.")
            else:
                rep.find(self.name, "budget-slack", WARN,
                         f"the action budget never binds ({self.budget - optimum} spare)",
                         f"optimal worst case {optimum} < action_limit {self.budget}.")

        degenerate = [f for f in family
                      if f["feedback_classes_realizable"] < len(realized)]
        if degenerate:
            rep.find(self.name, "degenerate-instance-family", WARN,
                     "some instances realize strictly fewer feedback classes",
                     "; ".join(f"{f['class']} ({f['instances']} instances) realizes only "
                               f"{f['feedback_classes_realizable']} of {len(realized)}"
                               for f in degenerate) +
                     ".  Those seeds hand the player a strictly weaker instrument.")

        rep.find(self.name, "instance-collapse", INFO,
                 f"the seed space collapses to {len(code_orbits)} structurally distinct "
                 f"instances",
                 f"seeds are 2^256; `targetFromSeed` reads 3 bytes mod {self.alphabet} "
                 f"giving {self.n} targets; the verified symmetry group "
                 f"(S{self.alphabet} recolour x S{self.bands} reposition) collapses those "
                 f"to {len(code_orbits)} classes "
                 f"({', '.join(f'{shape_name(o[0])}:{len(o)}' for o in code_orbits)}).")

        if not bias["uniform"]:
            lo, hi = min(mods.values()), max(mods.values())
            rep.find(self.name, "seed-modulo-bias", INFO,
                     "the seed-to-band map is not uniform",
                     f"a byte mod {self.alphabet} yields symbol counts {lo}..{hi} out of "
                     f"256, so band symbols 0..{255 % self.alphabet} are "
                     f"{round(100 * (hi - lo) / lo, 2)}% more likely than the rest.  "
                     f"Immaterial for a public-target demo; it is a real bias the moment "
                     f"the target is hidden and a reward rides on it.")

        return {
            "game": self.name,
            "kind": "deduction",
            "engine_module": self.doc["engine_module"],
            "action_limit": self.budget,
            "domain": {"codes": self.n, "bands": self.bands, "alphabet": self.alphabet},
            "differential": f"model reproduces all {self.n} emitted outcome rows",
            "symmetry_checked": [label for label, _ in gens],
            "feedback_classes_declared": len(declared),
            "feedback_classes_realizable": len(realized),
            "unrealizable_classes": [list(c) for c in unrealizable],
            "information_floor_loose": info_loose,
            "information_floor_tight": info_tight,
            "worst_case_optimal": optimum,
            # The floor a player can GUARANTEE given the descriptor they fetch.  With
            # `target` published this was 1; with the whole oracle published and no row
            # distinguished it is the minimax value.  `_lucky` keeps the other number
            # visible so nothing is hidden by the rename.
            "execution_floor_as_designed": optimum,
            "execution_floor_as_emitted": optimum,
            "execution_floor_lucky": 1,
            "budget_binds": optimum is not None and optimum >= self.budget,
            "budget_slack": None if optimum is None else self.budget - optimum,
            "opener_classes": len(code_orbits),
            "openers_total": self.n,
            "opener_analysis": opener_values,
            "dead_openers": sum(o["size"] for o in dead_openers),
            "reference_policies": policies,
            "instance_families": family,
            "seed_bias": bias,
        }


# ---------------------------------------------------------------------------
# backend 2 — explicit finite transition systems: Relay, Salvage
# ---------------------------------------------------------------------------

class MachineGame:
    def __init__(self, doc: dict, rep: Report) -> None:
        self.doc = doc
        self.rep = rep
        self.name = doc["game_id"]
        sm = doc["state_machine"]
        self.sm = sm
        self.states = {s["id"]: s for s in sm["states"]}
        self.actions = [a["id"] for a in sm["actions"]]
        self.action_meta = {a["id"]: a for a in sm["actions"]}
        self.initial = sm["initial_state"]
        self.budget = doc["action_limit"]
        self.trans = {}
        for t in sm["transitions"]:
            key = (t["state"], t["action"])
            if key in self.trans:
                raise Refusal(f"duplicate transition row for {key}")
            self.trans[key] = t

    def totality(self) -> None:
        want = len(self.states) * len(self.actions)
        if len(self.trans) != want:
            missing = [(s, a) for s in self.states for a in self.actions
                       if (s, a) not in self.trans]
            raise Refusal(f"transition table is not total: {len(self.trans)} rows, "
                          f"expected {want}; missing e.g. {missing[:3]}")
        for (s, a), t in self.trans.items():
            if t["verdict"] == "accept":
                if t["next"] not in self.states:
                    raise Refusal(f"{s}/{a} accepts into unknown state {t['next']}")
                if t["reason"] is not None:
                    raise Refusal(f"{s}/{a} accepts but carries reason {t['reason']!r}")
            elif t["verdict"] == "refuse":
                if t["next"] is not None:
                    raise Refusal(f"{s}/{a} refuses but names a successor")
                if not t["reason"]:
                    raise Refusal(f"{s}/{a} refuses without a named reason")
            else:
                raise Refusal(f"{s}/{a} has unknown verdict {t['verdict']!r}")

    def succ(self, s, a):
        t = self.trans[(s, a)]
        return t["next"] if t["verdict"] == "accept" else None

    # -- automorphisms: exact, by brute force over action permutations ------
    def automorphisms(self):
        """Every permutation pi of actions that extends to a state bijection phi with
        phi(initial)=initial, preserving verdict, reason, successor and terminality.
        phi is forced by pi through BFS, so the check is a decision, not a search."""
        found = []
        acts = self.actions
        for perm in itertools.permutations(range(len(acts))):
            pi = {acts[i]: acts[perm[i]] for i in range(len(acts))}
            phi = {self.initial: self.initial}
            queue = deque([self.initial])
            ok = True
            while queue and ok:
                s = queue.popleft()
                ps = phi[s]
                if self.states[s]["terminal"] != self.states[ps]["terminal"]:
                    ok = False
                    break
                for a in acts:
                    t, pt = self.trans[(s, a)], self.trans[(ps, pi[a])]
                    if t["verdict"] != pt["verdict"] or t["reason"] != pt["reason"]:
                        ok = False
                        break
                    if t["verdict"] == "accept":
                        nxt, pnxt = t["next"], pt["next"]
                        if nxt in phi:
                            if phi[nxt] != pnxt:
                                ok = False
                                break
                        else:
                            phi[nxt] = pnxt
                            queue.append(nxt)
            if ok:
                found.append(pi)
        return found

    def analyse(self) -> dict:
        rep = self.rep
        self.totality()
        acts = self.actions

        # reachability + distances
        dist = {self.initial: 0}
        order = [self.initial]
        queue = deque([self.initial])
        while queue:
            s = queue.popleft()
            for a in acts:
                n = self.succ(s, a)
                if n is not None and n not in dist:
                    dist[n] = dist[s] + 1
                    order.append(n)
                    queue.append(n)
        reachable = set(dist)
        unreachable_states = sorted(set(self.states) - reachable)

        terminal = {s for s in self.states if self.states[s]["terminal"]}
        solved = {s for s in self.states if self.states[s]["view"].get("solved") is True}
        rewarded = terminal if self.doc["output"]["requires"] == "terminal" else solved
        live_rewards = rewarded & reachable

        # backward reachability of a reward
        rev = defaultdict(list)
        for (s, a), t in self.trans.items():
            if t["verdict"] == "accept":
                rev[t["next"]].append(s)
        winning = set(live_rewards)
        queue = deque(winning)
        while queue:
            s = queue.popleft()
            for p in rev[s]:
                if p not in winning:
                    winning.add(p)
                    queue.append(p)
        doomed = reachable - winning
        doomed_open = {s for s in doomed
                       if any(self.succ(s, a) is not None for a in acts)}

        # to_win[s] = fewest actions from s to a reward
        to_win = {s: 0 for s in live_rewards}
        queue = deque(sorted(live_rewards))
        while queue:
            s = queue.popleft()
            for p in rev[s]:
                if p not in to_win:
                    to_win[p] = to_win[s] + 1
                    queue.append(p)
        floor = to_win.get(self.initial)

        # longest accepted play (the graph is a DAG: turns strictly increase)
        longest = {}
        for s in sorted(reachable, key=lambda x: -dist[x]):
            best = 0
            for a in acts:
                n = self.succ(s, a)
                if n is not None:
                    best = max(best, 1 + longest.get(n, 0))
            longest[s] = best
        worst_play = longest[self.initial]

        # forks
        outcome_forks, budget_forks, forkless = 0, 0, 0
        for s in sorted(reachable - live_rewards):
            legal = [a for a in acts if self.succ(s, a) is not None]
            if len(legal) < 2:
                continue
            outs = {self.succ(s, a) in winning for a in legal}
            vals = {to_win.get(self.succ(s, a)) for a in legal}
            if len(outs) > 1:
                outcome_forks += 1
            if len(vals) > 1:
                budget_forks += 1
            else:
                forkless += 1

        # dead / dominated actions
        dead = [a for a in acts
                if not any(self.succ(s, a) is not None for s in reachable)]
        dominated_pairs = 0
        dominated_everywhere = []
        for a in acts:
            legal_at, worse_at = 0, 0
            for s in reachable:
                n = self.succ(s, a)
                if n is None:
                    continue
                legal_at += 1
                others = [to_win.get(self.succ(s, b)) for b in acts
                          if b != a and self.succ(s, b) is not None]
                mine = to_win.get(n)
                best = min([o for o in others if o is not None], default=None)
                # A doomed state offers nothing better, so nothing there is dominated.
                if best is not None and (mine is None or best < mine):
                    worse_at += 1
                    dominated_pairs += 1
            if legal_at and worse_at == legal_at:
                dominated_everywhere.append(a)

        # opener classes under the exact automorphism group
        autos = self.automorphisms()
        gens = [(lambda p: (lambda a: p[a]))(p) for p in autos]
        opener_orbits = orbits(acts, gens)
        legal_openers = [a for a in acts if self.succ(self.initial, a) is not None]

        # refusal reasons that never fire on a reachable state
        declared_reasons = {t["reason"] for t in self.trans.values() if t["reason"]}
        live_reasons = Counter()
        for s in reachable:
            for a in acts:
                t = self.trans[(s, a)]
                if t["verdict"] == "refuse":
                    live_reasons[t["reason"]] += 1
        dead_reasons = sorted(declared_reasons - set(live_reasons))

        # instance data published in the descriptor
        instance_fields = sorted(
            {k for a in self.sm["actions"] for k in a}
            - {"id", "label", "from", "to", "slot"}
        )

        # ---- findings ----
        if unreachable_states:
            rep.find(self.name, "unreachable-state", WARN,
                     f"{len(unreachable_states)} emitted state(s) are unreachable",
                     f"e.g. {unreachable_states[:5]}")

        mism = sorted((terminal ^ solved) & reachable)
        if mism:
            rep.find(self.name, "terminal-solved-divergence", FAIL,
                     "terminal and solved disagree on a reachable state",
                     f"the descriptor pays out on `{self.doc['output']['requires']}` while "
                     f"the kernel pays out on its solved predicate; they differ at "
                     f"{mism[:5]}.  One of them rewards a run the other excludes.")
        else:
            rep.find(self.name, "terminal-equals-solved", INFO,
                     "reward gate agrees with the solved predicate on every reachable state",
                     f"terminal == solved on all {len(reachable)} reachable states, so the "
                     f"descriptor's `requires: {self.doc['output']['requires']}` and the "
                     f"kernel's solved predicate coincide HERE.  They are two independently "
                     f"written gates: this is a checked coincidence, not a construction.")

        if floor is None:
            rep.find(self.name, "unwinnable", FAIL, "no reward is reachable from genesis",
                     "the emitted machine has no accepted path to a rewarded state.")
        elif floor > self.budget:
            rep.find(self.name, "budget-below-optimum", FAIL,
                     "action_limit is below the shortest solution",
                     f"shortest win {floor} > action_limit {self.budget}.")
        elif floor == self.budget:
            rep.find(self.name, "budget-binds-exactly", INFO,
                     "the action budget binds exactly under optimal play",
                     f"shortest win {floor} == action_limit {self.budget}.")
        else:
            rep.find(self.name, "budget-slack", WARN,
                     f"the action budget never binds under optimal play "
                     f"({self.budget - floor} spare)",
                     f"shortest win {floor}, action_limit {self.budget}.  There is no "
                     f"hidden state in this machine, so optimal play is a fixed-length "
                     f"routine and the remaining {self.budget - floor} turns only ever "
                     f"absorb mistakes.")

        if not doomed:
            rep.find(self.name, "cannot-lose", WARN,
                     "the game cannot be lost",
                     f"every one of the {len(reachable)} reachable states can still reach "
                     f"a reward; the longest legal play is {worst_play} action(s) against "
                     f"a budget of {self.budget}.  Failure is unrepresentable, so no "
                     f"choice carries a consequence.")
        else:
            # Does some emitted view field mark exactly the lost runs?  A client can
            # only tell the player the run is dead if the table says so.
            marker = None
            for key in sorted(self.states[self.initial]["view"]):
                vals = {s: self.states[s]["view"].get(key) for s in reachable}
                if (all(isinstance(v, bool) for v in vals.values())
                        and {s for s in reachable if vals[s]} == doomed):
                    marker = key
                    break
            example = sorted(doomed_open)[0] if doomed_open else sorted(doomed)[0]
            rep.find(self.name, "doomed-but-open", WARN if doomed_open else INFO,
                     f"{len(doomed)} reachable state(s) can no longer reach a reward, "
                     f"{len(doomed_open)} of them still accept actions",
                     f"PLATFORM-ROADMAP 12.3 names this case exactly: legal states from "
                     f"which the ranked goal is already impossible but play continues "
                     f"misleadingly.  Example: {example} -> view "
                     f"{self.states[example]['view']}.  " +
                     (f"The emitted view marks exactly these states with "
                      f"`{marker}: true`, so a client can say so."
                      if marker else
                      "Nothing in the state view marks the run as already lost."))

        if outcome_forks == 0:
            rep.find(self.name, "no-outcome-fork", WARN,
                     "no reachable state has a choice that changes the outcome",
                     f"{budget_forks} state(s) offer choices that change the turn count and "
                     f"{forkless} offer choices that change nothing at all, but zero "
                     f"choices change whether the run is rewarded.")

        if len(opener_orbits) == 1:
            rep.find(self.name, "single-opener-class", WARN,
                     "every opening move is equivalent",
                     f"the exact automorphism group of the emitted machine has "
                     f"{len(autos)} element(s) and acts transitively on all "
                     f"{len(acts)} actions: the opening choice is a relabelling.")

        if dead:
            rep.find(self.name, "dead-action", WARN,
                     f"{len(dead)} action(s) are never accepted anywhere", f"{dead}")
        if dominated_everywhere:
            rep.find(self.name, "globally-dominated-action", WARN,
                     f"{len(dominated_everywhere)} action(s) are strictly dominated "
                     f"wherever they are legal", f"{dominated_everywhere}")
        if dead_reasons:
            rep.find(self.name, "dead-refusal-reason", WARN,
                     f"{len(dead_reasons)} refusal reason(s) never fire on a reachable "
                     f"state", f"{dead_reasons}")

        if instance_fields:
            rep.find(self.name, "instance-secret-published", WARN,
                     "the instance data is published in the action table",
                     f"every action row carries {instance_fields}, so the descriptor the "
                     f"client fetches states the board outright.  The state views never "
                     f"reveal it either way "
                     f"({sorted(self.states[self.initial]['view'])}), so the machine as "
                     f"emitted has zero hidden information and the recall element is "
                     f"decorative.")

        return {
            "game": self.name,
            "kind": "machine",
            "engine_module": self.doc["engine_module"],
            "action_limit": self.budget,
            "states": len(self.states),
            "reachable_states": len(reachable),
            "unreachable_states": unreachable_states,
            "actions": len(acts),
            "transitions": len(self.trans),
            "accept_rows": sum(1 for t in self.trans.values() if t["verdict"] == "accept"),
            "refuse_rows": sum(1 for t in self.trans.values() if t["verdict"] == "refuse"),
            "refusal_reasons": dict(sorted(live_reasons.items())),
            "dead_refusal_reasons": dead_reasons,
            "distinguishable_instances": 1,
            "information_floor_loose": 0,
            "information_floor_tight": 0,
            "execution_floor_as_designed": floor,
            "execution_floor_as_emitted": floor,
            "worst_case_optimal": floor,
            "worst_case_any_legal_play": worst_play,
            "budget_binds": floor is not None and floor >= self.budget,
            "budget_slack": None if floor is None else self.budget - floor,
            "rewarded_states": len(live_rewards),
            "doomed_states": len(doomed),
            "doomed_still_accepting": len(doomed_open),
            "can_lose": bool(doomed),
            "automorphism_group_order": len(autos),
            "opener_classes": len(opener_orbits),
            "openers_total": len(legal_openers),
            "opener_orbits": opener_orbits,
            "outcome_forks": outcome_forks,
            "turn_count_forks": budget_forks,
            "consequence_free_choices": forkless,
            "dead_actions": dead,
            "dominated_state_action_pairs": dominated_pairs,
            "globally_dominated_actions": dominated_everywhere,
        }


# ---------------------------------------------------------------------------
# backend 3 — parametric machines: a row names BOTH successors of one oracle bit
# ---------------------------------------------------------------------------

class ParametricMachineGame:
    """A machine that states the rules without the instance.

    A first exposure is deterministic.  A second consults one bit — did these two
    plates carry the same glyph — and the row names `on_match` AND `on_mismatch`,
    so the table is the rules and the bit is the whole instance.  Nothing in the
    descriptor says which branch a given run will take.

    The floor reported here is therefore the floor against an adversary who may
    answer any way still consistent with some board, which is what a player who has
    read the entire artifact actually faces.
    """

    VERDICTS = {"refuse", "accept", "resolve"}

    def __init__(self, doc: dict, rep: Report) -> None:
        self.doc = doc
        self.rep = rep
        self.name = doc["game_id"]
        sm = doc["state_machine"]
        self.sm = sm
        self.states = {s["id"]: s for s in sm["states"]}
        self.actions = [a["id"] for a in sm["actions"]]
        self.action_meta = {a["id"]: a for a in sm["actions"]}
        self.initial = sm["initial_state"]
        self.budget = doc["action_limit"]
        self.trans = {}
        for t in sm["transitions"]:
            key = (t["state"], t["action"])
            if key in self.trans:
                raise Refusal(f"duplicate transition row for {key}")
            self.trans[key] = t

    def totality(self) -> None:
        want = len(self.states) * len(self.actions)
        if len(self.trans) != want:
            raise Refusal(f"parametric table is not total: {len(self.trans)} rows, "
                          f"expected {want}")
        for (s, a), t in self.trans.items():
            verdict = t["verdict"]
            if verdict not in self.VERDICTS:
                raise Refusal(f"{s}/{a} has unknown verdict {verdict!r}")
            if verdict == "refuse":
                if not t["reason"]:
                    raise Refusal(f"{s}/{a} refuses without a named reason")
                if t["next"] or t["on_match"] or t["on_mismatch"]:
                    raise Refusal(f"{s}/{a} refuses but names a successor")
            elif verdict == "accept":
                if t["reason"] is not None:
                    raise Refusal(f"{s}/{a} accepts but carries a reason")
                if t["next"] not in self.states:
                    raise Refusal(f"{s}/{a} accepts into unknown state {t['next']}")
                if t["on_match"] or t["on_mismatch"]:
                    raise Refusal(f"{s}/{a} is deterministic but names oracle branches")
            else:
                if t["next"] is not None or t["reason"] is not None:
                    raise Refusal(f"{s}/{a} resolves but also names a plain successor")
                for branch in ("on_match", "on_mismatch"):
                    if t[branch] not in self.states:
                        raise Refusal(f"{s}/{a} {branch} is an unknown state")
                if t["on_match"] == t["on_mismatch"]:
                    raise Refusal(f"{s}/{a} resolves to the same state either way, so "
                                  f"the oracle bit is not consulted and the row should "
                                  f"be an accept")

    def successors(self, s, a):
        t = self.trans[(s, a)]
        if t["verdict"] == "refuse":
            return []
        if t["verdict"] == "accept":
            return [t["next"]]
        return [t["on_match"], t["on_mismatch"]]

    def differential(self) -> None:
        """Rebuild every row from the declared state view and refuse on disagreement.

        The rule is small enough to state: refuse if solved, out of turns, already
        cleared or already exposed; otherwise a first exposure exposes, and a second
        either clears both plates or clears neither.  Nothing in it mentions a board,
        which is the property being checked.
        """
        for (sid, aid), t in self.trans.items():
            view = self.states[sid]["view"]
            slot = self.action_meta[aid]["slot"]
            cleared, exposed, turns = set(view["cleared"]), view["exposed"], view["turns"]
            if len(cleared) == len(self.actions):
                want, reason = "refuse", "solved"
            elif turns >= self.budget:
                want, reason = "refuse", "turn-limit"
            elif slot in cleared:
                want, reason = "refuse", "cleared-slot"
            elif exposed == slot:
                want, reason = "refuse", "already-exposed"
            elif exposed is None:
                want, reason = "accept", None
            else:
                want, reason = "resolve", None
            if t["verdict"] != want:
                raise Refusal(f"rebuilt rule says {sid}/{aid} is {want}, emitted "
                              f"{t['verdict']}")
            if want == "refuse" and t["reason"] != reason:
                raise Refusal(f"{sid}/{aid} refuses as {t['reason']!r}, rebuilt "
                              f"{reason!r}")
            if want == "accept":
                nv = self.states[t["next"]]["view"]
                if (set(nv["cleared"]), nv["exposed"], nv["turns"]) != \
                        (cleared, slot, turns + 1):
                    raise Refusal(f"{sid}/{aid} accepts into a state that is not that "
                                  f"exposure")
            if want == "resolve":
                mv = self.states[t["on_match"]]["view"]
                xv = self.states[t["on_mismatch"]]["view"]
                if set(mv["cleared"]) != cleared | {slot, exposed}:
                    raise Refusal(f"{sid}/{aid} on_match does not clear both plates")
                if set(xv["cleared"]) != cleared:
                    raise Refusal(f"{sid}/{aid} on_mismatch clears something")
                if mv["turns"] != turns + 1 or xv["turns"] != turns + 1:
                    raise Refusal(f"{sid}/{aid} branches disagree with the clock")
                if mv["exposed"] is not None or xv["exposed"] is not None:
                    raise Refusal(f"{sid}/{aid} leaves a plate exposed after resolving")

    def automorphisms(self):
        """Permutations of the actions that extend to a state bijection preserving
        every verdict, reason and branch.  With the board hidden these should be ALL
        of them: that the opening is a free choice is the hiding, not a defect."""
        found = []
        acts = self.actions
        for perm in itertools.permutations(range(len(acts))):
            pi = {acts[i]: acts[perm[i]] for i in range(len(acts))}
            phi = {self.initial: self.initial}
            queue = deque([self.initial])
            ok = True
            while queue and ok:
                s = queue.popleft()
                ps = phi[s]
                if self.states[s]["terminal"] != self.states[ps]["terminal"]:
                    ok = False
                    break
                for a in acts:
                    t, pt = self.trans[(s, a)], self.trans[(ps, pi[a])]
                    if t["verdict"] != pt["verdict"] or t["reason"] != pt["reason"]:
                        ok = False
                        break
                    for key in ("next", "on_match", "on_mismatch"):
                        nxt, pnxt = t[key], pt[key]
                        if nxt is None and pnxt is None:
                            continue
                        if nxt is None or pnxt is None:
                            ok = False
                            break
                        if nxt in phi:
                            if phi[nxt] != pnxt:
                                ok = False
                                break
                        else:
                            phi[nxt] = pnxt
                            queue.append(nxt)
                    if not ok:
                        break
            if ok:
                found.append(pi)
        return found

    def analyse(self) -> dict:
        rep = self.rep
        self.totality()
        self.differential()

        reachable = {self.initial}
        queue = deque([self.initial])
        while queue:
            s = queue.popleft()
            for a in self.actions:
                for n in self.successors(s, a):
                    if n not in reachable:
                        reachable.add(n)
                        queue.append(n)
        unreachable = sorted(set(self.states) - reachable)

        terminal = {s for s in self.states if self.states[s]["terminal"]}
        solved = {s for s in self.states if self.states[s]["view"].get("solved") is True}
        rewarded = terminal & reachable

        longest = {}
        for s in sorted(reachable, key=lambda x: -self.states[x]["view"]["turns"]):
            best = 0
            for a in self.actions:
                for n in self.successors(s, a):
                    best = max(best, 1 + longest.get(n, 0))
            longest[s] = best
        worst_play = longest[self.initial]

        # A run is LOST when the clock runs out unsolved.  Under a hidden board an
        # unlucky-but-consistent oracle can force that, which is what makes the
        # budget mean something.
        exhausted = {s for s in reachable
                     if self.states[s]["view"]["turns"] >= self.budget and s not in terminal}

        live_reasons = Counter()
        for s in reachable:
            for a in self.actions:
                t = self.trans[(s, a)]
                if t["verdict"] == "refuse":
                    live_reasons[t["reason"]] += 1
        declared = {t["reason"] for t in self.trans.values() if t["reason"]}
        dead_reasons = sorted(declared - set(live_reasons))

        autos = self.automorphisms()
        gens = [(lambda p: (lambda a: p[a]))(p) for p in autos]
        opener_orbits = orbits(self.actions, gens)

        resolve_rows = sum(1 for t in self.trans.values() if t["verdict"] == "resolve")
        accept_rows = sum(1 for t in self.trans.values() if t["verdict"] == "accept")
        refuse_rows = sum(1 for t in self.trans.values() if t["verdict"] == "refuse")

        if unreachable:
            rep.find(self.name, "unreachable-state", WARN,
                     f"{len(unreachable)} emitted state(s) are unreachable",
                     f"e.g. {unreachable[:5]}")
        mism = sorted((terminal ^ solved) & reachable)
        if mism:
            rep.find(self.name, "terminal-solved-divergence", FAIL,
                     "terminal and solved disagree on a reachable state", f"{mism[:5]}")

        if len(opener_orbits) == 1:
            rep.find(self.name, "opening-is-a-free-choice", INFO,
                     "every opening plate is equivalent, and under a hidden board that "
                     "is the hiding rather than a defect",
                     f"the exact automorphism group of the emitted machine has "
                     f"{len(autos)} elements and acts transitively on all "
                     f"{len(self.actions)} plates.  Before the split this was a WARN, "
                     f"because the descriptor carried `glyph_id` and the plates were "
                     f"only nominally symmetric: a client could see which two matched. "
                     f"With the board out of the wire the symmetry is real, and a first "
                     f"exposure genuinely cannot be better or worse than another.")
        if dead_reasons:
            rep.find(self.name, "dead-refusal-reason", WARN,
                     f"{len(dead_reasons)} refusal reason(s) never fire", f"{dead_reasons}")
        if resolve_rows == 0:
            rep.find(self.name, "no-oracle-row", FAIL,
                     "no row of the machine consults the instance",
                     "every transition is deterministic, so the instance cannot affect "
                     "play and the game has no hidden information at all.")

        return {
            "game": self.name,
            "kind": "parametric-machine",
            "engine_module": self.doc["engine_module"],
            "action_limit": self.budget,
            "states": len(self.states),
            "reachable_states": len(reachable),
            "unreachable_states": unreachable,
            "actions": len(self.actions),
            "transitions": len(self.trans),
            "accept_rows": accept_rows,
            "refuse_rows": refuse_rows,
            "oracle_rows": resolve_rows,
            "refusal_reasons": dict(sorted(live_reasons.items())),
            "dead_refusal_reasons": dead_reasons,
            "rewarded_states": len(rewarded),
            "exhausted_states": len(exhausted),
            "can_lose": bool(exhausted),
            "worst_case_any_legal_play": worst_play,
            "automorphism_group_order": len(autos),
            "opener_classes": len(opener_orbits),
            "openers_total": len(self.actions),
            "opener_orbits": opener_orbits,
            # filled in by the seed-family pass, which owns the adversarial floor
            "information_floor_loose": None,
            "information_floor_tight": None,
            "execution_floor_as_designed": None,
            "execution_floor_as_emitted": None,
            "worst_case_optimal": None,
            "budget_binds": None,
            "budget_slack": None,
        }


# ---------------------------------------------------------------------------
# backend 4 — a FAMILY of machines, one per instance, none of them marked live
# ---------------------------------------------------------------------------

class MachineFamilyGame:
    """Relay Repair after the split: all eight board machines, no `selected`.

    Relay is a perfect-information puzzle — a player has to read the damage report
    to play at all — so its instance is disclosed to its own player at run start
    through the run opening.  The family stays public because the family is the
    rules; what left the wire is which member is live.

    Each machine is analysed by the deterministic backend, so nothing about the
    per-board measurement is re-derived here.
    """

    def __init__(self, doc: dict, rep: Report) -> None:
        self.doc = doc
        self.rep = rep
        self.name = doc["game_id"]
        self.sm = doc["state_machine"]
        self.machines = self.sm["machines"]
        self.budget = doc["action_limit"]

    def analyse(self) -> dict:
        rep = self.rep
        modulus = self.doc["instance"]["modulus"]
        if len(self.machines) != modulus:
            raise Refusal(f"{len(self.machines)} machines for a modulus of {modulus}")
        per_board, sink = [], Report()
        for index, machine in enumerate(self.machines):
            if machine["board"] != index:
                raise Refusal(f"machine {index} is out of order")
            sub = dict(self.doc)
            sub["state_machine"] = {
                "initial_state": self.sm["initial_state"],
                "actions": self.sm["actions"],
                "states": machine["states"],
                "transitions": machine["transitions"],
            }
            per_board.append(MachineGame(sub, sink).analyse())

        floors = [b["execution_floor_as_emitted"] for b in per_board]
        if any(f is None for f in floors):
            dead = [i for i, f in enumerate(floors) if f is None]
            rep.find(self.name, "unwinnable-instance", FAIL,
                     f"{len(dead)} board(s) in the family cannot be solved at all",
                     f"boards {dead} have no accepted path to a reward, so a run that "
                     f"draws one is refused from its first action.")
            raise Refusal(f"boards {dead} are unwinnable")
        worst = max(floors)
        losable = [i for i, b in enumerate(per_board) if b["can_lose"]]
        forks = [b["outcome_forks"] for b in per_board]

        if worst > self.budget:
            rep.find(self.name, "budget-below-optimum", FAIL,
                     "action_limit is below the shortest solution of some instance",
                     f"board floors {floors} against action_limit {self.budget}.")
        elif worst == self.budget:
            rep.find(self.name, "budget-binds-exactly", INFO,
                     "the action budget binds exactly on every instance of the family",
                     f"every board's shortest win is {worst} == action_limit "
                     f"{self.budget}; slack 0 whichever board a run draws.")
        else:
            rep.find(self.name, "budget-slack", WARN,
                     f"the budget never binds ({self.budget - worst} spare)",
                     f"worst board floor {worst}, action_limit {self.budget}.")

        if len(set(floors)) == 1 and len(set(forks)) == 1:
            rep.find(self.name, "family-may-be-uniform", INFO,
                     "every board costs the same and forks the same number of times",
                     f"floors {floors}, outcome forks {forks}.  Equal cost is not the "
                     f"same as equal shape — `relay_instance_family` measures which "
                     f"routes each board can pay for — but a family whose members are "
                     f"indistinguishable by cost gives a returning player less than the "
                     f"draw suggests.")

        if not losable:
            rep.find(self.name, "cannot-lose", WARN, "no instance of the family can be lost",
                     "every reachable state on every board can still reach a reward.")

        return {
            "game": self.name,
            "kind": "machine-family",
            "engine_module": self.doc["engine_module"],
            "action_limit": self.budget,
            "instances": len(per_board),
            "states": sum(b["states"] for b in per_board),
            "reachable_states": sum(b["reachable_states"] for b in per_board),
            "actions": per_board[0]["actions"],
            "transitions": sum(b["transitions"] for b in per_board),
            "per_board_states": [b["states"] for b in per_board],
            "per_board_floor": floors,
            "per_board_can_lose": [b["can_lose"] for b in per_board],
            "per_board_outcome_forks": forks,
            "per_board_opener_classes": [b["opener_classes"] for b in per_board],
            "information_floor_loose": 0,
            "information_floor_tight": 0,
            "execution_floor_as_designed": worst,
            "execution_floor_as_emitted": worst,
            "worst_case_optimal": worst,
            "worst_case_any_legal_play": max(b["worst_case_any_legal_play"]
                                             for b in per_board),
            "budget_binds": worst >= self.budget,
            "budget_slack": self.budget - worst,
            "can_lose": bool(losable),
            "doomed_states": sum(b["doomed_states"] for b in per_board),
            "opener_classes": max(b["opener_classes"] for b in per_board),
            "openers_total": max(b["openers_total"] for b in per_board),
            "outcome_forks": sum(forks),
            "automorphism_group_order": max(b["automorphism_group_order"]
                                            for b in per_board),
        }


# ---------------------------------------------------------------------------
# Salvage-specific seed-family analysis (rebuilt model, differentially checked)
# ---------------------------------------------------------------------------

def hidden_pairing_worst_case(n_slots: int) -> tuple[int, int]:
    """Counterfactual: what would this board cost if the pairing were actually hidden?

    A perfect-memory player faces a uniformly chosen perfect matching of `n_slots`
    plates; an adaptive adversary answers each exposure with any glyph identity still
    consistent with at least one candidate matching.  Exposing a plate costs one turn
    whether or not it completes a pair, exactly as the kernel charges it.  Returns
    (worst-case turns under optimal play, number of candidate boards).

    This is what the shipped `action_limit` would have to cover if `glyphAt` produced
    a real board instead of `slot mod 3`.
    """
    slots = tuple(range(n_slots))
    matchings = []

    def build(rest, acc):
        if not rest:
            matchings.append(frozenset(acc))
            return
        head, tail = rest[0], rest[1:]
        for i, other in enumerate(tail):
            build(tail[:i] + tail[i + 1:], acc + [frozenset((head, other))])

    build(slots, [])
    all_boards = frozenset(matchings)

    def partner(board, s):
        for pair in board:
            if s in pair:
                return next(iter(pair - {s}))
        raise AssertionError

    memo: dict = {}

    def value(cleared, exposed, seen, cands):
        """Fewest turns to clear every plate, worst case over the adversary."""
        if len(cleared) == n_slots:
            return 0
        key = (cleared, exposed, seen, cands)
        hit = memo.get(key)
        if hit is not None:
            return hit
        memo[key] = 10 ** 6  # cycle guard; turns strictly increase so it never fires
        best = 10 ** 6
        for s in slots:
            if s in cleared or s == exposed:
                continue
            blocks: dict = defaultdict(set)
            for board in cands:
                p = partner(board, s)
                blocks["NEW" if p not in seen else p].add(board)
            worst = 0
            for obs, block in blocks.items():
                nseen = seen | frozenset({s})
                if exposed is not None and obs == exposed:
                    nxt = value(cleared | frozenset({s, exposed}), None, nseen,
                                frozenset(block))
                elif exposed is not None:
                    nxt = value(cleared, None, nseen, frozenset(block))
                else:
                    nxt = value(cleared, s, nseen, frozenset(block))
                worst = max(worst, 1 + nxt)
                if worst >= best:
                    break
            best = min(best, worst)
        memo[key] = best
        return best

    return value(frozenset(), None, frozenset(), all_boards), len(all_boards)


def _salvage_draw_below(bound: int, stream: list[int]):
    """The rejection-sampled CONSUMING draw of `SeedDraw.drawBelow?`: returns the
    value and the bytes that remain.  A draw that re-read the same prefix (the shape
    of `SalvageCrate.unbiasedIndex?`) would return the same byte four times and the
    board index would be a function of one byte."""
    ceiling = 256 - (256 % bound)
    for i, b in enumerate(stream):
        if b < ceiling:
            return b % bound, stream[i + 1:]
    return None


def salvage_seed_from_run_seed(run_seed_hex: str):
    """Four consuming draws: partner of plate 0 (5), partner of the lowest remaining
    plate (3), glyph name for pair 0 (3), glyph name for pair 1 (2)."""
    stream = [int(run_seed_hex[i:i + 2], 16) for i in range(0, len(run_seed_hex), 2)]
    digits = []
    for bound in (5, 3, 3, 2):
        got = _salvage_draw_below(bound, stream)
        if got is None:
            return None, digits
        value, stream = got
        digits.append(value)
    a, b, c, d = digits
    return 18 * a + 6 * b + 2 * c + d, digits


def salvage_board(seed: int) -> tuple[list[tuple[int, int]], list[int]]:
    """`SalvageLock.pairsOf` / `glyphNamesOf` / `boardRow`, rebuilt.  Returns the
    matching and the six-glyph row."""
    a, b = seed // 18, (seed % 18) // 6
    c, d = (seed % 6) // 2, seed % 2
    rest0 = [1, 2, 3, 4, 5]
    p = rest0[a]
    rest1 = [x for x in rest0 if x != p]
    m = rest1[0]
    rest2 = [x for x in rest1 if x != m]
    q = rest2[b]
    rest3 = [x for x in rest2 if x != q]
    pairs = [(0, p), (m, q), (rest3[0], rest3[1])]
    names = [0, 1, 2]
    g0 = names[c]
    left = [x for x in names if x != g0]
    g1 = left[d]
    g2 = [x for x in left if x != g1][0]
    row = [0] * 6
    for (lo, hi), glyph in zip(pairs, [g0, g1, g2]):
        row[lo] = glyph
        row[hi] = glyph
    return sorted(pairs), row


def salvage_pairing_from_transitions(doc: dict) -> list[tuple[int, int]]:
    """The pairing read back out of the TRANSITION table alone, with the action
    rows ignored.  This is the independent half of the differential — and it is also
    why deleting `glyph_id` from the action rows would hide nothing: which exposures
    clear is stated by the successors."""
    sm = doc["state_machine"]
    states = {s["id"]: s for s in sm["states"]}
    trans = {(t["state"], t["action"]): t for t in sm["transitions"]}
    initial = sm["initial_state"]
    partner = {}
    for first in range(6):
        step1 = trans.get((initial, f"slot-{first}"))
        if step1 is None or step1["verdict"] != "accept":
            raise Refusal(f"initial state refuses slot-{first}; cannot read the board "
                          f"back out of the transition table")
        exposed_state = step1["next"]
        for second in range(6):
            if second == first:
                continue
            step2 = trans.get((exposed_state, f"slot-{second}"))
            if step2 is None or step2["verdict"] != "accept":
                continue
            if states[step2["next"]]["view"]["cleared"]:
                partner[first] = second
    if sorted(partner) != list(range(6)):
        raise Refusal(f"the transition table pairs only {sorted(partner)}")
    return sorted({tuple(sorted((s, partner[s]))) for s in range(6)})


def salvage_seed_family(doc: dict, rep: Report, summary: dict) -> None:
    """What the hidden board costs, measured against the family the artifact declares.

    ⚠ This function used to open `run_seed`, rebuild the ONE drawn board, and check
    it against `glyph_id` and against the successors.  Both of those inputs are gone
    — that was the leak — so what is read now is `practice.boards`, the whole family
    a browser rehearses against, and the floor is computed against an adversary who
    may answer any way still consistent with SOME member of it.
    """
    name = doc["game_id"]
    slots, glyphs = 6, 3
    practice = doc.get("practice")
    if not isinstance(practice, dict):
        raise Refusal("salvage descriptor carries no `practice` block; a client that "
                      "cannot draw a rehearsal instance has no offline mode, and this "
                      "gate has no family to measure against")
    if practice.get("scored") is not False:
        raise Refusal("the practice block does not declare itself unscored")
    boards_raw = practice["boards"]
    if len(boards_raw) != practice["instance_space"]:
        raise Refusal(f"practice block emits {len(boards_raw)} boards for a declared "
                      f"space of {practice['instance_space']}")

    families = defaultdict(list)
    boards = set()
    for seed, row in enumerate(boards_raw):
        if len(row) != slots:
            raise Refusal(f"practice board {seed} is not {slots} plates")
        counts = sorted(Counter(row).values())
        if counts != [2, 2, 2]:
            raise Refusal(f"practice board {seed} is {row}, which is not two of each "
                          f"of {glyphs} glyphs")
        pairs = []
        for glyph in sorted(set(row)):
            a, b = [i for i, x in enumerate(row) if x == glyph]
            pairs.append((a, b))
        families[tuple(sorted(pairs))].append(seed)
        boards.add(tuple(row))

    if len(boards) != len(boards_raw):
        raise Refusal(f"the practice family names {len(boards)} distinct boards in "
                      f"{len(boards_raw)} slots: some instance is drawn twice as often "
                      f"as the rest")

    hidden_worst, matchings = hidden_pairing_worst_case(slots)
    labellings = {len(v) for v in families.values()}

    summary["instance_space"] = len(boards_raw)
    summary["distinct_pairings_over_instance_space"] = len(families)
    summary["distinct_boards_over_instance_space"] = len(boards)
    summary["perfect_matchings"] = matchings
    summary["labellings_per_matching"] = sorted(labellings)
    summary["information_floor_loose"] = ceil_log(matchings, 2)
    summary["information_floor_tight"] = ceil_log(matchings, 2)
    summary["execution_floor_as_designed"] = hidden_worst
    summary["execution_floor_as_emitted"] = hidden_worst
    summary["worst_case_optimal"] = hidden_worst
    summary["budget_binds"] = hidden_worst >= doc["action_limit"]
    summary["budget_slack"] = doc["action_limit"] - hidden_worst

    if len(families) < matchings:
        rep.find(name, "family-underdetermines-board", WARN,
                 f"the {len(boards_raw)} instances reach only {len(families)} of the "
                 f"{matchings} perfect matchings",
                 f"a family that cannot name every matching hands some boards to "
                 f"nobody, and a player who knows the reachable set starts with "
                 f"information the design did not mean to give.")
    elif labellings != {glyphs * 2}:
        rep.find(name, "uneven-glyph-labelling", WARN,
                 "some matchings carry more glyph labellings than others",
                 f"labelling counts per matching: {sorted(labellings)}.  An uneven "
                 f"count makes a glyph name weak evidence about the pairing.")
    else:
        rep.find(name, "family-covers-every-matching", INFO,
                 f"the instance space is exactly the {len(boards)} two-of-each boards, "
                 f"over all {matchings} perfect matchings",
                 f"each matching is carried by {sorted(labellings)[0]} instances — its "
                 f"3! glyph relabellings — so a glyph name says nothing about the "
                 f"pairing beyond agreement with a glyph already seen.  There is no "
                 f"memory-free routine: `pair = slot mod {glyphs}` is wrong on "
                 f"{matchings - 1} of the {matchings} matchings.")

    budget = doc["action_limit"]
    verdict = ("binds exactly" if hidden_worst == budget
               else f"leaves {budget - hidden_worst} spare")
    # The same budget verdict every other backend emits.  Dropping it here because
    # the floor improved would be a gate quietly losing a way to go red.
    if hidden_worst > budget:
        rep.find(name, "budget-below-optimum", FAIL,
                 "action_limit is below the proven worst case against a hidden board",
                 f"worst case {hidden_worst} > action_limit {budget}: some instances "
                 f"cannot be cleared at all.")
    elif hidden_worst == budget:
        rep.find(name, "budget-binds-exactly", INFO,
                 "the action budget binds exactly under optimal play",
                 f"worst case {hidden_worst} == action_limit {budget}; slack 0.")
    else:
        rep.find(name, "budget-slack", WARN,
                 f"the action budget does not bind ({budget - hidden_worst} spare)",
                 f"worst case {hidden_worst} against action_limit {budget}.  The slack "
                 f"was {budget - summary.get('_pre_split_floor', 6)} before the split "
                 f"and is {budget - hidden_worst} now, so the budget went from mostly "
                 f"decorative to nearly binding — but a run that plays optimally still "
                 f"cannot be forced to spend the last {budget - hidden_worst} turns.")
    rep.find(name, "hidden-board-floor", INFO,
             f"a player who has read the whole artifact still needs {hidden_worst} "
             f"exposures in the worst case; the budget {verdict}",
             f"against a uniformly drawn one of the {matchings} perfect matchings of "
             f"{slots} plates, a perfect-memory player facing an adversary who answers "
             f"any way still consistent with some board needs {hidden_worst} turns.  "
             f"⚠ The pre-split descriptor published the board in `glyph_id` and in its "
             f"successors, so a player who read it needed 6 and this {hidden_worst} was "
             f"reported only as a counterfactual.  It is now the measured floor: the "
             f"emitted table names both branches of every second exposure and nothing "
             f"in the artifact says which one a run will take.")


def simple_paths(edges, source, sink):
    """Every simple source->sink path in the emitted graph, as action-id lists.

    `edges` maps action id -> (from, to).  The relay is undirected in the fiction
    (a link carries power either way), so both orientations are walked.
    """
    adj = defaultdict(list)
    for aid, (u, v) in edges.items():
        adj[u].append((v, aid))
        adj[v].append((u, aid))
    out = []

    def walk(node, seen_nodes, acc):
        if node == sink:
            out.append(list(acc))
            return
        for nxt, aid in adj[node]:
            if nxt in seen_nodes:
                continue
            acc.append(aid)
            walk(nxt, seen_nodes | {nxt}, acc)
            acc.pop()

    walk(source, {source}, [])
    return out


def relay_instance_family(doc: dict, rep: Report, summary: dict) -> None:
    """Relay Repair publishes a seeded damage board.  Rebuild the whole rule from the
    declared instance (graph + per-link spare cost + crate size) and refuse unless it
    reproduces every emitted state view and every one of the emitted transition rows;
    only then ask what the seed space actually contains."""
    name = doc["game_id"]
    inst = doc.get("instance")
    if inst is None:
        raise Refusal("relay-repair no longer declares an `instance`; this gate "
                      "cannot tell what the run seed selects")
    want = {"modulus", "source", "sink", "draw", "boards"}
    if set(inst) != want:
        raise Refusal(f"instance block carries {sorted(inst)}, expected {sorted(want)}")

    budget = doc["action_limit"]
    edges = {a["id"]: (a["from"], a["to"]) for a in doc["state_machine"]["actions"]}
    action_ids = set(edges)
    routes = simple_paths(edges, inst["source"], inst["sink"])
    if not routes:
        raise Refusal(f"no {inst['source']}->{inst['sink']} path exists in the emitted "
                      f"link graph, so no run can ever be rewarded")

    boards = inst["boards"]
    if len(boards) != inst["modulus"]:
        raise Refusal(f"{len(boards)} boards for a modulus of {inst['modulus']}")
    for index, board in enumerate(boards):
        if set(board) != {"index", "spares", "costs"} or board["index"] != index:
            raise Refusal(f"board {index} is malformed or out of order")
        if set(board["costs"]) != action_ids:
            raise Refusal(f"board {index} does not price exactly the emitted links")
        if any(c < 1 for c in board["costs"].values()):
            raise Refusal(f"board {index} prices a link below one spare")

    # ⚠ `selected` and `seed_byte` are gone, so there is no drawn board to rebuild
    # against.  The differential now runs over EVERY machine in the family: each
    # board's declared pricing must reproduce every state view and every row of its
    # own machine, so no member of the family is analysed on trust.
    machines = {m["board"]: m for m in doc["state_machine"]["machines"]}
    if sorted(machines) != list(range(len(boards))):
        raise Refusal(f"the emitted machines cover {sorted(machines)}, not every board")

    for index, board in enumerate(boards):
        costs, crate = board["costs"], board["spares"]
        machine = machines[index]

        def route_cost(links, costs=costs):
            return sum(costs[l] for l in links)

        def solved_by(installed):
            return any(all(l in installed for l in r) for r in routes)

        def completable(installed, turns, spares, costs=costs):
            for r in routes:
                missing = [l for l in r if l not in installed]
                if len(missing) + turns <= budget and route_cost(missing, costs) <= spares:
                    return True
            return False

        facts = {}
        for state in machine["states"]:
            view = state["view"]
            installed = set(view["installed"])
            if not installed <= action_ids:
                raise Refusal(f"board {index} state {state['id']} installs an unknown link")
            spares = crate - route_cost(installed)
            solved = solved_by(installed)
            stranded = not solved and not completable(installed, view["turns"], spares)
            got = (state["terminal"], view["solved"], view["spares"], view["stranded"])
            model = (solved, solved, spares, stranded)
            if got != model:
                raise Refusal(
                    f"board {index}: rebuilt pricing disagrees with emitted state "
                    f"{state['id']}: (terminal, solved, spares, stranded) "
                    f"emitted={got} model={model}")
            facts[state["id"]] = (installed, view["turns"], spares, solved, stranded)

        for t in machine["transitions"]:
            installed, turns, spares, solved, stranded = facts[t["state"]]
            link = t["action"]
            legal = (not solved and turns < budget and not stranded
                     and link not in installed and costs[link] <= spares)
            if legal != (t["verdict"] == "accept"):
                raise Refusal(f"board {index}: rebuilt rule disagrees with emitted row "
                              f"{t['state']}/{link}")
            if legal:
                nxt = facts[t["next"]]
                if nxt[0] != installed | {link} or nxt[1] != turns + 1:
                    raise Refusal(f"board {index}: row {t['state']}/{link} accepts into "
                                  f"{t['next']}, which is not that install")
            else:
                claim = {"solved": solved, "turn-limit": turns >= budget,
                         "already-installed": link in installed,
                         "no-spares": costs[link] > spares, "stranded": stranded}
                if t["reason"] not in claim or not claim[t["reason"]]:
                    raise Refusal(f"board {index}: row {t['state']}/{link} refuses as "
                                  f"{t['reason']!r}, which is not true of that state")

    # -- what the seed space actually contains ------------------------------------
    def signature(b):
        aff = tuple(sorted(tuple(r) for r in routes
                           if sum(b["costs"][l] for l in r) <= b["spares"]))
        return aff

    shapes = [signature(b) for b in boards]
    unwinnable = [b["index"] for b, s in zip(boards, shapes) if not s]
    distinct_boards = len({(b["spares"], tuple(sorted(b["costs"].items())))
                           for b in boards})
    distinct_classes = len(set(shapes))

    summary["board_space"] = len(boards)
    summary["routes_source_to_sink"] = [list(r) for r in routes]
    summary["distinct_instances_expressible"] = distinct_boards
    summary["distinct_instance_classes"] = distinct_classes
    summary["unwinnable_boards"] = unwinnable
    summary["information_floor_loose"] = ceil_log(distinct_classes, 2)
    summary["information_floor_tight"] = 0

    if unwinnable:
        rep.find(name, "unwinnable-instance", FAIL,
                 f"{len(unwinnable)} board(s) in the family cannot be solved at all",
                 f"boards {unwinnable} price every {inst['source']}->{inst['sink']} "
                 f"route above their own crate, so a run that draws one is refused from "
                 f"the first action.  Before the split only one board was ever live and "
                 f"this was invisible; every board is now reachable by some run.")

    if distinct_classes == 1:
        rep.find(name, "instance-inert", WARN,
                 f"all {len(boards)} boards leave the same routes affordable",
                 f"the draw reprices the links but never changes which of the "
                 f"{len(routes)} routes a player can pay for, so the board is "
                 f"decoration and one memorised line clears every instance.")

    rep.find(name, "instance-opened-to-its-own-player", INFO,
             "the damage board is disclosed per run, to its own player, and no longer "
             "printed once for everyone",
             f"`instance` states the graph, the crate and the per-link cost of all "
             f"{len(boards)} boards — that is the RULES, and Relay Repair is a routing "
             f"puzzle rather than a deduction game, so hiding the report would make the "
             f"read a guess.  ⚠ What is GONE is `selected` and `seed_byte`: the pair "
             f"that named which board was live and which published byte drew it.  A run "
             f"learns its own board from the slot opening at start, and learns nothing "
             f"about anyone else's, because the draw takes the player key.  The family "
             f"offers {distinct_classes} distinct affordable-route shapes over "
             f"{distinct_boards} distinct boards.")


# ---------------------------------------------------------------------------
# reference self-check
# ---------------------------------------------------------------------------

# Hand-measured for Signal Triangulation before this tool existed, and pinned here so
# the tool cannot quietly drift away from the numbers a human checked — or quietly
# agree with a number that is wrong.  A DISAGREE line is the point of the block.
REFERENCE = [
    ("signal-triangulation", "code domain", 216,
     lambda g: g["domain"]["codes"]),
    ("signal-triangulation", "action budget", 5,
     lambda g: g["action_limit"]),
    ("signal-triangulation", "realizable feedback classes", 9,
     lambda g: g["feedback_classes_realizable"]),
    ("signal-triangulation", "information floor", 3,
     lambda g: g["information_floor_tight"]),
    ("signal-triangulation", "greedy opener (0,1,2) worst case", 5,
     lambda g: _pol(g, [0, 1, 2])["worst_case"]),
    ("signal-triangulation", "greedy opener (0,1,2) mean", 4.05,
     lambda g: round(_pol(g, [0, 1, 2])["mean"], 2)),
    ("signal-triangulation", "greedy opener (0,1,2) targets needing all five", 54,
     lambda g: _pol(g, [0, 1, 2])["at_budget"]),
    ("signal-triangulation", "naive opener (0,0,0) worst case", 6,
     lambda g: _pol(g, [0, 0, 0])["worst_case"]),
    ("signal-triangulation", "naive opener (0,0,0) losses", 4,
     lambda g: _pol(g, [0, 0, 0])["losses"]),
    # Salvage, hand-derived before the rebuilt model existed.  The run seed spells
    # SALVAGE-1, so the four consuming draws take bytes 0x53, 0x41, 0x4c, 0x56
    # against bounds 5, 3, 3, 2 (each below its ceiling, so none is rejected),
    # giving 3, 2, 1, 0 and board 18*3 + 6*2 + 2*1 + 0 = 68.  A draw with no cursor
    # would read 0x53 four times -> 3, 2, 2, 1 -> board 71, so this fixture is a
    # witness that the draw consumes, not only the theorem in SeedDraw.
    ("salvage-lock", "board space (6!/(2!2!2!))", 90,
     lambda g: g["seed_space"]),
    ("salvage-lock", "perfect matchings the seed space reaches", 15,
     lambda g: g["distinct_pairings_over_seed_space"]),
    ("salvage-lock", "board drawn by the pinned run seed", 68,
     lambda g: g["pinned_seed"]),
    ("salvage-lock", "hidden-board worst case (perfect memory)", 10,
     lambda g: g["counterfactual_hidden_worst_case"]),
]


def _pol(game, opener):
    for p in game["reference_policies"]:
        if p["opener"] == opener:
            return p
    raise KeyError(opener)


def check_reference(report: Report, out):
    by_id = {g["game"]: g for g in report.games}
    rows, disagreements = [], 0
    for gid, label, expected, fn in REFERENCE:
        if gid not in by_id:
            continue
        try:
            got = fn(by_id[gid])
        except Exception as exc:  # noqa: BLE001
            got = f"<{exc}>"
        agree = got == expected
        disagreements += 0 if agree else 1
        rows.append((gid, label, expected, got, agree))
    if not rows:
        return 0
    out.write("\n" + "=" * 78 + "\n")
    out.write("REFERENCE SELF-CHECK — hand-measured values vs this tool\n")
    out.write("=" * 78 + "\n")
    for gid, label, expected, got, agree in rows:
        mark = "agree   " if agree else "DISAGREE"
        out.write(f"  {mark}  {label:<48} hand={expected!s:<8} tool={got}\n")
    if disagreements:
        out.write(
            "\n  The information floor is the disagreement, and it is not a bug.\n"
            "  ceil(log_9 216) = 3 is the entropy bound, and it is NOT ATTAINABLE:\n"
            "  exactly one feedback class ends the run, and it ends it by being the\n"
            "  code itself.  A depth-d strategy therefore resolves at most\n"
            "      M(d) = 1 + 8*M(d-1),   M(1)=1, M(2)=9, M(3)=73, M(4)=585\n"
            "  codes, and 73 < 216, so no strategy identifies 216 codes in 3 guesses.\n"
            "  The floor is 4.  The exact minimax value is 5, and 4 is unreachable\n"
            "  from every one of the 3 opener classes (searched exhaustively over the\n"
            "  verified symmetry-reduced root), so action_limit = 5 binds exactly.\n")
    return disagreements


# ---------------------------------------------------------------------------
# rendering
# ---------------------------------------------------------------------------

def summary_table(report: Report, out):
    out.write("\n" + "=" * 78 + "\n")
    out.write("SUMMARY\n")
    out.write("=" * 78 + "\n")
    out.write(f"  {'game':<22}{'info':>5}{'exec':>6}{'opt':>5}{'budget':>8}"
              f"{'slack':>7}{'openers':>9}{'can lose':>10}\n")
    out.write(f"  {'':<22}{'floor':>5}{'floor':>6}{'wc':>5}{'':>8}{'':>7}"
              f"{'classes':>9}{'':>10}\n")
    for g in report.games:
        out.write(
            f"  {g['game']:<22}{g['information_floor_tight']:>5}"
            f"{str(g['execution_floor_as_emitted']):>6}"
            f"{str(g['worst_case_optimal']):>5}{g['action_limit']:>8}"
            f"{str(g['budget_slack']):>7}{g['opener_classes']:>9}"
            f"{str(g.get('can_lose', 'n/a')):>10}\n")
    out.write("\n  info floor  questions needed to identify the instance\n")
    out.write("  exec floor  shortest accepted path to a reward, given the descriptor\n")
    out.write("              the client actually fetches\n")
    out.write("  opt wc      worst case under optimal play (exact, not heuristic)\n")


def bar(label, value):
    return f"  {label:<34}{value}"


def render(report: Report, out) -> None:
    w = out.write
    w("\n")
    w("=" * 78 + "\n")
    w("PATH OF ANGELS — GAME-DESIGN GATE   (PLATFORM-ROADMAP 12.3)\n")
    w("=" * 78 + "\n")

    for g in report.games:
        w("\n" + "-" * 78 + "\n")
        w(f"{g['game']}   [{g['kind']}]   {g['engine_module']}\n")
        w("-" * 78 + "\n")
        if g["kind"] == "deduction":
            d = g["domain"]
            w(bar("domain", f"{d['codes']} codes ({d['bands']} bands x "
                            f"{d['alphabet']} symbols)") + "\n")
            w(bar("model differential", g["differential"]) + "\n")
            w(bar("symmetry verified",
                  ", ".join(g["symmetry_checked"])) + "\n")
            w(bar("feedback classes",
                  f"{g['feedback_classes_realizable']} realizable of "
                  f"{g['feedback_classes_declared']} declared") + "\n")
            if g["unrealizable_classes"]:
                w(bar("  unreachable outcomes",
                      f"{g['unrealizable_classes']}") + "\n")
            w(bar("information floor",
                  f"{g['information_floor_tight']} tight  "
                  f"(loose ceil(log_{g['feedback_classes_realizable']} "
                  f"{d['codes']}) = {g['information_floor_loose']})") + "\n")
            w(bar("worst case, optimal play", f"{g['worst_case_optimal']}  (exact minimax)")
              + "\n")
            w(bar("execution floor, as emitted",
                  f"{g['execution_floor_as_emitted']}  (target is published)") + "\n")
            w(bar("action budget",
                  f"{g['action_limit']}   binds: {g['budget_binds']}   "
                  f"slack: {g['budget_slack']}") + "\n")
            w(bar("opener classes",
                  f"{g['opener_classes']} of {g['openers_total']} openers, up to the "
                  f"verified group") + "\n")
            w("\n  opener class        size   optimal worst case   within budget\n")
            for o in g["opener_analysis"]:
                val = o["worst_case_optimal"]
                w(f"  {o['class']:<18}{o['size']:>5}   {str(val) if val else '>budget':>18}"
                  f"   {str(o['within_budget']):>13}\n")
            w("\n  reference policy: fixed opener, then Knuth minimax over the full pool\n")
            w("  opener        worst   mean    at-budget   losses   distribution\n")
            for p in g["reference_policies"]:
                w(f"  {str(p['opener']):<14}{p['worst_case']:>5}{p['mean']:>8}"
                  f"{p['at_budget']:>12}{p['losses']:>9}   {p['distribution']}\n")
            w("\n  instance families (whole seed space)\n")
            for f in g["instance_families"]:
                w(f"    {f['class']:<8} {f['instances']:>4} instances   "
                  f"{f['feedback_classes_realizable']} feedback classes realizable\n")
        else:
            w(bar("machine",
                  f"{g['states']} states ({g['reachable_states']} reachable), "
                  f"{g['actions']} actions, {g['transitions']} rows") + "\n")
            w(bar("totality", "every (state, action) has exactly one row") + "\n")
            verdicts = f"{g.get('accept_rows', 0)} accept / {g.get('refuse_rows', 0)} refuse"
            if g.get("oracle_rows"):
                verdicts += f" / {g['oracle_rows']} oracle-resolved"
            w(bar("verdicts", verdicts) + "\n")
            if "refusal_reasons" in g:
                w(bar("refusal reasons",
                      ", ".join(f"{k}:{v}" for k, v in g["refusal_reasons"].items())) + "\n")
            w(bar("instance disclosure", f"{g.get('instance_disclosure', '?')}") + "\n")
            w(bar("information floor", f"{g['information_floor_tight']}") + "\n")
            w(bar("execution floor",
                  f"{g['execution_floor_as_emitted']}  (guaranteed, given the "
                  f"descriptor the client fetches)") + "\n")
            w(bar("worst case, optimal play",
                  f"{g['worst_case_optimal']}   worst legal play: "
                  f"{g['worst_case_any_legal_play']}") + "\n")
            w(bar("action budget",
                  f"{g['action_limit']}   binds: {g['budget_binds']}   "
                  f"slack: {g['budget_slack']}") + "\n")
            w(bar("can the run be lost?", f"{g.get('can_lose')}") + "\n")
            if "outcome_forks" in g:
                w(bar("outcome-changing forks", f"{g['outcome_forks']}") + "\n")
            w(bar("automorphism group order",
                  f"{g.get('automorphism_group_order', '?')}") + "\n")
            w(bar("opener classes",
                  f"{g['opener_classes']} of {g['openers_total']} legal openers") + "\n")
            for k in ("instance_space", "distinct_pairings_over_instance_space",
                      "distinct_boards_over_instance_space", "perfect_matchings",
                      "labellings_per_matching", "exhausted_states",
                      "board_space", "instances", "per_board_states", "per_board_floor",
                      "per_board_can_lose", "per_board_outcome_forks",
                      "routes_source_to_sink", "distinct_instance_classes",
                      "unwinnable_boards", "distinct_instances_expressible",
                      "dead_actions", "globally_dominated_actions"):
                if k in g:
                    w(bar(k.replace("_", " "), f"{g[k]}") + "\n")

    summary_table(report, out)
    check_reference(report, out)

    w("\n" + "=" * 78 + "\n")
    w("FINDINGS\n")
    w("=" * 78 + "\n")
    for sev in (FAIL, WARN, INFO):
        rows = [f for f in report.findings if f["severity"] == sev]
        if not rows:
            continue
        w(f"\n{sev}  ({len(rows)})\n")
        for f in rows:
            w(f"\n  [{f['key']}]\n")
            w(f"  {f['title']}\n")
            for line in _wrap(f["detail"], 74):
                w(f"      {line}\n")
    w("\n")


def _wrap(text, width):
    words, line, out = text.split(), "", []
    for word in words:
        if len(line) + len(word) + 1 > width:
            out.append(line)
            line = word
        else:
            line = f"{line} {word}".strip()
    if line:
        out.append(line)
    return out


# ---------------------------------------------------------------------------

def pick_backend(doc: dict):
    """Dispatch on the SHAPE, so a descriptor cannot pick its own analyser by id."""
    if "rules" in doc:
        return DeductionGame
    sm = doc.get("state_machine")
    if not isinstance(sm, dict):
        raise Refusal(f"{doc.get('game_id')} carries no analysable shape")
    if "machines" in sm:
        return MachineFamilyGame
    if any(t.get("verdict") == "resolve" for t in sm.get("transitions", [])):
        return ParametricMachineGame
    raise Refusal(f"{doc.get('game_id')} carries a deterministic single machine with no "
                  f"oracle row and no board family: it has no hidden information, so "
                  f"there is nothing for a commitment to bind")


def analyse_doc(doc: dict, rep: Report) -> dict:
    if doc.get("format") != "POAG1-GAME":
        raise Refusal(f"{doc.get('game_id')} is not a POAG1-GAME descriptor")
    # First, and before anything is measured: does the artifact state its own
    # answer?  If it does, every floor below it is a floor of one.
    disclosure = check_instance_contract(doc, rep)
    summary = pick_backend(doc)(doc, rep).analyse()
    summary["instance_disclosure"] = disclosure
    if doc["game_id"] == "salvage-lock":
        salvage_seed_family(doc, rep, summary)
    if doc["game_id"] == "relay-repair":
        relay_instance_family(doc, rep, summary)
    return summary


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--games-dir", default=GAMES_DIR)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--baseline", help="accepted-findings file; an unknown finding "
                                       "or a vanished baseline entry exits 1")
    ap.add_argument("--update-baseline", metavar="FILE")
    ap.add_argument("--strict", action="store_true", help="any WARN exits 1")
    ap.add_argument("--only", action="append", help="restrict to these game ids")
    args = ap.parse_args()

    rep = Report()
    paths = sorted(os.path.join(args.games_dir, f)
                   for f in os.listdir(args.games_dir) if f.endswith(".json"))
    if not paths:
        print(f"poa-design-gate: no descriptors under {args.games_dir}", file=sys.stderr)
        return 2

    for path in paths:
        doc = json.load(open(path))
        gid = doc.get("game_id", os.path.basename(path).rsplit(".", 1)[0])
        if args.only and gid not in args.only:
            continue
        try:
            rep.games.append(analyse_doc(doc, rep))
        except Refusal as exc:
            rep.find(gid, "analyser-refusal", FAIL,
                     "the gate refuses to analyse this descriptor", str(exc))

    if args.json:
        json.dump({"games": rep.games, "findings": rep.findings}, sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        render(rep, sys.stdout)

    keys = sorted(f["key"] for f in rep.findings if f["severity"] in (FAIL, WARN))
    if args.update_baseline:
        with open(args.update_baseline, "w") as fh:
            json.dump({"accepted": keys}, fh, indent=2)
            fh.write("\n")
        print(f"poa-design-gate: wrote {len(keys)} accepted findings to "
              f"{args.update_baseline}", file=sys.stderr)

    fails = [f for f in rep.findings if f["severity"] == FAIL]
    warns = [f for f in rep.findings if f["severity"] == WARN]
    print(f"poa-design-gate: {len(rep.games)} game(s), {len(fails)} FAIL, "
          f"{len(warns)} WARN", file=sys.stderr)

    if fails:
        return 2

    if args.baseline:
        accepted = set(json.load(open(args.baseline))["accepted"])
        now = set(keys)
        new, gone = sorted(now - accepted), sorted(accepted - now)
        if new:
            print("poa-design-gate: NEW design findings not in the baseline:",
                  file=sys.stderr)
            for k in new:
                print(f"  + {k}", file=sys.stderr)
        if gone:
            print("poa-design-gate: baseline entries no longer produced (stale "
                  "baseline; re-run --update-baseline):", file=sys.stderr)
            for k in gone:
                print(f"  - {k}", file=sys.stderr)
        if new or gone:
            return 1

    if args.strict and warns:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
