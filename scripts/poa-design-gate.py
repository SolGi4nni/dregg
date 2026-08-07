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

⚑ A COST ROW IS NOT A TRANSITION.  Read this before adding a "dominated action"
or "dead action" analysis to any organ.

Measured 2026-08-05 on `Dregg2.Games.PathOfAngels.NightWatchLoop` (deleted 2026-08-07 as
unreachable content — the MEASUREMENT stands, and the lesson is why this section exists;
only its source module is gone), whose 21 authored
choices each carry a `ChoiceDelta` cost row (turn, operational, supply, clueIntel,
artifacts, causesInjury).  Two choices are strictly dominated ON THAT ROW and are
nevertheless LIVE:

  * `misventRelief` is worse than `replaySharedIntervals` on every cost axis — and is
    the only choice that does not advance `encounterIndex`.  It is a retry, priced
    accordingly.  The row cannot see that.
  * `ignoreMovingClearance` is identical to `markMovingClearance` on all six delta
    fields, and artifacts can never hurt (acquisition is refused only when an artifact
    is not allowlisted).  It is live because it sets `navigationDebt` where the others
    set `entryMarked`.  The row cannot see that either.

A gate reasoning over cost rows alone would have reported both as dead content and
argued for deleting two real choices.  This is not hypothetical: it was caught twice
in one session, once by an author and once by an analysis lane whose first budget
probe reported a clue-intel binding that was actually `expectedTerminalId?`
re-selecting a terminal.  Plausible, and false.

The Lean-side statement of this was a named theorem,
`cost_row_domination_does_not_survive_the_real_transition`, proved over that reducer and
deleted with it.  Its consequence for this tool is unchanged and does not depend on the
theorem still existing: dominance and
liveness are properties of the TRANSITION (flags, phase/index advance, accumulated
evidence, downstream gates), so an organ whose per-action consequence is not fully
carried by its emitted row CANNOT be analysed from the row.  Either model the
reducer, or refuse the organ — do not analyse the row and call the answer dominance.

Note the shape that IS safe: `NightWatchCampaign`'s per-action consequence lives
entirely in its `TaskRule` table, so a row-level analysis of that organ is sound.
The distinction is whether the row is a sufficient statistic, not whether the game
looks tabular.

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
import math
import os
import sys
from collections import Counter, defaultdict, deque

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GAMES_DIR = os.path.join(REPO, "poa", "artifacts", "poag1", "games")

FAIL, WARN, INFO = "FAIL", "WARN", "INFO"

# A cost no legal play can reach.  Module scope because two rule models
# now run minimax sweeps and a per-method constant is two constants.
INF = 10 ** 6


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
            # ⚑ THE TRIGGER THIS FINDING NAMED HAS FIRED, AND IT IS READ FROM THE
            # ARTIFACT.  This was an INFO whose own text said "immaterial for a
            # public-target demo; it is a real bias the moment the target is hidden
            # and a reward rides on it".  Both halves of that condition are now
            # DECLARED in the bytes — the instance is `oracle-only` under a
            # `committed-hidden-instance` classification, and `output` pays a
            # mission reward — so the caveat is spent and the severity follows the
            # descriptor rather than a reader's memory of when it was written.
            hidden = (self.doc.get("security", {}).get("instance_visibility")
                      == "oracle-only")
            rewarded = self.doc.get("output", {}).get("contribution") is not None
            live = hidden and rewarded
            # exact per-target and per-class figures, over the whole 216-code domain
            weight = {}
            for code in self.codes:
                p = 1.0
                for band in code:
                    p *= mods[band] / 256
                weight[code] = p
            worst = max(weight.values()) / min(weight.values())
            tv = sum(abs(p - 1 / self.n) for p in weight.values()) / 2
            rep.find(self.name, "seed-modulo-bias", WARN if live else INFO,
                     "the hidden instance is not drawn uniformly"
                     if live else "the seed-to-band map is not uniform",
                     f"a byte mod {self.alphabet} yields symbol counts {lo}..{hi} out of "
                     f"256, so band symbols 0..{255 % self.alphabet} are "
                     f"{round(100 * (hi - lo) / lo, 2)}% more likely than the rest.  "
                     f"Over the whole {self.n}-target domain that is a "
                     f"{worst:.4f}x spread between the most and least likely target "
                     f"and {tv:.4f} in total variation from uniform.  " +
                     (f"⚠ ESCALATED FROM INFO: `security.instance_visibility` is "
                      f"'oracle-only' and `output.contribution` is "
                      f"{self.doc['output']['contribution']!r}, so the target is "
                      f"HIDDEN and a reward rides on it — the exact condition this "
                      f"finding was written to fire on.  The repo already owns the "
                      f"fix and does not use it here: `SeedDraw.drawBelow?` is "
                      f"rejection-sampled with `draw_is_uniform_on_every_bound` "
                      f"proved over every bound, `HiddenInstance` rejects a whole "
                      f"lane value to keep the byte stream uniform, and its docblock "
                      f"claims `drawBelow?` is the only draw used — then "
                      f"`SignalTriangulation.targetFromSeed` folds with `% "
                      f"{self.alphabet}`.  The repair is `targetFromSeed? : Digest32 "
                      f"→ Option Code` and `target_eq : some target = …`, the shape "
                      f"`BlackBoxReconstruction.orderFromRunSeed?` already has; it is "
                      f"a flag day through the fixture layer and it is NOT a design "
                      f"fork.  Do not baseline this."
                      if live else
                      "Immaterial for a public-target demo; it is a real bias the "
                      "moment the target is hidden and a reward rides on it."))

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

        ⚑ DISPATCHED ON `ruleset`, not hardcoded.  This method used to BE Salvage's
        rule, which meant a second parametric game either got Salvage's semantics
        checked against its rows — nonsense that happens to raise — or, worse, an
        analyser that quietly agreed with whatever it was handed.  A parametric
        machine with no registered rule model is REFUSED: the whole point of this
        backend is that the reconstruction is independent, and there is no
        independent reconstruction of a game nobody wrote one for.
        """
        model = PARAMETRIC_RULE_MODELS.get(self.doc.get("ruleset"))
        if model is None:
            raise Refusal(
                f"no rule model is registered for ruleset "
                f"{self.doc.get('ruleset')!r}; this backend analyses a table only "
                f"after rebuilding it from the declared semantics and checking every "
                f"row, and it will not analyse a table it cannot rebuild")
        model(self)

    def _salvage_differential(self) -> None:
        """Salvage Lock: refuse if solved, out of turns, already cleared or already
        exposed; otherwise a first exposure exposes, and a second either clears both
        plates or clears neither.  Nothing in it mentions a board, which is the
        property being checked."""
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

    def _artificer_differential(self) -> None:
        """Artificer Logic: rebuilt in full by `ManualRules`, which is written from
        the descriptor's own `manual` block and the state views and knows nothing
        about the Lean kernel's numbers."""
        ManualRules(self.doc).differential(self)

    def _descent_differential(self) -> None:
        """Deck Descent: rebuilt in full by `DescentRules`, which is written from the
        descriptor's own `shaft` block and the state views and knows nothing about
        the Lean kernel's numbers."""
        DescentRules(self.doc).differential(self)

    # ⚑ RAISED 2026-08-06.  This search was a bare `itertools.permutations` over the
    # action alphabet — 9! = 363k for a descent, and 24! for a rule-induction game,
    # which does not finish before the heat death of anything.  A cap that silently
    # gave up would be a gate that cannot go red, so the enumeration is REFINED
    # instead and an alphabet still too wide is REFUSED out loud.
    AUTOMORPHISM_SEARCH_CAP = 500_000

    def _action_profile(self, aid):
        """An invariant every automorphism preserves.

        An automorphism carries a state BIJECTION, so for each action the multiset
        of (verdict, reason) taken over ALL states is carried unchanged.  Two
        actions with different multisets can therefore never be images of one
        another, and refining by this loses no automorphism — it only removes
        permutations that the full structural test below would have rejected."""
        rows = Counter((self.trans[(s, aid)]["verdict"], self.trans[(s, aid)]["reason"])
                       for s in self.states)
        return tuple(sorted(rows.items(), key=repr))

    def automorphisms(self):
        """Permutations of the actions that extend to a state bijection preserving
        every verdict, reason and branch.  With the board hidden these should be ALL
        of them: that the opening is a free choice is the hiding, not a defect."""
        found = []
        acts = self.actions
        classes = {}
        for aid in acts:
            classes.setdefault(self._action_profile(aid), []).append(aid)
        blocks = list(classes.values())
        space = 1
        for block in blocks:
            space *= math.factorial(len(block))
        if space > self.AUTOMORPHISM_SEARCH_CAP:
            raise Refusal(
                f"the action alphabet has {len(acts)} actions in "
                f"{len(blocks)} profile classes, so the automorphism search space is "
                f"{space} permutations — past the {self.AUTOMORPHISM_SEARCH_CAP} cap. "
                f"This tool will not report a symmetry group it did not enumerate: "
                f"`opener_classes` is used to decide whether an opening is a free "
                f"choice, and a guessed group is a guessed verdict.")
        for combo in itertools.product(*[itertools.permutations(b) for b in blocks]):
            pi = {}
            for block, images in zip(blocks, combo):
                for src, dst in zip(block, images):
                    pi[src] = dst
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

        out = {
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
        # A rule model may have measured things only it can measure — the descent
        # backend's eight-board census, for one.  It goes in the summary rather than
        # into a second report, so `--json` carries everything the run knows.
        out.update(getattr(self, "extra_summary", {}))
        return out


# ---------------------------------------------------------------------------
# the descent rule model — a second, independent statement of Deck Descent
# ---------------------------------------------------------------------------

class DescentRules:
    """Deck Descent's rules, restated here and checked against every emitted row.

    ⚑ WHY THIS IS NOT `MachineFamilyGame`.  Descent is an ORACLE game, not a family
    of instantiated machines.  Its state carries `dark` — the ABSENCE of knowledge
    about a chamber — and the openness predicate never reads the board: a refusal is
    a fact the player can see, which the kernel states as `branches_agree_on_refusal`
    and which this file re-checks row by row below.  Emitting it as a machine family
    would declare `per-run-open`, and the family backend's dominance pass would then
    report `survey` and blind `shore` as DOMINATED — they spend a unit of the clock
    and move no body, so against a KNOWN board they are pure loss.  That verdict is
    exactly backwards: those two verbs are the only ones that buy information, and
    the whole decision in this game is when to buy it.  The information they buy is
    invisible to any analysis that has already been told the answer.

    ⚑ A COST ROW IS NOT A TRANSITION — and this backend does not compute one.  The
    tool's own header records the nightwatch measurement
    (`cost_row_domination_does_not_survive_the_real_transition`): two NightWatchLoop
    choices were dominated on every axis of their delta row and were nevertheless live.
    So nothing below ranks an action by what it spends.  Every number this class
    reports comes from walking the REAL transition — the same one the emitted table
    names — over the real state space.

    ## What is reconstructed, and from what

    Everything comes from the descriptor: the `shaft` block (topology, budgets,
    capacity, bank target, per-chamber relic counts, forfeit order, which lore
    damages) and the emitted state VIEWS.  Nothing is read from the Lean module.  In particular the four lore values
    are not hardcoded to their names:

      * `dark` is whatever every chamber reads in the INITIAL state view;
      * the two PASSAGES are read off the resolve rows — a row that consults the
        instance names two successors whose views differ in exactly one chamber's
        lore, and that chamber's two values ARE the two readings;
      * `shored` is the one declared lore value left over;
      * `sound` and `flooded` are then separated by `shaft.damaging_lore`, not by
        the `on_match` / `on_mismatch` labels — so the claim that `on_match` is the
        sound branch is CHECKED here rather than believed.

    ## What is checked

      1. every one of the emitted rows, verdict + reason + successor ids;
      2. every emitted view's derived fields (capacity, clock, doom, terminality);
      3. the emitted state set IS the two-branch closure of the initial state;
      4. the eight-board census — reachable states, outcome-changing forks, doomed
         states — computed by this file's own search over this file's own
         reconstruction, and then compared against the kernel's claim.

    Point 4 is the one that matters.  The kernel asserts the triple in
    `DeckDescent.family_shape_is_measured` by `native_decide` over its own
    definitions; this class arrives at it by simulating the descriptor a client
    downloads.  Those are two independent sources and the comparison is a gate.  A
    disagreement is a FAIL and it is the headline, because exactly one of the two
    is then wrong about the game people would be playing.
    """

    # The kernel's claim, as a claim.  ⚠ This is NOT an input to anything computed
    # below — the census is complete before this dict is consulted, and consulting it
    # can only produce a finding.  It is here so that a drift between the proved
    # numbers and the emitted descriptor is LOUD rather than a thing someone notices
    # by reading two files side by side.
    # (Before the east spur's second relic: 3905 / 1145 / 2059.)
    KERNEL_FAMILY_SHAPE = {
        "reachable_states": 4688,
        "outcome_forks": 1360,
        "doomed_states": 2469,
        "source": "DeckDescent.family_shape_is_measured (native_decide)",
    }

    REFUSAL_VOCABULARY = {
        "run-banked", "run-doomed", "no-air", "no-passage", "already-read",
        "no-shoring", "already-safe", "not-in-a-chamber", "chamber-emptied",
        "over-capacity", "at-the-hatch", "not-at-the-hatch", "short-sling",
    }

    def __init__(self, doc: dict) -> None:
        self.doc = doc
        shaft = doc.get("shaft")
        if not isinstance(shaft, dict):
            raise Refusal("descent descriptor carries no `shaft` block, so there is "
                          "nothing to rebuild the rules from")
        budgets = shaft["budgets"]
        self.air_budget = budgets["air"]
        self.shoring_budget = budgets["shoring"]
        self.base_capacity = budgets["base_capacity"]
        self.bank_target = budgets["bank_target"]
        self.air_per_action = shaft["air_per_action"]
        if self.air_per_action != 1:
            raise Refusal("this model prices every action at one unit of air; the "
                          f"descriptor declares {self.air_per_action}")
        if "relics_per_chamber" in shaft:
            raise Refusal(
                "the shaft declares `relics_per_chamber`, the pre-second-relic "
                "shape.  The kernel counts relics PER CHAMBER now (the east spur "
                "holds two); re-emit the descriptor from DeckDescentEmitMain "
                "rather than reinterpreting a scalar")
        self.relic_count = dict(shaft["relic_count"])
        self.surface = shaft["surface"]
        self.nodes = list(shaft["nodes"])
        self.chambers = list(shaft["chambers"])
        self.parent = dict(shaft["parent"])
        self.main_child = dict(shaft["main_child"])
        self.spur_child = dict(shaft["spur_child"])
        self.forfeit_order = list(shaft["forfeit_order"])
        self.lore_values = list(shaft["lore"])
        self.damaging = set(shaft["damaging_lore"])
        self.dist = {}
        for p, q, d in shaft["crossings"]:
            self.dist[(p, q)] = d

        if self.surface not in self.nodes:
            raise Refusal(f"the surface {self.surface!r} is not one of the nodes")
        if sorted(self.nodes) != sorted(set(self.nodes)):
            raise Refusal("the shaft names a node twice")
        if set(self.chambers) | {self.surface} != set(self.nodes):
            raise Refusal("the chambers and the surface do not exhaust the nodes")
        if set(self.relic_count) != set(self.chambers):
            raise Refusal("`relic_count` does not name exactly the chambers")
        for c, n in self.relic_count.items():
            if not isinstance(n, int) or n < 1:
                raise Refusal(f"chamber {c} declares {n!r} relics; every chamber "
                              f"holds at least one")
        if sorted(self.forfeit_order) != sorted(self.chambers):
            raise Refusal("the forfeit order is not a permutation of the chambers")
        for p in self.nodes:
            for q in self.nodes:
                if (p, q) not in self.dist:
                    raise Refusal(f"the crossing table has no entry for {p} -> {q}")
        for n in self.nodes:
            if self.dist[(n, n)] != 0:
                raise Refusal(f"the crossing table charges {n} for standing still")
            if self.dist[(n, self.surface)] != shaft["crossings_to_hatch"][n]:
                raise Refusal(f"`crossings_to_hatch` and `crossings` disagree at {n}")
        for p in self.nodes:
            for q in self.nodes:
                if self.dist[(p, q)] != self.dist[(q, p)]:
                    raise Refusal(f"the crossing table is not symmetric at {p}/{q}")
        if not self.damaging:
            raise Refusal("no lore value damages, so no crossing can ever cost a body "
                          "and the shaft holds no risk at all")

        self._bank_cache = {}

    # -- the lore alphabet, derived rather than named ------------------------

    def learn_alphabet(self, game) -> None:
        """Separate the four lore values without trusting any of their names."""
        init_view = game.states[game.initial]["view"]
        init_lore = {init_view["lore"][c] for c in self.chambers}
        if len(init_lore) != 1:
            raise Refusal("the initial state does not read the same on every chamber, "
                          "so the descriptor leaks a chamber before anything is done")
        self.dark = init_lore.pop()

        passages = set()
        for (sid, aid), t in game.trans.items():
            if t["verdict"] != "resolve":
                continue
            m = game.states[t["on_match"]]["view"]["lore"]
            f = game.states[t["on_mismatch"]]["view"]["lore"]
            differ = [c for c in self.chambers if m[c] != f[c]]
            if len(differ) != 1:
                raise Refusal(
                    f"{sid}/{aid} consults the instance but its two branches differ "
                    f"in {len(differ)} chambers' lore; a row that reveals more than "
                    f"one bit is not a row this model can rebuild")
            c = differ[0]
            if game.states[sid]["view"]["lore"][c] != self.dark:
                raise Refusal(f"{sid}/{aid} re-reads a chamber that is already known")
            passages.add(m[c])
            passages.add(f[c])
        if len(passages) != 2:
            raise Refusal(f"the emitted rows reveal {len(passages)} distinct passage "
                          f"readings; this model needs exactly two")
        damaging_passages = passages & self.damaging
        if len(damaging_passages) != 1:
            raise Refusal("exactly one of the two passage readings must damage; "
                          f"{sorted(passages)} against damaging {sorted(self.damaging)}")
        self.flooded = damaging_passages.pop()
        self.sound = (passages - {self.flooded}).pop()
        left = [v for v in self.lore_values
                if v not in (self.dark, self.sound, self.flooded)]
        if len(left) != 1:
            raise Refusal(f"the declared lore alphabet {self.lore_values} does not "
                          f"leave exactly one value for a shored passage")
        self.shored = left[0]
        if self.shored in self.damaging:
            raise Refusal("a shored passage damages, so shoring buys nothing")
        self.shoreable = {self.dark} | self.damaging

    # -- states --------------------------------------------------------------
    #
    # A state is (node, air, shoring, damage, lore, taken, sling, banked), with
    # `taken` and `sling` per-chamber COUNTS — the east spur holds two relics, so
    # a chamber set would collapse a real distinction.  The emitted view carries
    # every one of those and nothing else that is not derived from them.

    def state_of_view(self, view: dict) -> tuple:
        if "emptied" in view or not isinstance(view.get("taken"), dict) \
                or not isinstance(view.get("sling"), dict):
            raise Refusal(
                "state views carry the pre-relic-count shape (`emptied`/chamber "
                "lists); the kernel counts relics per chamber now — re-emit the "
                "descriptor from DeckDescentEmitMain")
        return (
            view["node"], view["air"], view["shoring"], view["damage"],
            tuple(view["lore"][c] for c in self.chambers),
            tuple(view["taken"][c] for c in self.chambers),
            tuple(view["sling"][c] for c in self.chambers),
            bool(view["banked"]),
        )

    def capacity(self, s) -> int:
        return max(0, self.base_capacity - s[3])

    def turns(self, s) -> int:
        return self.air_budget - s[1]

    def held(self, s) -> int:
        return sum(s[6])

    def cheapest_bank(self, s) -> int:
        """`shaft.reserve`, read as arithmetic: the cheapest ordered collection of
        the relics still needed — a chamber counts once per relic it still holds,
        one lift per relic — plus the extraction, on the most favourable board still
        consistent with what the run has seen.  A dark chamber is assumed to cost
        nothing, and a state this refuses is one no board rescues.  Standing still
        costs nothing (`dist[(c, c)] == 0`), so a plan that lifts twice in the same
        chamber prices the second relic at exactly one lift — which is what "a
        second relic at the SAME distance" means."""
        key = (s[0], s[5], s[6])
        hit = self._bank_cache.get(key)
        if hit is not None:
            return hit
        node = s[0]
        if self.held(s) >= self.bank_target:
            out = self.dist[(node, self.surface)] + 1
        else:
            need = self.bank_target - self.held(s)
            avail = []
            for i, c in enumerate(self.chambers):
                avail.extend([c] * (self.relic_count[c] - s[5][i]))
            best = self.air_budget + 1
            for seq in set(itertools.permutations(avail, need)):
                here, cost = node, 0
                for c in seq:
                    cost += self.dist[(here, c)]
                    here = c
                cost += self.dist[(here, self.surface)]
                best = min(best, cost + need + 1)
            out = best
        self._bank_cache[key] = out
        return out

    def can_still_bank(self, s) -> bool:
        return (not s[7]
                and self.capacity(s) >= self.bank_target
                and self.cheapest_bank(s) <= s[1])

    def doomed(self, s) -> bool:
        return not s[7] and not self.can_still_bank(s)

    # -- the transition ------------------------------------------------------

    def target(self, node: str, line: str):
        if line == "spur":
            return self.spur_child.get(node)
        if line == "main":
            return self.main_child.get(node)
        return None

    def is_open(self, s, kind: str, line: str) -> bool:
        if not self.can_still_bank(s):
            return False
        if s[1] <= 0:
            return False
        node = s[0]
        c = self.target(node, line)
        idx = {ch: i for i, ch in enumerate(self.chambers)}
        if kind == "survey":
            return c is not None and s[4][idx[c]] == self.dark
        if kind == "shore":
            return s[2] > 0 and c is not None and s[4][idx[c]] in self.shoreable
        if kind == "descend":
            return c is not None
        if kind == "lift":
            if node == self.surface:
                return False
            i = idx[node]
            return (s[5][i] < self.relic_count[node]
                    and self.held(s) + 1 <= self.capacity(s))
        if kind == "ascend":
            return node != self.surface
        if kind == "extract":
            return node == self.surface and self.held(s) >= self.bank_target
        raise Refusal(f"unknown action kind {kind!r}")

    def refusal_reason(self, s, kind: str, line: str) -> str:
        """The FIRST conjunct that failed, in the order openness tests them — so a
        client renders the reason that actually applies and not a plausible one."""
        if s[7]:
            return "run-banked"
        if not self.can_still_bank(s):
            return "run-doomed"
        if s[1] <= 0:
            return "no-air"
        node = s[0]
        c = self.target(node, line)
        idx = {ch: i for i, ch in enumerate(self.chambers)}
        if kind == "survey":
            return "no-passage" if c is None else "already-read"
        if kind == "shore":
            if s[2] == 0:
                return "no-shoring"
            return "no-passage" if c is None else "already-safe"
        if kind == "descend":
            return "no-passage"
        if kind == "lift":
            if node == self.surface:
                return "not-in-a-chamber"
            return ("chamber-emptied" if s[5][idx[node]] >= self.relic_count[node]
                    else "over-capacity")
        if kind == "ascend":
            return "at-the-hatch"
        if kind == "extract":
            return "not-at-the-hatch" if node != self.surface else "short-sling"
        raise Refusal(f"unknown action kind {kind!r}")

    def take_damage(self, s) -> tuple:
        damage = s[3] + 1
        cap = max(0, self.base_capacity - damage)
        sling = list(s[6])
        if cap < sum(sling):
            for c in self.forfeit_order:
                i = self.chambers.index(c)
                if sling[i] > 0:
                    sling[i] -= 1
                    break
        return (s[0], s[1], s[2], damage, s[4], s[5], tuple(sling), s[7])

    def cross(self, s, lore_value: str) -> tuple:
        return self.take_damage(s) if lore_value in self.damaging else s

    def step(self, s, kind: str, line: str, reading: str) -> tuple:
        """The transition with openness already decided.  `reading` is what the board
        says about the chamber this action reaches for; it is consulted only where a
        dark passage is actually resolved."""
        node, air, shoring, damage, lore, taken, sling, banked = s
        idx = {ch: i for i, ch in enumerate(self.chambers)}
        c = self.target(node, line)
        if kind == "survey":
            new = list(lore)
            new[idx[c]] = reading
            return (node, air - 1, shoring, damage, tuple(new), taken, sling, banked)
        if kind == "shore":
            new = list(lore)
            new[idx[c]] = self.shored
            return (node, air - 1, shoring - 1, damage, tuple(new), taken, sling,
                    banked)
        if kind == "descend":
            seen = reading if lore[idx[c]] == self.dark else lore[idx[c]]
            new = list(lore)
            new[idx[c]] = seen
            return self.cross(
                (c, air - 1, shoring, damage, tuple(new), taken, sling, banked), seen)
        if kind == "lift":
            i = idx[node]
            t, g = list(taken), list(sling)
            t[i] += 1
            g[i] += 1
            return (node, air - 1, shoring, damage, lore, tuple(t), tuple(g), banked)
        if kind == "ascend":
            i = idx[node]
            return self.cross(
                (self.parent[node], air - 1, shoring, damage, lore, taken, sling,
                 banked), lore[i])
        if kind == "extract":
            return (node, air - 1, shoring, damage, lore, taken, sling, True)
        raise Refusal(f"unknown action kind {kind!r}")

    def row_for(self, s, kind: str, line: str):
        """`(verdict, reason, next, on_match, on_mismatch)` — an accept exactly when
        the two readings agree, which is exactly when the action does not consult the
        board."""
        if not self.is_open(s, kind, line):
            return ("refuse", self.refusal_reason(s, kind, line), None, None, None)
        m = self.step(s, kind, line, self.sound)
        f = self.step(s, kind, line, self.flooded)
        if m == f:
            return ("accept", None, m, None, None)
        return ("resolve", None, None, m, f)

    def successor(self, s, kind: str, line: str, board: dict):
        """The real transition on one board — what a run actually does."""
        if not self.is_open(s, kind, line):
            return None
        c = self.target(s[0], line)
        return self.step(s, kind, line, board[c] if c is not None else self.sound)

    # -- the differential ----------------------------------------------------

    def differential(self, game) -> None:
        self.learn_alphabet(game)
        meta = {}
        for aid in game.actions:
            m = game.action_meta[aid]
            kind, line = m.get("kind"), m.get("line")
            if kind is None or line is None:
                raise Refusal(f"action {aid} declares no kind/line, so its target "
                              f"cannot be rebuilt from the shaft")
            if line not in ("main", "spur", "here"):
                raise Refusal(f"action {aid} declares an unknown line {line!r}")
            meta[aid] = (kind, line)

        # 1. every view is a state, and the ids separate them
        state_of = {}
        id_of = {}
        for sid, s in game.states.items():
            st = self.state_of_view(s["view"])
            if st in id_of:
                raise Refusal(f"states {id_of[st]} and {sid} carry the same view, so "
                              f"the emitted id is not a function of the state")
            id_of[st] = sid
            state_of[sid] = st
        self.id_of = id_of
        self.state_of = state_of

        # 2. every derived field of every view, rebuilt
        for sid, s in game.states.items():
            st = state_of[sid]
            v = s["view"]
            if v["capacity"] != self.capacity(st):
                raise Refusal(f"{sid} reports capacity {v['capacity']}, the shaft "
                              f"gives {self.capacity(st)}")
            if v["turns"] != self.turns(st):
                raise Refusal(f"{sid} reports {v['turns']} turns used against an air "
                              f"budget of {self.air_budget} and {st[1]} left")
            if bool(v["doomed"]) != self.doomed(st):
                raise Refusal(
                    f"{sid} reports doomed={v['doomed']}; rebuilding the reserve from "
                    f"`shaft.reserve` gives {self.doomed(st)}.  A client that greys a "
                    f"run out is telling a player their descent is over, so this is "
                    f"not a cosmetic field")
            if bool(v["solved"]) != st[7] or bool(s["terminal"]) != st[7]:
                raise Refusal(f"{sid} disagrees with its own view about being banked")
            if st[1] > self.air_budget or st[2] > self.shoring_budget:
                raise Refusal(f"{sid} holds more than the declared budget")

        # 3. every row
        seen_reasons = set()
        for sid, st in state_of.items():
            for aid in game.actions:
                kind, line = meta[aid]
                verdict, reason, nxt, on_m, on_f = self.row_for(st, kind, line)
                t = game.trans[(sid, aid)]
                if t["verdict"] != verdict:
                    raise Refusal(
                        f"{sid}/{aid}: the table says {t['verdict']}, the rebuilt "
                        f"rule says {verdict}")
                if verdict == "refuse":
                    seen_reasons.add(reason)
                    if t["reason"] != reason:
                        raise Refusal(
                            f"{sid}/{aid}: the table refuses for {t['reason']!r}, the "
                            f"rebuilt rule refuses for {reason!r}")
                elif verdict == "accept":
                    self._same_state(game, sid, aid, "next", t["next"], nxt)
                else:
                    self._same_state(game, sid, aid, "on_match", t["on_match"], on_m)
                    self._same_state(game, sid, aid, "on_mismatch",
                                     t["on_mismatch"], on_f)

        unknown = seen_reasons - self.REFUSAL_VOCABULARY
        if unknown:
            raise Refusal(f"the rebuilt rule refuses for reasons this model does not "
                          f"declare: {sorted(unknown)}")

        # 4. the emitted state set IS the two-branch closure of the initial state
        closure = {state_of[game.initial]}
        queue = deque([state_of[game.initial]])
        while queue:
            st = queue.popleft()
            for aid in game.actions:
                kind, line = meta[aid]
                _, _, nxt, on_m, on_f = self.row_for(st, kind, line)
                for n in (nxt, on_m, on_f):
                    if n is not None and n not in closure:
                        closure.add(n)
                        queue.append(n)
        emitted = set(state_of.values())
        if closure != emitted:
            extra = len(emitted - closure)
            missing = len(closure - emitted)
            raise Refusal(
                f"the emitted state set is not the closure of the initial state: "
                f"{extra} declared state(s) are unreachable under the rebuilt rule "
                f"and {missing} reachable state(s) are not declared")

        self.census(game)

    def _same_state(self, game, sid, aid, slot, emitted_id, mine) -> None:
        want = self.id_of.get(mine)
        if want is None:
            raise Refusal(f"{sid}/{aid} {slot}: the rebuilt rule reaches a state the "
                          f"descriptor does not declare")
        if emitted_id != want:
            raise Refusal(f"{sid}/{aid} {slot}: the table names {emitted_id}, the "
                          f"rebuilt rule reaches {want}")

    # -- the census ----------------------------------------------------------

    def census(self, game) -> None:
        """Walk the REAL transition on each board of the family and count.

        The board is one reading per chamber, and the readings are the two this class
        derived from the resolve rows — so the family is enumerated here, from the
        descriptor, and not taken from anywhere.
        """
        rep, name = game.rep, game.name
        meta = {aid: (game.action_meta[aid]["kind"], game.action_meta[aid]["line"])
                for aid in game.actions}
        init = self.state_of[game.initial]
        readings = (self.sound, self.flooded)

        boards = [dict(zip(self.chambers, combo))
                  for combo in itertools.product(readings, repeat=len(self.chambers))]

        per_board = []
        total_reach = total_fork = total_doom = 0
        for board in boards:
            reach = {init}
            queue = deque([init])
            while queue:
                st = queue.popleft()
                for aid in game.actions:
                    kind, line = meta[aid]
                    n = self.successor(st, kind, line, board)
                    if n is not None and n not in reach:
                        reach.add(n)
                        queue.append(n)
            forks = 0
            for st in reach:
                lives = dies = False
                for aid in game.actions:
                    kind, line = meta[aid]
                    n = self.successor(st, kind, line, board)
                    if n is None:
                        continue
                    if self.doomed(n):
                        dies = True
                    else:
                        lives = True
                if lives and dies:
                    forks += 1
            doom = sum(1 for st in reach if self.doomed(st))
            per_board.append({
                "board": {c: board[c] for c in self.chambers},
                "reachable": len(reach), "forks": forks, "doomed": doom,
            })
            total_reach += len(reach)
            total_fork += forks
            total_doom += doom

        game.extra_summary = {
            "instance_family_size": len(boards),
            "family_reachable_states": total_reach,
            "outcome_forks": total_fork,
            "family_doomed_states": total_doom,
            "per_board": per_board,
            "kernel_family_shape": dict(self.KERNEL_FAMILY_SHAPE),
            "lore_alphabet": {
                "unknown": self.dark, "sound": self.sound,
                "flooded": self.flooded, "shored": self.shored,
            },
        }

        # ⚑ the cross-check.  Two independent sources, compared.
        k = self.KERNEL_FAMILY_SHAPE
        mine = (total_reach, total_fork, total_doom)
        theirs = (k["reachable_states"], k["outcome_forks"], k["doomed_states"])
        if mine != theirs:
            rep.find(name, "kernel-census-disagreement", FAIL,
                     "the gate and the kernel disagree about the shape of the family",
                     f"walking the emitted descriptor gives "
                     f"{total_reach} reachable / {total_fork} forks / {total_doom} "
                     f"doomed across {len(boards)} boards; {k['source']} asserts "
                     f"{theirs[0]} / {theirs[1]} / {theirs[2]}.  These are independent "
                     f"— one is a compiled evaluation of the kernel's own definitions, "
                     f"the other is a simulation of the bytes a client downloads — so a "
                     f"disagreement means the descriptor and the engine are not the "
                     f"same game.")
        else:
            rep.find(name, "family-shape-agrees", INFO,
                     f"{total_reach} reachable states, {total_fork} outcome-changing "
                     f"forks and {total_doom} doomed states, arrived at twice",
                     f"this tool rebuilt the rules from `shaft`, checked all "
                     f"{len(game.trans)} emitted rows against them, then walked the "
                     f"real transition over all {len(boards)} boards of the family.  It "
                     f"gets {total_reach} / {total_fork} / {total_doom}, and "
                     f"{k['source']} independently asserts the same triple.  A pin "
                     f"against its own definition is decoration; this is two sources.")

        if total_fork == 0:
            rep.find(name, "no-outcome-fork", FAIL,
                     "no reachable state offers a choice that changes the outcome",
                     "every legal action from every reachable state leaves the run in "
                     "the same condition, so the player's decisions are decoration.")
        if total_doom == 0:
            rep.find(name, "cannot-be-lost", FAIL,
                     "no reachable state is doomed, so the descent cannot be lost",
                     "a run that cannot fail is not an expedition.")

        dead_boards = [b for b in per_board if b["forks"] == 0]
        if dead_boards:
            rep.find(name, "board-without-a-decision", WARN,
                     f"{len(dead_boards)} board(s) of the family offer no fork",
                     f"a run drawn onto one of these plays itself: {dead_boards[:3]}")

        spans = {b["reachable"] for b in per_board}
        if len(spans) == 1:
            rep.find(name, "boards-are-interchangeable", WARN,
                     "every board of the family has the same reachable count",
                     f"all {len(boards)} instances span {spans.pop()} states, which is "
                     f"consistent with a family whose members differ only by relabelling "
                     f"— check that the shaft is not symmetric under permuting the "
                     f"chambers, or the hidden bits buy less than they appear to.")

        shapes = {(b["reachable"], b["forks"], b["doomed"]) for b in per_board}
        game.extra_summary["distinct_board_shapes"] = len(shapes)
        if len(shapes) < len(boards):
            rep.find(name, "the-family-collapses", WARN,
                     f"the {len(boards)} boards of the family produce only "
                     f"{len(shapes)} distinct shapes",
                     f"two hidden draws that yield the same reachable count, the same "
                     f"fork count and the same doom count are the same game under a "
                     f"relabelling, so the bits that distinguish them buy a player "
                     f"nothing.  {len(boards)} draws collapsing to {len(shapes)} is "
                     f"{math.log2(len(boards)) - math.log2(len(shapes)):.2f} of a bit "
                     f"of the instance doing no work.")

        self.floors(game, boards)
        # the two spurs, priced against each other — AFTER the floors, because the
        # sharp question about a junction is answered in minimax values and not in
        # the topology.
        self.spur_symmetry(game, per_board)

    def floors(self, game, boards) -> None:
        """The three floors, computed exactly rather than estimated.

        ⚑ `worst_case_optimal` is a real MINIMAX, not the longest legal play.  The
        oracle answers adversarially, and it may: each chamber's bit is consulted at
        most once — a resolve row fires only on a `dark` passage, which
        `learn_alphabet` checks — so EVERY answer sequence is realised by some board
        of the family, and an adversary who picks answers is exactly an adversary who
        picked a board.  The value is therefore the ordinary minimax on the knowledge
        machine: a player minimises over legal actions, the oracle maximises over the
        two branches of a resolve row.

        The recursion terminates without a fixpoint pass because every action spends
        a unit of air, so the machine is a DAG layered by the clock.
        """
        meta = {aid: (game.action_meta[aid]["kind"], game.action_meta[aid]["line"])
                for aid in game.actions}
        rep, name = game.rep, game.name
        INF = float("inf")

        # minimax — the guaranteed cost, against any board still consistent
        value = {}
        for st in sorted(self.state_of.values(), key=lambda s: s[1]):
            if st[7]:
                value[st] = 0
                continue
            best = INF
            for aid in game.actions:
                kind, line = meta[aid]
                _, _, nxt, on_m, on_f = self.row_for(st, kind, line)
                branches = [b for b in (nxt, on_m, on_f) if b is not None]
                if not branches:
                    continue
                best = min(best, 1 + max(value.get(b, INF) for b in branches))
            value[st] = best
        guaranteed = value[self.state_of[game.initial]]
        self.value = value

        # the luckiest line — shortest accepted path to a bank on the kindest board
        luckiest = INF
        for board in boards:
            depth = {self.state_of[game.initial]: 0}
            queue = deque([self.state_of[game.initial]])
            while queue:
                st = queue.popleft()
                if st[7]:
                    luckiest = min(luckiest, depth[st])
                    continue
                for aid in game.actions:
                    kind, line = meta[aid]
                    n = self.successor(st, kind, line, board)
                    if n is not None and n not in depth:
                        depth[n] = depth[st] + 1
                        queue.append(n)

        info_floor = ceil_log(len(boards), 2)
        game.extra_summary["information_floor_loose"] = info_floor
        game.extra_summary["information_floor_tight"] = info_floor
        game.extra_summary["execution_floor_as_designed"] = (
            None if luckiest == INF else luckiest)
        game.extra_summary["execution_floor_as_emitted"] = (
            None if guaranteed == INF else guaranteed)
        game.extra_summary["worst_case_optimal"] = (
            None if guaranteed == INF else guaranteed)

        if guaranteed == INF:
            rep.find(name, "not-winnable-against-the-oracle", FAIL,
                     "no strategy banks the target against a worst-case oracle",
                     f"the minimax value of the opening position is infinite: for every "
                     f"line the player can take, some board of the family still "
                     f"consistent with what has been seen dooms it.  A descent that "
                     f"cannot be won by playing well is a coin, not an expedition.")
            game.extra_summary["budget_binds"] = True
            game.extra_summary["budget_slack"] = None
            return

        binds = guaranteed >= game.budget
        game.extra_summary["budget_binds"] = binds
        game.extra_summary["budget_slack"] = game.budget - guaranteed

        if guaranteed == game.budget:
            rep.find(name, "budget-binds-exactly", INFO,
                     "the air budget binds exactly under optimal play",
                     f"the exact minimax value of the opening position is "
                     f"{guaranteed} and `action_limit` is {game.budget}; slack 0.  "
                     f"Every unit of the clock is load-bearing, and a player who "
                     f"spends one badly cannot recover it — which is what makes the "
                     f"scout decision at the mouth a decision.  The luckiest line — "
                     f"the shortest accepted path to a bank on the kindest board — "
                     f"takes {luckiest}, so the gap between fortune and guarantee is "
                     f"{guaranteed - luckiest} units.")
        elif guaranteed > game.budget:
            rep.find(name, "budget-cannot-be-met", FAIL,
                     "optimal play needs more air than the descriptor allows",
                     f"minimax {guaranteed} against `action_limit` {game.budget}: the "
                     f"run is over before a guaranteed line can finish.")
        else:
            rep.find(name, "budget-has-slack", WARN,
                     f"the air budget has {game.budget - guaranteed} unit(s) of slack "
                     f"under optimal play",
                     f"minimax {guaranteed} against `action_limit` {game.budget}.  "
                     f"Spare clock means a player can buy information they do not need "
                     f"to buy, which is how a decision stops being one.")

        if luckiest == guaranteed:
            rep.find(name, "fortune-buys-nothing", WARN,
                     "the kindest board costs exactly what the cruellest guarantee does",
                     f"both are {guaranteed} actions, so the hidden bits change the "
                     f"route but never the length, and a player learns nothing from "
                     f"finishing early because nobody ever does.")

    def spur_symmetry(self, game, per_board) -> None:
        """⚑ Are the two branches of the junction the same branch?

        The junction is the whole reason this game is not a corridor, and it is worth
        exactly as much as the two spurs differ.  Topological symmetry is the cheap
        half of the answer: if swapping them preserves the crossing table then the two
        names are interchangeable BEFORE anything is learnt.

        ⚑ The expensive half is the one that matters, and it is measured here rather
        than assumed.  A junction is a real decision only when which way is right
        DEPENDS ON WHAT IS KNOWN — that is, when there are reachable positions at the
        junction where the main line is strictly better in minimax AND reachable
        positions where the spur is.  A junction where one side is never worse is a
        labelled corridor no matter how asymmetric the topology looks, and topology
        alone cannot tell the two apart.  So this counts both.
        """
        junctions = [n for n in self.nodes
                     if n in self.main_child and n in self.spur_child]
        if len(junctions) != 1:
            if not junctions:
                game.rep.find(game.name, "no-junction", WARN,
                              "the shaft has no node with two children",
                              "every descent walks the same corridor, so there is no "
                              "branch to commit to and no spur to regret.")
            return
        j = junctions[0]
        a, b = self.main_child[j], self.spur_child[j]
        swap = {a: b, b: a}
        sigma = lambda n: swap.get(n, n)
        # σ is an automorphism of the shaft exactly when it preserves every crossing
        # AND every prize: two spurs with different relic counts are different
        # branches even when the walking is identical.
        same_ring = all(self.dist[(sigma(p), sigma(q))] == self.dist[(p, q)]
                        for p in self.nodes for q in self.nodes)
        same_depth = self.dist[(a, self.surface)] == self.dist[(b, self.surface)]
        same_parent = self.parent[a] == self.parent[b]
        same_prize = self.relic_count[a] == self.relic_count[b]
        symmetric = same_depth and same_parent and same_ring and same_prize

        # how often the choice at the junction actually goes each way
        value = getattr(self, "value", {})
        meta = {aid: (game.action_meta[aid]["kind"], game.action_meta[aid]["line"])
                for aid in game.actions}
        main_aid = next((aid for aid, (k, l) in meta.items()
                         if k == "descend" and l == "main"), None)
        spur_aid = next((aid for aid, (k, l) in meta.items()
                         if k == "descend" and l == "spur"), None)
        main_better = spur_better = tied = 0
        if main_aid and spur_aid:
            for st in self.state_of.values():
                if st[0] != j or st[7]:
                    continue
                vals = []
                for aid in (main_aid, spur_aid):
                    kind, line = meta[aid]
                    _, _, nxt, on_m, on_f = self.row_for(st, kind, line)
                    br = [x for x in (nxt, on_m, on_f) if x is not None]
                    vals.append(1 + max(value.get(x, float("inf")) for x in br)
                                if br else None)
                if vals[0] is None or vals[1] is None:
                    continue
                if vals[0] < vals[1]:
                    main_better += 1
                elif vals[1] < vals[0]:
                    spur_better += 1
                else:
                    tied += 1
        game.extra_summary["junction_main_better"] = main_better
        game.extra_summary["junction_spur_better"] = spur_better
        game.extra_summary["junction_tied"] = tied

        split = (f"standing at {j} with both descents legal, the main line is strictly "
                 f"better in {main_better} reachable position(s), the spur in "
                 f"{spur_better}, and they are worth the same in {tied}")

        if main_better and spur_better:
            game.rep.find(
                game.name, "the-junction-is-a-decision", INFO,
                f"which branch of {j} is right depends on what has been learnt",
                f"{split}.  Both directions occur, so the fork is a genuine decision "
                f"and not a labelled corridor — a player who reads the lore differently "
                f"walks a different way and is right to." +
                (f"  ⚠ It is a decision that only EXISTS after information: the shaft "
                 f"is symmetric under swapping {a} and {b}, so on turn one the two are "
                 f"interchangeable and the {main_better}/{spur_better} split is the "
                 f"symmetry answering itself." if symmetric else ""))
        elif main_better or spur_better:
            winner, loser = ((a, b) if main_better else (b, a))
            game.rep.find(
                game.name, "the-junction-is-a-labelled-corridor", WARN,
                f"{winner} is never worse than {loser} anywhere at {j}",
                f"{split}.  One side of a fork that is never worse is not a branch, it "
                f"is the route with a second name on it — and this is what a shaft "
                f"looks like when a spur has been made asymmetric by making it more "
                f"EXPENSIVE.  ⚑ Measured 2026-08-06 on this very game: charging the "
                f"spur two units of air to enter (with or without a second relic in it) "
                f"turns an 18/18 split into 26/0 and drops the family's "
                f"outcome-changing forks from 1145 to 749.  A spur nobody takes is "
                f"worse than a spur that is only a name.")
        else:
            game.rep.find(
                game.name, "the-junction-is-a-coin", WARN,
                f"the two branches of {j} are worth exactly the same, always",
                f"{split}.  No reachable position at the junction prefers either "
                f"branch, so the commitment the fork is supposed to represent costs "
                f"the player nothing to get wrong.")

        if symmetric:
            game.rep.find(
                game.name, "the-spurs-are-one-spur", WARN,
                f"the shaft is symmetric under swapping {a} and {b}",
                f"both sit {self.dist[(a, self.surface)]} crossings from "
                f"{self.surface} under the same parent, hold the same "
                f"{self.relic_count[a]} relic(s), and the crossing table is invariant "
                f"under the swap.  The cost is exact and it is visible in the census "
                f"above: the draws collapse to "
                f"{game.extra_summary.get('distinct_board_shapes')} distinct shapes, "
                f"because a board and its mirror are the same game.  ⚑ The repair "
                f"that WORKS is not the obvious one.  Measured 2026-08-06 over this "
                f"model, on deck-descent: making {b} costlier to reach kills the "
                f"decision (18/18 became 26/0 — see the junction finding), while a "
                f"SECOND RELIC on {b} at the SAME distance broke the mirror and kept "
                f"the branch (all eight draws distinct, family forks 1145 -> 1360, "
                f"junction 18/19, clock still binding at 9).  That repair LANDED the "
                f"same day — `Chamber.relicCount` in `DeckDescent` — so if this "
                f"finding is firing, either the game has regressed to a mirror or a "
                f"new symmetric shaft is repeating the old mistake.  Break the prize, "
                f"not the price.")


# A parametric table is analysed only by a tool that can rebuild it.  Registering a
# ruleset here is the assertion "there is a second, independent statement of these
# rules in this file, and every emitted row is checked against it".  An unregistered
# ruleset is refused rather than measured.
PARAMETRIC_RULE_MODELS = {
    "salvage-v2": ParametricMachineGame._salvage_differential,
    "descent-v1": ParametricMachineGame._descent_differential,
    "artificer-v1": ParametricMachineGame._artificer_differential,
}


# ---------------------------------------------------------------------------
# the artificer rule model — a second, independent statement of Artificer Logic
# ---------------------------------------------------------------------------
class ManualRules:
    """Artificer Logic, rebuilt from the descriptor's own `manual` block.

    ⚑ WHY THIS IS NOT `ProbeOracleGame`.  Black Box probes an instance to name a
    VALUE.  This game probes to name a RULE, and the difference is where the
    hidden bit lives: there the answer is a function of the probe and the
    instance, here the whole instance IS a member of a published lattice and a
    probe partitions that lattice.  The state a player holds is therefore a
    POSTERIOR — the set of rules the evidence still permits — and every
    measurement below is over that set.

    ⚑ AND WHY IT IS NOT `DescentRules`.  A descent buys information with air and
    the interesting question is whether to.  Here a charge that cannot split the
    survivors is REFUSED, so every legal experiment is informative by
    construction and the only question is WHICH.  A dominance pass is therefore
    meaningful here in a way it is not for a descent, and it is run below.

    Nothing in this class reads a Lean constant.  `KERNEL_SHAPE` is consulted
    once, after every number it is compared against is already computed.
    """

    # The kernel's claim, as a claim.  ⚠ This is NOT an input to anything computed
    # below — the census is complete before this dict is consulted, and consulting
    # it can only produce a finding.  Two independent sources or it is decoration.
    KERNEL_SHAPE = {
        "declared_states": 1197,
        "rows": 28728,
        "actions": 24,
        "worst_case_probes": 4,
        "source": "ArtificerLogic.parametric_shape_is_measured + "
                  "four_charges_are_enough/three_charges_are_not (native_decide)",
    }

    def __init__(self, doc: dict) -> None:
        self.doc = doc
        manual = doc.get("manual")
        if not isinstance(manual, dict):
            raise Refusal("artificer descriptor carries no `manual` block, so there "
                          "is nothing to rebuild the rules from — and the manual is "
                          "the whole design: an induction game whose hypothesis space "
                          "is not published is Zendo, where losing feels arbitrary")
        self.cogs = manual["cogs_per_charge"]
        self.metals = list(manual["metals"])
        self.seats = list(manual["seats"])
        self.families = list(manual["families"])
        self.probe_budget = manual["probe_budget"]
        self.reasons = set(manual["refusal_reasons"])

        self.charges = []
        for entry in manual["charges"]:
            cid = entry["id"]
            cogs = list(entry["cogs"])
            if len(cogs) != self.cogs:
                raise Refusal(f"charge {cid} has {len(cogs)} cogs, the manual "
                              f"declares {self.cogs}")
            for cog in cogs:
                if cog not in self.metals:
                    raise Refusal(f"charge {cid} uses a metal {cog!r} the manual "
                                  f"does not declare")
            self.charges.append(cid)
        if len(set(self.charges)) != len(self.charges):
            raise Refusal("the manual names a charge twice")
        # The charge space is a full product or the manual is hiding an experiment.
        want = len(self.metals) ** self.cogs
        if len(self.charges) != want:
            raise Refusal(
                f"the manual declares {len(self.charges)} charges but "
                f"{len(self.metals)} metals in {self.cogs} seats is {want}.  A "
                f"legal-experiment set smaller than the product is a set of "
                f"experiments the player is not allowed to run, and every "
                f"separation bound below would be measured against the wrong space")

        # The rule lattice, as signatures over the charge space.
        self.rules = []
        self.sig = {}
        for entry in manual["rules"]:
            rid = entry["id"]
            if entry["family"] not in self.families:
                raise Refusal(f"rule {rid} claims a family {entry['family']!r} the "
                              f"manual does not declare")
            engages = list(entry["engages"])
            for c in engages:
                if c not in self.charges:
                    raise Refusal(f"rule {rid} engages on {c!r}, which is not a charge")
            if len(set(engages)) != len(engages):
                raise Refusal(f"rule {rid} names a charge twice")
            self.rules.append(rid)
            self.sig[rid] = frozenset(engages)
        if len(set(self.rules)) != len(self.rules):
            raise Refusal("the manual names a rule twice")
        self.full = frozenset(self.rules)
        # Memoised in `__init__` and not in `census`: the reserve is consulted by
        # the view differential, which runs FIRST.
        self._reserve_memo = {}

    # ---- the design gate ---------------------------------------------------

    def distinguishability(self, game) -> None:
        """⚑ THE HARD FAIL.  Two rules no legal experiment separates mean a player
        can run every charge, narrow perfectly, and still be handed a coin.

        This is computed from the EMITTED signatures, not from the kernel: the
        Lean side proves `manual_has_no_synonyms` over its own `Rule.accepts`,
        and that proof says nothing about the bytes a client downloads unless the
        bytes are checked too.  `synonym_manual_is_caught` in
        `ArtificerLogicEmit` is the falsifier for exactly this leg — a manual
        with a planted synonym passes the row-by-row differential and fails here.
        """
        rep, name = game.rep, game.name
        by_sig = {}
        for rid in self.rules:
            by_sig.setdefault(self.sig[rid], []).append(rid)
        collisions = sorted(tuple(sorted(v)) for v in by_sig.values() if len(v) > 1)
        if collisions:
            rep.find(name, "indistinguishable-rules", FAIL,
                     f"{len(collisions)} pair(s) or group(s) of rules that no legal "
                     f"experiment can separate",
                     f"{collisions}.  A player who runs every one of the "
                     f"{len(self.charges)} charges is left holding more than one "
                     f"candidate and must guess, so a perfectly played run loses to a "
                     f"coin flip.  This is the induction-game form of `the budget "
                     f"never binds` and it is a design defect, not a difficulty knob.")
            return
        # Which single experiment separates each pair — the witness, not just the count.
        pairs = 0
        min_separators = None
        for i, a in enumerate(self.rules):
            for b in self.rules[i + 1:]:
                pairs += 1
                seps = len(self.sig[a] ^ self.sig[b])
                if min_separators is None or seps < min_separators[0]:
                    min_separators = (seps, a, b)
        rep.find(name, "manual-is-distinguishing", INFO,
                 f"all {pairs} pairs of the {len(self.rules)}-rule manual are "
                 f"separated by at least one legal experiment",
                 f"every pair differs on at least {min_separators[0]} of the "
                 f"{len(self.charges)} charges; the closest pair is "
                 f"{min_separators[1]}/{min_separators[2]}, separated by exactly "
                 f"{min_separators[0]}.  Rebuilt from the emitted `manual` block "
                 f"alone — the kernel's `manual_has_no_synonyms` is a second, "
                 f"independent source and a pin against one definition is decoration.")

    # ---- the machine, rebuilt ---------------------------------------------

    def split(self, cands, charge):
        yes = frozenset(r for r in cands if charge in self.sig[r])
        return yes, cands - yes

    def splits(self, cands, charge):
        yes, no = self.split(cands, charge)
        return bool(yes) and bool(no)

    def state_of_view(self, view: dict):
        """The canonical state: the surviving posterior, the clock, the verdict."""
        return (frozenset(view["candidates"]), view["turns"], view["verdict"])

    def is_open(self, st, kind, charge, rule) -> bool:
        cands, spent, verdict = st
        if verdict != "probing":
            return False
        if kind == "probe":
            return spent < self.probe_budget and self.splits(cands, charge)
        if kind == "declare":
            return rule in cands
        raise Refusal(f"unknown action kind {kind!r}")

    def refusal_reason(self, st, kind, charge, rule) -> str:
        cands, spent, verdict = st
        if verdict == "identified":
            return "solved"
        if verdict == "mistaken":
            return "run-lost"
        if kind == "probe":
            return "no-charges-left" if spent >= self.probe_budget else "already-answered"
        return "refuted"

    def step(self, st, kind, charge, rule, answer):
        cands, spent, _ = st
        if kind == "probe":
            yes, no = self.split(cands, charge)
            return (yes if answer else no, spent + 1, "probing")
        if answer:
            return (frozenset([rule]), spent + 1, "identified")
        return (cands - {rule}, spent + 1, "mistaken")

    def row_for(self, st, kind, charge, rule):
        """(verdict, reason, next, on_match, on_mismatch), rebuilt.

        `accept` exactly when every surviving candidate answers the same way —
        which is exactly when the row does not need the oracle.
        """
        if not self.is_open(st, kind, charge, rule):
            return ("refuse", self.refusal_reason(st, kind, charge, rule), None, None, None)
        cands = st[0]
        if kind == "probe":
            answers = {charge in self.sig[r] for r in cands}
        else:
            answers = {r == rule for r in cands}
        on_t = self.step(st, kind, charge, rule, True)
        on_f = self.step(st, kind, charge, rule, False)
        if answers == {True}:
            return ("accept", None, on_t, None, None)
        if answers == {False}:
            return ("accept", None, on_f, None, None)
        return ("resolve", None, None, on_t, on_f)

    # ---- the differential --------------------------------------------------

    def differential(self, game) -> None:
        rep, name = game.rep, game.name
        meta = {}
        for aid in game.actions:
            m = game.action_meta[aid]
            kind = m.get("kind")
            if kind not in ("probe", "declare"):
                raise Refusal(f"action {aid} declares kind {kind!r}; this game has "
                              f"probes and declarations and nothing else")
            if kind == "probe" and m.get("charge") not in self.charges:
                raise Refusal(f"probe {aid} names a charge the manual does not declare")
            if kind == "declare" and m.get("rule") not in self.rules:
                raise Refusal(f"declaration {aid} names a rule the manual does not declare")
            meta[aid] = (kind, m.get("charge"), m.get("rule"))
        # Every charge and every rule must be reachable as an action, or the
        # descriptor publishes a lattice with entries no run can name.
        probed = {c for (k, c, _) in meta.values() if k == "probe"}
        named = {r for (k, _, r) in meta.values() if k == "declare"}
        if probed != set(self.charges):
            raise Refusal(f"the action alphabet does not offer every charge: "
                          f"{sorted(set(self.charges) - probed)} cannot be fed")
        if named != set(self.rules):
            raise Refusal(f"the action alphabet does not offer every rule: "
                          f"{sorted(set(self.rules) - named)} cannot be named, so a "
                          f"run that draws one is unwinnable by construction")
        self.meta = meta

        # 1. every emitted view is a distinct state, and the id is a function of it
        self.id_of, self.state_of = {}, {}
        for sid, s in game.states.items():
            st = self.state_of_view(s["view"])
            if st in self.id_of and self.id_of[st] != sid:
                raise Refusal(f"{sid} and {self.id_of[st]} declare the same state, so "
                              f"the emitted id is not a function of the state")
            self.id_of[st] = sid
            self.state_of[sid] = st

        # 2. every derived view field, rebuilt
        for sid, s in game.states.items():
            st = self.state_of[sid]
            v, cands, spent, verdict = s["view"], *self.state_of[sid]
            if not cands:
                raise Refusal(f"{sid} declares an EMPTY candidate set.  The hidden "
                              f"rule is always among the survivors, so no reachable "
                              f"state can have none — this state is unreachable under "
                              f"every instance and the table names it anyway")
            if v["remaining"] != len(cands):
                raise Refusal(f"{sid} reports {v['remaining']} survivors and lists "
                              f"{len(cands)}")
            if v["charges_left"] != max(0, self.probe_budget - spent):
                raise Refusal(f"{sid} misreports the charges left")
            if bool(v["certain"]) != (len(cands) == 1):
                raise Refusal(f"{sid} misreports certainty")
            if bool(v["solved"]) != (verdict == "identified"):
                raise Refusal(f"{sid} misreports the win")
            if bool(v["doomed"]) != (verdict == "mistaken"):
                raise Refusal(f"{sid} misreports the loss")
            if bool(s["terminal"]) != (verdict == "identified"):
                raise Refusal(f"{sid} misreports terminality")
            mine = self.certifiable(st)
            if bool(v["certifiable"]) != mine:
                raise Refusal(
                    f"{sid} reports certifiable={v['certifiable']}; rebuilding the "
                    f"reserve from `manual.reserve` gives {mine}.  A client that "
                    f"tells a player their run can still be won on skill is telling "
                    f"them what the budget is FOR, so this is not a cosmetic field")

        # 3. every row
        seen_reasons = set()
        for sid, st in self.state_of.items():
            for aid in game.actions:
                kind, charge, rule = meta[aid]
                verdict, reason, nxt, on_m, on_f = self.row_for(st, kind, charge, rule)
                t = game.trans[(sid, aid)]
                if t["verdict"] != verdict:
                    raise Refusal(f"{sid}/{aid} is emitted {t['verdict']} and the "
                                  f"rebuilt rule says {verdict}")
                if verdict == "refuse":
                    if t["reason"] != reason:
                        raise Refusal(f"{sid}/{aid} refuses as {t['reason']!r}; the "
                                      f"rebuilt rule gives {reason!r}")
                    seen_reasons.add(t["reason"])
                elif verdict == "accept":
                    self._same_state(game, sid, aid, "next", t["next"], nxt)
                else:
                    self._same_state(game, sid, aid, "on_match", t["on_match"], on_m)
                    self._same_state(game, sid, aid, "on_mismatch", t["on_mismatch"], on_f)
        stray = seen_reasons - self.reasons
        if stray:
            raise Refusal(f"the table refuses for reasons the manual does not "
                          f"declare: {sorted(stray)}")

        # 4. the emitted state set is exactly the two-branch closure
        closure, queue = {self.state_of[game.initial]}, deque([self.state_of[game.initial]])
        while queue:
            st = queue.popleft()
            for aid in game.actions:
                kind, charge, rule = meta[aid]
                _, _, nxt, on_m, on_f = self.row_for(st, kind, charge, rule)
                for n in (nxt, on_m, on_f):
                    if n is not None and n not in closure:
                        closure.add(n)
                        queue.append(n)
        emitted = set(self.state_of.values())
        if closure != emitted:
            raise Refusal(f"the emitted state set is not the two-branch closure: "
                          f"{len(emitted - closure)} extra, {len(closure - emitted)} "
                          f"missing")

        self.distinguishability(game)
        self.census(game)

    def _same_state(self, game, sid, aid, slot, emitted_id, mine) -> None:
        if mine not in self.id_of:
            raise Refusal(f"{sid}/{aid} {slot} rebuilds to a state the descriptor "
                          f"does not declare")
        if self.id_of[mine] != emitted_id:
            raise Refusal(f"{sid}/{aid} {slot} is emitted {emitted_id} and rebuilds "
                          f"to {self.id_of[mine]}")

    # ---- the reserve, and the two headline dials ---------------------------

    def certain_within(self, cands, fuel, memo=None):
        """Can this posterior be cut to ONE within `fuel` charges, on the WORST
        answer the mechanism can give?  A real minimax: both branches of every cut
        must succeed, so a True here is a guarantee and not a hope.

        ⚑ The adversary is legitimate.  Each charge is consulted at most once —
        a charge that cannot split is refused — so every answer sequence is
        realised by some rule of the manual, and an adversary who picks answers
        is exactly an adversary who picked a rule.
        """
        if memo is None:
            memo = self._reserve_memo
        if len(cands) <= 1:
            return True
        if fuel <= 0:
            return False
        key = (cands, fuel)
        if key in memo:
            return memo[key]
        out = False
        for c in self.charges:
            yes, no = self.split(cands, c)
            if not yes or not no:
                continue
            if self.certain_within(yes, fuel - 1, memo) and \
               self.certain_within(no, fuel - 1, memo):
                out = True
                break
        memo[key] = out
        return out

    def certifiable(self, st) -> bool:
        cands, spent, verdict = st
        if verdict != "probing":
            return False
        return self.certain_within(cands, max(0, self.probe_budget - spent))

    def worst_case(self, cands, memo):
        """Fewest charges that identify, against the worst answers.  INF if none."""
        if len(cands) <= 1:
            return 0
        if cands in memo:
            return memo[cands]
        memo[cands] = INF          # cycle guard; splits strictly shrink so it is moot
        best = INF
        for c in self.charges:
            yes, no = self.split(cands, c)
            if not yes or not no:
                continue
            best = min(best, 1 + max(self.worst_case(yes, memo),
                                     self.worst_case(no, memo)))
        memo[cands] = best
        return best

    def expected(self, cands, memo):
        """Expected charges to identify under optimal play, uniform prior.  THE
        DIFFICULTY DIAL: it is what a competent player actually pays, where the
        worst case is what the budget must cover."""
        n = len(cands)
        if n <= 1:
            return 0.0
        if cands in memo:
            return memo[cands]
        best = None
        for c in self.charges:
            yes, no = self.split(cands, c)
            if not yes or not no:
                continue
            v = 1.0 + (len(yes) * self.expected(yes, memo)
                       + len(no) * self.expected(no, memo)) / n
            if best is None or v < best:
                best = v
        memo[cands] = INF if best is None else best
        return memo[cands]

    # ---- the census --------------------------------------------------------

    def census(self, game) -> None:
        """Walk the belief machine this class rebuilt, and count.

        Nothing here is read from the descriptor's own counts; the posteriors are
        enumerated from the `manual` signatures and the budget, and only then is
        `KERNEL_SHAPE` consulted.
        """
        rep, name = game.rep, game.name
        wmemo, ememo = {}, {}

        # --- the two headline dials, over the full manual -------------------
        worst = self.worst_case(self.full, wmemo)
        expected = self.expected(self.full, ememo)
        floor = ceil_log(len(self.rules), 2)

        if worst >= INF:
            rep.find(name, "manual-cannot-be-identified", FAIL,
                     "no sequence of legal experiments identifies the rule",
                     "the charge space does not separate the manual at all, so the "
                     "game cannot be won on skill under any budget.")
            return

        # --- reachable posteriors, and the per-experiment texture ------------
        reach, queue = {self.full}, deque([self.full])
        while queue:
            cands = queue.popleft()
            if len(cands) <= 1:
                continue
            for c in self.charges:
                yes, no = self.split(cands, c)
                if not yes or not no:
                    continue
                for nxt in (yes, no):
                    if nxt not in reach:
                        reach.add(nxt)
                        queue.append(nxt)

        legal = Counter()
        best_worst = Counter()
        best_expected = Counter()
        bits_total = {c: 0.0 for c in self.charges}
        for cands in reach:
            if len(cands) <= 1:
                continue
            scored = []
            for c in self.charges:
                yes, no = self.split(cands, c)
                if not yes or not no:
                    continue
                legal[c] += 1
                # information value: expected bits this cut removes, uniform prior
                p = len(yes) / len(cands)
                bits = -(p * math.log2(p) + (1 - p) * math.log2(1 - p))
                bits_total[c] += bits
                scored.append((c,
                               1 + max(self.worst_case(yes, wmemo),
                                       self.worst_case(no, wmemo)),
                               1.0 + (len(yes) * self.expected(yes, ememo)
                                      + len(no) * self.expected(no, ememo)) / len(cands)))
            if not scored:
                continue
            bw = min(v for _, v, _ in scored)
            bx = min(v for _, _, v in scored)
            for c, dw, dx in scored:
                if dw == bw:
                    best_worst[c] += 1
                if abs(dx - bx) < 1e-12:
                    best_expected[c] += 1

        dominated = sorted(c for c in self.charges
                           if best_worst[c] == 0 and best_expected[c] == 0)
        never_legal = sorted(c for c in self.charges if legal[c] == 0)

        # ⚑ HOW MANY OF A RUN'S CUTS ARE REAL DECISIONS?
        #
        # ⚠ ADDED 2026-08-06 after this lane got the answer WRONG BY HAND and a
        # shipping decision was made on it.  The measurement I ran first asked
        # whether the MOST EVEN charge loses the guarantee; that answers "does one
        # particular heuristic fail here", not "is this a decision".  It reported 1
        # real decision per run for a manual whose true figure is 3.
        #
        # The honest test is whether the player CAN GO WRONG: a step is a real
        # decision when at least one LEGAL charge loses the guarantee, however a
        # solver would have found the right one.  A game whose cuts are all forced
        # is a game that plays itself, and no amount of hidden information fixes
        # that -- so this is measured along the line an optimal player actually
        # walks, once per instance, rather than averaged over posteriors nobody
        # reaches.
        real_steps = 0
        total_steps = 0
        per_instance = []
        for rule in self.rules:
            cands, hits, steps = self.full, 0, 0
            while len(cands) > 1:
                scored = []
                for c in self.charges:
                    yes, no = self.split(cands, c)
                    if not yes or not no:
                        continue
                    scored.append((c, 1 + max(self.worst_case(yes, wmemo),
                                              self.worst_case(no, wmemo))))
                if not scored:
                    break
                floor_here = min(v for _, v in scored)
                optimal = [c for c, v in scored if v == floor_here]
                if len(optimal) < len(scored):
                    hits += 1
                steps += 1
                yes, no = self.split(cands, optimal[0])
                cands = yes if optimal[0] in self.sig[rule] else no
            real_steps += hits
            total_steps += steps
            per_instance.append(hits)
        real_per_run = real_steps / len(self.rules)
        cuts_per_run = total_steps / len(self.rules)

        if real_per_run <= 1.0:
            rep.find(name, "the-cuts-are-forced", WARN,
                     f"an optimal run meets only {real_per_run:.2f} real decisions "
                     f"in {cuts_per_run:.2f} cuts",
                     f"at almost every step every legal charge is equally good, so "
                     f"the player is not choosing -- they are pressing whichever "
                     f"button is still lit. Hidden information does not fix that: "
                     f"the instance decides the ANSWERS, and this measures whether "
                     f"the QUESTIONS were ever a choice.")
        else:
            rep.find(name, "the-cuts-are-decisions", INFO,
                     f"an optimal run meets {real_per_run:.2f} real decisions in "
                     f"{cuts_per_run:.2f} cuts",
                     f"a step counts when at least one LEGAL charge loses the "
                     f"guarantee, so a player can go wrong there whatever heuristic "
                     f"they use. Per instance: "
                     f"{dict(sorted(Counter(per_instance).items()))} (real decisions "
                     f"-> how many of the {len(self.rules)} instances). "
                     f"⚠ Do NOT read a small `expected < worst` gap as difficulty: "
                     f"measured across 1400+ manual compositions on this charge "
                     f"space, that gap is SLACK against the information floor, and "
                     f"slack makes cuts freer. A manual with 2^worst = N -- a "
                     f"perfect code, where expected EQUALS worst -- averages 2.98 "
                     f"real decisions; one bit of slack averages 2.74, four bits "
                     f"1.55.")

        # --- the opening, which is where the texture is legible --------------
        opening = []
        for c in self.charges:
            yes, no = self.split(self.full, c)
            if not yes or not no:
                opening.append({"charge": c, "engages": len(yes), "slips": len(no),
                                "worst_case_total": None, "keeps_the_budget": False})
                continue
            total = 1 + max(self.worst_case(yes, wmemo), self.worst_case(no, wmemo))
            opening.append({
                "charge": c, "engages": len(yes), "slips": len(no),
                "worst_case_total": total,
                "keeps_the_budget": total <= self.probe_budget,
                "information_bits": round(
                    -((len(yes) / len(self.rules)) * math.log2(len(yes) / len(self.rules))
                      + (len(no) / len(self.rules)) * math.log2(len(no) / len(self.rules))), 4),
            })
        even = [o for o in opening if o["engages"] == o["slips"]]
        keeps = [o for o in opening if o["keeps_the_budget"]]
        traps = [o["charge"] for o in even if not o["keeps_the_budget"]]

        # --- the machine census, rebuilt ------------------------------------
        rows = len(self.state_of) * len(game.actions)
        resolve_rows = sum(
            1 for sid, st in self.state_of.items() for aid in game.actions
            if self.row_for(st, *self.meta[aid])[0] == "resolve")

        # ⚑ the cross-check.  Two independent sources, compared, and only now.
        k = self.KERNEL_SHAPE
        mine = (len(self.state_of), rows, len(game.actions), worst)
        theirs = (k["declared_states"], k["rows"], k["actions"], k["worst_case_probes"])
        if mine != theirs:
            rep.find(name, "kernel-census-disagreement", FAIL,
                     "the gate and the kernel disagree about the shape of the game",
                     f"walking the emitted descriptor gives {mine[0]} declared states "
                     f"/ {mine[1]} rows / {mine[2]} actions / worst-case {mine[3]} "
                     f"charges; {k['source']} asserts {theirs}.  These are "
                     f"independent — one is a compiled evaluation of the kernel's own "
                     f"definitions, the other is a simulation of the bytes a client "
                     f"downloads — so a disagreement means the descriptor and the "
                     f"engine are not the same game.")
        else:
            rep.find(name, "manual-shape-agrees", INFO,
                     f"{mine[0]} declared states, {mine[1]} rows and a worst case of "
                     f"{worst} charges, arrived at twice",
                     f"this tool rebuilt the rules from `manual`, checked all "
                     f"{len(game.trans)} emitted rows against them, then re-derived "
                     f"the belief machine and the minimax from the rebuilt rules "
                     f"alone.  It gets {mine}, and {k['source']} independently "
                     f"asserts the same tuple.  A pin against its own definition is "
                     f"decoration; this is two sources.")

        # --- the budget -----------------------------------------------------
        # The transcript is charges plus the one naming that ends the run.
        needed = worst + 1
        slack = game.budget - needed
        if slack < 0:
            rep.find(name, "budget-cannot-be-met", FAIL,
                     f"the budget cannot cover identification",
                     f"the worst case under optimal play is {worst} charges plus a "
                     f"naming = {needed} actions, and `action_limit` is "
                     f"{game.budget}.  A player who plays perfectly still cannot be "
                     f"sure, so every run ends on a wager.")
        elif slack == 0:
            rep.find(name, "budget-binds-exactly", INFO,
                     f"the budget is exactly identification: {worst} charges and the "
                     f"naming, with nothing spare",
                     f"worst case under optimal play is {worst} charges — the "
                     f"information floor for {len(self.rules)} rules over binary "
                     f"answers is {floor} — plus the naming, and `action_limit` is "
                     f"{game.budget}.  Slack zero means every wasted cut is paid for "
                     f"in certainty, which is what makes the choice of charge the "
                     f"whole game.")
        elif slack == 1:
            rep.find(name, "budget-has-one-spare", INFO,
                     f"the budget covers identification with exactly one spare action",
                     f"worst case {worst} charges + naming = {needed}, "
                     f"`action_limit` {game.budget}.  One mistake is survivable and "
                     f"a second is not.")
        else:
            rep.find(name, "budget-has-slack", WARN,
                     f"the budget is {slack} actions more than identification needs",
                     f"worst case {worst} charges + naming = {needed}, "
                     f"`action_limit` {game.budget}.  A budget that never binds is "
                     f"not a budget: a player can afford to waste {slack} cuts and "
                     f"still be certain.")

        if worst > floor:
            rep.find(name, "manual-is-not-a-tight-code", INFO,
                     f"identification costs {worst} charges against an information "
                     f"floor of {floor}",
                     f"{len(self.rules)} rules need {floor} bits and the manual "
                     f"cannot always deliver them one per charge.")

        # --- can it be lost? -------------------------------------------------
        wagers = 0
        for sid, st in self.state_of.items():
            cands, spent, verdict = st
            if verdict == "probing" and len(cands) >= 2 and spent >= self.probe_budget:
                wagers += 1
        if wagers == 0:
            rep.find(name, "cannot-be-lost", FAIL,
                     "no reachable state forces a wager",
                     "there is no position from which the run must name a rule with "
                     "more than one candidate standing, so a player cannot lose by "
                     "spending the budget badly and the budget does not bind.")
        else:
            rep.find(name, "the-budget-is-losable", INFO,
                     f"{wagers} reachable states force a naming with more than one "
                     f"candidate standing",
                     f"a player who spends a cut badly arrives with the charges gone "
                     f"and a posterior of size 2 or more; from there the naming is a "
                     f"wager.  This is the loss condition, and it is reachable only "
                     f"through a mistake the player could have avoided.")

        # --- experiment texture -----------------------------------------------
        if never_legal:
            rep.find(name, "charge-that-never-splits", FAIL,
                     f"{len(never_legal)} charge(s) never separate anything",
                     f"{never_legal} are offered as actions and are refused in every "
                     f"reachable posterior, so they are menu items that are never a "
                     f"move.")
        if dominated:
            rep.find(name, "dominated-experiment", WARN,
                     f"{len(dominated)} charge(s) are never the best probe in any "
                     f"reachable posterior",
                     f"{dominated}.  A charge that is legal but never optimal — "
                     f"neither in worst case nor in expectation — anywhere in the "
                     f"belief lattice is a menu item a player never has a reason to "
                     f"pick.  It is not a defect the way an indistinguishable pair "
                     f"is, but it is a decision that is not a decision.")
        else:
            rep.find(name, "every-charge-earns-its-place", INFO,
                     f"all {len(self.charges)} charges are the strictly best probe in "
                     f"at least one reachable posterior",
                     f"no charge is dominated: for each one there is a belief state "
                     f"in which it is the optimal cut, so the menu is a menu and not "
                     f"a decorated shortlist.  Best-in counts (worst case / expected) "
                     f"over {len([c for c in reach if len(c) > 1])} branching "
                     f"posteriors: " +
                     ", ".join(f"{c} {best_worst[c]}/{best_expected[c]}"
                               for c in self.charges))

        if len(keeps) == len(self.charges):
            rep.find(name, "the-opening-is-a-free-choice", WARN,
                     "every opening charge leaves the run able to finish inside the "
                     "budget",
                     "the first decision costs nothing, so the game does not start "
                     "until the second cut.  With the instance hidden this is not a "
                     "disclosure defect, but it is a wasted decision.")
        elif traps:
            rep.find(name, "an-even-split-is-not-a-good-one", INFO,
                     f"{len(even)} opening charges cut the manual exactly in half and "
                     f"only {len(keeps)} of them keep the budget",
                     f"{traps} split {even[0]['engages']}/{even[0]['slips']} and still "
                     f"cost {[o['worst_case_total'] for o in even if not o['keeps_the_budget']][0]} "
                     f"charges, because the halves cannot be separated in what "
                     f"remains.  Evenness is necessary and not sufficient, and that "
                     f"is the whole lesson of the opening: {len(self.charges) - len(keeps)} "
                     f"of {len(self.charges)} openings silently cost the guarantee.")

        game.extra_summary = {
            "shape": "rule-induction",
            "manual_size": len(self.rules),
            "manual_families": len(self.families),
            "charge_space": len(self.charges),
            "indistinguishable_pairs": 0,
            "information_floor_loose": floor,
            "information_floor_tight": floor,
            "execution_floor_as_designed": needed,
            "execution_floor_as_emitted": needed,
            "worst_case_optimal": needed,
            "worst_case_probes": worst,
            "expected_probes_to_identify": round(expected, 4),
            "probe_budget": self.probe_budget,
            "budget_binds": slack <= 1,
            "budget_slack": slack,
            "wager_states": wagers,
            "dominated_experiments": dominated,
            "real_decisions_per_run": round(real_per_run, 4),
            "cuts_per_run": round(cuts_per_run, 4),
            "code_slack_bits": 2 ** worst - len(self.rules),
            "reachable_posteriors": len(reach),
            "branching_posteriors": len([c for c in reach if len(c) > 1]),
            "rebuilt_resolve_rows": resolve_rows,
            "opening_table": opening,
            "probe_best_in_worst_case": {c: best_worst[c] for c in self.charges},
            "probe_best_in_expectation": {c: best_expected[c] for c in self.charges},
            "probe_mean_bits": {c: round(bits_total[c] / legal[c], 4) if legal[c] else None
                                for c in self.charges},
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
# backend 5 — hidden-instance ORACLE games: the descriptor is the whole question
#             -and-answer function and names no instance
# ---------------------------------------------------------------------------

class ProbeOracleGame:
    """A descriptor carrying `oracle`: the COMPLETE (instance, probe) -> class table.

    Black Box Reconstruction cannot use any earlier shape.  Its state is the SET of
    pairs a run has asked, so a total `(state, action)` table has 2^25 rows and does
    not exist; and its domain is the 120 permutations, not `alphabet^bands`, so the
    Mastermind backend refuses it.  What IS small is the oracle, and the oracle is
    the entire instance: publish it and the client has every rule and no answer.

    ANTI-MIRROR.  This backend builds NO model of the game.  Everything below is read
    off the emitted table, and the one semantic fact it uses — that a run must collect
    every solving probe of its instance — is a declared field (`required_per_instance`)
    checked against the table on every row.  The Lean side owns the other direction:
    `Emit.blackBox_table_is_the_kernel` reads the rendered descriptor back and compares
    all 3000 cells against the kernel's `hitB`.
    """

    def __init__(self, doc: dict, rep: Report) -> None:
        self.doc = doc
        self.rep = rep
        self.name = doc["game_id"]
        oracle = doc.get("oracle")
        if not isinstance(oracle, dict):
            raise Refusal("descriptor carries no `oracle` block")
        self.budget = doc["action_limit"]
        self.space = oracle["instance_space"]
        self.required = oracle["required_per_instance"]
        self.probes = [p["id"] for p in oracle["probes"]]
        if len(set(self.probes)) != len(self.probes):
            raise Refusal("oracle.probes contains a duplicate id")
        self.classes = oracle["classes"]
        solving = [c["id"] for c in self.classes if c["solving"]]
        if len(solving) != 1:
            raise Refusal(f"{len(solving)} observation classes are solving; expected exactly one")
        self.alphabet = oracle["class_alphabet"]
        if len(self.alphabet) != len(self.classes):
            raise Refusal("oracle.class_alphabet does not match the declared class count")
        self.solving_char = self.alphabet[
            next(i for i, c in enumerate(self.classes) if c["solving"])]
        self.rows = oracle["table"]
        if len(self.rows) != self.space:
            raise Refusal(f"oracle.table has {len(self.rows)} rows for a space of {self.space}")

        # ⚑ THE SETTLING RULE IS A DECLARED STRING, AND AN UNKNOWN ONE REFUSES.
        #
        # Refusal reachability below is derived from `settles` — which pairs a MATCH
        # retires — and that derivation is only sound for a rule this tool has an
        # exact reading of.  A kernel that changes what settling means has to change
        # this string, and an unrecognised string stops the analysis rather than
        # letting it silently measure the wrong game.  Same discipline as refusing an
        # organ whose row is not a sufficient statistic.
        self.settles = oracle.get("settles")
        if self.settles != "slot-and-fragment":
            raise Refusal(
                f"oracle.settles = {self.settles!r}; this backend derives refusal "
                f"reachability only for 'slot-and-fragment' and refuses to guess")
        self.slot_of = {p["id"]: p["slot"] for p in oracle["probes"]}
        self.fragment_of = {p["id"]: p["fragment"] for p in oracle["probes"]}
        self.declared_reasons = list(doc.get("refusals") or [])
        self.witnesses = doc.get("refusal_witnesses")
        self.precedence = doc.get("refusal_precedence")

    # -- refusal reachability, derived from the artifact -----------------------
    #
    # Nothing below reads the kernel.  The state a transcript reaches is the set of
    # probes played; which of them MATCHED is a cell of the emitted oracle table; and
    # `settles = "slot-and-fragment"` says a match retires both the position probed
    # and the fragment named.  Those three facts are the whole refusal vocabulary.

    def _settled(self, live: int, played: list):
        """Positions and fragments retired by the matches in `played`, on instance
        `live`.  Read off the emitted table, not off a rule model."""
        slots, frags = set(), set()
        for p in played:
            if p in self.hits[live]:
                slots.add(self.slot_of[p])
                frags.add(self.fragment_of[p])
        return slots, frags

    def _applicable(self, live: int, played: list, probe: str) -> set:
        """Every declared refusal whose OWN condition holds at this state."""
        slots, frags = self._settled(live, played)
        out = set()
        if len(slots) >= self.required:
            out.add("solved")
        if len(played) >= self.budget:
            out.add("turn-limit")
        if probe in played:
            out.add("repeated-probe")
        if self.slot_of[probe] in slots:
            out.add("settled-slot")
        if self.fragment_of[probe] in frags:
            out.add("settled-fragment")
        return out

    def _fires(self, live: int, played: list, probe: str):
        """The reason a client renders: the FIRST applicable one in the order the
        descriptor declares.  Precedence is semantics — `settled-slot` holds at every
        `solved` state — so it is read from the artifact, never assumed."""
        applicable = self._applicable(live, played, probe)
        for reason in self.declared_reasons:
            if reason in applicable:
                return reason, applicable
        return None, applicable

    def check_refusal_witnesses(self) -> dict:
        """Replay every emitted witness against the emitted ORACLE TABLE and re-derive
        the reason.  The kernel already asserted these (`BlackBoxReconstruction.
        every_refusal_is_witnessed`, and `Emit.blackBox_witnesses_are_the_kernel` reads
        them back out of the rendered bytes); this is the second source."""
        rep = self.rep
        if not isinstance(self.witnesses, list) or not self.witnesses:
            rep.find(self.name, "refusals-are-not-witnessed", WARN,
                     f"{len(self.declared_reasons)} refusal reason(s) are declared and "
                     f"this descriptor carries no witness for any of them",
                     f"the machine backends read refusal reachability off a total "
                     f"transition table; an oracle descriptor has none (the state space "
                     f"is a subset lattice, 2^{len(self.probes)} states), so the "
                     f"evidence has to travel IN the artifact.  The emitter now writes "
                     f"`refusal_witnesses` — a legal prefix and one further probe per "
                     f"reason — and this backend replays them.  These bytes predate "
                     f"that: RE-EMIT.  Declared and unwitnessed: "
                     f"{self.declared_reasons}.")
            return {"witnessed": False}

        if self.precedence != "first-applicable-in-declared-order":
            raise Refusal(
                f"refusal_precedence = {self.precedence!r}; this backend replays "
                f"witnesses only under 'first-applicable-in-declared-order'")

        disagreements, seen = [], []
        for w in self.witnesses:
            claimed = w["reason"]
            live = w["instance"]
            if claimed not in self.declared_reasons:
                disagreements.append(f"witness names undeclared reason {claimed!r}")
                continue
            if not 0 <= live < self.space:
                disagreements.append(f"{claimed}: instance {live} is outside the space")
                continue
            played, illegal = [], None
            for step in w["history"]:
                if step not in self.slot_of:
                    illegal = f"unknown probe {step!r}"
                    break
                fired, _ = self._fires(live, played, step)
                if fired is not None:
                    illegal = f"prefix probe {step} is itself refused ({fired})"
                    break
                played.append(step)
            if illegal:
                disagreements.append(f"{claimed}: {illegal}")
                continue
            probe = w["probe"]
            if probe not in self.slot_of:
                disagreements.append(f"{claimed}: unknown probe {probe!r}")
                continue
            fired, applicable = self._fires(live, played, probe)
            if fired is None:
                disagreements.append(
                    f"{claimed}: the probe is ACCEPTED here — no declared condition holds")
            elif fired != claimed:
                disagreements.append(
                    f"{claimed}: this tool derives {fired!r} (applicable: "
                    f"{sorted(applicable)})")
            else:
                seen.append(claimed)

        never = [r for r in self.declared_reasons if r not in seen]
        if disagreements:
            rep.find(self.name, "refusal-witness-disagreement", FAIL,
                     f"{len(disagreements)} emitted refusal witness(es) do not replay "
                     f"the way this tool reads the artifact",
                     "; ".join(disagreements) +
                     ".  These are independent — the kernel evaluated its own "
                     "`refusal?` and this tool replayed the transcript against the "
                     "emitted oracle table under the declared `settles` rule — so a "
                     "disagreement means the descriptor and the engine are not the "
                     "same game.")
        if never:
            rep.find(self.name, "declared-reason-never-fires", FAIL,
                     f"{never} is declared and witnessed by nothing",
                     f"a client carries a string for it and a reader believes it is a "
                     f"rule.  A refusal that cannot fire is a rule that does not exist.")
        if not disagreements and not never:
            rep.find(self.name, "every-declared-reason-fires", INFO,
                     f"all {len(self.declared_reasons)} declared refusal reasons fire, "
                     f"on a transcript that is legal up to the refused probe",
                     f"{self.declared_reasons}, each replayed from the emitted witness "
                     f"against the emitted oracle table: every prefix probe is accepted "
                     f"and the further probe is refused with exactly the declared "
                     f"reason, under `settles = {self.settles!r}` and "
                     f"`{self.precedence}`.  ⚠ Precedence is load-bearing here and is "
                     f"read from the artifact, not assumed: `settled-slot` holds at "
                     f"EVERY `solved` state, so `solved` is only ever reported because "
                     f"it is declared first.  Arrived at twice — "
                     f"`BlackBoxReconstruction.every_refusal_is_witnessed` is the "
                     f"kernel's compiled evaluation of its own `refusal?`, and this is "
                     f"a simulation of the bytes a client downloads.")
        return {"witnessed": True, "reasons_fired": sorted(seen),
                "reasons_never_fired": never, "witness_disagreements": disagreements}

    def build(self) -> None:
        """Decode every row into the set of probes that SOLVE for that instance."""
        self.hits = []
        for i, row in enumerate(self.rows):
            if len(row) != len(self.probes):
                raise Refusal(f"oracle row {i} is {len(row)} cells wide for "
                              f"{len(self.probes)} probes")
            bad = set(row) - set(self.alphabet)
            if bad:
                raise Refusal(f"oracle row {i} names class {sorted(bad)[0]!r}, which is "
                              f"outside the declared alphabet")
            h = frozenset(self.probes[j] for j, c in enumerate(row) if c == self.solving_char)
            if len(h) != self.required:
                raise Refusal(f"oracle row {i} has {len(h)} solving probes, but the "
                              f"descriptor declares required_per_instance = {self.required}")
            self.hits.append(h)
        if len(set(self.hits)) != self.space:
            dup = len(self.space * [0]) - len(set(self.hits))
            raise Refusal(f"the oracle table names only {len(set(self.hits))} distinct "
                          f"instances in {self.space} rows: some instances are "
                          f"indistinguishable by every probe, so the space is smaller "
                          f"than the descriptor claims")

    # -- exact adversarial minimax -----------------------------------------
    def waste_floor(self):
        """Fewest WASTED probes an optimal player can guarantee, worst case.

        Total turns = required + wasted, because every solving probe of the live
        instance must be played and costs one turn whenever it is played.  An
        optimal player takes a FORCED probe (one that solves for every remaining
        candidate) the moment one exists: it is required anyway and it is free
        information.  What is left to search is the wasted probes, and the state
        that determines them is the candidate set alone.

        ⚠ This ignores the kernel's LEGALITY refusals (a settled position retires).
        Legality only ever removes options from the PLAYER, so the value below is a
        LOWER bound on the true worst case.  The matching upper bound is proved in
        Lean over every instance, so the two together pin it.
        """
        memo = {}
        probes = list(self.probes)
        idx = {p: i for i, p in enumerate(self.probes)}

        def forced(cands):
            it = iter(cands)
            acc = set(self.hits[next(it)])
            for c in it:
                acc &= self.hits[c]
                if not acc:
                    break
            return acc

        def value(cands):
            if len(cands) <= 1:
                return 0
            got = memo.get(cands)
            if got is not None:
                return got
            memo[cands] = 10 ** 6
            f = forced(cands)
            best = 10 ** 6
            for p in probes:
                if p in f:
                    continue
                yes = frozenset(c for c in cands if p in self.hits[c])
                no = frozenset(c for c in cands if p not in self.hits[c])
                if not yes or not no:
                    continue
                worst = max(value(yes), 1 + value(no))
                if worst < best:
                    best = worst
            memo[cands] = best
            return best

        return value(frozenset(range(self.space))), len(memo)

    # -- verified symmetry of the oracle -----------------------------------
    def opener_orbits(self):
        """Probes are equivalent when some relabelling of the INSTANCES carries one
        to the other while preserving the whole table.  Checked, not assumed: the
        permutation is built from the table and then verified against every cell."""
        by_hits = defaultdict(list)
        for p in self.probes:
            sig = frozenset(i for i in range(self.space) if p in self.hits[i])
            by_hits[len(sig)].append(p)
        # every probe that solves for the same NUMBER of instances is a candidate
        # partner; the orbit is confirmed only when a witness relabelling exists.
        orbits, seen = [], set()
        for size in sorted(by_hits):
            group = by_hits[size]
            for p in group:
                if p in seen:
                    continue
                orb = [q for q in group if self._equivalent(p, q)]
                for q in orb:
                    seen.add(q)
                orbits.append(sorted(orb))
        return orbits

    def _equivalent(self, p, q):
        """Is there a bijection of instances carrying probe p's column to q's and
        preserving the multiset structure of the table?  A necessary and checked
        condition: the two columns partition the space into blocks of equal size,
        and the induced sub-tables agree up to instance relabelling on the counts."""
        pi = frozenset(i for i in range(self.space) if p in self.hits[i])
        qi = frozenset(i for i in range(self.space) if q in self.hits[i])
        if len(pi) != len(qi):
            return False
        # profile: for each candidate block, the sorted multiset of column sizes
        def profile(block):
            return tuple(sorted(
                len([i for i in block if r in self.hits[i]]) for r in self.probes))
        return (profile(pi) == profile(qi)
                and profile(frozenset(range(self.space)) - pi)
                    == profile(frozenset(range(self.space)) - qi))

    # -- reference policy ---------------------------------------------------
    def reference_policy(self):
        """Greedy: always take a forced probe; otherwise split the candidate set as
        evenly as possible.  Reported per instance so the DISTRIBUTION is visible,
        which is what says whether the worst case is the common case."""
        turns = []
        for live in range(self.space):
            cands = frozenset(range(self.space))
            played, spent = set(), 0
            while True:
                if len(cands) <= 1:
                    spent += len(self.hits[live] - played)
                    break
                f = set()
                it = iter(cands)
                f = set(self.hits[next(it)])
                for c in it:
                    f &= self.hits[c]
                pick = None
                if f - played:
                    pick = sorted(f - played)[0]
                else:
                    best = None
                    for p in self.probes:
                        if p in played:
                            continue
                        yes = sum(1 for c in cands if p in self.hits[c])
                        if yes == 0 or yes == len(cands):
                            continue
                        key = (max(yes, len(cands) - yes), p)
                        if best is None or key < best[0]:
                            best = (key, p)
                    if best is None:
                        spent += len(self.hits[live] - played)
                        break
                    pick = best[1]
                played.add(pick)
                spent += 1
                if pick in self.hits[live]:
                    cands = frozenset(c for c in cands if pick in self.hits[c])
                else:
                    cands = frozenset(c for c in cands if pick not in self.hits[c])
            turns.append(spent)
        return turns

    def analyse(self) -> dict:
        rep = self.rep
        self.build()

        # Information floor: probes needed to single out one of `space` instances.
        #
        # ⚠ NOT `naming_capacity`.  That tighter bound is Signal's, and it holds only
        # because exactly one of Signal's feedback classes ENDS the run by being the
        # code itself, so a depth-d strategy resolves 1 + (k-1)*M(d-1) codes rather
        # than k^d.  Here a `match` does not end anything — it settles one position of
        # `required` — so both classes keep the run alive and every one of them carries
        # its full share.  The plain entropy bound is therefore the right floor, and
        # applying the naming bound here reported 120, which is not a floor at all.
        n_classes = len(self.classes)
        info_loose = ceil_log(self.space, n_classes)
        info_tight = info_loose

        waste, memo = self.waste_floor()
        floor = self.required + waste

        # a probe whose column is constant carries no information anywhere
        dead = [p for p in self.probes
                if len({p in h for h in self.hits}) == 1]

        orbits = self.opener_orbits()
        turns = self.reference_policy()
        dist = dict(sorted(Counter(turns).items()))
        losses = [t for t in turns if t > self.budget]

        # ---- findings ----
        if len(orbits) == 1:
            rep.find(self.name, "opening-is-a-free-choice", INFO,
                     "every opening probe is equivalent, and under a hidden instance "
                     "that is the hiding rather than a defect",
                     f"the oracle's checked symmetry acts transitively on all "
                     f"{len(self.probes)} probes: relabelling positions and fragments "
                     f"carries any probe to any other while preserving every cell of the "
                     f"table.  A first probe genuinely cannot be better or worse than "
                     f"another, which is what it means for the instance to be out of the "
                     f"wire.  The machine backends WARN on a single opener class because "
                     f"there the board is disclosed and the symmetry is only nominal.")

        if dead:
            rep.find(self.name, "dead-probe", WARN,
                     f"{len(dead)} probe(s) answer the same way on every instance",
                     f"{dead[:6]}.  A probe whose column is constant is a turn that "
                     f"cannot buy information under any board.")

        if floor > self.budget:
            rep.find(self.name, "budget-below-optimum", FAIL,
                     "action_limit is below the proven adversarial worst case",
                     f"worst case {floor} > action_limit {self.budget}: some instances "
                     f"cannot be reconstructed at all.")
        elif floor == self.budget:
            rep.find(self.name, "budget-binds-exactly", INFO,
                     "the action budget binds exactly under optimal play",
                     f"adversarial worst case {floor} == action_limit {self.budget}; "
                     f"slack 0.  Every unit of the budget is load-bearing.")
        else:
            rep.find(self.name, "budget-slack", WARN,
                     f"the action budget never binds ({self.budget - floor} spare)",
                     f"worst case {floor} < action_limit {self.budget}.")

        if losses:
            rep.find(self.name, "reference-policy-loses", INFO,
                     f"the reference greedy policy loses on {len(losses)} of "
                     f"{self.space} instances",
                     f"an ordinary player is NOT guaranteed the optimum: the greedy "
                     f"policy overruns the budget on {len(losses)} boards.  That is the "
                     f"gap between 'winnable' and 'won'.")
        else:
            rep.find(self.name, "reference-policy-wins", INFO,
                     "the reference greedy policy wins on every instance",
                     f"turn distribution {dist}; worst {max(turns)}, mean "
                     f"{round(sum(turns)/len(turns), 4)} against a budget of "
                     f"{self.budget}.")

        rep.find(self.name, "floor-is-a-lower-bound", INFO,
                 f"the {floor}-probe floor is measured against an adversary and does "
                 f"NOT model the kernel's legality refusals",
                 f"a settled position retires both it and its fragment, which only ever "
                 f"REMOVES options from the player, so {floor} is a LOWER bound on the "
                 f"true worst case.  The matching upper bound is not measurable from an "
                 f"artifact and is proved in Lean instead "
                 f"(`five_positions_cost_exactly_fifteen_probes`: the reference sweep "
                 f"wins on every one of the {self.space} instances within "
                 f"{self.budget}).  Lower bound {floor} and upper bound {self.budget} "
                 f"coincide, so the worst case is exactly {floor}.")

        refusals = self.check_refusal_witnesses()

        return {
            "refusal_witness_check": refusals,
            "game": self.name,
            "kind": "probe-oracle",
            "engine_module": self.doc["engine_module"],
            "action_limit": self.budget,
            "instance_space": self.space,
            "probes": len(self.probes),
            "oracle_cells": self.space * len(self.probes),
            "required_per_instance": self.required,
            "observation_classes": n_classes,
            "distinguishable_instances": len(set(self.hits)),
            "information_floor_loose": info_loose,
            "information_floor_tight": info_tight,
            "execution_floor_as_designed": floor,
            "execution_floor_as_emitted": floor,
            "worst_case_optimal": floor,
            "worst_case_any_legal_play": self.budget,
            "wasted_probes_worst_case": waste,
            "minimax_memo_states": memo,
            "budget_binds": floor >= self.budget,
            "budget_slack": self.budget - floor,
            "can_lose": True,
            "opener_classes": len(orbits),
            "openers_total": len(self.probes),
            "dead_probes": dead,
            "reference_policy_worst": max(turns),
            "reference_policy_mean": round(sum(turns) / len(turns), 4),
            "reference_policy_distribution": dist,
            "reference_policy_losses": len(losses),
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
            # ⚠ every column is `str`-ed.  A game whose floor pass has not run yet
            # carries `None` here, and formatting `None` with `:>5` raises — which
            # took the whole render down AFTER every game had been analysed and every
            # finding recorded, so a clean run reported nothing at all.
            f"  {g['game']:<22}{str(g['information_floor_tight']):>5}"
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
        elif g["kind"] == "probe-oracle":
            w(bar("oracle", f"{g['instance_space']} instances x {g['probes']} probes "
                            f"= {g['oracle_cells']} cells") + "\n")
            w(bar("instance shape",
                  f"{g['required_per_instance']} solving probes per instance, "
                  f"{g['distinguishable_instances']} distinguishable") + "\n")
            w(bar("observation classes", f"{g['observation_classes']}") + "\n")
            w(bar("information floor",
                  f"{g['information_floor_tight']} tight  (loose "
                  f"ceil(log_{g['observation_classes']} {g['instance_space']}) = "
                  f"{g['information_floor_loose']})") + "\n")
            w(bar("worst case, optimal play",
                  f"{g['worst_case_optimal']}  = {g['required_per_instance']} required + "
                  f"{g['wasted_probes_worst_case']} wasted  (exact adversarial minimax, "
                  f"{g['minimax_memo_states']} memo states)") + "\n")
            w(bar("action budget",
                  f"{g['action_limit']}   binds: {g['budget_binds']}   "
                  f"slack: {g['budget_slack']}") + "\n")
            w(bar("can the run be lost?", f"{g['can_lose']}") + "\n")
            w(bar("opener classes",
                  f"{g['opener_classes']} of {g['openers_total']} probes") + "\n")
            w(bar("dead probes", f"{g['dead_probes'] or 'none'}") + "\n")
            w(bar("reference greedy policy",
                  f"worst {g['reference_policy_worst']}, mean "
                  f"{g['reference_policy_mean']}, losses "
                  f"{g['reference_policy_losses']}") + "\n")
            w(bar("  distribution", f"{g['reference_policy_distribution']}") + "\n")
        elif g["kind"] == "push-your-luck":
            w(bar("machine",
                  f"{g['states']} states, {g['actions']} verbs, "
                  f"{g['transitions']} rows "
                  f"({g['accept_rows']} accept / {g['refuse_rows']} refuse / "
                  f"{g['oracle_rows']} wager)") + "\n")
            w(bar("hazard, published",
                  f"rung 1..{g['depth_cap']} floods below "
                  f"{g['flood_ladder']} of {g['faces']}") + "\n")
            w(bar("hidden table",
                  f"{g['veins']} veins, shared per slot; the tape is per player") + "\n")
            w(bar("information floor",
                  f"{g['information_floor_tight']} crawls before the carry ladder "
                  f"names the day") + "\n")
            w(bar("family census",
                  f"{g['family_reachable']} reachable / {g['family_decisions']} "
                  f"decisions / {g['family_drowned']} drowned, over the vein family")
              + "\n")
            w(bar("refusal reasons",
                  ", ".join(f"{k}:{v}" for k, v in g["refusal_reasons"].items())) + "\n")
            w(bar("action budget",
                  f"{g['action_limit']}   binds: {g['budget_binds']}   "
                  f"slack: {g['budget_slack']}") + "\n")
            w(bar("can the run be lost?", f"{g['can_lose']}") + "\n")

            w("\n  ⚑ STOPPING RULE — exact backward induction over the belief state\n")
            w("     (the state IS the posterior: `carried` at `depth` names the veins\n")
            w("      whose ladder passes through it, and the prior is uniform)\n\n")
            postures = list(g["posture_thresholds"].keys())
            w("  depth carried  flood  still possible          "
              + "".join(f"{p[:12]:>13}" for p in postures) + "\n")
            for row in g["stopping_table"]:
                poss = ",".join(v[:3] for v in row["still_possible"])
                w(f"  {row['depth']:>5}{row['carried']:>8}"
                  f"{row['flood_below']:>5}/{g['faces']}  {poss:<22}"
                  + "".join(f"{row['postures'][p]:>13}" for p in postures) + "\n")
            w("\n  posture       optimal rule      value at the mouth\n")
            for p in postures:
                t = g["posture_thresholds"][p]
                rule = (f"bank at depth {t}" if t is not None
                        else "NOT a fixed depth")
                w(f"  {p:<14}{rule:<18}{g['posture_values'][p]:>10.4f}\n")
            w("\n  fixed-depth policies (a crawler who decided before going in)\n")
            w("  depth   P(reach)   mean carry     EV       sd\n")
            for f in g["fixed_depth_policies"]:
                mark = " <- best" if f["depth"] == g["best_fixed_depth"] else ""
                w(f"  {f['depth']:>5}{f['reach']:>11.4f}{f['mean_carry']:>13.3f}"
                  f"{f['ev']:>9.3f}{f['sd']:>9.3f}{mark}\n")
            w(f"\n  adaptive (risk-neutral) {g['adaptive_risk_neutral']:.4f} vs best "
              f"fixed {g['fixed_depth_policies'][g['best_fixed_depth'] - 1]['ev']:.4f}"
              f"  ->  reading the shaft is worth "
              f"{g['information_gain'] * 100:.1f}%\n")
            w("\n  `=` the posture values both verbs identically (a quota out of reach "
              "either way);\n      it is INDIFFERENCE and is excluded from the split "
              "count below.\n")
            w(f"\n  salvage postures STRICTLY disagreeing: "
              f"{len(g['posture_split_states'])} state(s) of "
              f"{len(g['stopping_table'])} decision states\n")
            w(f"  verbs optimal under no posture anywhere: "
              f"{g['dead_actions'] or 'none'}\n")
            w("\n  per vein\n")
            for v in g["per_vein"]:
                w(f"    {v['vein']:<14}{v['reachable']:>4} reachable  "
                  f"{v['decisions']:>3} decisions  {v['drowned']:>3} drowned\n")
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

            if g.get("shape") == "rule-induction":
                w("\n  \u26d1 RULE INDUCTION \u2014 the player names the LAW, not the "
                  "instance.\n     The state IS the posterior: the set of rules the "
                  "evidence still permits.\n\n")
                w(bar("published manual",
                      f"{g['manual_size']} rules in {g['manual_families']} families "
                      f"over {g['charge_space']} legal experiments") + "\n")
                w(bar("indistinguishable pairs",
                      f"{g['indistinguishable_pairs']}  \u2014 a pair no experiment "
                      f"separates is a coin a perfect player loses to") + "\n")
                w(bar("worst case to identify",
                      f"{g['worst_case_probes']} charges + the naming = "
                      f"{g['worst_case_optimal']} actions") + "\n")
                w(bar("EXPECTED charges to identify",
                      f"{g['expected_probes_to_identify']}   (information floor "
                      f"{g['information_floor_tight']}; uniform prior, optimal play)")
                  + "\n")
                w(bar("charge budget",
                      f"{g['probe_budget']}   slack {g['budget_slack']}   "
                      f"forced wagers {g['wager_states']}") + "\n")
                w(bar("dominated experiments",
                      f"{g['dominated_experiments'] or 'none'}") + "\n")
                w(bar("REAL decisions per run",
                      f"{g['real_decisions_per_run']} of {g['cuts_per_run']} cuts "
                      f"(a cut counts when some LEGAL charge loses the guarantee)")
                  + "\n")
                w(bar("code slack",
                      f"2^worst - manual = {g['code_slack_bits']}   "
                      f"(0 is a perfect code, and tighter is HARDER)") + "\n")
                w("\n  charge  engages/slips   bits   worst case if opened here\n")
                for o in g["opening_table"]:
                    mark = "" if o["keeps_the_budget"] else "   <- loses the guarantee"
                    w(f"  {o['charge']:<7} {o['engages']:>2}/{o['slips']:<2}"
                      f"          {o['information_bits']:<6} "
                      f"{o['worst_case_total']}{mark}\n")
                w(f"\n  charge  best-in over {g['branching_posteriors']} branching "
                  f"posteriors (worst case / expectation)   mean bits\n")
                for c in g["probe_best_in_worst_case"]:
                    w(f"  {c:<7} {g['probe_best_in_worst_case'][c]:>4} /"
                      f"{g['probe_best_in_expectation'][c]:<4}"
                      f"                                       "
                      f"{g['probe_mean_bits'][c]}\n")
                w("\n")

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
# backend 6 — push-your-luck: a PUBLIC escalating hazard over a HIDDEN shared
#             reward table.  Vent Crawl.
# ---------------------------------------------------------------------------

def _u_identity(x):
    return float(x)


def _u_sqrt(x):
    return math.sqrt(float(x))


def _u_log(x):
    return math.log(1.0 + float(x))


def _u_quota(n):
    def u(x):
        return 1.0 if x >= n else 0.0
    return u


def _close(a, b):
    return abs(a - b) <= 1e-12 * max(1.0, abs(a), abs(b))


class PushYourLuckGame:
    """A descriptor carrying `vent`: an escalating PUBLISHED hazard over a hidden
    shared reward table.

    ⚑ WHY THIS IS NOT `DescentRules` OR `ParametricMachineGame`.  Descent hides the
    RISK — a chamber's passage is unknown until a body or a survey resolves it — and
    its rows are two-branch resolves whose branches are the two readings of one bit.
    Vent Crawl hides the REWARD and publishes the risk in full: a crawl row carries
    the exact flood numerator against `faces`, and its branches are the flood plus
    ONE SUCCESSOR PER STILL-POSSIBLE VEIN.  A backend that reads `on_match` /
    `on_mismatch` cannot see a four-way haul, and a backend that treats the hazard as
    hidden would report the published odds as an unreachable field.

    ⚑ A COST ROW IS NOT A TRANSITION, and this backend computes no cost row.  Every
    number below comes from walking the REAL transition the emitted table names, and
    the stopping analysis is an exact backward induction over the BELIEF state — which
    is what a push-your-luck game IS.  Ranking `crawl` against `bank` by what they
    spend would rank `bank` as free and `crawl` as free and say nothing.

    ## What is reconstructed, and from what

    Everything comes from the descriptor: the `vent` block (depth cap, faces, the
    flood ladder, the four vein yield/carry tables, the refusal vocabulary) and the
    emitted state VIEWS.  Nothing is read from the Lean module.  In particular NO
    NAME IS TRUSTED:

      * the CRAWL action is whichever action id carries a `wager` row; the BANK
        action is the other one, and there must be exactly two;
      * `crawling` is whatever outcome the INITIAL state view reads; `drowned` is
        whatever a wager's `on_flood` successor reads; `banked` is whatever a bank
        row's successor reads — and the three must be distinct;
      * the three REFUSAL REASONS are derived from the three situations that produce
        them and are then checked against `vent.refusal_vocabulary` in BOTH
        directions, so a declared reason that never fires is a finding and an
        undeclared reason that fires is a refusal.

    ## What is checked

      1. every one of the emitted rows: verdict, reason, successor ids, the published
         flood numerator, and the haul list vein-by-vein;
      2. every emitted view's derived fields, including `still_possible` and
         `next_flood_below`;
      3. the emitted state set IS the branch closure of the initial state;
      4. the per-vein census — reachable states, decision states, drowned states —
         computed by this file's own search over this file's own reconstruction, and
         then compared against the kernel's claim;
      5. ⚑ THE STOPPING RULES.  An exact backward induction over the belief state,
         under EIGHT risk postures, reporting which verb each posture wants at each
         reachable state, which verbs are optimal under no posture anywhere, and
         whether the whole game collapses to one fixed depth threshold.

    Points 4 and 5 are the ones that matter.  Point 4 is two independent sources
    compared; point 5 is the only question that decides whether the thing is a game.
    """

    # The kernel's claim, as a claim.  ⚠ NOT an input to anything computed below —
    # the census is complete before this dict is consulted, and consulting it can only
    # produce a finding.
    KERNEL_SHAPE = {
        "parametric_states": 51,
        "family_reachable": 136,
        "family_decisions": 40,
        "family_drowned": 40,
        "source": "VentCrawl.parametric_shape_is_measured + "
                  "VentCrawl.family_shape_is_measured (native_decide)",
    }

    # Eight postures.  ⚠ These are NOT a sensitivity sweep around one answer: a quota
    # posture is a player who needs a number tonight, and it is the commonest real
    # posture in a daily game.  A game whose verb choice is the same under all eight
    # has one answer and is a ritual.
    #
    # ⚑ `cartographer` is the posture that is paid in MAP rather than salvage, and its
    # payoff is READ OFF THE DESCRIPTOR (`vent.payout.map_banked` / `map_drowned`), not
    # modelled here.  It used to be modelled here — as "value = depth reached" — and
    # that made this backend the second copy of a payout rule the kernel already owns:
    # a re-priced consolation could not have moved it, and the posture would have gone
    # on reporting a defect the game had fixed (or missing one it had introduced).  The
    # rule is the emitted one or the descriptor is refused.
    POSTURES = [
        ("risk-neutral", "salvage", _u_identity),
        ("sqrt-averse", "salvage", _u_sqrt),
        ("log-averse", "salvage", _u_log),
        ("quota-6", "salvage", _u_quota(6)),
        ("quota-12", "salvage", _u_quota(12)),
        ("quota-24", "salvage", _u_quota(24)),
        ("quota-40", "salvage", _u_quota(40)),
        ("cartographer", "map", None),
    ]

    def __init__(self, doc: dict, rep: Report) -> None:
        self.doc = doc
        self.rep = rep
        self.name = doc["game_id"]
        vent = doc.get("vent")
        if not isinstance(vent, dict):
            raise Refusal("push-your-luck descriptor carries no `vent` block, so there "
                          "is nothing to rebuild the rules from")
        self.depth_cap = vent["depth_cap"]
        self.faces = vent["faces"]
        self.mouth = vent["mouth_salvage"]
        self.initial_depth = vent["initial_depth"]
        self.budget = doc["action_limit"]
        self.declared_reasons = list(vent["refusal_vocabulary"])

        self.flood_below = {}
        for entry in vent["flood_below"]:
            rung, below = entry
            self.flood_below[rung] = below
        for rung in range(1, self.depth_cap + 1):
            if rung not in self.flood_below:
                raise Refusal(f"the flood ladder has no entry for rung {rung}")
            if self.flood_below[rung] >= self.faces:
                raise Refusal(
                    f"rung {rung} floods on {self.flood_below[rung]} of {self.faces} "
                    f"faces, which is certain death — a rung nobody can survive is a "
                    f"wall, not a wager")
        ladder = [self.flood_below[r] for r in range(1, self.depth_cap + 1)]
        if any(b > a for a, b in zip(ladder[1:], ladder[:-1])):
            raise Refusal(
                f"the hazard does not escalate: the flood ladder is {ladder}.  A "
                f"push-your-luck game whose risk does not rise with depth has no "
                f"reason for a player to ever stop")

        self.vein_order = []
        self.veins = {}
        for vein in vent["veins"]:
            vid = vein["id"]
            if vid in self.veins:
                raise Refusal(f"the vent names the vein {vid!r} twice")
            yields = [int(y) for y in vein["yields"]]
            carry = [int(c) for c in vein["carry"]]
            if len(yields) != self.depth_cap:
                raise Refusal(f"vein {vid} declares {len(yields)} yields for "
                              f"{self.depth_cap} rungs")
            if len(carry) != self.depth_cap + 1 or carry[0] != 0:
                raise Refusal(f"vein {vid}'s carry ladder is not a cumulative sum "
                              f"starting at zero")
            for i in range(self.depth_cap):
                if carry[i + 1] != carry[i] + yields[i]:
                    raise Refusal(
                        f"vein {vid}'s carry ladder disagrees with its own yields at "
                        f"rung {i + 1}: {carry[i]} + {yields[i]} != {carry[i + 1]}")
                if yields[i] <= 0:
                    raise Refusal(
                        f"vein {vid} pays nothing at rung {i + 1}, so crawling into it "
                        f"is pure loss on that day and the row is not a wager")
            self.vein_order.append(vid)
            self.veins[vid] = {"yields": yields, "carry": carry}
        if len(self.vein_order) < 2:
            raise Refusal("the vent declares fewer than two veins, so there is no "
                          "hidden table for a commitment to bind")

        opening = {self.veins[v]["carry"][self.initial_depth] for v in self.vein_order}
        if len(opening) != 1:
            raise Refusal(
                "the veins do not agree at the opening depth, so a run's starting "
                "sling already names the day and the table is not hidden at all")

        # ⚑ THE CONSOLATION, AS NUMBERS.  `vent.payout.map_*` gives, per depth, what a
        # run that came home and a run the water took are paid for the shaft they
        # mapped.  The `cartographer` posture is built from THESE and from nothing this
        # file knows, so the question "is the losing branch actually a loss?" is asked
        # of the descriptor rather than of a rule written here.  ⚠ No fallback: a
        # descriptor that does not carry the ladders is REFUSED, because the alternative
        # is a posture quietly reverting to this file's own guess at the payout.
        payout = vent.get("payout")
        if not isinstance(payout, dict):
            raise Refusal("the vent carries no `payout` block, so what a run is paid "
                          "for reaching a rung is not in the descriptor at all")
        ladders = {}
        for key in ("map_banked", "map_drowned"):
            ladder = payout.get(key)
            if not isinstance(ladder, list) or len(ladder) != self.depth_cap + 1:
                raise Refusal(
                    f"`vent.payout.{key}` is not a ladder over depths 0..{self.depth_cap}; "
                    f"a posture that is paid in map cannot be rebuilt from the bytes and "
                    f"this backend will not model one from its own source")
            if not all(isinstance(x, int) and x >= 0 for x in ladder):
                raise Refusal(f"`vent.payout.{key}` carries something that is not a "
                              f"count of rungs mapped")
            ladders[key] = [int(x) for x in ladder]
        self.map_banked = ladders["map_banked"]
        self.map_drowned = ladders["map_drowned"]

    # -- the alphabet, derived rather than named ----------------------------

    def learn_alphabet(self) -> None:
        """Separate the two verbs and the three outcomes without trusting a name."""
        sm = self.doc["state_machine"]
        self.action_ids = [a["id"] for a in sm["actions"]]
        if len(self.action_ids) != 2:
            raise Refusal(f"this backend models exactly two verbs; the descriptor "
                          f"declares {len(self.action_ids)}")
        wagering = {t["state"] for t in sm["transitions"] if t["verdict"] == "wager"}
        wager_actions = {t["action"] for t in sm["transitions"]
                         if t["verdict"] == "wager"}
        if len(wager_actions) != 1:
            raise Refusal(f"{len(wager_actions)} actions carry a wager row; exactly one "
                          f"verb may consult the hidden table")
        if not wagering:
            raise Refusal("no row wagers, so the hidden table cannot affect play and "
                          "there is nothing for a commitment to bind")
        self.crawl_action = wager_actions.pop()
        others = [a for a in self.action_ids if a != self.crawl_action]
        self.bank_action = others[0]

        self.crawling = self.states[self.initial]["view"]["outcome"]
        drowned = {self.states[t["on_flood"]]["view"]["outcome"]
                   for t in sm["transitions"] if t["verdict"] == "wager"}
        if len(drowned) != 1:
            raise Refusal(f"the wager rows flood into {len(drowned)} distinct outcomes")
        self.drowned = drowned.pop()
        banked = {self.states[t["next"]]["view"]["outcome"]
                  for t in sm["transitions"]
                  if t["verdict"] == "accept" and t["action"] == self.bank_action}
        if len(banked) != 1:
            raise Refusal(f"the bank rows accept into {len(banked)} distinct outcomes")
        self.banked = banked.pop()
        if len({self.crawling, self.drowned, self.banked}) != 3:
            raise Refusal(
                f"crawling/drowned/banked are not three distinct outcomes "
                f"({self.crawling!r}/{self.drowned!r}/{self.banked!r}); a run that "
                f"cannot be told apart from a drowned one has no push and no luck")

        # The three refusal reasons, derived from the three situations that produce
        # them and checked in BOTH directions against the declared vocabulary.
        self.reason_of = {}
        for t in sm["transitions"]:
            if t["verdict"] != "refuse":
                continue
            st = self.state_of[t["state"]]
            key = self.refusal_key(st, t["action"])
            if key is None:
                raise Refusal(
                    f"{t['state']}/{t['action']} refuses and the rebuilt rule says it "
                    f"is open")
            prior = self.reason_of.get(key)
            if prior is None:
                self.reason_of[key] = t["reason"]
            elif prior != t["reason"]:
                raise Refusal(
                    f"the same refusal situation {key!r} carries two reasons "
                    f"({prior!r} and {t['reason']!r}), so a client renders a different "
                    f"story for the same fact")
        fired = set(self.reason_of.values())
        declared = set(self.declared_reasons)
        if fired - declared:
            raise Refusal(f"the table refuses for reasons the vent does not declare: "
                          f"{sorted(fired - declared)}")
        self.never_fires = sorted(declared - fired)

    def refusal_key(self, st, aid):
        depth, carried, outcome = st
        if outcome == self.banked:
            return "run-banked"
        if outcome == self.drowned:
            return "run-drowned"
        if aid == self.crawl_action and depth >= self.depth_cap:
            return "at-the-bottom"
        return None

    # -- states and the rebuilt rule ----------------------------------------

    def state_of_view(self, view: dict) -> tuple:
        return (view["depth"], view["carried"], view["outcome"])

    def consistent(self, depth: int, carried: int) -> list:
        return [v for v in self.vein_order
                if depth < len(self.veins[v]["carry"])
                and self.veins[v]["carry"][depth] == carried]

    def is_open(self, st, aid) -> bool:
        depth, _carried, outcome = st
        if outcome != self.crawling:
            return False
        if aid == self.crawl_action:
            return depth < self.depth_cap
        return True

    def step(self, st, aid, vein, flooded: bool):
        depth, carried, _outcome = st
        if aid == self.bank_action:
            return (depth, carried, self.banked)
        if flooded:
            return (depth + 1, 0, self.drowned)
        return (depth + 1, carried + self.veins[vein]["yields"][depth], self.crawling)

    def row_for(self, st, aid):
        """`(verdict, reason, next, flood_below, on_flood, hauls)`."""
        if not self.is_open(st, aid):
            key = self.refusal_key(st, aid)
            return ("refuse", self.reason_of.get(key), None, None, None, None)
        if aid == self.bank_action:
            return ("accept", None, self.step(st, aid, None, False), None, None, None)
        fb = self.flood_below[st[0] + 1]
        return ("wager", None, None, fb, self.step(st, aid, None, True),
                [(v, self.step(st, aid, v, False))
                 for v in self.consistent(st[0], st[1])])

    # -- the differential ----------------------------------------------------

    def differential(self) -> None:
        sm = self.doc["state_machine"]
        self.states = {s["id"]: s for s in sm["states"]}
        self.initial = sm["initial_state"]
        if self.initial not in self.states:
            raise Refusal("the initial state is not among the declared states")
        self.state_of = {}
        self.id_of = {}
        for sid, s in self.states.items():
            st = self.state_of_view(s["view"])
            if st in self.id_of:
                raise Refusal(f"states {self.id_of[st]} and {sid} carry the same view, "
                              f"so the emitted id is not a function of the state")
            self.id_of[st] = st and sid
            self.state_of[sid] = st
        self.trans = {(t["state"], t["action"]): t for t in sm["transitions"]}
        self.learn_alphabet()

        if len(self.trans) != len(self.states) * len(self.action_ids):
            raise Refusal(f"the table is not total: {len(self.trans)} rows for "
                          f"{len(self.states)} states by {len(self.action_ids)} actions")

        # 1. every derived field of every view, rebuilt
        for sid, s in self.states.items():
            depth, carried, outcome = self.state_of[sid]
            v = s["view"]
            if bool(s["terminal"]) != (outcome != self.crawling):
                raise Refusal(f"{sid} disagrees with its own view about being over")
            if bool(v["banked"]) != (outcome == self.banked):
                raise Refusal(f"{sid} misreports the bank")
            if bool(v["drowned"]) != (outcome == self.drowned):
                raise Refusal(f"{sid} misreports the drowning")
            want_fb = self.flood_below.get(depth + 1)
            if want_fb is not None and v["next_flood_below"] != want_fb:
                raise Refusal(
                    f"{sid} publishes odds of {v['next_flood_below']}/{self.faces} for "
                    f"the next rung; the flood ladder gives {want_fb}/{self.faces}.  "
                    f"The hazard is the ONE thing this descriptor is trusted to state "
                    f"and a client renders it before every choice, so this is not a "
                    f"cosmetic field")
            mine = self.consistent(depth, carried)
            if outcome == self.crawling and list(v["still_possible"]) != mine:
                raise Refusal(
                    f"{sid} says the day could still be {list(v['still_possible'])}; "
                    f"the carry ladders leave {mine}")
            if outcome == self.crawling and not mine:
                raise Refusal(f"{sid} is a live state no vein can produce")

        # 2. every row
        for sid, st in self.state_of.items():
            for aid in self.action_ids:
                verdict, reason, nxt, fb, on_flood, hauls = self.row_for(st, aid)
                t = self.trans[(sid, aid)]
                if t["verdict"] != verdict:
                    raise Refusal(f"{sid}/{aid}: the table says {t['verdict']}, the "
                                  f"rebuilt rule says {verdict}")
                if verdict == "refuse":
                    if t["reason"] != reason:
                        raise Refusal(
                            f"{sid}/{aid}: the table refuses for {t['reason']!r}, the "
                            f"rebuilt rule refuses for {reason!r}")
                elif verdict == "accept":
                    self._same_state(sid, aid, "next", t["next"], nxt)
                else:
                    if t["flood_below"] != fb:
                        raise Refusal(
                            f"{sid}/{aid}: the row publishes {t['flood_below']} of "
                            f"{self.faces}, the flood ladder gives {fb}")
                    self._same_state(sid, aid, "on_flood", t["on_flood"], on_flood)
                    emitted = t["hauls"]
                    if len(emitted) != len(hauls):
                        raise Refusal(
                            f"{sid}/{aid} names {len(emitted)} hauls, the still-possible "
                            f"veins number {len(hauls)} — a row that has dropped a day "
                            f"is a row that has leaked one")
                    for got, (vein, mine) in zip(emitted, hauls):
                        if got["vein"] != vein:
                            raise Refusal(f"{sid}/{aid} names vein {got['vein']!r} where "
                                          f"the rebuilt rule has {vein!r}")
                        self._same_state(sid, aid, f"haul[{vein}]", got["next"], mine)

        # 3. the emitted state set IS the branch closure of the initial state
        closure = {self.state_of[self.initial]}
        queue = deque([self.state_of[self.initial]])
        while queue:
            st = queue.popleft()
            for aid in self.action_ids:
                _, _, nxt, _, on_flood, hauls = self.row_for(st, aid)
                for n in [nxt, on_flood] + [h[1] for h in (hauls or [])]:
                    if n is not None and n not in closure:
                        closure.add(n)
                        queue.append(n)
        emitted = set(self.state_of.values())
        if closure != emitted:
            raise Refusal(
                f"the emitted state set is not the closure of the initial state: "
                f"{len(emitted - closure)} declared state(s) are unreachable and "
                f"{len(closure - emitted)} reachable state(s) are not declared")

    def _same_state(self, sid, aid, slot, emitted_id, mine) -> None:
        want = self.id_of.get(mine)
        if want is None:
            raise Refusal(f"{sid}/{aid} {slot}: the rebuilt rule reaches a state the "
                          f"descriptor does not declare")
        if emitted_id != want:
            raise Refusal(f"{sid}/{aid} {slot}: the table names {emitted_id}, the "
                          f"rebuilt rule reaches {want}")

    # -- the census ----------------------------------------------------------

    def census(self) -> dict:
        """Walk the REAL transition on each vein, following BOTH outcomes of every
        rung — which is exactly the set of positions a crawler on that vein can be
        in.  ⚠ The tape is NOT enumerated: it is the crawler's dice, not the day, and
        enumerating faces**depth_cap tapes would be enumerating luck."""
        init = self.state_of[self.initial]
        per_vein, total_reach, total_dec, total_drown = [], 0, 0, 0
        for vein in self.vein_order:
            reach = {init}
            queue = deque([init])
            while queue:
                st = queue.popleft()
                for aid in self.action_ids:
                    if not self.is_open(st, aid):
                        continue
                    outs = ([self.step(st, aid, None, False)]
                            if aid == self.bank_action
                            else [self.step(st, aid, None, True),
                                  self.step(st, aid, vein, False)])
                    for n in outs:
                        if n not in reach:
                            reach.add(n)
                            queue.append(n)
            decisions = sum(1 for st in reach
                            if all(self.is_open(st, a) for a in self.action_ids))
            drowned = sum(1 for st in reach if st[2] == self.drowned)
            per_vein.append({"vein": vein, "reachable": len(reach),
                             "decisions": decisions, "drowned": drowned})
            total_reach += len(reach)
            total_dec += decisions
            total_drown += drowned
        return {"per_vein": per_vein, "family_reachable": total_reach,
                "family_decisions": total_dec, "family_drowned": total_drown}

    # -- ⚑ the stopping rules ------------------------------------------------

    def payoff_for(self, kind, u, outcome, depth, carried):
        """What a posture is worth at a terminal outcome.  ⚠ ONE function, used by the
        induction AND by the findings below: a second copy of this arithmetic is how a
        finding ends up describing a posture the induction never ran.

        The `map` kind indexes the EMITTED consolation ladders by depth, so a game that
        re-prices what a losing run is paid moves this posture without a line changing
        here — and a game that stops pricing it moves this posture too, which is what
        `posture-with-no-tradeoff` reads."""
        if kind == "map":
            ladder = self.map_banked if outcome == self.banked else self.map_drowned
            return float(ladder[depth])
        return u(carried if outcome == self.banked else 0)

    def stopping_rules(self) -> dict:
        """Exact backward induction over the BELIEF state, under every posture.

        The belief state is the emitted state: `carried` at `depth` is exactly the set
        of veins whose carry ladder passes through it, so `consistent()` IS the
        posterior and the prior over veins is uniform.  There is no approximation and
        no sampling here; the recursion is over a DAG whose only edge direction is
        deeper.
        """
        live = sorted((st for st in self.state_of.values() if st[2] == self.crawling),
                      key=lambda s: -s[0])
        results = {}
        for pname, kind, u in self.POSTURES:
            def payoff(outcome, depth, carried, kind=kind, u=u):
                return self.payoff_for(kind, u, outcome, depth, carried)

            value, choice = {}, {}
            for st in live:
                depth, carried, _ = st
                bank_v = payoff(self.banked, depth, carried)
                options = {self.bank_action: bank_v}
                if self.is_open(st, self.crawl_action):
                    fb = self.flood_below[depth + 1]
                    p = fb / self.faces
                    cons = self.consistent(depth, carried)
                    surv = 0.0
                    for vein in cons:
                        nxt = self.step(st, self.crawl_action, vein, False)
                        surv += value[nxt] / len(cons)
                    drown = self.step(st, self.crawl_action, None, True)
                    options[self.crawl_action] = (
                        p * payoff(self.drowned, drown[0], 0) + (1 - p) * surv)
                best = max(options.values())
                value[st] = best
                choice[st] = sorted(a for a, v in options.items() if _close(v, best))
            results[pname] = {"value": value, "choice": choice, "kind": kind}

        # ⚠ A TIE IS NOT A DISAGREEMENT.  A quota posture whose quota is out of reach
        # from here values BOTH verbs at zero, so it "wants both" — and counting that
        # as a live decision would inflate the one number this backend exists to
        # produce.  Only a STRICT preference counts below, and the states where a
        # posture is indifferent are reported separately as what they are: places that
        # posture has nothing to say about.
        strict = {}
        indifferent = {p: [] for p, _, _ in self.POSTURES}
        for pname, _, _ in self.POSTURES:
            choice = results[pname]["choice"]
            strict[pname] = {}
            for st, verbs in choice.items():
                if len(verbs) == 1:
                    strict[pname][st] = verbs[0]
                elif self.is_open(st, self.crawl_action):
                    indifferent[pname].append(st)

        # which verbs are STRICTLY optimal SOMEWHERE, under SOME posture
        live_verbs = {a: [] for a in self.action_ids}
        split_states, policies = [], {}
        for pname, _, _ in self.POSTURES:
            for st, a in strict[pname].items():
                live_verbs[a].append((pname, st))
        for pname, _, _ in self.POSTURES:
            choice = results[pname]["choice"]
            crawls = sorted(st[0] for st in choice
                            if self.crawl_action in choice[st]
                            and self.is_open(st, self.crawl_action))
            banks = sorted(st[0] for st in choice if self.bank_action in choice[st])
            threshold = None
            if crawls and banks and max(crawls) < min(banks):
                threshold = min(banks)
            elif crawls and not banks:
                threshold = self.depth_cap + 1
            elif banks and not crawls:
                threshold = min(banks)
            policies[pname] = {
                "value_at_start": results[pname]["value"][self.state_of[self.initial]],
                "fixed_threshold": threshold,
                "banks_at": sorted({(st[0], st[1]) for st in choice
                                    if self.bank_action in choice[st]
                                    and len(choice[st]) == 1}),
            }
        # ⚠ The split is computed over the SALVAGE postures only.  `cartographer` is
        # paid in MAP rather than in salvage, so counting its disagreement as evidence
        # that the salvage arithmetic is live would make this finding true of ANY game
        # with a consolation payout, including one whose salvage numbers were flat.  It
        # is not excluded from `posture-with-no-tradeoff`, which is the finding that
        # asks whether ITS payout is priced.
        salvage_postures = [p for p, kind, _ in self.POSTURES if kind == "salvage"]
        for st in self.state_of.values():
            if st[2] != self.crawling or not self.is_open(st, self.crawl_action):
                continue
            wants_crawl = {p for p in salvage_postures
                           if strict[p].get(st) == self.crawl_action}
            wants_bank = {p for p in salvage_postures
                          if strict[p].get(st) == self.bank_action}
            if wants_crawl and wants_bank:
                split_states.append(st)

        # the value of the information, priced: the best ADAPTIVE risk-neutral policy
        # against the best policy that ignores everything it sees.
        fixed = []
        survive = 1.0
        for k in range(self.initial_depth, self.depth_cap + 1):
            if k > self.initial_depth:
                survive *= 1 - self.flood_below[k] / self.faces
            carries = [self.veins[v]["carry"][k] for v in self.vein_order]
            mean = sum(carries) / len(carries)
            sq = sum(c * c for c in carries) / len(carries)
            ev = survive * mean
            var = survive * sq - ev * ev
            fixed.append({"depth": k, "reach": survive, "mean_carry": mean,
                          "ev": ev, "sd": math.sqrt(max(0.0, var))})
        best_fixed = max(fixed, key=lambda f: f["ev"])
        adaptive = policies["risk-neutral"]["value_at_start"]

        return {
            "per_posture": policies,
            "split_states": split_states,
            "dead_verbs": [a for a, hits in live_verbs.items() if not hits],
            "fixed_depth_policies": fixed,
            "best_fixed_depth": best_fixed,
            "indifferent": indifferent,
            "strict": strict,
            "salvage_postures": salvage_postures,
            "adaptive_risk_neutral": adaptive,
            "information_gain": (adaptive / best_fixed["ev"] - 1.0
                                 if best_fixed["ev"] > 0 else 0.0),
            "choices": {pname: results[pname]["choice"] for pname, _, _ in self.POSTURES},
        }

    # -- the report ----------------------------------------------------------

    def analyse(self) -> dict:
        rep, name = self.rep, self.name
        self.differential()
        cen = self.census()
        stop = self.stopping_rules()

        # ⚑ the cross-check.  Two independent sources, compared.
        k = self.KERNEL_SHAPE
        mine = (len(self.states), cen["family_reachable"], cen["family_decisions"],
                cen["family_drowned"])
        theirs = (k["parametric_states"], k["family_reachable"], k["family_decisions"],
                  k["family_drowned"])
        if mine != theirs:
            rep.find(name, "kernel-census-disagreement", FAIL,
                     "the gate and the kernel disagree about the shape of the game",
                     f"walking the emitted descriptor gives {mine[0]} declared states / "
                     f"{mine[1]} reachable / {mine[2]} decisions / {mine[3]} drowned "
                     f"across {len(self.vein_order)} veins; {k['source']} asserts "
                     f"{theirs}.  These are independent — one is a compiled evaluation "
                     f"of the kernel's own definitions, the other is a simulation of "
                     f"the bytes a client downloads — so a disagreement means the "
                     f"descriptor and the engine are not the same game.")
        else:
            rep.find(name, "family-shape-agrees", INFO,
                     f"{mine[0]} states, {mine[1]} reachable across the vein family, "
                     f"{mine[2]} decision states, {mine[3]} drowned — arrived at twice",
                     f"this tool rebuilt the rules from `vent`, derived both verbs and "
                     f"all three outcomes WITHOUT trusting a name, checked all "
                     f"{len(self.trans)} emitted rows against them, then walked the real "
                     f"transition on each of the {len(self.vein_order)} veins.  It gets "
                     f"{mine}, and {k['source']} independently asserts the same tuple.  "
                     f"A pin against its own definition is decoration; this is two "
                     f"sources.")

        # ⚑ the stopping-rule findings — the ones this game lives or dies on
        if stop["dead_verbs"]:
            rep.find(name, "dominated-verb", FAIL,
                     f"{stop['dead_verbs']} is optimal under NO posture at ANY reachable "
                     f"state",
                     f"a push-your-luck game is the tension between two verbs.  A verb "
                     f"that no risk posture ever wants is not a choice a player has; it "
                     f"is a button that is always wrong, and the game is the other verb "
                     f"repeated until it ends.")
        decisions = len(stop["choices"]["risk-neutral"]) and len(
            [s for s in self.state_of.values()
             if s[2] == self.crawling and self.is_open(s, self.crawl_action)])
        if not stop["split_states"]:
            rep.find(name, "flat-stopping-rule", FAIL,
                     "no reachable state is decided differently by any two risk postures",
                     f"every one of the {len(stop['salvage_postures'])} salvage postures "
                     f"— risk-neutral, two concave utilities and four quotas — STRICTLY "
                     f"prefers the same verb at every state a crawler can be in.  That "
                     f"means the stopping rule is a constant a player computes once and "
                     f"never thinks about again, which is the failure mode this whole "
                     f"backend exists to catch.")
        else:
            rep.find(name, "stopping-rule-is-live", INFO,
                     f"{len(stop['split_states'])} of {decisions} decision states are "
                     f"decided differently by different risk postures",
                     f"at {sorted((s[0], s[1]) for s in stop['split_states'])} "
                     f"(as depth/carried) at least one salvage posture STRICTLY prefers "
                     f"crawl and another STRICTLY prefers bank, so there is no single "
                     f"right answer to hand a player.  ⚠ Two exclusions, because both "
                     f"would inflate this number: a posture that VALUES BOTH VERBS "
                     f"EQUALLY is indifferent, not disagreeing (a quota out of reach "
                     f"from here is worth zero either way), and `cartographer` is "
                     f"excluded entirely because it is paid in the emitted MAP ladders "
                     f"rather than in salvage and would therefore disagree in a game "
                     f"whose salvage numbers were flat.  The induction is exact, over "
                     f"the BELIEF state, with a uniform prior over veins.")

        # ⚑ A POSTURE WITH NO TRADEOFF — and the one exclusion that is not a weakening.
        #
        # Two different causes used to land in this finding, and it said so itself in
        # the same breath as raising a WARN for both.  A gate that reports a cause it
        # declares is not a defect is a gate that has to be read past, so the causes are
        # now SEPARATED BY A TEST rather than by prose:
        #
        #   (a) THE LOSS IS NOT A LOSS.  The posture's payout is not priced against the
        #       risk — the drowned branch of a wager is worth as much as climbing out
        #       from where the crawler stood — so crawling is a free roll and there is
        #       no wager in this game for that player.  A DEFECT IN THE GAME.  This is
        #       what the finding is for and it still fires.
        #   (b) THE POSTURE CANNOT TELL TWO BANKS APART.  A quota above every carry a
        #       decision state can bank scores EVERY bank at zero.  Its preference is
        #       then a fact about the TARGET, not about the ladder, and no change to the
        #       game would give it a decision short of lowering the target.
        #
        # ⚠ The test for (b) is deliberately NARROW: the posture's BANK payoff is
        # CONSTANT over every decision state.  A posture that can rank two banks stays
        # inside the check however mute it is elsewhere — an always-crawling
        # risk-neutral player is still caught here — so this exempts a posture that
        # cannot see the game, never one the game has flattened.
        decision_states = [st for st in self.state_of.values()
                           if st[2] == self.crawling
                           and self.is_open(st, self.crawl_action)]
        no_tradeoff, blind_to_the_bank = [], []
        for pname, kind, u in self.POSTURES:
            verbs = {stop["strict"][pname].get(st) for st in decision_states} - {None}
            if len(verbs) >= 2:
                continue
            banks = {self.payoff_for(kind, u, self.banked, st[0], st[1])
                     for st in decision_states}
            (blind_to_the_bank if len(banks) < 2 else no_tradeoff).append(pname)
        if no_tradeoff:
            rep.find(name, "posture-with-no-tradeoff", WARN,
                     f"{no_tradeoff} never faces a decision: one verb is strictly better "
                     f"everywhere, and it CAN tell two banks apart",
                     f"a posture that always crawls (or always banks) wherever it has "
                     f"any preference at all is not playing this game; it is executing "
                     f"a constant.  This posture ranks the bankable outcomes — it is not "
                     f"blind to the ladder — so the constant is the GAME's, not the "
                     f"posture's.  The usual cause is a payout that is not PRICED "
                     f"against the risk: if the losing branch of a wager is worth as "
                     f"much as climbing out from where the crawler stood, the crawl is a "
                     f"free roll and the second verb is decoration.  Price the loss "
                     f"(discount it, cap it, or scale it by what was lost) rather than "
                     f"deleting it, if it is a consolation that exists to make a losing "
                     f"transcript worth submitting.")

        if blind_to_the_bank:
            rep.find(name, "posture-cannot-be-banked-into", INFO,
                     f"{blind_to_the_bank} scores every reachable bank the same, so it "
                     f"has no decision to face",
                     f"a quota above every carry a decision state can bank is worth zero "
                     f"whatever the crawler does short of the bottom, so this posture "
                     f"strictly prefers the same verb everywhere by arithmetic on its "
                     f"TARGET and not by anything the ladder does.  That is not a defect "
                     f"in the game — it is what a player with an impossible number "
                     f"actually faces — and it is reported here, separately from "
                     f"`posture-with-no-tradeoff`, so a target set too high is never "
                     f"read as a game with one answer.")

        mostly_mute = [p for p, sts in stop["indifferent"].items()
                       if decisions and len(sts) > decisions // 2]
        if mostly_mute:
            rep.find(name, "posture-is-mostly-mute", INFO,
                     f"{mostly_mute} is indifferent at more than half the decision states",
                     f"a quota posture is indifferent exactly where its quota is out of "
                     f"reach whatever it does.  That is not a defect — it is what a "
                     f"player with an impossible target actually faces — but it means "
                     f"this posture is carrying less of the split evidence than its "
                     f"presence in the table suggests, and the count above already "
                     f"excludes it at those states.")

        thresholds = {p["fixed_threshold"] for p in stop["per_posture"].values()}
        if len(thresholds) == 1 and None not in thresholds:
            rep.find(name, "single-threshold-game", FAIL,
                     f"every posture reduces to the same fixed depth threshold "
                     f"{thresholds}",
                     "if 'bank at depth k' is optimal for every posture then the hidden "
                     "table buys the player nothing: they crawl to k and stop, forever.")
        elif len([t for t in thresholds if t is not None]) < len(thresholds):
            rep.find(name, "stopping-rule-is-not-a-threshold", INFO,
                     "at least one posture's optimal rule is NOT a fixed depth",
                     f"posture thresholds: "
                     f"{ {p: v['fixed_threshold'] for p, v in stop['per_posture'].items()} }.  "
                     f"A `None` means the posture crawls at some depth and banks at a "
                     f"SHALLOWER one, which can only happen because what it learned "
                     f"changed its mind — the information is doing work.")

        # ⚑ WHERE THE DISCOVERY STOPS.  A push-your-luck game with a learnable table
        # has two halves: rungs where the crawler is still finding out what kind of day
        # it is, and rungs where they already know and are only doing arithmetic.  The
        # second half is not worthless — the hazard is highest there — but it has no
        # discovery in it, and a family that collapses to certainty early spends the
        # deep rungs, which are the tense ones, on a decision with no news in it.
        ambiguous = [st for st in self.state_of.values()
                     if st[2] == self.crawling and self.is_open(st, self.crawl_action)
                     and len(self.consistent(st[0], st[1])) > 1]
        exhausted_at = None
        if ambiguous:
            exhausted_at = max(st[0] for st in ambiguous) + 1
        deep = [st for st in self.state_of.values()
                if st[2] == self.crawling and self.is_open(st, self.crawl_action)]
        if exhausted_at is not None and deep and exhausted_at <= max(
                st[0] for st in deep):
            still_deciding = len([st for st in deep if st[0] >= exhausted_at])
            rep.find(name, "discovery-stops-early", WARN,
                     f"from rung {exhausted_at} on, the day is fully known and "
                     f"{still_deciding} decision state(s) have nothing left to learn",
                     f"only {len(ambiguous)} of {len(deep)} decision states still have "
                     f"more than one possible table.  Past rung {exhausted_at} the "
                     f"crawler is doing arithmetic against a known payout — and those "
                     f"are precisely the rungs with the HIGHEST hazard, so the tensest "
                     f"part of the shaft is the part with no news in it.  The repair is "
                     f"a table family that separates in more stages (more members, "
                     f"or ladders that stay ambiguous deeper), not a change to the "
                     f"hazard.")
        else:
            rep.find(name, "discovery-runs-to-the-bottom", INFO,
                     "the table is still ambiguous at the deepest decision",
                     f"{len(ambiguous)} of {len(deep)} decision states have more than "
                     f"one possible table, including the deepest, so no rung is pure "
                     f"arithmetic.")

        gain = stop["information_gain"]
        if gain < 0.01:
            rep.find(name, "information-is-decoration", WARN,
                     f"the best adaptive policy beats the best fixed-depth policy by "
                     f"{gain * 100:.1f}%",
                     f"the hidden table is observed during play, so an adaptive crawler "
                     f"should beat one that decided its depth before going in.  A gap "
                     f"this small means the observation is not worth acting on and the "
                     f"family could be collapsed to one vein with no loss.")
        else:
            rep.find(name, "information-is-worth-acting-on", INFO,
                     f"the best adaptive policy beats the best fixed-depth policy by "
                     f"{gain * 100:.1f}%",
                     f"exact backward induction over the belief state returns "
                     f"{stop['adaptive_risk_neutral']:.3f} at the mouth; the best policy "
                     f"that ignores what it sees ('always crawl to depth "
                     f"{stop['best_fixed_depth']['depth']}') returns "
                     f"{stop['best_fixed_depth']['ev']:.3f}.  That gap is what reading "
                     f"the shaft is worth.")

        if self.never_fires:
            rep.find(name, "declared-reason-never-fires", FAIL,
                     f"{self.never_fires} is declared and never refuses anything",
                     f"`vent.refusal_vocabulary` names it, so a client will carry a "
                     f"string for it and a reader will believe it is a rule.  A refusal "
                     f"that cannot fire is a rule that does not exist.")
        else:
            rep.find(name, "every-declared-reason-fires", INFO,
                     f"all {len(self.declared_reasons)} declared refusal reasons fire, "
                     f"and nothing else does",
                     f"{sorted(self.declared_reasons)}, checked in both directions "
                     f"against the emitted rows.")

        one_sided = sorted({st[0] for st in self.state_of.values()
                            if st[2] == self.crawling
                            and not all(self.is_open(st, a) for a in self.action_ids)})
        if one_sided and one_sided != [self.depth_cap]:
            rep.find(name, "verb-missing-above-the-bottom", WARN,
                     f"depths {one_sided} offer only one verb",
                     "a live crawler should always be able to choose.  The bottom rung "
                     "is expected (there is nowhere deeper); anything else is a place "
                     "the game plays itself.")

        if cen["family_drowned"] == 0:
            rep.find(name, "cannot-be-lost", FAIL,
                     "no reachable state is drowned, so the crawl cannot be lost",
                     "a run that cannot fail is not a wager.")

        shapes = {(v["reachable"], v["decisions"], v["drowned"]) for v in cen["per_vein"]}
        carries = {self.veins[v]["carry"][self.depth_cap] for v in self.vein_order}
        if len(carries) < len(self.vein_order):
            rep.find(name, "the-family-collapses", WARN,
                     f"the {len(self.vein_order)} veins produce only {len(carries)} "
                     f"distinct deepest carries",
                     "two hidden draws that pay the same at the bottom are the same day "
                     "under a relabelling.")
        elif len(shapes) == 1:
            rep.find(name, "veins-share-a-state-shape", INFO,
                     "every vein spans the same number of states",
                     f"all {len(self.vein_order)} veins reach {shapes} — which is "
                     f"expected here and is NOT the collapse finding: the shaft is one "
                     f"shaft, so the POSITIONS coincide while the PAYOUTS "
                     f"({sorted(carries)}) do not.  The bits are in the carry, not the "
                     f"topology.")

        refuse_rows = sum(1 for t in self.trans.values() if t["verdict"] == "refuse")
        accept_rows = sum(1 for t in self.trans.values() if t["verdict"] == "accept")
        wager_rows = sum(1 for t in self.trans.values() if t["verdict"] == "wager")
        reasons = Counter(t["reason"] for t in self.trans.values()
                          if t["verdict"] == "refuse")

        # information floor: how many rungs must be crawled before the carry ladder
        # names the day.  Computed from the ladders, not declared.
        floor = None
        for d in range(self.initial_depth, self.depth_cap + 1):
            if len({self.veins[v]["carry"][d] for v in self.vein_order}) == \
                    len(self.vein_order):
                floor = d - self.initial_depth
                break

        longest = 0
        for pname, _, _ in self.POSTURES:
            choice = stop["choices"][pname]
            depth, actions = self.state_of[self.initial], 0
            st = depth
            while self.crawl_action in choice.get(st, []) and \
                    self.is_open(st, self.crawl_action):
                # follow the modal (first-listed) vein; every vein gives the same depth
                st = self.step(st, self.crawl_action, self.consistent(st[0], st[1])[0],
                               False)
                actions += 1
            longest = max(longest, actions + 1)

        self.stop = stop
        self.cen = cen
        return {
            "game": name,
            "kind": "push-your-luck",
            "engine_module": self.doc["engine_module"],
            "states": len(self.states),
            "reachable_states": len(self.states),
            "actions": len(self.action_ids),
            "transitions": len(self.trans),
            "accept_rows": accept_rows,
            "refuse_rows": refuse_rows,
            "oracle_rows": wager_rows,
            "refusal_reasons": dict(reasons),
            "information_floor_tight": floor,
            "execution_floor_as_emitted": 1,
            "worst_case_optimal": longest,
            "worst_case_any_legal_play": self.budget,
            "action_limit": self.budget,
            "budget_binds": longest >= self.budget,
            "budget_slack": self.budget - longest,
            "can_lose": True,
            "opener_classes": len(self.action_ids),
            "openers_total": len(self.action_ids),
            "automorphism_group_order": 1,
            "depth_cap": self.depth_cap,
            "faces": self.faces,
            "veins": len(self.vein_order),
            "flood_ladder": [self.flood_below[r]
                             for r in range(1, self.depth_cap + 1)],
            "family_reachable": cen["family_reachable"],
            "family_decisions": cen["family_decisions"],
            "family_drowned": cen["family_drowned"],
            "per_vein": cen["per_vein"],
            "posture_count": len(self.POSTURES),
            "posture_split_states": [list(s) for s in stop["split_states"]],
            "posture_thresholds": {p: v["fixed_threshold"]
                                   for p, v in stop["per_posture"].items()},
            "posture_values": {p: v["value_at_start"]
                               for p, v in stop["per_posture"].items()},
            "fixed_depth_policies": stop["fixed_depth_policies"],
            "best_fixed_depth": stop["best_fixed_depth"]["depth"],
            "adaptive_risk_neutral": stop["adaptive_risk_neutral"],
            "information_gain": stop["information_gain"],
            "dead_actions": stop["dead_verbs"],
            "stopping_table": self.stopping_table(stop),
            "kernel_shape": dict(self.KERNEL_SHAPE),
        }

    def stopping_table(self, stop) -> list:
        """One row per reachable decision state: what each posture wants there."""
        rows = []
        for st in sorted((s for s in self.state_of.values()
                          if s[2] == self.crawling), key=lambda s: (s[0], s[1])):
            if not self.is_open(st, self.crawl_action):
                continue
            cell = {}
            for pname, _, _ in self.POSTURES:
                verbs = stop["choices"][pname][st]
                # `=` is INDIFFERENCE, not "both are good": the posture values the two
                # verbs identically, which for a quota means it is out of reach either
                # way.  Rendering it as `bank/crawl` reads as a live two-sided choice
                # and it is the opposite of one.
                cell[pname] = verbs[0] if len(verbs) == 1 else "="
            rows.append({"depth": st[0], "carried": st[1],
                         "still_possible": self.consistent(st[0], st[1]),
                         "flood_below": self.flood_below[st[0] + 1],
                         "postures": cell})
        return rows


# ---------------------------------------------------------------------------

def pick_backend(doc: dict):
    """Dispatch on the SHAPE, so a descriptor cannot pick its own analyser by id."""
    if "oracle" in doc:
        return ProbeOracleGame
    if "rules" in doc:
        return DeductionGame
    if "vent" in doc:
        return PushYourLuckGame
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
