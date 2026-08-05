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
    """A descriptor carrying `outcomes` : guess -> feedback for one pinned target."""

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
        self.codes = [tuple(c) for c in
                      itertools.product(range(self.alphabet), repeat=self.bands)]
        self.index = {c: i for i, c in enumerate(self.codes)}
        self.n = len(self.codes)

    # -- rule model, then differential against every emitted row ------------
    def feedback(self, target, guess):
        exact = sum(1 for i in range(self.bands) if target[i] == guess[i])
        ct, cg = Counter(target), Counter(guess)
        total = sum(min(ct[x], cg[x]) for x in ct.keys() | cg.keys())
        return exact, total - exact

    def build(self) -> None:
        self.fb = [[0] * self.n for _ in range(self.n)]
        self.cls_id: dict[tuple[int, int], int] = {}
        for t in self.codes:
            row = self.fb[self.index[t]]
            for g in self.codes:
                pair = self.feedback(t, g)
                cid = self.cls_id.setdefault(pair, len(self.cls_id))
                row[self.index[g]] = cid
        self.win = self.cls_id[(self.bands, 0)]
        self.classes = len(self.cls_id)

    def differential(self) -> None:
        """The reconstructed rules must reproduce the emitted table byte for byte."""
        target = tuple(self.doc["target"])
        emitted = {}
        for row in self.doc["outcomes"]:
            emitted[tuple(row["guess"])] = (row["exact"], row["present"], row["solved"])
        if len(emitted) != self.n:
            raise Refusal(f"outcomes table has {len(emitted)} distinct guesses, "
                          f"expected the complete {self.n}-row domain")
        bad = []
        for g in self.codes:
            e, p = self.feedback(target, g)
            want = (e, p, g == target)
            if emitted[g] != want:
                bad.append((g, emitted[g], want))
        if bad:
            raise Refusal(
                f"reconstructed rules disagree with the emitted table on {len(bad)} "
                f"row(s); first: guess={bad[0][0]} emitted={bad[0][1]} model={bad[0][2]}")
        solved_rows = [tuple(r["guess"]) for r in self.doc["outcomes"] if r["solved"]]
        if solved_rows != [target]:
            raise Refusal(f"solved rows {solved_rows} are not exactly the target {target}")

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

        target = tuple(self.doc["target"])
        target_realized = sorted({self.feedback(target, g) for g in self.codes})
        target_orbit = next(o for o in code_orbits if target in o)
        target_shape = shape_name(target_orbit[0])

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

        if self.doc["security"]["target_visibility"] == "public" and "target" in self.doc:
            rep.find(self.name, "instance-secret-published", WARN,
                     "the hidden instance is published in the descriptor the client fetches",
                     f"`target` = {list(target)} is a top-level field of "
                     f"{self.name}.json, and `outcomes` marks the solving row "
                     f"`solved: true`.  Information floor {info_tight} describes a game "
                     f"whose target is hidden; as emitted the execution floor is 1 guess "
                     f"and the deduction is decorative.  This is consistent with the "
                     f"declared `transparent-beta-demo` classification — it is a design "
                     f"fact to decide about, not a leak to patch quietly.")

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
            "execution_floor_as_designed": 1,
            "execution_floor_as_emitted": 1 if "target" in self.doc else None,
            "budget_binds": optimum is not None and optimum >= self.budget,
            "budget_slack": None if optimum is None else self.budget - optimum,
            "opener_classes": len(code_orbits),
            "openers_total": self.n,
            "opener_analysis": opener_values,
            "dead_openers": sum(o["size"] for o in dead_openers),
            "reference_policies": policies,
            "pinned_instance": {"target": list(target), "class": target_shape,
                                "feedback_classes_realizable": len(target_realized)},
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
    """The board is drawn from `run_seed` by four consuming draws over the 90 boards
    that carry two copies of each of three glyphs.  Rebuild it, differentially check
    the pinned one against BOTH the emitted action table and the emitted transitions,
    then ask what the seed actually changes."""
    name = doc["game_id"]
    slots, glyphs = 6, 3
    seed_space = list(range(90))
    pinned, digits = salvage_seed_from_run_seed(doc["run_seed"])
    if pinned is None:
        raise Refusal(f"the pinned run_seed exhausts its bytes after {len(digits)} of "
                      f"4 draws; no board is determined")

    pairs, row = salvage_board(pinned)
    emitted = {a["slot"]: a["glyph_id"] for a in doc["state_machine"]["actions"]}
    model = {s: row[s] for s in range(slots)}
    if emitted != model:
        raise Refusal(f"rebuilt glyph board {model} disagrees with the emitted action "
                      f"table {emitted} for seed {pinned} (drawn from run_seed "
                      f"{doc['run_seed'][:16]}...).  Re-emit the descriptor from Lean.")
    from_transitions = salvage_pairing_from_transitions(doc)
    if from_transitions != pairs:
        raise Refusal(f"the emitted transition table pairs {from_transitions} while the "
                      f"rebuilt board pairs {pairs}: the action rows and the successors "
                      f"describe different boards")

    families = defaultdict(list)
    boards = set()
    for seed in seed_space:
        seed_pairs, seed_row = salvage_board(seed)
        families[tuple(seed_pairs)].append(seed)
        boards.add(tuple(seed_row))
        counts = sorted(Counter(seed_row).values())
        if counts != [2, 2, 2]:
            raise Refusal(f"seed {seed} rebuilds to {seed_row}, which is not two of "
                          f"each glyph")

    summary["seed_space"] = len(seed_space)
    summary["pinned_seed"] = pinned
    summary["seed_draws"] = digits
    summary["distinct_pairings_over_seed_space"] = len(families)
    summary["distinct_boards_over_seed_space"] = len(boards)
    summary["pairing"] = [list(p) for p in pairs]
    summary["glyph_populations"] = sorted(Counter(row).values())

    hidden_worst, matchings = hidden_pairing_worst_case(slots)
    summary["counterfactual_hidden_boards"] = matchings
    summary["counterfactual_hidden_worst_case"] = hidden_worst

    if len(families) < matchings:
        rep.find(name, "seed-underdetermines-board", WARN,
                 f"the {len(seed_space)} seeds reach only {len(families)} of the "
                 f"{matchings} perfect matchings",
                 f"a seed space that cannot name every matching hands some boards to "
                 f"nobody, and a player who knows the reachable set starts with "
                 f"information the design did not mean to give.")
    else:
        rep.find(name, "seed-names-the-board", INFO,
                 f"the seed space is exactly the {len(boards)} two-of-each boards, over "
                 f"all {matchings} perfect matchings",
                 f"`run_seed` is drawn by four consuming rejection-sampled draws "
                 f"(bounds 5, 3, 3, 2 -> digits {digits}) into board {pinned} of "
                 f"{len(seed_space)}, whose pairing is {[list(p) for p in pairs]} and "
                 f"whose row is {row}.  Each of the {matchings} matchings is carried by "
                 f"{len(seed_space) // len(families)} seeds — its 3! glyph "
                 f"relabellings — so a glyph name says nothing about the pairing beyond "
                 f"agreement with a glyph already seen.  There is no memory-free "
                 f"routine: `pair = slot mod {glyphs}` is wrong on "
                 f"{matchings - 1} of the {matchings} matchings.")

    rep.find(name, "budget-sized-for-a-board-that-is-not-hidden", INFO,
             f"the budget fits a genuinely hidden board ({hidden_worst} turns) but the "
             f"emitted board needs {summary['execution_floor_as_emitted']}",
             f"against a uniformly drawn one of the {matchings} perfect matchings of "
             f"{slots} plates, a perfect-memory player facing an adaptive adversary "
             f"needs {hidden_worst} turns in the worst case — which is what "
             f"`action_limit = {doc['action_limit']}` looks sized for.  The board IS "
             f"now drawn from that family, so the {hidden_worst} is the honest cost of "
             f"the game underneath; the emitted descriptor still publishes the instance "
             f"(see `instance-secret-published`), so a player who reads it needs "
             f"{summary['execution_floor_as_emitted']}.  Closing that gap is a wire "
             f"change — a commitment to the board plus per-exposure openings — not a "
             f"budget change.")


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
    want = {"seed_byte", "modulus", "selected", "source", "sink", "boards"}
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

    byte = int(doc["run_seed"][2 * inst["seed_byte"]:2 * inst["seed_byte"] + 2], 16)
    if byte % inst["modulus"] != inst["selected"]:
        raise Refusal(f"run_seed byte {inst['seed_byte']} = {byte} selects board "
                      f"{byte % inst['modulus']}, but the descriptor claims "
                      f"{inst['selected']}")
    board = boards[inst["selected"]]
    costs, crate = board["costs"], board["spares"]

    def route_cost(links):
        return sum(costs[l] for l in links)

    def solved_by(installed):
        return any(all(l in installed for l in r) for r in routes)

    def completable(installed, turns, spares):
        for r in routes:
            missing = [l for l in r if l not in installed]
            if len(missing) + turns <= budget and route_cost(missing) <= spares:
                return True
        return False

    # -- differential 1: every emitted state view is what the board implies --------
    facts = {}
    for state in doc["state_machine"]["states"]:
        view = state["view"]
        installed = set(view["installed"])
        if not installed <= action_ids:
            raise Refusal(f"state {state['id']} installs an unknown link")
        spares = crate - route_cost(installed)
        solved = solved_by(installed)
        stranded = not solved and not completable(installed, view["turns"], spares)
        got = (state["terminal"], view["solved"], view["spares"], view["stranded"])
        model = (solved, solved, spares, stranded)
        if got != model:
            raise Refusal(
                f"rebuilt board disagrees with emitted state {state['id']}: "
                f"(terminal, solved, spares, stranded) emitted={got} model={model}")
        facts[state["id"]] = (installed, view["turns"], spares, solved, stranded)

    # -- differential 2: every emitted row is what the rule implies ----------------
    for t in doc["state_machine"]["transitions"]:
        installed, turns, spares, solved, stranded = facts[t["state"]]
        link = t["action"]
        legal = (not solved and turns < budget and not stranded
                 and link not in installed and costs[link] <= spares)
        if legal != (t["verdict"] == "accept"):
            raise Refusal(f"rebuilt rule disagrees with emitted row {t['state']}/"
                          f"{link}: model says {'accept' if legal else 'refuse'}")
        if legal:
            nxt = facts[t["next"]]
            if nxt[0] != installed | {link} or nxt[1] != turns + 1:
                raise Refusal(f"row {t['state']}/{link} accepts into {t['next']}, "
                              f"which is not that install")
        else:
            claim = {"solved": solved, "turn-limit": turns >= budget,
                     "already-installed": link in installed,
                     "no-spares": costs[link] > spares, "stranded": stranded}
            if t["reason"] not in claim:
                raise Refusal(f"row {t['state']}/{link} refuses with unmodelled "
                              f"reason {t['reason']!r}")
            if not claim[t["reason"]]:
                raise Refusal(f"row {t['state']}/{link} refuses as {t['reason']!r}, "
                              f"which is false of that state")

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
    summary["selected_board"] = inst["selected"]
    summary["routes_source_to_sink"] = [list(r) for r in routes]
    summary["selected_route_costs"] = {"|".join(r): route_cost(r) for r in routes}
    summary["selected_crate"] = crate
    summary["distinct_instances_expressible"] = distinct_boards
    summary["distinct_instance_classes"] = distinct_classes
    summary["unwinnable_boards"] = unwinnable
    summary["seed_consumed"] = True

    if unwinnable:
        rep.find(name, "unwinnable-seed", FAIL,
                 f"{len(unwinnable)} board(s) in the seed space cannot be solved at all",
                 f"boards {unwinnable} price every {inst['source']}->{inst['sink']} "
                 f"route above their own crate, so a run that draws one is refused from "
                 f"the first action.  The emitted machine only ever shows board "
                 f"{inst['selected']}; this is visible only from the whole table.")

    if distinct_classes == 1:
        rep.find(name, "seed-inert", WARN,
                 f"all {len(boards)} boards leave the same routes affordable",
                 f"the seed repriced the links but never changed which of the "
                 f"{len(routes)} routes a player can pay for, so the board is "
                 f"decoration and one memorised line clears every seed.")

    rep.find(name, "instance-published-by-design", INFO,
             "the damage board is published in the descriptor, and for this game that "
             "is the design",
             f"`instance` states the crate ({crate} spares), the per-link cost, and all "
             f"{len(boards)} boards the seed can select; run_seed byte "
             f"{inst['seed_byte']} = 0x{byte:02x} selects board {inst['selected']}.  "
             f"Relay Repair is a routing puzzle, not a deduction game: the damage report "
             f"is the material the player reasons over, and hiding it would make the "
             f"read a guess.  What the seed hides is nothing; what it changes is which "
             f"of {len(routes)} routes can be paid for — "
             f"{distinct_classes} distinct affordable-route shapes over "
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
            w(bar("verdicts",
                  f"{g['accept_rows']} accept / {g['refuse_rows']} refuse") + "\n")
            w(bar("refusal reasons",
                  ", ".join(f"{k}:{v}" for k, v in g["refusal_reasons"].items())) + "\n")
            w(bar("distinguishable instances",
                  f"{g['distinguishable_instances']}  -> information floor "
                  f"{g['information_floor_tight']}") + "\n")
            w(bar("execution floor",
                  f"{g['execution_floor_as_emitted']}  (shortest accepted win)") + "\n")
            w(bar("worst case, optimal play",
                  f"{g['worst_case_optimal']}   worst legal play: "
                  f"{g['worst_case_any_legal_play']}") + "\n")
            w(bar("action budget",
                  f"{g['action_limit']}   binds: {g['budget_binds']}   "
                  f"slack: {g['budget_slack']}") + "\n")
            w(bar("can the run be lost?",
                  f"{g['can_lose']}   doomed states: {g['doomed_states']} "
                  f"({g['doomed_still_accepting']} still accept actions)") + "\n")
            w(bar("forks",
                  f"outcome-changing: {g['outcome_forks']}   "
                  f"turn-count-changing: {g['turn_count_forks']}   "
                  f"consequence-free: {g['consequence_free_choices']}") + "\n")
            w(bar("automorphism group order", f"{g['automorphism_group_order']}") + "\n")
            w(bar("opener classes",
                  f"{g['opener_classes']} of {g['openers_total']} legal openers") + "\n")
            w(bar("dead actions", f"{g['dead_actions'] or 'none'}") + "\n")
            w(bar("dominated (state, action)",
                  f"{g['dominated_state_action_pairs']}   globally dominated: "
                  f"{g['globally_dominated_actions'] or 'none'}") + "\n")
            for k in ("seed_space", "pinned_seed", "seed_draws",
                      "distinct_pairings_over_seed_space",
                      "distinct_boards_over_seed_space", "pairing",
                      "counterfactual_hidden_boards",
                      "counterfactual_hidden_worst_case",
                      "board_space", "selected_board", "selected_crate",
                      "routes_source_to_sink", "selected_route_costs",
                      "distinct_instance_classes", "unwinnable_boards",
                      "distinct_instances_expressible", "seed_consumed"):
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

BACKENDS = {"outcomes": DeductionGame, "state_machine": MachineGame}


def analyse_doc(doc: dict, rep: Report) -> dict:
    if doc.get("format") != "POAG1-GAME":
        raise Refusal(f"{doc.get('game_id')} is not a POAG1-GAME descriptor")
    kinds = [k for k in BACKENDS if k in doc]
    if len(kinds) != 1:
        raise Refusal(f"{doc.get('game_id')} carries {kinds or 'no'} analysable shape; "
                      f"this gate models exactly one of {sorted(BACKENDS)}")
    summary = BACKENDS[kinds[0]](doc, rep).analyse()
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
