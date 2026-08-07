#!/usr/bin/env python3
"""check-recursion-closure.py — the recursion firewall, enforced against
`cargo metadata`'s RESOLVE instead of described in a comment.

═══ THE WOUND THIS EXISTS FOR ════════════════════════════════════════════════

`turn/Cargo.toml:17-25` forbids the `dregg-circuit-prove` edge and says why:

    turn's executor VERIFY reconstructs PIs through the `*_wide` generators,
    which are verify-level in `dregg-circuit`, so core turn is recursion-free
    by construction (the seL4 verifier-PD floor and the wasm/zkvm card), not by
    a feature that happened to be off.

That is a claim about a PROPERTY OF THE DEPENDENCY GRAPH, written in prose, and
until this file existed nothing checked it.  Measured 2026-08-05: no `deny.toml`
in the tree, no `[bans]` section, no `cargo tree`/`cargo metadata` gate naming
those crates, and none of `scripts/local-gates.sh`'s rows touching it.  The
crate-extraction design named the gate as its own acceptance criterion
(`docs/reference/TURN-PROVER-CRATE-EXTRACTION-DESIGN.md` §5 PR1: *"`cargo build
-p dregg-turn` is now prover-free and has no `dregg-circuit-prove` edge"*) and
it was never written.

An unenforced firewall is worse than none, because it gets BELIEVED.  This one
was believed hard enough to shape the code: `mina_head_verifier.rs` could not
verify a recursion root at all — while a 46-leaf fold of Mina block 539508's
whole phase-2 transcript sat proved and unreachable — because the comment said
the edge was forbidden and nobody could see that the two justifications it named
had both expired (the seL4 verifier PDs build no dregg crate; the wasm card
already declares `dregg-circuit-prove` on purpose).  A property nobody measures
drifts, and a prose property nobody measures drifts INVISIBLY.

`cargo metadata`'s resolve is this repo's own oracle for exactly this class —
~15 gating defects have been found with it, none of them broken code: things
never-connected or quietly disconnected while everything compiled.  So the
firewall is stated as data (`scripts/recursion-closure-policy.tsv`) and checked
against the resolve.

═══ WHAT IT CHECKS ═══════════════════════════════════════════════════════════

The LIBRARY graph: `normal` and `build` dependency edges, transitively, from
each named workspace member.  `dev` edges are excluded — deliberately and
load-bearingly, see below.

  FORBID <crate> <target> <reason>
      No path of normal/build edges from <crate> to <target>.  `<target>` may be
      the group `@recursion`, which expands to every `MARK` row.
  REQUIRE <crate> <target> <reason>
      There IS such a path.  This is the half that keeps the gate from being
      satisfiable by deletion: "nothing reaches the recursion fork" is trivially
      true of a tree that cannot verify anything.  A firewall gate with no
      positive rows measures absence only, and absence is the cheap direction.
  REQUIRE_DIRECT <crate> <target> <reason>
      <crate> DECLARES <target> in its own manifest — a normal/build edge with no
      hops.  ⚑ Not a stylistic variant of REQUIRE.  The first draft of this gate
      wrote `REQUIRE dregg-node dregg-recursion-verify` meaning "the node keeps
      its visible edge", and its own red-proof refused to go red when that edge
      was deleted: `dregg-node -> dregg-circuit-prove -> dregg-recursion-verify`
      satisfies the REACH through a path the node does not control.  The row
      asserted something true and useless while reading as the capability check.
      Where the claim is about a DECLARED edge — which is the whole of the
      operator's rule, *a crate you depend on when you need it, visible in `cargo
      tree`, never a feature* — the reach is the wrong predicate.
  MARK <pkg> <reason>
      A package that IS the recursion fork.  The `@recursion` group is data so
      that a NEW recursion crate is covered by every existing FORBID row the
      moment it is marked, rather than needing every row edited.

⚑ WHY `dev` EDGES ARE EXCLUDED, AND WHY THAT IS NOT A LOOPHOLE.  A dev-dependency
links into the crate's OWN test binaries and into nothing a consumer builds.  The
firewall is about what a consumer LINKS — the seL4 floor, the wasm card, the
weight the ~50 crates downstream of `dregg-turn` inherit — so the library graph
is the right object.  This is not a hypothetical: `dregg-recursion-verify`
declares `dregg-circuit-prove` as a DEV-dependency (its seam test mints a real
fold with the prover, then consumes the root through the verify path), and the
policy simultaneously FORBIDs it in the library graph.  Those two facts are
consistent, and the CONTROL run of `--self-test` is a live proof that the kind
filter works on real data: if this script counted dev edges, the control would
go red on a row that is correct.

⚑ `build` edges ARE included.  A build-dependency does not link into the final
artifact, so a narrower reading would drop them.  They are counted anyway
because the conservative direction is the correct one for a firewall, and
because "this crate cannot be COMPILED without the recursion fork present" is
itself a thing the seL4/wasm cards care about.  Widening a check needs a reason;
narrowing one needs a much better reason.

═══ WHAT IT DOES NOT CHECK ═══════════════════════════════════════════════════

  * That the code inside an allowed crate uses the edge correctly.  This is a
    GRAPH check.  `dregg-node` taking the `dregg-recursion-verify` edge is not
    evidence that its backend verifies anything; that is the seam test's job
    (`recursion-verify/tests/mina_chain_root_seam.rs`) and the node's.
  * Feature-conditional edges under a non-default feature set.  The resolve is
    read with the default feature selection, which is what `cargo build -p
    <crate>` produces.  ⚠ This tree's answer to that hole is not a wider gate: it
    is that the crates in play declare NO `[features]` at all
    (`recursion-verify/Cargo.toml`, `dregg-turn-prover`), so there is no other
    resolve to have.  A `[features]` section added to one of them would put a
    door in a wall this gate does not watch.
  * Anything about crates the policy does not name.  123 of 227 workspace
    members legitimately reach the recursion fork; the firewall is the set that
    must NOT, and an allowlist of the 123 would be a snapshot, not a rule.

═══ EXIT CODES ═══════════════════════════════════════════════════════════════

  0  every policy row holds
  1  a policy row is VIOLATED, or a row is decoration, or a floor was missed
  2  the policy file is absent or malformed — the gate cannot be trusted to report
  3  BLOCKED: `cargo metadata` produced no resolve (no lockfile, no network and a
     cold cache, a manifest that does not parse).  The gate DID NOT RUN.  It is
     still a failure — `scripts/local-gates.sh` counts BLOCKED in `fail` — but it
     is a different one from a divergence, and it wants the INPUT produced rather
     than the gate "fixed".

═══ USAGE ════════════════════════════════════════════════════════════════════

  python3 scripts/check-recursion-closure.py
  python3 scripts/check-recursion-closure.py --verbose      # print every row
  python3 scripts/check-recursion-closure.py --self-test    # red-proof

`--self-test` NEVER MUTATES THE TREE and never extracts a revision.  It reads the
real resolve once and injects faults into the in-memory GRAPH — which is exactly
the object the policy is evaluated against, so a fault is the graph a manifest
change would have produced.  A red-proof that edits shared files is a disarmed
guard for as long as the process that promised to restore them survives, and ten
lanes work this tree at once.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from collections import deque

# ── population floors ────────────────────────────────────────────────────────
# A reader that silently saw nothing reports CLEAN, which is how a negative
# assertion fails.  This workspace carried 227 members and the policy 10 rows
# when the gate landed; a run that sees far fewer has a broken resolve, a
# truncated parse or an empty policy, and must fail LOUDLY rather than pass
# having checked almost nothing.
MIN_MEMBERS = 200
MIN_POLICY_ROWS = 8
MIN_MARKS = 3

RECURSION_GROUP = "@recursion"
CARGO_TIMEOUT = 300

POLICY_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "recursion-closure-policy.tsv"
)

# ── SCOPE ─ this pair is the ONLY copy; it prints on every run, pass or fail. ─────────
SCOPE_ANSWERS = (
    "do all of scripts/recursion-closure-policy.tsv's rows hold against `cargo metadata`'s "
    "resolve — no normal/build path from each FORBIDden workspace member to its target "
    "(`@recursion` expanding to the MARK set), a path for each REQUIRE, a ONE-HOP DECLARED "
    "edge for each REQUIRE_DIRECT — with every MARK, crate and target naming a package that "
    "exists, over at least 200 workspace members?"
)
SCOPE_DOES_NOT_ANSWER = (
    "whether any crate USES the edge it is allowed, or whether the tree is recursion-free "
    "anywhere the policy is silent. It is a dependency-GRAPH question about the rows of one "
    "TSV, read at the DEFAULT feature selection and UNFILTERED BY PLATFORM (1024 resolve "
    "edges carry a `cfg(...)` target and every one of them counts): 123 of 227 members "
    "legitimately reach the fork and are never examined, a `[features]`-gated edge is a "
    "door in a wall this does not watch, and `dregg-turn` clearing every FORBID row says "
    "nothing about whether it can verify a root."
)
SCOPE_ANSWERS_SELFTEST = (
    "can the policy engine fire — is the real resolve green as CONTROL (which is itself the "
    "proof that DEV edges are excluded), and do five in-memory GRAPH faults, three "
    "policy-shaped faults and a blinded reader each go red with the expected finding kind?"
)
SCOPE_DOES_NOT_ANSWER_SELFTEST = (
    "whether the policy rows are the RIGHT rows. Faults go into the in-memory graph, never "
    "the tree; a firewall nobody wrote down is one this cannot fail."
)


def repo_root() -> str:
    here = os.path.dirname(os.path.abspath(__file__))
    try:
        out = subprocess.run(
            ["git", "-C", here, "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True,
        )
        return out.stdout.strip()
    except Exception:
        return os.path.dirname(here)


# ── the policy ───────────────────────────────────────────────────────────────

class Policy:
    def __init__(self) -> None:
        self.marks: list[tuple[str, str]] = []      # (pkg, reason)
        self.forbid: list[tuple[str, str, str]] = []  # (crate, target, reason)
        self.require: list[tuple[str, str, str]] = []
        self.require_direct: list[tuple[str, str, str]] = []

    def rows(self) -> int:
        return len(self.marks) + len(self.forbid) + len(self.require) + len(self.require_direct)


def read_policy(path: str = POLICY_PATH) -> Policy:
    """Parse the policy, or exit 2.

    ⚠ A MISSING policy file is a FAULT, not an empty policy.  "nothing is
    forbidden" and "the rules are gone" are indistinguishable to a reader and
    completely different in fact — a sibling gate in this tree shipped with its
    allowlist untracked and spent 25.5 hours green-because-empty in every clean
    checkout.
    """
    if not os.path.exists(path):
        print(
            f"{path}: MISSING.  A firewall whose policy is absent cannot be trusted to "
            f"report — an empty policy forbids nothing and reads exactly like a clean run.",
            file=sys.stderr,
        )
        raise SystemExit(2)

    pol = Policy()
    with open(path, encoding="utf-8") as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = [p.strip() for p in line.split("\t") if p.strip() != ""]
            if len(parts) < 3:
                print(
                    f"{path}:{lineno}: a row needs tab-separated fields "
                    f"`KIND<TAB>a<TAB>b[<TAB>reason]`, got: {line!r}",
                    file=sys.stderr,
                )
                raise SystemExit(2)
            kind = parts[0].upper()
            if kind == "MARK":
                pol.marks.append((parts[1], " ".join(parts[2:])))
            elif kind == "FORBID":
                if len(parts) < 4:
                    print(f"{path}:{lineno}: FORBID needs a reason field", file=sys.stderr)
                    raise SystemExit(2)
                pol.forbid.append((parts[1], parts[2], " ".join(parts[3:])))
            elif kind in ("REQUIRE", "REQUIRE_DIRECT"):
                if len(parts) < 4:
                    print(f"{path}:{lineno}: {kind} needs a reason field", file=sys.stderr)
                    raise SystemExit(2)
                row = (parts[1], parts[2], " ".join(parts[3:]))
                (pol.require if kind == "REQUIRE" else pol.require_direct).append(row)
            else:
                print(
                    f"{path}:{lineno}: unknown row kind {kind!r} "
                    f"(expected MARK / FORBID / REQUIRE / REQUIRE_DIRECT)",
                    file=sys.stderr,
                )
                raise SystemExit(2)
    return pol


# ── the graph ────────────────────────────────────────────────────────────────

class Graph:
    """The resolve, reduced to what the firewall is about.

    `edges[pkg_id]` is a list of `(dep_id, kinds)` where `kinds` is a set drawn
    from {"normal", "build", "dev"} — kept UNFILTERED so `--self-test` can flip
    a dev edge to normal and so a reader can see why an edge did not count.
    """

    def __init__(self) -> None:
        self.name: dict[str, str] = {}          # pkg id -> package name
        self.members: dict[str, str] = {}       # package name -> pkg id (workspace members)
        self.edges: dict[str, list[tuple[str, set]]] = {}
        self.all_names: set[str] = set()

    def linking_deps(self, pkg_id: str) -> list[str]:
        """Normal + build edges. See the module docstring for why dev is excluded."""
        return [
            dep for dep, kinds in self.edges.get(pkg_id, [])
            if "normal" in kinds or "build" in kinds
        ]

    def declares(self, crate_name: str, target_name: str) -> bool:
        """Does `crate_name`'s OWN manifest declare a normal/build dep on `target_name`?

        One hop, no closure.  See the module docstring: a REACH can be satisfied
        by a path the crate does not control, which makes it the wrong predicate
        for "this crate visibly takes the edge".
        """
        src = self.members.get(crate_name)
        if src is None:
            return False
        return any(self.name.get(d) == target_name for d in self.linking_deps(src))

    def path(self, start_name: str, target_name: str) -> list[str] | None:
        """Shortest normal/build path `start -> … -> target`, as package names.

        A violation report is only actionable if it names the EDGE that
        introduced it, so this returns the whole chain rather than a bool.
        """
        start = self.members.get(start_name)
        if start is None:
            return None
        q = deque([(start, [self.name.get(start, start)])])
        seen = {start}
        while q:
            cur, chain = q.popleft()
            if self.name.get(cur) == target_name:
                return chain
            for nxt in self.linking_deps(cur):
                if nxt not in seen:
                    seen.add(nxt)
                    q.append((nxt, chain + [self.name.get(nxt, nxt)]))
        return None

    def copy(self) -> "Graph":
        g = Graph()
        g.name = dict(self.name)
        g.members = dict(self.members)
        g.edges = {k: [(d, set(ks)) for d, ks in v] for k, v in self.edges.items()}
        g.all_names = set(self.all_names)
        return g


def load_graph(root: str) -> Graph:
    """Read `cargo metadata`'s resolve, or exit 3 (BLOCKED).

    ⚑ A failure here is BLOCKED, not FAIL.  "cargo could not resolve this tree"
    is an absent INPUT — the gate did not run and has no opinion — and reporting
    it as a firewall violation would send a reader to fix the wrong thing.
    """
    env = dict(os.environ)
    env["CARGO_TERM_COLOR"] = "never"
    try:
        proc = subprocess.run(
            ["cargo", "metadata", "--format-version", "1", "--manifest-path",
             os.path.join(root, "Cargo.toml")],
            capture_output=True, text=True, env=env, timeout=CARGO_TIMEOUT,
        )
    except FileNotFoundError:
        print("BLOCKED: `cargo` is not on PATH — no resolve, so no verdict.", file=sys.stderr)
        raise SystemExit(3)
    except subprocess.TimeoutExpired:
        print(f"BLOCKED: `cargo metadata` exceeded {CARGO_TIMEOUT}s — no resolve, so no verdict.",
              file=sys.stderr)
        raise SystemExit(3)

    if proc.returncode != 0:
        msg = (proc.stderr or proc.stdout).strip().splitlines()
        print("BLOCKED: `cargo metadata` produced no resolve — the gate DID NOT RUN.", file=sys.stderr)
        for line in msg[:6]:
            print(f"  {line}", file=sys.stderr)
        raise SystemExit(3)

    try:
        meta = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        print(f"BLOCKED: `cargo metadata` emitted unparseable JSON: {exc}", file=sys.stderr)
        raise SystemExit(3)

    resolve = meta.get("resolve")
    if not resolve or not resolve.get("nodes"):
        print("BLOCKED: metadata carries no `resolve` — this was run with --no-deps, "
              "or cargo declined to resolve. There is no graph to check.", file=sys.stderr)
        raise SystemExit(3)

    g = Graph()
    for pkg in meta["packages"]:
        g.name[pkg["id"]] = pkg["name"]
        g.all_names.add(pkg["name"])
    for mid in meta.get("workspace_members", []):
        nm = g.name.get(mid)
        if nm:
            g.members[nm] = mid
    for node in resolve["nodes"]:
        outs = []
        for dep in node.get("deps", []):
            kinds = set()
            for dk in dep.get("dep_kinds", []) or [{"kind": None}]:
                kinds.add(dk.get("kind") or "normal")
            outs.append((dep["pkg"], kinds))
        g.edges[node["id"]] = outs
    return g


# ── evaluation ───────────────────────────────────────────────────────────────

class Findings:
    def __init__(self) -> None:
        self.rows: list[tuple[str, str]] = []   # (kind, detail)

    def add(self, kind: str, detail: str) -> None:
        self.rows.append((kind, detail))

    def kinds(self) -> set[str]:
        return {k for k, _ in self.rows}

    def __bool__(self) -> bool:
        return bool(self.rows)


def evaluate(g: Graph, pol: Policy, enforce_floors: bool = True,
             verbose: bool = False) -> tuple[Findings, dict]:
    f = Findings()

    # ── the MARK set.  A mark that names no real package silently weakens every
    #    `@recursion` row that expands through it — the "pin against its own
    #    definition" shape, where a rule looks strict and constrains nothing.
    marks: list[str] = []
    for pkg, reason in pol.marks:
        if pkg not in g.all_names:
            f.add("UNKNOWN_MARK",
                  f"MARK `{pkg}` names no package in the resolve — every `@recursion` FORBID "
                  f"row expands through it and would be satisfied by a name that cannot exist. "
                  f"(was: {reason})")
            continue
        marks.append(pkg)

    def expand(target: str) -> list[str]:
        return list(marks) if target == RECURSION_GROUP else [target]

    checked = 0

    # ── FORBID ───────────────────────────────────────────────────────────────
    for crate, target, reason in pol.forbid:
        if crate not in g.members:
            f.add("UNKNOWN_CRATE",
                  f"FORBID row names `{crate}`, which is not a workspace member — the row is "
                  f"stale (renamed? deleted?) and has been protecting nothing. (was: {reason})")
            continue
        targets = expand(target)
        if target != RECURSION_GROUP and target not in g.all_names:
            f.add("UNKNOWN_TARGET",
                  f"FORBID `{crate}` -x-> `{target}`: that target is in no resolve node, so the "
                  f"row is trivially satisfied forever — decoration, not a rule. (was: {reason})")
            continue
        if not targets:
            f.add("EMPTY_GROUP",
                  f"FORBID `{crate}` -x-> `{RECURSION_GROUP}` expanded to NOTHING; the MARK set "
                  f"is empty or entirely unknown, so this row checks nothing.")
            continue
        for t in targets:
            checked += 1
            p = g.path(crate, t)
            if p is not None:
                f.add("FORBIDDEN_EDGE",
                      f"`{crate}` REACHES `{t}` through the library graph:\n"
                      f"      {' -> '.join(p)}\n"
                      f"      policy: {reason}")
            elif verbose:
                print(f"  ok   FORBID  {crate:26s} -x-> {t}")

    # ── REQUIRE ──────────────────────────────────────────────────────────────
    for crate, target, reason in pol.require:
        if crate not in g.members:
            f.add("UNKNOWN_CRATE",
                  f"REQUIRE row names `{crate}`, which is not a workspace member. (was: {reason})")
            continue
        if target not in g.all_names:
            f.add("UNKNOWN_TARGET",
                  f"REQUIRE `{crate}` --> `{target}`: that target is in no resolve node at all. "
                  f"(was: {reason})")
            continue
        checked += 1
        p = g.path(crate, target)
        if p is None:
            f.add("MISSING_REQUIRED_EDGE",
                  f"`{crate}` does NOT reach `{target}` through the library graph. The capability "
                  f"this edge carries is gone, and its absence is silent at compile time.\n"
                  f"      policy: {reason}")
        elif verbose:
            print(f"  ok   REQUIRE {crate:26s} -->  {target}   [{' -> '.join(p)}]")

    # ── REQUIRE_DIRECT ───────────────────────────────────────────────────────
    for crate, target, reason in pol.require_direct:
        if crate not in g.members:
            f.add("UNKNOWN_CRATE",
                  f"REQUIRE_DIRECT row names `{crate}`, which is not a workspace member. "
                  f"(was: {reason})")
            continue
        if target not in g.all_names:
            f.add("UNKNOWN_TARGET",
                  f"REQUIRE_DIRECT `{crate}` --> `{target}`: that target is in no resolve node "
                  f"at all. (was: {reason})")
            continue
        checked += 1
        if not g.declares(crate, target):
            reach = g.path(crate, target)
            via = (f"\n      ⚠ it still REACHES it transitively via "
                   f"{' -> '.join(reach)} — which is exactly why the reach is not the check: "
                   f"that path belongs to another crate and can go away without notice."
                   if reach else "")
            f.add("MISSING_DIRECT_EDGE",
                  f"`{crate}` does not DECLARE `{target}` in its own manifest.{via}\n"
                  f"      policy: {reason}")
        elif verbose:
            print(f"  ok   DIRECT  {crate:26s} -->  {target}")

    stats = {
        "members": len(g.members),
        "packages": len(g.all_names),
        "policy_rows": pol.rows(),
        "marks": len(marks),
        "assertions": checked,
    }

    if enforce_floors:
        if len(g.members) < MIN_MEMBERS:
            f.add("FLOOR",
                  f"the resolve carries only {len(g.members)} workspace members (floor "
                  f"{MIN_MEMBERS}) — the reader is blinded and this run checked almost nothing")
        if pol.rows() < MIN_POLICY_ROWS:
            f.add("FLOOR",
                  f"the policy parsed only {pol.rows()} rows (floor {MIN_POLICY_ROWS}) — the "
                  f"parser has lost the row shape, or the firewall has been emptied")
        if len(marks) < MIN_MARKS:
            f.add("FLOOR",
                  f"only {len(marks)} usable MARK rows (floor {MIN_MARKS}) — `{RECURSION_GROUP}` "
                  f"is narrower than the recursion fork actually is")

    return f, stats


def report(f: Findings, stats: dict) -> None:
    print(f"  {stats['members']} workspace members / {stats['packages']} packages / "
          f"{stats['policy_rows']} policy rows / {stats['marks']} marks / "
          f"{stats['assertions']} assertions checked")
    if not f:
        print("  ->  the recursion firewall HOLDS")
        return
    print(f"  ->  {len(f.rows)} FINDING(S)")
    for kind, detail in f.rows:
        print(f"    {kind}  {detail}")


# ── red-proof ────────────────────────────────────────────────────────────────
# Faults are injected into the in-memory GRAPH — the object the policy is
# evaluated against — so each one is the graph a manifest edit would have
# produced.  THE WORKING TREE IS NEVER TOUCHED BY THIS MODE.
#
# ⚠ SAY WHAT THIS PROVES AND WHAT IT DOES NOT.  It proves the policy engine goes
# red for each defect class, and that it does so via the CLOSURE rather than a
# direct-edge scan.  It does not re-prove that `cargo metadata` emits what this
# script parses — the CONTROL does that, on real data: the control is green only
# because `dregg-recursion-verify`'s DEV edge on `dregg-circuit-prove` is
# correctly not counted, while its normal edges on `p3-recursion` and
# `p3-circuit-prover` correctly are.  A parser that got either wrong could not
# produce a green control.


def _edge(g: Graph, frm: str, to: str, kinds: set) -> None:
    src = g.members.get(frm)
    dst = next((i for i, n in g.name.items() if n == to), None)
    if src is None or dst is None:
        raise AssertionError(
            f"fault injection matched NOTHING: cannot add {frm} -> {to} "
            f"(src={'ok' if src else 'MISSING'}, dst={'ok' if dst else 'MISSING'})"
        )
    g.edges.setdefault(src, []).append((dst, kinds))


def _inject_direct_forbidden(g: Graph) -> str:
    """The edge the firewall comment forbids, added back to `dregg-turn`."""
    _edge(g, "dregg-turn", "dregg-circuit-prove", {"normal"})
    return "dregg-turn takes a normal dep on dregg-circuit-prove"


def _inject_transitive_forbidden(g: Graph) -> str:
    """A dep of a dep takes the edge.

    This is the one that matters: a gate that scanned `turn/Cargo.toml` for a
    forbidden string would stay GREEN here, and `dregg-turn` would still link
    the whole recursion tower.  The firewall is a CLOSURE property.
    """
    _edge(g, "dregg-cell", "dregg-circuit-prove", {"normal"})
    return "dregg-cell (a dep of turn) takes the edge — turn inherits it transitively"


def _inject_dev_promoted_to_normal(g: Graph) -> str:
    """`dregg-recursion-verify`'s dev-dep on `dregg-circuit-prove`, promoted.

    The verify crate exists to be the SMALL edge a consumer can take.  If its
    dev-dep were ever moved into `[dependencies]`, every consumer of it would
    silently inherit the IVC tower, the shielded prover and the GPU backend, and
    the extraction would be cosmetic.  Nothing about the crate's own tests would
    change, so nothing else would notice.
    """
    src = g.members.get("dregg-recursion-verify")
    dst = next((i for i, n in g.name.items() if n == "dregg-circuit-prove"), None)
    if src is None or dst is None:
        raise AssertionError("fault injection matched NOTHING: recursion-verify or circuit-prove absent")
    hit = False
    for i, (dep, kinds) in enumerate(g.edges.get(src, [])):
        if dep == dst and "dev" in kinds:
            g.edges[src][i] = (dep, {"normal"})
            hit = True
    if not hit:
        raise AssertionError(
            "fault injection matched NOTHING: dregg-recursion-verify has no DEV edge on "
            "dregg-circuit-prove to promote. Fix this self-test rather than letting it no-op."
        )
    return "recursion-verify's dev-dep on circuit-prove promoted to a normal dep"


def _inject_required_edge_deleted(g: Graph) -> str:
    """The node quietly loses its DECLARED recursion-verify edge.

    The compile-time symptom is nothing at all if the backend module goes with
    it: `dregg-turn`'s verifier is constructed UNWIRED by default and refuses
    every Mina anchored head, so the node keeps building, keeps running, and
    silently stops being able to verify a head.  That is this repo's signature
    defect shape (the UN-CALLED INITIALIZER).

    ⚑ THIS FAULT IS WHY `REQUIRE_DIRECT` EXISTS.  Against a plain `REQUIRE` row
    the injection above stayed GREEN — `dregg-node -> dregg-circuit-prove ->
    dregg-recursion-verify` still satisfies the reach — so the row that was
    supposed to be the node's capability check could not go red for the thing it
    named.  Found by this self-test, on its first run.
    """
    src = g.members.get("dregg-node")
    dst = next((i for i, n in g.name.items() if n == "dregg-recursion-verify"), None)
    if src is None or dst is None:
        raise AssertionError("fault injection matched NOTHING: dregg-node or recursion-verify absent")
    before = len(g.edges.get(src, []))
    g.edges[src] = [(d, k) for d, k in g.edges.get(src, []) if d != dst]
    if len(g.edges[src]) == before:
        raise AssertionError("fault injection matched NOTHING: node has no recursion-verify edge already")
    return "dregg-node's declared dregg-recursion-verify edge removed"


def _inject_capability_left_the_graph(g: Graph) -> str:
    """`p3-circuit-prover` reachable from nobody — the recursive check itself gone.

    The complement of the row above: not "who declares it" but "is the code that
    runs `verify_all_tables` in the link at all".  A tree that answers no is a
    tree where every FORBID row passes perfectly.
    """
    dst = next((i for i, n in g.name.items() if n == "p3-circuit-prover"), None)
    if dst is None:
        raise AssertionError("fault injection matched NOTHING: p3-circuit-prover absent")
    removed = 0
    for src in list(g.edges):
        keep = [(d, k) for d, k in g.edges[src] if d != dst]
        removed += len(g.edges[src]) - len(keep)
        g.edges[src] = keep
    if removed == 0:
        raise AssertionError("fault injection matched NOTHING: no edge reaches p3-circuit-prover")
    return f"every edge into p3-circuit-prover removed ({removed})"


def GRAPH_FAULTS():
    return [
        ("forbidden edge, direct", _inject_direct_forbidden, {"FORBIDDEN_EDGE"}),
        ("forbidden edge, TRANSITIVE", _inject_transitive_forbidden, {"FORBIDDEN_EDGE"}),
        ("dev-dep promoted to normal", _inject_dev_promoted_to_normal, {"FORBIDDEN_EDGE"}),
        ("declared edge deleted", _inject_required_edge_deleted, {"MISSING_DIRECT_EDGE"}),
        ("capability left the graph", _inject_capability_left_the_graph,
         {"MISSING_REQUIRED_EDGE", "MISSING_DIRECT_EDGE"}),
    ]


def run_self_test(root: str) -> int:
    print("check-recursion-closure: SELF-TEST (red-proof)")
    print("  faults are injected into the in-memory RESOLVE GRAPH; the working tree is")
    print("  never mutated and no revision is extracted.")
    print()

    pol = read_policy()
    g = load_graph(root)

    # 0. CONTROL.  If the tree is already red every "red" below proves nothing.
    f, stats = evaluate(g, pol)
    if f:
        print("  CONTROL  \033[31mFAIL\033[0m — the working tree is already red;")
        report(f, stats)
        print("  Every fault injection below would be uninterpretable. Fix the tree first.")
        return 1
    print(f"  CONTROL  \033[32mgreen\033[0m — {stats['assertions']} assertions hold over "
          f"{stats['members']} members")
    print("           (green here is itself the proof that DEV edges are excluded: "
          "recursion-verify")
    print("            dev-deps circuit-prove and is FORBIDden it in the library graph.)")
    print()

    failures = 0
    for label, inject, expect in GRAPH_FAULTS():
        mutated = g.copy()
        try:
            what = inject(mutated)
        except AssertionError as exc:
            print(f"  {label:32s} \033[31mFAIL\033[0m — {exc}")
            failures += 1
            continue
        mf, _ = evaluate(mutated, pol)
        got = mf.kinds()
        if not mf:
            print(f"  {label:32s} \033[31mFAIL\033[0m — injected [{what}] and it stayed GREEN")
            failures += 1
        elif not (got & expect):
            print(f"  {label:32s} \033[31mFAIL\033[0m — red as {sorted(got)}, not {sorted(expect)}")
            failures += 1
        else:
            print(f"  {label:32s} \033[32mred\033[0m   {sorted(got & expect)[0]}")

    # ── policy-shaped faults: a row that cannot fail is not a row. ────────────
    for label, mutate, expect in [
        ("policy row that is decoration",
         lambda p: p.forbid.append(("dregg-turn", "p3-recursion-that-does-not-exist", "x")),
         "UNKNOWN_TARGET"),
        ("policy row naming a dead crate",
         lambda p: p.forbid.append(("dregg-turn-renamed-away", RECURSION_GROUP, "x")),
         "UNKNOWN_CRATE"),
        ("MARK naming no real package",
         lambda p: p.marks.append(("p3-recursion-typo", "x")),
         "UNKNOWN_MARK"),
    ]:
        p2 = Policy()
        p2.marks = list(pol.marks); p2.forbid = list(pol.forbid); p2.require = list(pol.require)
        mutate(p2)
        mf, _ = evaluate(g, p2)
        if expect in mf.kinds():
            print(f"  {label:32s} \033[32mred\033[0m   {expect}")
        else:
            print(f"  {label:32s} \033[31mFAIL\033[0m — red as {sorted(mf.kinds())}, not {expect}")
            failures += 1

    # ── the blinded reader. ──────────────────────────────────────────────────
    blind = g.copy()
    keep = dict(list(blind.members.items())[: len(blind.members) // 3])
    blind.members = keep
    mf, st = evaluate(blind, pol)
    if "FLOOR" in mf.kinds():
        print(f"  {'population floor (blind reader)':32s} \033[32mred\033[0m   "
              f"FLOOR at {st['members']} members (floor {MIN_MEMBERS})")
    else:
        print(f"  {'population floor (blind reader)':32s} \033[31mFAIL\033[0m — "
              f"a reader that saw {st['members']} members read as {sorted(mf.kinds()) or 'CLEAN'}")
        failures += 1

    total = len(GRAPH_FAULTS()) + 4
    print()
    if failures:
        print(f"check-recursion-closure --self-test: FAIL — {failures} of {total} faults not detected")
        return 1
    print(f"check-recursion-closure --self-test: all {total} faults detected, control green")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--self-test", action="store_true", help="red-proof (mutates nothing)")
    ap.add_argument("--verbose", action="store_true", help="print every policy row that holds")
    args = ap.parse_args()

    root = repo_root()
    if args.self_test:
        print(f"ANSWERS:         {SCOPE_ANSWERS_SELFTEST}", flush=True)
        print(f"DOES NOT ANSWER: {SCOPE_DOES_NOT_ANSWER_SELFTEST}", flush=True)
        return run_self_test(root)

    print(f"ANSWERS:         {SCOPE_ANSWERS}", flush=True)
    print(f"DOES NOT ANSWER: {SCOPE_DOES_NOT_ANSWER}", flush=True)
    print("check-recursion-closure: the recursion firewall, against `cargo metadata`'s resolve")
    pol = read_policy()
    g = load_graph(root)
    f, stats = evaluate(g, pol, verbose=args.verbose)
    report(f, stats)
    return 0 if not f else 1


if __name__ == "__main__":
    sys.exit(main())
