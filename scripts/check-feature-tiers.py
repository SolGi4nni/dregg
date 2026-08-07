#!/usr/bin/env python3
"""check-feature-tiers.py — THE FEATURE SURFACE GATE: no cargo feature is silently uncovered.

## The hole this closes

A `#[cfg(feature = "x")]` is A SUBTRACTION THAT EMITS NO LINE. A failing test prints a line; a
red build prints a line; code that is not compiled prints NOTHING. The build is green BECAUSE
the code is absent. That is a strictly worse signal than `#[ignore]`, which at least keeps the
file compiling so API drift reds the day it lands.

MEASURED 2026-07-26 on this tree: 243 `(crate, feature)` pairs across 145 distinct feature
names, declared by 73 of this repository's 270 first-party packages, spread over 8 cargo
workspaces. `cargo check --workspace` plus every `--features` flag in every PUSH-TRIGGERED
workflow activates 152 of them. NOTHING anywhere passes `--all-features`. So 91 pairs — 37% of
the surface — were compiled by no CI job at all, and produced no line saying so. Among them: the
three `#![cfg(feature = "prove")]` adversarial fold canaries (`armed-teeth.yml` arms them),
`tlsn-live` in 6 crates, `private-bazaar-live` in 4, `no-lean-link` in 2, all 13 of pg-dregg's
pgrx ABIs, and both seL4 protection-domain features.

Nine of the ten `--features` flags reachable from a workflow file are in `ci.yml` and fire on
every push. The other two things that look like coverage are not: `pages.yml` (`gpui-web`, `web`)
is `workflow_dispatch` ONLY, and `publish-sdk-py.yml` names `kernel` in a COMMENT while no step
passes it.

`private-bazaar-live` is the proof that this is not a tidiness item: a verified settling gate
shipped inside it and was never registered anywhere, and every settling test in that crate could
not go green on any host. Nobody saw it, because an uncompiled feature has no output.

## The check

  STATIC (no cargo; runs even if nothing in the tree compiles)
    S1  TOTALITY. Every `(crate, feature)` pair enumerated from the Cargo.toml files has a row
        in scripts/feature-tiers.tsv. An UNTIERED pair is RED. This is the whole point: a newly
        added feature cannot arrive silently uncovered, because arriving at all reds the gate.
    S2  STALENESS. Every row names a pair that still exists. A row for a deleted feature is RED,
        not merely ignored. A ledger that can only ever LAG describes a tree that is gone — this
        repository has been bitten by an upward-rotting ledger twice in two days.
    S3  WELL-FORMEDNESS. tier in {T1,T2,T3,T4}; `why` non-empty on every row; a T4 row's `why`
        must OPEN with one of the exemption classes in EXEMPT_CLASSES below, so "exempt because
        reasons" is not spellable. Plus two things the tables below make ENFORCED rather than
        merely documented:
          S3d  a pair whose only enabler is a `workflow_dispatch` workflow (MANUAL_ONLY_EXPLICIT)
               may not be tiered T1 — T1 means green EVERY PUSH, and a near-miss recorded but not
               enforced is how "we know about that" becomes "nothing checks it".
          S3e  every row of scripts/feature-t3-known-red.tsv names a pair that is CURRENTLY T3.
               That file is a SECOND ledger and rots the same way, and the sweep can never catch
               a stale row there because it only judges pairs it actually ran.
    S4  the ledger's own `#!` directives (total + per-tier counts) agree with its rows, so
        trimming rows to make a smaller reality pass requires editing the recorded number too.
    S5  THE FLOORS, hardcoded HERE in reviewed code rather than read from the data the accident
        could take out:
          * MAX_T4          — exemptions cannot grow past the reviewed count without an edit here.
          * MIN_T3          — the compile sweep cannot be emptied into exemptions.
          * MIN_PAIRS       — the enumerator finding almost nothing is an enumerator bug, not a
                              clean tree, and must not read as a pass.
          * NEVER_EXEMPT    — feature NAMES that may never be T4, by name, because their absence
                              is a known wound: prove, prover, private-bazaar-live, no-lean-link,
                              tlsn-live, lean-lib.
          * PUSH_TRIGGERED_EXPLICIT — the `--features` flags CI really passes, with provenance.
                              A T1 row whose only claim is CI must appear here or be activated by
                              default; a stale claim of coverage is RED.

  CARGO (optional; adds failures, never subtracts them)
    C1  --verify-enumeration: the static enumerator (a tomllib reimplementation of cargo's
        implicit-optional-dependency-feature rule) must agree EXACTLY with `cargo metadata
        --no-deps`. This is the guard against the static half quietly drifting from the oracle.
    C2  --verify-t1: every row claiming T1-by-default must be in the default workspace resolve
        that `cargo check --workspace` compiles. Used in the RED direction only: metadata can
        prove a claimed-covered pair is NOT activated, which is sound; it cannot be trusted to
        prove the converse, because resolver-v3 decouples build/proc-macro features and metadata
        reports one union per package. Stated so the inadequacy is visible.

## Why this cannot be defeated by the accident it exists to catch

The expected set is not recorded — it is DERIVED FROM THE TREE, every run, and the ledger must
cover it TOTALLY. That is the opposite arrangement from `check-gates-executed.py`, deliberately:
there the accident DELETES the thing, so the expectation had to be recorded; here the accident
ADDS a thing (a new feature) and the failure is that nothing notices. A recorded list would lag
by exactly the new feature. So the tree is the source and the ledger is the obligation, and the
floors in this file stop the ledger from being emptied into T4.

## --self-test

Runs the whole static checker against synthetic ledgers on every invocation — 19 poles: an
untiered pair, a stale row, a bad tier name, an empty reason, an unclassed exemption, `cost:`
refused as a class, a NEVER_EXEMPT feature parked in T4, an over-ceiling T4, an under-floor T3, a
miscounted directive, a T1 claim with no covering job, a T1-by-default claim in a workspace no
push job builds, an empty enumeration, a stale known-red row, the shard blocks partitioning the
plan for every n, cargo's implicit-optional-dep rule in both polarities, and two intact positive
controls. A guard that cannot be shown to go red is not a guard, and one that reds on everything
is not one either.

EXIT: 0 the ledger totally and non-staleley covers the tree
      1 LEDGER <-> TREE DISAGREEMENT — an untiered pair (a feature arrived uncovered) or a stale
        row (the ledger rotted upward). The incident class.
      2 environment / unparseable ledger ("I could not tell" is not a pass)
      3 the ledger is total, but TIER DISCIPLINE is broken — a floor, an unclassed exemption, or
        a coverage claim that is not true. Deliberately a different code: "the surface is
        unmapped" and "the map lies" are different problems with different fixes.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "scripts" / "feature-tiers.tsv"
# The sweep's recorded-broken set. Read here too, because it is a second ledger and rots the same
# way — see S3e. scripts/feature-t3-sweep.sh owns the cargo-side half of enforcing it.
KNOWN_RED = ROOT / "scripts" / "feature-t3-known-red.tsv"

# ════════════════════════════════════════════════════════════════════════════════
# THE FLOORS. In code, on purpose.
# ════════════════════════════════════════════════════════════════════════════════
TIERS = ("T1", "T2", "T3", "T4")

# Counted 2026-07-26 against HEAD. A drop below these is a ratchet break: either the enumerator
# broke, or the ledger was rewritten to describe a smaller tree.
MIN_PAIRS = 200  # 243 measured; the floor is not the count, it is "the enumerator worked at all"
MIN_T3 = 60  # 79 measured. T3 shrinking into T4 is how a compile sweep becomes decoration.
MAX_T4 = 12  # 9 measured. Exemptions may be added, but only by editing this number.
MIN_WORKSPACES = 8  # cargo workspaces `--verify-enumeration` must reach. 8 measured 2026-07-26.

# Exemption CLASSES. A T4 row's `why` must begin `<class>: `. Cost is NOT a class — an expensive
# feature is T2 (nightly, own job), never exempt. That distinction is the whole tiering.
EXEMPT_CLASSES = ("credentials", "network", "gpu", "target", "toolchain")

# Feature NAMES that may never be exempted, by name, because a lane already paid for finding out
# what their absence costs. Adding to this list is cheap; removing from it is a confession.
NEVER_EXEMPT = ("prove", "prover", "private-bazaar-live", "no-lean-link", "tlsn-live", "lean-lib")

# Vendored third-party crates — ANY path with a `vendor/` component, which in this tree means
# `vendor/`, `deos-homeserver/vendor/`, `starbridge-v2/vendor/` and `servo-render/vendor/`.
# Their feature surface belongs to upstream, not to this repo, and `cargo metadata` does not see
# them as workspace members either (16 pairs measured 2026-07-26). Named, not silently skipped:
# if a vendored crate ever grows a DREGG-authored feature it must be moved out of vendor/ before
# this gate will see it, and that is the correct place for the argument to happen.
VENDOR_DIR = "vendor"


def is_vendored(rel: Path) -> bool:
    return VENDOR_DIR in rel.parts

# WHAT CI ACTUALLY ENABLES ON EVERY PUSH, with provenance. Hardcoded rather than regexed out of
# the YAML: a derivation from the same file the accident edits will always agree that nothing was
# expected. One grep per line checks it.
PUSH_TRIGGERED_EXPLICIT: dict[tuple[str, str], str] = {
    ("dregg-chain", "mock"): "ci.yml:71 cargo test -p dregg-chain --features mock",
    ("dregg-chain", "on-chain"): "ci.yml:72 cargo check -p dregg-chain --features on-chain",
    ("starbridge-polis", "deos"): "ci.yml:82 cargo test -p starbridge-polis --features deos",
    ("dregg-doc", "substrate"): "ci.yml:101 cargo test -p dregg-doc --features substrate",
    ("deos-zed", "firmament"): "ci.yml:509 cargo test -p deos-zed --no-default-features --features firmament",
    ("dregg-agent", "live-brain"): "ci.yml:602 cargo test -p dregg-agent --features live-brain",
    ("dregg-lean-ffi", "lean-lib"): "ci.yml:984 cargo test -p dregg-lean-ffi --features lean-lib",
    ("durable-workflow", "deploy"): "ci.yml:305 excluded-workspace matrix, testflags: --features deploy",
    # ── THE COCKPIT CONE. ────────────────────────────────────────────────────────────────────
    # These eighteen used to be `default@.`, and that WAS true: `starbridge-v2` is a root
    # member and its `default` was `["desktop"]`, so ci.yml's `cargo check --workspace`
    # activated all of them. It also made them a hazard — a feature unifies across the resolve,
    # so `desktop` was silently rewriting OTHER packages' compilations (measured: `servo-render`
    # resolved `swgl-standalone` under `-p` and `libservo` under `--workspace`, i.e. a different
    # program depending on which packages cargo had been asked about). `default` is now
    # `["embedded-executor"]`, and the cone is built BY THE JOB WHOSE SUBJECT IT IS:
    # starbridge-v2-installers.yml, `push: branches: [main]` with NO paths filter, which builds
    # `--release --features desktop` on macos arm64 + x86_64 and on ubuntu.
    #
    # THE PROVENANCE IS TRANSITIVE AND SAYS SO. Only `desktop` is a flag anyone types; the rest
    # are what `desktop` pulls, and each entry names the edge. That is a weaker claim than a
    # typed flag and it is written down rather than rounded off.
    **{
        (c, f): (
            f"starbridge-v2-installers.yml:200,386 cargo build --release --features desktop{chain}"
        )
        for c, f, chain in [
            ("starbridge-v2", "desktop", ""),
            ("starbridge-v2", "app-registry", " → app-registry"),
            ("starbridge-v2", "gpui-ui", " → gpui-ui"),
            ("starbridge-v2", "live-node", " → live-node"),
            ("starbridge-v2", "render-capture", " → render-capture"),
            ("starbridge-v2", "dev-surfaces", " → dev-surfaces"),
            ("starbridge-v2", "web-shell", " → web-shell"),
            ("starbridge-v2", "agent-js", " → agent-js"),
            ("starbridge-v2", "card-pane", " → card-pane"),
            ("starbridge-v2", "android-systemui", " → android-systemui"),
            ("starbridge-v2", "servo", " → web-shell → servo"),
            ("starbridge-v2", "firmament", " → dev-surfaces → firmament"),
            ("servo-render", "libservo", " → web-shell → servo-render/libservo"),
            # NOT deos-zed:firmament — it already has a STRONGER provenance above
            # (ci.yml:509, a directly typed flag in the main per-push job). The cockpit
            # reaches it too, but the better claim is the one that does not go through a
            # transitive edge, so that entry stays and this block must not overwrite it.
            ("deos-terminal", "cockpit-surface", " → dev-surfaces → deos-terminal/cockpit-surface"),
            ("deos-hermes", "cockpit-surface", " → dev-surfaces → deos-hermes/cockpit-surface"),
            ("deos-matrix", "cockpit-surface", " → dev-surfaces → deos-matrix/cockpit-surface"),
            ("deos-matrix", "gui", " → dev-surfaces → deos-matrix/cockpit-surface → gui"),
        ]
    },
}

# Enabled by a workflow that is NOT push-triggered. Recorded so that their ABSENCE from T1 is a
# decision someone made and can be argued with, rather than a thing nobody noticed.
MANUAL_ONLY_EXPLICIT: dict[tuple[str, str], str] = {
    ("starbridge-web", "gpui-web"): "pages-wasm.yml — weekly schedule + push:tags[v*] + manual (NOT push-triggered, so not T1); was pages.yml workflow_dispatch-only until the 2026-07-26 fast/heavy split",
    ("deos-view", "web"): "pages-wasm.yml — weekly schedule + push:tags[v*] + manual (NOT push-triggered, so not T1); was pages.yml workflow_dispatch-only until the 2026-07-26 fast/heavy split",
    ("dregg-sdk-py", "kernel"): "publish-sdk-py.yml:8 — named in a COMMENT; no step passes it",
}

# Workspaces a push-triggered job builds at DEFAULT features. A crate outside these can never
# honestly be T1-by-default, however green its own resolve looks.
PUSH_BUILT_WORKSPACES: dict[str, str] = {
    ".": "ci.yml cargo check --workspace --all-targets --keep-going + cargo test --workspace",
    "discord-bot": "ci.yml excluded-workspace matrix (cargo check --all-targets)",
    "dregg-tui": "ci.yml excluded-workspace matrix (cargo check --all-targets + cargo test)",
    "durable-workflow": "ci.yml excluded-workspace matrix (cargo check --all-targets + cargo test)",
    "deos-homeserver": "ci.yml excluded-workspace matrix (cargo check --all-targets)",
    "forge-ci-runner": "ci.yml excluded-workspace matrix (cargo check --all-targets)",
}

BOLD, RED, GRN, YEL, DIM, OFF = (
    ("\033[1m", "\033[31m", "\033[32m", "\033[33m", "\033[2m", "\033[0m")
    if sys.stderr.isatty()
    else ("", "", "", "", "", "")
)


# Every human-readable line goes through _LOG. `--emit-t3-plan` retargets it to stderr so that
# stdout carries the plan and NOTHING else — a machine-readable mode whose output a banner can
# corrupt is a mode that silently feeds CI garbage.
_LOG = sys.stdout


def hdr(msg: str) -> None:
    print(f"\n{BOLD}== {msg} =={OFF}", file=_LOG, flush=True)


def ok(msg: str) -> None:
    print(f"  {GRN}ok{OFF}   {msg}", file=_LOG, flush=True)


def note(msg: str) -> None:
    print(f"  {DIM}note{OFF} {msg}", file=_LOG, flush=True)


def fatal(msg: str) -> None:
    print(f"{RED}{BOLD}environment: {msg}{OFF}", file=sys.stderr, flush=True)
    sys.exit(2)


# ════════════════════════════════════════════════════════════════════════════════
# ENUMERATION — the tree is the source of truth, so this is the load-bearing half
# ════════════════════════════════════════════════════════════════════════════════
SKIP_DIRS = {"target", "node_modules", ".git", ".lake", "pkg", "pkg-gpui", "dist"}


def find_manifests(root: Path) -> list[Path]:
    out: list[Path] = []

    def walk(d: Path) -> None:
        try:
            entries = list(d.iterdir())
        except OSError:
            return
        for e in entries:
            if e.is_dir():
                if e.name in SKIP_DIRS or e.name.startswith("."):
                    continue
                walk(e)
            elif e.name == "Cargo.toml":
                out.append(e)

    walk(root)
    return sorted(out)


def enumerate_features(manifest: dict) -> set[str]:
    """Cargo's feature set for one package: the `[features]` keys PLUS the implicit feature every
    optional dependency gets unless some feature already refers to it as `dep:<name>`.

    This is a reimplementation of a cargo rule, which is exactly the kind of thing that drifts —
    hence `--verify-enumeration`, which holds it to `cargo metadata`'s answer.
    """
    feats = manifest.get("features") or {}
    referenced_as_dep: set[str] = set()
    for entries in feats.values():
        for item in entries or []:
            if isinstance(item, str) and item.startswith("dep:"):
                referenced_as_dep.add(item[4:].split("/", 1)[0].split("?", 1)[0])
    optional: set[str] = set()

    def scan(tbl: dict | None) -> None:
        for dep_name, spec in (tbl or {}).items():
            if isinstance(spec, dict) and spec.get("optional"):
                optional.add(dep_name)

    scan(manifest.get("dependencies"))
    scan(manifest.get("build-dependencies"))
    for _target, tspec in (manifest.get("target") or {}).items():
        scan(tspec.get("dependencies"))
        scan(tspec.get("build-dependencies"))
    return set(feats) | (optional - referenced_as_dep - set(feats))


class Tree:
    """The (crate, feature) universe, plus where each crate's manifest lives."""

    def __init__(self, pairs: set[tuple[str, str]], home: dict[str, Path], n_pkgs: int):
        self.pairs = pairs
        self.home = home  # crate -> manifest dir, relative to ROOT
        self.n_pkgs = n_pkgs


def read_tree(root: Path) -> Tree:
    pairs: set[tuple[str, str]] = set()
    home: dict[str, Path] = {}
    n = 0
    for m in find_manifests(root):
        rel = m.relative_to(root)
        if is_vendored(rel):
            continue
        try:
            data = tomllib.load(open(m, "rb"))
        except Exception as exc:  # a Cargo.toml this gate cannot read is an environment problem
            fatal(f"{rel}: could not parse ({exc}). Refusing to report on a tree I cannot read.")
        pkg = data.get("package")
        if not pkg:
            continue
        name = pkg.get("name")
        if not isinstance(name, str):
            continue  # `name.workspace = true` — inherited; the owning workspace supplies it
        n += 1
        home.setdefault(name, rel.parent)
        for f in enumerate_features(data):
            pairs.add((name, f))
    return Tree(pairs, home, n)


# ════════════════════════════════════════════════════════════════════════════════
# THE LEDGER
# ════════════════════════════════════════════════════════════════════════════════
class Ledger:
    def __init__(self, rows: list[tuple[str, str, str, str]], directives: dict[str, str], path: Path):
        self.rows = rows  # (crate, feature, tier, why)
        self.directives = directives
        self.path = path

    @property
    def pairs(self) -> set[tuple[str, str]]:
        return {(c, f) for c, f, _, _ in self.rows}

    def by_tier(self, tier: str) -> list[tuple[str, str, str, str]]:
        return [r for r in self.rows if r[2] == tier]


def read_ledger(path: Path) -> Ledger:
    if not path.is_file():
        fatal(f"ledger {path} is missing. Without it every pair is untiered and nothing is claimed.")
    rows: list[tuple[str, str, str, str]] = []
    directives: dict[str, str] = {}
    seen: dict[tuple[str, str], int] = {}
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.rstrip("\n")
        if line.startswith("#!"):
            k, _, v = line[2:].partition("=")
            directives[k.strip()] = v.strip()
            continue
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 4:
            fatal(f"{path}:{lineno}: expected 4 tab-separated columns, got {len(parts)}: {line!r}")
        crate, feature, tier, why = (p.strip() for p in parts)
        if (crate, feature) in seen:
            fatal(f"{path}:{lineno}: {crate}:{feature} is already tiered at line {seen[(crate, feature)]}.")
        seen[(crate, feature)] = lineno
        rows.append((crate, feature, tier, why))
    return Ledger(rows, directives, path)


# ════════════════════════════════════════════════════════════════════════════════
# STATIC PHASE — returns (disagreement failures, discipline failures)
# ════════════════════════════════════════════════════════════════════════════════
def static_phase(
    tree: Tree,
    led: Ledger,
    *,
    min_pairs: int = MIN_PAIRS,
    min_t3: int = MIN_T3,
    max_t4: int = MAX_T4,
    known_red: Path | None = KNOWN_RED,
    quiet: bool = False,
) -> tuple[list[str], list[str]]:
    disagree: list[str] = []  # ledger <-> tree: exit 1
    discipline: list[str] = []  # the map lies: exit 3

    def d(msg: str) -> None:
        disagree.append(msg)
        if not quiet:
            print(f"  {RED}FAIL{OFF} {msg}", file=_LOG, flush=True)

    def x(msg: str) -> None:
        discipline.append(msg)
        if not quiet:
            print(f"  {RED}FAIL{OFF} {msg}", file=_LOG, flush=True)

    def o(msg: str) -> None:
        if not quiet:
            ok(msg)

    # S5c — the enumerator worked at all.
    if len(tree.pairs) < min_pairs:
        x(
            f"the enumerator found only {len(tree.pairs)} (crate, feature) pairs; the floor in this "
            f"script is {min_pairs} (242 counted 2026-07-26). A near-empty universe is an "
            f"enumerator bug, and it must not read as a clean tree."
        )
    else:
        o(f"enumerated {len(tree.pairs)} (crate, feature) pairs over {tree.n_pkgs} first-party packages")

    # S1 — TOTALITY. The one that catches a feature arriving uncovered.
    untiered = sorted(tree.pairs - led.pairs)
    for c, f in untiered:
        d(
            f"{c}:{f} EXISTS IN THE TREE AND HAS NO TIER. A cargo feature is a subtraction that "
            f"emits no line — until it is tiered, nothing in CI says whether it is compiled. Add a "
            f"row to {led.path.name} (T3 `compile-only` is the default answer) and bump the counts."
        )
    if not untiered:
        o(f"TOTAL: all {len(tree.pairs)} pairs are tiered")

    # S2 — STALENESS. The direction a hand-kept list always rots.
    stale = sorted(led.pairs - tree.pairs)
    for c, f in stale:
        d(
            f"{c}:{f} is tiered in {led.path.name} but NO SUCH (crate, feature) EXISTS. The ledger "
            f"is describing a tree that is gone — a row nothing can ever exercise reads as coverage "
            f"and is not."
        )
    if not stale:
        o("no stale rows: every tiered pair still exists")

    # S3 — well-formedness.
    for crate, feature, tier, why in led.rows:
        if tier not in TIERS:
            x(f"{crate}:{feature}: tier {tier!r} is not one of {', '.join(TIERS)}.")
            continue
        if not why:
            x(f"{crate}:{feature} ({tier}): the `why` column is EMPTY. A tier without a reason is a shrug.")
            continue
        if tier == "T4":
            cls = why.split(":", 1)[0].strip()
            if cls not in EXEMPT_CLASSES:
                x(
                    f"{crate}:{feature}: T4 reason must OPEN with one of "
                    f"{', '.join(EXEMPT_CLASSES)} — got {cls!r}. Note that COST is deliberately not a "
                    f"class: an expensive feature is T2 (nightly, own job), never exempt."
                )
            if feature in NEVER_EXEMPT:
                x(
                    f"{crate}:{feature}: the feature name {feature!r} is in NEVER_EXEMPT (in this "
                    f"script, in code). A lane already paid for finding out what its absence costs; "
                    f"it does not get to become an exemption."
                )
        if tier == "T1":
            in_default = why.startswith("default@")
            named = (crate, feature) in PUSH_TRIGGERED_EXPLICIT
            if not in_default and not named:
                x(
                    f"{crate}:{feature} claims T1 (green every push) but is neither recorded as "
                    f"default-activated (`default@<workspace>`) nor listed in "
                    f"PUSH_TRIGGERED_EXPLICIT in this script. A coverage claim with no covering job "
                    f"is the thing this gate exists to refuse."
                )
            if in_default:
                ws = why.split("@", 1)[1].split()[0].rstrip(":")
                if ws not in PUSH_BUILT_WORKSPACES:
                    x(
                        f"{crate}:{feature} claims default coverage in workspace {ws!r}, which no "
                        f"push-triggered job builds (PUSH_BUILT_WORKSPACES). Its own resolve being "
                        f"green is not a CI signal."
                    )
    # S3d — the manual-only flags. This table is not documentation: a pair whose ONLY enabler is
    # a workflow_dispatch workflow may not be counted as per-push coverage. Recording the near-miss
    # and then not enforcing it is how "we know about that" becomes "nothing checks it".
    tier_of = {(c, f): (t, w) for c, f, t, w in led.rows}
    for pair, prov in MANUAL_ONLY_EXPLICIT.items():
        got = tier_of.get(pair)
        if got is None:
            continue  # not in the tree any more; S2 handles the ledger side
        tier, why = got
        if tier == "T1" and not why.startswith("default@"):
            x(
                f"{pair[0]}:{pair[1]} is tiered T1 on the strength of {prov}. That workflow is not "
                f"push-triggered, so it is not per-push coverage. T1 means green EVERY PUSH."
            )
    if not quiet:
        for pair, prov in MANUAL_ONLY_EXPLICIT.items():
            if pair in tier_of and not tier_of[pair][1].startswith("default@"):
                note(f"{pair[0]}:{pair[1]} is enabled ONLY by a manual workflow — {prov}")

    if not discipline:
        o("every row well-formed; T1 claims trace to a named push-triggered job")

    # S5a/S5b — the tier floors.
    n_t3, n_t4 = len(led.by_tier("T3")), len(led.by_tier("T4"))
    if n_t3 < min_t3:
        x(
            f"only {n_t3} pairs in T3; the floor in this script is {min_t3} (79 measured "
            f"2026-07-26). T3 draining into T4 is how a compile sweep becomes decoration."
        )
    else:
        o(f"T3 count {n_t3} >= floor {min_t3}")
    if n_t4 > max_t4:
        x(
            f"{n_t4} pairs are EXEMPT (T4); the ceiling in this script is {max_t4} (9 measured "
            f"2026-07-26). Exemptions may grow, but only by editing that number — deliberately, and "
            f"visibly in a diff."
        )
    else:
        o(f"T4 count {n_t4} <= ceiling {max_t4}")

    # S3e — the sweep's known-red file is a SECOND ledger, so it rots the same way. Every row in
    # it must name a pair that is CURRENTLY T3. A row for a pair that was deleted, or quietly
    # retiered into T4, would otherwise sit there forever: the sweep only judges pairs it ran, so
    # nothing on the cargo side can ever see it. This is the cheap static half, and it is the
    # direction that bit this repo twice in two days.
    if known_red is not None and known_red.is_file():
        t3_pairs = {(c, f) for c, f, t, _ in led.rows if t == "T3"}
        n_rows = 0
        for lineno, raw in enumerate(known_red.read_text().splitlines(), 1):
            if not raw.strip() or raw.lstrip().startswith("#"):
                continue
            parts = raw.split("\t")
            if len(parts) < 3:
                x(f"{known_red.name}:{lineno}: expected 3 tab-separated columns, got {len(parts)}.")
                continue
            n_rows += 1
            pair = (parts[0].strip(), parts[1].strip())
            if pair not in t3_pairs:
                x(
                    f"{known_red.name}:{lineno}: {pair[0]}:{pair[1]} is recorded as a known-broken "
                    f"T3 pair, but it is not T3 today (deleted, or retiered). The sweep only judges "
                    f"pairs it RUNS, so a row like this can never go red on the cargo side — it just "
                    f"sits there looking like accounted-for debt."
                )
        o(f"{known_red.name}: {n_rows} recorded-broken row(s), all still T3")

    # S4 — the ledger's own recorded counts.
    expect = {
        "EXPECT_PAIRS": len(led.rows),
        "EXPECT_T1": len(led.by_tier("T1")),
        "EXPECT_T2": len(led.by_tier("T2")),
        "EXPECT_T3": n_t3,
        "EXPECT_T4": n_t4,
    }
    for key, actual in expect.items():
        if key not in led.directives:
            x(f"{led.path.name} is missing the #!{key}= directive (the recorded count IS the ratchet).")
            continue
        try:
            want = int(led.directives[key])
        except ValueError:
            x(f"{led.path.name}: #!{key}={led.directives[key]!r} is not an integer.")
            continue
        if want != actual:
            x(
                f"{led.path.name}: #!{key}={want} but the rows say {actual}. Rows moved without the "
                f"recorded number moving — make the change deliberate."
            )
    if all(k in led.directives for k in expect):
        o(
            "ledger self-consistent: "
            + ", ".join(f"{k.removeprefix('EXPECT_')}={v}" for k, v in expect.items())
        )

    return disagree, discipline


# ════════════════════════════════════════════════════════════════════════════════
# CARGO CROSS-CHECKS — they may ADD failures, never subtract them
# ════════════════════════════════════════════════════════════════════════════════
def workspace_roots(root: Path) -> list[Path]:
    out = []
    for m in find_manifests(root):
        rel = m.relative_to(root)
        if is_vendored(rel):
            continue
        try:
            data = tomllib.load(open(m, "rb"))
        except Exception:
            continue
        if "workspace" in data:
            out.append(rel.parent)
    return out


def cargo_metadata(cwd: Path, args: list[str]) -> dict | None:
    for extra in (["--offline"], []):
        p = subprocess.run(
            ["cargo", "metadata", "--format-version", "1", *args, *extra],
            cwd=cwd,
            capture_output=True,
            text=True,
        )
        if p.returncode == 0:
            return json.loads(p.stdout)
    return None


def verify_enumeration(root: Path, tree: Tree) -> list[str]:
    """C1 — the tomllib enumerator must agree with cargo's own answer, exactly."""
    fails: list[str] = []
    seen: set[tuple[str, str]] = set()
    queried = 0
    roots = workspace_roots(root)
    for ws in roots:
        md = cargo_metadata(root / ws, ["--no-deps"])
        if md is None:
            # NOT a note. A cross-check that cannot reach a workspace has not cross-checked it,
            # and "unverified" printed in dim grey is exactly the shape of degradation this gate
            # exists to refuse. `--no-deps` needs no network and no resolve, so a failure here is
            # a real environment problem (a missing pinned toolchain, an unreadable manifest).
            fails.append(
                f"{ws}: `cargo metadata --no-deps` FAILED, so the static enumerator is unchecked "
                f"for this workspace. C1's claim is 'the enumerator has not drifted'; it cannot be "
                f"made about a workspace cargo would not describe."
            )
            continue
        queried += 1
        for p in md["packages"]:
            for f in p["features"]:
                seen.add((p["name"], f))
    if queried < MIN_WORKSPACES:
        fails.append(
            f"only {queried} cargo workspaces were cross-checked; the floor in this script is "
            f"{MIN_WORKSPACES} (8 measured 2026-07-26). A shrinking cross-check is a shrinking "
            f"claim, and it must not read as a pass."
        )
    missed = sorted(seen - tree.pairs)
    for c, f in missed:
        fails.append(
            f"{c}:{f} — cargo metadata reports this feature and the static enumerator did NOT. The "
            f"tomllib reimplementation of cargo's implicit-optional-dep rule has drifted; the gate "
            f"is blind to whatever else it drifted on."
        )
    extra = sorted(p for p in tree.pairs - seen if p[0] in {n for n, _ in seen})
    for c, f in extra:
        fails.append(f"{c}:{f} — the static enumerator invented a feature cargo does not report.")
    if not fails:
        ok(f"static enumeration agrees with cargo metadata exactly ({len(seen)} pairs cross-checked)")
    return fails


def default_activated(root: Path, ws: Path, target: str) -> dict[str, set[str]] | None:
    md = cargo_metadata(root / ws, ["--filter-platform", target])
    if md is None or "resolve" not in md or md["resolve"] is None:
        return None
    members = set(md["workspace_members"])
    byid = {p["id"]: p for p in md["packages"]}
    return {byid[n["id"]]["name"]: set(n["features"]) for n in md["resolve"]["nodes"] if n["id"] in members}


def verify_t1(root: Path, led: Ledger, target: str) -> list[str]:
    """C2 — a T1-by-default claim that the resolve does not back is RED. One direction only."""
    fails: list[str] = []
    cache: dict[str, dict[str, set[str]] | None] = {}
    checked = 0
    for crate, feature, tier, why in led.rows:
        if tier != "T1" or not why.startswith("default@"):
            continue
        ws = why.split("@", 1)[1].split()[0].rstrip(":")
        if ws not in cache:
            cache[ws] = default_activated(root, Path(ws), target)
        act = cache[ws]
        if act is None:
            note(f"{ws}: cargo metadata resolve unavailable; T1 claims there unverified")
            continue
        checked += 1
        if feature not in act.get(crate, set()):
            fails.append(
                f"{crate}:{feature} is recorded T1 `default@{ws}`, but the default resolve for that "
                f"workspace does NOT activate it. The claim of per-push coverage is false."
            )
    if not fails:
        ok(f"{checked} T1-by-default claims confirmed against the workspace resolve ({target})")
    return fails


# ════════════════════════════════════════════════════════════════════════════════
# T3 PLAN — the compile-only sweep, emitted from the ledger so CI cannot drift from it
# ════════════════════════════════════════════════════════════════════════════════
NODEFAULT = "nodefault:"


def shard_slice(seq: list, i: int, n: int) -> list:
    """CONTIGUOUS block i of n over an already-sorted sequence.

    Not `k % n`. The plan sorts by (workspace, crate, feature), so a contiguous block keeps a
    crate's features — and usually a whole workspace — inside ONE shard. Modulo would scatter
    them and every shard would pay to build every workspace's dependency graph into its own
    cache. Same total pairs, far less compiling. The blocks PARTITION: no gaps, no overlaps, for
    every n and every length (self-tested below, including n > len).
    """
    if not (n > 0 and 0 <= i < n):
        fatal(f"--shard={i}/{n} is out of range")
    size, rem = divmod(len(seq), n)
    start = i * size + min(i, rem)
    return seq[start : start + size + (1 if i < rem else 0)]


def t3_plan(tree: Tree, led: Ledger, shard: tuple[int, int] | None) -> list[tuple[str, str, str, str]]:
    """-> [(workspace_dir, crate, feature, extra_cargo_flags)] in a stable order.

    The workspace a crate belongs to is the LONGEST workspace root that is a prefix of its
    manifest dir — an inner `[workspace]` (discord-bot, pg-dregg, sel4/dregg-pd, …) wins over the
    repo root, which is exactly cargo's own rule for the excluded members.

    A few features are only meaningful with the defaults OFF (starbridge-v2's `sel4-thin` is
    "mutually exclusive with native-full at the linker level"). A `why` that opens `nodefault:`
    carries that into the sweep's command line. The alternative — recording such a pair as
    permanently broken because the uniform invocation cannot express it — would be a documented
    wound that is never detected, which is the failure mode being closed, not a way to close it.
    """
    roots = sorted((str(w) for w in workspace_roots(ROOT)), key=len, reverse=True)
    plan = []
    for crate, feature, tier, why in led.rows:
        if tier != "T3":
            continue
        home = tree.home.get(crate)
        if home is None:
            continue  # a stale row; S2 already reds on it
        ws = "."
        for cand in roots:
            if cand == ".":
                continue
            if str(home) == cand or str(home).startswith(cand + "/"):
                ws = cand
                break
        flags = "--no-default-features" if why.startswith(NODEFAULT) else ""
        plan.append((ws, crate, feature, flags))
    plan.sort()
    if shard:
        plan = shard_slice(plan, *shard)
    return plan


# ════════════════════════════════════════════════════════════════════════════════
# REGEN — the census is machine-generated; tiers already decided are preserved
# ════════════════════════════════════════════════════════════════════════════════
HEADER = """\
# feature-tiers.tsv — THE FEATURE SURFACE LEDGER that scripts/check-feature-tiers.py enforces.
#
# Every `(crate, feature)` pair in this repository gets a TIER here, or the gate goes RED. That
# TOTALITY is the point: a `#[cfg(feature = ...)]` is a SUBTRACTION THAT EMITS NO LINE, so a
# feature nothing compiles produces no signal at all — the build is green BECAUSE the code is
# absent, which is strictly worse than `#[ignore]` (that at least keeps the file compiling).
#
# MEASURED 2026-07-26: 243 pairs / 145 distinct feature names, declared by 73 of 270 first-party
# packages across 8 cargo workspaces. A push-triggered job compiled 152 of them. NOTHING anywhere
# passes `--all-features`, so the other 91 — 37% of the surface — were fed to rustc by no CI job
# at all and said nothing about it. Two things that LOOK like coverage are not: `pages.yml`
# (`gpui-web`, `web`) is workflow_dispatch ONLY, and `publish-sdk-py.yml` names `kernel` in a
# comment while no step passes it.
#
# THE TIERS
#   T1  green every push. Either activated by the default resolve of a workspace a push-triggered
#       job builds (`default@<workspace>`), or explicitly enabled by a `--features` flag listed
#       WITH ITS PROVENANCE in PUSH_TRIGGERED_EXPLICIT in the checker — never inferred from YAML,
#       because a derivation from the file the accident edits always agrees nothing was expected.
#   T2  heavy but load-bearing — nightly, its own job. These stay OFF by default on purpose
#       (`prove` pulls the plonky3 recursion prover; forcing it into the dev loop would be
#       strictly worse). Armed in .github/workflows/armed-teeth.yml.
#   T3  must at least COMPILE — one `cargo check -p <crate> --features <feature> --all-targets`
#       per pair, run by scripts/feature-t3-sweep.sh from .github/workflows/feature-surface.yml.
#       This catches `#![cfg]` ROT, the majority class: a feature-gated FILE that no longer
#       compiles is invisible until someone turns the feature on, and nobody ever does.
#       `--all-targets` is load-bearing — the gated files here overwhelmingly live in `tests/`.
#       A `why` opening `nodefault:` makes the sweep pass `--no-default-features` (starbridge-v2's
#       `sel4-thin` is mutually exclusive with the default set at the linker level).
#   T4  explicitly EXEMPT, WITH A REASON opening with one of
#       credentials / network / gpu / target / toolchain. COST IS DELIBERATELY NOT A CLASS — an
#       expensive feature is T2, not exempt. armed-teeth.yml's "WHAT IS NOT HERE" section is the
#       discipline being imitated: named, not hidden.
#
# T3 IS COMPILE-ONLY AND SAYS SO. Green means rustc accepted the code. It does not mean the
# feature works, and it NEVER means its tests ran.
#
# COLUMNS (tab-separated; blank lines and '#' comments ignored)
#   crate    cargo package name
#   feature  the feature name as `--features` takes it
#   tier     T1 | T2 | T3 | T4
#   why      T1: `default@<workspace>` or the CI flag. T2: the job that arms it.
#            T3: what turning it on compiles. T4: `<class>: <reason>` — never empty.
#
# REGENERATE:  python3 scripts/check-feature-tiers.py --regen
#   Existing tiers and reasons are PRESERVED; new pairs land as T3 `REVIEW-ME` and stale rows are
#   dropped. The `#!` counts below are rewritten to match, so a regen always shows in a diff.
#
# crate\tfeature\ttier\twhy
"""


def regen(root: Path, tree: Tree, target: str) -> str:
    old = {}
    if LEDGER.is_file():
        for c, f, t, w in read_ledger(LEDGER).rows:
            old[(c, f)] = (t, w)

    act: dict[str, dict[str, set[str]] | None] = {}
    for ws in PUSH_BUILT_WORKSPACES:
        act[ws] = default_activated(root, Path(ws), target)

    rows: list[tuple[str, str, str, str]] = []
    for crate, feature in sorted(tree.pairs):
        if (crate, feature) in old:
            tier, why = old[(crate, feature)]
        else:
            tier, why = None, None
            for ws, activated in act.items():
                if activated and feature in activated.get(crate, set()):
                    tier, why = "T1", f"default@{ws}"
                    break
            if tier is None and (crate, feature) in PUSH_TRIGGERED_EXPLICIT:
                tier, why = "T1", PUSH_TRIGGERED_EXPLICIT[(crate, feature)]
            if tier is None:
                tier, why = "T3", "REVIEW-ME (newly enumerated; no tier decided yet)"
        rows.append((crate, feature, tier, why))

    counts = {t: sum(1 for r in rows if r[2] == t) for t in TIERS}
    out = [HEADER]
    out.append(f"#!EXPECT_PAIRS={len(rows)}\n")
    for t in TIERS:
        out.append(f"#!EXPECT_{t}={counts[t]}\n")
    for r in rows:
        out.append("\t".join(r) + "\n")
    return "".join(out)


# ════════════════════════════════════════════════════════════════════════════════
# SELF-TEST — this guard proves it can go RED, on every run
# ════════════════════════════════════════════════════════════════════════════════
_FIX_PAIRS = {("alpha", "default"), ("alpha", "wide"), ("beta", "gpu-thing"), ("beta", "prove")}
_FIX_HOME = {"alpha": Path("alpha"), "beta": Path("beta")}


def _ledger(rows: list[tuple[str, str, str, str]], tmp: Path, name: str, **override) -> Ledger:
    counts = {t: sum(1 for r in rows if r[2] == t) for t in TIERS}
    body = [f"#!EXPECT_PAIRS={override.get('EXPECT_PAIRS', len(rows))}\n"]
    for t in TIERS:
        body.append(f"#!EXPECT_{t}={override.get('EXPECT_' + t, counts[t])}\n")
    for r in rows:
        body.append("\t".join(r) + "\n")
    p = tmp / name
    p.write_text("".join(body))
    return read_ledger(p)


_GOOD_ROWS = [
    ("alpha", "default", "T1", "default@."),
    ("alpha", "wide", "T3", "compiles the wide-felt encoder"),
    ("beta", "gpu-thing", "T4", "gpu: needs a wgpu adapter; hosted runners have none"),
    ("beta", "prove", "T2", "armed-teeth.yml feature-gated-prove-teeth"),
]


def self_test() -> bool:
    hdr("SELF-TEST — can this gate go RED? (synthetic ledgers; no cargo)")
    passed = True

    def check(label: str, cond: bool, detail: str = "") -> None:
        nonlocal passed
        if cond:
            ok(f"self-test: {label}")
        else:
            passed = False
            print(f"  {RED}FAIL{OFF} self-test: {label} {detail}", file=_LOG, flush=True)

    tmp = Path(tempfile.mkdtemp(prefix="feature-tiers-selftest."))
    try:
        tree = Tree(set(_FIX_PAIRS), dict(_FIX_HOME), 2)
        fx = dict(min_pairs=4, min_t3=1, max_t4=1, known_red=None, quiet=True)

        # POLE A — the honest ledger is GREEN. A gate that reds on everything is not a gate.
        led = _ledger(_GOOD_ROWS, tmp, "good.tsv")
        dis, dsc = static_phase(tree, led, **fx)
        check("intact ledger is GREEN", dis == [] and dsc == [], f"got {dis} / {dsc}")

        # POLE B1 — THE INCIDENT: a pair exists and nothing tiers it.
        led = _ledger([r for r in _GOOD_ROWS if r[1] != "wide"], tmp, "untiered.tsv")
        dis, dsc = static_phase(tree, led, **fx)
        check(
            "an UNTIERED pair (a feature arrived uncovered) goes RED as a disagreement",
            any("alpha:wide" in m and "NO TIER" in m for m in dis),
            f"got {dis}",
        )

        # POLE B2 — the ledger rotting upward: a row for a feature that no longer exists.
        led = _ledger(_GOOD_ROWS + [("alpha", "deleted-feature", "T3", "x")], tmp, "stale.tsv")
        dis, dsc = static_phase(tree, led, **fx)
        check(
            "a STALE row (tier for a feature that no longer exists) goes RED",
            any("alpha:deleted-feature" in m and "NO SUCH" in m for m in dis),
            f"got {dis}",
        )

        # POLE B3 — an unknown tier name.
        led = _ledger([("alpha", "wide", "T9", "?") if r[1] == "wide" else r for r in _GOOD_ROWS], tmp, "tier9.tsv")
        dis, dsc = static_phase(tree, led, **fx)
        check("an unknown TIER name goes RED as discipline", any("'T9'" in m for m in dsc), f"got {dsc}")

        # POLE B4 — a tier with no reason.
        led = _ledger([("alpha", "wide", "T3", "") if r[1] == "wide" else r for r in _GOOD_ROWS], tmp, "noreason.tsv")
        dis, dsc = static_phase(tree, led, **fx)
        check("an EMPTY reason goes RED", any("EMPTY" in m for m in dsc), f"got {dsc}")

        # POLE B5 — an exemption with no class ("exempt because reasons").
        led = _ledger(
            [("beta", "gpu-thing", "T4", "it is awkward") if r[1] == "gpu-thing" else r for r in _GOOD_ROWS],
            tmp,
            "unclassed.tsv",
        )
        dis, dsc = static_phase(tree, led, **fx)
        check("an UNCLASSED exemption goes RED", any("must OPEN with" in m for m in dsc), f"got {dsc}")

        # POLE B6 — COST is not an exemption class; expensive means T2, not exempt.
        led = _ledger(
            [("beta", "gpu-thing", "T4", "cost: it takes 40 minutes") if r[1] == "gpu-thing" else r for r in _GOOD_ROWS],
            tmp,
            "cost.tsv",
        )
        dis, dsc = static_phase(tree, led, **fx)
        check("`cost:` is REFUSED as an exemption class", any("must OPEN with" in m for m in dsc), f"got {dsc}")

        # POLE B7 — a NEVER_EXEMPT feature parked in T4.
        led = _ledger(
            [("beta", "prove", "T4", "network: needs a notary") if r[1] == "prove" else r for r in _GOOD_ROWS],
            tmp,
            "neverexempt.tsv",
        )
        dis, dsc = static_phase(tree, led, **fx)
        check("a NEVER_EXEMPT feature in T4 goes RED", any("NEVER_EXEMPT" in m for m in dsc), f"got {dsc}")

        # POLE B8 — the T4 ceiling, in code.
        led = _ledger(
            [("alpha", "wide", "T4", "network: pretend") if r[1] == "wide" else r for r in _GOOD_ROWS],
            tmp,
            "ceiling.tsv",
        )
        dis, dsc = static_phase(tree, led, **fx)
        check("EXEMPTING past the ceiling goes RED", any("ceiling in this script" in m for m in dsc), f"got {dsc}")

        # POLE B9 — the T3 floor: draining the compile sweep into exemptions.
        led = _ledger(_GOOD_ROWS, tmp, "t3floor.tsv")
        dis, dsc = static_phase(tree, led, min_pairs=4, min_t3=2, max_t4=1, known_red=None, quiet=True)
        check("T3 UNDER the hardcoded floor goes RED", any("floor in this script is 2" in m for m in dsc), f"got {dsc}")

        # POLE B10 — trimming rows without moving the recorded count.
        led = _ledger(_GOOD_ROWS, tmp, "count.tsv", EXPECT_T3=7)
        dis, dsc = static_phase(tree, led, **fx)
        check("a MISCOUNTED #! directive goes RED", any("#!EXPECT_T3=7" in m for m in dsc), f"got {dsc}")

        # POLE B11 — a T1 claim with no covering job.
        led = _ledger(
            [("alpha", "wide", "T1", "it feels covered") if r[1] == "wide" else r for r in _GOOD_ROWS],
            tmp,
            "fakeT1.tsv",
        )
        dis, dsc = static_phase(tree, led, **fx)
        check("a T1 claim with NO covering job goes RED", any("no covering job" in m for m in dsc), f"got {dsc}")

        # POLE B12 — a T1 default claim in a workspace no push job builds.
        led = _ledger(
            [("alpha", "wide", "T1", "default@pg-dregg") if r[1] == "wide" else r for r in _GOOD_ROWS],
            tmp,
            "unbuiltws.tsv",
        )
        dis, dsc = static_phase(tree, led, **fx)
        check(
            "T1-by-default in a workspace NO push job builds goes RED",
            any("push-triggered job builds" in m for m in dsc),
            f"got {dsc}",
        )

        # POLE B13 — the enumerator returning almost nothing must not read as a clean tree.
        dis, dsc = static_phase(Tree(set(), {}, 0), _ledger([], tmp, "empty.tsv"), **fx)
        check("an EMPTY enumeration is an enumerator bug, not a pass", any("enumerator bug" in m for m in dsc), f"got {dsc}")

        # POLE B14 — the SECOND ledger (the sweep's known-red file) rotting upward: a row for a
        # pair that is no longer T3 can never be caught on the cargo side, because the sweep only
        # judges pairs it ran.
        kr = tmp / "known-red.tsv"
        kr.write_text("# fixture\nalpha\twide\tE0432\nbeta\tgpu-thing\tE0599 (but this is T4 now)\n")
        led = _ledger(_GOOD_ROWS, tmp, "kr.tsv")
        dis, dsc = static_phase(tree, led, min_pairs=4, min_t3=1, max_t4=1, known_red=kr, quiet=True)
        check(
            "a known-red row for a pair that is NOT T3 goes RED",
            any("not T3 today" in m for m in dsc),
            f"got {dsc}",
        )
        kr.write_text("# fixture\nalpha\twide\tE0432\n")
        dis, dsc = static_phase(tree, led, min_pairs=4, min_t3=1, max_t4=1, known_red=kr, quiet=True)
        check("a known-red file naming only T3 pairs is GREEN", dsc == [], f"got {dsc}")

        # POLE B15 — the shards must PARTITION the plan. A sharded sweep whose blocks overlap
        # wastes time; one with a GAP silently never compiles some pairs, which is the entire
        # wound wearing a matrix.
        part_ok = True
        for length in (0, 1, 5, 79, 100):
            for n in (1, 2, 3, 6, 7, 128):
                seq = list(range(length))
                merged = [x for i in range(n) for x in shard_slice(seq, i, n)]
                if merged != seq:
                    part_ok = False
        check("the shard blocks PARTITION the plan (no gaps, no overlaps, any n)", part_ok)

        # POLE C — the enumerator itself, against cargo's implicit-optional-dep rule.
        m_implicit = {"dependencies": {"serde": {"version": "1", "optional": True}}}
        check("an optional dep with no `dep:` reference yields an IMPLICIT feature",
              enumerate_features(m_implicit) == {"serde"}, f"got {enumerate_features(m_implicit)}")
        m_explicit = {"features": {"ser": ["dep:serde"]}, "dependencies": {"serde": {"version": "1", "optional": True}}}
        check("an optional dep referenced as `dep:` yields NO implicit feature",
              enumerate_features(m_explicit) == {"ser"}, f"got {enumerate_features(m_explicit)}")
    finally:
        import shutil

        shutil.rmtree(tmp, ignore_errors=True)

    if passed:
        print(
            f"  {GRN}{BOLD}self-test: this gate demonstrably goes RED on every shape it claims to catch.{OFF}",
            file=_LOG,
            flush=True,
        )
    return passed


# ════════════════════════════════════════════════════════════════════════════════
KNOWN_FLAGS = ("--self-test", "--regen", "--emit-t3-plan", "--verify-enumeration", "--verify-t1")
KNOWN_OPTS = ("--target=", "--shard=")


def main() -> int:
    argv = sys.argv[1:]
    # A MISTYPED FLAG MUST NOT BE SILENTLY IGNORED. `--verify-tl` accepted and doing nothing would
    # make a CI step that looks like it cross-checks and does not — which is this gate's own
    # subject matter, applied to itself.
    for a in argv:
        if a in KNOWN_FLAGS or a.startswith(KNOWN_OPTS):
            continue
        print(
            f"{RED}{BOLD}unknown argument {a!r}.{OFF} Known: {', '.join(KNOWN_FLAGS)}, "
            f"{', '.join(KNOWN_OPTS)}<value>. Refusing rather than ignoring it.",
            file=sys.stderr,
        )
        return 2
    target = "x86_64-unknown-linux-gnu"
    for a in argv:
        if a.startswith("--target="):
            target = a.split("=", 1)[1]

    global _LOG
    if "--emit-t3-plan" in argv:
        _LOG = sys.stderr

    print(f"{BOLD}check-feature-tiers.py — is any cargo feature silently uncovered?{OFF}", file=_LOG)
    print(f"{DIM}  a #[cfg(feature)] is a subtraction that emits no line; this is the line{OFF}", file=_LOG)

    if not self_test():
        print(
            f"\n{RED}{BOLD}THE SELF-TEST FAILED.{OFF} This gate could not demonstrate that it goes "
            f"red, so nothing it says about the tree can be believed.",
            file=sys.stderr,
        )
        return 2
    if "--self-test" in argv:
        return 0

    tree = read_tree(ROOT)

    if "--regen" in argv:
        text = regen(ROOT, tree, target)
        LEDGER.write_text(text)
        print(f"\n{BOLD}wrote {LEDGER.relative_to(ROOT)}{OFF} ({len(tree.pairs)} pairs)", file=_LOG)
        return 0

    led = read_ledger(LEDGER)

    if "--emit-t3-plan" in argv:
        shard = None
        for a in argv:
            if a.startswith("--shard="):
                i, n = a.split("=", 1)[1].split("/")
                shard = (int(i), int(n))
        for ws, crate, feature, flags in t3_plan(tree, led, shard):
            print(f"{ws}\t{crate}\t{feature}\t{flags}")
        return 0

    hdr(f"STATIC — {LEDGER.relative_to(ROOT)} vs the tree (no cargo; runs even if nothing compiles)")
    disagree, discipline = static_phase(tree, led)

    if "--verify-enumeration" in argv:
        hdr("CARGO C1 — the static enumerator vs `cargo metadata` (adds failures, never subtracts)")
        discipline += verify_enumeration(ROOT, tree)
    if "--verify-t1" in argv:
        hdr(f"CARGO C2 — every T1-by-default claim vs the workspace resolve ({target})")
        discipline += verify_t1(ROOT, led, target)

    hdr("VERDICT")
    if not disagree and not discipline:
        counts = {t: len(led.by_tier(t)) for t in TIERS}
        print(
            f"  {GRN}{BOLD}all {len(tree.pairs)} (crate, feature) pairs are tiered{OFF} — "
            f"T1 {counts['T1']} (every push) · T2 {counts['T2']} (nightly) · "
            f"T3 {counts['T3']} (compile-only) · T4 {counts['T4']} (exempt, with a reason)"
        )
        return 0

    if disagree:
        print(f"  {RED}{BOLD}{len(disagree)} LEDGER<->TREE disagreement(s):{OFF}", file=sys.stderr)
        for m in disagree:
            print(f"    - {m}", file=sys.stderr)
    if discipline:
        print(f"  {RED}{BOLD}{len(discipline)} tier-discipline failure(s):{OFF}", file=sys.stderr)
        for m in discipline:
            print(f"    - {m}", file=sys.stderr)

    if disagree:
        print(
            f"\n{RED}{BOLD}THE LEDGER AND THE TREE DISAGREE.{OFF} Either a feature arrived with no "
            f"tier (nothing in CI compiles it and nothing said so), or a row describes a feature "
            f"that is gone. Do NOT fix an untiered pair by deleting the gate's floor — give the "
            f"pair a tier, and if that tier is T4, give it a class and a reason.",
            file=sys.stderr,
        )
        return 1
    print(
        f"\n{RED}{BOLD}THE MAP LIES.{OFF} Every pair is tiered, but a tier claims coverage it does "
        f"not have, an exemption has no class, or a floor moved. Different problem, different code.",
        file=sys.stderr,
    )
    return 3


if __name__ == "__main__":
    sys.exit(main())
