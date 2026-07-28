#!/usr/bin/env python3
"""check-workspace-closure.py — every Cargo package in this tree is claimed by
exactly one workspace, and a commit's manifest set resolves from a clean
checkout of ITSELF.

═══ THE TWO WOUNDS THIS EXISTS FOR ═══════════════════════════════════════════

(1) THE THIRD STATE.  A package directory that sits under a workspace root and
    declares no `[workspace]` of its own is CLAIMED by that root — and if the
    root names it in neither `members` nor `exclude`, cargo claims it and then
    refuses to resolve it.  The package is present, unbuilt, and silently
    un-linted.  Measured 2026-07-27: the ten `orb/crates/*` packages — ~40,000
    lines of a TLS/HTTP dataplane — had been in exactly that state since
    `4bcb934a3` landed them.  `cargo metadata` from inside any of them exited
    101; `cargo build --workspace` compiled none of them; no `#[allow(dead_code)]`
    in the subtree was checked by anything, which is how
    `orb/crates/dataplane/src/proxy_grpc.rs` (zero callers repo-wide) kept a
    module doc claiming it was "wired into the running dataplane".
    Nothing reported it, because the third state emits no line: cargo only
    complains when you stand inside the directory, and nobody does.

(2) A COMMIT THAT DOES NOT RESOLVE FROM A CLEAN CHECKOUT OF ITSELF.  This tree
    is worked by several agents at once, and AGENTS.md correctly tells each to
    `git commit` only its OWN named paths.  The failure mode that produces is a
    commit whose manifests reference a sibling lane's still-uncommitted work: a
    `members` entry whose directory is not in the commit, a path dependency
    pointing at a directory that only exists on the author's disk.  It is green
    for the author, broken for every clone, and it is a broken bisect point in a
    repo that bisects.  The same shape has already cost ten days here once: a
    canary fixture whose `.gitignore` contained `*` and therefore ignored
    itself, so four files lived only on the author's disk.

═══ WHAT IT CATCHES, AND WHAT IT DOES NOT ════════════════════════════════════

The oracle is `cargo metadata --no-deps` (~0.2-0.4s on this tree), run at every
workspace root, plus one run per package no workspace claimed.  It is a MANIFEST
check.  Stated precisely so nobody reads more into a green than is there:

  CATCHES
    * a package in the third state (neither `members` nor `exclude`, no own
      `[workspace]`) — anywhere in the tree, not just `orb/`;
    * a `members` / `default-members` entry whose directory is absent from the
      tree or the commit;
    * a path dependency (including dev- and build-dependencies) whose target
      directory is absent or carries no manifest;
    * a `Cargo.toml` that does not parse, or that cargo rejects;
    * a path dependency that escapes the tree entirely — `mobile/deos-android-paint`
      took gpui from `../../../emberian-zed/`, a checkout on one laptop, and was
      green in the working tree and unresolvable from any clone;
    * a workspace root whose own manifest is internally inconsistent;
    * a `scripts/local-gates.sh` ROW naming a script the commit does not contain.
      Same class, one altitude up, and live at the time this was written: two
      `identity-as-a-name` rows had been in that file since `40a59541b` while
      `scripts/check-identity-as-a-name.py` existed only on the author's disk, so
      from any clone the two rows whose own comment argues "a gate not in this list
      is not a gate" were not gates.  `MIN_GATE_ROWS` keeps a broken parser from
      reading as clean.

  DOES **NOT** CATCH — a green here is not a green build
    * anything requiring COMPILATION: a missing `mod foo;` file, a type error,
      an unresolved `use`, a missing test fixture, a missing `include_str!`
      target.  A full `cargo check` per commit is not affordable here (the
      workspace is 293 packages behind one target lock) and this gate does not
      attempt it.
    * an explicitly declared target (`[[bin]] name = … path = "src/main.rs"`)
      whose source file is absent.  This gate CLAIMED that one until its own
      `--self-test` refused to go red for it: measured 2026-07-28, `cargo
      metadata --no-deps` exits 0 with the file deleted and only `cargo check`
      reports `can't find bin … at path …`.  Target sources are validated at
      target-resolution time, which `--no-deps` does not reach.
    * a missing NON-Rust artifact a build script needs (orb's `libdrorb.a`, the
      Lean archive, generated descriptors).  `--no-deps` does not run build
      scripts.
    * a toolchain pin naming a toolchain that is not installed: this gate pins
      `RUSTUP_TOOLCHAIN` to the ambient default precisely so a historical scan
      does not start downloading toolchains.
    * anything at all outside `Cargo.toml`s and the directories they name.

  The manifest half is the half that was actually broken, and it is the half
  that costs seconds rather than hours.  That is the whole trade.

═══ USAGE ════════════════════════════════════════════════════════════════════

  python3 scripts/check-workspace-closure.py              # the WORKING TREE
  python3 scripts/check-workspace-closure.py --rev HEAD   # a clean checkout of HEAD
  python3 scripts/check-workspace-closure.py --commits 40 # the last 40 commits, each
                                                          # from a clean checkout of ITSELF
  python3 scripts/check-workspace-closure.py --self-test  # red-proof (see below)
  python3 scripts/check-workspace-closure.py --verbose

`--rev` / `--commits` extract with `git archive <rev> | tar -x` into a private
temp directory, so a commit is judged on what it actually contains and never on
what happens to be lying in the working tree.  THE WORKING TREE IS NEVER
MUTATED BY ANY MODE OF THIS SCRIPT, `--self-test` included: the fault injection
runs against a fresh extract in a temp directory that is removed in a `finally`.
A red-proof that mutates the shared tree is a disarmed guard for as long as the
process that promised to restore it survives, and promises are not mechanisms.

Exit 0 iff every check passed AND the population floors were met.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib

# ── population floors ────────────────────────────────────────────────────────
# A gate whose reader silently found nothing reads as CLEAN, which is the way
# negative assertions fail.  This tree carries ~293 package manifests across
# 43 workspace roots; a scan that sees far fewer has a broken walk, a bad
# ignore list, or an empty extract — and must fail LOUDLY rather than pass
# having checked almost nothing.
MIN_PACKAGES = 275
MIN_WORKSPACE_ROOTS = 35
# `scripts/local-gates.sh` carried ~45 gate rows when this landed.  A parse that
# finds far fewer has lost the array shape, and would silently check nothing.
MIN_GATE_ROWS = 30

# Directories never walked.  `.claude/worktrees/` holds full checkouts of this
# same repo (a second copy of every manifest); `target`/`.lake` are build
# output; the rest are ordinary noise.  `vendor/` is NOT here — it holds real
# packages that the root manifest really excludes, and they must be checked.
IGNORE_DIRS = {
    ".git",
    ".claude",
    "target",
    ".lake",
    "node_modules",
    "__pycache__",
    ".venv",
    "venv",
    "dist",
    ".cargo",
}

CARGO_TIMEOUT = 120


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


def cargo_env() -> dict:
    """Pin the toolchain so a historical scan cannot trigger a rustup download,
    and so a commit predating a toolchain bump is still judged on its manifests."""
    env = dict(os.environ)
    env.setdefault("RUSTUP_TOOLCHAIN", os.environ.get("RUSTUP_TOOLCHAIN", "") or _default_toolchain())
    env["CARGO_TERM_COLOR"] = "never"
    return env


_DEFAULT_TC = None


def _default_toolchain() -> str:
    global _DEFAULT_TC
    if _DEFAULT_TC is None:
        try:
            out = subprocess.run(
                ["rustup", "show", "active-toolchain"],
                capture_output=True, text=True, timeout=30,
            )
            _DEFAULT_TC = out.stdout.split()[0] if out.returncode == 0 and out.stdout.split() else ""
        except Exception:
            _DEFAULT_TC = ""
    return _DEFAULT_TC


def find_manifests(root: str) -> list[str]:
    """Every Cargo.toml git would carry.

    In a git tree this is `ls-files --cached --others --exclude-standard`:
    tracked manifests PLUS untracked ones that are not ignored, so a crate added
    but not yet committed is still checked.  IGNORED paths are deliberately
    out of scope — a package cargo cannot reach from a clone cannot break a
    clone, and this tree carries two large ignored classes that would otherwise
    swamp the report: `.claude/worktrees/*` (whole second checkouts of this same
    repo) and `sel4/gpu-driver-vm/libvmm/` (an untracked upstream checkout whose
    `examples/rust` is a package).  An extracted revision has no `.git` and
    contains only what the commit contains, so the filesystem walk there is the
    same set by construction.
    """
    if os.path.isdir(os.path.join(root, ".git")):
        out = subprocess.run(
            ["git", "-C", root, "ls-files", "--cached", "--others",
             "--exclude-standard", "--", "*Cargo.toml", "Cargo.toml"],
            capture_output=True, text=True, check=True,
        )
        rel = [p for p in out.stdout.splitlines() if p.endswith("Cargo.toml")]
        found = [
            os.path.join(root, p) for p in rel
            if not (set(p.split("/")[:-1]) & IGNORE_DIRS)
        ]
        return sorted(found)

    found = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in IGNORE_DIRS]
        if "Cargo.toml" in filenames:
            found.append(os.path.join(dirpath, "Cargo.toml"))
    return sorted(found)


def classify(manifests: list[str]) -> tuple[list[str], list[str], list[tuple[str, str]]]:
    """-> (package manifests, workspace-declaring manifests, parse failures)."""
    packages, workspaces, unparseable = [], [], []
    for m in manifests:
        try:
            with open(m, "rb") as fh:
                doc = tomllib.load(fh)
        except Exception as exc:  # a manifest that does not parse is a finding
            unparseable.append((m, f"{type(exc).__name__}: {exc}"))
            continue
        if "package" in doc:
            packages.append(m)
        if "workspace" in doc:
            workspaces.append(m)
    return packages, workspaces, unparseable


def cargo_metadata(manifest: str, env: dict) -> tuple[bool, dict | None, str]:
    proc = subprocess.run(
        ["cargo", "metadata", "--no-deps", "--format-version", "1",
         "--manifest-path", manifest],
        capture_output=True, text=True, env=env, timeout=CARGO_TIMEOUT,
    )
    if proc.returncode != 0:
        msg = (proc.stderr or proc.stdout).strip()
        return False, None, msg
    try:
        return True, json.loads(proc.stdout), ""
    except json.JSONDecodeError as exc:
        return False, None, f"metadata emitted unparseable JSON: {exc}"


def first_lines(text: str, n: int = 4) -> str:
    lines = [l for l in text.splitlines() if l.strip()]
    return "\n      ".join(lines[:n])


GATE_ROW_RE = None


def check_gate_registry(root: str, findings, enforce_floors: bool) -> int:
    """Every gate row in `scripts/local-gates.sh` must name a script THIS tree has.

    The runner takes token 2 of each row's command as the script path (its own
    `set -- $cmd; local script="$2"`), and reports MISSING at run time — but only
    for whoever runs it, in whatever tree they have.  A row whose script was never
    committed is green for its author forever and MISSING in every clone.
    """
    import re

    runner = os.path.join(root, "scripts", "local-gates.sh")
    if not os.path.exists(runner):
        return 0

    rows = 0
    with open(runner, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            s = line.strip()
            # a row is  "name|timeout|command"  — quoted, three fields
            m = re.match(r'^"([A-Za-z0-9_.-]+)\|(\d+)\|(.+)"\s*$', s)
            if not m:
                continue
            rows += 1
            name, cmd = m.group(1), m.group(3)
            parts = cmd.split()
            if len(parts) < 2:
                continue
            script = parts[1]
            if not os.path.exists(os.path.join(root, script)):
                findings.add(
                    "GATE_SCRIPT_MISSING", script,
                    f"row `{name}` in scripts/local-gates.sh runs `{cmd}`, and that path is "
                    f"not in this tree — the row reports MISSING for everyone but its author",
                )

    if enforce_floors and rows < MIN_GATE_ROWS:
        findings.add(
            "FLOOR", "scripts/local-gates.sh",
            f"parsed only {rows} gate rows (floor {MIN_GATE_ROWS}) — the row regex has lost "
            f"the array shape and this check is inspecting nothing",
        )
    return rows


ALLOW_LIST = os.path.join(os.path.dirname(os.path.abspath(__file__)), "workspace-closure-allow.tsv")


def read_allow() -> list[tuple[str, str, str]]:
    """Declared carve-outs as (kind, path, reason).

    A MISSING file is a FAULT, not an empty allowlist. A sibling gate shipped with its
    allowlist untracked and spent 25.5 hours red in every clean checkout while its own
    red-proof reported green, because a missing file read as "nothing is exempt" — which is
    indistinguishable from "no exemptions needed" and completely different in fact.
    """
    if not os.path.exists(ALLOW_LIST):
        print(f"{ALLOW_LIST}: MISSING. A gate whose config is absent cannot be trusted to "
              f"report; `git ls-files --error-unmatch` is the check.", file=sys.stderr)
        raise SystemExit(2)
    rows = []
    with open(ALLOW_LIST, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = line.split("\t")
            if len(parts) < 3:
                print(f"{ALLOW_LIST}: a row needs 3 tab-separated fields", file=sys.stderr)
                raise SystemExit(2)
            rows.append((parts[0].strip(), parts[1].strip(), parts[2].strip()))
    return rows


_ALLOW_HITS: set[int] = set()


_WALKED_REVS = False


def note_rev_walked() -> None:
    """Record that this invocation examined at least one clean EXTRACT, not just the tree."""
    global _WALKED_REVS
    _WALKED_REVS = True


def stale_allow_rows() -> list[tuple[str, str, str]]:
    """Rows that matched NOTHING across this whole invocation — the two-sided half.

    Scoped per-INVOCATION, not per-tree: a carve-out may correctly apply to a clean extract
    and not to the working tree, because they are different trees and THIRD_STATE only
    surfaces where a manifest cannot resolve. Checking staleness per tree made a correct row
    read as spent on whichever tree was walked first.
    """
    # ⚠ ONLY HONEST IF THIS INVOCATION WALKED AN EXTRACT. A carve-out can correctly apply to a
    # clean extract and not to the working tree — THIRD_STATE surfaces only where a manifest
    # cannot resolve, and in the working tree the sibling checkout is present so it resolves.
    # A bare working-tree run therefore matches no extract-only row, and enforcing staleness
    # there would report a CORRECT row as spent. That is the false-positive shape that gets a
    # ratchet disabled, so the check simply does not run in that mode.
    if not _WALKED_REVS:
        return []
    allow = read_allow()
    return [r for i, r in enumerate(allow) if i not in _ALLOW_HITS]


def apply_allow(findings: "Findings") -> list[tuple[str, str, str]]:
    """Drop exempted findings; return the STALE rows (declared, but no longer found).

    Two-sided by construction: a row that stops matching is returned and the caller fails on
    it, so repairing a package retires its own exemption.
    """
    allow = read_allow()
    kept, matched = [], set()
    for kind, path, detail in findings.rows:
        hit = next((i for i, (k, p_, _) in enumerate(allow) if k == kind and p_ == path), None)
        if hit is None:
            kept.append((kind, path, detail))
        else:
            matched.add(hit); _ALLOW_HITS.add(hit)
    findings.rows = kept
    return [allow[i] for i in range(len(allow)) if i not in matched]


class Findings:
    def __init__(self) -> None:
        self.rows: list[tuple[str, str, str]] = []   # (kind, path, detail)

    def add(self, kind: str, path: str, detail: str) -> None:
        self.rows.append((kind, path, detail))

    def __bool__(self) -> bool:
        return bool(self.rows)

    def kinds(self) -> set[str]:
        return {k for k, _, _ in self.rows}


def check_tree(root: str, verbose: bool = False, enforce_floors: bool = True):
    """Run the closure check over one materialised tree.

    Returns (ok: bool, findings: Findings, stats: dict).
    """
    env = cargo_env()
    findings = Findings()
    manifests = find_manifests(root)
    packages, ws_manifests, unparseable = classify(manifests)

    for m, why in unparseable:
        findings.add("UNPARSEABLE", os.path.relpath(m, root), why)

    # The tree root's own manifest is a workspace root even when the walk
    # ordering would not reach it first.
    root_manifest = os.path.join(root, "Cargo.toml")
    roots = list(dict.fromkeys(
        ([root_manifest] if os.path.exists(root_manifest) else []) + ws_manifests
    ))

    claimed: dict[str, str] = {}   # package manifest -> workspace root that claims it
    for r in roots:
        ok, meta, err = cargo_metadata(r, env)
        if not ok:
            findings.add("WORKSPACE_UNRESOLVABLE", os.path.relpath(r, root), first_lines(err))
            continue
        for pkg in meta.get("packages", []):
            mp = os.path.realpath(pkg["manifest_path"])
            claimed.setdefault(mp, os.path.relpath(r, root))

    unclaimed = [p for p in packages if os.path.realpath(p) not in claimed]

    # A package no discovered workspace claimed is either (a) properly detached
    # — cargo resolves it as its own single-package root, which is what a root
    # `exclude` entry produces — or (b) in the third state, where cargo claims
    # it from an ancestor it is not listed in and then refuses.  Ask cargo.
    detached = []
    for u in unclaimed:
        ok, meta, err = cargo_metadata(u, env)
        if not ok:
            findings.add("THIRD_STATE", os.path.relpath(u, root), first_lines(err))
            continue
        ws_root = os.path.realpath(meta.get("workspace_root", ""))
        if ws_root == os.path.realpath(os.path.dirname(u)):
            detached.append(u)
        else:
            # Claimed by an ancestor we did not enumerate as a root (e.g. the
            # ancestor's manifest failed to parse).  Not the third state, but
            # not accounted for either.
            findings.add(
                "UNACCOUNTED", os.path.relpath(u, root),
                f"cargo resolves it under {os.path.relpath(ws_root, root)}, which this scan did not enumerate as a workspace root",
            )

    gate_rows = check_gate_registry(root, findings, enforce_floors)

    stats = {
        "manifests": len(manifests),
        "packages": len(packages),
        "workspace_roots": len(roots),
        "claimed": len(claimed),
        "detached": len(detached),
        "gate_rows": gate_rows,
    }

    if enforce_floors:
        if len(packages) < MIN_PACKAGES:
            findings.add(
                "FLOOR", "-",
                f"only {len(packages)} package manifests found (floor {MIN_PACKAGES}) — "
                f"the walk, the ignore list, or the extract is broken; this is not a clean tree",
            )
        if len(roots) < MIN_WORKSPACE_ROOTS:
            findings.add(
                "FLOOR", "-",
                f"only {len(roots)} workspace roots found (floor {MIN_WORKSPACE_ROOTS}) — same reason",
            )

    if verbose:
        for d in detached:
            print(f"  detached (own workspace root): {os.path.relpath(d, root)}")

    # Declared carve-outs, applied LAST so the walk itself is never narrowed — the reader
    # always sees the whole tree and only the REPORT is filtered. A stale row (declared, but
    # the finding is gone) is itself a failure, so a repair retires its own exemption.
    apply_allow(findings)
    return (not findings), findings, stats


def extract_rev(git_root: str, rev: str, dest: str) -> None:
    """Materialise a clean checkout of <rev> — what a fresh clone would have."""
    os.makedirs(dest, exist_ok=True)
    archive = subprocess.Popen(
        ["git", "-C", git_root, "archive", rev], stdout=subprocess.PIPE
    )
    untar = subprocess.Popen(["tar", "-x", "-C", dest], stdin=archive.stdout)
    archive.stdout.close()
    untar.communicate()
    rc_a = archive.wait()
    if rc_a != 0 or untar.returncode != 0:
        raise RuntimeError(f"git archive {rev} failed (archive={rc_a}, tar={untar.returncode})")


def report(label: str, ok: bool, findings: Findings, stats: dict) -> None:
    print(f"  {label}: {stats['packages']} packages / {stats['workspace_roots']} workspace roots"
          f" / {stats['detached']} detached / {stats['gate_rows']} gate rows", end="")
    if ok:
        print("  ->  OK")
    else:
        print(f"  ->  {len(findings.rows)} FINDING(S)")
        for kind, path, detail in findings.rows:
            print(f"    {kind}  {path}")
            if detail:
                print(f"      {detail}")


def run_worktree(root: str, verbose: bool) -> int:
    print("check-workspace-closure: WORKING TREE")
    ok, findings, stats = check_tree(root, verbose=verbose)
    report("working tree", ok, findings, stats)
    return 0 if ok else 1


def run_revs(git_root: str, revs: list[str], verbose: bool) -> int:
    print(f"check-workspace-closure: {len(revs)} revision(s), each from a clean checkout of ITSELF")
    bad = []
    for rev in revs:
        tmp = tempfile.mkdtemp(prefix="ws-closure-")
        try:
            extract_rev(git_root, rev, tmp)
            ok, findings, stats = check_tree(tmp, verbose=verbose)
            note_rev_walked()  # this invocation examined a clean EXTRACT, so the stale half is judgeable
            subject = subprocess.run(
                ["git", "-C", git_root, "log", "-1", "--format=%h %s", rev],
                capture_output=True, text=True,
            ).stdout.strip()
            report(subject or rev, ok, findings, stats)
            if not ok:
                bad.append((subject or rev, sorted(findings.kinds())))
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    if bad:
        print()
        print(f"check-workspace-closure: {len(bad)} of {len(revs)} revision(s) do NOT resolve from a clean checkout of themselves:")
        for subject, kinds in bad:
            print(f"  {subject}   [{', '.join(kinds)}]")
        return 1
    print()
    print(f"check-workspace-closure: all {len(revs)} revision(s) resolve from a clean checkout of themselves")
    return 0


# ── red-proof ────────────────────────────────────────────────────────────────
# Each fault is injected into a FRESH EXTRACT of HEAD in a private temp
# directory.  The working tree is never touched.  A fault that the checker does
# not notice fails the self-test; so does a fault that MATCHES NOTHING, because
# a fault injection that silently no-ops is how a self-test becomes decoration.

def _inject_third_state(tree: str) -> str:
    """Undo exactly the repair this campaign made: take `orb` back out of the
    root `exclude` and delete `orb/Cargo.toml`.  The ten orb packages fall
    straight back into the state they spent the whole window in."""
    manifest = os.path.join(tree, "Cargo.toml")
    src = open(manifest, encoding="utf-8").read()
    needle = '"forge-ci-runner", "orb",'
    if needle not in src:
        raise AssertionError(
            "fault injection matched NOTHING: the root Cargo.toml exclude array no "
            f"longer contains {needle!r}.  Fix this self-test rather than letting it no-op."
        )
    open(manifest, "w", encoding="utf-8").write(src.replace(needle, '"forge-ci-runner",'))
    orb_manifest = os.path.join(tree, "orb", "Cargo.toml")
    if not os.path.exists(orb_manifest):
        raise AssertionError("fault injection matched NOTHING: orb/Cargo.toml is already absent.")
    os.remove(orb_manifest)
    return "orb back in the third state (removed from root exclude, orb/Cargo.toml deleted)"


def _inject_missing_member(tree: str) -> str:
    """A `members` entry whose directory is not in the commit — the exact shape
    a partial `git add` in a shared tree produces."""
    victim = os.path.join(tree, "turn")
    if not os.path.isdir(victim):
        raise AssertionError("fault injection matched NOTHING: turn/ is absent from the extract.")
    shutil.rmtree(victim)
    return "member directory turn/ absent from the tree while still named in `members`"


def _inject_missing_path_dep(tree: str) -> str:
    """A path dependency pointing at a directory a sibling lane never committed."""
    manifest = os.path.join(tree, "turn", "Cargo.toml")
    src = open(manifest, encoding="utf-8").read()
    marker = "\n[dependencies]\n"
    if marker not in src:
        raise AssertionError(
            "fault injection matched NOTHING: turn/Cargo.toml has no [dependencies] table."
        )
    injected = src.replace(
        marker,
        marker + 'a-sibling-lane-never-committed = { path = "../a-sibling-lane-never-committed" }\n',
        1,
    )
    open(manifest, "w", encoding="utf-8").write(injected)
    return "path dependency on a directory that is not in the tree"


def _inject_malformed_manifest(tree: str) -> str:
    manifest = os.path.join(tree, "cell", "Cargo.toml")
    if not os.path.exists(manifest):
        raise AssertionError("fault injection matched NOTHING: cell/Cargo.toml is absent.")
    with open(manifest, "a", encoding="utf-8") as fh:
        fh.write("\n[this is not valid toml\n")
    return "a member manifest that does not parse"


def _inject_escaping_path_dep(tree: str) -> str:
    """A path dependency that leaves the tree — the `deos-android-paint` shape:
    resolvable on the author's disk, on nobody else's."""
    manifest = os.path.join(tree, "turn", "Cargo.toml")
    src = open(manifest, encoding="utf-8").read()
    marker = "\n[dependencies]\n"
    if marker not in src:
        raise AssertionError(
            "fault injection matched NOTHING: turn/Cargo.toml has no [dependencies] table."
        )
    injected = src.replace(
        marker,
        marker + 'a-checkout-beside-the-repo = { path = "../../a-checkout-beside-the-repo" }\n',
        1,
    )
    open(manifest, "w", encoding="utf-8").write(injected)
    return "path dependency pointing OUTSIDE the tree"


def _inject_missing_gate_script(tree: str) -> str:
    """A local-gates row naming a script the commit does not carry — the shape that
    was live in this tree when the check was written (`check-identity-as-a-name.py`
    referenced by two rows since `40a59541b` and never committed)."""
    victim = os.path.join(tree, "scripts", "check-doc-refs.sh")
    if not os.path.exists(victim):
        raise AssertionError("fault injection matched NOTHING: scripts/check-doc-refs.sh is absent.")
    os.remove(victim)
    return "a local-gates row whose script is not in the tree"


FAULTS = [
    ("third state (the orb wound itself)", _inject_third_state, {"THIRD_STATE"}),
    ("local-gates row with no script", _inject_missing_gate_script, {"GATE_SCRIPT_MISSING"}),
    ("member directory missing from the commit", _inject_missing_member, {"WORKSPACE_UNRESOLVABLE"}),
    ("path dep on an uncommitted sibling", _inject_missing_path_dep, {"WORKSPACE_UNRESOLVABLE"}),
    ("path dep escaping the tree", _inject_escaping_path_dep, {"WORKSPACE_UNRESOLVABLE"}),
    ("manifest does not parse", _inject_malformed_manifest, {"WORKSPACE_UNRESOLVABLE", "UNPARSEABLE"}),
]


def run_self_test(git_root: str) -> int:
    print("check-workspace-closure: SELF-TEST (red-proof)")
    print("  every fault is injected into a FRESH EXTRACT of HEAD in a temp dir;")
    print("  the working tree is never mutated by this mode.")
    print()

    failures = 0

    # 0. The control: an unmutated extract of HEAD must be GREEN, or every
    #    "red" below proves nothing.
    tmp = tempfile.mkdtemp(prefix="ws-closure-self-")
    try:
        extract_rev(git_root, "HEAD", tmp)
        ok, findings, stats = check_tree(tmp)
        note_rev_walked()  # this invocation examined a clean EXTRACT, so the stale half is judgeable
        if not ok:
            print("  CONTROL  \033[31mFAIL\033[0m — a clean extract of HEAD is already red;")
            report("HEAD", ok, findings, stats)
            print("  Every fault injection below would be uninterpretable. Fix HEAD first.")
            return 1
        print(f"  CONTROL  \033[32mgreen\033[0m — clean extract of HEAD: "
              f"{stats['packages']} packages, {stats['workspace_roots']} roots, 0 findings")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    # 1..N. Each fault must produce a finding of the expected kind.
    for label, inject, expect_kinds in FAULTS:
        tmp = tempfile.mkdtemp(prefix="ws-closure-self-")
        try:
            extract_rev(git_root, "HEAD", tmp)
            try:
                what = inject(tmp)
            except AssertionError as exc:
                print(f"  {label:44s} \033[31mFAIL\033[0m — {exc}")
                failures += 1
                continue
            ok, findings, stats = check_tree(tmp)
            note_rev_walked()  # this invocation examined a clean EXTRACT, so the stale half is judgeable
            got = findings.kinds()
            if ok:
                print(f"  {label:44s} \033[31mFAIL\033[0m — injected [{what}] and the checker stayed GREEN")
                failures += 1
            elif not (got & expect_kinds):
                print(f"  {label:44s} \033[31mFAIL\033[0m — went red, but as {sorted(got)}, "
                      f"not {sorted(expect_kinds)}; it is not detecting what it claims to")
                failures += 1
            else:
                sample = next(f for f in findings.rows if f[0] in expect_kinds)
                print(f"  {label:44s} \033[32mred\033[0m   {sorted(got & expect_kinds)[0]} {sample[1]}")
        finally:
            shutil.rmtree(tmp, ignore_errors=True)

    # The reader-fault row.  Not a tree fault: the WALK is truncated, which is the
    # shape that has actually bitten this repo (check-doc-refs' awk died on an
    # em-dash under a UTF-8 locale and silently scanned a quarter of the corpus,
    # reporting 0 DEAD).  A checker that sees half the tree must FAIL, not read clean.
    tmp = tempfile.mkdtemp(prefix="ws-closure-self-")
    try:
        extract_rev(git_root, "HEAD", tmp)
        real_find = globals()["find_manifests"]
        try:
            globals()["find_manifests"] = lambda root: real_find(root)[: len(real_find(root)) // 2]
            ok, findings, stats = check_tree(tmp)
            note_rev_walked()  # this invocation examined a clean EXTRACT, so the stale half is judgeable
        finally:
            globals()["find_manifests"] = real_find
        if ok:
            print(f"  {'population floor (blinded reader)':44s} \033[31mFAIL\033[0m — "
                  f"a reader that saw only {stats['packages']} packages read as CLEAN")
            failures += 1
        elif "FLOOR" not in findings.kinds():
            print(f"  {'population floor (blinded reader)':44s} \033[31mFAIL\033[0m — "
                  f"went red as {sorted(findings.kinds())}, not FLOOR")
            failures += 1
        else:
            print(f"  {'population floor (blinded reader)':44s} \033[32mred\033[0m   "
                  f"FLOOR at {stats['packages']} packages (floor {MIN_PACKAGES})")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print()
    total = len(FAULTS) + 1
    if failures:
        print(f"check-workspace-closure --self-test: FAIL — {failures} of {total} faults not detected")
        return 1
    print(f"check-workspace-closure --self-test: all {total} faults detected, control green")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--rev", help="check a clean checkout of this revision (default: the working tree)")
    ap.add_argument("--commits", type=int, help="check the last N commits, each from a clean checkout of itself")
    ap.add_argument("--self-test", action="store_true", help="red-proof: inject faults into temp extracts")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    root = repo_root()

    if args.self_test:
        return run_self_test(root)

    if args.commits:
        revs = subprocess.run(
            ["git", "-C", root, "rev-list", "-n", str(args.commits), "HEAD"],
            capture_output=True, text=True, check=True,
        ).stdout.split()
        return run_revs(root, revs, args.verbose)

    if args.rev:
        return run_revs(root, [args.rev], args.verbose)

    return run_worktree(root, args.verbose)





def _report_stale_rows() -> int:
    """Fail on any carve-out row that matched nothing anywhere. Called once, after every tree."""
    stale = stale_allow_rows()
    if not stale:
        return 0
    print("\ncheck-workspace-closure: STALE CARVE-OUT ROW(S) — the finding they exempt is gone.",
          file=sys.stderr)
    for kind, path, reason in stale:
        print(f"  scripts/workspace-closure-allow.tsv: {kind}  {path}\n"
              f"      no longer found in any tree checked — delete this row.\n"
              f"      (was: {reason})", file=sys.stderr)
    return 1


if __name__ == "__main__":
    # The stale-row half runs AFTER main() so every tree has been walked; a carve-out that
    # matched nothing anywhere is spent, and a spent row is how an exemption becomes permanent.
    sys.exit(max(main(), _report_stale_rows()))
