#!/usr/bin/env python3
"""mirror_gates.py — the mechanical gates against the re-authored-mirror disease.

WHAT THIS IS. `docs/audit/RE-AUTHORED-MIRROR-MAP.md` swept 13 subsystems and found 21 instances of
ONE failure mode: a re-authored mirror standing in for the real thing while docs/tests claim the seam
is closed — the tests green BECAUSE they test the mirror. The map's closing line is the mandate for
this file:

    "Fixing 21 and shipping no gate returns this map to its current length within two quarters."

WHY A GATE AND NOT A RULE. The map contains its own control experiment (§3.1 mechanism 2): where the
tree FACTORED the shared thing, no drift occurred — `register_surfaces` is reused verbatim by every
surface, and exactly those 8 of 18 offering keys are the only ones in M10 not at risk. The other 10
were hand-retyped by disciplined authors and drifted. The conclusion is not rhetorical:

    SHARING PREVENTS THIS; DISCIPLINE DOES NOT.

So this is mechanism, not exhortation. Every check below is a thing a machine can decide.

THE GATES.

  A  — ARTIFACT SINGLE AUTHOR (the map's §3.2 highest-leverage move: "an artifact that is loaded at
       runtime may not also be typed by hand anywhere in the tree"; closes 7 of 21 incl. the critical
       M13). Two arms:
         A1  a hand-typed literal re-authoring an artifact that something loads   → the artifact has
             two authors, free to drift. UNLESS the same file welds literal to disk (see below).
         A2  a "golden" that IS the artifact it checks — `const GOLDEN = include_str!(P)` where
             production code also loads P. The test compares the file to itself. It proves nothing.
  D1 — RE-DECLARED-ARTIFACT LINT (map §3.3 D1). A1 is D1's first arm; D1 adds the self-confessing
       mirror doc ("Mirrors `X`" / "Kept inline" / "independent of the ... crate").
  D2 — CITATION CHECKER (map §3.3 D2; "highest truth-per-line"). Every finding in the map cites its
       own falsifier in its own prose. This makes the prose checkable.
  D3 — LIVE-PATH-VS-TESTED-PATH DIFF (map §3.3 D3; "the sharpest signal"). "The tested program is the
       one nothing outside the crate deploys; the deployed program is the one nothing tests" is a
       mechanically detectable inversion.

THE RATCHET. The 21 findings are live at HEAD and are other lanes' work, not this file's. A gate that
is red on arrival gets disabled in a week, so known findings live in `baseline.txt` keyed by a
line-number-independent identity. The gate fails on anything NOT baselined. It ALSO fails when a
baseline entry stops firing — a fixed finding must leave the baseline, so the file can only shrink.
That is the whole ratchet: new mirrors are impossible to land, old ones are impossible to forget.

FALSE POSITIVES ARE THE FAILURE MODE OF A GATE. The iterative/approximative method LEGITIMATELY
builds low-resolution parts and labels them; tripping on those would make this gate hated, and hated
gates get deleted. Two escape hatches, both of which leave a reviewable trace at the site:
  * `// mirror-gate: allow(<gate>) — <reason>` on/above the offending item — for a genuinely
    legitimate shape (a labeled off-live-path double).
  * `baseline.txt` — for a known finding awaiting its lane. Requires an M-id.
An allow with no reason text is itself a failure. Silence is never permission.

USAGE
    python3 scripts/mirror-gates/mirror_gates.py            # all gates, ratchet-enforced
    python3 scripts/mirror-gates/mirror_gates.py --gate A   # one gate
    python3 scripts/mirror-gates/mirror_gates.py --no-baseline   # every finding, incl. baselined
    python3 scripts/mirror-gates/mirror_gates.py --print-baseline  # regenerate baseline.txt body

Exit 0 = clean. Exit 1 = a finding not covered by the baseline, or a stale baseline entry.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

# ── configuration ─────────────────────────────────────────────────────────────

REPO = Path(__file__).resolve().parent.parent.parent
GATEDIR = Path(__file__).resolve().parent

#: Directories whose contents are ARTIFACTS: emitted by a generator (Lean, a script), loaded at
#: runtime, and therefore owned by exactly one author. Anything here is the authority on itself.
ARTIFACT_DIRS = ["circuit/descriptors"]

#: Trees that are not ours to police (vendored, generated, build output).
SKIP_DIRS = {
    "target", ".git", "node_modules", ".cache", "vendor", "dist", "build",
    "__pycache__", ".venv", "venv", ".lake", "lake-packages", ".elan",
}

#: The canary's fixtures are DELIBERATE mirrors — that is their whole job. Scanning them as if they
#: were tree source would have this gate report its own test data as findings. They are reached only
#: via `canary.sh`, which points `--root` straight at them.
EXCLUDE_PREFIXES = ("scripts/mirror-gates/canary/",)

#: A const holding a golden is named like one. Used by A2 to find the goldens that are the artifact.
GOLDEN_NAME = re.compile(r"GOLDEN|EXPECTED|PINNED|CANONICAL|REFERENCE")

#: D3 only looks at constructors — fns returning a program / world / engine / registry, per the map's
#: "each `pub fn` that constructs/deploys a program, world, or engine". The noun at the END of the
#: type name is what decides: `CompiledStory` and `WorldCell` are programs; `CellId` is a name for one
#: and `&[WorldEvent]` is a view into one. Getting this wrong is not cosmetic — a loose match reported
#: `focus`-vs-`lantern` (two `CellId` accessors) as a twin-engine, and a gate that cries about
#: accessors is a gate that gets switched off.
CONSTRUCTED_NOUN = re.compile(
    r"(Story|World|Engine|Program|Host|Board|Roster|Registry|Catalog|Descriptor|Cell)$"
)
#: An identity/handle/view is not the thing it identifies.
NOT_A_PROGRAM = re.compile(r"(Id|Ref|Name|Key|Path|Event|State|Kind|Error|Config)$")
#: Wrappers that still return the constructed object.
UNWRAP = re.compile(r"^(?:Result|Option|Arc|Rc|Box)\s*<\s*(.+?)\s*(?:,[^<>]*)?>$", re.S)


def constructed_type(ret: str) -> str | None:
    """The program/world/engine this return type constructs, or None if it constructs nothing.

    A borrow (`&World`) hands back something the caller already owns — it is an accessor, never a
    second constructor, so it can never be a twin.
    """
    t = re.sub(r"\s+", " ", ret).strip()
    for _ in range(3):
        m = UNWRAP.match(t)
        if not m:
            break
        t = m.group(1).strip()
    if t.startswith("&") or t.startswith("[") or t.startswith("("):
        return None
    core = re.sub(r"<.*$", "", t).strip()
    if not re.fullmatch(r"\w+", core):
        return None
    if NOT_A_PROGRAM.search(core) or not CONSTRUCTED_NOUN.search(core):
        return None
    return core

ALLOW_RE = re.compile(r"mirror-gate:\s*allow\(([A-Za-z0-9_]+)\)\s*(?:[—\-–:]\s*(.+))?")

# ── model ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class Site:
    """One place in the tree. Findings name every site involved — a mirror is always ≥2 places."""
    path: str
    line: int
    note: str = ""

    def __str__(self) -> str:
        base = f"{self.path}:{self.line}"
        return f"{base}  {self.note}" if self.note else base


@dataclass
class Finding:
    gate: str
    kind: str
    #: Line-number-independent identity, so the baseline survives edits above the finding.
    key: str
    message: str
    sites: list[Site] = field(default_factory=list)
    #: An advisory finding is a lead for a human, not a verdict — it never fails a build. D3's
    #: inversion table is the case: "public constructor only tests reach" is mechanically true and
    #: worth reading, but it is not by itself proof of a twin, and failing on it would bury the
    #: signal in siblings that merely share a return type.
    advisory: bool = False

    def render(self) -> str:
        out = [f"  [{self.gate}/{self.kind}] {self.message}"]
        for s in self.sites:
            out.append(f"        {s}")
        out.append(f"        key: {self.key}")
        return "\n".join(out)


@dataclass
class RustFile:
    path: Path
    rel: str
    text: str
    crate: str
    #: True when the whole file is test-only (`tests/`, `benches/`).
    file_is_test: bool
    #: Char offsets of `#[cfg(test)]` regions.
    test_spans: list[tuple[int, int]]

    def line_of(self, off: int) -> int:
        return self.text.count("\n", 0, off) + 1

    def is_test_at(self, off: int) -> bool:
        if self.file_is_test:
            return True
        return any(a <= off < b for a, b in self.test_spans)

    def allows(self, gate: str, off: int) -> tuple[bool, str]:
        """An allow pragma on the item, or in the ~6 lines above it. Must carry a reason."""
        start = max(0, self.text.rfind("\n", 0, max(0, off - 400)))
        window = self.text[start: off + 200]
        for m in ALLOW_RE.finditer(window):
            if m.group(1) in (gate, "all"):
                return True, (m.group(2) or "").strip()
        return False, ""


# ── loading ───────────────────────────────────────────────────────────────────


def crate_of(path: Path) -> str:
    """Nearest ancestor Cargo.toml's package name — the compilation unit that owns this file."""
    for parent in path.parents:
        cargo = parent / "Cargo.toml"
        if cargo.is_file():
            try:
                txt = cargo.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            m = re.search(r'^\s*name\s*=\s*"([^"]+)"', txt, re.M)
            if m:
                return m.group(1)
        if parent == REPO:
            break
    return "?"


def find_test_spans(text: str) -> list[tuple[int, int]]:
    """Char ranges of `#[cfg(test)] mod ... { ... }`, by brace matching."""
    spans: list[tuple[int, int]] = []
    for m in re.finditer(r"#\[cfg\(test\)\]", text):
        brace = text.find("{", m.end())
        if brace < 0 or brace - m.end() > 200:
            continue
        depth, i, n = 0, brace, len(text)
        while i < n:
            c = text[i]
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    spans.append((m.start(), i + 1))
                    break
            elif c == '"':  # skip strings so a brace in a literal cannot unbalance us
                i += 1
                while i < n and text[i] != '"':
                    i += 2 if text[i] == "\\" else 1
            i += 1
    return spans


def load_rust(repo: Path) -> list[RustFile]:
    files: list[RustFile] = []
    for root, dirs, names in os.walk(repo):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
        for name in names:
            if not name.endswith(".rs"):
                continue
            p = Path(root) / name
            try:
                text = p.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            rel = str(p.relative_to(repo))
            if rel.startswith(EXCLUDE_PREFIXES):
                continue
            parts = set(Path(rel).parts)
            files.append(
                RustFile(
                    path=p,
                    rel=rel,
                    text=text,
                    crate=crate_of(p),
                    file_is_test=bool(parts & {"tests", "benches"}),
                    test_spans=find_test_spans(text),
                )
            )
    return files


@dataclass
class Artifact:
    rel: str
    text: str
    name: str | None  # the JSON `name` field — the artifact's self-declared identity
    parsed: object | None


def crate_deps(repo: Path) -> dict[str, set[str]]:
    """crate -> the crates it may call into (deps + dev-deps + itself).

    D3 matches call sites by bare fn name, and names like `compile` / `deploy` / `new` are defined in
    dozens of crates. Without this, `cell/src/interface.rs`'s `compile()` gets attributed to
    `dreggnet-faction::Roster::compile` and every D3 finding cites evidence that is not real. Rust
    cannot call across a dependency it does not declare, so the manifest is a sound over-approximation
    of "could this call site possibly be this symbol" — and it is one file read per crate.
    """
    out: dict[str, set[str]] = {}
    manifests: list[Path] = []
    # A pruned walk, NOT `repo.rglob("Cargo.toml")`: rglob descends into `target/` and every vendored
    # tree and stats ~76k dirs (67s, the whole of D3's cost). `os.walk` with the same SKIP_DIRS prune
    # the file loader uses visits only the source tree.
    for r, dirs, names in os.walk(repo):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
        if "Cargo.toml" in names:
            manifests.append(Path(r) / "Cargo.toml")
    for cargo in manifests:
        if str(cargo.relative_to(repo)).startswith(EXCLUDE_PREFIXES):
            continue
        try:
            txt = cargo.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        m = re.search(r'^\s*name\s*=\s*"([^"]+)"', txt, re.M)
        if not m:
            continue
        name = m.group(1)
        deps: set[str] = {name}
        in_deps = False
        for line in txt.splitlines():
            s = line.strip()
            if s.startswith("["):
                in_deps = "dependencies" in s
                continue
            if not in_deps or not s or s.startswith("#"):
                continue
            d = re.match(r'([A-Za-z0-9_-]+)\s*(?:=|\.)', s)
            if d:
                deps.add(d.group(1))
            # `dep = { package = "real-name" }` — the alias is not the crate.
            p = re.search(r'package\s*=\s*"([^"]+)"', s)
            if p:
                deps.add(p.group(1))
        out[name] = deps
    return out


def load_artifacts(repo: Path) -> list[Artifact]:
    out: list[Artifact] = []
    for d in ARTIFACT_DIRS:
        base = repo / d
        if not base.is_dir():
            continue
        for p in sorted(base.rglob("*")):
            if not p.is_file() or p.suffix not in (".json", ".tsv"):
                continue
            try:
                text = p.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            name, parsed = None, None
            if p.suffix == ".json":
                try:
                    parsed = json.loads(text)
                    if isinstance(parsed, dict):
                        name = parsed.get("name")
                except json.JSONDecodeError:
                    pass
            out.append(Artifact(rel=str(p.relative_to(repo)), text=text, name=name, parsed=parsed))
    return out


# ── non-Rust surfaces (the location miss of §3.3: the tools were Rust-shaped) ──
#
# Sweep two's headline is that the worst finding (M30, a PUBLISHED npm soundness hole) lived on a
# surface no instrument could READ. "UNSWEPT-BECAUSE-UNREADABLE IS NOT LOWER-RISK, IT IS
# LOWER-OBSERVED." So the gate must reach past Rust: Lean (who authors a golden), and the JS/TS
# package graph (whether a differential's oracle is a real build input or a frozen mirror of itself).


def load_lean_json_refs(repo: Path) -> set[str]:
    """Every `*.json` basename named anywhere in a `.lean` file.

    A test-local golden is legitimately authored when a Lean `#guard` PINS it — that is the second
    author the artifact does not otherwise have (map §4.2: "pinned by a Lean `#guard` that names them
    ⇒ a second author the artifact cannot outvote"). This set is how G1 tells a Lean-pinned golden
    (fine) from a private single-loader copy (the M27 blind spot).
    """
    refs: set[str] = set()
    for root, dirs, names in os.walk(repo):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
        for name in names:
            if not name.endswith(".lean"):
                continue
            p = Path(root) / name
            if str(p.relative_to(repo)).startswith(EXCLUDE_PREFIXES):
                continue  # the canary's own fixtures are deliberate mirrors — never scan them as tree
            try:
                txt = p.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for m in re.finditer(r'([\w.\-]+\.json)', txt):
                refs.add(Path(m.group(1)).name)
    return refs


def load_packages(repo: Path) -> list[tuple[Path, dict]]:
    """Every `package.json` and its parsed body — the JS/TS compilation units G2 reasons over."""
    out: list[tuple[Path, dict]] = []
    for root, dirs, names in os.walk(repo):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
        if "package.json" not in names:
            continue
        p = Path(root) / "package.json"
        if str(p.relative_to(repo)).startswith(EXCLUDE_PREFIXES):
            continue  # the canary's own fixtures are deliberate mirrors — never scan them as tree
        try:
            d = json.loads(p.read_text(encoding="utf-8", errors="replace"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(d, dict):
            out.append((p, d))
    return out


def git_untracked(root: Path, reldir: str) -> bool:
    """True when `git ls-files <reldir>` lists NOTHING — the dir is gitignored/untracked.

    This is M30's dispositive fact: `wasm/pkg/.gitignore` is a single `*`, `git ls-files wasm/pkg` =
    0, so on a fresh clone the oracle does not exist and the drift-killer cannot run at all. Falls back
    to a `.gitignore`-ignores-everything read when git is unavailable (e.g. a non-repo canary root that
    was not `git init`ed), so the gate is decidable with or without git.
    """
    try:
        r = subprocess.run(
            ["git", "-C", str(root), "ls-files", "--", reldir],
            capture_output=True, text=True, timeout=30,
        )
        if r.returncode == 0:
            return r.stdout.strip() == ""
    except (OSError, subprocess.SubprocessError):
        pass
    gi = root / reldir / ".gitignore"
    if gi.is_file():
        try:
            lines = [ln.strip() for ln in gi.read_text(encoding="utf-8", errors="replace").splitlines()]
        except OSError:
            lines = []
        if any(ln in ("*", "**", "**/*", "/*") for ln in lines if ln and not ln.startswith("#")):
            return True
    return False


# ── literal / const scanning ──────────────────────────────────────────────────

#: `const NAME: &str = r#"..."#;` — the hand-typed artifact copy.
RAW_CONST = re.compile(
    r'(?:pub(?:\([^)]*\))?\s+)?const\s+([A-Z_0-9]+)\s*:\s*&(?:\'static\s+)?str\s*=\s*r#"(.*?)"#\s*;',
    re.S,
)
#: `const NAME: &str = include_str!("path");` — the loaded artifact.
INCLUDE_CONST = re.compile(
    r'(?:pub(?:\([^)]*\))?\s+)?const\s+([A-Z_0-9]+)\s*:\s*&(?:\'static\s+)?str\s*=\s*'
    r'include_str!\(\s*"([^"]+)"\s*\)\s*;'
)
#: any `include_str!("path")`, const-bound or not.
INCLUDE_ANY = re.compile(r'include_str!\(\s*"([^"]+)"\s*\)')


def resolve_include(rf: RustFile, rel_target: str) -> str | None:
    """`include_str!` is relative to the including FILE — resolve to a repo-relative path."""
    try:
        p = (rf.path.parent / rel_target).resolve()
        return str(p.relative_to(REPO))
    except (ValueError, OSError):
        return None


def json_identity(s: str) -> tuple[str | None, object | None]:
    try:
        v = json.loads(s)
    except json.JSONDecodeError:
        return None, None
    if isinstance(v, dict):
        return v.get("name"), v
    return None, v


# ── GATE A — artifact single author ───────────────────────────────────────────


def gate_a(rust: list[RustFile], artifacts: list[Artifact]) -> list[Finding]:
    """An artifact loaded at runtime may not also be typed by hand anywhere in the tree.

    A1 — a hand-typed literal whose parsed identity IS a loaded artifact's identity. Two authors of
         one object: they are free to drift, and M13 is what that looks like (the deployed
         `predicate-arith.json` is 5 columns wide; the "golden" hand-typed beside it is 24, missing
         the entire value<->fact weld — and NOTHING compared them).

         THE ONE LEGITIMATE FORM, and the reason this is not simply "no literals": a hand-typed copy
         is fine when the same file ALSO `include_str!`s the artifact and asserts the two are equal.
         Then the literal cannot silently drift — the assert is the weld, and disk stays the single
         authority. `turn_chain_emit_gate.rs` is the map's named compliant exemplar and it has
         exactly this shape. So the rule is not "never type it" but "never type it UNWELDED".

    A2 — a golden that IS the artifact. `const GOLDEN_JSON = include_str!(P)` where production code
         also loads P means the test compares the file to itself: a tautology that survives any
         corruption of P, because both sides move together. The map names two live instances
         (`presentation_descriptor_witness.rs:179`, `blinded_membership_witness.rs:347`) and they
         are real: `descriptor_by_name.rs:200` loads the same file the "golden" loads.
    """
    findings: list[Finding] = []
    by_name = {a.name: a for a in artifacts if a.name}

    # Who LOADS each artifact, and from where? An artifact loaded only by a test is not a runtime
    # artifact; one loaded by production code is, and it is that author's alone.
    loaders: dict[str, list[Site]] = {}
    prod_loaders: dict[str, list[Site]] = {}
    load_offsets: dict[str, list[tuple[str, int]]] = {}
    for rf in rust:
        for m in INCLUDE_ANY.finditer(rf.text):
            tgt = resolve_include(rf, m.group(1))
            if not tgt or not any(tgt.startswith(d + "/") for d in ARTIFACT_DIRS):
                continue
            site = Site(rf.rel, rf.line_of(m.start()), f"[{rf.crate}]")
            loaders.setdefault(tgt, []).append(site)
            if not rf.is_test_at(m.start()):
                # Keyed by (file, char offset) so a const can recognise its OWN `include_str!` and
                # never count itself as the second author.
                prod_loaders.setdefault(tgt, []).append(site)
                load_offsets.setdefault(tgt, []).append((rf.rel, m.start()))

    for rf in rust:
        # Which artifacts does THIS file weld (load + compare against a literal)?
        welded: set[str] = set()
        for m in INCLUDE_ANY.finditer(rf.text):
            tgt = resolve_include(rf, m.group(1))
            if tgt and re.search(r"assert(_eq)?!", rf.text):
                welded.add(tgt)

        # ---- A1: hand-typed second author -------------------------------------------------
        for m in RAW_CONST.finditer(rf.text):
            cname, body = m.group(1), m.group(2)
            ident, _ = json_identity(body)
            if not ident or ident not in by_name:
                continue
            art = by_name[ident]
            if art.rel not in loaders:
                continue  # nothing loads it; it is not yet a runtime artifact
            if art.rel in welded:
                continue  # WELDED — literal and disk are asserted equal. The exemplar shape.
            ok, reason = rf.allows("A1", m.start())
            if ok and reason:
                continue
            line = rf.line_of(m.start())
            drift = ""
            if body.strip() != art.text.strip():
                lw = (json.loads(body) or {}).get("trace_width")
                aw = (art.parsed or {}).get("trace_width") if isinstance(art.parsed, dict) else None
                detail = f" (literal trace_width={lw} vs artifact trace_width={aw})" if lw != aw else ""
                drift = f" — AND THEY HAVE ALREADY DRIFTED{detail}"
            findings.append(
                Finding(
                    gate="A",
                    kind="A1-second-author",
                    key=f"A1:{Path(rf.rel).name}:{cname}:{ident}",
                    message=(
                        f"artifact `{ident}` has TWO authors: it is loaded from disk, and re-typed by "
                        f"hand as `{cname}`, with no assertion welding them{drift}. "
                        f"Fix: `include_str!` the artifact and assert the literal equals it (see "
                        f"circuit-prove/tests/turn_chain_emit_gate.rs), or drop the literal."
                    ),
                    sites=[
                        Site(rf.rel, line, f"hand-typed `{cname}` [{rf.crate}]"),
                        Site(art.rel, 1, "the artifact — the single author"),
                    ] + loaders[art.rel][:3],
                )
            )

        # ---- A2: the golden IS the artifact -----------------------------------------------
        for m in INCLUDE_CONST.finditer(rf.text):
            cname, target = m.group(1), m.group(2)
            if not GOLDEN_NAME.search(cname):
                continue
            tgt = resolve_include(rf, target)
            if not tgt or not any(tgt.startswith(d + "/") for d in ARTIFACT_DIRS):
                continue
            # A loader OTHER than this const's own `include_str!`. Without this, every
            # `pub const X = include_str!(P)` would report itself as its own second author.
            others = [
                Site(p, next(f.line_of(o) for f in rust if f.rel == p), "the production loader")
                for (p, o) in load_offsets.get(tgt, [])
                if not (p == rf.rel and m.start() <= o < m.end())
            ]
            if not others:
                continue  # nothing else loads it: the const IS the loader, not a "golden"
            ok, reason = rf.allows("A2", m.start())
            if ok and reason:
                continue
            findings.append(
                Finding(
                    gate="A",
                    kind="A2-golden-is-the-artifact",
                    key=f"A2:{Path(rf.rel).name}:{cname}:{tgt}",
                    message=(
                        f"`{cname}` is defined AS the artifact it checks — it `include_str!`s the same "
                        f"file the production loader reads, so any assertion against it compares the "
                        f"file to itself and holds no matter what the file says. A golden needs an "
                        f"author the artifact does not have (a Lean `#guard` pin), or it is not a golden."
                    ),
                    sites=[
                        Site(rf.rel, rf.line_of(m.start()), f"the \"golden\" `{cname}` [{rf.crate}]"),
                        Site(tgt, 1, "the artifact it claims to check"),
                    ] + others[:3],
                )
            )
    return findings


# ── GATE D1 — the self-confessing mirror ──────────────────────────────────────

MIRROR_DOC = re.compile(
    r"^\s*(?://[/!]|\*)\s*.*?\b("
    r"[Mm]irrors?\s+\[?`([A-Za-z_][A-Za-z0-9_:]*(?:::[A-Za-z0-9_]+)+)`?\]?"
    r"|[Kk]ept inline"
    r"|independent of the\s+`?([a-z0-9_-]+)`?\s+crate"
    r"|[Ii]nline (?:projection|copy|re-implementation|reimplementation)"
    r"|hand-(?:copied|typed|written) (?:mirror|copy|peer)"
    r"|byte-for-byte peer"
    r")",
    re.M,
)

FN_DEF = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+(\w+)", re.M)


def gate_d1(rust: list[RustFile]) -> list[Finding]:
    """A test may not re-declare an object it could import — and the mirrors say so themselves.

    The map's observation (§3.3 D1, third bullet) is that this class CONFESSES: "`project_turn_to_vm`'s
    own doc comment names its violation." M11's doc says it "Mirrors `TurnExecutor::
    convert_turn_effects_to_vm` (which is module-private). Kept inline here so the differential test is
    independent of the executor crate" — and both of those justifications are factually false at HEAD
    (it is `pub use`d at `turn/src/executor/mod.rs:737`, and the file imports `TurnExecutor`).

    So: a doc that says "Mirrors X" / "Kept inline" / "independent of the C crate", attached to an item
    in a test or differential harness, is a self-report. Where the mirrored symbol is importable, the
    mirror is a choice, and this gate makes it a reviewed one.
    """
    findings: list[Finding] = []
    exported = public_symbols(rust)

    harness = re.compile(r"(^|/)(protocol-tests|[\w-]*-differential|[\w-]*-tests)/|(^|/)tests/")
    for rf in rust:
        if not (harness.search(rf.rel) or rf.test_spans):
            continue
        for m in MIRROR_DOC.finditer(rf.text):
            off = m.start()
            if not (rf.file_is_test or rf.is_test_at(off) or harness.search(rf.rel)):
                continue
            ok, reason = rf.allows("D1", off)
            if ok and reason:
                continue
            mirrored = m.group(2) or ""  # group 2 is the mirrored SYMBOL; group 3 is the named crate
            leaf = mirrored.split("::")[-1] if mirrored else ""
            # The item the doc is attached to: the next fn below it.
            fn = FN_DEF.search(rf.text, m.end())
            if not fn or fn.start() - m.end() > 600:
                continue
            fnname = fn.group(1)
            # A `#[test]` fn is a test, not a mirror. Prose like "`runtime_available()` mirrors
            # `init_single_threaded()`" describes BEHAVIOUR and happens to sit above a test; reading
            # it as "this test re-declares that symbol" is misattribution, and it was a real FP here.
            if "#[test]" in rf.text[m.end(): fn.start()]:
                continue
            # THE RULE IS "a test may not re-declare an object it CAN IMPORT". If the named symbol is
            # not publicly reachable, the copy is forced, not chosen — `starbridge-v2`'s `scratch_path`
            # mirrors a helper inside someone else's `#[cfg(test)] mod`, which is genuinely
            # un-importable. Firing there would be blaming an author for a wall.
            if not leaf or leaf not in exported:
                continue
            evidence = [Site(exported[leaf].path, exported[leaf].line,
                             f"`{leaf}` IS importable here — the mirror is avoidable")]
            findings.append(
                Finding(
                    gate="D1",
                    kind="D1-self-declared-mirror",
                    key=f"D1:{rf.crate}:{rf.rel}:{fnname}",
                    message=(
                        f"`{fnname}` documents itself as a re-authored mirror ({m.group(1).strip()!r}), "
                        f"and the symbol it mirrors — `{leaf}` — is publicly importable. So this copy "
                        f"is a CHOICE, and it is free to drift while every test stays green: the "
                        f"harness and the mirror are the same object, so the test cannot see the drift. "
                        f"Fix: import `{leaf}` and delete the copy, or carry "
                        f"`// mirror-gate: allow(D1) — <why>` if the copy is genuinely warranted."
                    ),
                    sites=[Site(rf.rel, rf.line_of(off), f"the self-report [{rf.crate}]")] + evidence,
                )
            )
    return findings


# ── GATE D2 — the citation checker ────────────────────────────────────────────


def gate_d2(rust: list[RustFile]) -> list[Finding]:
    """Prose claims a mechanism; this asserts the mechanism exists.

    The map's §3.3 D2 note is the whole justification: "Every finding in this map cites its own
    falsifier in its own prose. The claims are already written in a near-checkable register — this
    makes them checkable." Only rules with a decidable dual are implemented; each is listed with the
    map finding that motivated it.
    """
    findings: list[Finding] = []

    pub_uses = public_symbols(rust)

    # every call site of every symbol, bucketed — for the "reads it via `F`" rule
    calls: dict[str, list[tuple[RustFile, int]]] = {}
    for rf in rust:
        for m in re.finditer(r"[.\s(\[,]([a-z_][a-z0-9_]{3,})\s*\(", rf.text):
            calls.setdefault(m.group(1), []).append((rf, m.start()))

    deps_cache: dict[str, str] = {}

    def crate_manifest(rf: RustFile) -> str:
        if rf.crate in deps_cache:
            return deps_cache[rf.crate]
        txt = ""
        for parent in rf.path.parents:
            c = parent / "Cargo.toml"
            if c.is_file():
                txt = c.read_text(encoding="utf-8", errors="replace")
                break
            if parent == REPO:
                break
        deps_cache[rf.crate] = txt
        return txt

    # RULE 1 — "`X` is module-private" ⇒ X must not be `pub use`d.        (M11)
    priv_re = re.compile(r"`([A-Za-z_][A-Za-z0-9_:]*)`\s*\((?:which is\s*)?module-\s*\n?\s*private\)"
                         r"|`([A-Za-z_][A-Za-z0-9_:]*)`\s+is\s+module-private")
    for rf in rust:
        flat = re.sub(r"\n\s*//[/!]?", " ", rf.text)  # doc comments wrap; unwrap before matching
        for m in priv_re.finditer(flat):
            sym = (m.group(1) or m.group(2) or "").split("::")[-1]
            if not sym or sym not in pub_uses:
                continue
            ok, reason = rf.allows("D2", 0)
            if ok and reason:
                continue
            findings.append(Finding(
                gate="D2", kind="D2-false-privacy-claim",
                key=f"D2-priv:{rf.crate}:{sym}",
                message=(f"this file claims `{sym}` is module-private and justifies a hand-written "
                         f"mirror with that claim. `{sym}` is `pub use`d. The justification for the "
                         f"mirror is false, so the mirror is unjustified."),
                sites=[Site(rf.rel, 1, f"the claim [{rf.crate}]"), pub_uses[sym]],
            ))

    # RULE 2 — "reads it via `F`" ⇒ F must have ≥1 caller outside its own crate's tests.   (M04)
    reads_re = re.compile(r"(?:reads?|consumes?|dispatch(?:es)?)\s+(?:it\s+)?via\s+\[?`?"
                          r"([A-Za-z_][A-Za-z0-9_:]*::)?([a-z_][a-z0-9_]*)`?\]?")
    for rf in rust:
        flat = re.sub(r"\n\s*//[/!]?", " ", rf.text)
        seen: set[str] = set()
        for m in reads_re.finditer(flat):
            fn = m.group(2)
            if fn in seen:
                continue
            seen.add(fn)
            sites = calls.get(fn, [])
            live_external = [
                (c, o) for c, o in sites
                if c.crate != rf.crate and not c.is_test_at(o)
            ]
            if live_external or not sites:
                continue  # either a real consumer exists, or the symbol is not a fn we can see
            ok, reason = rf.allows("D2", 0)
            if ok and reason:
                continue
            findings.append(Finding(
                gate="D2", kind="D2-cited-consumer-absent",
                key=f"D2-reads:{rf.crate}:{fn}",
                message=(f"the docs say a consumer \"reads it via `{fn}`\", but `{fn}` has no caller "
                         f"outside `{rf.crate}`'s own tests — the cited consumer does not exist. Either "
                         f"a consumer reads it (cite that call), or the claim is a name, not a proof."),
                sites=[Site(rf.rel, 1, f"the claim [{rf.crate}]")] +
                      [Site(c.rel, c.line_of(o), "in-crate test caller") for c, o in sites[:3]],
            ))

    # RULE 3 — "the SAME N offerings `C` registers" ⇒ the citing crate must depend on C.   (M10)
    same_re = re.compile(r"(?:the\s+)?(?:full\s+|SAME\s+|same\s+)(\d+)[- ](?:offering|key|surface|entry)"
                         r"[s]?\s+(?:set\s+)?(?:the\s+)?[^.\n]{0,60}?\(`([a-z0-9_]+)::")
    for rf in rust:
        flat = re.sub(r"\n\s*//[/!]?", " ", rf.text)
        for m in same_re.finditer(flat):
            n, producer_crate = m.group(1), m.group(2).replace("_", "-")
            manifest = crate_manifest(rf)
            if producer_crate in manifest:
                continue
            ok, reason = rf.allows("D2", 0)
            if ok and reason:
                continue
            findings.append(Finding(
                gate="D2", kind="D2-uncited-producer",
                key=f"D2-roster:{rf.crate}:{producer_crate}:{n}",
                message=(f"this file hand-types a {n}-entry roster and cites `{producer_crate}` as the "
                         f"crate that registers it — but `{rf.crate}` does not depend on "
                         f"`{producer_crate}`, so nothing checks the two agree. A parity proof whose "
                         f"peer is a literal is a parity proof about a literal. Fix: dev-dep "
                         f"`{producer_crate}`, derive the roster from it, assert set equality."),
                sites=[Site(rf.rel, 1, f"the hand-typed roster [{rf.crate}]")],
            ))

    return findings


# ── GATE D3 — live path vs tested path ────────────────────────────────────────

FN_SIG = re.compile(
    r"^(?P<indent>\s*)(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:async\s+)?fn\s+(?P<name>\w+)"
    r"\s*(?:<[^>{;]*>)?\s*\((?P<args>[^{;]*?)\)\s*->\s*(?P<ret>[^{;]+?)\s*\{",
    re.M | re.S,
)


def public_symbols(rust: list[RustFile]) -> dict[str, Site]:
    """leaf name -> where it is made public. The oracle for "could you have imported this?".

    Both re-export forms count. A symbol is no less reachable for being a `pub fn` rather than a
    `pub use`, and reading only `pub use` is what let the D2 canary's false "module-private" claim
    slip through the first time this ran.
    """
    out: dict[str, Site] = {}
    for rf in rust:
        for m in re.finditer(r"^\s*pub use\s+([^;]+);", rf.text, re.M):
            for seg in re.split(r"[{},\s]+", m.group(1)):
                leaf = seg.strip().split("::")[-1]
                if leaf and leaf != "*":
                    out.setdefault(leaf, Site(rf.rel, rf.line_of(m.start()), f"`pub use` [{rf.crate}]"))
        for m in re.finditer(r"^\s*pub\s+(?:async\s+)?fn\s+(\w+)", rf.text, re.M):
            if not rf.is_test_at(m.start()):
                out.setdefault(m.group(1), Site(rf.rel, rf.line_of(m.start()), f"`pub fn` [{rf.crate}]"))
    return out


def doc_above(rf: RustFile, off: int) -> str:
    """The `///` block immediately above the item at `off` — where a twin confesses to being one."""
    head = rf.text[max(0, off - 2000): off]
    lines, out = head.splitlines(), []
    for line in reversed(lines[:-1] if lines else []):
        s = line.strip()
        if s.startswith("///") or s.startswith("//!") or s.startswith("*") or s.startswith("/*"):
            out.append(s)
        elif s.startswith("#[") or not s:
            continue
        else:
            break
    return " ".join(reversed(out))


def gate_d3(rust: list[RustFile]) -> list[Finding]:
    """"The tested program is the one nothing outside the crate deploys; the deployed program is the
    one nothing tests" — a mechanically detectable inversion (map §3.3 D3).

    For each crate, group constructors by the type they return. A group with ≥2 members is two
    constructors of one thing — the twin-engine precondition. Then bucket each member's call sites:

        live-external : a caller in another crate, not under `#[cfg(test)]`/`tests/`  → DEPLOYED
        test          : any caller in a test scope                                    → TESTED

    Report the group where one sibling is deployed-but-untested and another is tested-but-undeployed.
    That is M01: `Roster::compile` is what `dreggnet-quest` deploys; `faction_compiled` is what the
    faction tests exercise; they are two hand-maintained constructors of one `CompiledStory` and they
    drifted. Calls propagate through in-crate non-test callers, because `Roster::compile` is deployed
    *through* `Roster::deploy` — reachability is what "deployed" means, not a direct call.
    """
    findings: list[Finding] = []

    # ---- index every constructor: (crate, return type) -> [fn] ------------------------------
    @dataclass
    class Fn:
        name: str
        rf: RustFile
        line: int
        ret: str
        body_span: tuple[int, int]
        is_pub: bool

    def names_sibling(a: "Fn", b: "Fn") -> bool:
        """Does `a`'s doc name `b`? The doc must NAME it, not merely mention the word."""
        return bool(re.search(rf"[`\[]\s*(?:\w+::)*{re.escape(b.name)}\s*[`\]()]",
                              doc_above(a.rf, a.body_span[0] - 1)))

    fns: list[Fn] = []
    for rf in rust:
        # A constructor defined inside a test is a FIXTURE, and fixtures are the legitimate output of
        # the iterative method — never the finding. The disease is a twin on the PUBLIC LIVE SURFACE
        # (`pub fn` in `src/`, outside `#[cfg(test)]`) that only tests reach: that is a shipped API
        # asserting a program nothing deploys. Excluding fixtures here is what keeps this gate honest
        # enough to stay switched on.
        if rf.file_is_test:
            continue
        for m in FN_SIG.finditer(rf.text):
            ret = constructed_type(m.group("ret"))
            if not ret:
                continue
            if rf.is_test_at(m.start()):
                continue
            # A builder CONSUMES self and hands the same value back (`with_config(mut self) ->
            # DeployEngine`). It constructs nothing, so it can never be a rival constructor — and
            # `with_*`-vs-`new` was the largest false-positive class this gate produced. Note `&self`
            # methods stay: `Roster::compile(&self) -> CompiledStory` builds a NEW program out of a
            # roster, which is exactly M01's deployed leg.
            if re.match(r"\s*(?:mut\s+)?self\b", m.group("args")):
                continue
            is_pub = bool(re.match(r"\s*pub", m.group(0)))
            # body span by brace matching from the `{`
            start = rf.text.index("{", m.end() - 1)
            depth, i, n = 0, start, len(rf.text)
            end = n
            while i < n:
                c = rf.text[i]
                if c == "{":
                    depth += 1
                elif c == "}":
                    depth -= 1
                    if depth == 0:
                        end = i
                        break
                i += 1
            fns.append(Fn(m.group("name"), rf, rf.line_of(m.start()), ret, (start, end), is_pub))

    # ---- call sites -------------------------------------------------------------------------
    names = {f.name for f in fns}
    #: sym -> list of (crate, is_test, site)
    sites: dict[str, list[tuple[str, bool, Site]]] = {n: [] for n in names}
    #: (crate, caller_fn) edges, for reachability
    for rf in rust:
        for m in re.finditer(r"[.\s(\[,:]([a-z_][a-z0-9_]*)\s*\(", rf.text):
            n = m.group(1)
            if n not in names:
                continue
            off = m.start()
            sites[n].append((rf.crate, rf.is_test_at(off), Site(rf.rel, rf.line_of(off), f"[{rf.crate}]")))

    # in-crate call graph: caller fn -> callees (both constructors). Computed ONCE — the reachability
    # fixpoint below reads it up to six times, and re-running this regex over every body each pass was
    # the whole of D3's cost (41s -> a few).
    callees: dict[int, set[str]] = {}
    for f in fns:
        body = f.rf.text[f.body_span[0]: f.body_span[1]]
        callees[id(f)] = {m.group(1) for m in re.finditer(r"[.\s(\[,:]([a-z_][a-z0-9_]*)\s*\(", body)} & names

    # ---- reachability: is this constructor DEPLOYED (reachable from a live external caller)? --
    live_ext: dict[str, set[str]] = {}   # sym -> {"crate/path:line"} evidence
    test_hits: dict[str, list[Site]] = {}
    deps = crate_deps(REPO)
    for f in fns:
        # `live_ext` holds rendered strings, not Sites: propagation appends "via f() — <site>" chains,
        # so the set must be homogeneous and orderable. A call site only counts against `f` if its
        # crate actually declares a dependency on `f`'s crate — see `crate_deps`.
        ext = {
            str(s) for (c, t, s) in sites[f.name]
            if c != f.rf.crate and not t and f.rf.crate in deps.get(c, set())
        }
        tst = [s for (c, t, s) in sites[f.name] if t and f.rf.crate in deps.get(c, {c})]
        live_ext[f.name] = set(ext)
        test_hits[f.name] = tst

    by_name: dict[str, list[Fn]] = {}
    for f in fns:
        by_name.setdefault(f.name, []).append(f)

    # propagate: if caller is deployed and calls callee in the same crate (non-test), callee is deployed
    for _ in range(6):  # fixpoint; depth is tiny in practice
        changed = False
        for f in fns:
            if not live_ext[f.name]:
                continue
            if f.rf.is_test_at(f.body_span[0]):
                continue
            for callee in callees[id(f)]:
                if callee == f.name:
                    continue
                for g in by_name.get(callee, []):
                    if g.rf.crate != f.rf.crate:
                        continue
                    before = len(live_ext[callee])
                    live_ext[callee] |= {f"via {f.name}() — {s}" for s in list(live_ext[f.name])[:1]}
                    if len(live_ext[callee]) != before:
                        changed = True
        if not changed:
            break

    # ---- the inversion ----------------------------------------------------------------------
    groups: dict[tuple[str, str], list[Fn]] = {}
    for f in fns:
        groups.setdefault((f.rf.crate, f.ret), []).append(f)

    for (crate, ret), members in sorted(groups.items()):
        uniq = {f.name: f for f in members}
        if len(uniq) < 2:
            continue
        deployed = [f for f in uniq.values() if live_ext[f.name]]
        # `pub` matters: a private helper nothing outside reaches is just a helper. A PUBLIC
        # constructor that only tests reach, sitting beside a sibling the tree deploys, is the twin.
        tested_only = [f for f in uniq.values()
                       if f.is_pub and not live_ext[f.name] and test_hits[f.name]]
        if not deployed or not tested_only:
            continue
        for t in tested_only:
            ok, reason = t.rf.allows("D3", t.body_span[0])
            if ok and reason:
                continue
            # Does either constructor's doc NAME the other? That is the tree admitting the two build
            # one program. It is what separates M01 — whose doc calls `Roster::compile` "the
            # data-driven twin of [`crate::faction_compiled`]" — from a crate that merely has eleven
            # different `CompiledStory` rooms sharing a return type.
            #
            # Body similarity was tried here first and REFUTED on the tree: M01's real twin scores
            # 0.19 Jaccard while `vault_cell_program` vs `escrow_cell_program` — genuinely different
            # programs — scores 0.67. Twins drift, which is the entire point, so their bodies are not
            # similar. The measurement is why this gate cites docs and not bodies.
            twin = next((d for d in deployed if names_sibling(t, d) or names_sibling(d, t)), None)
            d = twin or deployed[0]
            common = [
                Site(d.rf.rel, d.line, f"DEPLOYED  `{d.name}` -> {ret}"),
                *[Site("", 0, f"          external: {s}") for s in sorted(map(str, live_ext[d.name]))[:2]],
                Site(t.rf.rel, t.line, f"TESTED    `{t.name}` -> {ret}   external: (none)"),
                *[Site("", 0, f"          tests: {s}") for s in map(str, test_hits[t.name][:2])],
            ]
            if twin:
                findings.append(Finding(
                    gate="D3", kind="D3-tested-twin-is-not-the-deployed-one",
                    key=f"D3:{crate}:{ret}:{t.name}|{d.name}",
                    message=(
                        f"`{crate}` has two constructors of `{ret}` — and its own docs say so. "
                        f"`{d.name}` is what the tree deploys; `{t.name}` is what the tests exercise, "
                        f"and nothing outside `{crate}` reaches it. So the tested program is not the "
                        f"deployed program, and nothing makes them agree: whatever `{t.name}`'s tests "
                        f"prove, they prove about a program no caller runs. Fix: ONE constructor — "
                        f"factor the shared shape and call it from both, so \"they are identical\" is "
                        f"a tautology rather than a claim."
                    ),
                    sites=common,
                ))
            else:
                findings.append(Finding(
                    gate="D3", kind="D3-public-constructor-only-tests-reach", advisory=True,
                    key=f"D3-adv:{crate}:{ret}:{t.name}|{d.name}",
                    message=(
                        f"`{t.name}` is a PUBLIC constructor of `{ret}` that nothing outside `{crate}` "
                        f"reaches — only tests do — while sibling `{d.name}` is deployed. This is a "
                        f"LEAD, not a verdict: if the two build the same program it is M01's shape and "
                        f"they are free to drift; if `{t.name}` is simply dead public surface, delete "
                        f"it. A human decides which."
                    ),
                    sites=common,
                ))
    return findings


# ── GATE G1 — the test-local golden with no external author ───────────────────
#
# A2 (`:480`) exempts a golden whose only reader is its own `include_str!`, on the theory that a
# single-reader const "IS the loader, not a golden". That theory holds for a PRODUCTION loader of a
# descriptors artifact. It is exactly wrong for a `*golden*` json that lives beside a test: there the
# const is the ONLY reader AND the json is the ONLY author, so the audit compares the file to itself
# and holds no matter what the file says. Measured (map §5.1 G1): the tests-local private-golden shape
# has exactly 4 instances — accumulator_nonrev, adjacency_membership, committed_threshold,
# quantified_absence — all four invisible to A2, and 1 of 4 (adjacency, 26 vs the deployed 34) had
# already drifted. G1 is the inversion A2's own docstring asks for: a `*golden*` under `tests/` must
# have an author the artifact does not have — a Lean `#guard` naming it, a second in-tree loader, or a
# weld to a tracked descriptors artifact. Absent all three, it FAILS.

GOLDEN_INCLUDE = re.compile(
    r'(?:pub(?:\([^)]*\))?\s+)?const\s+([A-Z_0-9]+)\s*:\s*&(?:\'static\s+)?str\s*=\s*'
    r'include_str!\(\s*"([^"]+\.json)"\s*\)\s*;'
)


def gate_g1(rust: list[RustFile], artifacts: list[Artifact], lean_json_refs: set[str]) -> list[Finding]:
    findings: list[Finding] = []
    by_name = {a.name: a for a in artifacts if a.name}

    # Every include_str reader of every json path — so "single loader" is decidable, and a golden read
    # by a SECOND file (a real second pin) is correctly exempted.
    readers: dict[str, list[Site]] = {}
    for rf in rust:
        for m in INCLUDE_ANY.finditer(rf.text):
            tgt = resolve_include(rf, m.group(1))
            if tgt:
                readers.setdefault(tgt, []).append(Site(rf.rel, rf.line_of(m.start()), f"[{rf.crate}]"))

    for rf in rust:
        # A golden is a test asset. A production `include_str!` of a descriptors artifact is not in
        # scope here — that is A1/A2's job, and firing on it would double-report and cry wolf.
        for m in GOLDEN_INCLUDE.finditer(rf.text):
            cname, target = m.group(1), m.group(2)
            off = m.start()
            if not (rf.file_is_test or rf.is_test_at(off)):
                continue
            tgt = resolve_include(rf, target)
            if not tgt:
                continue
            base = Path(tgt).name
            # scope: a GOLDEN-named const, or a file literally named `*golden*`.
            if not (GOLDEN_NAME.search(cname) or "golden" in base.lower()):
                continue
            # descriptors-dir goldens belong to A2 (which has the loader-vs-artifact machinery).
            if any(tgt.startswith(d + "/") for d in ARTIFACT_DIRS):
                continue

            # ---- the three legitimate authors -------------------------------------------------
            second_loader = any(s.path != rf.rel for s in readers.get(tgt, []))
            lean_pinned = base in lean_json_refs
            welded = any(
                (wt := resolve_include(rf, w.group(1))) is not None
                and any(wt.startswith(d + "/") for d in ARTIFACT_DIRS)
                and re.search(r"assert(_eq)?!", rf.text)
                for w in INCLUDE_ANY.finditer(rf.text)
            )
            if second_loader or lean_pinned or welded:
                continue
            ok, reason = rf.allows("G1", off)
            if ok and reason:
                continue

            # ---- drift: does this private copy claim a deployed descriptor's identity? ---------
            drift = ""
            extra_sites: list[Site] = []
            try:
                gd = json.loads((REPO / tgt).read_text(encoding="utf-8", errors="replace"))
            except (OSError, json.JSONDecodeError):
                gd = None
            if isinstance(gd, dict):
                gname = gd.get("name")
                gcons = len(gd.get("constraints", [])) if isinstance(gd.get("constraints"), list) else None
                if gname and gname in by_name:
                    art = by_name[gname]
                    acons = (len(art.parsed.get("constraints", []))
                             if isinstance(art.parsed, dict) and isinstance(art.parsed.get("constraints"), list)
                             else None)
                    if gcons is not None and acons is not None and gcons != acons:
                        drift = (f" — AND IT HAS ALREADY DRIFTED FROM THE DEPLOYED TWIN "
                                 f"(golden {gcons} constraints vs deployed {acons})")
                        extra_sites = [Site(art.rel, 1, f"the DEPLOYED twin `{gname}` — {acons} constraints, "
                                                        f"the single author this golden pretends to mirror")]

            findings.append(Finding(
                gate="G1",
                kind="G1-unpinned-test-golden",
                key=f"G1:{base}:{cname}",
                message=(
                    f"`{cname}` is a test-local golden (`{base}`) whose ONLY reader is its own "
                    f"`include_str!` and whose ONLY author is the file itself — no Lean `#guard` names "
                    f"it, no second loader pins it, no weld ties it to a tracked artifact. Every "
                    f"assertion against it compares the file to itself and holds no matter what the file "
                    f"says{drift}. Fix: pin it from a Lean `#guard` that names the file, weld it to the "
                    f"deployed descriptor (`include_str!` + `assert_eq!`), or carry "
                    f"`// mirror-gate: allow(G1) — <why>`."
                ),
                sites=[
                    Site(rf.rel, rf.line_of(off), f"the \"golden\" `{cname}` [{rf.crate}]"),
                    Site(tgt, 1, "the golden it claims to check — its own single author"),
                ] + extra_sites,
            ))
    return findings


# ── GATE G2 — the oracle-freshness gate ───────────────────────────────────────
#
# The map's G2 (§5.1), the sharpest new signal: a differential test may not compare against a
# gitignored/untracked artifact that no test step rebuilds. That is M30 exactly — `sdk-ts` links its
# oracle as `dregg-wasm: file:../wasm/pkg`, `wasm/pkg/.gitignore` is `*`, `git ls-files wasm/pkg` = 0,
# and (pre-fix) the `test` script built the TS but never the wasm, so "THE DRIFT KILLER" compared a
# 13-day-old binary to itself and passed while the published `@dregg/sdk@0.3.0` dropped `provenance`
# from every capability grant. The rule is decidable from the package graph alone: a `file:` oracle
# dep, used in a test, whose target dir is untracked AND is not regenerated by the `pretest`/`test`
# chain, FAILS LOUD.

WASM_PACK_BUILD = re.compile(r"wasm-pack\s+build\s+(\S+)((?:\s+\S+)*?)\s+--out-dir\s+(\S+)")
OUT_DIR = re.compile(r"--out-dir\s+(\S+)")
NPM_RUN = re.compile(r"npm run (\S+)")
_JS_SUFFIXES = (".mjs", ".cjs", ".js", ".ts", ".mts", ".cts")


def _shell_path(tok: str) -> str:
    """A path lifted out of a shell one-liner, with the quoting stripped off it.

    A real `build:oracle` is rarely a bare command: `sdk-ts` wraps its wasm-pack invocation in
    `sh -c '... exec wasm-pack build ../wasm --target web --out-dir pkg'`, so a `\\S+` capture of the
    out-dir picks up `pkg'` — the closing quote of the `sh -c` — which resolves to `wasm/pkg'`, a
    directory that exists nowhere, and the chain reads as NOT rebuilding the oracle. That reported
    the M30 FIX as M30, which is the worst possible failure for this gate: it accuses the one package
    that actually did the work. Quote and separator characters cannot be part of a path token, so
    dropping them off the edges is unambiguous and does not loosen the match."""
    return tok.strip("'\"`").rstrip(";&|").strip("'\"`")


def _test_chain_text(scripts: dict) -> str:
    """The commands `npm test` actually runs: the `pretest` hook, `test` itself, and every
    `npm run X` they transitively invoke. This is what decides whether the oracle gets rebuilt."""
    seen: set[str] = set()
    parts: list[str] = []

    def add(name: str) -> None:
        if name in seen:
            return
        seen.add(name)
        body = scripts.get(name)
        if not isinstance(body, str) or not body:
            return
        parts.append(body)
        for m in NPM_RUN.finditer(body):
            add(m.group(1))

    add("pretest")
    add("test")
    return "  &&  ".join(parts)


def _rebuilds_oracle(pkgdir: Path, chain: str, oracle: Path) -> bool:
    """Does the test chain contain a command that writes the oracle dir? Resolves `wasm-pack build
    <path> --out-dir <out>` and bare `--out-dir <out>` against the package dir and compares to the
    oracle. Precise on purpose: the pre-fix `tsup ... ` writes `dist`, not `wasm/pkg`, so it does not
    match — which is why M30 was a finding — while the fix `wasm-pack build ../wasm --out-dir pkg`
    resolves to `wasm/pkg` and clears it."""
    try:
        target = oracle.resolve()
    except OSError:
        return False
    for m in WASM_PACK_BUILD.finditer(chain):
        buildpath, outdir = _shell_path(m.group(1)), _shell_path(m.group(3))
        try:
            if (pkgdir / buildpath / outdir).resolve() == target:
                return True
        except OSError:
            pass
    for m in OUT_DIR.finditer(chain):
        try:
            if (pkgdir / _shell_path(m.group(1))).resolve() == target:
                return True
        except OSError:
            pass
    return False


def gate_g2(pkgs: list[tuple[Path, dict]], root: Path) -> list[Finding]:
    findings: list[Finding] = []
    for p, d in pkgs:
        scripts = d.get("scripts", {})
        if not isinstance(scripts, dict) or "test" not in scripts:
            continue  # no differential to gate
        deps = {}
        for key in ("dependencies", "devDependencies"):
            v = d.get(key)
            if isinstance(v, dict):
                deps.update(v)
        file_oracles = {k: v[len("file:"):] for k, v in deps.items()
                        if isinstance(v, str) and v.startswith("file:")}
        if not file_oracles:
            continue

        pkgdir = p.parent
        chain = _test_chain_text(scripts)

        # the package's own test/source text, to confirm the file-dep is actually used as an oracle
        srctext = ""
        for tf in pkgdir.rglob("*"):
            if not tf.is_file() or tf.suffix not in _JS_SUFFIXES:
                continue
            if SKIP_DIRS & set(tf.parts):
                continue
            try:
                srctext += tf.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue

        for name, rel in file_oracles.items():
            # is this dep read as an oracle anywhere in the package? (import/require/resolve of it)
            if not re.search(rf"""['"]{re.escape(name)}(?:/[^'"]*)?['"]""", srctext):
                continue
            oracle = pkgdir / rel
            try:
                reldir = os.path.relpath(oracle.resolve(), root)
            except OSError:
                continue
            if not git_untracked(root, reldir):
                continue  # tracked oracle — a real committed artifact, not a frozen mirror
            if _rebuilds_oracle(pkgdir, chain, oracle):
                continue  # the pretest/test chain rebuilds it — the fresh-build path M30 was missing
            findings.append(Finding(
                gate="G2",
                kind="G2-stale-oracle",
                key=f"G2:{name}:{reldir}",
                message=(
                    f"the differential in this package compares against `{name}` (`file:{rel}`), whose "
                    f"target `{reldir}` is UNTRACKED (`git ls-files` empty — gitignored build output), "
                    f"and NOTHING in the `pretest`/`test` chain rebuilds it. So the test compares "
                    f"against a frozen, possibly-stale snapshot of itself and passes no matter how far "
                    f"the source has drifted — and on a fresh clone the oracle does not exist at all. "
                    f"This is M30's shape: a published byte-faithfulness claim guarding on a 13-day-old "
                    f"binary. Fix: add a `pretest` that rebuilds the oracle (e.g. "
                    f"`wasm-pack build {rel.rsplit('/', 1)[0] if '/' in rel else '.'} --out-dir "
                    f"{rel.rsplit('/', 1)[-1]}`), and make the loader FAIL LOUD when the oracle is absent."
                ),
                sites=[
                    Site(os.path.relpath(p.resolve(), root), 1, "the differential package (test script)"),
                    Site(reldir, 1, f"the oracle `{name}` — untracked, and no test step rebuilds it"),
                ],
            ))
    return findings


# ── ratchet ───────────────────────────────────────────────────────────────────

BASELINE = GATEDIR / "baseline.txt"


def key_gate(key: str) -> str:
    """Which gate owns a baseline key. `A1:`/`A2:` are gate A's two arms; `D2-priv:` etc. are D2's.

    Needed so that `--gate A` does not declare every D1/D2/D3 baseline entry "stale" merely because
    those gates did not run. Without it, debugging one gate reports a tree-wide regression.
    """
    head = key.split(":", 1)[0]
    if head in ("A1", "A2"):
        return "A"
    return head.split("-", 1)[0]


def read_baseline(path: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    if not path.is_file():
        return out
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key, _, note = line.partition("  #")
        out[key.strip()] = note.strip()
    return out


# ── main ──────────────────────────────────────────────────────────────────────

#: Registered gate names. G1/G2 read past Rust (Lean authorship; the JS/TS package graph), closing
#: the §3.3 location miss — the instruments were Rust-shaped, so the Rust-shaped risk model was the
#: only one they could produce.
GATE_NAMES = ["A", "D1", "D2", "D3", "G1", "G2"]


def main() -> int:
    # `REPO` is the resolution base for `include_str!` targets, artifact dirs and the crate graph.
    # The canary points the whole gate at a fixture tree via --root, so this must move with it.
    global REPO
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--gate", action="append", choices=GATE_NAMES, help="run only this gate")
    ap.add_argument("--no-baseline", action="store_true", help="report everything, ratchet off")
    ap.add_argument("--report", action="store_true",
                    help="also print advisory leads (D3's inversion table); never changes exit code")
    ap.add_argument("--print-baseline", action="store_true", help="emit baseline.txt body and exit")
    ap.add_argument("--root", default=str(REPO))
    ap.add_argument("--baseline", default=str(BASELINE),
                    help="the ratchet file; the canary points this at an empty one")
    args = ap.parse_args()

    root = Path(args.root).resolve()
    REPO = root
    rust = load_rust(root)
    artifacts = load_artifacts(root)

    which = args.gate or GATE_NAMES
    # Load the non-Rust surfaces only when a gate that needs them is running — keeps `--gate A` fast.
    lean_json_refs = load_lean_json_refs(root) if "G1" in which else set()
    pkgs = load_packages(root) if "G2" in which else []

    runners = {
        "A": lambda: gate_a(rust, artifacts),
        "D1": lambda: gate_d1(rust),
        "D2": lambda: gate_d2(rust),
        "D3": lambda: gate_d3(rust),
        "G1": lambda: gate_g1(rust, artifacts, lean_json_refs),
        "G2": lambda: gate_g2(pkgs, root),
    }
    findings: list[Finding] = []
    for g in which:
        findings.extend(runners[g]())

    # One key, one finding. `project_turn_to_vm` trips three D1 rules at once ("Inline projection",
    # "Mirrors `X`", "Kept inline") and is still one mirror to fix.
    seen: set[str] = set()
    findings = [f for f in findings if not (f.key in seen or seen.add(f.key))]

    advisories = [f for f in findings if f.advisory]
    findings = [f for f in findings if not f.advisory]

    if args.print_baseline:
        for f in sorted(findings, key=lambda f: f.key):
            print(f"{f.key}  # {f.gate}/{f.kind}")
        return 0

    baseline = read_baseline(Path(args.baseline))
    new = [f for f in findings if f.key not in baseline]
    known = [f for f in findings if f.key in baseline]
    # Only the gates that actually RAN can judge their own baseline entries stale.
    stale = sorted(k for k in set(baseline) - {f.key for f in findings} if key_gate(k) in which)

    surfaces = f"{len(rust)} rust files, {len(artifacts)} artifacts"
    if "G2" in which:
        surfaces += f", {len(pkgs)} npm packages"
    if "G1" in which:
        surfaces += f", {len(lean_json_refs)} lean-named json refs"
    print(f"mirror-gates — {surfaces}, gates: {', '.join(which)}")
    print(f"  findings: {len(findings)}   baselined: {len(known)}   NEW: {len(new)}   "
          f"stale baseline: {len(stale)}   advisory leads: {len(advisories)}")
    print()

    if args.no_baseline:
        for f in sorted(findings, key=lambda f: f.key):
            print(f.render())
            print()

    if args.report and advisories:
        print("-" * 96)
        print("ADVISORY — leads for a human. These never fail a build.")
        print("-" * 96)
        for f in sorted(advisories, key=lambda f: f.key):
            print(f.render())
            print()

    if args.no_baseline:
        return 0

    rc = 0
    if new:
        print("=" * 96)
        print("NEW MIRROR — this is the disease the map is about, and it is not on the ratchet.")
        print("Every finding below names each site involved. Fix it, or if the shape is genuinely")
        print("legitimate, carry `// mirror-gate: allow(<gate>) — <reason>` at the site.")
        print("=" * 96)
        for f in sorted(new, key=lambda f: f.key):
            print(f.render())
            print()
        rc = 1

    if stale:
        print("=" * 96)
        print("STALE BASELINE — these no longer fire. The ratchet only turns one way: delete them")
        print("from scripts/mirror-gates/baseline.txt so they can never silently come back.")
        print("=" * 96)
        for k in stale:
            print(f"  {k}  # {baseline[k]}")
        print()
        rc = 1

    if rc == 0:
        print("GREEN — no new mirrors. " +
              (f"{len(known)} known findings still on the ratchet (see baseline.txt)." if known else ""))
    return rc


if __name__ == "__main__":
    sys.exit(main())
