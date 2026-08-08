#!/usr/bin/env python3
"""check-lean-citations.py — a comment may not cite a Lean name that does not exist.

═══ THE WOUND THIS CLOSES ═══════════════════════════════════════════════════════════════
Measured 2026-08-08: `FinalizedRegionStable` (a deleted hypothesis) was cited as LIVE by six
files including production Rust doc comments; `stableCheck` (deleted, never called) was cited
as "the executable mirror" the node should run; `Distributed.BlocklaceFinality.isCordialBlock`
was cited in a Lean header as "now defined and exported" and exists nowhere; `join --help`
named `propose_join_if_needed`, zero definitions in the tree. Every one of those is a reader
being told something false at exactly the moment they check.

A citation to a deleted or renamed Lean object is the documentation form of a dangling
import — and we gate dangling imports (scripts/check-dangling-imports.sh) precisely because
they kill builds. This gate makes the documentation form DETECTABLE instead of a discovery a
reader makes six weeks later.

═══ WHAT IT CHECKS ══════════════════════════════════════════════════════════════════════
Over every TRACKED .rs and .lean file's comments (worktree), three citation forms:

  1. `Some/File.lean::name`   — the name must occur in that file (decls, fields, ctors).
  2. `Dregg2.Foo.Bar.name`    — dotted, FULLY-QUALIFIED (`Dregg2.`-rooted) only: the last
                                segment must be declared in some tracked .lean file. Relative
                                citations (`Foo.name`) collide with other trees/ecosystems
                                and only reach the --relative report, never the verdict.
                                Tokens that are themselves file names (`Foo.lean`) are
                                check-doc-refs's job and skipped here.
  3. THE WATCHLIST (`.github/dead-lean-names.txt`) — curated known-dead names (and wrong
                                attribution strings): narrating one as live fires anywhere
                                in .rs/.lean comments. When you delete/rename a cited Lean
                                object, add it there in the same commit.
  (report-only, --bare)       — bare backticked names that resolve to nothing; NEVER part
                                of the verdict (comments legitimately cite OCaml daemon
                                functions, kimchi crate methods, GraphQL fields, tactics —
                                existence is undecidable without the target ecosystem).

PRECISION RULES (deliberate: this gate must be quiet to stay alive):
  * In .rs files, forms 2 and 3 only fire inside comment blocks that actually name the Lean
    world (`.lean`, `metatheory`, or `Dregg2`); prose about other ecosystems is out of
    contract.
  * Bare names are only candidates when they contain an underscore or an internal capital
    and are ≥ 4 chars — `stableCheck`, `fold_agrees`, `FinalizedRegionStable` are in;
    `tau`, `insert`, `Finset` are out.  ALL_CAPS names are out (Rust consts).
  * External Lean roots (`List.…`, `Option.…`, Mathlib etc.) are OUT OF CONTRACT for the
    dotted form; if `metatheory/.lake/packages` is present its declarations are also
    admitted to the resolution universe (belt and suspenders for bare names).
  * HISTORY IS LEGAL: a mention within ±5 lines of an explicit history marker
    ("deleted", "former", "used to", "renamed", "no longer", "does not exist", "retracted",
    "removed", "superseded", "was called") or a forward marker ("not yet", "never authored",
    "planned") is skipped. Name history (or plans) explicitly and the gate stays quiet;
    narrate a dead name as live and it fires.

WHAT IT CANNOT CHECK: whether the named thing SAYS what the citing comment claims. That is
a reading job (see docs/reference/READING-ACCOUNTABILITY-2026-08-08.md for the method).
This gate is the existence floor under that job.

═══ USAGE ═══════════════════════════════════════════════════════════════════════════════
    scripts/check-lean-citations.py               # scan the working tree
    scripts/check-lean-citations.py --list        # dump every candidate + resolution
    scripts/check-lean-citations.py --self-test   # prove the gate can go RED (constructive
                                                  # plant: a citation to a name that does
                                                  # not exist MUST fire; a real one must not)

EXIT: 0 clean · 1 dead citation(s) · 2 usage · 3 degenerate scan (fail closed)
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

# ─── repo plumbing ───────────────────────────────────────────────────────────────────────


def repo_root() -> Path:
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True
    )
    if out.returncode != 0:
        print("not a git repository", file=sys.stderr)
        sys.exit(2)
    return Path(out.stdout.strip())


def tracked(root: Path, *patterns: str) -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "--", *patterns],
        capture_output=True,
        text=True,
        cwd=root,
    )
    return [root / line for line in out.stdout.splitlines() if line]


# ─── comment extraction ──────────────────────────────────────────────────────────────────
# A "block" is a run of consecutive comment-bearing lines; we keep (lineno, text) pairs so
# findings point at real lines and the history-marker window works.


def comment_blocks_rust(text: str) -> list[list[tuple[int, str]]]:
    blocks: list[list[tuple[int, str]]] = []
    cur: list[tuple[int, str]] = []
    in_block_comment = False
    for i, line in enumerate(text.splitlines(), 1):
        picked = None
        if in_block_comment:
            end = line.find("*/")
            if end >= 0:
                picked = line[:end]
                in_block_comment = False
            else:
                picked = line
        else:
            m = re.search(r"//[/!]?(.*)$", line)
            b = line.find("/*")
            if b >= 0 and (m is None or b < m.start()):
                end = line.find("*/", b + 2)
                if end >= 0:
                    picked = line[b + 2 : end]
                else:
                    picked = line[b + 2 :]
                    in_block_comment = True
            elif m:
                picked = m.group(1)
        if picked is not None:
            cur.append((i, picked))
        else:
            if cur:
                blocks.append(cur)
            cur = []
    if cur:
        blocks.append(cur)
    return blocks


def comment_blocks_lean(text: str) -> list[list[tuple[int, str]]]:
    """Comment text per line: `--` to EOL and (nested) `/- … -/` spans. Code is dropped."""
    blocks: list[list[tuple[int, str]]] = []
    cur: list[tuple[int, str]] = []
    depth = 0
    for i, line in enumerate(text.splitlines(), 1):
        picked: list[str] = []
        was_in_comment = depth > 0
        rest = line
        while rest:
            if depth > 0:
                close = rest.find("-/")
                nested = rest.find("/-")
                if nested >= 0 and (close < 0 or nested < close):
                    picked.append(rest[:nested])
                    depth += 1
                    rest = rest[nested + 2 :]
                elif close >= 0:
                    picked.append(rest[:close])
                    depth -= 1
                    rest = rest[close + 2 :]
                else:
                    picked.append(rest)
                    rest = ""
            else:
                open_ = rest.find("/-")
                dash = rest.find("--")
                if dash >= 0 and (open_ < 0 or dash < open_):
                    picked.append(rest[dash + 2 :])
                    rest = ""
                elif open_ >= 0:
                    depth += 1
                    rest = rest[open_ + 2 :]
                else:
                    rest = ""
        joined = " ".join(p for p in picked if p.strip())
        if joined.strip():
            cur.append((i, joined))
        elif depth > 0 or was_in_comment:
            cur.append((i, ""))  # blank line INSIDE a block comment keeps block continuity
        else:
            if cur:
                blocks.append(cur)
            cur = []
    if cur:
        blocks.append(cur)
    return blocks


# ─── resolution universes ────────────────────────────────────────────────────────────────

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|scoped\s+)*"
    r"(?:theorem|def|abbrev|structure|inductive|class(?:\s+inductive)?|instance|opaque|axiom|lemma)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
FIELDLIKE_RE = re.compile(r"^\s{2,}(?:\|?\s*)?([a-zA-Z_][A-Za-z0-9_']*)\s*[:(]")
CTOR_RE = re.compile(r"^\s*\|\s*([a-zA-Z_][A-Za-z0-9_']*)")
NAMESPACE_RE = re.compile(r"^\s*(?:namespace|open|section)\s+([A-Za-z0-9_'. ]+)")

RUST_DECL_RE = re.compile(
    r"\b(?:fn|struct|enum|trait|mod|const|static|type|union)\s+([A-Za-z_][A-Za-z0-9_]*)"
)
RUST_FIELD_RE = re.compile(r"^\s+(?:pub(?:\([^)]*\))?\s+)?([a-z_][a-z0-9_]*)\s*:")
RUST_VARIANT_RE = re.compile(r"^\s+([A-Z][A-Za-z0-9_]*)\s*(?:[({,=]|$)")
RUST_LET_RE = re.compile(r"\blet\s+(?:mut\s+)?([a-z_][a-z0-9_]*)")
EXPORT_RE = re.compile(r"@\[export\s+([A-Za-z_][A-Za-z0-9_]*)")

# External Lean names commonly cited bare in prose; kept tiny on purpose — the .lake scan
# is the real widener when the toolchain is present.
EXTERNAL_COMMON = {
    "DecidableEq",
    "HashMap",
    "HashSet",
    "Nodup",
    "Prop",
    "Type",
    "Bool",
    "Nat",
    "List",
    "Array",
    "Option",
    "Finset",
    "Sublist",
    "IsPrefix",
}


def lean_universe(root: Path, include_lake: bool = True) -> tuple[set[str], set[str]]:
    """Returns (decl names incl. dotted-last-segments + fields + ctors, namespace/module segments)."""
    names: set[str] = set()
    segments: set[str] = set()
    files = [
        p
        for p in tracked(root, "*.lean", "**/*.lean")
        if "/.lake/" not in str(p) and not str(p).startswith(str(root / "headver"))
    ]
    for p in files:
        rel = p.relative_to(root)
        for seg in str(rel.with_suffix("")).split("/"):
            segments.add(seg)
        try:
            text = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for line in text.splitlines():
            m = DECL_RE.match(line)
            if m:
                full = m.group(1)
                names.add(full)
                names.add(full.split(".")[-1])
            m = FIELDLIKE_RE.match(line)
            if m:
                names.add(m.group(1))
            m = CTOR_RE.match(line)
            if m:
                names.add(m.group(1))
            m = NAMESPACE_RE.match(line)
            if m:
                for part in m.group(1).replace(",", " ").split():
                    for seg in part.split("."):
                        if seg:
                            segments.add(seg)
            for m in EXPORT_RE.finditer(line):
                names.add(m.group(1))
    if include_lake:
        lake = root / "metatheory" / ".lake" / "packages"
        if lake.is_dir():
            for p in lake.rglob("*.lean"):
                try:
                    text = p.read_text(encoding="utf-8", errors="replace")
                except OSError:
                    continue
                for line in text.splitlines():
                    m = DECL_RE.match(line)
                    if m:
                        full = m.group(1)
                        names.add(full)
                        names.add(full.split(".")[-1])
    names |= EXTERNAL_COMMON
    return names, segments


def rust_universe(root: Path) -> set[str]:
    idents: set[str] = set()
    for p in tracked(root, "*.rs", "**/*.rs"):
        try:
            text = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for m in RUST_DECL_RE.finditer(text):
            idents.add(m.group(1))
        for m in RUST_LET_RE.finditer(text):
            idents.add(m.group(1))
        for line in text.splitlines():
            m = RUST_FIELD_RE.match(line)
            if m:
                idents.add(m.group(1))
            m = RUST_VARIANT_RE.match(line)
            if m:
                idents.add(m.group(1))
    # crate names, hyphens as underscores (`dregg-auth` is cited as `dregg_auth`)
    for c in tracked(root, "Cargo.toml", "*/Cargo.toml", "**/Cargo.toml"):
        try:
            for line in c.read_text(encoding="utf-8", errors="replace").splitlines():
                m = re.match(r'\s*name\s*=\s*"([A-Za-z0-9_-]+)"', line)
                if m:
                    idents.add(m.group(1).replace("-", "_"))
        except OSError:
            continue
    return idents


# ─── citation extraction ─────────────────────────────────────────────────────────────────

FILE_NAME_RE = re.compile(r"([A-Za-z0-9_\-./]+\.lean)::([A-Za-z_][A-Za-z0-9_'.]*)")
DOTTED_RE = re.compile(r"`([A-Z][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+)`")
BARE_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)`")

HISTORY_RE = re.compile(
    r"\b(deleted|DELETED|former(ly)?|used to|renamed|no longer|does not exist|doesn'?t exist|"
    r"not exist|retracted|RETRACTED|removed|superseded|was called|history|historical|"
    r"not yet|NOT YET|never authored|never landed|planned)\b"
)
LEAN_CONTEXT_RE = re.compile(r"\.lean\b|\bmetatheory\b|\bDregg2\b")


def bare_shape_ok(name: str) -> bool:
    if len(name) < 4:
        return False
    if name.isupper() or (name.replace("_", "").isupper()):
        return False  # SCREAMING_CASE = Rust const territory
    has_underscore = "_" in name.strip("_") and not name.startswith("_")
    has_internal_cap = any(c.isupper() for c in name[1:])
    return has_underscore or has_internal_cap


class Finding:
    def __init__(self, path: Path, line: int, kind: str, cited: str, detail: str):
        self.path, self.line, self.kind, self.cited, self.detail = (
            path,
            line,
            kind,
            cited,
            detail,
        )


def scan_file(
    path: Path,
    root: Path,
    lean_names: set[str],
    lean_segments: set[str],
    rust_idents: set[str],
    lean_files_by_suffix: dict[str, Path],
    listing: list[str] | None,
    watchlist: list[tuple[str, str]],
    bare_report: list[str] | None = None,
    relative_report: list[str] | None = None,
) -> list[Finding]:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []

    def rel(p: Path) -> str:
        try:
            return str(p.relative_to(root))
        except ValueError:
            return str(p)

    is_lean = path.suffix == ".lean"
    blocks = comment_blocks_lean(text) if is_lean else comment_blocks_rust(text)
    # the file's own CODE (comments stripped): a name used by the code beside the comment is
    # not a citation that can dangle — the compiler already checks it.
    comment_line_texts = {}
    for b in blocks:
        for ln, tx in b:
            comment_line_texts[ln] = tx
    code_lines = []
    for ln, full in enumerate(text.splitlines(), 1):
        c = comment_line_texts.get(ln)
        if c is None:
            code_lines.append(full)
        elif c and c in full:
            code_lines.append(full.replace(c, ""))
        else:
            code_lines.append("")
    code_text = "\n".join(code_lines)
    findings: list[Finding] = []
    for block in blocks:
        block_text = "\n".join(t for _, t in block)
        lean_ctx = is_lean or bool(LEAN_CONTEXT_RE.search(block_text))
        history_lines = {
            idx for idx, (_, t) in enumerate(block) if HISTORY_RE.search(t)
        }

        def in_history_window(idx: int) -> bool:
            return any(abs(idx - h) <= 5 for h in history_lines)

        for idx, (lineno, t) in enumerate(block):
            # form 1: File.lean::name
            for m in FILE_NAME_RE.finditer(t):
                fpath, name = m.group(1), m.group(2)
                short = name.split(".")[-1]
                target = lean_files_by_suffix.get(fpath) or lean_files_by_suffix.get(
                    fpath.lstrip("./")
                )
                if listing is not None:
                    listing.append(f"FILE::NAME {rel(path)}:{lineno} {fpath}::{name}")
                if in_history_window(idx):
                    continue
                if target is None:
                    findings.append(
                        Finding(path, lineno, "dead-file", f"{fpath}::{name}",
                                "no tracked .lean file ends with that path")
                    )
                    continue
                ttext = target.read_text(encoding="utf-8", errors="replace")
                if not re.search(rf"\b{re.escape(short)}\b", ttext):
                    findings.append(
                        Finding(path, lineno, "dead-name-in-file", f"{fpath}::{name}",
                                f"`{short}` does not occur in {rel(target)}")
                    )
            # form 2: dotted, FULLY-QUALIFIED repo-rooted (`Dregg2.…`) — the only dotted form
            # precise enough to gate. Relative citations (`MinaPhase2Chain.foo`, `Common.bar`)
            # collide with other trees and other ecosystems; they go to the --relative report.
            for m in DOTTED_RE.finditer(t):
                dotted = m.group(1)
                if re.search(r"\.(lean|olean|rs|md|json|toml|yml|yaml|sh|py|js|mjs|ts)$", dotted):
                    continue  # a FILE mention, not a declaration path (check-doc-refs territory)
                if not lean_ctx:
                    continue  # .rs comment that never names Lean — out of contract
                parts = dotted.split(".")
                first, last = parts[0], parts[-1]
                module_prefix = "/".join(parts[:-1]) + ".lean"
                mod_file = lean_files_by_suffix.get(module_prefix)
                if mod_file is not None and "metatheory/" not in str(mod_file):
                    mod_file = None  # a suffix collision with another tree (orb/, docs/) is not a match
                if first != "Dregg2":
                    if (relative_report is not None and mod_file is not None
                            and last not in lean_names and last not in lean_segments
                            and not in_history_window(idx)):
                        relative_report.append(f"{rel(path)}:{lineno} {dotted}")
                    continue
                if listing is not None:
                    listing.append(f"DOTTED    {rel(path)}:{lineno} {dotted}")
                if in_history_window(idx):
                    continue
                if last in lean_names or last in lean_segments:
                    continue
                if mod_file is not None:
                    findings.append(
                        Finding(path, lineno, "dead-dotted", dotted,
                                f"module {rel(mod_file)} exists but `{last}` is declared nowhere")
                    )
                else:
                    findings.append(
                        Finding(path, lineno, "dead-dotted", dotted,
                                f"`{last}` is declared in no tracked .lean file")
                    )
            # form 3 (REPORT-ONLY, --bare): bare backticked names in Lean-context blocks.
            # Measured 2026-08-08: comments here cite OCaml daemon functions, kimchi crate
            # methods, GraphQL fields and tactics bare — existence cannot be decided without
            # knowing the target ecosystem, so bare names NEVER gate. The curated watchlist
            # (.github/dead-lean-names.txt) is the precise instrument for known-dead names.
            if bare_report is not None and lean_ctx:
                for m in BARE_RE.finditer(t):
                    name = m.group(1)
                    if not bare_shape_ok(name):
                        continue
                    if in_history_window(idx):
                        continue
                    if name in lean_names or name in lean_segments or name in rust_idents:
                        continue
                    if re.search(rf"\b{re.escape(name)}\b", code_text):
                        continue
                    bare_report.append(f"{rel(path)}:{lineno} {name}")
            # form 4: the WATCHLIST — known-dead names narrated as live.
            for token, why in watchlist:
                for m in re.finditer(rf"(?<![\w'’]){re.escape(token)}(?![\w'])", t):
                    if in_history_window(idx):
                        continue
                    findings.append(
                        Finding(path, lineno, "watchlist", token, why)
                    )
    return findings


def load_watchlist(root: Path) -> list[tuple[str, str]]:
    wl_path = root / ".github" / "dead-lean-names.txt"
    rows: list[tuple[str, str]] = []
    if wl_path.is_file():
        for line in wl_path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split("\t", 1)
            rows.append((parts[0].strip(), parts[1].strip() if len(parts) > 1 else "on the dead-names watchlist"))
    return rows


def run_scan(root: Path, listing: list[str] | None = None,
             extra_files: list[Path] | None = None,
             bare_report: list[str] | None = None,
             relative_report: list[str] | None = None) -> tuple[list[Finding], int]:
    lean_names, lean_segments = lean_universe(root)
    rust_idents = rust_universe(root)
    if len(lean_names) < 5000:
        print(
            f"LEAN-CITATION SCAN DEGENERATE: only {len(lean_names)} Lean declarations found "
            f"(corpus is tens of thousands). The universe scan matched almost nothing; a green "
            f"here proves nothing.",
            file=sys.stderr,
        )
        sys.exit(3)
    lean_files = [
        p
        for p in tracked(root, "*.lean", "**/*.lean")
        if "/.lake/" not in str(p) and not str(p).startswith(str(root / "headver"))
    ]
    by_suffix: dict[str, Path] = {}
    for p in lean_files:
        rel = str(p.relative_to(root))
        parts = rel.split("/")
        for i in range(len(parts)):
            by_suffix.setdefault("/".join(parts[i:]), p)
    files = tracked(root, "*.rs", "**/*.rs", "*.lean", "**/*.lean")
    files = [p for p in files if "/.lake/" not in str(p)]
    if extra_files:
        files = files + extra_files
    watchlist = load_watchlist(root)
    findings: list[Finding] = []
    my_listing: list[str] = [] if listing is None else listing
    for p in files:
        findings.extend(
            scan_file(p, root, lean_names, lean_segments, rust_idents, by_suffix,
                      my_listing, watchlist, bare_report, relative_report)
        )
    candidates = len(my_listing)
    return findings, candidates


# ─── self-test: the gate MUST be able to go red ─────────────────────────────────────────


def self_test(root: Path) -> int:
    with tempfile.TemporaryDirectory() as td:
        plant = Path(td) / "planted_citation.rs"
        plant.write_text(
            "//! Verified against the Lean theorem\n"
            "//! `Dregg2.Consensus.this_theorem_never_existed_9f3q` and the\n"
            "//! Lean spec `Dregg2/Consensus/Nowhere9f3q.lean::ghost_9f3q`; the cursor is guarded\n"
            "//! by the `FinalizedRegionStable` hypothesis (a WATCHLIST name narrated as live).\n"
            "//! Also cites the REAL `Dregg2.Consensus.OnDemandFeasibility.Commute` which must NOT fire.\n"
            "fn f() {}\n"
            "//! The former `stableCheck` was deleted — a history-marked mention, must NOT fire.\n"
            "fn g() {}\n"
            "//! And a bare Lean-context orphan `neverEverDefined_9f3q` for the --bare report\n"
            "//! (metatheory context marker).\n"
            "fn h() {}\n"
        )
        # assert the plant LANDED before reading the verdict (a falsifier that stopped
        # falsifying is worse than none)
        planted_text = plant.read_text()
        for needle in ("this_theorem_never_existed_9f3q", "FinalizedRegionStable",
                       "ghost_9f3q", "neverEverDefined_9f3q"):
            if needle not in planted_text:
                print(f"SELF-TEST BROKEN: plant did not land ({needle} missing)", file=sys.stderr)
                return 1
        bare_report: list[str] = []
        findings, _ = run_scan(root, extra_files=[plant], bare_report=bare_report)
        mine = [f for f in findings if f.path == plant]
        kinds = {f.kind for f in mine}
        cited = {f.cited for f in mine}
        ok = True
        if "Dregg2.Consensus.this_theorem_never_existed_9f3q" not in cited:
            print("SELF-TEST RED-PROOF FAILED: dotted dead citation did not fire", file=sys.stderr)
            ok = False
        if not any(c.startswith("Dregg2/Consensus/Nowhere9f3q.lean::") for c in cited):
            print("SELF-TEST RED-PROOF FAILED: file::name dead citation did not fire", file=sys.stderr)
            ok = False
        if not any(f.kind == "watchlist" and f.cited == "FinalizedRegionStable" for f in mine):
            print("SELF-TEST RED-PROOF FAILED: watchlist name narrated as live did not fire", file=sys.stderr)
            ok = False
        if any(f.kind == "watchlist" and f.cited == "stableCheck" for f in mine):
            print("SELF-TEST FALSE-POSITIVE: a history-marked watchlist mention fired", file=sys.stderr)
            ok = False
        if any("Commute" == c.split(".")[-1] for c in cited):
            print("SELF-TEST FALSE-POSITIVE: the REAL `Commute` citation fired", file=sys.stderr)
            ok = False
        if not any("neverEverDefined_9f3q" in row for row in bare_report):
            print("SELF-TEST REPORT-PROOF FAILED: --bare channel missed the bare orphan", file=sys.stderr)
            ok = False
        if ok:
            print(
                f"check-lean-citations --self-test: OK — 3 planted dead citations fired "
                f"({sorted(kinds)}), the history-marked and REAL mentions did not, and the "
                f"--bare report channel saw its orphan."
            )
            return 0
        return 1


# ─── main ────────────────────────────────────────────────────────────────────────────────


def main() -> int:
    root = repo_root()
    args = sys.argv[1:]
    if "--self-test" in args:
        return self_test(root)
    listing: list[str] | None = [] if "--list" in args else None
    bare_report: list[str] | None = [] if "--bare" in args else None
    relative_report: list[str] | None = [] if "--relative" in args else None
    findings, candidates = run_scan(root, listing=listing, bare_report=bare_report,
                                    relative_report=relative_report)
    if relative_report is not None:
        print("# --relative report (NOT part of the verdict): relative dotted citations whose")
        print("# metatheory module exists but whose last segment resolves nowhere")
        for row in relative_report:
            print(f"#   {row}")
    if bare_report is not None:
        print("# --bare report (NOT part of the verdict): unresolvable bare backticked names")
        for row in bare_report:
            print(f"#   {row}")
    if listing is not None:
        for row in listing:
            print(row)
        print(f"# {len(listing)} citation candidate(s) scanned", file=sys.stderr)
    if candidates < 50:
        print(
            f"LEAN-CITATION SCAN DEGENERATE: only {candidates} citation candidates repo-wide "
            f"(hundreds expected). The comment scan matched almost nothing; a green here proves "
            f"nothing.",
            file=sys.stderr,
        )
        return 3
    if not findings:
        print(
            f"check-lean-citations: OK — {candidates} cited name(s) scanned, none dead."
        )
        return 0
    print(
        f"\n\033[31mDEAD LEAN CITATION\033[0m: {len(findings)} comment(s) cite a Lean name "
        f"that does not exist.\n",
        file=sys.stderr,
    )
    for f in sorted(findings, key=lambda f: (str(f.path), f.line)):
        try:
            shown = f.path.relative_to(root)
        except ValueError:
            shown = f.path
        print(
            f"  {shown}:{f.line}  [{f.kind}]  {f.cited}\n"
            f"      {f.detail}",
            file=sys.stderr,
        )
    print(
        "\nEither the named object was deleted/renamed (fix the comment to the live name, or"
        "\nnarrate the history explicitly — the words 'deleted'/'former'/'renamed' near the"
        "\nmention silence this gate), or the comment claims a check that was never built —"
        "\nin which case the finding is the missing check, not the wording.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
