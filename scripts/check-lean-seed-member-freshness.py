#!/usr/bin/env python3
"""check-lean-seed-member-freshness.py — is every object IN the seed archive newer than the
Lean it claims to be the compilation of?

═══ THE WOUND THIS CLOSES (measured 2026-08-07) ════════════════════════════════════════════
`dregg-lean-ffi::deployed_constraint_probe` printed `8 passed` every day from 2026-07-30 to
08-06 with SIX of its eight assertions false. The admission wire's header grew from 6 tokens
to 17; the probe's builder still emitted six; the evaluator refused every wire and
`DeployedConstraint.admitsWire` renders a refusal-to-parse as `"1"`, the same string as
`ConstraintViolated`. It went green because the archive on the box carried a **2026-07-25**
`Dregg2_Exec_DeployedConstraint.o` — a six-token evaluator agreeing with a six-token builder.
Two stale things agreeing reads exactly like correctness.

═══ WHY THE THREE EXISTING GATES CANNOT SEE IT ═════════════════════════════════════════════
  * `dregg-lean-ffi/build.rs`'s PROVENANCE DOWNGRADE is whole-archive and CONTROL-FLOW-shaped:
    it fires when the Lean build did not run. The Lean build ran. The `.c` was current. The
    splice ran. ONE object was old, and every gate's question was answered truthfully.
  * `scripts/check-lean-seed-closure.sh` asks whether a module HAS A MEMBER. It had one.
  * `scripts/check-lean-seed-freshness.sh` compares the pin's `DREGG_CLOSURE_HASH` — a fact
    about which PUBLISHED ASSET is reachable by name, not about any object's age.
  * `dregg-lean-ffi/tests/linked_archive_freshness.rs` DOES ask the per-member question, but
    only of the archive a test process happened to LINK (`DREGG_LEAN_LINKED_ARCHIVE`). The
    seed at `dregg-lean-ffi/libdregg_lean.a` is the artifact that gets fetched, rsync'd,
    inherited across checkouts and copied into every new `OUT_DIR` — and no process links it
    directly, so nothing asked. Measured at that moment: the working archive was CLEAN
    (0 of 323); the SEED was **56 stale of 188**.

═══ THE COMPARISON, AND WHY IT IS STRICTLY STRONGER THAN THE RUST TEST'S ═══════════════════
For every archive member that maps to an in-tree Lean module, the member's `ar` header mtime
must not predate

        max( mtime(metatheory/<Mod>.lean) , mtime(metatheory/.lake/build/ir/<Mod>.c) )

The `.lean` leg is the same question `linked_archive_freshness.rs` asks, unchanged — this is
not a widened comparison. The `.c` leg only ever makes it FIRE MORE: lake regenerates a
module's emitted C when its compiled image changes, which happens for reasons the module's own
source file cannot show — an import changed, an instance resolved differently, a `@[inline]`
upstream moved. A member newer than its `.lean` and older than its `.c` is an object that is
not the compilation of the C the tree now emits, and the `.lean`-only comparison calls it
fresh.

Timestamps come from the `ar` HEADERS (exact epoch seconds), not from `ar tv`'s rendering
(local time, minute resolution, no seconds field). That removes the timezone parse and the
minute rounding entirely; the slack below survives only as an ordering allowance.

⚠ DO NOT RAISE THE SLACK TO CLEAR A FINDING. If a member is legitimately allowed to lag it
goes in an allowlist with a REASON PER ENTRY, and this checkout has none — see ALLOWLIST.

═══ WHAT THIS IS A STATEMENT ABOUT: ONE BOX'S CLOCK ════════════════════════════════════════
Every input here — the archive's member headers, the `.lean` mtimes, the emitted `.c` mtimes —
is a local filesystem timestamp. That makes this exactly the right instrument for the failure
it was built for: an archive that was CORRECT WHEN IT LANDED and went stale in place while the
tree moved around it, everything happening in one clock frame on one machine.

It is the WRONG instrument for a freshly cloned or freshly fetched tree, and the difference is
not a nuance. `git clone` stamps every `.lean` at clone time, so any published seed — which was
necessarily built earlier — reads as entirely stale. `scripts/fetch-lean-seed.sh` therefore does
NOT run this check and carries a note saying why: for a downloaded asset the sound instrument is
the CONTENT KEY (the asset name is a hash of platform + toolchain + mathlib rev + the closure
SOURCES), so a seed whose Lean does not match this checkout is not reachable by name at all.

Consequence, stated rather than hidden: on a box that cloned and then `lake build`-ed after its
seed was cut, this reports every member. That is an OVER-report, not a false design — the remedy
is the same 90-second `dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh` that any such box wants
anyway, and it clears the row for real rather than by widening anything. The comparison errs
toward reporting; it cannot miss a member that is genuinely behind.

═══ A GATE WHOSE INPUT IS ABSENT IS A FAULT ════════════════════════════════════════════════
Exit 2 (not 0) for: no archive, no metatheory tree, an archive this cannot parse, fewer than
MIN_MEMBERS members, fewer than MIN_RESOLVED members mapping to a source, or an archive whose
member mtimes are all zero (`ar -D`/deterministic mode strips provenance — such an archive
carries NO evidence of its own age and must never read as fresh).

Usage:  scripts/check-lean-seed-member-freshness.py [ARCHIVE] [--self-test]
        (ARCHIVE defaults to dregg-lean-ffi/libdregg_lean.a, the seed)
Exit:   0 every member is at least as new as its Lean · 1 at least one is older · 2 cannot measure
"""

from __future__ import annotations

import datetime
import os
import sys
import tempfile
from pathlib import Path

# A reader that harvests nothing must not read as clean. The `Dregg2.FFI` boundary closure is
# ~334 in-tree modules; even the short 2026-07-25 seed carried 198 that resolve. Anything under
# these floors means the archive reader or the source mapping broke, not that the tree shrank.
MIN_MEMBERS = 200
MIN_RESOLVED = 100

# Ordering allowance, in seconds. Reading the `ar` header directly gives exact epoch seconds, so
# there is no minute rounding left to absorb; what remains is that a splice writes an object and
# packs it in a sequence whose steps are not atomic. Two minutes covers that and nothing else.
# This is NOT a staleness budget. Raising it to clear a finding is the move this file exists to
# make impossible.
SLACK_SECS = 120

# ⚑ ALLOWLIST — empty, and an entry costs a REASON, not a flag.
# The rule (CLAUDE.md): a member that is legitimately allowed to lag its source is an allowlist
# row with a written reason, never a widened comparison. There is no such member in this tree:
# the seed is re-spliced from the current IR and every in-tree object is stamped at splice time.
# Format: "Dregg2_Some_Module.o": "why this one may lag, and what would retire the entry".
ALLOWLIST: dict[str, str] = {}

IN_TREE_ROOTS = ("Dregg2", "Metatheory", "Polis")


# ── the archive reader ───────────────────────────────────────────────────────────────────────
class ArchiveError(Exception):
    """The archive could not be read. Always a FAULT, never a quiet pass."""


def read_members(path: Path) -> list[tuple[str, int]]:
    """Every member of a Unix `ar` archive as (name, mtime-epoch-seconds).

    Handles both long-name conventions, because both are in play: BSD/Darwin `ar` writes
    `#1/<len>` and prepends the name to the member data; GNU/binutils writes `/<offset>` into a
    `//` string table. A reader that understands only one silently drops every long member on
    the other platform — and dropping members is how a freshness check reports zero findings.
    """
    data = path.read_bytes()
    if not data.startswith(b"!<arch>\n"):
        raise ArchiveError(f"{path}: no `!<arch>` magic — not an ar archive")
    pos = 8
    long_names = b""
    out: list[tuple[str, int]] = []
    while pos + 60 <= len(data):
        hdr = data[pos : pos + 60]
        if hdr[58:60] != b"`\n":
            raise ArchiveError(
                f"{path}: member header at byte {pos} has no `\\n terminator — the listing is "
                f"unreadable from here, and an unreadable listing finds nothing stale"
            )
        raw_name = hdr[0:16].decode("ascii", "replace")
        mtime_s = hdr[16:28].decode("ascii", "replace").strip()
        size_s = hdr[48:58].decode("ascii", "replace").strip()
        try:
            size = int(size_s)
        except ValueError as e:
            raise ArchiveError(f"{path}: member at {pos} has unparseable size {size_s!r}") from e
        mtime = int(mtime_s) if mtime_s.lstrip("-").isdigit() else 0
        body = pos + 60
        consumed = 0
        name = raw_name.rstrip()
        if name.startswith("#1/"):  # BSD long name, stored in the first `n` bytes of the data
            n = int(name[3:])
            name = data[body : body + n].split(b"\0")[0].decode("ascii", "replace")
            consumed = n
        elif name == "//":  # GNU string table — remember it, it is not a real member
            long_names = data[body : body + size]
            pos = body + size + (size & 1)
            continue
        elif name.startswith("/") and name[1:].isdigit():  # GNU long name, offset into `//`
            off = int(name[1:])
            end = long_names.find(b"/\n", off)
            if end < 0:
                end = long_names.find(b"\0", off)
            name = long_names[off : end if end >= 0 else None].decode("ascii", "replace")
        else:
            name = name.rstrip("/")  # GNU pads short names with a trailing `/`
        if name not in ("__.SYMDEF", "__.SYMDEF SORTED", "/", "/SYM64/"):
            out.append((name, mtime))
        pos = body + size + (size & 1)
    if not out:
        raise ArchiveError(f"{path}: parsed ZERO members")
    return out


# ── the source mapping ───────────────────────────────────────────────────────────────────────
def source_index(meta: Path) -> dict[str, Path]:
    """Every in-tree `*.lean` keyed by the FLATTENED object name the splice produces.

    `Dregg2/Exec/DeployedConstraint.lean` -> `Dregg2_Exec_DeployedConstraint.o`. Built by walking
    the real tree, so a module whose own name contains `_` maps correctly; inverting the
    flattening by splitting on `_` would map it to a path that does not exist, the member would
    resolve to nothing, and the gate would find it fresh by construction.
    """
    out: dict[str, Path] = {}
    for root in IN_TREE_ROOTS:
        base = meta / root
        if not base.is_dir():
            continue
        for p in base.rglob("*.lean"):
            if ".lake" in p.parts:
                continue
            rel = p.relative_to(meta).with_suffix("")
            out["_".join(rel.parts) + ".o"] = p
    return out


def ir_path(meta: Path, src: Path) -> Path:
    """The emitted C for a module: `metatheory/.lake/build/ir/<same relative path>.c`."""
    return meta / ".lake" / "build" / "ir" / src.relative_to(meta).with_suffix(".c")


def iso(t: float) -> str:
    return datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ── the comparison ───────────────────────────────────────────────────────────────────────────
def stale_members(
    members: list[tuple[str, int]], sources: dict[str, Path], meta: Path
) -> tuple[int, list[tuple[str, int, str, float]], list[str]]:
    """(resolved, findings, allowed).

    `resolved` is how many members mapped to a live `.lean` — the caller applies a floor to it,
    so a broken mapping cannot report "nothing stale". A finding is
    (member name, member mtime, which input is newer, that input's mtime).
    """
    resolved = 0
    findings: list[tuple[str, int, str, float]] = []
    allowed: list[str] = []
    for name, mtime in members:
        src = sources.get(name)
        if src is None:
            # A member whose module is gone from the tree is not a staleness finding (the splice
            # prunes those) and is not silently ignored either — the `resolved` floor fails the
            # run if the mapping stops resolving in general.
            continue
        resolved += 1
        newest_label, newest_t = f"{src.relative_to(meta)}", src.stat().st_mtime
        c = ir_path(meta, src)
        if c.exists() and c.stat().st_mtime > newest_t:
            newest_label, newest_t = f".lake/build/ir/{c.relative_to(meta / '.lake/build/ir')}", c.stat().st_mtime
        if newest_t > mtime + SLACK_SECS:
            if name in ALLOWLIST:
                allowed.append(name)
            else:
                findings.append((name, mtime, newest_label, newest_t))
    findings.sort(key=lambda f: -f[3])
    return resolved, findings, allowed


def check(archive: Path, meta: Path) -> int:
    if not archive.is_file():
        print(
            f"check-lean-seed-member-freshness: no archive at {archive}.\n"
            f"  A gate whose input is absent is a FAULT, not a pass — with no seed on this box every\n"
            f"  test behind `if !<x>_available() {{ SKIP }}` reports ok having asserted nothing.\n"
            f"  Install one:  scripts/fetch-lean-seed.sh   (or ./scripts/bootstrap.sh)",
            file=sys.stderr,
        )
        return 2
    if not (meta / "Dregg2" / "FFI.lean").is_file():
        print(
            f"check-lean-seed-member-freshness: no boundary module at {meta}/Dregg2/FFI.lean — there\n"
            f"  is nothing to compare the archive's objects against, which is a FAULT, not `no drift`.",
            file=sys.stderr,
        )
        return 2

    try:
        members = read_members(archive)
    except ArchiveError as e:
        print(f"check-lean-seed-member-freshness: {e}\n  A broken READER reports zero findings.", file=sys.stderr)
        return 2

    if len(members) < MIN_MEMBERS:
        print(
            f"check-lean-seed-member-freshness: parsed only {len(members)} members of {archive} "
            f"(floor {MIN_MEMBERS}).\n  A reader that harvests nothing reads as clean; this floor is why it cannot.",
            file=sys.stderr,
        )
        return 2

    if all(mt == 0 for _, mt in members):
        print(
            f"check-lean-seed-member-freshness: every member of {archive} carries mtime 0.\n"
            f"  This archive was packed in DETERMINISTIC mode (`ar -D` / `ar rcsD`), which strips the\n"
            f"  per-member timestamps. It therefore carries no evidence of its own age, and an archive\n"
            f"  with no evidence must not read as fresh. Re-pack without -D, or record provenance some\n"
            f"  other way before this gate can speak for it.",
            file=sys.stderr,
        )
        return 2

    sources = source_index(meta)
    if len(sources) < MIN_RESOLVED:
        print(
            f"check-lean-seed-member-freshness: indexed only {len(sources)} in-tree .lean sources "
            f"under {meta} — the source walk is broken, not the tree.",
            file=sys.stderr,
        )
        return 2

    resolved, findings, allowed = stale_members(members, sources, meta)
    if resolved < MIN_RESOLVED:
        print(
            f"check-lean-seed-member-freshness: only {resolved} of {len(members)} members mapped to a\n"
            f"  .lean source (floor {MIN_RESOLVED}) — the NAME MAPPING is broken, and a broken mapping\n"
            f"  finds nothing stale by construction.",
            file=sys.stderr,
        )
        return 2

    print(f"archive          {archive}")
    print(f"members          {len(members)}  ({resolved} map to an in-tree Lean module)")
    print(f"comparison       member mtime >= max(mtime(.lean), mtime(.lake/build/ir/*.c)) - {SLACK_SECS}s")
    print(f"stale members    {len(findings)} / {resolved}" + (f"   (+{len(allowed)} allowlisted)" if allowed else ""))
    for name in allowed:
        print(f"    ALLOWED  {name} — {ALLOWLIST[name]}")

    if not findings:
        print()
        print("VERDICT: every object in this archive is at least as new as the Lean it was compiled")
        print("  from. A verified gate deciding against it is deciding against THIS tree's Lean.")
        return 0

    print()
    print(f"⛔ {len(findings)} of {resolved} objects in {archive} are OLDER than the Lean they claim to be:")
    for name, mtime, label, newest in findings[:40]:
        print(f"    {name}")
        print(f"        member {iso(mtime)}  <  {label} {iso(newest)}")
    if len(findings) > 40:
        print(f"    … and {len(findings) - 40} more")
    print()
    print("WHAT THIS MEANS, and it is not a build-hygiene nit: this archive is what a fresh")
    print("  `OUT_DIR` is seeded FROM, so every one of those objects is the decision procedure a")
    print("  verified gate runs until something happens to re-splice it. A green from such a gate is")
    print("  a claim about the OLDER Lean — which is exactly how six `deployed_constraint_probe`")
    print("  assertions reported `ok` for a week (2026-07-30 → 08-06).")
    print()
    print("FIX: re-splice the seed's in-tree slice from the current IR:")
    print("      dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh")
    print("  or install a key-matched published one:  scripts/fetch-lean-seed.sh --force")
    print("  Do NOT raise SLACK_SECS. It is an ordering allowance, not a staleness budget, and a")
    print("  member that may legitimately lag needs an ALLOWLIST entry with a written reason.")
    return 1


# ── the red proof ────────────────────────────────────────────────────────────────────────────
def self_test() -> int:
    """⚑ NOT OPTIONAL: the headline is a NEGATIVE assertion, and a negative assertion passes just
    as happily when its own reader is broken. Every leg builds its subject CONSTRUCTIVELY and
    asserts the mutation is present BEFORE reading the verdict — a mutation that quietly stopped
    being applied is how a falsifier stops falsifying while staying green.

    Everything runs in this process's own temp dir. The shared tree is never touched, so no window
    exists in which a sibling lane builds against a disarmed guard.
    """
    fails: list[str] = []

    def ok(cond: bool, what: str) -> None:
        print(("  ok   " if cond else "  RED  ") + what)
        if not cond:
            fails.append(what)

    def ar_write(path: Path, entries: list[tuple[str, int, bytes]], style: str = "bsd") -> None:
        """Synthesize an ar archive. Hand-built on purpose: it needs no `ar`, no C compiler and no
        `touch`, and it lets a leg set a member's mtime to an EXACT second, which is the one input
        this gate reads."""
        buf = bytearray(b"!<arch>\n")
        table = b""
        if style == "gnu":
            for name, _, _ in entries:
                if len(name) > 15:
                    table += name.encode() + b"/\n"
            if table:
                hdr = b"//" + b" " * 14 + b" " * 12 + b" " * 6 + b" " * 6 + b" " * 8
                hdr += f"{len(table)}".ljust(10).encode() + b"`\n"
                buf += hdr + table + (b"\n" if len(table) & 1 else b"")
        for name, mtime, body in entries:
            if style == "bsd" and len(name) > 15:
                payload = name.encode() + b"\0" * ((4 - len(name) % 4) % 4)
                field = f"#1/{len(payload)}"
                size = len(payload) + len(body)
                data = payload + body
            elif style == "gnu" and len(name) > 15:
                field = "/" + str(table.find(name.encode() + b"/\n"))
                size, data = len(body), body
            else:
                field = name + ("/" if style == "gnu" else "")
                size, data = len(body), body
            hdr = field.ljust(16).encode()
            hdr += str(mtime).ljust(12).encode() + b"0".ljust(6) + b"0".ljust(6)
            hdr += b"100644".ljust(8) + str(size).ljust(10).encode() + b"`\n"
            buf += hdr + data + (b"\n" if size & 1 else b"")
        path.write_bytes(bytes(buf))

    NOW = int(datetime.datetime.now(datetime.timezone.utc).timestamp())
    JUL25 = 1784962929  # 2026-07-25T07:02:09Z — the real stamp on the seed that hid the six reds

    with tempfile.TemporaryDirectory(prefix="dregg-member-freshness-redproof-") as td:
        tmp = Path(td)

        # 1 · THE READER, both long-name conventions. Darwin writes `#1/N`, binutils writes a `//`
        #     table; a reader that knows one drops every long member on the other platform, and a
        #     dropped member is a finding that can never be made.
        print("leg 1 — the ar header reader (BSD `#1/N` and GNU `//` long names)")
        for style in ("bsd", "gnu"):
            a = tmp / f"reader-{style}.a"
            ar_write(
                a,
                [
                    ("Dregg2_Exec_DeployedConstraint.o", JUL25, b"\x01" * 32),
                    ("Dregg2_FFI.o", NOW, b"\x02" * 33),
                    ("short.o", NOW, b"\x03" * 8),
                ],
                style=style,
            )
            got = dict(read_members(a))
            ok(len(got) == 3, f"{style}: all three members read back (got {len(got)}: {sorted(got)})")
            ok(
                got.get("Dregg2_Exec_DeployedConstraint.o") == JUL25,
                f"{style}: the long member's EXACT epoch second survives ({got.get('Dregg2_Exec_DeployedConstraint.o')} == {JUL25})",
            )
            ok(got.get("Dregg2_FFI.o") == NOW, f"{style}: a second long member reads its own distinct mtime")

        # 2 · THE PLANT. A real scratch source tree + an archive whose member is stamped in the
        #     past. The mutation is ASSERTED PRESENT before any verdict is read.
        print("leg 2 — a planted stale member is REPORTED")
        meta = tmp / "metatheory"
        (meta / "Dregg2" / "Exec").mkdir(parents=True)
        (meta / "Dregg2" / "FFI.lean").write_text("-- red-proof boundary\n")
        # A module name containing `_`, on purpose: it is the case a split-on-`_` inverse of the
        # flattened object name gets wrong, and getting it wrong finds nothing stale.
        for n in ("DeployedConstraint.lean", "Deployed_Constraint.lean"):
            (meta / "Dregg2" / "Exec" / n).write_text("-- red-proof fixture\n")
        srcs = source_index(meta)
        ok(len(srcs) == 3, f"the source walk indexed the scratch tree ({sorted(srcs)})")
        ok(
            "Dregg2_Exec_Deployed_Constraint.o" in srcs,
            "a module name containing `_` still maps (the split-on-`_` trap)",
        )
        planted = [
            ("Dregg2_Exec_DeployedConstraint.o", JUL25, b"\x01" * 16),
            ("Dregg2_Exec_Deployed_Constraint.o", JUL25, b"\x01" * 16),
            ("Dregg2_FFI.o", NOW, b"\x02" * 16),
        ]
        a = tmp / "planted.a"
        ar_write(a, planted)
        back = read_members(a)
        by_name = dict(back)
        ok(
            by_name.get("Dregg2_Exec_DeployedConstraint.o") == JUL25 and by_name.get("Dregg2_FFI.o") == NOW,
            "THE MUTATION IS PRESENT: one member stamped 2026-07-25, one stamped now",
        )
        resolved, findings, _ = stale_members(back, srcs, meta)
        ok(resolved == 3, f"all three members mapped to a source (resolved={resolved})")
        ok(len(findings) == 2, f"BOTH planted members are reported stale (findings={[f[0] for f in findings]})")
        ok(
            any("2026-07-25" in iso(f[1]) for f in findings),
            "a finding prints the member's own timestamp, so a reader can act on it",
        )

        # 3 · THE HEALTHY DIRECTION STAYS QUIET. A gate that reports a fresh object is a wall.
        print("leg 3 — an object NEWER than its source is not a finding")
        a = tmp / "fresh.a"
        ar_write(a, [(n, NOW + 86400, b"\x01" * 16) for n, _, _ in planted])
        _, findings, _ = stale_members(read_members(a), srcs, meta)
        ok(not findings, f"no findings for an archive newer than the tree (got {[f[0] for f in findings]})")

        # 4 · THE `.c` LEG — the direction the `.lean`-only comparison MISSES. Source untouched,
        #     emitted C regenerated (an import changed): the object is no longer the compilation of
        #     the C this tree emits, and it MUST be a finding.
        print("leg 4 — a member newer than its .lean but older than its emitted .c is STALE")
        irdir = meta / ".lake" / "build" / "ir" / "Dregg2" / "Exec"
        irdir.mkdir(parents=True)
        old_src = NOW - 30 * 86400
        for n in ("DeployedConstraint.lean", "Deployed_Constraint.lean"):
            os.utime(meta / "Dregg2" / "Exec" / n, (old_src, old_src))
        os.utime(meta / "Dregg2" / "FFI.lean", (old_src, old_src))
        member_t = NOW - 15 * 86400  # NEWER than every .lean …
        a = tmp / "irstale.a"
        ar_write(a, [(n, member_t, b"\x01" * 16) for n, _, _ in planted])
        srcs = source_index(meta)
        _, findings, _ = stale_members(read_members(a), srcs, meta)
        ok(not findings, "…with no .c present and every .lean older, the member is fresh (control)")
        (irdir / "DeployedConstraint.c").write_text("/* regenerated */\n")  # … and NEWER than this .c
        ok((irdir / "DeployedConstraint.c").stat().st_mtime > member_t, "THE MUTATION IS PRESENT: the .c is newer than the member")
        _, findings, _ = stale_members(read_members(a), srcs, meta)
        ok(
            [f[0] for f in findings] == ["Dregg2_Exec_DeployedConstraint.o"],
            f"exactly the module whose .c moved is reported (got {[f[0] for f in findings]})",
        )
        ok(any(".lake/build/ir" in f[2] for f in findings), "the finding NAMES the .c as the newer input, not the .lean")

        # 5 · THE SLACK IS AN ORDERING ALLOWANCE, NOT A BUDGET.
        print("leg 5 — the slack forgives seconds, never an hour")
        os.utime(meta / "Dregg2" / "Exec" / "DeployedConstraint.lean", (NOW, NOW))
        (irdir / "DeployedConstraint.c").unlink()
        for delta, want_finding in ((SLACK_SECS - 10, False), (3600, True)):
            a = tmp / f"slack-{delta}.a"
            ar_write(a, [("Dregg2_Exec_DeployedConstraint.o", NOW - delta, b"\x01" * 16)])
            _, findings, _ = stale_members(read_members(a), source_index(meta), meta)
            ok(
                bool(findings) == want_finding,
                f"a member {delta}s behind its source is {'a finding' if want_finding else 'inside the allowance'}",
            )

        # 6 · A LISTING THE READER CANNOT PARSE MUST RAISE, so the caller FAULTS rather than
        #     printing a clean run over zero members.
        print("leg 6 — an unreadable archive is a FAULT, never a clean run")
        bad = tmp / "garbage.a"
        bad.write_bytes(b"!<arch>\n" + b"x" * 200)
        try:
            read_members(bad)
            ok(False, "a corrupt member header raises ArchiveError")
        except ArchiveError:
            ok(True, "a corrupt member header raises ArchiveError")
        empty = tmp / "empty.a"
        empty.write_bytes(b"not an archive at all")
        try:
            read_members(empty)
            ok(False, "a non-archive raises ArchiveError")
        except ArchiveError:
            ok(True, "a non-archive raises ArchiveError")

        # 7 · DETERMINISTIC MODE. `ar -D` zeroes every member mtime; such an archive carries no
        #     evidence of its own age and must FAULT rather than read as fresh.
        print("leg 7 — an `ar -D` archive (all mtimes 0) faults instead of reading fresh")
        det = tmp / "deterministic.a"
        ar_write(det, [(f"Dregg2_M{i}.o", 0, b"\x01" * 16) for i in range(MIN_MEMBERS + 5)])
        back = read_members(det)
        ok(all(mt == 0 for _, mt in back), "THE MUTATION IS PRESENT: every member reads mtime 0")
        rc = check(det, meta)
        ok(rc == 2, f"check() FAULTS (exit 2) on a timestamp-stripped archive (got {rc})")

        # 8 · THE FLOORS. A short archive, and a mapping that resolves nothing, both FAULT.
        print("leg 8 — the member and mapping floors fault rather than report clean")
        short = tmp / "short.a"
        ar_write(short, [("Dregg2_FFI.o", NOW, b"\x01" * 16)])
        ok(check(short, meta) == 2, "an archive under MIN_MEMBERS faults")
        wide = tmp / "wide.a"
        ar_write(wide, [(f"Mathlib_M{i}.o", NOW, b"\x01" * 16) for i in range(MIN_MEMBERS + 5)])
        ok(check(wide, meta) == 2, "an archive whose members map to NO source faults (broken mapping)")

    # 9 · THE REAL READER ON A REAL ARCHIVE. Legs 1-8 run on archives this file wrote; if the
    #     synthesizer and the reader share a misunderstanding they agree with each other forever.
    #     This one reads whatever `ar` actually produced on this box.
    print("leg 9 — the reader against a REAL archive on this box")
    real = Path("dregg-lean-ffi/libdregg_lean.a")
    if real.is_file():
        got = read_members(real)
        ok(len(got) >= MIN_MEMBERS, f"the real seed reads back {len(got)} members")
        ok(
            sum(1 for n, _ in got if n.startswith("Dregg2_")) > 100,
            "and over a hundred of them are Dregg2 objects (the mapping's subject)",
        )
        ok(any(mt > 1_700_000_000 for _, mt in got), "with plausible epoch-second timestamps")
    else:
        ok(False, f"no real archive at {real} to read — this leg cannot run, and a leg that cannot run is not a pass")

    print()
    if fails:
        print(f"SELF-TEST RED — {len(fails)} leg(s) failed:")
        for f in fails:
            print(f"    {f}")
        return 1
    print("SELF-TEST GREEN — the reader parses both ar dialects, the mapping survives a `_` in a")
    print("  module name, a planted 2026-07-25 member IS reported, the .c leg fires where the .lean")
    print("  leg cannot, the slack is not a budget, and every absent/unreadable input FAULTS.")
    return 0


def main(argv: list[str]) -> int:
    root = Path(__file__).resolve().parent.parent
    os.chdir(root)
    args = [a for a in argv[1:]]
    if "--self-test" in args:
        return self_test()
    archive = Path(args[0]) if args else Path("dregg-lean-ffi/libdregg_lean.a")
    meta = Path(os.environ.get("DREGG_METATHEORY_DIR", "metatheory"))
    return check(archive, meta)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
