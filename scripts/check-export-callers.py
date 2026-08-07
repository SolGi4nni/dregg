#!/usr/bin/env python3
"""check-export-callers.py — a verified Lean gate that SHIPS in the archive and that NO Rust file
ever names.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
`@[export foo]` on a Lean decision, plus an `import` line in `metatheory/Dregg2/FFI.lean`, is
enough to put `foo` in `libdregg_lean.a`. Nothing else is required, and in particular **no caller
is required**. So a gate can be authored, proved, `#assert_axioms`-ed, documented as "THE GATE",
compiled into every binary the node links — and decide nothing, forever, silently.

There is no diagnostic for this. It is not dead code (Lean emitted it and the linker kept it), it
is not an unused import, it breaks no build, and the module's own theorems stay green because they
are theorems about a function, not about a call. `check-dark-modules.py` catches a `.rs` file
rustc never opens; this catches a Lean DECISION rustc never asks.

Measured 2026-08-03, by a census of `dregg_mina_*` exports against their Rust bindings:

    lc_verify 4 · better_tip 4 · proof_chain_ok 3 · state_hash_word_ok 3 · checkpoint_advance 3
    head_advance 3 · wrap_challenges 3 · wrap_shape_ok 3 · account_state_ok 2 · wrap_ft_eval 2
    ────────────────────────────────────────────────────────────────────────────────────────────
    deferral_ok 0 · vrf_threshold_satisfied 0 · window_transition_ok 0

`dregg_mina_deferral_ok` is the sharp one. It is `Dregg2.Circuit.Emit.PastaIpaDeferral`'s §5 gate —
the object that decides whether a batch of deferred IPA accumulator claims may be ACCEPTED — and
its `d=` field ("the batched MSM was evaluated and found to vanish") was read straight off a wire
string. With no caller, nothing ever computed that MSM, so `opening_is_vacuous_when_sg_is_free`
applied to the live runtime: an undischarged accumulator is not a weakened check, it is NO check.
The gate was closed on 2026-08-04 by `dregg_bridge::mina_accumulator_discharge`.

═══ WHAT COUNTS ═══════════════════════════════════════════════════════════════════
SHIPPED — an `@[export NAME]` whose module is in the transitive `import` closure of
`metatheory/Dregg2/FFI.lean`. That closure is the ship condition: a module rooted only in
`Dregg2.lean` ELABORATES and emits no `:c` facet, so its symbol never enters the archive and
"nobody calls it" is not a finding. Computed statically from `import` lines — no build needed.

NAMED — the export's name (or `NAME_str`, the C string bridge) appears in a tracked BINDER file:
a `.rs` file other than `dregg-lean-ffi/build.rs`, or a `.c`/`.h` under `dregg-lean-ffi/`
OUTSIDE its `extern` DECLARATIONS. Two exclusions, both the same rule — a file that merely
SPELLS a symbol has not bound it:
  · `dregg-lean-ffi/build.rs` names every symbol it PROBES with `archive_exports(...)`, so
    counting it would make every shipped export look wired.
  · a C `extern <ret> NAME(...);` prototype is the DECLARATION the compiler needs in order for a
    call to typecheck. It is the exact analogue of the build-script probe: writing it costs
    nothing and asserts nothing. `lean_init.c` declares all 15 `dregg_poa_bazaar_runtime_*`
    exports in one block; 14 are then CALLED and one — `..._request_encode` — is not, and that
    difference is the entire finding. So the prototype block is stripped before matching, and
    what remains is call sites.

⚑ 2026-08-05 — WHY C AT ALL. This gate scanned `tracked(["*.rs"])` only, while the binder for
`Dregg2.Games.PathOfAngels.BazaarGameRuntime`'s exports is C: `dregg-lean-ffi/src/lean_init.c`
calls fourteen of them directly, with the Rust side entering through `..._fixture_str`. The gate
therefore reported 15 problems of which 14 were wrong, and a reader who learns to skip a red is a
reader who will skip the next `deferral_ok` — this gate's own failure mode, pointed at itself.
The scan is scoped to `dregg-lean-ffi/` because that crate is what LINKS `libdregg_lean.a`; C
elsewhere in the tree (`orb/ffi/*.c`) links nothing from the archive, and a Lean-GENERATED
`.lake/build/ir/*.c` would name its own exports the way `build.rs` does.

A shipped export that is not named is a RED. That is the whole rule, and it is deliberately the
weaker of the two available bars: it asks "is there a binding at all", not "is the binding
reached". The stronger question — is the wrapper called from a CONSUMER crate — is reported in the
second column (`consumers`) so a reader can see it, and is NOT ratcheted, because a gate should
red on a fact it can state exactly rather than on a heuristic about call graphs. The C shim lives
INSIDE `dregg-lean-ffi/`, so a C call site never counts as a consumer either.

⚠ THE `binding-only` LINE MOVED 144 -> 158 WHEN C WAS ADDED, AND THAT IS NOT A REGRESSION. Those
14 are the `lean_init.c` call sites: they went from "no binding at all" (wrong) to "bound, but the
binder is in `dregg-lean-ffi`" (right). Nothing about the tree changed. The line stays UNGATED
deliberately — a consumer-crate ratchet would be a ratchet on a heuristic, and would fire on the
whole `dregg_d_*` FFIDirect constructor family, whose correct binder IS `lean_direct.rs` inside
this crate. Read it as a standing SIZE, not a defect count.

═══ THE RATCHET ═══════════════════════════════════════════════════════════════════
`.github/uncalled-exports.txt`, one row per deliberately-uncalled export:

    dregg_some_export   # why nothing calls it, and what would

An uncalled export NOT on the list fails. A row on the list that is NOW called ALSO fails — a stale
allowlist is how the next one gets waved through.

⚠ IT SWEEPS THE INDEX, NOT THE WORKING TREE (`git ls-files`), same as `check-dark-modules.py`: a
NEW `.rs`/`.c` you have not `git add`ed is INVISIBLE, so a freshly written caller reads as absent.
In CI that is correct and total; locally, `git add` first.

Usage:  python3 scripts/check-export-callers.py [--list PATH] [--print-all] [--self-test]
Exit:   0 clean · 1 ratchet violation · 2 usage/environment error
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_LIST = os.path.join(ROOT, ".github", "uncalled-exports.txt")
FFI_ROOT = os.path.join(ROOT, "metatheory", "Dregg2", "FFI.lean")
METATHEORY = os.path.join(ROOT, "metatheory")

EXPORT_RE = re.compile(r"@\[\s*export\s+([A-Za-z_][A-Za-z0-9_']*)\s*\]")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.M)

# Lean comments, stripped before `EXPORT_RE` runs. ⚑ 2026-08-05: without this, a DOC-COMMENT that
# spells `@[export foo]` — a header explaining a seam, or the note recording that one was deleted —
# registers `foo` as a SHIPPED EXPORT, and the gate then demands a caller for a symbol that is not
# in the archive at all. Measured over the tree at the time: 13 (file, name) pairs came from prose
# only, including one for an export deleted in this same change; stripping loses ZERO real
# `@[export]`s (checked both directions). The nested-block-comment case under-strips rather than
# over-strips, which leaves a phantom rather than hiding a real export — the safe direction.
LEAN_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
LEAN_LINE_COMMENT = re.compile(r"--[^\n]*")

# The build script names every symbol it PROBES with `archive_exports(...)`. Naming is not wiring.
PROBE_FILES = {"dregg-lean-ffi/build.rs"}

# The C half of the binder. Scoped to the crate that LINKS `libdregg_lean.a` — see the header.
C_PATTERNS = ["dregg-lean-ffi/**/*.c", "dregg-lean-ffi/**/*.h"]

# A C `extern` prototype: `extern <type> NAME(<params>);`, possibly spanning lines. It is the
# DECLARATION a call needs to typecheck, not a call — the C analogue of `build.rs`'s probe list.
# Stripped before matching so a declared-and-never-called export still reads as uncalled.
C_EXTERN_DECL = re.compile(r"\bextern\b[^;{]*;", re.DOTALL)

# ── SCOPE ─ this pair is the ONLY copy; it prints on every run, pass or fail. ─────────
SCOPE_ANSWERS = (
    "for every `@[export NAME]` in a git-TRACKED metatheory/**.lean whose module is in the import "
    "closure of metatheory/Dregg2/FFI.lean, does NAME or NAME_str appear as a plain SUBSTRING in some "
    "tracked .rs other than dregg-lean-ffi/build.rs, or in a tracked dregg-lean-ffi C/H file with its "
    "`extern …;` prototypes stripped — and is every row of .github/uncalled-exports.txt still a "
    "shipped export that nothing names?"
)
SCOPE_DOES_NOT_ANSWER = (
    "whether that mention is a CALL, or is reached. It is a substring hit: the name in a comment, a "
    "string literal, a `#[cfg(...)]`-dead wrapper or a test fixture all read as bound, and the "
    "stronger `binding-only` column (shipped, bound, but by nothing outside dregg-lean-ffi) is printed "
    "and deliberately NOT gated. It also sweeps the git INDEX, so a caller you have written but not "
    "`git add`ed is invisible and its export reads as dark."
)

SCOPE_ANSWERS_SELFTEST = (
    "can this INSTRUMENT still fire? Both poles of each matcher: a canary name no tracked file contains "
    "reads as UNNAMED, dregg_mina_lc_verify reads as named, a synthetic C `extern` prototype is stripped "
    "while a real lean_init.c call site survives it, and an `@[export]` spelled only in Lean prose is not "
    "a shipped export while a real attribute is."
)
SCOPE_DOES_NOT_ANSWER_SELFTEST = (
    "the census itself. This mode never runs survey(), never computes the shipped-export set and never "
    "reads .github/uncalled-exports.txt, so a SELF-TEST PASS says the matchers are not blind — never "
    "that any export in this tree is wired."
)


def tracked(patterns: list[str]) -> list[str]:
    out = subprocess.run(
        ["git", "-C", ROOT, "ls-files", "-z", *patterns],
        capture_output=True,
        text=True,
        check=True,
    )
    return [p for p in out.stdout.split("\0") if p]


def module_path(mod: str) -> str | None:
    """`Dregg2.Circuit.Emit.PastaIpaDeferral` -> metatheory/Dregg2/Circuit/Emit/PastaIpaDeferral.lean"""
    p = os.path.join(METATHEORY, *mod.split(".")) + ".lean"
    return p if os.path.isfile(p) else None


def ffi_closure() -> set[str]:
    """Every module transitively imported by `Dregg2/FFI.lean`, plus FFI itself."""
    seen: set[str] = set()
    stack = ["Dregg2.FFI"]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        p = module_path(mod)
        if p is None:
            continue
        with open(p, "r", encoding="utf-8", errors="replace") as fh:
            src = fh.read()
        for imp in IMPORT_RE.findall(src):
            if imp not in seen:
                stack.append(imp)
    return seen


def exports_by_module() -> dict[str, list[str]]:
    """{module -> [export names]} over every tracked .lean under metatheory/."""
    out: dict[str, list[str]] = {}
    for rel in tracked(["metatheory/**/*.lean"]):
        if "/.lake/" in rel:
            continue
        with open(os.path.join(ROOT, rel), "r", encoding="utf-8", errors="replace") as fh:
            src = fh.read()
        names = EXPORT_RE.findall(
            LEAN_LINE_COMMENT.sub(" ", LEAN_BLOCK_COMMENT.sub(" ", src))
        )
        if not names:
            continue
        mod = os.path.relpath(os.path.join(ROOT, rel), METATHEORY)[: -len(".lean")]
        out.setdefault(mod.replace(os.sep, "."), []).extend(names)
    return out


def binder_mentions(names: set[str]) -> dict[str, list[str]]:
    """{export -> [tracked binder files that name it]}.

    Binders are tracked `.rs` (minus `PROBE_FILES`) and tracked `.c`/`.h` under `dregg-lean-ffi/`
    with their `extern` prototypes stripped. Both exclusions say the same thing: a file that
    merely SPELLS a symbol has not bound it.
    """
    hits: dict[str, set[str]] = {n: set() for n in names}
    sources: list[tuple[str, str]] = []
    for rel in tracked(["*.rs"]):
        if rel in PROBE_FILES:
            continue
        sources.append((rel, "rs"))
    for rel in tracked(C_PATTERNS):
        sources.append((rel, "c"))
    for rel, kind in sources:
        try:
            with open(os.path.join(ROOT, rel), "r", encoding="utf-8", errors="replace") as fh:
                src = fh.read()
        except OSError:
            continue
        if kind == "c":
            src = C_EXTERN_DECL.sub(" ", src)
        for n in names:
            if n in src:
                hits[n].add(rel)
    return {k: sorted(v) for k, v in hits.items()}


def read_list(path: str) -> dict[str, str]:
    allow: dict[str, str] = {}
    if not os.path.isfile(path):
        return allow
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            body = line.split("#", 1)[0].strip()
            if not body:
                continue
            allow[body.split()[0]] = line.split("#", 1)[1].strip() if "#" in line else ""
    return allow


def survey(list_path: str):
    closure = ffi_closure()
    by_mod = exports_by_module()
    shipped: dict[str, str] = {}
    for mod, names in by_mod.items():
        if mod in closure:
            for n in names:
                shipped[n] = mod
    probe_names = set(shipped) | {f"{n}_str" for n in shipped}
    mentions = binder_mentions(probe_names)

    rows = []
    for name, mod in sorted(shipped.items()):
        files = sorted(set(mentions.get(name, [])) | set(mentions.get(f"{name}_str", [])))
        consumers = [f for f in files if not f.startswith("dregg-lean-ffi/")]
        rows.append((name, mod, files, consumers))
    return rows, read_list(list_path)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", default=DEFAULT_LIST)
    ap.add_argument("--print-all", action="store_true")
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="prove the gate can go RED: inject a shipped export that nothing names.",
    )
    args = ap.parse_args()

    if args.self_test:
        print(f"ANSWERS:         {SCOPE_ANSWERS_SELFTEST}", flush=True)
        print(f"DOES NOT ANSWER: {SCOPE_DOES_NOT_ANSWER_SELFTEST}", flush=True)
        # A name no `.rs` in this tree contains, checked against the same matcher.
        canary = "dregg_selftest_export_no_caller_zzz"
        found = binder_mentions({canary, canary + "_str"})
        named = bool(found[canary] or found[canary + "_str"])
        if named:
            print(f"SELF-TEST FAIL: the canary {canary} is named in {found}")
            return 1
        # …and the positive control: an export that IS named must read as named.
        control = "dregg_mina_lc_verify"
        ctrl = binder_mentions({control, control + "_str"})
        if not (ctrl[control] or ctrl[control + "_str"]):
            print(f"SELF-TEST FAIL: the control {control} reads as uncalled")
            return 1
        # ── the C leg, BOTH poles. A gate that scans C must be shown to (a) SEE a C call and
        # (b) NOT see an `extern` prototype — otherwise "scanning C" degenerates into "every
        # declared symbol is wired", which is the build.rs confusion in a second language.
        # The negative pole is SYNTHETIC on purpose: the only real extern-only export in the tree
        # was deleted on 2026-08-05, and a self-test that needs one to exist would go quiet the
        # moment the gate did its job.
        c_called = "dregg_poa_bazaar_runtime_state_key_validate"  # declared AND called in lean_init.c
        cleg = binder_mentions({c_called})
        c_files = [f for f in cleg[c_called] if f.endswith((".c", ".h"))]
        if not c_files:
            print(
                f"SELF-TEST FAIL: the C control {c_called} reads as unnamed — the C scan is blind "
                f"(it is called from dregg-lean-ffi/src/lean_init.c)"
            )
            return 1
        c_canary = "dregg_selftest_extern_only_zzz"
        shim = os.path.join(ROOT, "dregg-lean-ffi", "src", "lean_init.c")
        with open(shim, "r", encoding="utf-8", errors="replace") as fh:
            c_src = fh.read()
        spliced = c_src + f"\nextern lean_object *{c_canary}(lean_object *x);\n"
        after = C_EXTERN_DECL.sub(" ", spliced)
        if c_canary in after:
            print(
                f"SELF-TEST FAIL: an `extern` prototype for {c_canary} SURVIVED the stripper — a "
                f"declared-and-never-called export would read as wired, so no dark C export can red"
            )
            return 1
        if c_called not in after:
            print(
                f"SELF-TEST FAIL: the stripper ate {c_called}'s CALL SITE too — it over-fires, and "
                f"every C-bound export would read as uncalled"
            )
            return 1
        # ── the prose pole: a doc-comment spelling an attribute is not an attribute.
        p_canary = "dregg_selftest_prose_export_zzz"
        prose = f"-- see `@[export {p_canary}]`\n/-- `@[export {p_canary}]` -/\ndef f := 1\n"
        real = f"@[export {p_canary}]\ndef f := 1\n"
        strip = lambda s: LEAN_LINE_COMMENT.sub(" ", LEAN_BLOCK_COMMENT.sub(" ", s))
        if EXPORT_RE.findall(strip(prose)):
            print(
                f"SELF-TEST FAIL: {p_canary} named only in a Lean COMMENT reads as a shipped "
                f"export — the gate would demand a caller for a symbol not in the archive"
            )
            return 1
        if EXPORT_RE.findall(strip(real)) != [p_canary]:
            print(
                f"SELF-TEST FAIL: a REAL `@[export {p_canary}]` is lost to comment-stripping — the "
                f"gate has gone blind to the population it exists to census"
            )
            return 1
        print(
            f"SELF-TEST PASS: an unnamed export reads as uncalled; {control} reads as called "
            f"({len(ctrl[control]) + len(ctrl[control + '_str'])} files); {c_called} reads as "
            f"called from C ({', '.join(c_files)}); a synthetic extern-only prototype does NOT; "
            f"and an `@[export]` spelled in Lean prose is not a shipped export while a real one is."
        )
        return 0

    print(f"ANSWERS:         {SCOPE_ANSWERS}", flush=True)
    print(f"DOES NOT ANSWER: {SCOPE_DOES_NOT_ANSWER}", flush=True)

    rows, allow = survey(args.list)
    uncalled = [(n, m, c) for (n, m, f, c) in rows if not f]
    binding_only = [(n, m) for (n, m, f, c) in rows if f and not c]

    print(f"shipped exports (in the Dregg2.FFI import closure): {len(rows)}")
    print(f"  with a binding (.rs, or a C call site) : {len(rows) - len(uncalled)}")
    print(f"  UNCALLED            : {len(uncalled)}")
    print(f"  binding-only (no consumer crate outside dregg-lean-ffi): {len(binding_only)}")

    if args.print_all:
        for name, mod, files, consumers in rows:
            print(f"  {len(files):>2} rs / {len(consumers):>2} consumer  {name:<44} {mod}")

    bad = 0
    for name, mod, _ in uncalled:
        if name in allow:
            continue
        bad += 1
        print(
            f"UNCALLED EXPORT: {name}  ({mod})\n"
            f"    it is in the Dregg2.FFI import closure, so it SHIPS in libdregg_lean.a, and no\n"
            f"    tracked .rs file — and no C call site in dregg-lean-ffi outside an `extern`\n"
            f"    prototype — names it. Wire it, delete it, or put it on {os.path.relpath(args.list, ROOT)}\n"
            f"    with the reason nothing calls it."
        )
    stale = [n for n in allow if any(n == r[0] and r[2] for r in rows)]
    for n in stale:
        bad += 1
        print(
            f"STALE ALLOWLIST ROW: {n} is now named by a binder — remove it from "
            f"{os.path.relpath(args.list, ROOT)}."
        )
    unknown = [n for n in allow if not any(n == r[0] for r in rows)]
    for n in unknown:
        bad += 1
        print(
            f"STALE ALLOWLIST ROW: {n} is not a shipped export at all (renamed, deleted, or no "
            f"longer imported by Dregg2/FFI.lean)."
        )

    if bad:
        print(f"\nFAIL: {bad} problem(s).")
        return 1
    print(
        "\nCLEAN: every shipped Lean export is named by a Rust or C binder, or is on the ratchet "
        "with a reason."
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as e:
        print(f"environment error: {e}", file=sys.stderr)
        sys.exit(2)
