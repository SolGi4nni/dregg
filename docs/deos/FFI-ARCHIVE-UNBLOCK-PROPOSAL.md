# Proposal: promote the runtime-dead init trim's no-op stubs to the DEFAULT archive

**One change, for coordination with the archive-shrink terminal.** This is the single infra
decision that turns every committed Lean `@[export]` — the render FFI (`dregg_render_with_proof`),
the census "port-now" deciders, and the future QuorumThreshold / derives / accumulator gates —
into something Rust can actually link and call. It is a **proposal for the archive-shrink
terminal's files**, authored here so we can agree the diff shape before either terminal touches
`dregg-lean-ffi/build.rs`, `src/lean_init.c`, or `src/lib.rs` (all shared, all theirs this pass).

Grounded in `docs/deos/LEAN-FFI-ARCHIVE-BLOCKER.md` (committed) and a read-only sweep of
`dregg-lean-ffi/build.rs` @ HEAD (2026-07-17). Line numbers drift — every anchor below names the
function/symbol so it survives edits.

---

## 1. The problem, in one sentence

A Mathlib-heavy non-trivial export links only if the archive **carries or no-ops** every
`_initialize_mathlib_*` / ProofWidgets / aesop / elaborator symbol its kept init-chain still
references. The default archive carries neither, so `dregg_render_with_proof` (and any real
computation over imported Mathlib defs) dangles at the final link. The **mechanism that severs
that init-pull already exists** — it is just gated behind an opt-in flag and written to a throwaway
archive.

## 2. The lever that already exists

`runtime_dead_init_trim` (`build.rs`, doc-comment "The PRINCIPLED elaborator / proof-time TRIM",
currently ~`:1028`) does two separable things:

1. **REPACK** — nm-walks the runtime-FUNCTION closure from the `dregg_*` roots (chasing every
   edge *except* `initialize_*`), keeps only live members, and `ar rcs`-repacks them into a
   **separate** `libdregg_lean_trim.a`. This is the *size* win (the archive-shrink terminal's
   headline).
2. **NO-OP STUB GEN** — for every runtime-dead module init the kept chain still references but
   no kept member defines (the `dangling` set, skipping toolchain `initialize_{Init,Std,Lean,Lake}`),
   it emits `runtime_trim_init_stubs.c`: an idempotent `NOOP_INIT(name)` per dangling init
   (`lean_object* name(uint8_t){ return lean_io_result_mk_ok(lean_box(0)); }`). The caller
   compiles this into the `+whole-archive` shim (`shim.file(stub)` under `if let Some(stub) =
   &runtime_trim_stub`, ~`:1996`), so the no-ops **win over any archive definition** and the
   elaborator/Mathlib init-pull is severed at the closure boundary.

**Step 2 is the render-FFI unblock.** It is the general, automated form of the grain/holding
hand-trick the trivial `"1"/"0"` deciders got by luck. But today it only runs when
`DREGG_LEAN_FFI_RUNTIME_TRIM=1` (`build.rs`, `runtime_trim_requested`, ~`:1610`) and the caller
guards the whole thing (`if runtime_trim_requested { runtime_dead_init_trim(...) } else { None }`,
~`:1721`), then links `dregg_lean_trim` instead of `dregg_lean` only when the stub is `Some`
(`build.rs` ~`:2117-2124`). The default link (`env unset`) links `libdregg_lean.a` and **never
sees the stubs** — so archive-shrink does not unblock render as a side effect.

## 3. The proposal — the EXACT change

We want the **no-op stub generation applied to the DEFAULT archive**, decoupled from the
opt-in *repack*. Two shapes, in preference order.

### 3a. PREFERRED — a stub-only pass that always runs (keeps the repack opt-in)

Add a second, cheap function next to `runtime_dead_init_trim` — call it
`boundary_init_noops(build_archive, out_dir) -> Option<PathBuf>` — that does **only** step 2's
analysis and emits the stub `.c`, but does **not** repack (it leaves the default
`libdregg_lean.a` intact and keeps every member).

The dangling-set computation it needs is the same nm-walk already in `runtime_dead_init_trim`
(`undef_func` / `undef_init` / `sym_def_in` / `roots` maps, the live-BFS, then the `dangling`
loop that skips `is_toolchain`). Refactor that analysis into a shared helper so both callers use
one code path (no second copy of the parser — the blocker doc's "MIRROR" hazard). The only
behavioral difference: `boundary_init_noops` stops after writing the stub; it never calls `ar x`
/ `ar rcs` / `ranlib` and never switches the linked archive name.

**Wiring diff (in `build()`):**

```
// was:
let runtime_trim_stub = if runtime_trim_requested {
    runtime_dead_init_trim(&build_archive, &trim_archive, &out_dir)
} else {
    None
};

// becomes:
let runtime_trim_stub = if runtime_trim_requested {
    // opt-in: repack to the trimmed archive AND emit the boundary no-ops (size + link win)
    runtime_dead_init_trim(&build_archive, &trim_archive, &out_dir)
} else {
    // DEFAULT: keep the full archive, but ALWAYS emit the boundary no-op stubs so
    // Mathlib-heavy exports (render FFI + port-now deciders) link. No repack, no size change.
    boundary_init_noops(&build_archive, &out_dir)
};
```

**Nothing else in the link path changes shape.** `shim.file(stub)` already compiles whatever
stub `runtime_trim_stub` carries into the whole-archive shim (~`:1996`). The archive-selection
block (~`:2117`) keys on `runtime_trim_stub.is_some()` to pick `dregg_lean_trim` vs `dregg_lean`
— that must be re-keyed so the **default** stub-only path still links `dregg_lean` (the full
archive), while only the **opt-in repack** path links `dregg_lean_trim`. Concretely, branch on a
separate boolean (e.g. `let linked_trim = runtime_trim_requested && runtime_trim_stub.is_some();`)
rather than on `runtime_trim_stub.is_some()`:

```
// was:  if runtime_trim_stub.is_some() { link dregg_lean_trim } else { link dregg_lean }
// becomes:
if linked_trim {
    println!("cargo:rustc-link-lib=static=dregg_lean_trim");
} else {
    println!("cargo:rustc-link-lib=static=dregg_lean");
}
```

This is the load-bearing correctness point of the whole proposal: **decouple "a stub was
generated" from "we repacked and are linking the trimmed archive."** Today they are the same
`Option`; after the change they are two facts.

### 3b. ALTERNATIVE — flip the default of the existing flag

Make `runtime_trim_requested` default to `true` (opt *out* via
`DREGG_LEAN_FFI_RUNTIME_TRIM=0`). Simpler diff, but it changes the DEFAULT archive from the full
byte-for-byte-verified `libdregg_lean.a` to the repacked `libdregg_lean_trim.a` for *every*
consumer (node, dregg-turn, render). That is a much bigger blast radius — the verified-link
byte-identity property (called out at `build_archive` seed, ~`:1599-1601`) is lost by default,
and any latent repack bug now breaks the node, not just an opt-in lane. **Prefer 3a**: the
default keeps the full verified archive and merely *adds* boundary no-ops, which are inert for
exports that don't reference dead inits and load-bearing for the ones that do.

## 4. Risk assessment (be honest)

- **A no-op stub for an init that was NOT actually runtime-dead would skip a real CAF
  initialization → null-deref at runtime.** The `dangling` computation only no-ops an init when
  **no kept member defines it** and it is **not toolchain** (`is_toolchain` guards
  `initialize_{Init,Std,Lean,Lake}`, so sysroot inits still really run). In the **default
  (no-repack) path every member is kept**, so `dangling` is *smaller* than in the trim path — a
  module init is dangling only if the archive genuinely never carries it (the Mathlib inits the
  leanc-native archive was never built with). That is exactly the set we WANT to no-op. Risk is
  strictly lower than the already-shipped opt-in path.
- **A no-op could shadow a real Mathlib CAF that `renderWithProofWire` actually reads at
  runtime.** This is the one genuine hazard and the reason the blocker doc rates a clean render
  link "plausible but unlikely." If `renderWithProofWire`'s computation over imported `List` /
  `Option` / `DecidableEq` defs bottoms out in a Mathlib CAF whose init we no-op'd, the value is
  null at call time. **Mitigation:** this is an *empirical* question — wire the export (§5), build,
  and drive one real render through the FFI (an executor-probe-style KAT, the same empirical
  safety check `embeddable_runtime_probe` gives the trim). If it faults on a specific
  `initialize_Mathlib_*`, that init is NOT runtime-dead for render, and the fallback is the
  per-export **proof-split** (option (b) in the blocker doc: import-thin `HandlebarsFFI` the way
  `FriLedger`/`FriLedgerSound` split, so the runtime slice carries no Mathlib CAFs).
- **Build-time cost:** the extra nm-walk on the default path is one `nm -A` over the archive plus
  a HashMap BFS — the same analysis the opt-in path already pays; sub-second next to the `lake
  build` / splice. No repack means no `ar x` / `ar rcs` on the default path.
- **Whole-archive precedence:** the stub is compiled into the `+whole-archive` shim
  (`rustc-link-lib=static:+whole-archive=dregg_ffi_shim`, ~`:2116`), so the no-op definitions are
  guaranteed present and win over any archive-side definition regardless of link order — the same
  property the opt-in path relies on today.

## 5. The per-export wiring boilerplate (independent of §3; ~5 edits + 2 files per export)

Promoting the stubs unblocks the *link*; each export still needs its advertise-wiring. For
`dregg_render_with_proof` (module `Dregg2.Deos.HandlebarsFFI`, the render case) the edits mirror
the existing `dregg_decide_refines` / `dregg_storage_content_root` exports exactly:

1. **`build.rs` `lake_targets`** (~`:257-286`): add `"Dregg2.Deos.HandlebarsFFI"` so its `.c` IR
   is emitted and the splice picks up the `dregg_render_with_proof` symbol. (It is OUTSIDE the FFI
   module's import closure, like `FlowRefine` / `Storage.Deployed`.)
2. **`build.rs` `rustc-check-cfg`** (~`:1470-1477`): add
   `println!("cargo::rustc-check-cfg=cfg(dregg_render_present)");`.
3. **`build.rs` archive_exports probe → rustc-cfg** (the block of `archive_exports(&build_archive,
   "dregg_…")` guards, ~`:1731-1846`): add
   `let render_present = archive_exports(&build_archive, "dregg_render_with_proof");` with the
   `println!("cargo:rustc-cfg=dregg_render_present");` on hit and the honest
   `cargo:warning=… lacks dregg_render_with_proof … bridge compiled out` on miss.
4. **`build.rs` `shim.define`** (the `if handler_present { shim.define("DREGG_HANDLER_TURN", ...) }`
   family, ~`:2013-2024`): add `if render_present { shim.define("DREGG_RENDER", None); }`.
5. **`src/lean_init.c`**: add the `dregg_render_with_proof_str` wrapper under `#ifdef DREGG_RENDER`
   (mirror the existing `dregg_decide_refines_str` / decider wrappers — marshal the args, call the
   Lean export, hand back the string; and either add its `initialize_…_HandlebarsFFI` to the
   explicit-init list *or* keep it deliberately un-init'd like the self-contained deciders, which
   is the decision §4's empirical test settles).
6. **`src/lib.rs`**: the `extern "C"` declaration for `dregg_render_with_proof_str` gated on
   `#[cfg(dregg_render_present)]`, plus the `shadow_render*` safe wrapper and its
   `#[cfg(not(dregg_render_present))]` fallback (mirror `shadow_decide_refines` / the existing
   `shadow_*` pattern).

The census "port-now" kill deciders (QuorumThreshold, the derives/accumulator gates) each repeat
the same 6-edit shape against their own module + `dregg_<name>` symbol. None of it is
load-bearing until §3 makes the link succeed.

## 6. The handshake

- **Owner of the change:** the archive-shrink terminal (it owns `build.rs` / `lean_init.c` /
  `lib.rs` this pass). This doc is the agreed spec, not an edit to those files.
- **Sequencing:** land §3a (the stub-only default pass + the `linked_trim` re-key) FIRST — it is
  self-contained infra with strictly-lower risk than the already-shipped opt-in path and no
  consumer-visible archive change. THEN either terminal does the §5 wiring for a single export
  (render) and runs the §4 empirical probe. If render links + runs, the census deciders follow
  mechanically; if it faults on a Mathlib CAF, fall back to the per-export proof-split for that
  one module — the default-stub infra still stands and unblocks every export that doesn't hit a
  live Mathlib CAF.
- **Do NOT** fire a concurrent lane that also edits `build.rs` / `lean_init.c` / `lib.rs` — single
  owner, single sequence, as the blocker doc's coordination note requires.

---

*Verdict: one infra change (§3a) + one empirical probe settles the entire "Lean authors the
decider/witness, Rust calls it" cluster. The mechanism is built; it needs promoting from a
throwaway opt-in archive to the default, with the "stub generated" fact decoupled from the "link
the trimmed archive" fact.*
