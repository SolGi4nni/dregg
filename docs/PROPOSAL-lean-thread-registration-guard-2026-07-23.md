# Proposal: make Lean-thread-registration an ENFORCED precondition, not an implicit one (2026-07-23)

**Status: PROPOSAL** (for the node / dregg-lean-ffi owners). Author: claude-of-dregg, from the
2026-07-22 flaw-hunt (`docs/FLAW-HUNT-BACKLOG-2026-07-22.md`).

## The class, in one sentence

Every `dregg_lean_ffi::shadow_*` call and every installed Lean oracle/gate has an **unenforced,
implicit precondition**: the calling thread must be one the Lean runtime has *registered*. A call
from an unregistered thread (a `tokio::task::spawn_blocking` pool thread, a bare `std::thread`, a
rayon worker) does not error usefully — under full-Lean it **silently refuses or silently
downgrades**, and under `no-lean-link` the gate is off so nothing is exercised at all. The precondition
is real, load-bearing, and invisible.

## Evidence it is live, not theoretical

- **Caught in the wild** (commit `6d0e024f19`): the crowd-stream close ran the executor turn via
  `spawn_blocking`; under full-Lean the reality-gate's Lean constraint eval ran on the unregistered
  pool thread, the turn was **silently refused**, the world never moved. Inline on the registered
  runtime worker: fine. Only full-Lean *verification* exposed it; `no-lean-link` masked it as LARP.
- **The same anti-pattern is ARMED in the node** (the binary that actually calls
  `register_constraint_oracle()`, `node/src/lib.rs:617`):
  - `node/src/blocklace_sync.rs:6680` — **authoritative** finalized-turn execution
    (`produce_via_lean` → `shadow_exec_full_forest_auth` + the armed oracle) on `spawn_blocking`.
  - `:5617` — FNSP-v3 `execute()` (the global oracle fires inside `execute()` regardless of the Rust
    producer fence) on `spawn_blocking`.
  - `:1549`, `:1708` — the VERIFIED finality/projection gates on `spawn_blocking`; a failing
    unregistered-thread call is `timeout`→`None`→**falls back to the unverified Rust `tau` order**.
    The verified finality gate becomes **decorative with no surfaced error**.
- **Latent, waiting on arming**: the whole `discord-bot` `spawn_blocking` fleet + any off-thread
  `MlDsaKey::try_sign` — safe today only because the bot/web do not arm the Lean cores; they join the
  critical class the instant a full-Lean build installs one. (This is why the full-Lean bot redeploy
  is HELD.)

The mechanism (confirmed from source): both inits register only the FIRST calling thread
(`dregg_ffi_init` → `lean_initialize_runtime_module`; `dregg_ffi_init_st` → `lean::initialize_thread`,
behind process-wide `OnceLock`s). The per-thread primitive is `lean_initialize_thread()`; the ONLY
correct caller in the repo is `orb/crates/dataplane/src/serve.rs:2660` / `control.rs:487` — a
single-owner job loop on a registered thread. That is the pattern to generalize.

## The fix — two complementary moves

### 1. STRUCTURAL: expose registration + a registered owner-thread idiom

Add to `dregg-lean-ffi`:

```rust
/// Register the CURRENT thread with the Lean runtime so it may cross a `shadow_*` seam.
/// Idempotent per thread (thread-local guard). No-op (Ok) under `no-lean-link`.
pub fn register_this_thread_with_lean() -> Result<(), String>;   // wraps lean_initialize_thread()
pub fn finalize_this_thread();                                    // wraps lean_finalize_thread()

/// RAII: register on construction, finalize on drop. For a long-running owner thread, construct once
/// at the top of the thread body.
pub struct LeanThread(());                                        // register on `enter()`, finalize on Drop
impl LeanThread { pub fn enter() -> Result<LeanThread, String>; }
```

Then the node's executor + finality FFI run on a **registered owner thread** — the `HostThread`
channel pattern already in `dreggnet-web`/`dreggnet-telegram` generalizes cleanly: one owning thread
that calls `LeanThread::enter()` at the top and receives Lean jobs over a channel; the reactor stays
free (the point of `spawn_blocking`) AND the thread is registered. Where a dedicated owner is
overkill, the blocking closure calls `register_this_thread_with_lean()?` on entry (cheap, idempotent).

### 2. ENFORCEMENT: refuse loudly off a registered thread (turn silent → visible)

A thread-local `REGISTERED: Cell<bool>` set by init/registration. Every `shadow_*` entry point and
every installed oracle/gate `eval` checks it FIRST:

```rust
// at the top of every shadow_* / oracle eval, before touching Lean:
if cfg!(dregg_full_lean_ci) || cfg!(debug_assertions) {
    debug_assert!(lean_thread_registered(), "Lean FFI called from an UNREGISTERED thread: {fn_name} \
        — register the thread (dregg_lean_ffi::register_this_thread_with_lean) or run on a \
        LeanThread owner. This silently refuses/downgrades in release; do NOT ship it.");
}
```

In a **full-Lean CI build**, make it a hard, loud refusal (a distinct `Err`/panic naming the call
site) rather than a silent wrong answer. This converts today's *day-later* symptom ("the world never
moved" / "finality quietly ran unverified") into a *call-site* failure.

### 3. CI + a grep-lint (so the next one is caught mechanically)

- **Run the full-Lean path in CI.** It is the only thing that exercises this class — it is exactly what
  caught the overlay bug. `no-lean-link` CI structurally cannot.
- **A grep-lint**: flag any `spawn_blocking` / `thread::spawn` / `par_iter` closure whose body
  transitively reaches `dregg_lean_ffi::` or a `*_oracle` / `*_gate` seam. It would flag the four node
  sites above mechanically. Belongs in the same CI as the full-Lean run.

## Migration (concrete, ordered)

1. Land `register_this_thread_with_lean` / `LeanThread` in `dregg-lean-ffi` (+ the thread-local flag).
2. Node: route `blocklace_sync.rs:{6680,5617}` (execution) and `{1549,1708}` (finality) through a
   `LeanThread` owner (or `register_this_thread_with_lean()` on the closure entry). Reference:
   `orb/dataplane`.
3. Add the `debug_assert!`/CI-refuse guard to every `shadow_*` entry + the constraint/finality oracle
   evals (`exec-lean/src/{constraint_oracle,lean_shadow}.rs`).
4. Turn on full-Lean CI + the grep-lint. The overlay fix (`dreggnet-web/src/overlay.rs`) and the
   `HostThread` owner threads become the reference-correct examples.
5. THEN the full-Lean bot redeploy is safe (its `spawn_blocking` fleet either routes through a
   registered thread or the guard catches it in CI first).

## Scope / ownership

The node execution + finality code and the `dregg-lean-ffi` FFI layer are the node/crypto owners'
territory; this proposal is a design + the exact sites, not a unilateral rewrite. The frontend
reference fix (overlay inline-on-registered-worker) is already landed. Happy to implement any/all of
this against a green-light — the `dregg-lean-ffi` registration API + the guard are the load-bearing,
reusable piece.
