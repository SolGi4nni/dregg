# Turn-Prover Crate Extraction — Design

**Status:** design only (read-only survey; no code moved). **Date:** 2026-07-24.
**Goal:** retire the brittle `feature = "prover"` on `dregg-turn` in favor of a
`dregg-turn-prover` crate, so prover-only code composes via **always-compiled crate
boundaries + explicit deps** instead of a `#[cfg]` matrix.

---

## 0. Why (the failure this fixes)

A `#[cfg(feature = "prover")]` arm inside a shared `match` (or a `#[cfg]` struct
field) goes **non-exhaustive / shape-divergent** the moment a new enum variant or
struct literal is added, but the omission compiles **green** in `cargo build -p
dregg-turn` (default has `prover`) and even in `-p dregg-turn --features prover`
when cached. It breaks only in a downstream crate whose feature *resolution* lights
up the exact `not(prover)` (or differently-unified) path — this session, a
`ShieldedNoteInserted` match gap surfaced only in `dreggnet-game-board`'s **test
target, 4 crates away**.

Root cause: **a feature-gated green does not prove the gated code compiles.** Cargo
compiles the crate under *one* resolved feature set; the cfg arms not selected are
never type-checked in that build. A crate boundary is different — `dregg-turn-prover`
is **always compiled as itself**, so an omission is a compile error **at the source**,
in the same `cargo build`, not a landmine downstream.

Secondary win: the majority of `dregg-turn`'s ~50 consumers only use the **core**
(TurnBuilder / TurnReceipt / executor-verify) and inherit `dregg-circuit-prove`
(multi-MB, recursion substrate) purely because it rides `turn`'s `default =
["prover"]`. Extraction gives them a lighter build with an honest dep graph.

---

## 1. Survey (verified against HEAD)

### 1.1 `turn`'s prover sites — 84 grep hits (~83 real; one is a doc-comment in
`bilateral_schedule.rs:733`). Grouped by cohesion and, crucially, by **what `turn`
internal each group touches**:

| Grp | What | Files / sites | circuit-prove surface | Turn internal touched | Extractable? |
|-----|------|---------------|----------------------|----------------------|--------------|
| **A** | **Rotation witness producers** (the per-turn wide/rotated leg mints) | `rotation_witness.rs` (8) | `ivc_turn_chain`, `joint_turn_aggregation`, `descriptor_ir2::prove_*` | **PUBLIC only**: `crate::umem::*` (pub mod), `crate::action::*` (pub mod), `RecordKernelState` (pub cell projection) | **Clean** |
| **B** | **Aggregate bilateral prover** | `aggregate_bilateral_prover.rs` (21, incl. `not(prover)` stubs) | `bilateral_aggregation_air::{prove_*, verify_*}`, `descriptor_ir2::{DreggStarkConfig, Ir2BatchProof}` | **PUBLIC only**: `bilateral_schedule` (pub), `error::TurnError` (pub), `turn::Turn` (pub), `witnessed_receipt::WitnessedReceipt` (pub) | **Clean** |
| **C** | **Recursive witness bundle producer** | `witnessed_receipt.rs` (5) | `recursive_witness_bundle::RecursiveProofProducer` | The `WitnessedReceipt` / `WitnessBundle` **types are unconditional** (verify-side needs them); only the `produce_*` methods are gated | **Split** (type stays, producer moves) |
| **D** | **Proof-carrying Custom-leaf modules** (whole `#![cfg]` modules) | `descent_census_custom.rs`, `private_preference_custom.rs`, `private_graph_rewrite_custom.rs`, `private_graph_rewrite_history.rs` (1 each) | `descent_census`, `private_preference`, `private_graph_rewrite`, `private_quest_graph` | **NONE** (self-contained wrappers over circuit-prove cells) | **Cleanest** |
| **E** | **Exact-FNSP-v3 acceptance family** — 5 whole `#![cfg]` modules **+ the executor admission slot** | modules: `exact_fnsp_v4_consensus_envelope.rs`, `faithful_note_spend_exact_v3_acceptance.rs`, `faithful_note_spend_exact_v3_receipt_epoch.rs`, `faithful_note_spend_exact_v3_verifier.rs`, `faithful_note_spend_verifier.rs`; **woven**: `executor/mod.rs` (14 — the `exact_fnsp_v3_admission` field, `ExactFnspV3AdmissionError`, 4 admission methods, 3 struct literals), `executor/execute.rs` (3), `executor/apply.rs` (the exact-v3 `NoteSpend` route) | `faithful_note_spend*`, verify-side descriptors | acceptance module touches `crate::executor::{ExactFnspV3AdmissionError, TurnExecutor}`, `crate::journal::LedgerJournal`; **admission slot is a FIELD of `TurnExecutor`** | **Hard (woven)** |
| **F** | **Shielded-transfer apply** (`apply_shielded_transfer` prover + `not(prover)` fail-closed pair) | `executor/apply.rs` (method pair) | `dregg_circuit_prove::shielded::{ShieldedTransfer, ...}` (a **verifier** that happens to live in the prove crate) | Method **on `TurnExecutor`**, invoked mid-`apply`, takes `&mut LedgerJournal` | **Hard (hot path)** |
| **G** | Prover-gated **tests** | `conditional.rs` (4), `executor/atomic.rs` (1), `apply.rs` (1), plus the `#[cfg(all(test, feature="prover"))]` modules | — | test-local | move with subject |
| — | Module decls + re-exports | `lib.rs` (15) | — | — | mechanical |
| — | Shared proving recipe | `conditional::mint_transfer_proven_receipt` | `descriptor_ir2::prove_vm_descriptor2`, `effect_vm::trace_rotated` | public projections | Clean (with A) |
| — | Custom-proof binding | `turn::with_custom_program_proofs` | `custom_proof_bind::BoundCustomProof` | builds pub `CustomProgramProof` | Clean |

**The decisive structural fact:** Groups **A / B / C / D** and the two loose items
touch **only `turn`'s public interface** (`Turn`, `TurnReceipt`, `WitnessedReceipt`,
`RecordKernelState`, the `umem` / `action` pub modules). They can move to
`turn-prover` **with zero new visibility exposure**. Groups **E / F** are **woven
into the `TurnExecutor` struct and the `apply` hot path** — the executor *calls into*
them during execution, so they cannot simply move to a downstream crate (the dep
would point `turn → turn-prover`, the wrong way). They need the executor's existing
**dependency-inversion seam**, not a relocation. This split is the spine of the plan.

### 1.2 The other 10 crates that define a `prover` feature (site counts @ HEAD)

| crate | sites | `prover =` definition | kind |
|-------|-------|----------------------|------|
| `cell` | 0 | `prover = []` | **no-op** (retained only so `dregg-cell/prover` forwards stay valid) |
| `demo` | 0 | `prover = []` | **no-op** declaration |
| `teasting` | 0 | `prover = []` | **no-op** declaration |
| `tests` | 2 | `prover = []` | near-no-op (2 self-gated sites, enables nothing) |
| `lightclient` | 3 | `["dregg-turn/prover"]` | **pure forward** |
| `perf` | 3 | `["dregg-sdk/prover", "dregg-turn/prover"]` | **pure forward** |
| `node` | 19 | `["dregg-sdk/prover", "dregg-turn/prover", "dregg-cell/prover"]` | forward + 19 local gated sites |
| `grain-turn` | 2 | `["dep:dregg-turn", "dep:dregg-circuit", "dep:dregg-circuit-prove", "dregg-turn/prover"]` | forward, makes turn optional (R3 adapter) |
| `sdk` | 104 | `["dregg-turn/prover", "dregg-cell/prover"]` | forward + **104 local sites** — the next big domino |
| `verifier` | 7 | `["verifier", "dep:dregg-circuit-prove"]` | **own** circuit-prove dep, **not** a turn forward — a separate `verifier-prover` extraction |

Workspace-wide there are **262** `cfg(feature = "prover")` sites; this design retires
`turn`'s 83 first and lays the pattern for `sdk` (104) and `node` (19).

### 1.3 Two forwards are already dead weight
- **`dregg-cell/prover` is a NO-OP** — `cell/Cargo.toml` has `prover = []` (the
  faithful 8-felt commitment is now unconditional in `dregg-cell`). Every
  `dregg-cell/prover` forward (in `turn`, `sdk`, `node`) can be **deleted** with no
  behavior change.
- `demo` / `teasting` / `tests` define `prover = []` — cosmetic; drop when convenient.

---

## 2. The crate boundary — what moves, what stays

```
        dregg-circuit (verify floor, unconditional)
              ▲                         ▲
              │                         │
        dregg-turn (CORE)         dregg-circuit-prove (produce + heavy verifiers)
   - Turn / TurnReceipt / Builder      ▲            ▲
   - TurnExecutor (VERIFY path)        │            │
   - JournalEntry (pub(crate))         │            │
   - WitnessedReceipt (TYPE)           │            │
   - the injection TRAITS (defined here)            │
   - verify.rs, reversible.rs, pending.rs, umem.rs  │
              ▲                        │            │
              │  (public interface)    │            │
              └──────── dregg-turn-prover ──────────┘
                 - rotation_witness producers (A)
                 - aggregate_bilateral_prover (B)
                 - recursive-bundle producer methods (C)
                 - Custom-leaf modules (D)
                 - exact-FNSP-v3 verifiers/minters (E: the proof half)
                 - shielded-transfer VERIFIER impl (F)
                 - IMPLs of the core injection traits
```

**Dependency direction:** `dregg-turn-prover → dregg-turn` (public interface) `+
dregg-circuit-prove + dregg-circuit`. **`dregg-turn` never depends on
`dregg-turn-prover`.** The core is prover-free and drops the `dregg-circuit-prove`
dependency entirely.

**No circular hazard (verified).** `dregg-circuit-prove`'s dep on `dregg-turn` is a
**`[dev-dependencies]`** entry (`circuit-prove/Cargo.toml:88` is the section header;
line 107 is under it) with **zero non-comment `dregg_turn` uses in
`circuit-prove/src`** — every reference is a doc-comment. So the library edge
`circuit-prove → turn` does not exist; `turn-prover → circuit-prove → turn` is not a
real path. The DAG is clean.

### The runtime seam (this is the mechanism, not just relocation)

`TurnExecutor` **already** carries dependency-inversion seams: `proof_verifier:
Option<Box<dyn ProofVerifier>>`, `custom_effect_registry`, `witnessed_registry`, and
`shadow_observer: Arc<dyn ShadowObserver>` (into which `dregg-exec-lean` injects
`LeanShadowObserver` via `with_shadow_observer`). The woven prover code (Groups E/F)
rides **this same pattern**:

- Core `turn` **defines the trait** (`ShieldedTransferVerifier`, the exact-v3
  admission stays as the already-present installed-token API).
- `turn-prover` **implements** it over `dregg-circuit-prove`.
- The **consumer** (node/sdk) injects the impl at startup — exactly like
  `with_shadow_observer`.
- A `not`-injected core executor **fails the effect closed** — the *same* behavior
  the `#[cfg(not(feature="prover"))]` stub gives today, but now enforced by the type
  system and a crate boundary rather than a cfg.

This is the project-correct default: the core **fails closed by absence of an
injected prover**, and the prover code lives where it is always compiled.

---

## 3. The visibility interface — per-type recommendation

The task frames this as "make `JournalEntry` / write-trace / executor-snapshot `pub`,
or a read-only projection/accessor trait." The survey **narrows the question sharply**,
because the clean groups (A–D) touch **no** private internals. Only E/F do. Per type:

### 3.1 `JournalEntry` + `LedgerJournal` — **keep `pub(crate)`. Do NOT make `pub`.**
Recommendation: **verify-returns-value refactor**, no new journal ABI, no accessor
trait.

Rationale: the undo-log's exhaustive-`match` invariant (`rollback`, `touched_cells`,
`compute_delta_from_journal`, `finalize.rs`, `umem.rs` all match every variant) is
**precisely the bug class we are eliminating.** Promoting `JournalEntry` to `pub`
turns all ~30 variants into public ABI — every future variant becomes a
breaking-change surface *and* re-opens exactly the "downstream non-exhaustive match"
hazard, one crate further out. That is the opposite of the goal.

The only prover path that touches the journal is **F** (`apply_shielded_transfer`
takes `&mut LedgerJournal`). Refactor it so the **prover trait verifies and returns
the validated datum** (the `ShieldedNoteCommitment` to insert), and **core `apply`
does the journal recording** (`journal.record_shielded_note_inserted(...)`). The
prover crate then never sees the journal. Concretely:

```rust
// core turn (defines the seam):
pub trait ShieldedTransferVerifier: Send + Sync {
    /// Verify the hiding uni-STARK; return the note commitment to insert,
    /// or a TurnError. NO journal / ledger access — pure verification.
    fn verify(&self, payload: &ShieldedTransferPayload)
        -> Result<ShieldedNoteCommitment, TurnError>;
}
// core apply: verifier.verify(payload)? then journal.record_shielded_note_inserted(c)
// turn-prover: impl ShieldedTransferVerifier using dregg_circuit_prove::shielded
```

This keeps **journal mutation entirely in core**, needs **zero** new public journal
surface, and the exhaustive matches stay in-crate where a missing arm is a same-build
error. (Fallback if a future prover path genuinely must author journal entries: a
narrow `pub trait JournalRecorder` exposing only the ~5 `record_*` ops it needs —
never the enum. But F does not need it.)

### 3.2 The executor "snapshot" the witness producers read — **no new exposure needed.**
Finding: `rotation_witness` (Group A) reads `RecordKernelState` (a **public** cell
projection) plus the **public** `crate::umem` / `crate::action` modules. It does
**not** read the executor's private mutex state (`note_nullifiers`, `bridged_nullifiers`,
etc.). So "the executor snapshot must become `pub`" is **not required** — a key
de-risking result. Producers ride the public per-cell projection that already exists.

### 3.3 The exact-FNSP-v3 admission slot (`TurnExecutor.exact_fnsp_v3_admission`) —
**make the field UNCONDITIONAL; move the token TYPE to core; keep minting in
turn-prover.**

This field is `#[cfg(feature="prover")]` today and is the **single worst brittleness
source in the file**: because it is a cfg'd struct field, all **three** `TurnExecutor
{ ... }` literals (`new`, `with_budget_gate`, `with_proof_verifier`) carry a cfg line,
and the **struct shape itself is feature-dependent** — the canonical
"compiles-here-breaks-there" trap.

Recommendation: **drop the cfg on the field.** The slot is small one-shot runtime
state (`pending / applied / consumed` opaque tokens); it is not "prover code." Move
the opaque token type `AcceptedFaithfulNoteSpendExactV3` and
`ExactFnspV3AdmissionError` **into core `turn`** as an opaque newtype + its installer
/ taker methods (already `pub`: `install_…`, `take_consumed_…`,
`promote_applied_…`, `restore_…`). Only the **minting** (the verifier that checks the
exact-v3 STARK and *produces* an `Accepted…` token) lives in `turn-prover`. Result:
14 cfg sites deleted, the struct shape becomes **feature-invariant**, and the
apply-path exact-v3 route dispatches on `slot.pending.is_some()` (runtime) instead of
`#[cfg]` (compile-time) — a new effect variant can no longer silently skip it.

### 3.4 `Turn` / `TurnReceipt` / `WitnessedReceipt` / `WitnessBundle` /
`bilateral_schedule` types / `CustomProgramProof` — **already `pub`, no change.**
The producers (B/C) already ride these. `WitnessedReceipt`/`WitnessBundle` **types
stay in core** (the verify path needs them); only their `produce_*` /
`from_components_strict_recursive` methods move to `turn-prover` as free functions or
an extension trait.

**Summary of visibility verdict:** *make almost nothing new `pub`.* One field goes
un-cfg'd (its token type relocates to core), one hot-path method becomes a
verify-returns-value trait. `JournalEntry` stays `pub(crate)`. The clean 4 groups
need nothing.

---

## 4. Consumers — repoint list + churn

### 4.1 The core problem: `turn`'s `default = ["prover"]`
~50 crates just write `dregg-turn = { path = "../turn" }` and inherit `prover`
transitively. After extraction **there is no `prover` feature on `turn`** and its
default drops it. Migration must, per consumer, decide: *does it actually call a
prover API?*

- **Needs proving → add `dregg-turn-prover`** (and inject the impl at startup where
  it drives the executor). Known provers: `node`, `sdk` (→ its own extraction),
  `preflight`, `grain-verify`, `grain-turn` (R3 adapter), `dreggnet-prove-service`,
  `perf`, `lightclient` (rotation leg mint), `dungeon-on-dregg` (private-quest),
  `deos-zed` (in-browser prover), `pg-dregg`, `starbridge-v2` (embedded executor).
- **Core-only → NO CHANGE, lighter build.** The majority (`bridge`, `wire`, `intent`,
  `coord`, `federation`, `app-framework`, most `starbridge-apps/*`, most `dreggnet-*`,
  `observability`, `persist`, `redteam`, `protocol-tests`, `realm-model`, …) use
  `TurnBuilder` / `TurnReceipt` / executor-verify only. They stop pulling
  `dregg-circuit-prove`.
- **Already `default-features = false` (prover-free) → unaffected / cleaner:**
  `wasm`, `dregg-tui`, `sdk-ts/test/rust-verifier`, `starbridge-v2` (wasm side). They
  currently exclude `prover`; now they exclude a whole crate, no cfg.

### 4.2 The forwards to rewrite (the ones that reference `dregg-turn/prover`)
`sdk`, `node`, `lightclient`, `perf`, `grain-turn`, `dungeon-on-dregg` (`private-quest`),
`deos-zed` (wasm `features=["prover"]`), `pg-dregg`, `preflight`, `grain-verify`.
Each: replace `"dregg-turn/prover"` in its own `prover`/feature with a
`dregg-turn-prover` **dependency** (optional, behind the crate's own feature if it
keeps one) and drop the dead `"dregg-cell/prover"`.

### 4.3 Trivial vs real
- **Trivial forwards (delete/rewrite mechanically), no local prover code to extract:**
  `lightclient` (3 sites are re-export gates), `perf` (3), `demo`/`teasting`/`tests`
  (`prover=[]`, cosmetic), the `dregg-cell/prover` no-op everywhere.
- **Real gated code (needs its own extraction, later dominoes):** `sdk` (104),
  `node` (19), `verifier` (7 — but `verifier` owns its own `dep:dregg-circuit-prove`,
  so it is a *separate* `verifier-prover` extraction, not a turn forward).

---

## 5. Staging

**Principle (from the record): prove the pattern on the lowest-risk chunk first,
verify the core compiles-always at the source, then propagate.**

- **PR1 — establish `dregg-turn-prover` + the always-compiles guarantee (Group D + B).**
  Create the crate. Move the **four self-contained Custom-leaf modules** (D:
  `descent_census_custom`, `private_preference_custom`, `private_graph_rewrite_custom`,
  `private_graph_rewrite_history`) and the **aggregate bilateral prover** (B) — all
  touch **only `turn`'s public interface** and B already ships `not(prover)` stubs.
  Re-export from `dregg_turn_prover::*`. Delete the corresponding `#[cfg]` module
  decls / re-exports from `turn/src/lib.rs`. **Cement the visibility verdict (§3) in
  this PR's doc:** `JournalEntry` stays `pub(crate)`; the seam is verify-returns-value
  + runtime injection (first *exercised* in PR2). **Acceptance gate:** `cargo build -p
  dregg-turn` is now **prover-free and has no `dregg-circuit-prove` edge**; `cargo
  build -p dregg-turn-prover` builds; the workspace builds. This is the "brittleness
  caught at the source" proof — turn-prover is always compiled as itself.
  *(D touches no journal, so the JournalEntry decision is documented here and
  first-exercised in PR2; if the reviewer wants the journal seam exercised in PR1,
  swap the first chunk to F — higher risk, not recommended.)*

- **PR2 — the woven hot-path seam (Group F, then E).** Introduce
  `pub trait ShieldedTransferVerifier` in core; move the impl to `turn-prover`;
  refactor `apply_shielded_transfer` to verify-returns-value with core doing the
  journal record (§3.1). Then un-cfg the exact-v3 admission field, relocate its token
  type to core, and move the exact-v3 **verifiers/minters** (E) to `turn-prover`
  (§3.3). Wire injection through the executor's existing seam; `not`-injected =
  fail-closed. This retires the 14 `executor/mod.rs` + apply/execute sites.

- **PR3 — the remaining producers (A + C) + `mint_transfer_proven_receipt` +
  `with_custom_program_proofs`.** Move rotation-witness producers and the
  recursive-bundle `produce_*` methods (types stay in core). Turn's own prover surface
  is now empty; **delete the `prover` feature + the `dregg-circuit-prove` optional dep
  from `turn/Cargo.toml`, and the dead `dregg-cell/prover`.**

- **PR4+ — propagate to consumers, one domino at a time.** Repoint the §4.2 forwards
  to `dregg-turn-prover`; audit the ~50 default-inheritors and add the crate only
  where a prover API is actually called (grep each for prover-API symbols BEFORE
  dropping the transitive edge). Then repeat the whole pattern for `sdk` (104) and
  `node` (19) as their own `-prover` crates; treat `verifier` (7, own circuit-prove)
  as a separate `verifier-prover`.

---

## 6. Risks

1. **The no-default-features / wasm / zkvm core MUST still build.** After PR1–3, core
   `turn` has no prover code and no `dregg-circuit-prove` dep. The **existing
   `#[cfg(not(feature="prover"))]` stubs are the safety net** — they already prove the
   core compiles and fails-closed prover-free; the extraction makes that stub behavior
   *permanent and unconditional*. **CI gate:** build `dregg-turn` standalone (it is
   now the only "core" config) on native **and** `wasm32-unknown-unknown`; the
   `dregg-tui` / `wasm` / `sdk-ts-rust-verifier` prover-free consumers are the
   canaries.
2. **In-browser proving is a live config.** `deos-zed` / `starbridge-v2` build
   `dregg-turn` with `default-features=false, features=["prover"]` on wasm32 — a
   **wasm prover**. `dregg-turn-prover` therefore **MUST stay wasm32-buildable** (no
   native-only deps); `dregg-circuit-prove` already builds for wasm there, so
   turn-prover inherits the constraint but does not add to it. Test wasm32 in CI.
3. **Circular-dep hazard — checked, clear.** `circuit-prove → turn` is **dev-only**
   with zero library uses (§2), so `turn-prover → circuit-prove → turn` is not a real
   library path. Re-confirm after PR3 that nothing in `turn-prover` re-introduces a
   `turn → turn-prover` edge (the injection trait lives in **core**, impl in
   turn-prover, both consumed by node — no cycle).
4. **`threshold-sig` is SEPARATE — keep it a feature for now.** It gates a *verify*-side
   BLS12-381+KZG committee verifier (`hints`/`ark-serialize`/`ark-ff`) for the
   governance `Authorization::Custom` discharge; it is default-on and off for wasm
   (arkworks). It is the *same* optional-dep+cfg anti-pattern, but it is a **localized
   leaf verifier**, not woven into the executor struct the way `prover` is, so it does
   **not** carry the same brittleness. Do not expand this campaign to it; a follow-up
   `turn-threshold-verifier` crate is the natural sequel once the pattern is proven.
5. **Dropping `turn`'s `default=["prover"]` is the loud step.** ~50 consumers inherit
   prover transitively; some may call a prover API without declaring it and will fail
   to compile once default drops it. Mitigation: the PR4 audit greps each consumer for
   prover-API symbols and adds `dregg-turn-prover` **before** removing the transitive
   edge. Expect this to surface a handful of "silently depended on default prover"
   crates — that surfacing is the point.
6. **The `dregg-cell/prover` no-op forward** can be deleted anywhere it appears
   (`turn`, `sdk`, `node`) — verified `cell` has `prover = []`. Do it in the same PRs
   to avoid confusion.

---

## 7. Concrete first-PR scope

**Deliverable:** `dregg-turn-prover` crate holding the four Custom-leaf modules (D)
and the aggregate bilateral prover (B), always compiled, `turn` core prover-free.

**`turn-prover/Cargo.toml` (sketch):**
```toml
[package]
name = "dregg-turn-prover"
version.workspace = true
edition.workspace = true
# ...inherit workspace...
description = "Proof PRODUCTION for dregg turns (rotation witnesses, bilateral aggregation, Custom-leaf proofs). Depends on dregg-turn's PUBLIC interface; dregg-turn never depends on this."

[dependencies]
dregg-turn = { path = "../turn" }            # PUBLIC interface only
dregg-circuit = { path = "../circuit" }
dregg-circuit-prove = { path = "../circuit-prove" }
dregg-cell = { path = "../cell" }
dregg-types = { path = "../types" }
serde = { workspace = true }
# (no `prover` feature — the crate IS the prover)

[lints]
workspace = true
```

**Moves in PR1:**
- `turn/src/{descent_census_custom,private_preference_custom,private_graph_rewrite_custom,private_graph_rewrite_history}.rs`
  → `turn-prover/src/` (drop the `#![cfg(feature="prover")]` inner attribute; the crate
  is unconditionally the prover). Zero `turn`-internal edits — these touch no `crate::`
  internals.
- `turn/src/aggregate_bilateral_prover.rs` → `turn-prover/src/`; its `not(prover)`
  error stubs collapse away (no more cfg). Repoint its `use crate::{bilateral_schedule,
  error::TurnError, turn::Turn, witnessed_receipt::WitnessedReceipt}` to
  `use dregg_turn::{...}` (all already `pub`).
- Delete the matching `#[cfg(feature="prover")] pub mod …` and `#[cfg(feature="prover")]
  pub use …` lines from `turn/src/lib.rs` (D-modules + the `aggregate_bilateral_prover`
  re-export).

**Not in PR1:** anything touching `TurnExecutor`, `apply`, the journal, or the exact-v3
slot (Groups E/F, PR2) and the rotation/recursive producers (A/C, PR3). `turn`'s
`prover` feature is **not deleted yet** (PR3) — after PR1 it still gates A/C/E/F; PR1
only proves the crate + the always-compiled property on the cleanest chunk.

**Acceptance gate (buildable + green):**
- `cargo build -p dregg-turn-prover` — builds.
- `cargo build -p dregg-turn` (default) — builds, **still** carries the residual
  `prover` feature for A/C/E/F (deleted in PR3); the four D-modules + B are gone from it.
- `cargo build -p dregg-turn --no-default-features` — builds prover-free (unchanged
  safety net).
- The workspace builds; any consumer that imported the moved modules via
  `dregg_turn::private_preference_custom::…` repoints to `dregg_turn_prover::…`
  (grep first — these are niche Custom-leaf demos, expect ~0–3 call sites).
- **The proof the whole campaign exists for:** add a throwaway variant to one of the
  moved modules' internal enums and confirm the error lands in **`cargo build -p
  dregg-turn-prover`** (at the source), not four crates away.
