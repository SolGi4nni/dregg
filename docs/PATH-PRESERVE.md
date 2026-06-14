# PATH-PRESERVE — the soundness-core build that makes the rotated path TOTAL (unblocks C7)

> **Decision (ember, 2026-06-14): PRESERVE.** Every finalized turn must keep carrying a
> per-turn proof on the ROTATED path — no v1 fallback — so the ARGUS light-client-unfoolability
> guarantee stays intact. *"we need to build path-preserve for SURE. any other decision wouldn't
> be dregg."* This doc is the **staged, persvati-green build plan**. It is NOT the build; it is the
> gating plan so C7 (delete the legacy v1 effect-VM proof) cannot ship RED.

This doc is grounded against the CODE at HEAD (branch `main`, ~2026-06-14). Where a cross-ref
doc's line number had drifted, the corrected `path:line` is given inline and flagged **[LINE-FIX]**.

---

## 0. Orientation — where the v1 fallback actually lives, and the ONE crux

The public claim PATH-PRESERVE protects: *every committed state transition is proven* — and
on the ROTATED path (the IR-v2 R=24 registry is the VK-epoch default). The fallback that
currently violates "rotated, no v1" for three turn shapes is the v1 effect-vm leg inside
`prove_full_turn`:

- **The v1 fallback leg**: `sdk/src/full_turn_proof.rs:1185-1202` — `if rotated_effect_pi.is_none()
  { … prove_effect_vm_with_cutover(&witness.effects, effect_trace, effect_pi) … label: "effect-vm" }`.
  It runs whenever `witness.rotation` is `None` (no rotation witness was built). The rotated leg
  is attached at `:1151-1181` (`label: "effect-vm-rotated"`), recursion-gated.

- **THE CRUX — the verifier expects EXACTLY ONE effect-vm leg**:
  `sdk/src/full_turn_proof.rs:1688-1693` — `let effect_sub = proof.composed.sub_proofs.iter()
  .find(|sp| sp.label == "effect-vm" || sp.label == "effect-vm-rotated").ok_or(…)?`. **[LINE-FIX]**
  the cross-refs (`V1-DELETION-MANIFEST.md`, `HORIZONLOG.md`) cite the `.find` at `1688-1719`; the
  actual `.find` call is at **line 1692** (the binding block is 1688-1693; it reads OLD/NEW at
  `:1709-1710` and the commitment-mismatch teeth fire at `:1712-1725`). Path-PRESERVE turns this
  single-leg finder into an N-leg collect+chain-check.

The rotation witness is `None` (⇒ v1 runs) precisely when one of the gates in
`node/src/turn_proving.rs` rejects. **[LINE-FIX]** the cross-refs cite these gates at
`turn/src/turn_proving.rs` — the file is actually **`node/src/turn_proving.rs`** (there is no
`turn/src/turn_proving.rs`).

The single load-bearing structural fact that makes PRESERVE *composition, not new circuitry*:

> **`prove_vm_descriptor2` proves exactly ONE cohort descriptor per call**
> (`circuit/src/descriptor_ir2.rs:3832`, `desc: &EffectVmDescriptor2`), and the rotated prover
> already proves a **homogeneous multi-effect run** natively — "the rotated per-effect constraint
> family natively holds over a multi-row trace of its own effect (the PI pins bind first-row pre /
> last-row post)" (`sdk/src/full_turn_proof.rs:860-883`). It **fails closed** on a heterogeneous or
> empty turn (`:873-883`).

So a heterogeneous turn's missing capability is **not** a missing constraint — it is the absence
of (a) a split into homogeneous runs, (b) per-run pre/post-state threading, (c) N attached legs,
and (d) a verifier that chains them. **Every one of those four is Rust composition over
already-proven, already-Lean-emitted per-cohort legs.** This is the LAW-#1 verdict (§5), pinned
early because it governs the whole plan.

---

## 1. The exact gap census (the 3 shapes)

The node projects **ONE finalized turn over `signed_turn.turn.agent` with the FULL
`call_forest.total_effects()` projected onto that actor** — `node/src/blocklace_sync.rs:2605-2611`:

```rust
let effects: Vec<dregg_turn::Effect> = signed_turn.turn.call_forest
    .total_effects()           // forest.rs:228 — depth-first ALL effects, NO per-effect split
    .into_iter().cloned().collect();
```

`total_effects()` (`turn/src/forest.rs:228-234`) is a flat depth-first collection of every effect
in the forest — there is **NO per-effect / per-cohort decomposition** that would make a
heterogeneous turn vacuous. The whole `effects` slice flows into one `prove_and_verify_finalized_turn*`
call and one `convert_effects_to_vm` projection. The projector `convert_effects_to_vm`
(`sdk/src/cipherclerk.rs:5488-5527`) pushes **one `VmEffect` per matching effect** — a `Transfer`
+ `SetField` from the same actor yields a 2-element heterogeneous `vm_effects` (Transfer arm
`:5491-5503`, SetField arm `:5504-5509`). Heterogeneous is therefore **ordinary and reachable.**

### Shape 1 — Heterogeneous turns (ORDINARY, reachable)
- **What:** one actor doing >1 distinct cohort effect in a turn (Transfer AND SetField, etc.).
- **The gate that forces v1:** `cohort_ok` in BOTH rotation-witness builders —
  `node/src/turn_proving.rs:380-387` (self-sovereign) and `:472-479` (capability). **[LINE-FIX]**
  the cross-refs cite `380-387/468-479`; the `cohort_ok` *computation* is `472-479` (the
  `vm_effects`/`lead_name` setup it reads begins at `:468`). The gate:
  ```rust
  let lead_name = vm_effects.first().and_then(rotated_descriptor_name_for_effect);
  let cohort_ok = lead_name.is_some()
      && vm_effects.iter().all(|e| rotated_descriptor_name_for_effect(e) == lead_name);
  if !cohort_ok { return None; }   // ⇒ caller passes None ⇒ v1 fallback runs
  ```
  Even if a witness slipped through, the prover itself fails closed at
  `sdk/src/full_turn_proof.rs:873-883` ("heterogeneous multi-effect turn (one rotated descriptor
  per proof)").
- **Reachable on the live finalized path:** YES. Routine SDK-projector output.

### Shape 2 — Non-synthetic-field cells (reachable)
- **What:** any actor cell with a non-zero field or a non-empty c-list, where the rotated witness
  gate currently demands a pristine cap-less `CellState::new` pre-state so OLD_COMMIT agrees.
- **The gate that forces v1:**
  - self-sovereign: `cell_is_synthetic_shaped`, `node/src/turn_proving.rs:353-357`:
    ```rust
    let cell_is_synthetic_shaped = before_cell.state.balance() == pre_balance as i64
        && before_cell.state.nonce() == pre_nonce
        && before_cell.state.fields.iter().all(|f| *f == [0u8; 32])
        && compute_canonical_capability_root_felt(&before_cell.capabilities)
            == empty_capability_root();
    if !cell_is_synthetic_shaped { return None; }
    ```
  - capability: `cell_matches_v1_prestate`, `node/src/turn_proving.rs:445-448` (same shape, but
    requires `cell_cap_root == pre_capability_root` instead of the EMPTY root — a cap-gated turn's
    whole point is a non-empty c-list, so the cap path already tolerates a real cap root; it still
    forces **zero fields**).
- **Why the gate exists:** the welded scalars (`r0↔balance_lo · r1↔nonce · r2↔balance_hi ·
  r3..r10↔fields[0..8] · cap_root`) are OVERRIDDEN per-row from the v1 sub-trace by
  `trace_rotated::fill_block` (`circuit/src/effect_vm/trace_rotated.rs:294-303`). The OLD_COMMIT pin
  (PI 34) is `r0[BEFORE_BASE + B_STATE_COMMIT]`, computed from THOSE welded scalars
  (`trace_rotated.rs:234, :331`). The gate's worry is that if the real cell's fields are non-zero
  while the v1 `initial_vm_state` is `CellState::new` (zero fields), the rotated OLD_COMMIT and the
  v1 leg would attest *different* commitments. **§4 shows this worry is mostly already moot** —
  the rotated leg welds from the v1 *trace*, not from the synthetic cell — so the lift is small.
- **Reachable on the live finalized path:** YES. Any cell that has ever had a field set or holds a
  capability. The self-sovereign path's `prove_and_verify_finalized_turn` seeds
  `CellState::new(pre_balance, pre_nonce)` at `:521`, zero fields; the capability path seeds
  `CellState::with_capability_root(…)` at `:819`, real cap root but zero fields. Real cells with
  fields exist (apps set fields).

### Shape 3 — NoOp-only turns (LIKELY UNREACHABLE on this path — document why, then confirm)
- **What:** a turn whose entire projected `vm_effects` is empty / a single `Effect::NoOp`.
- **The relevant code:** the NoOp injection at `turn/src/executor/effect_vm_bridge.rs:556-558`:
  ```rust
  if vm_effects.is_empty() { vm_effects.push(dregg_circuit::effect_vm::Effect::NoOp); }
  ```
  is inside `collect_effects` — a **per-cell executor projector** in `turn/src/executor/`, a
  DIFFERENT projector that is NOT on the FullTurnProof path.
- **The FullTurnProof path's projector** is `AgentCipherclerk::convert_effects_to_vm`
  (`sdk/src/cipherclerk.rs:5488`), used at `node/src/turn_proving.rs:512/685/817` and
  `blocklace_sync.rs:2605`. **It does NOT inject NoOp** — if no effect matches the actor it returns
  an empty `vm_effects`. With an empty `vm_effects`:
  - the cohort gate `lead_name = vm_effects.first()…` is `None` ⇒ `cohort_ok == false` ⇒ rotation
    `None` ⇒ today v1 runs (and `generate_effect_vm_trace` on an empty slice yields an empty trace,
    which `trace_rotated.rs:204-206` rejects — so the rotated path *cannot* take an empty turn).
  - `rotated_descriptor_name_for_effect(&Effect::NoOp)` is `None` (`trace_rotated.rs:467, :579`).
- **Verdict:** a NoOp-only / empty-projection turn is **not provable on EITHER leg as a state
  transition** (it makes no state change). The honest question is whether such a turn ever reaches
  `prove_and_verify_finalized_turn*` on the finalized path at all.
  - **Confirm at build-time (Phase 0 task):** instrument / assert that `convert_effects_to_vm`
    never returns empty on the finalized commit path (i.e. the node only proves turns with ≥1
    actor-affecting effect). If empty projections DO reach the path, the correct PRESERVE answer is
    **a one-row identity rotated leg** (OLD_COMMIT == NEW_COMMIT, net_delta 0, a `NoOp` cohort
    descriptor) rather than v1 — this is a *tiny* addition (a single Lean `noOpVmDescriptor2R24`
    + its weld), and it is the ONLY place in this plan where a new Lean descriptor *might* be
    needed (§5). If empty projections do NOT reach the path (the likely case), Shape 3 is a
    non-issue: document the invariant and add a `debug_assert!(!vm_effects.is_empty())` guard so a
    future regression is loud.

---

## 2. The data-structure changes (single-leg → N-leg; the chain-witness builder)

### 2.1 What carries the N legs
`FullTurnProof.composed.sub_proofs: Vec<AttachedSubProof>` (`sdk/src/full_turn_proof.rs`, the
`ComposedProof` struct) is ALREADY a `Vec` — so **no struct field changes** to hold N legs. Today
it holds exactly one `"effect-vm"` OR one `"effect-vm-rotated"`. Path-PRESERVE attaches **N
`"effect-vm-rotated"` legs**, one per homogeneous cohort-run, in chain order. Each leg is the
existing `AttachedSubProof { label: "effect-vm-rotated", proof_bytes, sub_public_inputs: rot_pi,
vk_hash }` (the exact shape built at `:1167-1177`).

> **Ordering is load-bearing and must be explicit.** `sub_proofs` order is the chain order
> s0→s1→…→sN. The verifier (§3) reads the rotated legs **in `sub_proofs` order**; the builder MUST
> push them in run order. (Other legs — authorization / membership / non-revocation / cap-membership
> — are interleaved after; the verifier filters by label, so their position is free, but the
> rotated legs' relative order is the chain.)

### 2.2 The run-splitter
A new pure function (Rust, verifier-side-eligible — see §5), e.g. in `circuit::effect_vm::trace_rotated`
or `sdk`:

```rust
/// Split a homogeneous-or-heterogeneous VmEffect sequence into maximal runs where every effect in
/// a run resolves to the SAME rotated cohort descriptor. NoOp / non-cohort effects (descriptor
/// None) terminate a run and are handled per the §1 Shape-3 invariant.
pub fn split_into_cohort_runs(effects: &[VmEffectKind]) -> Vec<Range<usize>>;
```

derived purely from `rotated_descriptor_name_for_effect` (`trace_rotated.rs:464`). A homogeneous
turn yields ONE run (so the homogeneous case is byte-identical to today's single rotated leg — this
is what makes Phase 1 a no-op for existing green turns). A `Transfer,SetField,Transfer` turn yields
THREE runs `[0..1], [1..2], [2..3]` (Transfer and SetField are different cohorts; consecutive same
cohort would coalesce).

### 2.3 The chain-witness builder (the per-run OLD/NEW threading — the real new work)
The intermediate states s1…s_{N-1} are **synthetic mid-points** the executor never materialized
as `Cell`s. The builder must thread them. Concretely, replace the single
`RotationTurnWitness` with an **ordered `Vec<RotationTurnWitness>`**, one per run, built as:

```text
s0 := initial_vm_state                          // the real pre-state (CellState::new / with_capability_root)
for k in 0..N:
    run_effects := effects[runs[k]]
    (trace_k, pi_k) := generate_effect_vm_trace(s_k, run_effects)   // threads s_k → s_{k+1}
    s_{k+1} := state read off pi_k[NEW_COMMIT] / the run's last new_state
    rot_k := RotationTurnWitness for run k over (before=s_k, after=s_{k+1})
```

Key code facts that make this threading correct **without re-running the executor**:
- `generate_effect_vm_trace` (`circuit/src/effect_vm/trace.rs:88`, `:503` `current_state`, `:508`
  loop) threads `current_state → new_state` **per effect row**, recomputing `state_commitment` each
  row. Running it on `run_effects` starting from `s_k` produces exactly the sub-trace for run k and
  `s_{k+1}` as its last `new_state`. This is the SAME generator the rotated trace builder opens with
  (`trace_rotated.rs:203`), so the rotated OLD_COMMIT/NEW_COMMIT pins per run are derived from these
  real per-run boundary states.
- The welded scalars per row come from THAT run's v1 sub-trace (`fill_block`,
  `trace_rotated.rs:294-303`), so they're automatically consistent with `s_k`/`s_{k+1}` — the
  builder does NOT hand-replay balance/nonce/field math.

**The producer-witness subtlety (the one genuinely new mint).** `rotation_witness::produce`
(`turn/src/rotation_witness.rs`) reads a single cell's `RecordKernelState` (balance/nonce/fields/
cap_root/lifecycle/epoch/height) + the turn-invariant `cells_root`/`iroot`. For run k the
welded limbs are overridden from the v1 trace (so they need not be "real"), but the
**witness-carried** limbs (`cells_root`, `iroot`, `lifecycle`, `epoch`, `committed_height`,
`r11..r23`, and critically `r23 = authority digest`) come from the producer witness `w`. For the
chain:
- `cells_root`, `iroot`, `lifecycle`, `epoch`, `r11..r23` are **turn-invariant** (the same cell's
  turn-level boundary view — `rotation_witness.rs:46-49` "the same for every effect row of the
  turn"). So a SINGLE producer witness (the real before-cell's) can be REUSED for the before-block
  of every run, and the real after-cell's for the after-block of the LAST run.
- For the *interior* run boundaries the after-block of run k and before-block of run k+1 must agree
  on the witness-carried limbs. Since those limbs are turn-invariant, the cleanest construction is:
  **before-block witness = the real before-cell's producer witness for ALL runs; after-block
  witness = the real before-cell's producer witness for interior runs and the real after-cell's
  for the final run** — EXCEPT the per-run welded scalars (which `fill_block` overrides from each
  run's v1 sub-trace) carry the changing balance/nonce/fields. This mirrors the existing cap-less
  note-spend construction at `node/src/turn_proving.rs:320-333` (`before == after`, per-row welds
  carry the post-state). **Build-time obligation:** the chained differential (§6) must confirm the
  interior `s_k` welded scalars + invariant witness limbs reproduce the monolithic per-row trace
  exactly — this is where a hand-replay bug would surface.

### 2.4 The conservation read across the chain
`prove_full_turn`'s conservation leg currently reads `net_delta` from the single effect leg PI
(`sdk/src/full_turn_proof.rs:1290-1302`, reads `NET_DELTA_MAG(16)/NET_DELTA_SIGN(17)`). With N
legs, `net_delta` is **per-run** (each run's `generate_effect_vm_trace` accumulates only its own
effects' delta — `trace.rs:506 net_delta`). The conservation obligation must become **Σ_k
net_delta(leg_k) == expected_net_delta**, decoded via `effect_vm::encode_net_delta`
(`:1299-1302`). This is a verifier/prover-side sum over already-bound PIs — no circuit change.

---

## 3. The verifier change (`verify_full_turn` collect-and-chain-check)

Replace the single-leg `.find` at `sdk/src/full_turn_proof.rs:1688-1693` with a **collect**, then
a **chain-check**. The existing OLD/NEW commitment teeth (`:1709-1725`) move to operate on the
chain endpoints. Precisely:

### 3.1 Collect (replaces the `.find`)
```rust
let effect_legs: Vec<&AttachedSubProof> = proof.composed.sub_proofs.iter()
    .filter(|sp| sp.label == "effect-vm" || sp.label == "effect-vm-rotated")
    .collect();
if effect_legs.is_empty() { return Err(MissingComponent("effect-vm".into())); }
```
Each leg is already cryptographically re-verified in the step-3 loop (`:1562-1680`); the
`"effect-vm-rotated"` arm (`:1591-1597`) resolves each leg's cohort descriptor selector-bound and
verifies via the audited IR-v2 batch verifier. **No change to step 3** — it already loops over ALL
sub-proofs, so N rotated legs are each verified. (Confirm: the arm at `:1591` is `#[cfg(feature =
"recursion")]`; under `not(recursion)` no rotated leg exists and the collect yields the single v1
leg — see §7 wasm note.)

### 3.2 Chain-check (the new adjacency + endpoint logic)
Read each leg's OLD/NEW from its PI. The rotated leg carries OLD_COMMIT at `pi::OLD_COMMIT` (offset
0) and NEW_COMMIT at `pi::NEW_COMMIT` (offset 4) — the **v1 prefix `[0..34)` is carried unchanged on
the rotated leg** (`trace_rotated.rs:233` `dpis = pis[..V1_PI_COUNT]`), and the verifier already
relies on this (`:1696-1702`, `min_pi = V1_PI_COUNT` for rotated). The verifier currently checks
**position-0 only** (`:1709-1710` reads the single felt `pi[OLD_COMMIT]`). Keep that convention for
adjacency:

```rust
// endpoints
let first = effect_legs.first().unwrap();
let last  = effect_legs.last().unwrap();
if first.sub_public_inputs[pi::OLD_COMMIT] != expected_old_commit {
    return Err(CommitmentMismatch { which: "old_commitment", … });   // moved from :1712
}
if last.sub_public_inputs[pi::NEW_COMMIT] != expected_new_commit {
    return Err(CommitmentMismatch { which: "new_commitment", … });   // moved from :1719
}
// adjacency: leg_k.OLD == leg_{k-1}.NEW
for w in effect_legs.windows(2) {
    let prev_new = w[0].sub_public_inputs[pi::NEW_COMMIT];
    let this_old = w[1].sub_public_inputs[pi::OLD_COMMIT];
    if this_old != prev_new {
        return Err(FullTurnVerifyError::ChainBreak {
            at: /* index */, prev_new, this_old,
        });   // NEW error variant
    }
}
```

`ChainBreak` is a new `FullTurnVerifyError` variant (the only verifier-API addition). The
single-leg case (N=1) collapses to exactly today's two endpoint checks with no adjacency window —
**byte-identical behavior for homogeneous turns**, which is what keeps Phase 3 green for the
existing fleet.

### 3.3 effects_hash re-derivation across the chain
**Critical finding.** `EFFECTS_HASH` at PI[8] (`pi.rs:24` `EFFECTS_HASH_BASE`) is the hash of
**that leg's effects subset** (`compute_effects_hash_4(effects)`, `trace.rs:941/1118`), NOT the
whole turn. And the whole-turn anchor `EFFECTS_HASH_GLOBAL` at PI[29] (`pi.rs:94`) is **NOT
populated on the live path** — `generate_effect_vm_trace` uses `EffectVmContext::default()`
(`trace.rs:99-103`), so `effects_hash_global = [ZERO;4]` and `turn_hash = [ZERO;4]`
(`trace.rs:126, :353`; filled only at `:1157-1158` from a non-default context the live path doesn't
supply). Two consequences and the chosen design:

- **The effects-binding obligation.** The verifier must bind the N legs to the WHOLE turn's
  effects, not just per-run subsets, else a prover could attach legs for a *different* effect
  multiset that happens to chain. `compute_effects_hash` (`helpers.rs:186`) is a **sequential
  Poseidon2 sponge — order-sensitive** (and `compute_effects_hash_4` derives 4 felts from it,
  `helpers.rs:405-413`). So the whole-turn binding is order-sensitive too.
- **Chosen design (no circuit change):** the verifier **re-derives the run split from the actor's
  projected effects** and checks each leg's PI[8] equals `compute_effects_hash_4(run_effects_k)` for
  run k, AND that the concatenation of runs equals the actor's full projected `vm_effects`. The
  verifier already has the turn's effects available on the bound path (it is handed
  `expected_old/new_commit`; the caller — `prove_and_verify_finalized_turn*` — has `vm_effects` and
  passes them, or the bound entry takes them). Concretely, add a `expected_effects: &[VmEffectKind]`
  (or the run boundaries) to a new bound entry `verify_full_turn_chained` (§7 Phase 3) so the
  verifier recomputes `split_into_cohort_runs(expected_effects)` and pins each leg's PI[8].
  *Alternative considered and rejected for now:* populate `EFFECTS_HASH_GLOBAL` (PI[29], already in
  the carried prefix) on every leg to the same whole-turn hash and pin equality across legs — this
  needs the live path to thread a non-default `EffectVmContext`, a broader change touching the
  generator call sites. The re-derive-from-effects design is local to the verifier and the SDK
  caller, so it is the staged choice; revisit if a future need wants the global anchor anyway.

### 3.4 net_delta across the chain
Replace the single-leg conservation read (`:1290-1302`) with **Σ_k net_delta(leg_k)** as in §2.4.
The verifier's conservation check (when `expected_cap_membership`/conservation is in play) and the
prover's `prove_full_turn` conservation block both sum the per-leg `NET_DELTA_MAG(16)/SIGN(17)`.

### 3.5 The note-spend step-8 read (must stay correct under N legs)
Step 8 (`:1917-1963`) reads the spend nullifier from `effect_sub` (the single leg today). Under N
legs the nullifier is on whichever run carries the (single) `NoteSpend` (the single-spend invariant
holds — `trace_rotated.rs:264-275` and the cap-less builder gate `:312-318` keep ≤1 spend). The
collect must surface **the rotated leg whose `sub_public_inputs.len() >= ROT_NULLIFIER_PI_COUNT`**
(the 39-PI note-spend leg, `trace_rotated.rs:107`) as `effect_sub` for step 8; if no leg has the
fifth PI slot, there is no spend (zero sentinel, as today `:1937-1939`). This is a small refinement
of step 8's leg selection — it must pick the note-spend leg from the chain, not assume leg-0.

---

## 4. The non-synthetic-cell rotated witness (lift the synthetic-shape gate)

The gate (`cell_is_synthetic_shaped` `:353-357`, `cell_matches_v1_prestate` `:445-448`) refuses any
cell with non-zero fields (and, for self-sovereign, a non-empty c-list). The **lift** rests on a
fact already true in the trace builder:

> The rotated block's welded scalars are filled **per-row from the v1 sub-trace's own state block**
> (`trace_rotated.rs:294-303` `fill_block`: `row[base+1] = row[state_base + state::BALANCE_LO]`,
> …, fields `:304+`, `cap_root`), and the OLD_COMMIT pin is `r0[BEFORE_BASE + B_STATE_COMMIT]`
> computed from those welded scalars (`:331`). So the rotated OLD_COMMIT agrees with the **v1
> trace** by construction *regardless of whether the cell is synthetic* — the welds copy the v1
> state block, fields and all.

The gate's real (and correct) worry today is narrower: it is comparing the rotated leg against the
**v1 `initial_vm_state`** that `prove_and_verify_finalized_turn*` seeds — `CellState::new(pre_balance,
pre_nonce)` (`:521`, zero fields, empty cap root) or `CellState::with_capability_root(…)` (`:819`,
real cap root, zero fields). If the real cell has non-zero fields but `initial_vm_state` has zero
fields, the v1 OLD_COMMIT (which the verifier pins as `expected_old_commit`,
`turn_proving.rs:522/687/820`) would NOT match the rotated OLD_COMMIT welded from the real cell.
**The fix is to seed the Effect-VM pre-state from the REAL cell, not a synthetic one**, so the v1
OLD_COMMIT the verifier expects and the rotated OLD_COMMIT the leg attests are the same object:

### 4.1 The change
- Add `CellState::from_cell(before_cell)` (or reuse an existing real-cell→CellState path) that
  carries the cell's **real fields + real cap_root + balance + nonce** into `initial_vm_state`, so
  `old_commit = initial_vm_state.state_commitment` (`turn_proving.rs:522`) binds the real pre-state.
  The producer witness's welded limbs then match it on row 0 by construction.
- **Replace** `cell_is_synthetic_shaped` / `cell_matches_v1_prestate` with a gate that checks the
  cell's real state is faithfully represented by the chosen `CellState` (a *representability* check,
  not a *zero-fields* check): balance/nonce fit, fields map into the 8-field block
  (`state::fields[0..8]`), cap_root equals the canonical root. The gate stops being "is this cell
  pristine?" and becomes "can the Effect-VM CellState losslessly hold this cell?" — which a normal
  app cell can.
- **The authority-digest faithfulness already exists** for the capability path: `r23 =
  compute_authority_digest_felt(before_cell)` is witness-carried (NOT welded), folding the real
  cell's identity/permissions/VK/delegate/program into the rotated commit pins
  (`turn_proving.rs:406-415`, `rotation_witness.rs:51-52`). The lift must keep r23 fed by the real
  cell (it already is — the call sites pass `full_turn_pre_cell`, `blocklace_sync.rs:2638-2651`).

### 4.2 What the differential must show for the lift
That for a field-bearing / cap-holding real cell, `CellState::from_cell(before_cell).state_commitment`
== `r0[BEFORE_BASE + B_STATE_COMMIT]` of the rotated trace (OLD_COMMIT agreement), and the same at
the after-cell for NEW_COMMIT. This is the existing `effect_vm_rotation_flip.rs`
cell≡circuit differential (`circuit/tests/effect_vm_rotation_flip.rs`,
`rotation_witness.rs:12-17`) **extended to a non-synthetic cell** (today it likely runs the
synthetic shape). One new differential case: a cell with `fields[0] = 0x07…`, a non-empty c-list,
proves rotated and OLD/NEW agree — the inverse of the current
`flow_b_non_synthetic_cell_falls_back_to_v1` test (`turn_proving.rs:1056-1084`), which today asserts
`rotation.is_none()` and must FLIP to `is_some()` + a verifying proof.

> **Note:** Shape 2 (non-synthetic cell) and Shape 1 (heterogeneous) are *orthogonal* and compose:
> a field-bearing cell doing Transfer+SetField needs BOTH the lifted witness (§4) AND the chain
> (§2/§3). Sequence §4 before the chained-prover cutover so the chain is exercised on real cells.

---

## 5. The LAW-#1 verdict — DEFINITIVE

**Chaining needs NO new Lean-emitted descriptor/AIR/constraint kind for the heterogeneous and
non-synthetic shapes.** It is **Rust verifier-side composition + a differential** over legs that
each already prove through a Lean-emitted per-cohort descriptor. Justification, point by point:

1. **Each run already has a Lean-emitted descriptor.** Every run is homogeneous, so it proves
   through one of the 36 cohort members in `V3_STAGED_REGISTRY_TSV`
   (`circuit/src/effect_vm_descriptors.rs`), each emitted from
   `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` (the registry's provenance,
   `ROTATION-CUTOVER.md §EXEC.3` table; the Rust twin is the sha-256-pinned TSV). The per-cohort
   first-row-pre/last-row-post PI pins are Lean constraints (`pi_binding`), unchanged.
2. **The split is pure data over an existing resolver.** `split_into_cohort_runs` is a fold over
   `rotated_descriptor_name_for_effect` (`trace_rotated.rs:464`) — no constraint.
3. **The chain-check is equality over already-bound PIs.** `leg_k.OLD == leg_{k-1}.NEW` compares two
   felts each of which is cryptographically pinned **in its own leg** (the IR-v2 batch verifier at
   `:1591-1597` re-binds them via the cohort descriptor's PI pins). Equality of two
   independently-proven public inputs is a verifier arithmetic check, exactly the kind LAW #1
   permits ("A verifier-side chain-check over existing proven legs is fine in Rust"). It introduces
   no new *semantics* about what a transition means.
4. **net_delta sum + effects_hash re-derivation** are likewise reads/sums over bound PIs +
   recomputation of the same `compute_effects_hash_4`/`encode_net_delta` helpers the prover and
   in-circuit constraints already use (`helpers.rs:405`, `effect_vm::encode_net_delta`) — Rust, not
   a constraint.
5. **The non-synthetic lift (§4) is a witness/seed change**, not a constraint: it changes which
   `CellState` seeds `initial_vm_state` and which gate admits the witness. The welds, pins, and r23
   binding are the SAME Lean-emitted constraints; we just feed them a real cell.

**The ONE place Lean *might* be on the critical path: Shape 3 (NoOp-only), IF reachable.** If the
Phase-0 confirmation finds empty/NoOp-only projections reaching the finalized path, the
PRESERVE-faithful fix is a `noOpVmDescriptor2R24` identity leg (OLD==NEW, net_delta 0), which **is**
a new Lean-emitted descriptor in `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` +
its TSV twin + the registry-coverage tooth (`trace_rotated.rs:507-568` asserts the resolvers cover
EXACTLY the registry, currently 36 members — adding NoOp would make it 37 and the cohort gate would
need NoOp to resolve). **This is the only Lean fork in the plan, and §1 argues it is likely
unreachable** — so the plan's spine (heterogeneous + non-synthetic) is **Rust-only**, and the NoOp
descriptor is a contingent, isolated, single-descriptor addition gated on the Phase-0 finding.

> **Verdict for the campaign tracker:** PATH-PRESERVE is a *Rust soundness-core composition*
> campaign (prover-side run-splitter + chained witness builder; verifier-side collect+chain-check;
> a non-synthetic witness seed; a chained differential). Lean re-emission is **review-only** for the
> spine (confirm no per-cohort theorem assumed a single-run trace — they don't; the pins are
> first-row/last-row, which a per-run trace satisfies), with **one contingent new descriptor**
> (NoOp identity) only if Shape 3 is reachable.

---

## 6. The differential + anti-ghost test plan

The discipline: **chain ≡ monolithic transition**, with a tampered-middle-leg anti-ghost tooth and
conservation across the chain. All of these are Rust tests (plus the Lean review).

### 6.1 chain ≡ mono (the load-bearing differential)
For a heterogeneous turn `[Transfer, SetField, Transfer]` on a real (non-synthetic) cell:
- Build the **monolithic** v1 reference: `generate_effect_vm_trace(s0, all_effects)` →
  `(mono_trace, mono_pi)`; record `mono_pi[OLD_COMMIT]`, `mono_pi[NEW_COMMIT]`, and the monolithic
  `net_delta` (`mono_pi[NET_DELTA_MAG/SIGN]`).
- Build the **chained** witnesses (§2.3), prove each run rotated, collect the legs.
- **Assert:**
  - `legs.first().OLD == mono_pi[OLD_COMMIT]` and `legs.last().NEW == mono_pi[NEW_COMMIT]`
    (endpoints agree with the monolithic transition);
  - `∀k: legs[k].NEW == legs[k+1].OLD` (interior chain closes);
  - `Σ_k net_delta(legs[k]) == mono net_delta` (conservation across the chain ≡ monolithic);
  - the interior boundary states `s_k` reproduce the monolithic trace's per-row state blocks at the
    run boundaries (the §2.3 hand-replay correctness — this is the tooth that catches a bad
    intermediate-state construction).
- This is the chained analogue of the existing cell≡circuit differential
  (`circuit/tests/effect_vm_rotation_flip.rs`); add a `*_chained` case.

### 6.2 anti-ghost: tampered middle leg ⇒ verify FAILS
- Prove a 3-run chain, then **corrupt leg-1's NEW_COMMIT PI** (off by one felt, the
  `forged_post_state_is_rejected` pattern at `turn_proving.rs:909-941`). Re-run
  `verify_full_turn_chained`. **Assert** it returns `ChainBreak` (adjacency leg-2.OLD ≠ leg-1.NEW)
  — UNSAT-equivalent at the chain layer. (The leg itself is also internally re-verified at
  `:1591`; a tamper that desyncs PI from proof fails there first — assert either rejection path.)
- **Tamper the split:** attach legs for `[Transfer, Transfer]` while the actor's real effects are
  `[Transfer, SetField, Transfer]`. **Assert** the effects-hash re-derivation (§3.3) rejects (PI[8]
  of some leg ≠ `compute_effects_hash_4(real_run_k)`), so a prover cannot substitute a
  different-but-chaining effect multiset.
- **Drop a leg:** remove the middle leg. **Assert** endpoints no longer chain (leg gap) ⇒
  `ChainBreak` or endpoint mismatch.

### 6.3 heterogeneous turn proves + verifies end-to-end (the live-path test)
- Mirror `flow_b_self_sovereign_turn_proves_rotated` (`turn_proving.rs:982-1049`) for a
  heterogeneous turn: assert the composed proof carries **≥2** `"effect-vm-rotated"` legs and **zero**
  `"effect-vm"` legs, and `verify_full_turn` (chained) passes against the carried commitments. Add a
  field-bearing variant (Shape 2 + Shape 1 composed).

### 6.4 conservation across the chain
- A turn whose runs have opposing deltas (outgoing Transfer then incoming Transfer) must sum to the
  net; assert Σ matches and a forged per-leg delta breaks the conservation tooth (§3.4 / `:1304`).

### 6.5 Lean review (NOT a new proof, but a recorded check)
- Confirm each per-cohort theorem in `EffectVmEmitRotationV3.lean` binds **first-row pre / last-row
  post** (not "the trace has exactly one effect row"), so a multi-row single-cohort run already
  satisfies it. The §EXEC.3 keystone `rotV3_binds_published` (one theorem, 26→36 descriptors) is the
  per-leg soundness; the chain adds no Lean obligation. **Record this finding in
  `_RUST-LEAN-DIVERGENCE-LEDGER.md`** (the chain is a Rust composition; no Lean divergence opened).

---

## 7. The phase sequence (each a persvati-green landing; v1 deletion LAST)

House style: **additive behind a flag, then cutover.** Never a red intermediate (no
prover-chains-but-verifier-expects-one-leg, and no verifier-chains-but-prover-emits-one-leg). The
flag gating the chained path is the existing `recursion` feature (rotated legs only exist there);
within that, stage with an internal route until the cutover.

> Independence rule for every phase below: it must land **persvati-green on its own** and leave the
> live path's behavior unchanged until its own cutover line.

### Phase 0 — Confirm Shape 3 + extend the differential harness (pure additive)
- **Do:** add the `debug_assert!(!vm_effects.is_empty())` / instrumentation to confirm
  empty/NoOp-only projections never reach `prove_and_verify_finalized_turn*`
  (`turn_proving.rs:512/685/817`). Add the `split_into_cohort_runs` pure fn + unit tests
  (homogeneous → 1 run; heterogeneous → N runs; coalescing). Extend `effect_vm_rotation_flip.rs`
  with a **non-synthetic-cell** differential case (still proving via the EXISTING single-run path,
  just on a field-bearing cell to establish the §4 OLD/NEW-agreement fact).
- **Green:** new pure-fn tests pass; the differential extension passes; live path untouched.
- **RED if:** the run-splitter mis-coalesces, or the non-synthetic differential reveals OLD_COMMIT
  disagreement (would mean §4's premise is wrong — investigate before proceeding).

### Phase 1 — The chained PROVER, behind an internal route (additive; verifier still single-leg)
- **Do:** add the chained witness builder (`Vec<RotationTurnWitness>`, §2.3) and a
  `prove_full_turn_chained` path that emits N rotated legs — **gated so it is only taken for turns
  the single-run path REJECTS today** (heterogeneous / >1 run). For homogeneous turns the existing
  single-leg path runs unchanged. **Crucially:** in this phase the chained path is exercised ONLY in
  tests (a `#[cfg(test)]` or env-gated internal route), NOT wired into `blocklace_sync`. The live
  node still passes `rotation: None` for heterogeneous turns ⇒ **v1 still runs live** (no regression,
  no behavior change).
- **Green:** unit/integration tests prove a heterogeneous turn into N legs and the §6.1 differential
  (chain ≡ mono) passes. The single-leg verifier is NOT yet asked to verify N legs (tests check the
  legs structurally + via the chained verifier built in Phase 2, OR Phase 1 lands together with
  Phase 2 if you prefer one PR — see the ordering note).
- **RED if:** a heterogeneous proof is attached but the LIVE verifier (still single-leg) is invoked
  on it. **So Phase 1 must NOT change what the live path emits.** This is the additive guarantee.

> **Ordering note (avoid the forbidden red).** The cleanest swarm-safe sequence lands **Phase 1
> (chained prover) and Phase 2 (chained verifier) as ONE atomic PR** behind the internal route, so
> at no commit does the live wire carry N legs a single-leg verifier would choke on. The flag-day
> cutover (Phase 4) flips the live route. If split into two PRs, Phase 2 (verifier) MUST land first
> (a verifier that *accepts* N legs but also still accepts 1 is backward-compatible), then Phase 1
> (prover) — never the reverse.

### Phase 2 — The chained VERIFIER (`verify_full_turn` collect+chain-check; backward-compatible)
- **Do:** implement §3 — collect (`:1688-1693` `.find` → `filter`), endpoint + adjacency checks,
  `ChainBreak` error variant, effects-hash re-derivation, net_delta sum, step-8 note-spend leg
  selection. Add `verify_full_turn_chained`/extend `verify_full_turn_bound` to take the expected
  effects (for §3.3). **N=1 collapses to today's exact two endpoint checks** — so every existing
  green turn verifies byte-identically.
- **Green:** all existing `full_turn_proof` + `turn_proving` verifier tests pass unchanged (N=1
  path); the new §6.2/§6.3 anti-ghost + heterogeneous end-to-end tests pass.
- **RED if:** any existing single-leg test regresses (means the N=1 collapse isn't faithful), or a
  tampered-middle-leg verifies (anti-ghost hole).

### Phase 3 — Non-synthetic-cell witness lift (§4; additive, then the gate flips)
- **Do:** add `CellState::from_cell` (real fields/cap_root seed), replace
  `cell_is_synthetic_shaped`/`cell_matches_v1_prestate` (`:353-357/445-448`) with the
  representability gate, seed `initial_vm_state` from the real cell at the call sites
  (`:521/819`). Flip `flow_b_non_synthetic_cell_falls_back_to_v1` (`:1056-1084`) to assert a
  verifying rotated proof. Extend the §6.1 differential to field-bearing + cap-holding cells.
- **Green:** non-synthetic cells now yield rotation witnesses and verify; the OLD/NEW agreement
  differential passes; homogeneous-synthetic turns still pass (the gate is a superset).
- **RED if:** a non-synthetic OLD_COMMIT disagrees with the v1-expected commitment (the §4 premise
  fails), or the seed change regresses the synthetic path.

### Phase 4 — CUTOVER: wire the chained path live (the flag-day; v1 fallback goes dormant)
- **Do:** in `blocklace_sync.rs:2637-2720`, BUILD the chained rotation witness (instead of `None`)
  for heterogeneous + non-synthetic turns, so the LIVE node emits N rotated legs and the chained
  verifier gates acceptance. After this, **`rotation: None` is reached only for turns that genuinely
  cannot rotate** — which, post-Phases 1-3, is the empty/NoOp case (Shape 3). If Phase 0 confirmed
  Shape 3 unreachable, **no live turn takes the v1 leg anymore** (the rotated path is TOTAL).
- **Green:** a devnet / integration run commits heterogeneous + field-bearing turns, each carrying
  a verifying N-leg rotated proof; the v1 leg (`:1185-1202`) is dead code on the live path (still
  present, not yet deleted).
- **RED if:** any live finalized turn shape still falls to the v1 leg (means coverage is not total
  — find the shape, return to the relevant phase). This is the **gate for Phase 5**: C7 may not
  proceed until a coverage sweep shows zero live v1-leg invocations.
- **Contingent sub-step (only if Phase 0 found Shape 3 reachable):** land the
  `noOpVmDescriptor2R24` identity descriptor (Lean `EffectVmEmitRotationV3.lean` + TSV twin +
  registry-coverage tooth update `trace_rotated.rs:507-568`) and route empty projections to it.

### Phase 5 — C7: delete v1 (Bucket F, then Bucket A/C grep-zero) — the FINAL phase
Per `V1-DELETION-MANIFEST.md` Execution shape, the honest order is **F → (this plan = G) → #103 →
A/C fan-out**. PATH-PRESERVE Phases 0-4 ARE Bucket G. So Phase 5 is:
- **5a (Bucket F):** make the rotated participant leg mandatory in the 5 recursion/aggregation files
  (`proof_forest.rs`, `joint_turn_aggregation.rs`, `ivc_turn_chain.rs`, `joint_turn_recursive.rs`,
  …; `V1-DELETION-MANIFEST.md:87-95`), drop the `EffectVmP3Proof` field, fix host-admission reads.
  *(F is a sibling lane to G; it can land in parallel but MUST precede the `EffectVmP3Proof`
  delete.)*
- **5b (#103):** flip `proof_verify.rs` + `prove_pool.rs` off `EffectVmAir`.
- **5c (Bucket A/C):** delete `effect_vm_p3_full_air.rs`, `effect_vm_p3_air.rs`, `effect_vm/air.rs`,
  `EffectVmP3Proof`/`prove_effect_vm_p3`, `CutoverFallback`, `EFFECT_VM_WIDTH`, `ACTIVE_BASE_COUNT`
  (v1 PI), the `BilateralAggregationAir` block, and their test harnesses; run the grep-zero
  checklist (`V1-DELETION-MANIFEST.md:119-125`) to 0 in recursion builds.
- **Green:** the grep-zero checklist reaches 0 (recursion builds, minus Bucket E `generate_effect_vm_trace`
  which stays for the wasm floor); persvati workspace gauntlet green.
- **RED if:** grep-zero is not actually 0 (a residual v1 ref survives), or any deletion lands before
  5a/G completes (ships RED per the manifest).

> **Wasm / `not(recursion)` (Bucket E + the wasm-prover ember-decision):** the
> `#[cfg(not(feature="recursion"))]` path has no rotated leg, so it keeps the v1 single-leg verifier
> + `generate_effect_vm_trace`. PATH-PRESERVE's chained path is entirely `recursion`-gated; it does
> NOT change the wasm floor. C7's FULL grep-zero (including wasm) waits on the separate Option-A
> wasm-rotated prover (`HORIZONLOG.md` "THE WASM-PROVER ember-DECISION"), which is out of scope here.

---

## 8. Open questions for ember (implementation forks only — the strategic one is DECIDED)

1. **Shape 3 (NoOp-only) policy, pending the Phase-0 finding.** If empty/NoOp-only projections turn
   out to reach the finalized path, do you want the `noOpVmDescriptor2R24` **identity rotated leg**
   (keeps "every finalized turn carries a rotated proof" literally true, +1 Lean descriptor), or is
   an empty projection a turn that should never have been finalized (so a hard
   `debug_assert!`/reject is the right answer)? My read: it's almost certainly unreachable, so this
   is a contingency, not a blocker. **No action needed unless Phase 0 surfaces it.**

2. **effects-hash binding mechanism (§3.3).** The plan re-derives the run split + per-leg effects
   hash in the verifier (local change). The alternative — populate the existing `EFFECTS_HASH_GLOBAL`
   PI[29] anchor on every leg to the whole-turn hash and pin equality — is also sound but threads a
   non-default `EffectVmContext` through the generator call sites (broader). I've staged the
   local-verifier choice; flag if you'd rather invest in the global anchor now (it would also serve
   future cross-cell bundle binding). **Implementation fork, not strategic.**

3. **Phase 1+2 as one PR vs. verifier-first two PRs (the ordering note in §7).** Atomic is cleanest
   for swarm-safety; two PRs (verifier-first) is more reviewable. Either is green-safe if the order
   holds. **Pick per review preference.**

Everything else is settled: PRESERVE is the path (no WEAKEN), the spine is **Rust composition over
Lean-emitted per-cohort legs** (LAW #1 satisfied, §5), and C7's deletion is the final phase gated on
a zero-live-v1-leg coverage sweep.

---

## Appendix — corrected `path:line` index (verify-before-claim)

| Claim | Cross-ref said | **Actual (HEAD)** |
|---|---|---|
| gates file | `turn/src/turn_proving.rs` | **`node/src/turn_proving.rs`** (no `turn/src/turn_proving.rs` exists) |
| single-leg `.find` (the crux) | `full_turn_proof.rs:1688-1719` | `.find` at **`:1692`** (block 1688-1693; OLD/NEW read `:1709-1710`; teeth `:1712-1725`) |
| v1 fallback leg | `full_turn_proof.rs:1185-1202` | **`:1185-1202`** ✓ (rotated leg attached `:1151-1181`) |
| `cohort_ok` (self-sovereign) | `turn_proving.rs:353-387` | **`:380-387`** (computation); reads `vm_effects`/`lead_name` `:376-384` |
| `cohort_ok` (capability) | `turn_proving.rs:445-479` (cross-ref `468-479`) | **`:472-479`** (computation); setup from `:468` |
| `cell_is_synthetic_shaped` | `turn_proving.rs:353-357` | **`:353-357`** ✓ |
| `cell_matches_v1_prestate` | `turn_proving.rs:445-448` | **`:445-448`** ✓ |
| `rotated_descriptor_name_for_effect` | `trace_rotated.rs:438` | resolver `:464`; per-selector map `:405-442`; **`:438`** is the "residue empty" comment |
| one-descriptor-per-proof note | `trace_rotated.rs:507` | **`:507-568`** (the `resolvers_cover_exactly_the_rotated_registry` test, "36 cohort members") |
| `generate_rotated_effect_vm_trace` opens with shared generator | `trace_rotated.rs:203` | **`:203`** ✓ (`generate_effect_vm_trace(initial_state, effects)`) |
| node projection (one turn, full effects) | `blocklace_sync.rs:2605-2722` | **`:2605-2611`** (projection); routing `:2626-2722` ✓ |
| heterogeneous projector | `cipherclerk.rs:5491-5527` | **`:5488-5527`** (`convert_effects_to_vm`; Transfer `:5491`, SetField `:5504`) |
| NoOp injection (NOT on this path) | `effect_vm_bridge.rs:557` | **`turn/src/executor/effect_vm_bridge.rs:556-558`** (in `collect_effects`, the executor per-cell projector — not the FullTurnProof path) ✓ |
| prover fails closed on heterogeneous | — | `full_turn_proof.rs:873-883` |
| `prove_vm_descriptor2` proves ONE descriptor | — | `descriptor_ir2.rs:3832` (`desc: &EffectVmDescriptor2`) |
| `EFFECTS_HASH` per-leg vs `EFFECTS_HASH_GLOBAL` | — | per-leg `pi.rs:24` (PI[8]); whole-turn `pi.rs:94` (PI[29], **unpopulated on live path** — `trace.rs:99-103` default ctx) |
| rotated OLD/NEW pins (single felt) | — | `trace_rotated.rs:234-235` (`B_STATE_COMMIT`, col 218/261); v1 prefix carried `:233` |
