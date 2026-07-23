# DESIGN — shielded-pool soundness (C4) + dark value v4 (C5)

**Design lane, 2026-07-23. Campaign tracks C4 + C5 of `docs/SPRINT-poster-honesty-closure-2026-07-23.md`
(ember-greenlit 07-23).** This lane produces a design + first-slice scoping and lands ADDITIVE Lean
model work only. It touches NO deployed descriptor, VK, wire format, or the frozen
`NullifierAccumulator` gate (`metatheory/.../Exec/NullifierAccumulator.lean` — ember-fired only).

**SUBSTRATE, said out loud (house law #1):** the shielded spend circuit and every commitment /
nullifier / value-binding scheme here is **Lean-authored AIR**. The Lean module *is* the constraint
author; Rust only fills traces and calls the emitted object. Where a scheme is currently authored in
Rust (`circuit-prove/src/shielded/spend_circuit.rs`), that is **house-law-#1 DEBT** and a Lean-port
target — never a foundation to extend.

---

## 0. Build-state finding (the precondition, re-checked today)

The 07-22 note that "the turn / circuit-prove tree was RED" is **CLEARED at HEAD (2026-07-23).**

```
cargo check -p dregg-turn -p dregg-circuit-prove --features dregg-turn/prover  →  exit 0
```

(warnings only: one `dead_code`, the usual `block`/`proc-macro-error2` future-incompat notices). Both
crates build. The metatheory tree builds the shielded cluster: `lake build
Dregg2.Circuit.ShieldedWideJoinPin` → `Build completed successfully (2944 jobs)`. The design below is
stated against this green reality.

Package-name note for future lanes: the crates are `dregg-turn` / `dregg-circuit-prove`, not
`turn` / `circuit-prove` (a bare `-p circuit-prove` errors "did not match any packages").

---

## 1. The target object — and a load-bearing correction to the campaign premise

The sprint doc (and this lane's brief) says stage (a) is *"the Lean MODEL of the spend circuit first —
the object to falsify against, **which today does not exist**."* **That premise is STALE.** Ground-truth
read of the tree at HEAD: the Lean model substantially **EXISTS and is proven.** Reality-gate first —
do not build a mirror of what is already there.

### 1.1 What already exists (verified by direct read, HEAD)

| object | file | what it proves |
|---|---|---|
| **abstract falsifier #15** | `metatheory/Dregg2/Circuit/ShieldedMerkleRootPin.lean` (`a1ebd82c43`) | `root_substitution_forges` / `deployed_admits_but_pin_rejects` (wire-root theft); `pinned_accept_is_committed` (fix sound under `AccumulatorSound`); launder `mutation_test_is_not_the_pin`. `#assert_axioms`-clean. |
| **abstract falsifier #16** | `metatheory/Dregg2/Circuit/ShieldedValueLinkPin.lean` (`6078336003`) | `genuine_note_inflates` (a genuine v-note mints v+1, no forged leaf); `linked_conservation_over_real_value` (fix ⟹ minted = real spent); launder `link_test_is_not_the_gate`. |
| **Lean-authored spend AIR** | `metatheory/Dregg2/Circuit/Emit/ShieldedSpendDescriptor.lean` | `root_is_pinned` (:311 — supplied-root lane, chain-fold, and claim-PI all ≡ the committed-accumulator PI); `chain_root_forge_unsat` (:353); `spend_relation_row0` (genuine C4/C6/C7 relation under `ChipTableSound`); `zero_witness_satisfies` (inhabited). |
| **Lean-authored value-link + Σ-conservation AIR** | `metatheory/Dregg2/Circuit/Emit/ShieldedValueLinkDescriptor.lean` | `value_link_bound` (value_binding & leaf_commit are hash-images of ONE shared value cell); `conservation_holds` (Σ value ≡ Σ out mod p); `mint_unbalanced_unsat`; `honest_balanced_satisfies`. |
| **the discharge — falsifiers refuted against the emitted objects** | `metatheory/Dregg2/Circuit/ShieldedSpendPortDischarge.lean` (`28c74d7dbd`) | `emitted_accept_is_committed` (**NO `AccumulatorSound` hyp** — the emitted C6a/C6b force the accepted leaf to be a genuine committed note + the chain to fold to the committed PI); `emitted_conserved_is_leaf_bound` (leg = leaf = one in-AIR cell ⇒ `genuine_note_inflates` **unrepresentable**); `emitted_linkHolds` (the deployed-omitted `legValue = leafValue` is a theorem here). |
| **residual soundness downstream** | `metatheory/Dregg2/Circuit/ShieldedSpendPortResidual.lean` | nullifier double-spend **composed** with the landed 8-felt `NullifierAccumulator` (`emitted_nullifier_double_spend_refused`); the ∀-leaf `NoteAccumulatorCR` floor **reduced** to a single Poseidon2-CR floor (`noteAccumulatorCR_of_hashFloor`) via the multi-row fold-walk; mod-p→ℤ range lift under a named no-wrap bound; the #17 verdict. |

**So the acceptance bar this lane's brief sets for stage (a) — "the two banked falsifiers become
unrepresentable or refused, as theorems" — is ALREADY MET, as metatheory.** `emitted_accept_is_committed`
refutes the #15 wire-root theft by construction; `emitted_conserved_is_leaf_bound` + `emitted_linkHolds`
refute the #16 value-leg inflation by construction. The abstract falsifiers' two free hypotheses
(`AccumulatorSound`, `linkHolds`) are discharged against the emitted objects.

### 1.2 What is GENUINELY missing (the real wound, re-priced)

The proven Lean object **is not the deployed object.** Verified at HEAD:

- **No emit driver.** No `metatheory/Emit*.lean` references `shieldedSpendDesc` or
  `shieldedValueLinkDesc` (grep: zero hits).
- **No descriptor JSON.** `circuit/descriptors/by-name/` has `note-spend-leaf.json`,
  `faithful-note-spend-{v2,exact-v3}.json`, `shielded-whole-note-swap-substrate-v1.json` — **no
  shielded-spend / shielded-value-link descriptor.**
- **No PROVENANCE row** for the spend / value-link descriptors.
- **The deployed path is unchanged.** `apply_shielded_transfer` (`turn/src/executor/apply.rs:1703`) still
  reconstructs `ShieldedTransfer::from_serialized_parts(payload.merkle_root, …)` (`:1738`, wire root),
  verifies the **Rust-authored** `shielded_spend_circuit()` via `verify_stark_with_wide_bindings`
  (`:1753`), and clears value through **off-AIR Ristretto** `verify_full_conservation_bytes` (`:1764`).
  The wire-root theft (#15) and the leaf↔leg inflation (#16) are **open on the deployed prover path**
  exactly as priced; the proven Lean object that closes them is sitting beside the deployed Rust,
  unrouted.

**This is the mapping-is-the-launchpad correction (`feedback-mapping-is-the-launchpad-not-the-outcome`):**
the campaign is **NOT "author the Lean model"** (done). It is **"make the proven Lean object BE the
deployed object, and DELETE the Rust-authored `spend_circuit` debt"** — the unadditive move — plus close
the three named residuals (`NoteAccumulatorCR` ∀-leaf fold-walk discharge; `VALUE_BITS` ℤ-lift; #17 PQ
posture). The Rust-authored `spend_circuit.rs` AIR is debt to be deleted, never extended.

### 1.3 Module layout for what remains (Lean side)

The new Lean authoring is small because the constraint logic exists. The layout:

- **Emit drivers (NEW):** `metatheory/EmitShieldedSpend.lean` + `metatheory/EmitShieldedValueLink.lean`
  (or one `EmitShieldedTransferClear.lean`) — call the existing `shieldedSpendDesc` / `shieldedValueLinkDesc`
  through the standard `emitVmJson2` path (as `EmitRotationV3` / `EmitWideRegistryProbe` do), producing the
  `circuit/descriptors/*.json` + a `PROVENANCE.json` sha256 row. This is the object the Rust decodes. It
  imports only the two existing `Emit/Shielded*Descriptor.lean` modules — no new constraint authoring.
- **Composition (NEW, or extend `ShieldedRingEndpointDescriptor.lean`):** one transfer-clearing
  descriptor that welds `shieldedSpendDesc` (per input) and `shieldedValueLinkDesc` (the Σ block) with the
  apex `connect` of each leg's `[nullifier, merkle_root, value_binding]` claim — the "degenerate
  single-transfer clearing descriptor" of `PLAN-shielded-apex-redesign-2026-07-20.md §1`.
- **C5 same-opening (LANDED THIS LANE):** `metatheory/Dregg2/Circuit/ShieldedWideJoinPin.lean` — see §3.

**Acceptance bar (unchanged, and already met as metatheory; the campaign's job is to make it hold of the
DEPLOYED object):** the emitted, routed spend/clearing descriptor must refute the two banked falsifiers
by construction — `emitted_accept_is_committed` (wire-root theft unrepresentable) and
`emitted_conserved_is_leaf_bound` + `emitted_linkHolds` (value-leg inflation unrepresentable) — now over
the object Rust actually verifies, with an **emit-equality gate** (Lean-emitted == the object the node
consumes) discharging house law #1 and catching the `traceWidth-1537` drift the plan §5 flags.

---

## 2. Staged plan with per-stage gates

The stages track `DECISION-shielded-redesign-2026-07-20.md` (ember: **B now + A redesign**) and
`PLAN-shielded-apex-redesign-2026-07-20.md`, re-scoped for the fact that stage (a) is done-as-metatheory.

### Stage (a) — Lean model + falsifier-refutation theorems  ·  **STATUS: substantially DONE**

The model + refutation-by-construction theorems exist (§1.1). Residual authoring inside (a):

- **(a.1) emit the descriptors** — `EmitShieldedSpend` / `EmitShieldedValueLink` drivers →
  `circuit/descriptors/*.json` + `PROVENANCE.json` rows. *Additive; no VK flip* (there is **no committed
  shielded descriptor VK today** — the deployed path verifies via standalone `verify_dsl_zk`, not the
  descriptor registry). **Gate:** the JSON is emitted, byte-pinned by a `#guard` on the wire string, and
  an **emit-equality differential** shows the Rust producer consumes byte-identical bytes.
- **(a.2) discharge the `NoteAccumulatorCR` ∀-leaf floor** — `ShieldedSpendPortResidual` already reduces
  it to a single Poseidon2-CR floor via the fold-walk (`noteAccumulatorCR_of_hashFloor`). Confirm that
  reduction is the final resolution wanted, or push the fold-walk further. **Gate:** no un-named ∀-leaf
  assumption remains; the residual is exactly one Poseidon2-CR floor, `#assert_axioms`-clean.

**Gate for (a):** all shielded metatheory `#assert_axioms`-clean and non-vacuous (holds today); the two
falsifiers refuted against the *emitted* (a.1) object, not only the in-memory `def`.

### Stage (b) — route the merkle_root pin into the AIR  ·  **VK-affecting: staged, regen prepared, NOT flipped**

Route `apply_shielded_transfer` through the emitted spend descriptor whose `merkle_root` claim lane is
PI-pinned to the committed accumulator (`ShieldedSpendDescriptor.root_is_pinned`), supplying `pi[committed_root]`
from the **ledger's** committed commitments-root, never from `payload`. Retire the wire
`ShieldedTransferPayload::merkle_root` field. Introduce the committed shielded-commitment accumulator the
root pins to (today the shielded set only pollutes `note_nullifiers.root8()` as a Stage-B placeholder,
`apply.rs:1793-1802`).

- **Substrate:** Lean-authored AIR (the pin lives in `shieldedSpendDesc`); Rust supplies the committed-root
  witness and calls the emitted verify.
- **Gate:** the deployed differential — a wire-chosen root is *unrepresentable* (no wire slot) and the
  in-AIR `connect` makes a decoupled root UNSAT; the existing `forged_membership_root_rejects` test plus a
  NEW attacker-proves-against-chosen-root test both fail closed. Staged behind a build flag / not flipped
  into the committed path until stage (e).

### Stage (c) — fold value_link into the deployed AIR  ·  **same discipline**

Route the Σ-conservation + value-link block (`shieldedValueLinkDesc`) into the deployed clearing, retiring
the off-AIR `verify_full_conservation_bytes` over free Pedersen legs (GATE 2, `apply.rs:1764`) in favour of
in-AIR conservation over the SAME value cells the leaf commits (`emitted_conserved_is_leaf_bound`).

- **Substrate:** Lean-authored AIR; Rust fills the value/asset/randomness witness columns.
- **Gate:** the deployed `genuine_note_inflates` differential — a genuine v-note attempting to mint v+1 is
  UNSAT in-AIR (leg = leaf = one cell); `verify_value_link` and its test-only invocation are deleted (the
  property is now a circuit constraint). Keep the Ristretto legs as an **explicitly non-TCB** large-amount
  range crutch (plan §4, option 4b) until the in-AIR Bulletproof residual lands.

### Stage (d) — #17 PQ-commitment posture  ·  **EMBER DECISION (options laid out, not chosen)**

After (c) the authoritative no-mint gate is the in-AIR Poseidon2 chain (value-binding recompute + Σ
conservation + range) on `HashCR` — quantum-safe. What remains is **which commitment is load-bearing**,
and the deployed 1-felt (~31-bit) digests. Three options, tradeoffs for **ember's** call — **do not pick**:

| option | what it makes authoritative | pro | con / obligation |
|---|---|---|---|
| **Ristretto Pedersen apex** (keep the curve as the value commitment) | the classical Pedersen conservation stays the value law | least new crypto; large-amount range "for free" via Bulletproofs | **Shor-broken** (DLog); contradicts the "PQ cutover" narration; keeps a non-PQ commitment in the TCB |
| **Poseidon2 `value_binding` "Option A"** (the plan's rec) | the in-AIR Poseidon2 value-binding + Σ conservation | PQ (hash floor, same as membership/nullifier); one commitment; retires the curve | caps amounts at `2^VALUE_BITS` until the **in-AIR Bulletproof** (or multi-limb range) lands (residual §6); the deployed 1-felt digest still wants widening to the 8-lane / 16-lane carrier |
| **a PQ commitment (lattice/hash-based, wide)** | a dedicated PQ value commitment (e.g. the 16-lane `wide_value_binding` carrier as the sole value commitment) | full-`u64` binding, PQ, no curve, no felt-width waist | most authoring; must prove the wide carrier binds conservation directly (ties into C5 §3 Fix B) |

**Recommendation to inform (not make) the decision:** Option A (Poseidon2 authoritative) with the Ristretto
legs demoted to a **named non-TCB** range crutch, converging to the wide PQ commitment as C5's Fix B lands —
so #17 and C5 close on the *same* wide carrier. But the load-bearing choice is ember's: **which commitment
is the value law, and whether large-amount range waits for the in-AIR Bulletproof or ships capped.**

### Stage (e) — the ONE deliberate VK-epoch flip  ·  **ember-fired**

The single coordinated flip. **The unknown to resolve BEFORE building (plan §5, "the single most
important unknown"):** whether admitting the shielded segment into the committed turn changes the
**aggregate turn VK** (descriptor-enumerated) or is additive (descriptor-agnostic aggregation). That
classification decides additive-vs-coordinated-flag-day.

- **Gate:** the frozen-kernel `NullifierAccumulator` gate fires **only by ember's hand**, never piecemeal.
  Batch this flip with any pending felt-width E-kind rotations (the shielded 1-felt→8-lane digest widening,
  the E2 batch) so the epoch carries one coordinated registry + light-client + node move.
- **Substrate:** the emitted descriptors ride the standard rotation registry (`PROVENANCE.json` +
  `rotation-*-staged-registry.tsv`); the light client accepts the new turn VK at the epoch.

---

## 3. C5 — dark value v4: the same-opening design

### 3.1 The wound, precisely (ground-truthed)

The exact-spend path ties two proofs whose value coordinates must agree:

- the **wide carrier** (`circuit-prove/src/shielded/wide_value_binding.rs`): commits the full-`u64`
  `(value, asset)` opening — four bit-constrained 16-bit limbs each, two domain-separated `node8`
  Poseidon2 images (`WIDE_VALUE_BINDING_LANES = 16`), and **recomputes the legacy one-felt binding from
  those limbs in the same AIR** (`col::LEGACY_BINDING`). Internally, wide and legacy agree.
- the **ring / conservation proof** (`shielded_ring_clearing_air.rs`): per-leg claim
  `[nullifier, merkle_root, value_binding]` (`RING_LEG_CLAIM_LEN = 3`) — exposes only the **one-felt**
  `value_binding` as the join slot.
- **the join is ONE felt.** `apply_shielded_transfer` reconstructs the wide carrier from
  `input.legacy_value_binding` and the ring/spend proof from that **same** `legacy_value_binding`
  (`apply.rs:1723-1743`). The only tie between the two proofs is felt-equality on the ~31-bit
  `legacy_binding`. Per HORIZONLOG 07-22: *"the present ring↔wide sidecar join is only one BabyBear
  `legacy_binding` (~31 bits), not a cryptographic same-opening; v4 must share one witness or a faithful
  full-width commitment across both proofs."*

**Attack:** pick two distinct full-width openings `o₁ ≠ o₂` whose `legacy_binding` felts collide
(birthday ~2^15.5, chosen ~2^31 — the squeeze reduces `value`/`asset` mod BabyBear `p` to one felt, so
distinct `u64` values alias). Let the ring conserve `o₁` (the value that moves) while the wide carrier's
PI advertises `o₂` (the "dark value" the receipt binds). The join accepts; `o₁.value ≠ o₂.value`. The
advertised dark value is decoupled from the value that conserves.

### 3.2 The v4 same-opening design — two shapes, honestly named

The obligation is a **same-opening argument: a proof, not a wiring task.** Two ways to discharge it:

- **Fix A — share one witness (the collapse).** ONE hidden `(value, asset)` cell feeds *both* the wide
  carrier hash and the ring conservation. `ringOpen = wideOpen` by construction; the same-opening is
  literally one opening; the decouple is unrepresentable. This is the shape `ShieldedValueLinkDescriptor`
  already uses for the leaf↔leg link at one felt (leg = leaf = one in-AIR cell) — **lift it to the wide
  carrier**: conservation runs over the same cells the 16-lane carrier hashes. Dispatches the argument by
  collapse; no cross-scheme proof needed.
- **Fix B — a faithful full-width join (the injective tie).** Join on the injective **wide** binding
  instead of the narrow felt: under the wide carrier's collision-resistance (`Function.Injective` on the
  16-lane image), a shared wide binding forces a shared opening — same-opening as a **theorem** under the
  Poseidon2-CR floor. Requires the ring proof to consume the wide lanes (not the legacy felt).

**What dies:** the ~31-bit `legacy_binding` join slot. Under Fix A it is redundant (one cell); under
Fix B it is replaced by the 16-lane tie. The `RING_LEG_CLAIM_LEN = 3` claim's one-felt `value_binding`
slot ceases to be the value law.

**What the 76-PI public statement shrinks to:** v3 (`faithful-note-spend-exact-v3`) publishes 76 PIs
exposing nullifier / **value** / **asset** / root / count / outer coordinates, with a value-zero executor
slice and no value commitment. Under the shared-witness / wide-binding shape, **value and asset leave the
public inputs** — they become hidden witness cells bound only through the wide carrier + in-AIR
conservation. That is exactly the v4 boundary `shielded_exact_apex_v4.rs` already declares:
`SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT = 100`, **no clear-value or clear-asset slot**, the leaf payload
replaced by the 16-lane blinded binding.

### 3.3 What we already have vs what is genuinely new

- **Already have (substrate):** the hiding PCS — FWS1 / HidingFRI whole-note-swap
  (`shielded-whole-note-swap-substrate-v1.json`, emitted + PROVENANCE-rowed, `f540ed95a1`); the 16-lane
  wide carrier itself (`wide_value_binding.rs`, internally faithful); the v4 boundary primitives
  (`shielded_exact_apex_v4.rs` — binding/wire only, explicitly **not proof-acceptance authority**).
- **Genuinely NEW (the crypto obligation):** the same-opening BINDING relation — proving the wide carrier
  and the conservation representation open to the same `(value, asset)`. `shielded_exact_apex_v4.rs` states
  it plainly: *"A v4 relation must prove same-opening between the wide carrier and its conservation
  representation (or replace the latter with a native PQ conserving relation)."* This is a **proof
  obligation**, not wiring. Fix A dispatches it by collapse (one witness); Fix B by injectivity (one
  scheme); keeping two schemes (Ristretto conservation + Poseidon carrier) leaves a genuine cross-scheme
  same-opening argument — a sigma-protocol / equality-of-committed-value proof — that must be authored.
- **Still out (the v4 apex beyond the join):** the 19+27 FXC4 consequence binding, the output-note
  transaction, selector/persistence, committee authority (HORIZONLOG 07-22, `f540ed95a1`) — the whole-apex
  green, orthogonal to the value-join and not in this design's scope.

---

## 4. First additive slice — precisely scoped (and STARTED this lane)

The first cycle-2 executable slice is the C5 same-opening wound + refutation, stated in Lean — the piece
that was **genuinely missing** (the ring↔wide join had no Lean model; only the leaf↔leg link did). It is
the C5 twin of `ShieldedValueLinkPin` lifted to the join, and mirrors `Cell/InterfaceIdWidth`'s
`narrow_conflates` / `wideId_injective` shape.

**LANDED IN THIS LANE (`2ca3ca47f7`):** `metatheory/Dregg2/Circuit/ShieldedWideJoinPin.lean` (rooted in
`Dregg2.lean`; `lake build Dregg2.Circuit.ShieldedWideJoinPin` → 2944 jobs, clean; `#assert_axioms`-clean;
non-vacuous `#guard`s). Theorems (over all inputs; binds abstract, hold for the real Poseidon2 carrier and
BabyBear squeeze):

- `narrow_join_admits_dark_value_decouple` / `dark_value_decouples` — **THE FALSIFIER:** with a
  value-distinct squeeze collision (`demo_narrow_collides` shows the modular `legacy_binding` has one:
  `1 % 5 = 6 % 5`), the ring conserves `o₁.value` while the wide carrier advertises a different dark value
  `o₂.value` and the narrow join accepts.
- `join_still_decouples` — **THE LAUNDER:** even with the wide carrier internally faithful
  (`WideCarrierFaithful = Function.Injective`, the honest reading of `wide_value_binding.rs`), the narrow
  join still decouples — the ring never consults the 16 wide lanes.
- `shared_witness_forbids_decouple` — **FIX A:** one opening cell feeds both ⇒ values forced equal.
- `wide_join_forces_same_opening` / `wide_join_same_value` / `wide_join_rejects_the_falsifier` — **FIX B:**
  join on the injective wide bind ⇒ same opening, under the wide-hash CR floor named as
  `Function.Injective`.
- `CrossSchemeSameOpening` / `cross_scheme_join_needs_argument` — **THE HONEST OBLIGATION:** keeping two
  schemes leaves a genuine same-opening argument, a NAMED crypto hypothesis dispatched by Fix A collapse or
  Fix B injectivity, never wiring.

**Next additive slices (cycle-2 lanes execute), in dependency order:**

1. **`EmitShieldedSpend` / `EmitShieldedValueLink` drivers** (stage a.1). Files:
   `metatheory/EmitShieldedSpend.lean`, `metatheory/EmitShieldedValueLink.lean`; regen
   `circuit/descriptors/by-name/*.json` + `PROVENANCE.json`. Theorem/gate: `#guard` byte-pin on the emitted
   wire string; an emit-equality differential vs the Rust producer. Effort: **~1 lane** (calls existing
   descriptors through `emitVmJson2`; the risk is the emit-pipeline plumbing + the `traceWidth-1537` drift
   the plan §5 flags, which the equality gate must catch). **Additive; no VK flip.**
2. **Wide-carrier discharge of C5 Fix B against the emitted object** — the twin of
   `ShieldedSpendPortDischarge`: connect `ShieldedWideJoinPin.wide_join_forces_same_opening` to the emitted
   wide-carrier + conservation descriptor (once the conservation runs over the wide cells), turning the
   `Function.Injective WideBind` floor into the emitted `node8` CR floor. File:
   `metatheory/Dregg2/Circuit/ShieldedWideJoinDischarge.lean`. Theorem:
   `emitted_wide_join_forces_same_value`. Effort: **~1 lane** (bridge, no new constraint authoring), but
   **gated on the shared-witness / wide-binding conservation descriptor existing** (stage c).
3. **The transfer-clearing composition descriptor** (the apex `connect` of §1.3) — Lean-authored, folds
   `shieldedSpendDesc` per input + `shieldedValueLinkDesc` Σ block. File:
   `metatheory/Dregg2/Circuit/Emit/ShieldedTransferClearDescriptor.lean`. Effort: **~1-2 lanes** (real
   authoring — the "degenerate single-transfer clearing descriptor", drop the ring matcher gates, keep
   conservation/range/value-binding-connect).

The **Rust routing** (stages b/c), the **VK classification** (stage e), and the **#17 posture** (stage d)
are NOT lane-additive — they are the ember-fired deploy and the ember decision below.

---

## 5. Ember-decision list

Two decisions gate the campaign; a lane cannot make either.

1. **#17 PQ-commitment posture (stage d) — WHICH commitment is the value law.**
   - (A) Ristretto Pedersen apex — least crypto, but Shor-broken and non-PQ in the TCB.
   - (B) Poseidon2 `value_binding` authoritative — PQ, one commitment, but caps amounts at `2^VALUE_BITS`
     until the in-AIR Bulletproof lands (or ship capped).
   - (C) a wide PQ commitment (the 16-lane carrier as the sole value commitment) — full-`u64`, PQ, no
     felt-width waist, converges with C5 Fix B; most authoring.
   - Sub-question: **do the Ristretto legs stay as a named non-TCB large-amount range crutch** until the
     in-AIR Bulletproof, or drop entirely now (regressing large-amount range for honesty)?
   - *Design's non-binding lean:* (B)→(C) convergence, legs demoted to named non-TCB. **Ember picks.**

2. **VK-epoch timing (stage e) — the ONE deliberate flip.**
   - First resolve the **aggregate-turn-VK classification** (descriptor-agnostic aggregation ⇒ additive;
     descriptor-enumerated ⇒ coordinated flag-day) — an engineering read of the aggregation code, to be
     done before the flip.
   - Then ember fires the single epoch, **batched with the pending felt-width E-kind rotations** (the
     shielded 1-felt→8-lane digest widening). The frozen `NullifierAccumulator` gate moves only by ember's
     hand, never piecemeal.

---

## 6. Discipline note

Read-only outside the one new design doc + the one new Lean module. No deployed Rust / descriptor / VK /
wire-format edits from this lane. Shared tree: no stash / worktree / checkout. The Lean slice is additive,
`#assert_axioms`-clean, rooted in a building target, and committed path-limited (`2ca3ca47f7`). The
poster caveat for shielded / dark-value follows the code — it is edited only after the integrator verifies
the *deployed* object (not the metatheory) refutes the falsifiers.
