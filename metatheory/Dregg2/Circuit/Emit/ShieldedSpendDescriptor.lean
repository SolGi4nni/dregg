/-
# Dregg2.Circuit.Emit.ShieldedSpendDescriptor — the Lean-authored shielded-spend descriptor
# with the membership root PINNED to the committed accumulator (seam #15, in-AIR).

**This is Lean-authored AIR.** This module authors the algebra; Rust parses the emitted IR2
bytes and supplies witnesses — it constructs no constraints. FIRST build lane of the
ember-approved shielded Option-A redesign (`docs/DECISION-shielded-redesign-2026-07-20.md`,
`docs/PLAN-shielded-apex-redesign-2026-07-20.md` §5): the deployed shielded-spend AIR
(`circuit-prove/src/shielded/spend_circuit.rs:192` — `shielded_spend_descriptor()`, C1–C7b as
Rust `ConstraintExpr` data) is house-law-#1 DEBT, and its `merkle_root` PI is prover-supplied,
pinned to nothing (seam **#15** = spend a note that was never created — theft/inflation).

## What this descriptor IS

The IR2 (`EffectVmDescriptor2`) re-authoring of the spend relation the Rust `spend_circuit`
proves — 4-ary Merkle membership + nullifier + note-commitment preimage + value-binding, all
Poseidon2 `hash_fact` sites (the chip tuple is the byte-twin of the Rust `fact_site_always`
encoding at `shielded_ring_clearing_nleg_air.rs:300-324`: arity-7 absorb
`[x, f0, f1, f2, f3, 0xFACF, 1]`) — **with the security fix**:

* a fourth PI, `pi[3] = committed_root` — the committed shielded-commitment accumulator root,
  filled by the EXECUTOR from the ledger (NEVER from the wire), and at the apex `connect`ed to
  the turn's committed commitments-root exactly as the already-built
  `prove_shielded_spend_root_binding_node_segmented`
  (`circuit-prove/src/shielded_spend_leaf_adapter.rs:594`) binds claim lane 1;
* the membership chain's final fold (`parent` on the last row) is PI-pinned to `pi[3]` — the
  tree the spend opens against IS the committed accumulator;
* the `merkle_root` claim LANE (column 19, the `[nf, root, vb]` tuple slot the apex reads) is
  pinned to BOTH `pi[1]` (the claim slot, kept for `RING_LEG_CLAIM_LEN = 3` shape parity) and
  `pi[3]` — so `pi[1] ≡ pi[3]` is FORCED: there is no satisfiable assignment in which the wire
  supplies a root different from the committed accumulator root. The deployed wound — the
  verifier filling the root PI from `payload.merkle_root` — becomes UNSAT-or-unrepresentable.

Constraint map (Rust C-number → here): C2 position-validity → `posBody` gate (+ last-row
re-lowering, the deployed last-row-repair shape); C3 Merkle fold → `lkParent` (arity-7 fact
chip lookup, every row); C4 nullifier → `lkNullifier` — hashing `leaf_commit` (not the gated
`current`): row 0 has `current ≡ leaf_commit` (C6b boundary), so this binds the SAME relation
`nullifier = hash_fact(note_commitment, key[0..4])` with an EXACT ℤ-link to the recomputed
commitment, and IR2's first-row boundary gating replaces the C1 `is_leaf` selector column;
C5 chain continuity → `chainWindow`; C6a leaf-commit recompute → `lkLeafCommit`; C6b leaf
binding → first-row boundary `current − leaf_commit`; C7a value-binding recompute →
`lkValueBinding` (+ the two pad-zero gates); C7b/nullifier/root PI pins → `piBinding`s.

## What is PROVED here (the point — seam #15 in the AIR)

* **`root_is_pinned`** — field-faithful: a `Satisfied2` trace forces (i) the row-0
  `merkle_root` lane ≡ `pi[committed_root]`, (ii) the last row's `parent` — the root the
  membership chain actually folds to — ≡ `pi[committed_root]`, and (iii)
  `pi[merkle_root] ≡ pi[committed_root]`.
* **The theft-forge teeth** — `self_chosen_tree_unsat` / `chain_root_forge_unsat` /
  `wire_root_decoupled_unsat`: a trace whose membership root (lane or chain fold) differs from
  the committed-accumulator PI, or whose claim-root PI decouples from the committed-root PI,
  is UNSAT. A prover cannot open against a self-chosen tree.
* **`spend_relation_row0`** — under a sound chip table (`ChipTableSound`), a satisfying trace's
  row 0 carries the genuine spend relation: `nullifier = hash_fact(leaf_commit, key[0..4])`,
  `leaf_commit = hash_fact(value, [asset, owner, randomness])`, `value_binding =
  hash_fact(value, [asset, randomness, pad])`, `parent = hash_fact(current, [sibs, pos])`,
  `current ≡ leaf_commit`, and the nullifier/value-binding PI pins.
* **`zero_witness_satisfies`** — the constraint system is INHABITED (an explicit all-zero
  1-row witness with a genuine chip-table row), so the UNSAT teeth are not vacuous; and
  `forged_zero_trace_refused` runs a tooth on a concrete forged instance.

## What this descriptor does NOT yet close (named honestly)

* **#16 (value-link fold)** — this leaf publishes/recomputes `value_binding` exactly as the
  deployed leaf does, but the Σ-conservation fold over the legs' value cells (the
  `nleg_air.rs:384-408` conservation + range machinery) lives in the NEXT lane's
  transfer-clearing descriptor, not here.
* **#17 (Ristretto cut)** — retiring the off-AIR Ristretto conservation gate is the routing
  cutover, a later lane.
* Wiring this descriptor as an `Effect::Custom` carrier in `apply_shielded_transfer` (Rust,
  integrator), the descriptor-JSON golden regen into `circuit/descriptors/` + `PROVENANCE.json`
  row, and the apex fold that supplies `pi[3]` from the committed turn root. The VK-gate is
  RESOLVED descriptor-agnostically (a Custom carrier's own vk rides in the witness,
  version-checked by `require_custom_carrier_vk8`), so this lane is staged-additive.
* The multi-row recomposed-Merkle-path refinement walk (the `*Refine`-tier composition across
  the trace) — deferred exactly as `MerkleMembership4aryWideEmit` defers its walk.
* The post-A frontier residuals: `pedTwoGen` ≠ real Ristretto; the BabyBear `2^VALUE_BITS`
  amount cap. And this descriptor's digests are the deployed 1-felt (~31-bit) lanes — the
  felt-width widening of the SHIELDED tree is a separate campaign item, not smuggled in here.

## Axiom hygiene

Definitional descriptor + byte-pinned `#guard` on the wire string + non-vacuous teeth.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.BlindedMembershipEmit

namespace Dregg2.Circuit.Emit.ShieldedSpendDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow VmRowEnv VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId Table TraceFamily VmTrace zeroAsg envAt
   Satisfied2 chipLookupTuple ChipTableSound chip_lookup_sound CHIP_RATE CHIP_OUT_LANES padToE
   emitVmJson2 WindowExpr WindowConstraint memLog mapLog memOpsOf mapOpsOf)
open Dregg2.Circuit.Emit.BlindedMembershipEmit (ev ek eadd emul eneg esub)

set_option autoImplicit false

/-! ## §1 — the trace column layout (the Rust `spend_circuit::col` layout, plus the
`merkle_root` claim lane, plus the four fact-chip lane blocks).

One 4-ary Merkle level per trace row (depth = trace height), leaf on row 0, root = the LAST
row's `parent` (the deployed forward-chained-padding convention). -/

/-- Running membership hash (row 0: the leaf = the input note commitment). -/
def cCUR : Nat := 0
def cSIB0 : Nat := 1
def cSIB1 : Nat := 2
def cSIB2 : Nat := 3
/-- Child position 0..3 (absorbed into the fold, validated by the quartic gate). -/
def cPOS : Nat := 4
/-- `parent = hash_fact(current, [sib0, sib1, sib2, position])`; last row = the root. -/
def cPAR : Nat := 5
/-- The nullifier (row 0 pinned to `pi[0]`). -/
def cNUL : Nat := 6
/-- Spending-key limbs key[0..4] (the same 4-limb binding the deployed circuit uses). -/
def cKEY0 : Nat := 7
def cKEY1 : Nat := 8
def cKEY2 : Nat := 9
def cKEY3 : Nat := 10
/-- Note value / asset / owner / randomness — the leaf-commitment preimage (HIDDEN). -/
def cVAL : Nat := 11
def cASSET : Nat := 12
def cOWNER : Nat := 13
def cRAND : Nat := 14
/-- Recomputed note commitment `hash_fact(value, [asset, owner, randomness])` (C6a). -/
def cLEAF : Nat := 15
/-- Value-binding commitment `hash_fact(value, [asset, randomness, pad0])` (C7a). -/
def cVB : Nat := 16
/-- Value-binding pad cells (pinned to 0; `cVBP1` vestigial, kept for layout parity). -/
def cVBP0 : Nat := 17
def cVBP1 : Nat := 18
/-- **The `merkle_root` claim LANE** — the `[nf, root, vb]` tuple slot the apex `connect`s,
carried constant across rows and pinned to BOTH `pi[1]` and `pi[3]` (the #15 fix). -/
def cROOT : Nat := 19

/-- The four fact-chip lane blocks (`CHIP_OUT_LANES − 1 = 7` exposed permutation lanes each,
exactly the Rust `alloc_lanes()` discipline of `shielded_ring_clearing_nleg_air.rs`). -/
def LANE_PAR : Nat := 20
def LANE_NUL : Nat := 27
def LANE_LEAF : Nat := 34
def LANE_VB : Nat := 41

/-- Main-trace width: the 20 spend columns + 4 × 7 chip lanes. -/
def SPEND_WIDTH : Nat := 48

/-- PI 0: the published nullifier. -/
def piNUL : Nat := 0
/-- PI 1: the `merkle_root` claim slot (kept at slot 1 for `[nf, root, vb]` shape parity with
`RING_LEG_CLAIM_LEN`; provably ≡ `pi[3]` on any satisfying trace). -/
def piROOT : Nat := 1
/-- PI 2: the published value-binding commitment. -/
def piVB : Nat := 2
/-- **PI 3: the committed shielded-commitment accumulator root** — executor-filled from the
LEDGER, apex-connected to the committed turn root; NEVER a wire value. -/
def piCOMMITTED : Nat := 3
/-- Number of public inputs: `[nullifier, merkle_root, value_binding, committed_root]`. -/
def SPEND_PI_COUNT : Nat := 4

/-! ## §2 — the `hash_fact` chip absorb (the byte-twin of the Rust `fact_site_always`). -/

/-- The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]) — `0xFACF`,
identical to the Rust `NS_FACT_MARK` in the 2-leg/N-leg ring modules and the note-spend
adapter's `hash_fact` KAT. -/
def NS_FACT_MARK : ℤ := 64207

/-- The 7-lane `hash_fact` absorb block `[x, f0, f1, f2, f3, MARK, 1]` (missing fact slots ride
literal zeros) — slots 0..6 of the Rust `fact_site_always` tuple, term-for-term. -/
def factIns (cols : List Nat) : List EmittedExpr :=
  padToE 5 (cols.map .var) ++ [.const NS_FACT_MARK, .const 1]

/-- The 7 lane columns of a fact site's chip lookup (the `lane_base + j, j ∈ 0..7` block). -/
def laneCols (base : Nat) : List Nat := (List.range (CHIP_OUT_LANES - 1)).map (base + ·)

/-- A 5-input fact absorb evaluates to `[x, f0, f1, f2, f3, MARK, 1]`. -/
theorem factIns_eval_5 (a : Assignment) (c0 c1 c2 c3 c4 : Nat) :
    (factIns [c0, c1, c2, c3, c4]).map (·.eval a)
      = [a c0, a c1, a c2, a c3, a c4, NS_FACT_MARK, 1] := by
  simp [factIns, padToE, EmittedExpr.eval]

/-- A 4-input fact absorb evaluates to `[x, f0, f1, f2, 0, MARK, 1]` (the padded 5th slot). -/
theorem factIns_eval_4 (a : Assignment) (c0 c1 c2 c3 : Nat) :
    (factIns [c0, c1, c2, c3]).map (·.eval a)
      = [a c0, a c1, a c2, a c3, 0, NS_FACT_MARK, 1] := by
  simp [factIns, padToE, EmittedExpr.eval]

/-! ## §3 — the constraints. -/

/-- C2: position validity `pos·(pos−1)·(pos−2)·(pos−3)` (degree 4). -/
def posBody : EmittedExpr :=
  emul (emul (ev cPOS) (esub (ev cPOS) (ek 1)))
    (emul (esub (ev cPOS) (ek 2)) (esub (ev cPOS) (ek 3)))

/-- C3: the Merkle fold — `parent = hash_fact(current, [sib0, sib1, sib2, position])`,
every row (forward-chained padding keeps it satisfiable on pad rows, the deployed shape). -/
def lkParent : VmConstraint2 :=
  .lookup ⟨.poseidon2,
    chipLookupTuple (factIns [cCUR, cSIB0, cSIB1, cSIB2, cPOS]) cPAR (laneCols LANE_PAR)⟩

/-- C4′: the nullifier — `nullifier = hash_fact(leaf_commit, key[0..4])`, every row. Hashing
the RECOMPUTED commitment (C6a's output) instead of the `is_leaf`-gated `current` binds the
same relation with an exact ℤ-link to the note commitment; row 0's C6b boundary ties
`current ≡ leaf_commit`, so the membership leaf is that same commitment. -/
def lkNullifier : VmConstraint2 :=
  .lookup ⟨.poseidon2,
    chipLookupTuple (factIns [cLEAF, cKEY0, cKEY1, cKEY2, cKEY3]) cNUL (laneCols LANE_NUL)⟩

/-- C6a: the note-commitment recompute — `leaf_commit = hash_fact(value, [asset, owner,
randomness])`, every row. -/
def lkLeafCommit : VmConstraint2 :=
  .lookup ⟨.poseidon2,
    chipLookupTuple (factIns [cVAL, cASSET, cOWNER, cRAND]) cLEAF (laneCols LANE_LEAF)⟩

/-- C7a: the value-binding recompute — `value_binding = hash_fact(value, [asset, randomness,
pad0])`, every row, from the SAME cells C6a binds into the leaf. -/
def lkValueBinding : VmConstraint2 :=
  .lookup ⟨.poseidon2,
    chipLookupTuple (factIns [cVAL, cASSET, cRAND, cVBP0]) cVB (laneCols LANE_VB)⟩

/-- C5: chain continuity `next.current − this.parent` (transition window). -/
def chainWindow : WindowExpr := .add (.nxt cCUR) (.mul (.const (-1)) (.loc cPAR))

/-- The `merkle_root` claim lane is carried constant: `next.merkle_root − this.merkle_root`. -/
def rootCarryWindow : WindowExpr := .add (.nxt cROOT) (.mul (.const (-1)) (.loc cROOT))

/-- The full constraint list. Per-row gates are re-lowered on the last row (gates ride the
`when_transition()` domain — the deployed last-row-repair shape, cf. the wide membership). -/
def spendConstraints : List VmConstraint2 :=
  [ -- per-row gates (C2 position validity; C7 pad zeros)
    .base (.gate posBody)
  , .base (.gate (ev cVBP0))
  , .base (.gate (ev cVBP1))
    -- the four Poseidon2 fact sites (C3, C4′, C6a, C7a)
  , lkParent
  , lkNullifier
  , lkLeafCommit
  , lkValueBinding
    -- C5 chain continuity + the root-lane carry
  , .windowGate ⟨chainWindow, true⟩
  , .windowGate ⟨rootCarryWindow, true⟩
    -- C6b: the leaf IS the recomputed note commitment (the value-theft tooth), row 0
  , .base (.boundary .first (esub (ev cCUR) (ev cLEAF)))
    -- last-row re-lowerings of the per-row gates
  , .base (.boundary .last posBody)
  , .base (.boundary .last (ev cVBP0))
  , .base (.boundary .last (ev cVBP1))
    -- PI pins: nullifier, the claim tuple, the value binding
  , .base (.piBinding .first cNUL piNUL)
  , .base (.piBinding .first cROOT piROOT)
  , .base (.piBinding .first cVB piVB)
    -- ⚑ THE #15 PIN: the root lane AND the chain's final fold are the COMMITTED root PI
  , .base (.piBinding .first cROOT piCOMMITTED)
  , .base (.piBinding .last cROOT piCOMMITTED)
  , .base (.piBinding .last cPAR piCOMMITTED)
  ]

/-- **`shieldedSpendDesc`** — the Lean-authored shielded-spend descriptor with the membership
root pinned to the committed accumulator (closes seam #15 in the AIR). Staged-additive: rides
as an `Effect::Custom` carrier; no deployed descriptor or registry entry changes here. -/
def shieldedSpendDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-spend-pinned-root::v1"
  , traceWidth  := SPEND_WIDTH
  , piCount     := SPEND_PI_COUNT
  , tables      := []
  , constraints := spendConstraints
  , hashSites   := []
  , ranges      := [] }

-- Non-vacuous structural pins.
#guard shieldedSpendDesc.traceWidth == 48
#guard shieldedSpendDesc.piCount == 4
#guard shieldedSpendDesc.constraints.length == 19
#guard (factIns [cCUR, cSIB0, cSIB1, cSIB2, cPOS]).length == 7
#guard (factIns [cVAL, cASSET, cOWNER, cRAND]).length == 7
#guard (chipLookupTuple (factIns [cCUR, cSIB0, cSIB1, cSIB2, cPOS]) cPAR (laneCols LANE_PAR)).length
  == 1 + CHIP_RATE + CHIP_OUT_LANES
#guard laneCols LANE_PAR == [20, 21, 22, 23, 24, 25, 26]
#guard laneCols LANE_VB == [41, 42, 43, 44, 45, 46, 47]

-- Window canaries: the chain window vanishes iff next.current = this.parent.
#guard decide (chainWindow.eval
  { loc := fun c => if c = cPAR then 9 else 0
  , nxt := fun c => if c = cCUR then 9 else 0
  , pub := zeroAsg } = 0)
#guard decide (¬ (chainWindow.eval
  { loc := fun c => if c = cPAR then 9 else 0
  , nxt := fun c => if c = cCUR then 8 else 0
  , pub := zeroAsg } = 0))

/-! ## §4 — `root_is_pinned`: the membership root IS the committed accumulator PI.

Field-faithful (`ZMOD 2013265921` throughout, matching the deployed BabyBear denotation). -/

private theorem modeq_of_sub {x y : ℤ} (h : x + -1 * y ≡ 0 [ZMOD 2013265921]) :
    x ≡ y [ZMOD 2013265921] := by
  have hd := Int.modEq_iff_dvd.mp h
  have he : (0 : ℤ) - (x + -1 * y) = y - x := by ring
  rw [he] at hd
  exact Int.modEq_iff_dvd.mpr hd

/-- **⚑ THE KEYSTONE (`root_is_pinned`).** A satisfying trace forces:
(i) the row-0 `merkle_root` claim lane ≡ the committed-accumulator PI;
(ii) the LAST row's `parent` — the root the membership chain actually folds to — ≡ the
committed-accumulator PI; and (iii) `pi[merkle_root] ≡ pi[committed_root]` — the claim slot the
apex reads CANNOT decouple from the committed root. The spend can only open against the
committed accumulator; a self-chosen tree has no satisfying assignment. -/
theorem root_is_pinned (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t) :
    (t.rows.getD 0 zeroAsg cROOT ≡ t.pub piCOMMITTED [ZMOD 2013265921])
    ∧ (t.rows.getD (t.rows.length - 1) zeroAsg cPAR ≡ t.pub piCOMMITTED [ZMOD 2013265921])
    ∧ (t.pub piROOT ≡ t.pub piCOMMITTED [ZMOD 2013265921]) := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  have h0c := hsat.rowConstraints 0 hpos (.base (.piBinding .first cROOT piCOMMITTED))
    (by simp [shieldedSpendDesc, spendConstraints])
  have h0r := hsat.rowConstraints 0 hpos (.base (.piBinding .first cROOT piROOT))
    (by simp [shieldedSpendDesc, spendConstraints])
  have hlt : t.rows.length - 1 < t.rows.length := by omega
  have hL := hsat.rowConstraints (t.rows.length - 1) hlt
    (.base (.piBinding .last cPAR piCOMMITTED))
    (by simp [shieldedSpendDesc, spendConstraints])
  have hlastb : ((t.rows.length - 1) + 1 == t.rows.length) = true := by
    have h : t.rows.length - 1 + 1 = t.rows.length := by omega
    simpa using h
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h0c h0r hL
  have e0c := h0c rfl
  have e0r := h0r rfl
  have eL := hL hlastb
  exact ⟨e0c, eL, e0r.symm.trans e0c⟩

/-! ## §5 — the theft-forge teeth: `merkle_root ≠ committed_root` is UNSAT. -/

/-- **THE THEFT TOOTH.** A trace whose row-0 `merkle_root` lane differs (mod p) from the
committed-accumulator PI does not satisfy the descriptor — a prover cannot expose a claim root
for a tree of their own choosing. -/
theorem self_chosen_tree_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hforge : ¬ (t.rows.getD 0 zeroAsg cROOT ≡ t.pub piCOMMITTED [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedSpendDesc minit mfin maddrs t :=
  fun hsat => hforge (root_is_pinned hash minit mfin maddrs t hne hsat).1

/-- **THE CHAIN TOOTH.** A trace whose membership chain folds to anything other than the
committed-accumulator PI (the last row's `parent`) is UNSAT — the OPENED tree is the committed
one, not merely the exposed lane. -/
theorem chain_root_forge_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hforge : ¬ (t.rows.getD (t.rows.length - 1) zeroAsg cPAR
      ≡ t.pub piCOMMITTED [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedSpendDesc minit mfin maddrs t :=
  fun hsat => hforge (root_is_pinned hash minit mfin maddrs t hne hsat).2.1

/-- **THE WIRE TOOTH.** Public inputs whose claim-root slot decouples from the committed-root
slot admit NO satisfying trace — the deployed seam (`payload.merkle_root` filling `pi[1]`
independently of any committed root) is unrepresentable against this descriptor. -/
theorem wire_root_decoupled_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hforge : ¬ (t.pub piROOT ≡ t.pub piCOMMITTED [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedSpendDesc minit mfin maddrs t :=
  fun hsat => hforge (root_is_pinned hash minit mfin maddrs t hne hsat).2.2

/-! ## §6 — the spend relation on row 0 (under a sound chip table). -/

/-- Under a SOUND chip table (`ChipTableSound hash (t.tf .poseidon2)` — the chip AIR's own
per-permutation faithfulness), a satisfying trace's row 0 carries the genuine C-shape:
the four `hash_fact` bindings hold as ℤ equations of the abstract `hash`, the membership leaf
is the recomputed note commitment, and the nullifier / value-binding PIs are pinned. -/
theorem spend_relation_row0 (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2)) :
    let a := t.rows.getD 0 zeroAsg
    a cPAR = hash [a cCUR, a cSIB0, a cSIB1, a cSIB2, a cPOS, NS_FACT_MARK, 1]
    ∧ a cNUL = hash [a cLEAF, a cKEY0, a cKEY1, a cKEY2, a cKEY3, NS_FACT_MARK, 1]
    ∧ a cLEAF = hash [a cVAL, a cASSET, a cOWNER, a cRAND, 0, NS_FACT_MARK, 1]
    ∧ a cVB = hash [a cVAL, a cASSET, a cRAND, a cVBP0, 0, NS_FACT_MARK, 1]
    ∧ (a cCUR ≡ a cLEAF [ZMOD 2013265921])
    ∧ (a cNUL ≡ t.pub piNUL [ZMOD 2013265921])
    ∧ (a cVB ≡ t.pub piVB [ZMOD 2013265921]) := by
  intro a
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons x l => simp
  -- the four chip lookups on row 0
  have hkP := hsat.rowConstraints 0 hpos lkParent
    (by simp [shieldedSpendDesc, spendConstraints])
  have hkN := hsat.rowConstraints 0 hpos lkNullifier
    (by simp [shieldedSpendDesc, spendConstraints])
  have hkL := hsat.rowConstraints 0 hpos lkLeafCommit
    (by simp [shieldedSpendDesc, spendConstraints])
  have hkV := hsat.rowConstraints 0 hpos lkValueBinding
    (by simp [shieldedSpendDesc, spendConstraints])
  simp only [lkParent, lkNullifier, lkLeafCommit, lkValueBinding,
    Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] at hkP hkN hkL hkV
  have hlen5 : (factIns [cCUR, cSIB0, cSIB1, cSIB2, cPOS]).length ≤ CHIP_RATE := by decide
  have hlenN : (factIns [cLEAF, cKEY0, cKEY1, cKEY2, cKEY3]).length ≤ CHIP_RATE := by decide
  have hlenL : (factIns [cVAL, cASSET, cOWNER, cRAND]).length ≤ CHIP_RATE := by decide
  have hlenV : (factIns [cVAL, cASSET, cRAND, cVBP0]).length ≤ CHIP_RATE := by decide
  have eP := chip_lookup_sound hash (t.tf TableId.poseidon2) hChip ((envAt t 0).loc)
    _ cPAR (laneCols LANE_PAR) hlen5 hkP
  have eN := chip_lookup_sound hash (t.tf TableId.poseidon2) hChip ((envAt t 0).loc)
    _ cNUL (laneCols LANE_NUL) hlenN hkN
  have eL := chip_lookup_sound hash (t.tf TableId.poseidon2) hChip ((envAt t 0).loc)
    _ cLEAF (laneCols LANE_LEAF) hlenL hkL
  have eV := chip_lookup_sound hash (t.tf TableId.poseidon2) hChip ((envAt t 0).loc)
    _ cVB (laneCols LANE_VB) hlenV hkV
  rw [factIns_eval_5] at eP eN
  rw [factIns_eval_4] at eL eV
  -- C6b (row-0 boundary) + the two PI pins
  have hb := hsat.rowConstraints 0 hpos (.base (.boundary .first (esub (ev cCUR) (ev cLEAF))))
    (by simp [shieldedSpendDesc, spendConstraints])
  have hpn := hsat.rowConstraints 0 hpos (.base (.piBinding .first cNUL piNUL))
    (by simp [shieldedSpendDesc, spendConstraints])
  have hpv := hsat.rowConstraints 0 hpos (.base (.piBinding .first cVB piVB))
    (by simp [shieldedSpendDesc, spendConstraints])
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at hb hpn hpv
  have hb0 := hb rfl
  simp only [esub, eadd, emul, eneg, ev, ek, EmittedExpr.eval] at hb0
  exact ⟨eP, eN, eL, eV, modeq_of_sub hb0, hpn rfl, hpv rfl⟩

/-! ## §7 — non-vacuity: an explicit satisfying witness (the teeth bite something real). -/

/-- The toy hash (the chip-table soundness carrier is a parameter; zero suffices here). -/
def hzero : List ℤ → ℤ := fun _ => 0

/-- The one chip row every fact lookup of the all-zero trace evaluates to:
`arity 7 :: padded [0,0,0,0,0,MARK,1] :: (hash = 0) :: 7 zero lanes`. -/
def zChipRow : List ℤ :=
  [7, 0, 0, 0, 0, 0, 64207, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The zero-witness trace family: the chip table carries exactly the one genuine row. -/
def zTf : TraceFamily := fun tid =>
  match tid with
  | .poseidon2 => [zChipRow]
  | _ => []

/-- The all-zero 1-row witness (row 0 is both first and last; every PI is 0). -/
def zTrace : VmTrace := { rows := [zeroAsg], pub := zeroAsg, tf := zTf }

/-- **The descriptor is SATISFIABLE** — an explicit witness, so the UNSAT teeth above are not
vacuously true of an empty relation. -/
theorem zero_witness_satisfies :
    Satisfied2 hzero shieldedSpendDesc (fun _ => 0) (fun _ => (0, 0)) [] zTrace := by
  have hmemlog : memLog shieldedSpendDesc zTrace = [] := rfl
  have hmaplog : mapLog shieldedSpendDesc zTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [zTrace] using hi
      omega
    subst hi0
    simp only [shieldedSpendDesc, spendConstraints, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [lkParent, lkNullifier, lkLeafCommit, lkValueBinding,
        Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt,
        Dregg2.Circuit.DescriptorIR2.WindowConstraint.holdsAt,
        Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt, zTrace, zTf]
    all_goals trivial
  · -- rowHashes: no v1 hash sites
    intro i _
    exact trivial
  · -- rowRanges: no ranges
    intro i _ r hr
    simp [shieldedSpendDesc] at hr
  · -- memAddrsNodup
    simp
  · -- memClosed
    intro op hop
    rw [hmemlog] at hop
    cases hop
  · -- memDisciplined
    rw [hmemlog]
    trivial
  · -- memBalanced (empty boundary, empty log)
    rw [hmemlog]
    rfl
  · -- memTableFaithful
    rw [hmemlog]
    rfl
  · -- mapTableFaithful
    rw [hmaplog]
    rfl

/-- A concretely FORGED instance (committed-root PI = 1, everything else 0): the theft tooth
refuses it. The forge class is inhabited and the refusal is exercised, not asserted. -/
def forgedPub : Assignment := fun k => if k = piCOMMITTED then 1 else 0

def forgedTrace : VmTrace := { rows := [zeroAsg], pub := forgedPub, tf := zTf }

theorem forged_zero_trace_refused :
    ¬ Satisfied2 hzero shieldedSpendDesc (fun _ => 0) (fun _ => (0, 0)) [] forgedTrace :=
  self_chosen_tree_unsat hzero (fun _ => 0) (fun _ => (0, 0)) [] forgedTrace
    (by simp [forgedTrace]) (by decide)

/-! ## §8 — the byte-pinned wire golden (generated once via `#eval repr (emitVmJson2 …)`;
the Rust decoder ingests THIS string at the coordinated integrator step). -/

/-- Exact emitted-wire golden (generated via `#eval repr (emitVmJson2 shieldedSpendDesc)`).
Rust includes these bytes verbatim at the coordinated integrator step. -/
def SHIELDED_SPEND_PINNED_ROOT_GOLDEN : String :=
  "{\"name\":\"dregg-shielded-spend-pinned-root::v1\",\"ir\":2,\"trace_width\":48,\"public_input_count\":4,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":3}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":17}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":18}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31},{\"t\":\"var\",\"v\":32},{\"t\":\"var\",\"v\":33}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":34},{\"t\":\"var\",\"v\":35},{\"t\":\"var\",\"v\":36},{\"t\":\"var\",\"v\":37},{\"t\":\"var\",\"v\":38},{\"t\":\"var\",\"v\":39},{\"t\":\"var\",\"v\":40}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":17},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":41},{\"t\":\"var\",\"v\":42},{\"t\":\"var\",\"v\":43},{\"t\":\"var\",\"v\":44},{\"t\":\"var\",\"v\":45},{\"t\":\"var\",\"v\":46},{\"t\":\"var\",\"v\":47}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":19}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":3}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"var\",\"v\":17}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"var\",\"v\":18}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":19,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":5,\"pi_index\":3}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 shieldedSpendDesc == SHIELDED_SPEND_PINNED_ROOT_GOLDEN

/-! ## §9 — axiom hygiene on the keystones. -/

#assert_axioms root_is_pinned
#assert_axioms self_chosen_tree_unsat
#assert_axioms chain_root_forge_unsat
#assert_axioms wire_root_decoupled_unsat
#assert_axioms spend_relation_row0
#assert_axioms zero_witness_satisfies
#assert_axioms forged_zero_trace_refused

end Dregg2.Circuit.Emit.ShieldedSpendDescriptor
