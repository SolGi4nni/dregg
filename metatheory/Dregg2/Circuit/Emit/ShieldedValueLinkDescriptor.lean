/-
# Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor — the Lean-authored VALUE-LINK +
# Σ-CONSERVATION clearing block: seam #16 folded IN-AIR (shielded Option-A, lane 2).

**This is Lean-authored AIR.** This module authors the algebra; Rust parses the emitted IR2
bytes and supplies witnesses — it constructs no constraints. SECOND build lane of the
ember-approved shielded Option-A redesign (`docs/DECISION-shielded-redesign-2026-07-20.md`,
`docs/PLAN-shielded-apex-redesign-2026-07-20.md` §3), following lane 1
(`ShieldedSpendDescriptor.lean`, which pinned `merkle_root` to the committed accumulator —
seam #15). Seam **#16**: the value-link (STARK leaf value ↔ the conserved amount) is checked
ONLY in tests (`verify_value_link` needs the secret opening, so it cannot run in `apply`), and
deployed conservation gates only the Shor-broken Ristretto legs — a prover can decouple the
leaf values from the legs and MINT. The fix authored here is the `nleg_air.rs` binding shape
(`circuit-prove/src/shielded_ring_clearing_nleg_air.rs:27-70,436-451,384-395`), in Lean:

## What this descriptor IS

`shieldedValueLinkDesc` — one clearing slot per trace row (M-in/K-out rides pad slots with
value 0, the deployed forward-chained-padding style). Per row, from the SAME witness cells:

* **(a) the value-link, chip-bound.** `value_binding = hash_fact(value, [asset, randomness,
  pad0])` (`lkValueBinding`) AND `leaf_commit = hash_fact(value, [asset, owner, randomness])`
  (`lkLeafCommit`) are BOTH Poseidon2 fact-chip lookups over the SAME `value`/`asset`/
  `randomness` columns — the byte-twin of the Rust `fact_site_always` arity-7 absorb
  `[x, f0, f1, f2, f3, 0xFACF, 1]`, exactly the encoding lane 1 used. The published binding
  cannot float free of the leaf: both digests are ℤ-images of one shared value cell. (The apex
  `connect` of an EXTERNAL spend leaf's `value_binding` lane to this block's — where Poseidon2
  CR turns shared-digest into shared-preimage — is the deferred composition, lane 3.)
* **(b) Σ-conservation, in-AIR.** A cumulative column `acc` is SEEDED on the first row
  (`acc = value − out_val`), STEPPED by a `windowGate` on every transition
  (`next.acc = acc + next.value − next.out_val`), and forced to ZERO on the last row — the
  BilateralAggregation cumulative-sum shape. A satisfying trace therefore carries
  `Σ value ≡ Σ out_val [ZMOD p]` over the SAME in-AIR value cells the bindings hash: there is
  no second, free "Pedersen value" to decouple. No secret opening is ever exposed — the
  values/assets/randomness are WITNESS columns (hidden under the hiding PCS); only
  `value_binding`/`leaf_commit` digests are PI-pinned.

## What is PROVED here (the point — seam #16 in the AIR)

* **`value_link_bound`** — under a sound chip table, a `Satisfied2` trace forces EVERY row's
  `value_binding` and `leaf_commit` to be the genuine `hash_fact` images of the SAME
  value/asset/randomness cells (chip-bound ℤ-link), the pad cell ≡ 0, and the row-0 digests
  pinned to the PIs. Field-faithful (ZMOD 2013265921) on the pins; EXACT ℤ on the chip links.
* **`value_decoupled_unsat`** — the tooth: a trace whose PUBLISHED `value_binding` PI decouples
  from the `hash_fact` of the leaf's value cells admits NO satisfying assignment.
* **`conservation_holds`** — the in-AIR Σ-fold forces
  `Σ value ≡ Σ out_val [ZMOD 2013265921]` (running-sum induction over the seed + window + last
  boundary). **`mint_unbalanced_unsat`** — the tooth: an unbalanced trace (a mint) is UNSAT.
* **Non-vacuity** — `honest_balanced_satisfies`: an explicit 2-row balanced witness
  (values 5+3 in, 4+4 out, genuine chip rows) SATISFIES the descriptor; `mint_refused` /
  `decoupled_refused` exercise both teeth on concrete forged instances.

## What this lane does NOT close (named honestly)

* **#17 (Ristretto cut)** — this closes #16 in-AIR; it does NOT by itself replace the deployed
  Ristretto conservation gate. Retiring GATE 2 is the routing cutover, a later lane.
* Composition with lane 1's root-pinned spend descriptor into ONE transfer-clearing descriptor
  (the apex `connect` of each leg's claim tuple), the `Effect::Custom` wiring in
  `apply_shielded_transfer`, and the descriptor-JSON golden regen into `circuit/descriptors/` +
  `PROVENANCE.json` — integrator steps.
* **The range residual.** Conservation here is FIELD conservation (mod p). The ℤ-integer lift
  needs the `VALUE_BITS` bit-decomposition range gadget (`nleg_air.rs:397-408`,
  `Dregg2.Bignum.legs_noWrap_conservation`) — the named BabyBear `2^VALUE_BITS` amount-cap
  residual, deferred with the `pedTwoGen ≠ real Ristretto` faithfulness residual (plan §6).
* This block's digests are the deployed 1-felt (~31-bit) lanes — the felt-width widening of the
  shielded tree is a separate campaign item, not smuggled in here.

## Axiom hygiene

Definitional descriptor + byte-pinned `#guard` on the wire string + both-polarity teeth with an
explicit satisfying witness. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.BlindedMembershipEmit

namespace Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow VmRowEnv VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId Table TraceFamily VmTrace zeroAsg envAt
   Satisfied2 chipLookupTupleNarrow poseidon2narrow ChipTableSound CHIP_RATE CHIP_OUT_LANES padToE
   emitVmJson2 WindowExpr WindowConstraint memLog mapLog memOpsOf mapOpsOf)
open Dregg2.Circuit.ChipNarrowLookup (chip_lookup_narrow_sound_of_wide_table)
open Dregg2.Circuit.Emit.BlindedMembershipEmit (ev ek eadd emul eneg esub)

set_option autoImplicit false

/-! ## §1 — the trace column layout: one clearing slot per row.

Per row: an input-note block (`value`/`asset`/`owner`/`randomness` + the recomputed
`leaf_commit` and `value_binding`, the two fact-chip lane blocks) and the row's `out_val` +
the running conservation accumulator. Pad slots ride value 0. -/

/-- Input-note value (WITNESS — hidden under the hiding PCS; the cell BOTH hashes bind). -/
def cVAL : Nat := 0
/-- Asset type (witness; absorbed into BOTH the leaf and the value binding). -/
def cASSET : Nat := 1
/-- Note owner (witness; leaf-commitment preimage limb). -/
def cOWNER : Nat := 2
/-- Commitment randomness (witness; absorbed into BOTH the leaf and the value binding). -/
def cRAND : Nat := 3
/-- Value-binding pad cell (pinned to 0 per row + last row, the deployed vb_pad0). -/
def cVBP0 : Nat := 4
/-- Recomputed note commitment `hash_fact(value, [asset, owner, randomness])` — THE LEAF. -/
def cLEAF : Nat := 5
/-- Recomputed value binding `hash_fact(value, [asset, randomness, pad0])` — same cells. -/
def cVB : Nat := 6
/-- The row's output value `out_val` (witness). -/
def cOUT : Nat := 7
/-- The running conservation accumulator `Σ (value − out_val)` up to this row. -/
def cACC : Nat := 8

/-- Main-trace width: the 9 clearing columns. The two `CHIP_OUT_LANES − 1 = 7` fact-chip lane
blocks the WIDE `TID_P2` tuples carried (the Rust `alloc_lanes()` discipline of
`shielded_ring_clearing_nleg_air.rs`) are GONE (E7 narrowing, `ChipNarrowLookup.lean`) — they sat
at lane positions 18..24 of the 25-wide tuples and entered no soundness conclusion. -/
def VLINK_WIDTH : Nat := 9

/-- PI 0: the published `value_binding` (the claim slot the apex `connect`s). -/
def piVB : Nat := 0
/-- PI 1: the published `leaf_commit` (the membership-leaf digest the spend leaf opens). -/
def piLEAF : Nat := 1
/-- Number of public inputs: `[value_binding, leaf_commit]`. -/
def VLINK_PI_COUNT : Nat := 2

/-! ## §2 — the `hash_fact` chip absorb (the byte-twin of the Rust `fact_site_always`;
term-for-term the encoding lane 1 (`ShieldedSpendDescriptor.lean`) used). -/

/-- The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]) — `0xFACF`,
identical to the Rust `NS_FACT_MARK` in the 2-leg/N-leg ring modules. -/
def NS_FACT_MARK : ℤ := 64207

/-- The 7-lane `hash_fact` absorb block `[x, f0, f1, f2, f3, MARK, 1]` (missing fact slots ride
literal zeros) — slots 0..6 of the Rust `fact_site_always` tuple, term-for-term. -/
def factIns (cols : List Nat) : List EmittedExpr :=
  padToE 5 (cols.map .var) ++ [.const NS_FACT_MARK, .const 1]

/-- A 4-input fact absorb evaluates to `[x, f0, f1, f2, 0, MARK, 1]` (the padded 5th slot). -/
theorem factIns_eval_4 (a : Assignment) (c0 c1 c2 c3 : Nat) :
    (factIns [c0, c1, c2, c3]).map (·.eval a)
      = [a c0, a c1, a c2, a c3, 0, NS_FACT_MARK, 1] := by
  simp [factIns, padToE, EmittedExpr.eval]

/-! ## §3 — the constraints: the reusable value-link block + the Σ-conservation block. -/

/-- The leaf-commit recompute — `leaf_commit = hash_fact(value, [asset, owner, randomness])`,
every row (the fact site the membership leaf commits; lane 1's C6a shape). -/
def lkLeafCommit : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow (factIns [cVAL, cASSET, cOWNER, cRAND]) cLEAF⟩

/-- The value-binding recompute — `value_binding = hash_fact(value, [asset, randomness,
pad0])`, every row, from the SAME cells `lkLeafCommit` binds into the leaf (the
`nleg_air.rs:436-451` fusion anchor). -/
def lkValueBinding : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow (factIns [cVAL, cASSET, cRAND, cVBP0]) cVB⟩

/-- `a − b` over a row window. -/
def wsub (a b : WindowExpr) : WindowExpr := .add a (.mul (.const (-1)) b)

/-- The conservation step: `next.acc − (acc + (next.value − next.out_val))` (vanishes on every
transition — the BilateralAggregation cumulative-sum window). -/
def accWindow : WindowExpr :=
  wsub (.nxt cACC) (.add (.loc cACC) (wsub (.nxt cVAL) (.nxt cOUT)))

def accStep : WindowConstraint := ⟨accWindow, true⟩

/-- The conservation seed (first row): `acc − (value − out_val)`. -/
def seedBody : EmittedExpr := esub (ev cACC) (esub (ev cVAL) (ev cOUT))

/-- **The reusable VALUE-LINK block** — pad-zero gate (per-row + last-row re-lowering, since
per-row gates ride the `when_transition()` domain) + the two fact-chip recomputes over shared
cells. This is the block a composed transfer-clearing descriptor re-uses per input leg. -/
def valueLinkConstraints : List VmConstraint2 :=
  [ .base (.gate (ev cVBP0))
  , lkLeafCommit
  , lkValueBinding
  , .base (.boundary .last (ev cVBP0)) ]

/-- **The Σ-CONSERVATION block** — seed + windowed cumulative step + final-row zero. -/
def conservationConstraints : List VmConstraint2 :=
  [ .windowGate accStep
  , .base (.boundary .first seedBody)
  , .base (.boundary .last (ev cACC)) ]

/-- The row-0 claim pins: the published `value_binding` and `leaf_commit` digests. -/
def claimPins : List VmConstraint2 :=
  [ .base (.piBinding .first cVB piVB)
  , .base (.piBinding .first cLEAF piLEAF) ]

def linkClearConstraints : List VmConstraint2 :=
  valueLinkConstraints ++ conservationConstraints ++ claimPins

/-- **`shieldedValueLinkDesc`** — the Lean-authored value-link + Σ-conservation clearing
descriptor (closes seam #16 in the AIR). Staged-additive: rides as an `Effect::Custom`
carrier; no deployed descriptor or registry entry changes here. -/
def shieldedValueLinkDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-value-link-conserve::v1"
  , traceWidth  := VLINK_WIDTH
  , piCount     := VLINK_PI_COUNT
  , tables      := []
  , constraints := linkClearConstraints
  , hashSites   := []
  , ranges      := [] }

-- Non-vacuous structural pins.
#guard shieldedValueLinkDesc.traceWidth == 9
#guard shieldedValueLinkDesc.piCount == 2
#guard shieldedValueLinkDesc.constraints.length == 9
#guard (factIns [cVAL, cASSET, cRAND, cVBP0]).length == 7
#guard (factIns [cVAL, cASSET, cOWNER, cRAND]).length == 7
#guard (chipLookupTupleNarrow (factIns [cVAL, cASSET, cRAND, cVBP0]) cVB).length
  == 1 + CHIP_RATE + 1
-- The narrowing dropped exactly 2 × (CHIP_OUT_LANES − 1) = 14 main columns for the same two
-- forced `hash_fact` equations.
#guard VLINK_WIDTH + 2 * (CHIP_OUT_LANES - 1) == 23
#guard poseidon2narrow.wireId == 8

-- Window canaries: the conservation step vanishes iff the accumulator threads the net.
#guard decide (accWindow.eval
  { loc := fun c => if c = cACC then 1 else 0
  , nxt := fun c => if c = cVAL then 3 else if c = cOUT then 4 else 0
  , pub := zeroAsg } = 0)
#guard decide (¬ (accWindow.eval
  { loc := fun c => if c = cACC then 1 else 0
  , nxt := fun c => if c = cVAL then 3 else if c = cOUT then 5 else 0
  , pub := zeroAsg } = 0))

/-! ## §4 — trace accessors + the running sum. -/

/-- Row `i`'s assignment (off-the-end default never load-bearing on a well-formed trace). -/
def rowAt (t : VmTrace) (i : Nat) : Assignment := t.rows.getD i zeroAsg

def valAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i cVAL
def outAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i cOUT
def accAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i cACC
/-- The row's net contribution `value − out_val`. -/
def netAt (t : VmTrace) (i : Nat) : ℤ := valAt t i - outAt t i

/-- The prefix sum `f 0 + f 1 + … + f n`. -/
def prefixSum (f : Nat → ℤ) : Nat → ℤ
  | 0     => f 0
  | n + 1 => prefixSum f n + f (n + 1)

private theorem modeq_of_shape {e a b : ℤ} (hshape : e = a - b)
    (h : e ≡ 0 [ZMOD 2013265921]) : a ≡ b [ZMOD 2013265921] := by
  subst hshape
  have hd := Int.modEq_iff_dvd.mp h
  have he : (0 : ℤ) - (a - b) = b - a := by ring
  rw [he] at hd
  exact Int.modEq_iff_dvd.mpr hd

/-! ## §5 — extraction: read the per-row facts out of a `Satisfied2` witness. -/

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace}

/-- The vb pad cell vanishes (mod p) on EVERY row: the per-row gate off the last row (gates
ride the `when_transition()` domain), the last-row re-lowering on it. -/
private theorem pad_zero (hsat : Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    rowAt t i cVBP0 ≡ 0 [ZMOD 2013265921] := by
  by_cases hl : i + 1 = t.rows.length
  · have h := hsat.rowConstraints i hi (.base (.boundary .last (ev cVBP0)))
      (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
        conservationConstraints, claimPins])
    have hbt : (i + 1 == t.rows.length) = true := by simpa using hl
    simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h
    simpa only [ev, EmittedExpr.eval, rowAt] using h hbt
  · have h := hsat.rowConstraints i hi (.base (.gate (ev cVBP0)))
      (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
        conservationConstraints, claimPins])
    have hlf : (i + 1 == t.rows.length) = false := by simpa using hl
    simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, hlf, envAt] at h
    simpa only [ev, EmittedExpr.eval, rowAt] using h

/-- The final accumulator vanishes (mod p) — the last-row conservation boundary. -/
private theorem acc_final (hsat : Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    accAt t (t.rows.length - 1) ≡ 0 [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  have hlt : t.rows.length - 1 < t.rows.length := by omega
  have h := hsat.rowConstraints (t.rows.length - 1) hlt (.base (.boundary .last (ev cACC)))
    (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
      conservationConstraints, claimPins])
  have hlastb : ((t.rows.length - 1) + 1 == t.rows.length) = true := by
    have hx : t.rows.length - 1 + 1 = t.rows.length := by omega
    simpa using hx
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h
  simpa only [ev, EmittedExpr.eval, accAt, rowAt] using h hlastb

/-- **The accumulator IS the running sum (mod p)** — seed + window step, by induction. -/
theorem acc_folds (hsat : Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t) :
    ∀ j, j < t.rows.length → accAt t j ≡ prefixSum (netAt t) j [ZMOD 2013265921] := by
  intro j
  induction j with
  | zero =>
      intro hj
      have h := hsat.rowConstraints 0 hj (.base (.boundary .first seedBody))
        (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
          conservationConstraints, claimPins])
      simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h
      have h0 := h rfl
      simp only [seedBody, esub, eadd, emul, eneg, ev, ek, EmittedExpr.eval] at h0
      simp only [prefixSum, netAt, valAt, outAt, accAt, rowAt]
      exact modeq_of_shape (by ring) h0
  | succ n ih =>
      intro hj
      have hn : n < t.rows.length := by omega
      have hnl : n + 1 ≠ t.rows.length := by omega
      have h := hsat.rowConstraints n hn (.windowGate accStep)
        (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
          conservationConstraints, claimPins])
      have hlf : (n + 1 == t.rows.length) = false := by simpa using hnl
      have honT : accStep.onTransition = true := rfl
      have hbody : accStep.body = accWindow := rfl
      simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.WindowConstraint.holdsAt, honT, if_true] at h
      have h1 := h hlf
      simp only [hbody, accWindow, wsub, Dregg2.Circuit.DescriptorIR2.WindowExpr.eval,
        envAt] at h1
      have hstep : accAt t (n + 1) ≡ accAt t n + netAt t (n + 1) [ZMOD 2013265921] := by
        simp only [accAt, netAt, valAt, outAt, rowAt]
        exact modeq_of_shape (by ring) h1
      have hplus := Int.ModEq.add_right (netAt t (n + 1)) (ih hn)
      simpa only [prefixSum] using hstep.trans hplus

end Extract

/-! ## §6 — `value_link_bound`: the published binding is chip-bound to the leaf's cells. -/

/-- **⚑ KEYSTONE 1 (`value_link_bound`).** Under a SOUND chip table (`ChipTableSound` — the
chip AIR's own per-permutation faithfulness), a satisfying trace forces, on EVERY row: the
`value_binding` cell is the genuine `hash_fact` of the value/asset/randomness cells, AND the
`leaf_commit` cell is the genuine `hash_fact` of those SAME value/asset(/owner)/randomness
cells — the chip-bound ℤ-link that makes decoupling the published binding from the leaf value
impossible — AND the pad cell ≡ 0; plus the row-0 digests are PI-pinned (field-faithful,
ZMOD 2013265921). The value that conserves (§7) is provably the value bound into the leaf. -/
theorem value_link_bound (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    (∀ i, i < t.rows.length →
        rowAt t i cVB
          = hash [rowAt t i cVAL, rowAt t i cASSET, rowAt t i cRAND, rowAt t i cVBP0,
              0, NS_FACT_MARK, 1]
        ∧ rowAt t i cLEAF
          = hash [rowAt t i cVAL, rowAt t i cASSET, rowAt t i cOWNER, rowAt t i cRAND,
              0, NS_FACT_MARK, 1]
        ∧ (rowAt t i cVBP0 ≡ 0 [ZMOD 2013265921]))
    ∧ (rowAt t 0 cVB ≡ t.pub piVB [ZMOD 2013265921])
    ∧ (rowAt t 0 cLEAF ≡ t.pub piLEAF [ZMOD 2013265921]) := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hkV := hsat.rowConstraints i hi lkValueBinding
      (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
        conservationConstraints, claimPins])
    have hkL := hsat.rowConstraints i hi lkLeafCommit
      (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
        conservationConstraints, claimPins])
    simp only [lkValueBinding, lkLeafCommit,
      Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] at hkV hkL
    rw [hwire] at hkV hkL
    have hlenV : (factIns [cVAL, cASSET, cRAND, cVBP0]).length ≤ CHIP_RATE := by decide
    have hlenL : (factIns [cVAL, cASSET, cOWNER, cRAND]).length ≤ CHIP_RATE := by decide
    have eV := chip_lookup_narrow_sound_of_wide_table hash (t.tf TableId.poseidon2) hChip
      ((envAt t i).loc) _ cVB hlenV hkV
    have eL := chip_lookup_narrow_sound_of_wide_table hash (t.tf TableId.poseidon2) hChip
      ((envAt t i).loc) _ cLEAF hlenL hkL
    rw [factIns_eval_4] at eV eL
    exact ⟨eV, eL, pad_zero hsat hi⟩
  · have h0 := hsat.rowConstraints 0 hpos (.base (.piBinding .first cVB piVB))
      (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
        conservationConstraints, claimPins])
    simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h0
    exact h0 rfl
  · have h0 := hsat.rowConstraints 0 hpos (.base (.piBinding .first cLEAF piLEAF))
      (by simp [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
        conservationConstraints, claimPins])
    simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h0
    exact h0 rfl

/-- **THE DECOUPLING TOOTH.** A trace whose PUBLISHED `value_binding` PI is not (mod p) the
genuine `hash_fact` of the leaf's value/asset/randomness cells admits NO satisfying
assignment — the deployed seam (a wire `value_binding` floating free of the STARK-witnessed
leaf value) is unrepresentable against this descriptor. -/
theorem value_decoupled_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2))
    (hforge : ¬ (t.pub piVB
      ≡ hash [rowAt t 0 cVAL, rowAt t 0 cASSET, rowAt t 0 cRAND, rowAt t 0 cVBP0,
          0, NS_FACT_MARK, 1] [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t := by
  intro hsat
  obtain ⟨hrows, hpin, _⟩ := value_link_bound hash minit mfin maddrs t hne hsat hChip hwire
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  have h0 := (hrows 0 hpos).1
  have hp := hpin.symm
  rw [h0] at hp
  exact hforge hp

/-! ## §7 — `conservation_holds`: the in-AIR Σ-fold + the mint tooth. -/

/-- **⚑ KEYSTONE 2 (`conservation_holds`).** A satisfying trace's in-AIR values CONSERVE:
`Σᵢ value[i] ≡ Σⱼ out_val[j] [ZMOD 2013265921]` over the SAME cells the value-link hashes
bind (§6) — there is no free second value to decouple and mint. Field conservation; the
ℤ-integer lift is the named `VALUE_BITS` range residual (header). -/
theorem conservation_holds (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t) :
    prefixSum (valAt t) (t.rows.length - 1)
      ≡ prefixSum (outAt t) (t.rows.length - 1) [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  have hsplit : ∀ n : Nat,
      prefixSum (netAt t) n = prefixSum (valAt t) n - prefixSum (outAt t) n := by
    intro n
    induction n with
    | zero => simp only [prefixSum, netAt]
    | succ m ih => simp only [prefixSum, ih, netAt]; ring
  have hfold := acc_folds hsat (t.rows.length - 1) (by omega)
  have hz : prefixSum (netAt t) (t.rows.length - 1) ≡ 0 [ZMOD 2013265921] :=
    hfold.symm.trans (acc_final hsat hne)
  rw [hsplit] at hz
  exact modeq_of_shape rfl hz

/-- **THE MINT TOOTH.** An unbalanced trace — `Σ value ≢ Σ out_val (mod p)`, a mint attempt —
admits NO satisfying assignment. -/
theorem mint_unbalanced_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hforge : ¬ (prefixSum (valAt t) (t.rows.length - 1)
      ≡ prefixSum (outAt t) (t.rows.length - 1) [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t :=
  fun hsat => hforge (conservation_holds hash minit mfin maddrs t hne hsat)

/-! ## §8 — non-vacuity: an explicit HONEST BALANCED witness, and both teeth exercised. -/

/-- The abstract-hash carrier for the concrete witnesses (zero suffices; the chip table below
carries genuine `chipRow hzero` rows). -/
def hzero : List ℤ → ℤ := fun _ => 0

/-- Honest row 0: value 5 (asset 2, owner 9, randomness 3), out_val 4, acc = 5 − 4 = 1. -/
def honRow0 : Assignment := fun j =>
  if j = 0 then 5 else if j = 1 then 2 else if j = 2 then 9 else if j = 3 then 3
  else if j = 7 then 4 else if j = 8 then 1 else 0

/-- Honest row 1: value 3 (asset 2, owner 8, randomness 6), out_val 4, acc = 1 + 3 − 4 = 0. -/
def honRow1 : Assignment := fun j =>
  if j = 0 then 3 else if j = 1 then 2 else if j = 2 then 8 else if j = 3 then 6
  else if j = 7 then 4 else 0

/-- Row 0's genuine leaf chip row: `arity 7 :: padded [5,2,9,3,0,MARK,1] :: 0 :: 7 lanes`. -/
def chipL0 : List ℤ :=
  [7, 5, 2, 9, 3, 0, 64207, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Row 0's genuine value-binding chip row (same value/asset/randomness cells). -/
def chipV0 : List ℤ :=
  [7, 5, 2, 3, 0, 0, 64207, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Row 1's genuine leaf chip row. -/
def chipL1 : List ℤ :=
  [7, 3, 2, 8, 6, 0, 64207, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Row 1's genuine value-binding chip row. -/
def chipV1 : List ℤ :=
  [7, 3, 2, 6, 0, 0, 64207, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The witness trace family: the chip table carries exactly the four genuine rows. -/
def honChipTbl : List (List ℤ) := [chipL0, chipV0, chipL1, chipV1]

def honTf : TraceFamily := fun tid =>
  match tid with
  | .poseidon2 => honChipTbl
  | .custom 3  => Dregg2.Circuit.ChipNarrowLookup.narrowTable honChipTbl
  | _ => []

/-- The honest family wires the NARROW bus to the 18-prefix of its wide chip table — ONE physical
chip serving both buses, exactly the deployed Rust `narrow_hist` serving (definitional). -/
theorem honTf_narrow_wire :
    honTf poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (honTf TableId.poseidon2) := rfl

/-- The honest balanced 2-row witness: 5 + 3 in ≡ 4 + 4 out. -/
def honestTrace : VmTrace := { rows := [honRow0, honRow1], pub := zeroAsg, tf := honTf }

-- The witness really is balanced; the mint below really is not.
#guard decide (prefixSum (valAt honestTrace) 1 = 8 ∧ prefixSum (outAt honestTrace) 1 = 8)

/-- The witness chip table is SOUND: every row is a genuine `chipRow hzero` tuple. -/
theorem honTf_sound : ChipTableSound hzero (honTf TableId.poseidon2) := by
  intro r hr
  simp only [honTf, honChipTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨[5, 2, 9, 3, 0, 64207, 1], [0, 0, 0, 0, 0, 0, 0], by decide, by decide, by decide⟩
  · exact ⟨[5, 2, 3, 0, 0, 64207, 1], [0, 0, 0, 0, 0, 0, 0], by decide, by decide, by decide⟩
  · exact ⟨[3, 2, 8, 6, 0, 64207, 1], [0, 0, 0, 0, 0, 0, 0], by decide, by decide, by decide⟩
  · exact ⟨[3, 2, 6, 0, 0, 64207, 1], [0, 0, 0, 0, 0, 0, 0], by decide, by decide, by decide⟩

/-- **The descriptor is SATISFIABLE by an honest balanced clearing** — an explicit witness, so
the UNSAT teeth are not vacuously true of an empty relation. -/
theorem honest_balanced_satisfies :
    Satisfied2 hzero shieldedValueLinkDesc (fun _ => 0) (fun _ => (0, 0)) [] honestTrace := by
  have hmemlog : memLog shieldedValueLinkDesc honestTrace = [] := rfl
  have hmaplog : mapLog shieldedValueLinkDesc honestTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    have hi2 : i = 0 ∨ i = 1 := by
      have hx : i < 2 := hi
      omega
    simp only [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
      conservationConstraints, claimPins, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hi2 with rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [lkLeafCommit, lkValueBinding, accStep, accWindow, wsub, seedBody,
        esub, eadd, emul, eneg, ev, ek,
        Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt,
        Dregg2.Circuit.DescriptorIR2.WindowConstraint.holdsAt,
        Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm,
        Dregg2.Circuit.DescriptorIR2.WindowExpr.eval,
        envAt, honestTrace, honTf, EmittedExpr.eval,
        List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      decide
  · -- rowHashes: no v1 hash sites
    intro i _
    exact trivial
  · -- rowRanges: no ranges
    intro i _ r hr
    simp [shieldedValueLinkDesc] at hr
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

/-- A concrete MINT attempt: same honest inputs (5 + 3 = 8 in) but 4 + 5 = 9 out. -/
def mintRow1 : Assignment := fun j =>
  if j = 0 then 3 else if j = 1 then 2 else if j = 2 then 8 else if j = 3 then 6
  else if j = 7 then 5 else 0

def mintTrace : VmTrace := { rows := [honRow0, mintRow1], pub := zeroAsg, tf := honTf }

#guard decide (prefixSum (valAt mintTrace) 1 = 8 ∧ prefixSum (outAt mintTrace) 1 = 9)

/-- **The mint tooth BITES a concrete forged instance** (8 in, 9 out ⇒ refused). -/
theorem mint_refused :
    ¬ Satisfied2 hzero shieldedValueLinkDesc (fun _ => 0) (fun _ => (0, 0)) [] mintTrace :=
  mint_unbalanced_unsat hzero (fun _ => 0) (fun _ => (0, 0)) [] mintTrace
    (by simp [mintTrace]) (by decide)

/-- A concrete DECOUPLING attempt: the honest rows, but the published `value_binding` PI is 1
while the genuine chip digest of the leaf's cells is `hzero … = 0`. -/
def decoupledPub : Assignment := fun k => if k = piVB then 1 else 0

def decoupledTrace : VmTrace := { rows := [honRow0, honRow1], pub := decoupledPub, tf := honTf }

/-- **The decoupling tooth BITES a concrete forged instance** (published binding ≠ the leaf's
genuine digest ⇒ refused). -/
theorem decoupled_refused :
    ¬ Satisfied2 hzero shieldedValueLinkDesc (fun _ => 0) (fun _ => (0, 0)) [] decoupledTrace :=
  value_decoupled_unsat hzero (fun _ => 0) (fun _ => (0, 0)) [] decoupledTrace
    (by simp [decoupledTrace]) honTf_sound (by rfl) (by decide)

/-! ## §9 — the byte-pinned wire golden (generated once via `#eval repr (emitVmJson2 …)`;
the Rust decoder ingests THIS string at the coordinated integrator step). -/

/-- Exact emitted-wire golden (generated via `#eval repr (emitVmJson2 shieldedValueLinkDesc)`).
Rust includes these bytes verbatim at the coordinated integrator step. -/
def SHIELDED_VALUE_LINK_CONSERVE_GOLDEN : String :=
  "{\"name\":\"dregg-shielded-value-link-conserve::v1\",\"ir\":2,\"trace_width\":9,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":4}},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":5}]},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":6}]},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"var\",\"v\":4}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":7}}}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"var\",\"v\":8}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":1}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 shieldedValueLinkDesc == SHIELDED_VALUE_LINK_CONSERVE_GOLDEN

/-! ## §10 — axiom hygiene on the keystones. -/

#assert_axioms honTf_narrow_wire
#assert_axioms value_link_bound
#assert_axioms value_decoupled_unsat
#assert_axioms conservation_holds
#assert_axioms mint_unbalanced_unsat
#assert_axioms acc_folds
#assert_axioms honest_balanced_satisfies
#assert_axioms mint_refused
#assert_axioms decoupled_refused

end Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor
