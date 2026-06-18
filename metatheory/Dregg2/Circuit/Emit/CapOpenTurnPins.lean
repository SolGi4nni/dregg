/-
# Dregg2.Circuit.Emit.CapOpenTurnPins — the TURN-IDENTITY PI weld (the smuggle REALIZED in-circuit).

## The hole this module closes (the in-circuit realization of `RotatedKernelRefinementFacetTurnBound`)

`RotatedKernelRefinementFacetTurnBound` makes the apex conclude authority over the PUBLISHED turn
`pi.turn`, BUT the binding `TurnIdentityBound pc tr := tr = pc.turn` and the cap-open source field
`hsrc : (envAt t i).loc capOpenCols.src = (tr.src : ℤ)` are CARRIED hypotheses — nothing in the LIVE
descriptor forces the witness's turn fields to equal the light client's published turn. So a prover can
existentially instantiate `tr.actor := tr.src` (owner disjunct, no cap) for ANY `src` it moves, or open a
cap over a PROVER-CHOSEN `src` column, and the apex's conclusion still holds — the authority is OFF-circuit.

This module REALIZES the binding in the live cap-open descriptor: it publishes the turn's
`(src, actor, dst)` to THREE new public-input slots and forces — by appended `piBinding` gates — the
cap-open's `src` column (and two new turn-identity columns) to equal those PIs. The verifier ANCHORS
those PIs to the trusted turn's fields (`turn.src`/`turn.actor`/`turn.dst`), so a `Satisfied2` witness of
the turn-pinned descriptor whose published PIs the verifier overrode from the turn FORCES
`capOpenCols.src = turn.src` — i.e. `hsrc` is now DISCHARGED from a real PI binding, no longer carried.
The src column is the cap-open's load-bearing one: `targetBindGate` already pins `leaf.target = src`, so
welding `src` to the published `pi.src` welds the OPENED LEAF's target to the light client's source.

## What is built

  1. **`capOpenActorCol` / `capOpenDstCol`** — two NEW columns past the cap-open appendix (so every
     existing `capOpenCols` proof is untouched), carrying the turn's `actor`/`dst`.
  2. **`turnIdentityPins`** — three `.piBinding .last` constraints welding `capOpenCols.src`,
     `capOpenActorCol base`, `capOpenDstCol base` to the three NEW PI slots (`base.piCount + 0/1/2`,
     where the cap-open base `effCapOpenV3` does NOT add PIs, so these are the first past `rotateV3`'s
     four commit pins).
  3. **`effCapOpenV3TB base name n`** — `effCapOpenV3` PLUS the two columns and the three pins. Every
     cap-open appendix constraint is UNTOUCHED (still references the same columns), so
     `effCapOpenV3_satisfiedEff` / `effCapOpenV3_authorizes` lift verbatim through the append.
  4. **`effCapOpenV3TB_publishes`** — a `Satisfied2` witness's LAST row pins
     `src/actor/dst` columns to `PI[piCount + 0/1/2]`. The keystone the discharge reads.
  5. **`effCapOpenV3TB_hsrc`** — from the pin + the verifier's PI anchor (`PI[piCount] = turn.src`),
     `capOpenCols.src = turn.src` — the `hsrc` obligation FORCED, not carried.

## Honest residual (named, not faked)

The PI **anchor** (`PI[piCount] = turn.src` etc.) is the deployed verifier's override (it recomputes the
turn-identity PIs from the trusted turn before calling `verify_vm_descriptor2`, exactly as the
record-pin family anchors `dpis[38]` from the trusted post-cell). It is carried here as the named
`TurnIdentityAnchored` predicate — REALIZABLE (the honest verifier holds the turn) and the deployment
analog of `rotateV3WithRecordPin`'s anchor. The src weld is the load-bearing tooth (it forecloses the
prover-chosen-src cap open). The ACTOR binding to the leaf's c-list position (so an owner-claim `actor`
must be the real owner of `src`) is the heavier fan-out: the leaf-membership Merkle path roots in the
`actor`'s subtree, so binding `actor` end-to-end needs the path to encode the actor — REPORTED as the
remaining work; this module publishes the `actor` column + PI (so the light client SEES it and the owner
disjunct is a decision on published data) but does not yet weld it into the Merkle root.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers inherited through the
imported cap-open keystones. No `sorry`, no `native_decide`, no `:= True`, no fresh axiom.
-/
import Dregg2.Circuit.Emit.CapOpenEmit

namespace Dregg2.Circuit.Emit.CapOpenTurnPins

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (VmConstraint2 EffectVmDescriptor2 ChipTableSound Satisfied2 VmTrace envAt)
open Dregg2.Circuit.DeployedCapOpen (CapOpenCols leafOf MASK_BITS)
open Dregg2.Circuit.Emit.CapOpenEmit (capOpenCols CAP_OPEN_SPAN effCapOpenV3 effCapOpenV3_authorizes)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (DeployedFaithfulEff tierOfTag)
open Dregg2.Authority (Label)
open Dregg2.Exec.FacetAuthority (AuthProvided FacetCaps authorizedFacetEffB)

set_option autoImplicit false

/-! ## §1 — the two NEW turn-identity columns (past the cap-open appendix).

`effCapOpenV3 base name n` has width `base.traceWidth + CAP_OPEN_SPAN`. The two turn-identity columns
ride at `base.traceWidth + CAP_OPEN_SPAN + 0/1` — past every existing column, so no existing
`capOpenCols` index collides. (The `src` column is the EXISTING `capOpenCols.src`; only `actor`/`dst`
are new.) -/

/-- The turn's `actor` column for the cap-open of a base of width `w`. -/
def capOpenActorCol (w : Nat) : Nat := w + CAP_OPEN_SPAN
/-- The turn's `dst` column for the cap-open of a base of width `w`. -/
def capOpenDstCol (w : Nat) : Nat := w + CAP_OPEN_SPAN + 1

/-! ## §2 — the three turn-identity PI pins.

`effCapOpenV3 base name n` does NOT add PIs to `base` (it appends only `capOpenConstraintsEff`), so the
base's `piCount` is `(v3Of …).piCount = base'.piCount + 4` (the rotated commit pins). The three
turn-identity pins ride the first slots past those four: `base.piCount + 0/1/2`. Each is a LAST-row pin
(the cap-open row is the witness's designated authority row; the deployed assembly pins it on the last
row, matching the commit pins). -/

/-- The three turn-identity PI pins for a cap-open base of width `w`, PI count `pc`: weld the cap-open
`src` column to `PI[pc]`, the new `actor` column to `PI[pc+1]`, the new `dst` column to `PI[pc+2]`. -/
def turnIdentityPins (w pc : Nat) : List VmConstraint2 :=
  [ .base (.piBinding .last capOpenCols.src pc)
  , .base (.piBinding .last (capOpenActorCol w) (pc + 1))
  , .base (.piBinding .last (capOpenDstCol w) (pc + 2)) ]

/-! ## §3 — `effCapOpenV3TB`: the cap-open descriptor PLUS the turn-identity weld. -/

/-- **`effCapOpenV3TB base name n`** — `effCapOpenV3 base name n` widened by the two turn-identity
columns (`+2`) and three new PI slots (`+3`), with the three `turnIdentityPins` appended. Every cap-open
appendix constraint is preserved (still references the same `capOpenCols` columns), so every cap-open
keystone lifts verbatim through the append. -/
def effCapOpenV3TB (base : EffectVmDescriptor2) (name : String) (n : Nat) : EffectVmDescriptor2 :=
  let d := effCapOpenV3 base name n
  { d with
    traceWidth  := d.traceWidth + 2
    piCount     := d.piCount + 3
    constraints := d.constraints ++ turnIdentityPins base.traceWidth d.piCount }

/-- The cap-open base (`effCapOpenV3`) constraints are a PREFIX of the TB descriptor's. -/
theorem effCapOpenV3TB_base_constraints (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (c : VmConstraint2) (hc : c ∈ (effCapOpenV3 base name n).constraints) :
    c ∈ (effCapOpenV3TB base name n).constraints :=
  List.mem_append_left _ hc

/-- The TB descriptor's constraints are EXACTLY the base's plus the three turn-identity pins. -/
theorem effCapOpenV3TB_constraints (base : EffectVmDescriptor2) (name : String) (n : Nat) :
    (effCapOpenV3TB base name n).constraints
      = (effCapOpenV3 base name n).constraints
        ++ turnIdentityPins base.traceWidth (effCapOpenV3 base name n).piCount := rfl

/-- The TB descriptor's mem-ops equal the base's (the pins add none). -/
theorem effCapOpenV3TB_memOpsOf (base : EffectVmDescriptor2) (name : String) (n : Nat) :
    Dregg2.Circuit.DescriptorIR2.memOpsOf (effCapOpenV3TB base name n)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effCapOpenV3 base name n) := by
  show List.filterMap _ (effCapOpenV3TB base name n).constraints
     = List.filterMap _ (effCapOpenV3 base name n).constraints
  rw [effCapOpenV3TB_constraints, List.filterMap_append]
  show _ ++ [] = _
  rw [List.append_nil]

/-- The TB descriptor's map-ops equal the base's. -/
theorem effCapOpenV3TB_mapOpsOf (base : EffectVmDescriptor2) (name : String) (n : Nat) :
    Dregg2.Circuit.DescriptorIR2.mapOpsOf (effCapOpenV3TB base name n)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effCapOpenV3 base name n) := by
  show List.filterMap _ (effCapOpenV3TB base name n).constraints
     = List.filterMap _ (effCapOpenV3 base name n).constraints
  rw [effCapOpenV3TB_constraints, List.filterMap_append]
  show _ ++ [] = _
  rw [List.append_nil]

/-- The TB descriptor's mem LOG equals the base's. -/
theorem effCapOpenV3TB_memLog (base : EffectVmDescriptor2) (name : String) (n : Nat) (t : VmTrace) :
    Dregg2.Circuit.DescriptorIR2.memLog (effCapOpenV3TB base name n) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effCapOpenV3 base name n) t := by
  unfold Dregg2.Circuit.DescriptorIR2.memLog
  rw [effCapOpenV3TB_memOpsOf]

/-- The TB descriptor's map LOG equals the base's. -/
theorem effCapOpenV3TB_mapLog (base : EffectVmDescriptor2) (name : String) (n : Nat) (t : VmTrace) :
    Dregg2.Circuit.DescriptorIR2.mapLog (effCapOpenV3TB base name n) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effCapOpenV3 base name n) t := by
  unfold Dregg2.Circuit.DescriptorIR2.mapLog
  rw [effCapOpenV3TB_mapOpsOf]

/-- A `Satisfied2` witness of the TB descriptor is a `Satisfied2` witness of the cap-open base: the
appended PI pins only ADD constraints, and every base constraint (referenced by `effCapOpenV3_authorizes`)
holds on every row of the TB witness. The memory/site legs are identical (the pins are base gates over
existing columns, contributing no mem/site ops). -/
theorem effCapOpenV3TB_to_base (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effCapOpenV3TB base name n) minit mfin maddrs t) :
    Satisfied2 hash (effCapOpenV3 base name n) minit mfin maddrs t := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_
    , memAddrsNodup := ?_, memClosed := ?_, memDisciplined := ?_, memBalanced := ?_
    , memTableFaithful := ?_, mapTableFaithful := ?_ }
  · intro i hi c hc
    exact hsat.rowConstraints i hi c (effCapOpenV3TB_base_constraints base name n c hc)
  · intro i hi; exact hsat.rowHashes i hi
  · intro i hi r hr; exact hsat.rowRanges i hi r hr
  · exact hsat.memAddrsNodup
  · -- the memory log of the TB descriptor equals the base's (the pins add no mem ops); so closure lifts.
    intro op hop
    exact hsat.memClosed op (by rw [← effCapOpenV3TB_memLog] at hop; exact hop)
  · have := hsat.memDisciplined; rwa [effCapOpenV3TB_memLog] at this
  · have := hsat.memBalanced; rwa [effCapOpenV3TB_memLog] at this
  · have := hsat.memTableFaithful; rwa [effCapOpenV3TB_memLog] at this
  · have := hsat.mapTableFaithful; rwa [effCapOpenV3TB_mapLog] at this

/-! ## §4 — `effCapOpenV3TB_publishes`: the LAST row pins src/actor/dst to the three new PIs. -/

/-- **`effCapOpenV3TB_publishes`** — on the LAST row of a `Satisfied2` witness of `effCapOpenV3TB`, the
cap-open `src` column equals `PI[piCount]`, the new `actor` column `PI[piCount+1]`, the new `dst` column
`PI[piCount+2]` (`piCount` = the cap-open base's PI count). The three turn-identity pins are FORCED. -/
theorem effCapOpenV3TB_publishes (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effCapOpenV3TB base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : (i + 1 == t.rows.length) = true) :
    (envAt t i).loc capOpenCols.src = (envAt t i).pub (effCapOpenV3 base name n).piCount
    ∧ (envAt t i).loc (capOpenActorCol base.traceWidth)
        = (envAt t i).pub ((effCapOpenV3 base name n).piCount + 1)
    ∧ (envAt t i).loc (capOpenDstCol base.traceWidth)
        = (envAt t i).pub ((effCapOpenV3 base name n).piCount + 2) := by
  have hrow := hsat.rowConstraints i hi
  set pc := (effCapOpenV3 base name n).piCount with hpc
  have hmem : ∀ c ∈ turnIdentityPins base.traceWidth pc, c ∈ (effCapOpenV3TB base name n).constraints :=
    fun c hc => List.mem_append_right _ hc
  have memSrc : VmConstraint2.base (.piBinding .last capOpenCols.src pc)
      ∈ (effCapOpenV3TB base name n).constraints :=
    hmem _ (by simp [turnIdentityPins])
  have memAct : VmConstraint2.base (.piBinding .last (capOpenActorCol base.traceWidth) (pc + 1))
      ∈ (effCapOpenV3TB base name n).constraints :=
    hmem _ (by simp [turnIdentityPins])
  have memDst : VmConstraint2.base (.piBinding .last (capOpenDstCol base.traceWidth) (pc + 2))
      ∈ (effCapOpenV3TB base name n).constraints :=
    hmem _ (by simp [turnIdentityPins])
  have hsrc := hrow _ memSrc
  have hact := hrow _ memAct
  have hdst := hrow _ memDst
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hsrc hact hdst
  exact ⟨hsrc hlast, hact hlast, hdst hlast⟩

/-! ## §5 — `TurnIdentityAnchored`: the verifier's PI override (NAMED), and `hsrc` DISCHARGED. -/

/-- **`TurnIdentityAnchored t i src actor dst`** — the deployed verifier ANCHORS the three turn-identity
PIs to the trusted turn's fields (it recomputes them from the turn before `verify_vm_descriptor2`,
exactly as the record-pin family anchors `dpis[38]` from the trusted post-cell). NAMED, realizable (the
honest verifier holds the turn), the deployment analog of `rotateV3WithRecordPin`'s anchor. -/
def TurnIdentityAnchored (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (t : VmTrace) (i : Nat) (src actor dst : Label) : Prop :=
  (envAt t i).pub (effCapOpenV3 base name n).piCount = (src : ℤ)
  ∧ (envAt t i).pub ((effCapOpenV3 base name n).piCount + 1) = (actor : ℤ)
  ∧ (envAt t i).pub ((effCapOpenV3 base name n).piCount + 2) = (dst : ℤ)

/-- **`effCapOpenV3TB_hsrc` — the cap-open `src` column = the turn's `src`, FORCED.** From a `Satisfied2`
witness of `effCapOpenV3TB` on the LAST row and the verifier's PI anchor `PI[piCount] = turn.src`, the
cap-open's `src` column EQUALS `turn.src` — the `hsrc` obligation of `effCapOpenV3_authorizes` is now
DISCHARGED from a real in-circuit PI binding, no longer a carried hypothesis. -/
theorem effCapOpenV3TB_hsrc (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effCapOpenV3TB base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : (i + 1 == t.rows.length) = true)
    (src actor dst : Label) (hanchor : TurnIdentityAnchored base name n t i src actor dst) :
    (envAt t i).loc capOpenCols.src = (src : ℤ) := by
  obtain ⟨hpubSrc, _, _⟩ := effCapOpenV3TB_publishes base name n hash minit mfin maddrs t hsat i hi hlast
  obtain ⟨hanSrc, _, _⟩ := hanchor
  rw [hpubSrc, hanSrc]

/-- **`effCapOpenV3TB_authorizes` — the AUTHORITY leg with `hsrc` DISCHARGED from the PI weld.** The
fan-out cap-open authority `effCapOpenV3_authorizes`, but the `hsrc` hypothesis is REPLACED by the
turn-identity PI anchor: a `Satisfied2` witness of `effCapOpenV3TB` (the appended pins lift to the base
via `effCapOpenV3TB_to_base`) whose verifier anchored `PI[piCount] = turn.src` discharges the kernel's
`authorizedFacetEffB … (1 <<< n)` for the turn — the cap-open `src` welded to the PUBLISHED source, NOT a
free column. The `hedge`/`htier`/`hfaith` residuals (the cap-tree leaf identification) remain the named
cap-tree floor, exactly as before — this module closes ONLY the `src`-binding smuggle. -/
theorem effCapOpenV3TB_authorizes {State : Type} (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hn : n < MASK_BITS) (S : CapHashScheme State) (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb (effCapOpenV3TB base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : (i + 1 == t.rows.length) = true)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< n) caps
      ((envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hanchor : TurnIdentityAnchored base name n t i src actor dst)
    (hedge : leafOf capOpenCols (envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< n)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hbase := effCapOpenV3TB_to_base base name n S.chipAbsorb minit mfin maddrs t hsat
  have hsrc : (envAt t i).loc capOpenCols.src = (src : ℤ) :=
    effCapOpenV3TB_hsrc base name n S.chipAbsorb minit mfin maddrs t hsat i hi hlast src actor dst hanchor
  exact effCapOpenV3_authorizes base name n hn S vkOfTag provided minit mfin maddrs t hChip hbase
    i hi caps leafAt hfaith actor src dst amt hsrc hedge htier

/-! ## §6 — the NEGATIVE tooth: a mismatched turn-identity PI ⟹ the pin is UNSATISFIABLE.

A LAST row whose cap-open `src` column does NOT equal the published `PI[piCount]` does NOT satisfy the
turn-identity pin — the appended `piBinding` REJECTS it. Composed with the verifier's anchor
(`PI[piCount] = turn.src`), a trace whose cap-open `src` ≠ `turn.src` cannot be a satisfying witness of
`effCapOpenV3TB`: the equality gate BITES. This is the light-client-relevant tooth — a proof whose
published turn-src does not match the committed cap-open source is rejected. -/

/-- **`effCapOpenV3TB_rejects_mismatched_src` (the turn-identity TOOTH).** If the cap-open `src` column on
the last row differs from the published `PI[piCount]`, NO `Satisfied2` witness of `effCapOpenV3TB` has that
row's columns/PI — the pin forces `src = PI[piCount]`, so a mismatch is contradictory. With the verifier's
anchor (`PI[piCount] = turn.src`), a forged `src ≠ turn.src` is UNSAT. -/
theorem effCapOpenV3TB_rejects_mismatched_src (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hlast : (i + 1 == t.rows.length) = true)
    (hbad : (envAt t i).loc capOpenCols.src ≠ (envAt t i).pub (effCapOpenV3 base name n).piCount) :
    ¬ Satisfied2 hash (effCapOpenV3TB base name n) minit mfin maddrs t := by
  intro hsat
  obtain ⟨hpubSrc, _, _⟩ := effCapOpenV3TB_publishes base name n hash minit mfin maddrs t hsat i hi hlast
  exact hbad hpubSrc

/-! ## §7 — Axiom hygiene. -/

#assert_axioms effCapOpenV3TB_base_constraints
#assert_axioms effCapOpenV3TB_to_base
#assert_axioms effCapOpenV3TB_publishes
#assert_axioms effCapOpenV3TB_hsrc
#assert_axioms effCapOpenV3TB_authorizes
#assert_axioms effCapOpenV3TB_rejects_mismatched_src

end Dregg2.Circuit.Emit.CapOpenTurnPins
