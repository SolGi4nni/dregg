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

  1. **`turnIdentityPins`** — ONE `.piBinding .first` constraint welding `capOpenCols.src` to the NEW
     PI slot `base.piCount` (the cap-open base `effCapOpenV3` does NOT add PIs, so this is the first
     slot past `rotateV3`'s four commit pins).
  2. **`effCapOpenV3TB base name n`** — `effCapOpenV3` PLUS that one pin. Every cap-open appendix
     constraint is UNTOUCHED (still references the same columns), so
     `effCapOpenV3_satisfiedEff` / `effCapOpenV3_authorizes` lift verbatim through the append.
  3. **`effCapOpenV3TB_publishes`** — a `Satisfied2` witness's FIRST row pins the `src` column to
     `PI[piCount]`. The keystone the discharge reads.
  4. **`effCapOpenV3TB_hsrc`** — from the pin + the verifier's PI anchor (`PI[piCount] = turn.src`),
     `capOpenCols.src = turn.src` — the `hsrc` obligation FORCED, not carried.

## ⚑ WHAT WAS REMOVED, 2026-07-30, and why (the `actor`/`dst` publication)

This module used to carry TWO MORE columns (`capOpenActorCol` / `capOpenDstCol`) and TWO MORE pins,
publishing the turn's `actor` and `dst` at `PI[piCount+1]` / `PI[piCount+2]`. **They bound nothing.**
The two columns were introduced by this module and read by NO other constraint, so a
`.piBinding` on them is `local[c] == pi[k]` with the prover choosing both sides — measured by
`UnforcedPiPins.unforcedPins`, which flagged exactly those two on
`transferCapOpenTBVmDescriptor2R24` (emitted columns 928/929 → PI 47/48), and proved a no-op by
`UnforcedPiPins.unforced_pin_row_admits_any_value`. Nothing downstream lost a discharge: the
actor/dst legs of `TurnIdentityAnchored` were destructured and DISCARDED at every use
(`effCapOpenV3TB_hsrc` reads only `PI[piCount]`), and the facet claim's `actor`/`dst` were always
carried through `hedge`, never forced by a pin.

A weld that publishes a PROVER-CHOSEN felt for *who acted* and *who received* is worse than no weld,
because its name says otherwise: a light client, which has no executor to overwrite the slot from a
trusted turn, would read `PI[actor]` as attested. It never was. The `src` weld — the load-bearing
one, since `targetBindGate` already pins `leaf.target = src` — stays and is FORCED.

The real actor binding (an owner-claim `actor` must be the genuine holder of the opened c-list slot)
needs the cap-tree Merkle path to encode the actor; that is the authorization-in-AIR lane's work,
and it will publish `actor` when it can also force it.

## The row-domain match (the turn-identity weld pins on the FIRST row)

Under the deployed `when_transition()` denotation (`VmConstraint.holdsVm`), the cap-open MEMBERSHIP
binding gates (`rootPinGate`/`targetBindGate`/`effBitGateFor`/the facet gates) are `.base (.gate …)` —
FORCED only on NON-last rows. A `.piBinding .last` weld fires on the LAST row, a DISJOINT domain, so it
could never constrain the membership row, and on a single-effect trace whose cap-open row IS the last row
the membership would be vacuous (the prior `.last` choice was UNSOUND there). `turnIdentityPins`
therefore rides the FIRST row (`when_first_row()` — the deployed mechanism the rotation's BEFORE-commit
pin already uses, `EffectVmEmitRotationV3.rotPins`'s `.piBinding .first`). On the first row of any real
(≥2-row) cap-open trace, `isFirst = true` (the weld fires) AND `isLast = false` (the membership gates
bite): ONE active row carries both, so `capOpenCols.src` is welded to the published source EXACTLY where
the depth-16 open reads it — no cross-row residual. The `≥2-row` fact (`hlen : 2 ≤ rows.length`) is the
genuine shape of a real cap-open trace (a depth-16 open plus its wrap/pad row); it gives `0 + 1 ≠
rows.length`, the `hiNotLast` the membership keystone needs on the first row.

## The one carried hypothesis (named, not faked)

The PI **anchor** (`PI[piCount] = turn.src`) is the deployed verifier's override (it recomputes the
turn-identity PI from the trusted turn before calling `verify_vm_descriptor2`, exactly as the
record-pin family anchors `dpis[38]` from the trusted post-cell). It is carried here as the named
`TurnIdentityAnchored` predicate — REALIZABLE (the honest verifier holds the turn) and the deployment
analog of `rotateV3WithRecordPin`'s anchor. Unlike the removed actor/dst pins, this one BITES without
the anchor too: `capOpenCols.src` is read by `targetBindGate` and the depth-16 membership open, so
the pin relates the published slot to a column the AIR forces.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers inherited through the
imported cap-open keystones.
-/
import Dregg2.Circuit.Emit.CapOpenEmit

namespace Dregg2.Circuit.Emit.CapOpenTurnPins

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (VmConstraint2 EffectVmDescriptor2 ChipTableSound ChipTableSoundN Satisfied2 VmTrace envAt)
open Dregg2.Circuit.DeployedCapOpen (CapOpenCols leafOf MASK_BITS capPermOut groupVal)
open Dregg2.Circuit.Emit.CapOpenEmit
  (capOpenCols CAP_OPEN_SPAN effCapOpenV3 effCapOpenV3_authorizes CapOpenRowCanon)
open Dregg2.Circuit.Emit.EffectVmEmitRotation (canon_eq_of_modEq)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme Cap8Scheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (DeployedFaithfulEff tierOfTag)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (DeployedFaithfulEff8)
open Dregg2.Authority (Label)
open Dregg2.Exec.FacetAuthority (AuthProvided FacetCaps authorizedFacetEffB)

set_option autoImplicit false

/-! ## §1 — no new columns.

The weld adds NO column: it pins the EXISTING `capOpenCols.src`, which the depth-16 membership open
and `targetBindGate` already read. (The two columns this module used to add for `actor`/`dst` were
read by nothing else and are GONE — see the header.) -/

/-! ## §2 — the turn-identity PI pin.

`effCapOpenV3 base name n` does NOT add PIs to `base` (it appends only `capOpenConstraintsEff`), so the
base's `piCount` is `(v3Of …).piCount = base'.piCount + 4` (the rotated commit pins). The
turn-identity pin rides the first slot past those four: `base.piCount`. It is a FIRST-row pin
(`when_first_row()`, the deployed mechanism the rotation's BEFORE-commit pin already uses —
`EffectVmEmitRotationV3.rotPins`'s `.piBinding .first`).

THE ROW-DOMAIN MATCH (why `.first`, not `.last`): the cap-open MEMBERSHIP binding gates
(`rootPinGate`/`targetBindGate`/`effBitGateFor`/the facet gates) ride `.base (.gate …)` — under the
deployed `when_transition()` denotation (`VmConstraint.holdsVm`) they are FORCED only on NON-last rows.
A `.piBinding .last` weld would fire on the LAST row, a DISJOINT domain — so the turn-identity binding
and the membership it must constrain could never share a row, and on a single-effect trace whose cap-open
row IS the last row the membership would be vacuous (the prior `.last` choice was UNSOUND there). Pinning
on the FIRST row co-locates the weld with the membership: on the first row of any real (≥2-row) cap-open
trace, `isFirst = true` (the pin fires) AND `isLast = false` (the membership gates bite). One active row
carries both — `capOpenCols.src` welded to the published source EXACTLY where it is opened. -/

/-- The turn-identity PI pin for a cap-open base of width `w`, PI count `pc`: weld the cap-open
`src` column to `PI[pc]`. It rides the FIRST row (`when_first_row()`) — the same active row the
membership binding gates are forced on, so the published-src weld and the depth-16 open constrain
ONE row. (The `actor`/`dst` pins that used to sit beside it named columns nothing else read; see the
header for the measurement that removed them.) -/
def turnIdentityPins (w pc : Nat) : List VmConstraint2 :=
  [ .base (.piBinding .first (capOpenCols w).src pc) ]

/-! ## §3 — `effCapOpenV3TB`: the cap-open descriptor PLUS the turn-identity weld. -/

/-- **`effCapOpenV3TB base name n`** — `effCapOpenV3 base name n` with ONE new PI slot (`+1`) and the
`turnIdentityPins` weld appended. NO new column (the pinned `src` column already exists). Every
cap-open appendix constraint is preserved (still references the same `capOpenCols` columns), so every
cap-open keystone lifts verbatim through the append. -/
def effCapOpenV3TB (base : EffectVmDescriptor2) (name : String) (n : Nat) : EffectVmDescriptor2 :=
  let d := effCapOpenV3 base name n
  { d with
    piCount     := d.piCount + 1
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

/-! ## §4 — `effCapOpenV3TB_publishes`: the FIRST row pins `src` to the new PI. -/

/-- **`effCapOpenV3TB_publishes`** — on the FIRST row of a `Satisfied2` witness of `effCapOpenV3TB`, the
cap-open `src` column is pinned to `PI[piCount]` (`piCount` = the cap-open base's PI count) —
`≡ [ZMOD p]`, the field-faithful pin the deployed AIR forces (the ℤ equality follows under cell
canonicality, at the consumer). The turn-identity `.piBinding .first` pin is FORCED — on the SAME
active row the membership binding gates bite (in any ≥2-row trace). -/
theorem effCapOpenV3TB_publishes (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effCapOpenV3TB base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hfirst : (i == 0) = true) :
    (envAt t i).loc (capOpenCols base.traceWidth).src
        ≡ (envAt t i).pub (effCapOpenV3 base name n).piCount [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi
  set pc := (effCapOpenV3 base name n).piCount with hpc
  have hmem : ∀ c ∈ turnIdentityPins base.traceWidth pc, c ∈ (effCapOpenV3TB base name n).constraints :=
    fun c hc => List.mem_append_right _ hc
  have memSrc : VmConstraint2.base (.piBinding .first (capOpenCols base.traceWidth).src pc)
      ∈ (effCapOpenV3TB base name n).constraints :=
    hmem _ (by simp [turnIdentityPins])
  have hsrc := hrow _ memSrc
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hsrc
  exact hsrc hfirst

/-! ## §5 — `TurnIdentityAnchored`: the verifier's PI override (NAMED), and `hsrc` DISCHARGED. -/

/-- **`TurnIdentityAnchored t i src`** — the deployed verifier ANCHORS the turn-identity PI to the
trusted turn's `src` (it recomputes it from the turn before `verify_vm_descriptor2`, exactly as the
record-pin family anchors `dpis[38]` from the trusted post-cell). NAMED, realizable (the honest
verifier holds the turn), the deployment analog of `rotateV3WithRecordPin`'s anchor.

⚑ It used to carry two more conjuncts, for `actor` and `dst`. Every consumer destructured them and
DISCARDED them — nothing was ever derived from an anchored `actor` or `dst`, because the columns they
anchored were read by no gate. They are gone with the pins. -/
def TurnIdentityAnchored (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (t : VmTrace) (i : Nat) (src : Label) : Prop :=
  (envAt t i).pub (effCapOpenV3 base name n).piCount = (src : ℤ)

/-- **`effCapOpenV3TB_hsrc` — the cap-open `src` column = the turn's `src`, FORCED.** From a `Satisfied2`
witness of `effCapOpenV3TB` on the FIRST row and the verifier's PI anchor `PI[piCount] = turn.src`, the
cap-open's `src` column EQUALS `turn.src` — the `hsrc` obligation of `effCapOpenV3_authorizes` is now
DISCHARGED from a real in-circuit PI binding on the SAME active row the membership opens, no longer a
carried hypothesis. -/
theorem effCapOpenV3TB_hsrc (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effCapOpenV3TB base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hfirst : (i == 0) = true)
    (src : Label) (hanchor : TurnIdentityAnchored base name n t i src)
    -- the src cell is field-canonical + the turn's src label is a canonical field element: lifts the
    -- mod-`p` pin congruence to the ℤ equality the membership keystone consumes.
    (hcellSrc : 0 ≤ (envAt t i).loc (capOpenCols base.traceWidth).src
      ∧ (envAt t i).loc (capOpenCols base.traceWidth).src < 2013265921)
    (hsrcLt : (src : ℤ) < 2013265921) :
    (envAt t i).loc (capOpenCols base.traceWidth).src = (src : ℤ) := by
  have hpubSrc := effCapOpenV3TB_publishes base name n hash minit mfin maddrs t hsat i hi hfirst
  exact canon_eq_of_modEq hcellSrc ⟨Int.natCast_nonneg _, hsrcLt⟩ (by rw [← hanchor]; exact hpubSrc)

/-- **`effCapOpenV3TB_authorizes` — the AUTHORITY leg, the turn-identity weld and the cap-open membership
co-located on the FIRST (active) row.**

Under the deployed `when_transition()` denotation (`VmConstraint.holdsVm`) the cap-open MEMBERSHIP
binding gates (`rootPinGate`/`targetBindGate`/`effBitGateFor`/the facet gates) ride `.base (.gate …)` —
FORCED only on NON-last rows — while the turn-identity weld `turnIdentityPins` rides `.piBinding .first`
— FORCED on the FIRST row. On the first row of any real ≥2-row cap-open trace these COINCIDE: `isFirst =
true` (the weld fires, anchoring `capOpenCols.src = src`) AND `isLast = false` (the membership gates
bite). So a SINGLE active row carries both — the published-src binding and the depth-16 open constrain
the same `src` column. No cross-row residual: the `≥2-row` fact `hlen` gives the `hiNotLast` the
membership keystone needs on row `0`. The `hedge`/`htier`/`hfaith` cap-tree-leaf residuals remain. -/
theorem effCapOpenV3TB_authorizes (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hn : n < MASK_BITS) (S8 : Cap8Scheme) (hash : List ℤ → ℤ) (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapOpenV3TB base name n) minit mfin maddrs t)
    -- the FIRST row carries BOTH the membership gates (non-last) AND the turn-identity pin (first);
    -- `hlen` is the genuine ≥2-row shape of a real cap-open trace (depth-16 open + its wrap row).
    (hlen : 2 ≤ t.rows.length)
    -- the field-faithful canonicality envelope on the first row (cells canonical + effect-bit range +
    -- ℤ-exact mask recomposition) — what lifts the mod-`p` gates to the ℤ-level `SatisfiedEff`.
    (hcanon : CapOpenRowCanon (capOpenCols base.traceWidth) (envAt t 0) n)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff8 S8 vkOfTag provided (1 <<< n) caps
      (groupVal (envAt t 0) (capOpenCols base.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hanchor : TurnIdentityAnchored base name n t 0 src)
    -- the turn's src label is a canonical field element (the deployed label range).
    (hsrcLt : (src : ℤ) < 2013265921)
    (hedge : leafOf (capOpenCols base.traceWidth) (envAt t 0) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< n)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hbase := effCapOpenV3TB_to_base base name n hash minit mfin maddrs t hsat
  have hi : 0 < t.rows.length := by omega
  have hiNotLast : (0 : Nat) + 1 ≠ t.rows.length := by omega
  -- the published-src binding on the FIRST row (the `.piBinding .first` weld + the anchor) — the SAME
  -- active row the membership opens, so no cross-row transport is needed.
  have hsrc : (envAt t 0).loc (capOpenCols base.traceWidth).src = (src : ℤ) :=
    effCapOpenV3TB_hsrc base name n hash minit mfin maddrs t hsat 0 hi rfl src hanchor
      (hcanon.cells _) hsrcLt
  -- the membership on the FIRST (active) row FORCES authority for the PUBLISHED `src`.
  exact effCapOpenV3_authorizes base name n hn S8 hash vkOfTag provided minit mfin maddrs t hChip hbase
    0 hi hiNotLast hcanon caps leafAt hfaith actor src dst amt hsrc hedge htier

/-! ## §6 — the NEGATIVE tooth: a mismatched turn-identity PI ⟹ the pin is UNSATISFIABLE.

A FIRST row whose cap-open `src` column does NOT equal the published `PI[piCount]` does NOT satisfy the
turn-identity pin — the appended `.piBinding .first` REJECTS it. Composed with the verifier's anchor
(`PI[piCount] = turn.src`), a trace whose cap-open `src` ≠ `turn.src` cannot be a satisfying witness of
`effCapOpenV3TB`: the equality gate BITES. This is the light-client-relevant tooth — a proof whose
published turn-src does not match the committed cap-open source is rejected. -/

/-- **`effCapOpenV3TB_rejects_mismatched_src` (the turn-identity TOOTH).** If the cap-open `src` column on
the first row differs from the published `PI[piCount]` — both CANONICAL field values (`0 ≤ · < p`, the
deployed range invariant; the mod-`p` pin cannot see a wrap between canonical representatives) — NO
`Satisfied2` witness of `effCapOpenV3TB` has that row's columns/PI: the pin forces `src ≡ PI[piCount]`,
which collapses to equality in `(−p, p)`, contradicting the mismatch. With the verifier's anchor
(`PI[piCount] = turn.src`), a forged `src ≠ turn.src` is UNSAT. -/
theorem effCapOpenV3TB_rejects_mismatched_src (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hfirst : (i == 0) = true)
    (hcellSrc : 0 ≤ (envAt t i).loc (capOpenCols base.traceWidth).src
      ∧ (envAt t i).loc (capOpenCols base.traceWidth).src < 2013265921)
    (hcellPub : 0 ≤ (envAt t i).pub (effCapOpenV3 base name n).piCount
      ∧ (envAt t i).pub (effCapOpenV3 base name n).piCount < 2013265921)
    (hbad : (envAt t i).loc (capOpenCols base.traceWidth).src ≠ (envAt t i).pub (effCapOpenV3 base name n).piCount) :
    ¬ Satisfied2 hash (effCapOpenV3TB base name n) minit mfin maddrs t := by
  intro hsat
  have hpubSrc := effCapOpenV3TB_publishes base name n hash minit mfin maddrs t hsat i hi hfirst
  exact hbad (canon_eq_of_modEq hcellSrc hcellPub hpubSrc)

/-! ## §7 — Axiom hygiene. -/

#assert_axioms effCapOpenV3TB_base_constraints
#assert_axioms effCapOpenV3TB_to_base
#assert_axioms effCapOpenV3TB_publishes
#assert_axioms effCapOpenV3TB_hsrc
#assert_axioms effCapOpenV3TB_authorizes
#assert_axioms effCapOpenV3TB_rejects_mismatched_src

end Dregg2.Circuit.Emit.CapOpenTurnPins
