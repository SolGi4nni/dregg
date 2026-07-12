/-
# Dregg2.Circuit.RotatedKernelRefinementCapOpenAvail — the CAP-OPEN transfer availability weld
(the GAP #4 wrap class closed on the cap-authorized transfer route: eff + TB twin).

## What this module is

The bare-transfer + burn wrap forgeries are closed on the cohort keys (`AvailWireMembers`,
`RotatedKernelRefinement{Avail,MintBurnAvail}`). The LIVE cap-open transfer members —
`transferCapOpenEffV3` (registry key `transferCapOpenEffVmDescriptor2R24`) and its turn-bound twin
(`transferCapOpenTBVmDescriptor2R24`, `effCapOpenV3TB`) — are the SAME debit shape (`gBalLo` debits
`BALANCE_LO` by `param.AMOUNT` mod `p`) over the SAME bare v1 transfer face, so they carry the SAME
underflow-wrap mint-from-nothing (`docs/FINDING-modp-wrap-forgery-audit.md` forgery 1) with a
cap-open authority facet on top. The authority facet is ORTHOGONAL to availability: the appendix
(`capOpenConstraintsEff`) reads no balance column and adds no value gate, so a cap-authorized
over-debit passes the bare-based cap-open members exactly as it passed the bare cohort member.

This module swaps the BASE: the cap-open appendix (and the TB turn-identity weld) are re-hosted on
the HARDENED rotated transfer `transferV3Avail = v3OfFrozenWide transferVmDescriptorAvail` (the
§11.7 borrow-weld face — 15-bit limb decomposition of `before`/`after`/`amount`, `dir`-gated borrow
chain + NO-FINAL-BORROW, `(1−dir)`-gated credit carry chain + NO-FINAL-CARRY, 6 × 15-bit ranges).
Everything is width-parametric already (`effCapOpenV3`/`effCapOpenV3TB` append at
`base.traceWidth`), so the two hardened members are ONE instantiation each:

  * **`transferCapOpenEffV3Avail`** — `withSelectorGate TRANSFER (effCapOpenV3 transferV3Avail …)`,
    the hardened `transferCapOpenEffVmDescriptor2R24` wire member;
  * **`transferCapOpenEffV3TBAvail`** — `effCapOpenV3TB transferV3Avail …`, the hardened
    `transferCapOpenTBVmDescriptor2R24` wire member (turn-identity pins at PI 46/47/48 as before).

## What is proven (both members)

  * **AVAILABILITY FORCED** (`capOpenAvail_availability_and_exact_move_forced` / the TB twin): a
    `Satisfied2` witness of the hardened cap-open member strips — through the selector-gate / TB /
    appendix peels, all of which only APPEND constraints and no mem/map op — to a `Satisfied2` of
    `transferV3Avail`, on which `RotatedKernelRefinementAvail.availability_and_exact_move_forced`
    forces `tr.amt ≤ pre.bal tr.src a` AND the exact ℤ debit. The cap-open availability residual is
    GONE — same discharge object as the cohort flip, no re-proof of the borrow chain.
  * **THE TOOTH** (`…_rejects_overdebit`): any over-debit decode riding a satisfying hardened
    cap-open witness is UNSAT (the audit's mint-from-nothing class, on the cap-authorized route).
  * **AUTHORITY INTACT** (`transferCapOpenEffV3Avail_authorizes` / `…TBAvail_authorizes` + the
    wrong-facet / mismatched-src teeth): the generic keystones (`effCapOpenV3_authorizes`,
    `effCapOpenV3TB_authorizes`, `effCapOpenV3_rejects_bit_clear`,
    `effCapOpenV3TB_rejects_mismatched_src`) are base-parametric; instantiating them at
    `transferV3Avail` re-establishes the exact live-keystone statements on the hardened members.
    The appendix constraints are VERBATIM (`capOpenConstraintsEff base.traceWidth EFF_TRANSFER`,
    just at the avail-shifted width), so nothing about non-amplification / the facet gates changes.

## The availability residual on the facet refinement route

`RotatedKernelRefinementFacet` / `…FacetTurnBound` carry NO `guardAvail`: their VALUE leg is reused
verbatim from the transfer value rung (`transfer_descriptorRefines`), whose availability residual is
the one `RotatedKernelRefinementAvail` already discharges. The cap-open route's availability close
is therefore exactly these hardened members + the emission retarget — there is no separate facet
`guardAvail` to discharge.

## Deployment (mirrors the cohort flip; NO VK regen here)

`EmitRotationV3.lean` overrides `transferCapOpenEffVmDescriptor2R24` and emits the TB key from the
hardened members, so the ACK-gated `scripts/emit-descriptors.sh` regen mints the hardened bytes.
The committed registry/VK stay bare until the ember-gated regen. The Rust producer is
descriptor-name-driven (`avail_pad_for_descriptor_name` — the `dregg-effectvm-transfer-v1-avail`
prefix routes the generic transfer weld fill), so pre-regen the fleet keeps proving byte-identically.
Named follow-ups (HORIZONLOG class, same as transfer/burn): the in-library `v3RegistryCapOpen`
tail + apex `Rfix` re-key over these members, and the 8-felt WIDE twins of the avail cap-open
members (`EmitWideRegistryProbe` hosts stay bare-based until their own flip; the SDK wide route
stays self-consistent — a resolved wide descriptor's name derives pad 0 — but the wrap window
stays open on the wide leg until then).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports are
read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementAvail
import Dregg2.Circuit.Emit.CapOpenTurnPins

namespace Dregg2.Circuit.RotatedKernelRefinementCapOpenAvail

open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt ChipTableSoundN)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (withSelectorGate withSelectorGate_satisfied2)
open Dregg2.Circuit.Emit.CapOpenEmit
  (CAP_OPEN_SPAN capOpenCols CapOpenRowCanon effCapOpenV3 effCapOpenV3_authorizes
   effCapOpenV3_rejects_bit_clear effCapOpenV3_satisfied2_strips_to_base
   capOpen_satisfied2_strips_to_base EFF_TRANSFER)
open Dregg2.Circuit.Emit.CapOpenTurnPins
  (effCapOpenV3TB effCapOpenV3TB_to_base effCapOpenV3TB_authorizes
   effCapOpenV3TB_rejects_mismatched_src TurnIdentityAnchored)
open Dregg2.Circuit.RotatedKernelRefinementAvail
  (transferV3Avail RotTableSideW rotatedEncodesAvail availability_and_exact_move_forced)
open Dregg2.Circuit.DeployedCapOpen (leafOf groupVal capPermOut MASK_BITS)
open Dregg2.Circuit.DeployedCapTree (CapLeaf Cap8Scheme)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (DeployedFaithfulEff8)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (tierOfTag)
open Dregg2.Authority (Label)
open Dregg2.Exec.FacetAuthority
  (AuthProvided FacetCaps authorizedFacetB authorizedFacetEffB authorizedFacetB_eq_eff)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — the two HARDENED cap-open transfer members (the avail-based re-hosts). -/

/-- The hardened cap-open member names carry the `dregg-effectvm-transfer-v1-avail` prefix — the
name the Rust producer's `avail_pad_for_descriptor_name` routes the generic transfer weld fill by
(the pad is a property of the descriptor, not the effect). -/
def availEffName : String := "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff"
def availTBName : String := "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff-tb"

/-- **`transferCapOpenEffV3Avail`** — the HARDENED live transfer cap-open: the availability-weld
rotated base `transferV3Avail` + the effect-GENERAL appendix at `EFF_TRANSFER` (genuine submask
facet + decoded tier, verbatim) + the deployed selector tooth. The
`transferCapOpenEffVmDescriptor2R24` registry key's post-flip bytes. -/
def transferCapOpenEffV3Avail : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
    (effCapOpenV3 transferV3Avail availEffName EFF_TRANSFER)

/-- **`transferCapOpenEffV3TBAvail`** — the HARDENED turn-bound twin: the availability-weld rotated
base + the cap-open appendix + the #225 turn-identity weld (two columns, three first-row PI pins at
`piCount + 0/1/2 = 46/47/48`, exactly the bare TB shape). The
`transferCapOpenTBVmDescriptor2R24` key's post-flip bytes. -/
def transferCapOpenEffV3TBAvail : EffectVmDescriptor2 :=
  effCapOpenV3TB transferV3Avail availTBName EFF_TRANSFER

/-! ## §2 — THE PEELS: a hardened cap-open witness is a fortiori a `transferV3Avail` witness.

The selector gate, the cap-open appendix, and the TB pins only APPEND `.base`/`.lookup` constraints
and surface no mem/map op — the existing generic strips compose. The stripped object is EXACTLY the
descriptor `RotatedKernelRefinementAvail` states its availability discharge over. -/

/-- `Satisfied2 (transferCapOpenEffV3Avail) ⟹ Satisfied2 transferV3Avail` (selector peel +
appendix peel). -/
theorem transferCapOpenEffV3Avail_strips (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash transferCapOpenEffV3Avail minit mfin maddrs t) :
    Satisfied2 hash transferV3Avail minit mfin maddrs t :=
  capOpen_satisfied2_strips_to_base hash Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
    transferV3Avail availEffName EFF_TRANSFER minit mfin maddrs t hsat

/-- `Satisfied2 (transferCapOpenEffV3TBAvail) ⟹ Satisfied2 transferV3Avail` (TB peel +
appendix peel). -/
theorem transferCapOpenEffV3TBAvail_strips (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash transferCapOpenEffV3TBAvail minit mfin maddrs t) :
    Satisfied2 hash transferV3Avail minit mfin maddrs t :=
  effCapOpenV3_satisfied2_strips_to_base hash transferV3Avail availTBName EFF_TRANSFER
    minit mfin maddrs t
    (effCapOpenV3TB_to_base transferV3Avail availTBName EFF_TRANSFER hash minit mfin maddrs t hsat)

/-! ## §3 — AVAILABILITY FORCED on the cap-authorized route (the discharge + the teeth). -/

/-- **`capOpenAvail_availability_and_exact_move_forced` — the cap-open transfer wrap forgery
CLOSED.** A `Satisfied2` witness of the HARDENED live cap-open member + the hardened decode FORCE
`tr.amt ≤ pre.bal tr.src a` (availability) AND the exact ℤ debit — the same discharge as the cohort
flip, reached through the cap-open peel. The cap-open authority facet contributes nothing here and
loses nothing (§4). -/
theorem capOpenAvail_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferCapOpenEffV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt :=
  availability_and_exact_move_forced hash hside
    (transferCapOpenEffV3Avail_strips hash hsat) pre post tr a henc

/-- The TB twin's availability + exact-move discharge. -/
theorem capOpenTBAvail_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferCapOpenEffV3TBAvail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt :=
  availability_and_exact_move_forced hash hside
    (transferCapOpenEffV3TBAvail_strips hash hsat) pre post tr a henc

/-- **THE TOOTH (eff).** Any over-debit decode (`pre.bal src a < tr.amt` — the audit's
mint-from-nothing class) riding a satisfying hardened cap-open witness is UNSAT: a cap-AUTHORIZED
transfer still cannot move more than the source holds. -/
theorem capOpenAvail_rejects_overdebit (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferCapOpenEffV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (capOpenAvail_availability_and_exact_move_forced hash hside hsat pre post tr a henc).1
  omega

/-- **THE TOOTH (TB twin).** -/
theorem capOpenTBAvail_rejects_overdebit (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferCapOpenEffV3TBAvail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (capOpenTBAvail_availability_and_exact_move_forced hash hside hsat pre post tr a henc).1
  omega

/-! ## §4 — AUTHORITY INTACT: the live keystones re-established on the hardened members.

The generic keystones are stated over an ARBITRARY base (`effCapOpenV3 base name n` /
`effCapOpenV3TB base name n`); the hardened members are those shapes at `base = transferV3Avail`,
so each live-keystone statement is one instantiation — no facet gate, mask-recon gate, or
non-amplification argument is touched. -/

open Dregg2.Circuit.DeployedCapOpen in
/-- **`transferCapOpenEffV3Avail_authorizes`** — the LIVE transfer authority keystone on the
HARDENED member (the mirror of `transferCapOpenEffV3_authorizes`, base swapped): a `Satisfied2`
witness whose opened leaf IS the effect-faithful `(actor ⇒ src)` edge discharges the kernel's
`authorizedFacetB caps provided turn` and `leaf.target = src`, forced by the depth-16 open. -/
theorem transferCapOpenEffV3Avail_authorizes (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash transferCapOpenEffV3Avail minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : CapOpenRowCanon (capOpenCols transferV3Avail.traceWidth) (envAt t i) EFF_TRANSFER)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff8 S8 vkOfTag provided (1 <<< EFF_TRANSFER) caps
      (groupVal (envAt t i) (capOpenCols transferV3Avail.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (envAt t i).loc (capOpenCols transferV3Avail.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols transferV3Avail.traceWidth) (envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hsat := withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
    _ minit mfin maddrs t hsat
  have h := effCapOpenV3_authorizes transferV3Avail availEffName EFF_TRANSFER (by decide)
    S8 hash vkOfTag provided minit mfin maddrs t hChip hsat i hi hnotlast hcanon caps leafAt hfaith
    actor src dst amt hsrc hedge htier
  refine ⟨?_, h.2⟩
  rw [authorizedFacetB_eq_eff]
  exact h.1

/-- **`transferCapOpenEffV3Avail_rejects_wrong_facet`** — the wrong-facet tooth on the hardened
member: a leaf whose `EFF_TRANSFER` mask bit is CLEAR ⟹ UNSAT (the selected-bit submask gate
bites, verbatim at the avail-shifted columns). -/
theorem transferCapOpenEffV3Avail_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (envAt t i).loc ((capOpenCols transferV3Avail.traceWidth).bit EFF_TRANSFER) = 0) :
    ¬ Satisfied2 hash transferCapOpenEffV3Avail minit mfin maddrs t := fun hsat =>
  effCapOpenV3_rejects_bit_clear transferV3Avail availEffName EFF_TRANSFER hash
    minit mfin maddrs t i hi hnotlast hclear
    (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
      _ minit mfin maddrs t hsat)

open Dregg2.Circuit.DeployedCapOpen in
/-- **`transferCapOpenEffV3TBAvail_authorizes`** — the TB authority keystone on the hardened twin
(the mirror of the bare TB route): the turn-identity weld (`hsrc` DERIVED from the first-row PI
pin + the verifier anchor) and the depth-16 membership co-located on the first active row, with the
`authorizedFacetEffB` conclusion collapsed to the kernel's `authorizedFacetB`. -/
theorem transferCapOpenEffV3TBAvail_authorizes (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash transferCapOpenEffV3TBAvail minit mfin maddrs t)
    (hlen : 2 ≤ t.rows.length)
    (hcanon : CapOpenRowCanon (capOpenCols transferV3Avail.traceWidth) (envAt t 0) EFF_TRANSFER)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff8 S8 vkOfTag provided (1 <<< EFF_TRANSFER) caps
      (groupVal (envAt t 0) (capOpenCols transferV3Avail.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hanchor : TurnIdentityAnchored transferV3Avail availTBName EFF_TRANSFER t 0 src actor dst)
    (hsrcLt : (src : ℤ) < 2013265921)
    (hedge : leafOf (capOpenCols transferV3Avail.traceWidth) (envAt t 0) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have h := effCapOpenV3TB_authorizes transferV3Avail availTBName EFF_TRANSFER (by decide)
    S8 hash vkOfTag provided minit mfin maddrs t hChip hsat hlen hcanon caps leafAt hfaith
    actor src dst amt hanchor hsrcLt hedge htier
  refine ⟨?_, h.2⟩
  rw [authorizedFacetB_eq_eff]
  exact h.1

/-- **`transferCapOpenEffV3TBAvail_rejects_mismatched_src`** — the #225 turn-identity tooth on the
hardened twin: a first row whose cap-open `src` column ≠ the published `PI[46]` is UNSAT. -/
theorem transferCapOpenEffV3TBAvail_rejects_mismatched_src (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hfirst : (i == 0) = true)
    (hcellSrc : 0 ≤ (envAt t i).loc (capOpenCols transferV3Avail.traceWidth).src
      ∧ (envAt t i).loc (capOpenCols transferV3Avail.traceWidth).src < 2013265921)
    (hcellPub : 0 ≤ (envAt t i).pub (effCapOpenV3 transferV3Avail availTBName EFF_TRANSFER).piCount
      ∧ (envAt t i).pub (effCapOpenV3 transferV3Avail availTBName EFF_TRANSFER).piCount < 2013265921)
    (hbad : (envAt t i).loc (capOpenCols transferV3Avail.traceWidth).src
      ≠ (envAt t i).pub (effCapOpenV3 transferV3Avail availTBName EFF_TRANSFER).piCount) :
    ¬ Satisfied2 hash transferCapOpenEffV3TBAvail minit mfin maddrs t :=
  effCapOpenV3TB_rejects_mismatched_src transferV3Avail availTBName EFF_TRANSFER hash
    minit mfin maddrs t i hi hfirst hcellSrc hcellPub hbad

/-! ## §5 — geometry / non-vacuity witnesses (the emitted-bytes shape pins). -/

section Witnesses

-- The hardened rotated base is 10 wider than the bare (`transferV3.traceWidth = 1647`): the avail
-- witness pad shifts the cap-open appendix (and the TB columns) uniformly.
#guard transferV3Avail.traceWidth == 1657
#guard transferCapOpenEffV3Avail.traceWidth == transferV3Avail.traceWidth + CAP_OPEN_SPAN
#guard transferCapOpenEffV3Avail.traceWidth == 1986
#guard transferCapOpenEffV3TBAvail.traceWidth == transferV3Avail.traceWidth + CAP_OPEN_SPAN + 2
#guard transferCapOpenEffV3TBAvail.traceWidth == 1988
-- PI shape unchanged: 46 (42 v1 + 4 rotated commit pins); TB adds the 3 turn-identity pins.
#guard transferCapOpenEffV3Avail.piCount == 46
#guard transferCapOpenEffV3TBAvail.piCount == 49
-- Constraint deltas: the 78-gate appendix + the selector tooth (eff) / + the 3 TB pins (TB).
#guard transferCapOpenEffV3Avail.constraints.length == transferV3Avail.constraints.length + 79
#guard transferCapOpenEffV3TBAvail.constraints.length == transferV3Avail.constraints.length + 78 + 3
-- The wide graduation's 15-bit range table rides along (6 tables — the borrow-limb teeth land).
#guard transferCapOpenEffV3Avail.tables.length == 6
#guard transferCapOpenEffV3TBAvail.tables.length == 6
-- The name prefix the Rust producer routes the transfer avail pad by.
#guard transferCapOpenEffV3Avail.name == "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff"
#guard transferCapOpenEffV3TBAvail.name == "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff-tb"

end Witnesses

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms transferCapOpenEffV3Avail_strips
#assert_axioms transferCapOpenEffV3TBAvail_strips
#assert_axioms capOpenAvail_availability_and_exact_move_forced
#assert_axioms capOpenTBAvail_availability_and_exact_move_forced
#assert_axioms capOpenAvail_rejects_overdebit
#assert_axioms capOpenTBAvail_rejects_overdebit
#assert_axioms transferCapOpenEffV3Avail_authorizes
#assert_axioms transferCapOpenEffV3Avail_rejects_wrong_facet
#assert_axioms transferCapOpenEffV3TBAvail_authorizes
#assert_axioms transferCapOpenEffV3TBAvail_rejects_mismatched_src

end Dregg2.Circuit.RotatedKernelRefinementCapOpenAvail
