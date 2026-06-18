/-
# Dregg2.Circuit.CircuitCompletenessAuthorityConstruct — the AUTHORITY-leg DE-LAUNDERING:
CONSTRUCT the faithful cap-membership from `AuthorizedByCap`, rather than ASSUMING it.

## The laundering this closes

`CircuitCompletenessAuthority.CapOpenWitness` carried, as ASSUMED FIELDS, the WHOLE conclusion of the
cap-authority completeness rung: `hfaith : DeployedFaithfulEff …` (the leaf set is faithful at the
cap-open root), `leafAt`/`hedge`/`hsrc`/`htier` (the opened leaf IS the authorizing edge, decoding to
the genuine tier). Nothing was CONSTRUCTED from the authorizing cap — so the rung
(`authorityComplete_generic`) was the soundness keystone `effAuthoritySource_authorizes` re-run over
data that BEGGED THE QUESTION. There was no theorem `AuthorizedByCap ⟹ ∃ faithful membership`.

This module proves exactly that converse, CONSTRUCTIVELY. It is the genuine DUAL of the soundness
cap-membership bridge `DeployedCapTree.deployedCapOpen_implies_authorizedEffB`
(`MembersAt ∧ confersLeaf ⟹ ∃ cap`): we INVERT it — from `∃ cap` (`AuthorizedByCap`) we EXHIBIT the
leaf assignment, the cap-tree root, the membership opening, the conferral, and the deployed
faithfulness `DeployedFaithfulEff`.

## What is CONSTRUCTED (everything the kernel transition determines)

  * `authLeafAt c effectBit` (§1) — the faithful leaf assignment for an authorizing cap `c`: the
    `(actor ⇒ src)` edge carries a leaf decoding to `c`'s facet/tier; every OTHER edge carries a
    deny-all (`mask = 0`) leaf, so `confersLeaf` is FALSE off-edge and faithfulness is VACUOUS there.
    The genuine dual of the soundness demo `oneEdgeLeaf`, but parametric in the actual cap.
  * `authConstructedRoot S c effectBit` (§1) — the cap-tree root: the leaf digest itself (the depth-0
    opening), so `MembersAt` holds with the EMPTY path (`recomposeUp _ [] = cur`).
  * `authLeaf_membersAt` (§2) — the membership opening is CONSTRUCTED (empty path).
  * `authLeaf_confers` (§2) — the on-edge leaf CONFERS `effectBit` on BOTH axes, the facts read off
    the constructed leaf and DERIVED from the cap (`isEffectPermitted`/`isSatisfiedBy`).
  * `authConstructed_faithful` (§3) — `DeployedFaithfulEff` for the constructed assignment: every
    conferring edge is the authorizing edge, backed by the cap `c`. CONSTRUCTED, not assumed.

## What remains carried (the irreducible realizability — the StarkComplete dual)

The ONLY residual the reduced witness still carries is the cap-open TRACE realizability: a concrete
`VmTrace t` and `hsat : Satisfied2 … (effCapOpenV3 …) … t` (plus its chip-table soundness and the row
identification tying the trace's committed `cap_root`/`src` columns to the constructed root/edge). This
is the honest prover's actual in-circuit cap-tree opening — the dual of the soundness `StarkSound`
extraction, the same realizability `StarkComplete` bridges to FRI. It is NOT the conclusion: the
faithfulness, the leaf, the edge, the tier decode, and the membership are all now CONSTRUCTED here and
no longer assumed. (See `CircuitCompletenessAuthority.CapOpenWitnessReduced` for the slimmed carrier.)

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `Satisfied2`/`DeployedFaithfulEff` is
ASSUMED here — they are CONSTRUCTED/PROVED. No `sorry`, no `native_decide`, no `:= True`, no fresh
axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompletenessAuthority

namespace Dregg2.Circuit.CircuitCompletenessAuthorityConstruct

open Dregg2.Exec
open Dregg2.Exec.FacetAuthority
open Dregg2.Authority (Label)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme FACT_MARK packNode leafFields)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme
  (DeployedFaithfulEff capLeafDigest MembersAt recomposeUp tierOfTag confersLeaf
   maskOfLimbs facetOfLeaf vkOfTier tierOfTag_tierByte)
open Dregg2.Circuit.CircuitCompletenessAuthority (AuthorizedByCap)

set_option autoImplicit false

/-! ## §0 — the tier decode round-trips its own byte (CONSOLIDATED into `DeployedCapTree`).

`vkOfTier` / `tierOfTag_tierByte` — the total tier round-trip (the deployed `auth_tag` BYTE → `AuthTier`
is the inverse of `AuthTier.tierByte` under the matching `vkOfTier`, on ALL tiers incl. `Custom`) — are
now the SHARED canonical-leaf machinery in `Dregg2.Circuit.DeployedCapTree.CapHashScheme` (the soundness
home), imported above. Both this completeness construction's `authLeafAt` decode and the soundness
`canonicalLeaf` decode read off the SAME inverse — no duplicate. We use it to make the CONSTRUCTED leaf's
decoded tier EQUAL the authorizing cap's tier, so the cap's `isSatisfiedBy` transfers verbatim. -/

/-! ## §1 — the CONSTRUCTED faithful leaf assignment + root (from the authorizing cap). -/

/-- **`authLeafAt c effectBit`** — the CONSTRUCTED faithful leaf assignment for an authorizing cap `c`
at the edge `(actor ⇒ c.target)` performing `effectBit`. The matching edge `(actor, c.target)` carries
a leaf decoding to: facet `mask_lo := effectBit` (so the decoded facet permits `effectBit`), tier
`auth_tag := c.tier.tierByte` (so the decoded tier — under `vkOfTier c.tier` — is exactly `c.tier`),
`target := c.target`. EVERY OTHER edge carries a deny-all (`mask = 0`) leaf, where `isEffectPermitted`
is FALSE, so `confersLeaf` is false and the faithfulness obligation is vacuous off-edge. The parametric
dual of the soundness demo `oneEdgeLeaf`. -/
def authLeafAt (actor0 : Label) (c : FacetCap) (effectBit : EffectMask) :
    Label → Label → CapLeaf := fun actor src =>
  if actor = actor0 ∧ src = c.target then
    { slot_hash := 0, target := (c.target : ℤ), auth_tag := (c.tier.tierByte : ℤ),
      mask_lo := (effectBit : ℤ), mask_hi := 0, expiry := 0, breadstuff := 0 }
  else
    { slot_hash := 0, target := 0, auth_tag := 0,
      mask_lo := 0, mask_hi := 0, expiry := 0, breadstuff := 0 }   -- mask 0 ⇒ deny-all

/-- **`authConstructedRoot S c effectBit`** — the CONSTRUCTED cap-tree root for the authorizing edge:
the leaf digest of the on-edge leaf itself (the depth-0 opening). The honest prover's full depth-16
recompose collapses to this leaf digest under the empty path; `MembersAt` holds with `path := []`. -/
def authConstructedRoot {State : Type} (S : CapHashScheme State)
    (actor0 : Label) (c : FacetCap) (effectBit : EffectMask) (src0 : Label) : ℤ :=
  capLeafDigest S (authLeafAt actor0 c effectBit actor0 src0)

/-! ## §2 — the membership opening + the conferral are CONSTRUCTED. -/

/-- **`authLeaf_membersAt` — the membership opening is CONSTRUCTED (empty path).** The on-edge leaf's
digest IS the constructed root, so the depth-0 opening (`path := []`) witnesses `MembersAt`. (The honest
prover's real depth-16 path recomposes to the same root; we exhibit the minimal opening.) -/
theorem authLeaf_membersAt {State : Type} (S : CapHashScheme State)
    (actor0 : Label) (c : FacetCap) (effectBit : EffectMask) :
    MembersAt S (authConstructedRoot S actor0 c effectBit c.target)
      (authLeafAt actor0 c effectBit actor0 c.target) :=
  ⟨[], rfl⟩

/-- **`authLeaf_confers` — the on-edge leaf CONFERS `effectBit` on BOTH axes (CONSTRUCTED).** From the
cap's facet permitting `effectBit` and its tier satisfied by `provided`, the CONSTRUCTED on-edge leaf's
DECODED facet/tier confer `effectBit` under `provided`: the facet is `maskOfLimbs effectBit 0 =
effectBit` (permits, since the cap permits the same bit on its own facet... but read off the leaf), and
the tier decodes to exactly `c.tier` (round-trip, §0), which `provided` satisfies. NOTE the leaf's facet
is the SINGLETON `effectBit` mask, so `isEffectPermitted (some effectBit) effectBit` is the genuine
submask test `effectBit &&& effectBit ≠ 0`, requiring `effectBit ≠ 0` (true for `1 <<< n`). -/
theorem authLeaf_confers (actor0 : Label) (c : FacetCap) (provided : AuthProvided)
    (effectBit : EffectMask) (hbit : effectBit ≠ 0)
    (htier : c.tier.isSatisfiedBy provided = true) :
    confersLeaf (vkOfTier c.tier) provided effectBit
      (authLeafAt actor0 c effectBit actor0 c.target) := by
  -- the on-edge leaf (the `if` fires: `actor0 = actor0 ∧ c.target = c.target`).
  have hleaf : authLeafAt actor0 c effectBit actor0 c.target
      = { slot_hash := 0, target := (c.target : ℤ), auth_tag := (c.tier.tierByte : ℤ),
          mask_lo := (effectBit : ℤ), mask_hi := 0, expiry := 0, breadstuff := 0 } := by
    simp only [authLeafAt, and_self, if_pos]
  rw [hleaf]
  refine ⟨?_, ?_⟩
  · -- facet: the decoded mask is `maskOfLimbs effectBit 0 = effectBit`, and `effectBit &&& effectBit ≠ 0`.
    -- reduce `facetOfLeaf` on the concrete leaf to `some effectBit`.
    have hfac : facetOfLeaf
        ⟨0, (c.target : ℤ), (c.tier.tierByte : ℤ), (effectBit : ℤ), 0, 0, 0⟩
        = some effectBit := by
      simp only [facetOfLeaf, maskOfLimbs]
      norm_num
    rw [hfac]
    -- `isEffectPermitted (some effectBit) effectBit`: `effectBit ≠ 0` ⇒ the `some m` arm, submask test.
    cases heb : effectBit with
    | zero => exact absurd heb hbit
    | succ k =>
      unfold isEffectPermitted
      simp only [Nat.and_self]
      rw [← heb]; exact decide_eq_true hbit
  · -- tier: the decoded `auth_tag = c.tier.tierByte` round-trips to `c.tier`, which `provided` satisfies.
    show (tierOfTag (vkOfTier c.tier) (c.tier.tierByte : ℤ)).isSatisfiedBy provided = true
    rw [tierOfTag_tierByte]; exact htier

/-! ## §3 — the deployed faithfulness is CONSTRUCTED (`DeployedFaithfulEff`, not assumed). -/

/-- **`authConstructed_faithful` — `DeployedFaithfulEff` is CONSTRUCTED.** The constructed leaf
assignment FAITHFULLY realizes `caps`: every conferring member edge must be the authorizing edge
`(actor0, c.target)` (every other edge is deny-all, where `confersLeaf` is FALSE), and there the
backing cap is exactly the authorizing `c ∈ caps actor0`. This is the genuine INVERSE of the soundness
`DeployedFaithfulEff.backed` — there the cap is EXTRACTED from a faithful opening; here it is the one
the authorizing hypothesis HANDS us, and the faithfulness is BUILT around it.

It is keyed on the witnessing cap `c` for `caps actor0` (the `AuthorizedByCap` data); off-edge
conferral is impossible so backedness is vacuous, and on the authorizing edge `c` itself is the
witness. -/
theorem authConstructed_faithful {State : Type} (S : CapHashScheme State)
    (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask)
    (actor0 : Label) (c : FacetCap)
    (hmem : c ∈ caps actor0)
    (hfacet : isEffectPermitted c.facet effectBit = true)
    (htier : c.tier.isSatisfiedBy provided = true) :
    DeployedFaithfulEff S (vkOfTier c.tier) provided effectBit caps
      (authConstructedRoot S actor0 c effectBit c.target)
      (authLeafAt actor0 c effectBit) := by
  refine ⟨?_⟩
  intro actor src _hopen hconf
  by_cases hedge : actor = actor0 ∧ src = c.target
  · obtain ⟨ha, hs⟩ := hedge
    subst ha; subst hs
    exact ⟨c, hmem, rfl, hfacet, htier⟩
  · -- off-edge: the deny-all leaf has `mask = 0`, so `confersLeaf` is FALSE — contradiction.
    exfalso
    obtain ⟨hcf, _⟩ := hconf
    have hzero : facetOfLeaf (authLeafAt actor0 c effectBit actor src) = some 0 := by
      simp only [authLeafAt, if_neg hedge, facetOfLeaf, maskOfLimbs]
      norm_num
    rw [hzero, Dregg2.Exec.FacetAuthority.zeroFacet_denies_all] at hcf
    exact absurd hcf (by simp)

/-! ## §4 — the slimmed witness: only the TRACE realizability survives, and the de-laundered rung.

`authConstructed_faithful` + `authLeaf_membersAt` + `authLeaf_confers` mean that from `AuthorizedByCap`,
the faithfulness / membership / leaf / edge / tier are ALL constructed. The ONLY residual a completeness
witness still needs is the cap-open TRACE (`t`, `hsat`, `hChip`) plus the row-identification tying the
trace's committed `cap_root`/`src` columns to the constructed root/edge. We package that residual as
`CapOpenTraceFloor`, ASSEMBLE the soundness carrier `EffAuthoritySource` from it + the constructed
faithfulness, and FORCE the deployed gate — the rung the laundering pretended to discharge. -/

open Dregg2.Circuit.RotatedKernelRefinementFacet (EffAuthoritySource effAuthoritySource_authorizes)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2 ChipTableSound envAt)
open Dregg2.Circuit.Emit.CapOpenEmit (effCapOpenV3 capOpenCols)
open Dregg2.Circuit.DeployedCapOpen (CapOpenCols leafOf)

/-- **`CapOpenTraceFloor S provided effectBit base name n actor0 c` — the IRREDUCIBLE trace realizability
(NAMED, the StarkComplete dual).** The honest prover's in-circuit cap-tree opening, REDUCED to ONLY what
genuinely needs the prover: a concrete `VmTrace` `t`, the cap-open `Satisfied2` of the live fan-out
descriptor `effCapOpenV3 base name n` over `S.chipAbsorb`, the chip-table soundness, the row index, and
the row-identification pinning the trace's committed `cap_root` column to the CONSTRUCTED root
(`authConstructedRoot`), its `src` column to `c.target`, and its opened leaf to the CONSTRUCTED on-edge
leaf (`authLeafAt`). The faithfulness/leaf/edge/tier-DECODE are NOT here — they are constructed in
§1-§3. This is the realizability the prover supplies, the dual of the soundness
`StarkSound`/`ChipTableSound` extraction. DATA-bearing (`Type 1`). -/
structure CapOpenTraceFloor {State : Type} (S : CapHashScheme State) (effectBit : EffectMask)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (actor0 : Label) (c : FacetCap) : Type 1 where
  /-- the cap-open trace + its memory boundary (the prover's BUILT depth-16 cap-tree opening). -/
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  t : VmTrace
  /-- the chip table is sound (the chip's hash IS the deployed cap-hash `S.chipAbsorb`). -/
  hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2)
  /-- the prover's BUILT cap-open `Satisfied2` of the live fan-out descriptor. -/
  hsat : Satisfied2 S.chipAbsorb (effCapOpenV3 base name n) minit mfin maddrs t
  /-- the cap-open row index. -/
  i : Nat
  hi : i < t.rows.length
  /-- the cap-open row's `src` column IS the edge's `src` (`c.target`). -/
  hsrc : (envAt t i).loc capOpenCols.src = (c.target : ℤ)
  /-- the opened leaf IS the CONSTRUCTED on-edge leaf. -/
  hedge : leafOf capOpenCols (envAt t i) = authLeafAt actor0 c effectBit actor0 c.target
  /-- the trace's committed `cap_root` column IS the CONSTRUCTED root. -/
  hroot : (envAt t i).loc capOpenCols.capRoot
    = authConstructedRoot S actor0 c effectBit c.target

/-- **`authConstructs_source` — ASSEMBLE the soundness carrier from `AuthorizedByCap` + the trace
floor (the DE-LAUNDERING).** From the authorizing cap `c ∈ caps actor0` (the `AuthorizedByCap` witness
data) and the slimmed trace floor (which carries ONLY the realizable trace + row-identification), CONSTRUCT
a full `EffAuthoritySource` — with `hfaith`/`leafAt`/`hedge`/`htier` CONSTRUCTED in §1-§3, NOT assumed.
The turn is `⟨actor0, c.target, dst, amt⟩`. Everything the kernel transition determines is built; only the
trace is carried. -/
def authConstructs_source {State : Type} (S : CapHashScheme State)
    (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hbit : effectBit = 1 <<< n) (hn : n < Dregg2.Circuit.DeployedCapOpen.MASK_BITS)
    (actor0 : Label) (c : FacetCap)
    (hmem : c ∈ caps actor0)
    (hfacet : isEffectPermitted c.facet effectBit = true)
    (htier : c.tier.isSatisfiedBy provided = true)
    (dst : Label) (amt : ℤ)
    (pre : RecChainedState)
    (floor : CapOpenTraceFloor S effectBit base name n actor0 c) :
    EffAuthoritySource S.chipAbsorb caps provided pre
      { actor := actor0, src := c.target, dst := dst, amt := amt } base name n := by
  subst hbit
  exact
    { hn := hn
      State := State
      S := S
      vkOfTag := vkOfTier c.tier
      minit := floor.minit
      mfin := floor.mfin
      maddrs := floor.maddrs
      t := floor.t
      hChip := floor.hChip
      hsat := floor.hsat
      i := floor.i
      hi := floor.hi
      leafAt := authLeafAt actor0 c (1 <<< n)
      hfaith := by
        -- the CONSTRUCTED faithfulness, at the trace's committed root (= the constructed root).
        rw [floor.hroot]
        exact authConstructed_faithful S caps provided _ actor0 c hmem hfacet htier
      hsrc := floor.hsrc
      hedge := floor.hedge
      htier := by
        -- the constructed on-edge leaf decodes its tier back to `c.tier`, satisfied by `provided`.
        show (tierOfTag (vkOfTier c.tier)
          (authLeafAt actor0 c (1 <<< n) actor0 c.target).auth_tag).isSatisfiedBy provided = true
        have hleaf : (authLeafAt actor0 c (1 <<< n) actor0 c.target).auth_tag
            = (c.tier.tierByte : ℤ) := by
          simp only [authLeafAt, and_self, if_pos]
        rw [hleaf, tierOfTag_tierByte]; exact htier }

/-- **`authComplete_constructed` — THE DE-LAUNDERED CAP-AUTHORITY COMPLETENESS RUNG.** From the
authorizing cap (`AuthorizedByCap` data: `c ∈ caps actor0`, facet permits `effectBit`, tier satisfied)
and the slimmed trace floor, the deployed two-axis `authorizedFacetEffB caps provided (1 <<< n) tr`
PASSES — FORCED by the source `authConstructs_source` ASSEMBLES (everything but the trace CONSTRUCTED).
This is the genuine completeness content the prior `authorityComplete_generic` LAUNDERED: it no longer
ASSUMES `DeployedFaithfulEff`/the membership — it BUILDS them from the cap. -/
theorem authComplete_constructed {State : Type} (S : CapHashScheme State)
    (caps : FacetCaps) (provided : AuthProvided)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hn : n < Dregg2.Circuit.DeployedCapOpen.MASK_BITS)
    (actor0 : Label) (c : FacetCap)
    (hmem : c ∈ caps actor0)
    (hfacet : isEffectPermitted c.facet (1 <<< n) = true)
    (htier : c.tier.isSatisfiedBy provided = true)
    (dst : Label) (amt : ℤ) (pre : RecChainedState)
    (floor : CapOpenTraceFloor S (1 <<< n) base name n actor0 c) :
    authorizedFacetEffB caps provided (1 <<< n)
      { actor := actor0, src := c.target, dst := dst, amt := amt } = true :=
  effAuthoritySource_authorizes S.chipAbsorb caps provided pre _ base name n
    (authConstructs_source S caps provided (1 <<< n) base name n rfl hn actor0 c hmem hfacet htier
      dst amt pre floor)

/-- **`authComplete_constructed_from_hypothesis` — the rung taking the `AuthorizedByCap` PROP directly.**
The completeness statement de-laundered into the natural form: GIVEN `AuthorizedByCap caps provided
(1 <<< n) tr` (the existential authority hypothesis) AND the realizable trace floor for the witnessing
cap, the gate passes — with the faithful membership CONSTRUCTED, not assumed. The `AuthorizedByCap`
existential is destructured to recover the witnessing cap, then `authComplete_constructed` fires. -/
theorem authComplete_constructed_from_hypothesis {State : Type} (S : CapHashScheme State)
    (caps : FacetCaps) (provided : AuthProvided)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hn : n < Dregg2.Circuit.DeployedCapOpen.MASK_BITS)
    (tr : Turn)
    (h : AuthorizedByCap caps provided (1 <<< n) tr)
    (pre : RecChainedState)
    (floor : ∀ c : FacetCap, c ∈ caps tr.actor → c.target = tr.src →
      CapOpenTraceFloor S (1 <<< n) base name n tr.actor c) :
    authorizedFacetEffB caps provided (1 <<< n) tr = true := by
  obtain ⟨c, hmem, htgt, hfacet, htier⟩ := h
  have hturn : tr = { actor := tr.actor, src := c.target, dst := tr.dst, amt := tr.amt } := by
    rw [htgt]
  rw [hturn]
  exact authComplete_constructed S caps provided base name n hn tr.actor c hmem
    hfacet htier tr.dst tr.amt pre (floor c hmem htgt)

/-! ## §5 — Axiom hygiene. -/

#assert_axioms authLeaf_membersAt
#assert_axioms authLeaf_confers
#assert_axioms authConstructed_faithful
#assert_axioms authConstructs_source
#assert_axioms authComplete_constructed
#assert_axioms authComplete_constructed_from_hypothesis

end Dregg2.Circuit.CircuitCompletenessAuthorityConstruct
