/-
# Dregg2.Circuit.PeepholeFrontierScanSound — the SCAN → `Forced` soundness bridge that closes the
frontier collapse's certification for AND-NODE descriptors.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Nothing here hand-writes a constraint; the
scan (`PeepholeFrontierScan`) READS the constraint list an `EffectVmDescriptor2` carries, and every
soundness step is a machine-checked field-algebra / list-membership argument over the emitted gate
bodies. This module adds theorems ABOUT that scan; it changes none of it.

## What this closes — the named residual of `PeepholeFrontierScan`

`PeepholeFrontierScan` proved `frontier_security : ∀ d, FrontierCertified d → SecurityRefinement`,
where `FrontierCertified d` demands a `Forced` (accept-reachability) certificate — over the SURVIVING
(kept) constraints — for every collapsed zero-test output. It auto-discharged that ONLY for the
depth-0 no-and case (`frontierCertified_of_no_and`); and-node descriptors certified only trivially.

THE MISSING LEMMA the residual named: `acceptReachable_sound : ∀ cs c, c ∈ acceptReachable cs →
Forced cs c` — the syntactic fixpoint scan is SOUND w.r.t. the inductive `Forced` certificate. §2
proves it, program-independently, by induction on the reach-step index: each `reachStep` move
reconstructs an `andL`/`andR` `Forced` constructor from the scanned and-edge and sibling bit gate.

§1 supplies the two scan-recogniser soundness lemmas the induction needs (`andGate_of_mem_andEdges`,
`bitGate_of_hasBitGate`). §3 packages the full-list certificate. §4 gives the GENERAL bridge
`frontierCertified_of_kept_reachable`: a descriptor whose every collapse-site output is
accept-reachable OVER THE KEPT LIST is `FrontierCertified`, hence `frontier_preservation` applies —
`acceptReachable_sound` instantiated at the surviving constraints. This covers `secondDescriptor`
(its one site is the left child of the accept-root and-node, forced through the surviving sibling bit
gate — NOT `atomDesc`, NOT the no-and case).

## The wall the pilot exposes (GROUND-TRUTHED, not conjectured)

The field-delta pilot's `collapseSites = [(0,95,96),(1,97,98)]`, `collapsedOuts = [95,97]`, with a
31-and right-nested spine rooted at the accept output `279`. Over the FULL constraint list both 95
and 97 are accept-reachable (so both are recognised as sites). But over the KEPT list the committed
scan reaches only `{279, 95}`: `frontierKeep` DROPS each site's own bit gate, and the committed
`Forced` inductive forces a node ONLY through its SIBLING'S bit gate — so forcing the internal spine
node `c_N1` (needed to descend to site 97) would require site 95's DROPPED bit gate. Hence
`Forced (kept) 97` is genuinely UNINHABITED, and `acceptReachable_sound` alone does NOT discharge
`FrontierCertified` for the pilot's second site.

§5–§7 close this by STRENGTHENING the certificate: `ForcedS` adds the "force a bit-gated child of a
forced product node by its OWN bit gate" constructors (`andLself`/`andRself`), sound by the same
field algebra (`l·r = 1 ∧ l ∈ {0,1} ⟹ l = 1`, no sibling needed). `forcedS_field_one` proves it;
`frontier_preservation_S` re-runs both refinement legs on the strengthened certificate; and the
strengthened scan `acceptReachableS` reaches BOTH pilot sites over the kept list (§8 #guards it,
alongside the committed scan reaching only 95). The pilot's collapse IS semantically sound and the
strengthened machinery witnesses it — the committed `Forced` was simply too weak.

## Named residual (no `sorry`, no stand-in)

* Instantiating `frontier_preservation` / `frontier_preservation_S` on a CONCRETE descriptor requires
  discharging its side condition `site.out ∈ acceptReachable(S) (kept)` as a kernel Prop. Without
  `decide`/`native_decide` (forbidden here — kernel-reducing the 374-constraint pilot scan is the
  OOM class) that is a decide-free concrete-membership leg: cheap for `secondDescriptor`'s single
  and-node, a structural induction over the `Formula`→descriptor lowering for the pilot's spine. §8
  demonstrates the mechanism fires via `#guard` (compiled evaluation, not the kernel), the same
  discipline `PeepholeFrontierScan`'s Generality section uses. The general theorems (§2,§4,§7) are
  kernel-clean and #assert-checked.

Standalone and additive: imports `PeepholeFrontierScan`; changes none of it.
-/
import Dregg2.Circuit.PeepholeFrontierScan

namespace Dregg2.Circuit.PeepholeFrontierScanSound

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (Wire Node gate bitBody subW negW fieldWindow fieldAssignment)
open Dregg2.Circuit.PeepholeR2Certified (gate_holds_any field_of_src_gate)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.PeepholeGeneralBatch (hasProdGate isProdGate isProdGate_eq)
open Dregg2.Circuit.PeepholeFrontierScan

set_option autoImplicit false

/-! ## 1. Scan-recogniser soundness — a recognised and-edge / bit gate really IS in the list.

These invert the two shape recognisers the fixpoint reads, mirroring the existing
`acceptGate_of_mem_acceptRoots` / `collapseSites_hasProd` inversions. No `decide` on the descriptor. -/

/-! A recognised and-edge `(out, l, r)` witnesses the exact and-gate `out − l·r = 0` in the list. -/
theorem andGate_of_mem_andEdges {cs : List VmConstraint2} {out l r : Nat}
    (h : (out, l, r) ∈ andEdges cs) : andGate out l r ∈ cs := by
  obtain ⟨c, hc, hmatch⟩ := List.mem_filterMap.1 h
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only at hmatch
    split at hmatch
    · exact absurd hmatch (by simp)
    · rename_i honT
      have honT' : onT = false := by cases onT <;> simp_all
      subst honT'
      split at hmatch
      · rename_i out' k l' r'
        split at hmatch
        · rename_i hcond
          rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hmatch
          obtain ⟨hout, hl, hr⟩ := hmatch
          subst hout; subst hl; subst hr
          simp only [beq_iff_eq] at hcond
          subst hcond
          exact hc
        · exact absurd hmatch (by simp)
      · exact absurd hmatch (by simp)
  | base _ => simp at hmatch
  | lookup _ => simp at hmatch
  | memOp _ => simp at hmatch
  | mapOp _ => simp at hmatch
  | umemOp _ => simp at hmatch
  | proofBind _ => simp at hmatch

/-- A column the list `hasBitGate` on really carries the booleanity gate `c·(c−1) = 0`. -/
theorem bitGate_of_hasBitGate {cs : List VmConstraint2} {c : Nat}
    (h : hasBitGate cs c = true) : bitGate c ∈ cs := by
  unfold hasBitGate at h
  rw [List.any_eq_true] at h
  obtain ⟨d, hd, hp⟩ := h
  cases d with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only at hp
    cases onT with
    | true => simp at hp
    | false =>
      simp only [Bool.not_false, Bool.true_and] at hp
      split at hp
      · rename_i a b k
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨⟨ha, hb⟩, hk⟩ := hp
        subst ha; subst hb; subst hk
        exact hd
      · exact absurd hp (by simp)
  | base _ => exact absurd hp (by simp)
  | lookup _ => exact absurd hp (by simp)
  | memOp _ => exact absurd hp (by simp)
  | mapOp _ => exact absurd hp (by simp)
  | umemOp _ => exact absurd hp (by simp)
  | proofBind _ => exact absurd hp (by simp)

/-! ## 2. THE MISSING LEMMA — `acceptReachable_sound`. The syntactic fixpoint is SOUND w.r.t. the
inductive `Forced` certificate. -/

/-- Every scanned accept root is `Forced` by its own accept gate. -/
theorem forced_of_mem_acceptRoots {cs : List VmConstraint2} {c : Nat}
    (h : c ∈ acceptRoots cs) : Forced cs c :=
  .accept c (acceptGate_of_mem_acceptRoots h)

/-- One reach step preserves forcedness: every column it adds reconstructs an `andL`/`andR`
certificate from the scanned and-edge and the surviving sibling bit gate. -/
theorem forced_of_mem_reachStep {cs : List VmConstraint2} {S : List Nat}
    (hS : ∀ c ∈ S, Forced cs c) {c : Nat} (h : c ∈ reachStep cs S) : Forced cs c := by
  unfold reachStep at h
  rw [List.mem_append] at h
  rcases h with hin | hflat
  · exact hS c hin
  · rw [List.mem_flatMap] at hflat
    obtain ⟨e, he, hc⟩ := hflat
    obtain ⟨eout, el, er⟩ := e
    simp only at hc
    split at hc
    · rename_i houtS
      have hforcedOut : Forced cs eout := hS eout houtS
      have hedge : andGate eout el er ∈ cs := andGate_of_mem_andEdges he
      rw [List.mem_append] at hc
      rcases hc with hL | hR
      · split at hL
        · rename_i hbit
          simp only [List.mem_singleton] at hL
          subst hL
          exact .andL eout _ _ hforcedOut hedge (bitGate_of_hasBitGate hbit)
        · simp at hL
      · split at hR
        · rename_i hbit
          simp only [List.mem_singleton] at hR
          subst hR
          exact .andR eout _ _ hforcedOut hedge (bitGate_of_hasBitGate hbit)
        · simp at hR
    · simp at hc

/-- Every column in the `n`-step reach iterate is `Forced`. -/
theorem forced_of_mem_reachIter {cs : List VmConstraint2} :
    ∀ (n : Nat) (c : Nat), c ∈ reachIter cs n → Forced cs c
  | 0, _, h => forced_of_mem_acceptRoots h
  | n + 1, c, h => by
      rw [reachIter] at h
      exact forced_of_mem_reachStep (fun c' hc' => forced_of_mem_reachIter n c' hc') h

/-- THE BRIDGE. The decidable accept-reachability scan is SOUND: every column it reports is carried
by an inductive `Forced` certificate over the same constraint list. Program-independent. -/
theorem acceptReachable_sound {cs : List VmConstraint2} {c : Nat}
    (h : c ∈ acceptReachable cs) : Forced cs c :=
  forced_of_mem_reachIter _ c h

/-! ## 3. The full-list certificate — every collapse site's output is `Forced` over the FULL list. -/

/-- Auto-discharge over the ORIGINAL constraints: every recognised collapse-site output carries a
`Forced` certificate, via `acceptReachable_sound` and the scan condition it was recognised under. -/
theorem forced_of_collapseSite {cs : List VmConstraint2} {x out inv : Nat}
    (h : (x, out, inv) ∈ collapseSites cs) : Forced cs out :=
  acceptReachable_sound (collapseSites_out_reachable h)

/-! ## 4. THE GENERAL BRIDGE to `FrontierCertified` — reachability OVER THE KEPT LIST certifies.

`FrontierCertified` demands the `Forced` certificate over the SURVIVING (kept) constraints, because
on an accepting TARGET trace only the surviving gates hold. `acceptReachable_sound` instantiated at
the kept list turns a kept-reachability side condition into that certificate, program-independently.
Any descriptor whose every collapse-site output is accept-reachable over its kept constraints is thus
`FrontierCertified`, and `frontier_security` / `frontier_preservation` apply. -/

/-- If every collapse-site output is reachable over the kept constraints, the descriptor is
`FrontierCertified`. This is `acceptReachable_sound` at `cs := kept`. -/
theorem frontierCertified_of_kept_reachable (d : EffectVmDescriptor2)
    (h : ∀ x out inv, (x, out, inv) ∈ collapseSites d.constraints →
          out ∈ acceptReachable (d.constraints.filter (frontierKeep d.constraints))) :
    FrontierCertified d :=
  fun x out inv hs => acceptReachable_sound (h x out inv hs)

/-- Consequently the frontier collapse is a genuine satisfiability-preserving pass on any such
descriptor — `frontier_security`/`frontier_completeness` through the general kept-reachability path. -/
theorem frontier_preservation_of_kept_reachable (d : EffectVmDescriptor2)
    (h : ∀ x out inv, (x, out, inv) ∈ collapseSites d.constraints →
          out ∈ acceptReachable (d.constraints.filter (frontierKeep d.constraints))) :
    SatisfiabilityPreservation (frontierPass d) :=
  frontier_preservation d (frontierCertified_of_kept_reachable d h)

/-! ## 5. The STRENGTHENED certificate `ForcedS` — closes the wall the pilot exposes.

The committed `Forced` forces a node ONLY through its SIBLING'S bit gate (`andL`/`andR`). When a
descendant's forcing path passes through a node whose sibling is a collapsed site (its bit gate
DROPPED), the chain breaks over the kept list — exactly the pilot's `c_N1`. `ForcedS` adds the
OWN-bit-gate rule: if a product node `out = l·r` is forced to 1 and a child is bit-gated, THAT child
is 1 (`l·r = 1 ∧ l ∈ {0,1} ⟹ l = 1`), no sibling needed. It also keeps the two sibling rules, so it
is a genuine generalisation (`Forced.toForcedS`). -/

/-- `ForcedS cs c` : column `c` is forced to 1 by the accept gate, transitively through and-nodes,
using EITHER a sibling's OR the child's OWN booleanity gate. Every premise is a gate membership. -/
inductive ForcedS (cs : List VmConstraint2) : Nat → Prop where
  | accept (c : Nat) (h : acceptGate c ∈ cs) : ForcedS cs c
  /-- force the LEFT child via the RIGHT sibling's bit gate (committed `andL`). -/
  | andLsib (out l r : Nat) (hpar : ForcedS cs out)
      (hg : andGate out l r ∈ cs) (hrb : bitGate r ∈ cs) : ForcedS cs l
  /-- force the RIGHT child via the LEFT sibling's bit gate (committed `andR`). -/
  | andRsib (out l r : Nat) (hpar : ForcedS cs out)
      (hg : andGate out l r ∈ cs) (hlb : bitGate l ∈ cs) : ForcedS cs r
  /-- force the LEFT child via its OWN bit gate — no constraint on the sibling. -/
  | andLself (out l r : Nat) (hpar : ForcedS cs out)
      (hg : andGate out l r ∈ cs) (hlb : bitGate l ∈ cs) : ForcedS cs l
  /-- force the RIGHT child via its OWN bit gate — no constraint on the sibling. -/
  | andRself (out l r : Nat) (hpar : ForcedS cs out)
      (hg : andGate out l r ∈ cs) (hrb : bitGate r ∈ cs) : ForcedS cs r

/-- THE STRENGTHENED SOUNDNESS CORE. A `ForcedS` column carries field value 1 whenever every gate
holds — the two new own-bit cases use `l·r = 1 ∧ l ∈ {0,1} ⟹ l = 1` directly. -/
theorem forcedS_field_one {cs : List VmConstraint2} {c : Nat}
    {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f l : Bool}
    (hall : ∀ g ∈ cs, g.holdsAt hash tf env f l)
    (cert : ForcedS cs c) :
    fieldAssignment env.loc c = 1 := by
  induction cert with
  | accept c h =>
      have hz := field_of_src_gate (hall _ h)
      rw [fw_acceptBody] at hz
      have := sub_eq_zero.mp hz
      simpa using this
  | andLsib out l r hpar hg hrb ihpar =>
      have hgz := field_of_src_gate (hall _ hg)
      have hbz := field_of_src_gate (hall _ hrb)
      rw [fw_andBody] at hgz
      rw [fw_bitBody] at hbz
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      rcases mul_eq_zero.mp hbz with hr0 | hr1
      · rw [hr0, mul_zero] at hlr; exact absurd hlr (by norm_num)
      · have hr : fieldAssignment env.loc r = 1 := sub_eq_zero.mp hr1
        rw [hr, mul_one] at hlr; exact hlr
  | andRsib out l r hpar hg hlb ihpar =>
      have hgz := field_of_src_gate (hall _ hg)
      have hbz := field_of_src_gate (hall _ hlb)
      rw [fw_andBody] at hgz
      rw [fw_bitBody] at hbz
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      rcases mul_eq_zero.mp hbz with hl0 | hl1
      · rw [hl0, zero_mul] at hlr; exact absurd hlr (by norm_num)
      · have hl : fieldAssignment env.loc l = 1 := sub_eq_zero.mp hl1
        rw [hl, one_mul] at hlr; exact hlr
  | andLself out l r hpar hg hlb ihpar =>
      have hgz := field_of_src_gate (hall _ hg)
      have hbz := field_of_src_gate (hall _ hlb)
      rw [fw_andBody] at hgz
      rw [fw_bitBody] at hbz
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      rcases mul_eq_zero.mp hbz with hl0 | hl1
      · rw [hl0, zero_mul] at hlr; exact absurd hlr (by norm_num)
      · exact sub_eq_zero.mp hl1
  | andRself out l r hpar hg hrb ihpar =>
      have hgz := field_of_src_gate (hall _ hg)
      have hbz := field_of_src_gate (hall _ hrb)
      rw [fw_andBody] at hgz
      rw [fw_bitBody] at hbz
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      rcases mul_eq_zero.mp hbz with hr0 | hr1
      · rw [hr0, mul_zero] at hlr; exact absurd hlr (by norm_num)
      · exact sub_eq_zero.mp hr1

/-- `ForcedS` is monotone in its constraint list. -/
theorem ForcedS.mono {cs cs' : List VmConstraint2} (hsub : cs ⊆ cs') {c : Nat}
    (cert : ForcedS cs c) : ForcedS cs' c := by
  induction cert with
  | accept c h => exact .accept c (hsub h)
  | andLsib out l r hpar hg hrb ih => exact .andLsib out l r ih (hsub hg) (hsub hrb)
  | andRsib out l r hpar hg hlb ih => exact .andRsib out l r ih (hsub hg) (hsub hlb)
  | andLself out l r hpar hg hlb ih => exact .andLself out l r ih (hsub hg) (hsub hlb)
  | andRself out l r hpar hg hrb ih => exact .andRself out l r ih (hsub hg) (hsub hrb)

/-- `ForcedS` genuinely generalises the committed `Forced`: every committed certificate lifts. -/
theorem Forced.toForcedS {cs : List VmConstraint2} {c : Nat} (cert : Forced cs c) : ForcedS cs c := by
  induction cert with
  | accept c h => exact .accept c h
  | andL out l r hpar hg hrb ih => exact .andLsib out l r ih hg hrb
  | andR out l r hpar hg hlb ih => exact .andRsib out l r ih hg hlb

/-! ## 6. The strengthened scan — adds BOTH children of a forced and-node whenever EITHER child is
bit-gated (if one child is bit-gated, the other is forced via that same gate as sibling). -/

/-- One strengthened reach step. -/
def reachStepS (cs : List VmConstraint2) (S : List Nat) : List Nat :=
  S ++ (andEdges cs).flatMap fun e =>
    if e.1 ∈ S then
      (if hasBitGate cs e.2.1 || hasBitGate cs e.2.2 then [e.2.1, e.2.2] else [])
    else []

def reachIterS (cs : List VmConstraint2) : Nat → List Nat
  | 0 => acceptRoots cs
  | n + 1 => reachStepS cs (reachIterS cs n)

/-- The strengthened fixpoint over the constraint list. -/
def acceptReachableS (cs : List VmConstraint2) : List Nat :=
  reachIterS cs ((andEdges cs).length + 1)

/-- The strengthened reach step preserves `ForcedS`: an added child is forced either by its own or by
its sibling's bit gate, whichever the list carries. -/
theorem forcedS_of_mem_reachStepS {cs : List VmConstraint2} {S : List Nat}
    (hS : ∀ c ∈ S, ForcedS cs c) {c : Nat} (h : c ∈ reachStepS cs S) : ForcedS cs c := by
  unfold reachStepS at h
  rw [List.mem_append] at h
  rcases h with hin | hflat
  · exact hS c hin
  · rw [List.mem_flatMap] at hflat
    obtain ⟨e, he, hc⟩ := hflat
    obtain ⟨eout, el, er⟩ := e
    simp only at hc
    split at hc
    · rename_i houtS
      have hforcedOut : ForcedS cs eout := hS eout houtS
      have hedge : andGate eout el er ∈ cs := andGate_of_mem_andEdges he
      split at hc
      · rename_i hbit
        -- hbit : hasBitGate cs el || hasBitGate cs er = true ; c ∈ [el, er]
        simp at hc
        simp only [Bool.or_eq_true] at hbit
        rcases hbit with hl | hr
        · -- left child bit-gated : force el by own bit, er by sibling (el) bit
          rcases hc with rfl | rfl
          · exact .andLself eout _ _ hforcedOut hedge (bitGate_of_hasBitGate hl)
          · exact .andRsib eout _ _ hforcedOut hedge (bitGate_of_hasBitGate hl)
        · -- right child bit-gated : force el by sibling (er) bit, er by own bit
          rcases hc with rfl | rfl
          · exact .andLsib eout _ _ hforcedOut hedge (bitGate_of_hasBitGate hr)
          · exact .andRself eout _ _ hforcedOut hedge (bitGate_of_hasBitGate hr)
      · simp at hc
    · simp at hc

theorem forcedS_of_mem_reachIterS {cs : List VmConstraint2} :
    ∀ (n : Nat) (c : Nat), c ∈ reachIterS cs n → ForcedS cs c
  | 0, _, h => .accept _ (acceptGate_of_mem_acceptRoots h)
  | n + 1, c, h => by
      rw [reachIterS] at h
      exact forcedS_of_mem_reachStepS (fun c' hc' => forcedS_of_mem_reachIterS n c' hc') h

/-- The strengthened scan is SOUND w.r.t. `ForcedS`. -/
theorem acceptReachableS_sound {cs : List VmConstraint2} {c : Nat}
    (h : c ∈ acceptReachableS cs) : ForcedS cs c :=
  forcedS_of_mem_reachIterS _ c h

/-! ## 7. The strengthened refinement legs — `frontier_security`/`completeness` on a `ForcedS`
certificate. These re-run the committed row proofs (verbatim shape) with `Forced` → `ForcedS` and the
strengthened field core, so a `ForcedS`-certified descriptor gets a genuine preservation. -/

/-- The strengthened side condition: every collapse-site output carries a `ForcedS` certificate over
the surviving (kept) constraints of `d`. -/
def FrontierCertifiedS (d : EffectVmDescriptor2) : Prop :=
  ∀ x out inv, (x, out, inv) ∈ collapseSites d.constraints →
    ForcedS (d.constraints.filter (frontierKeep d.constraints)) out

theorem frontier_security_row_S (d : EffectVmDescriptor2) (hcert : FrontierCertifiedS d)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (htgt : ∀ c ∈ (frontierCollapse d).constraints, c.holdsAt hash tf env f l)
    (c : VmConstraint2) (hc : c ∈ d.constraints) :
    c.holdsAt hash tf env f l := by
  by_cases hkeep : frontierKeep d.constraints c = true
  · exact htgt c (kept_sub_target d (List.mem_filter.2 ⟨hc, hkeep⟩))
  · simp only [Bool.not_eq_true] at hkeep
    rcases dropped_is_site hkeep with ⟨out, rfl, hout⟩ | ⟨x, out, rfl, hxo⟩ | ⟨x, out, inv, rfl, hs⟩
    · obtain ⟨x, inv, hs⟩ := collapsedOut_site hout
      have hforced : ForcedS (frontierCollapse d).constraints out :=
        (hcert x out inv hs).mono (kept_sub_target d)
      have hone : fieldAssignment env.loc out = 1 := forcedS_field_one htgt hforced
      refine gate_holds_any hash tf env f l ?_
      rw [fw_bitBody, hone]; ring
    · obtain ⟨inv, hs⟩ := prodPair_site hxo
      have hzero : fieldAssignment env.loc x = 0 := by
        have := field_of_src_gate (htgt _ (List.mem_append_right _ (rawGate_mem hs)))
        rw [fw_rawBody] at this; exact this
      refine gate_holds_any hash tf env f l ?_
      rw [fw_prodBody, hzero, zero_mul]
    · have hforced : ForcedS (frontierCollapse d).constraints out :=
        (hcert x out inv hs).mono (kept_sub_target d)
      have hone : fieldAssignment env.loc out = 1 := forcedS_field_one htgt hforced
      have hzero : fieldAssignment env.loc x = 0 := by
        have := field_of_src_gate (htgt _ (List.mem_append_right _ (rawGate_mem hs)))
        rw [fw_rawBody] at this; exact this
      refine gate_holds_any hash tf env f l ?_
      rw [fw_invBody, hzero, hone]; ring

theorem frontier_completeness_row_S (d : EffectVmDescriptor2) (hcert : FrontierCertifiedS d)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (hsrc : ∀ c ∈ d.constraints, c.holdsAt hash tf env f l)
    (c : VmConstraint2) (hc : c ∈ (frontierCollapse d).constraints) :
    c.holdsAt hash tf env f l := by
  rcases List.mem_append.1 hc with hkept | hraw
  · exact hsrc c (List.mem_of_mem_filter hkept)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hraw
    obtain ⟨x, out, inv⟩ := s
    have hforced : ForcedS d.constraints out := (hcert x out inv hs).mono (kept_sub_source d)
    have hone : fieldAssignment env.loc out = 1 := forcedS_field_one hsrc hforced
    have hprod := field_of_src_gate (hsrc _ (collapseSites_hasProd hs))
    rw [fw_prodBody, hone, mul_one] at hprod
    refine gate_holds_any hash tf env f l ?_
    show fieldWindow env (.loc x) = 0
    rw [fw_rawBody]; exact hprod

theorem frontier_security_S (d : EffectVmDescriptor2) (hcert : FrontierCertifiedS d) :
    SecurityRefinement (frontierPass d) := by
  intro hash minit mfin maddrs t hsat
  refine Dregg2.Circuit.PeepholeGeneralBatch.satisfied2_congr_constraints
    (frontierCollapse d) d rfl rfl (memOps_frontier d).symm (mapOps_frontier d).symm ?_ hsat
  intro i hi c hc
  exact frontier_security_row_S d hcert hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
    (hsat.rowConstraints i hi) c hc

theorem frontier_completeness_S (d : EffectVmDescriptor2) (hcert : FrontierCertifiedS d) :
    CompletenessPreservation (frontierPass d) := by
  intro hash minit mfin maddrs t hsat
  refine Dregg2.Circuit.PeepholeGeneralBatch.satisfied2_congr_constraints
    d (frontierCollapse d) rfl rfl (memOps_frontier d) (mapOps_frontier d) ?_ hsat
  intro i hi c hc
  exact frontier_completeness_row_S d hcert hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
    (hsat.rowConstraints i hi) c hc

/-- BOTH LEGS on the strengthened certificate — a genuine equisatisfiability-preserving pass on every
`ForcedS`-certified descriptor. -/
theorem frontier_preservation_S (d : EffectVmDescriptor2) (hcert : FrontierCertifiedS d) :
    SatisfiabilityPreservation (frontierPass d) :=
  ⟨frontier_security_S d hcert, frontier_completeness_S d hcert⟩

/-- The strengthened general bridge: strengthened reachability over the kept list certifies. This is
`acceptReachableS_sound` at `cs := kept`, and it CLOSES the pilot's spine (§8 exhibits both sites
reachable over kept by the strengthened scan). -/
theorem frontierCertifiedS_of_kept_reachable (d : EffectVmDescriptor2)
    (h : ∀ x out inv, (x, out, inv) ∈ collapseSites d.constraints →
          out ∈ acceptReachableS (d.constraints.filter (frontierKeep d.constraints))) :
    FrontierCertifiedS d :=
  fun x out inv hs => acceptReachableS_sound (h x out inv hs)

theorem frontier_preservation_S_of_kept_reachable (d : EffectVmDescriptor2)
    (h : ∀ x out inv, (x, out, inv) ∈ collapseSites d.constraints →
          out ∈ acceptReachableS (d.constraints.filter (frontierKeep d.constraints))) :
    SatisfiabilityPreservation (frontierPass d) :=
  frontier_preservation_S d (frontierCertifiedS_of_kept_reachable d h)

/-! ## 8. CONCRETE evidence — the mechanism fires on the real descriptors (compiled `#guard`, no
kernel `decide`). These exhibit, at ground truth, the wall and its closure.

`keptOf d` is the surviving constraint list the certificate ranges over. -/

section Concrete
open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (descriptor)
open Dregg2.Circuit.PeepholeGeneralPass (secondDescriptor)

def keptOf (d : EffectVmDescriptor2) : List VmConstraint2 :=
  d.constraints.filter (frontierKeep d.constraints)

--  PILOT: the two recognised sites and their dropped bit columns. 
#guard collapseSites (descriptor prog).constraints == [(0, 95, 96), (1, 97, 98)]
#guard collapsedOuts (descriptor prog).constraints == [95, 97]

/-! THE WALL: the COMMITTED scan over the KEPT list reaches site 95 but NOT site 97 — the committed
`Forced` cannot certify the pilot's second site. -/
#guard 95 ∈ acceptReachable (keptOf (descriptor prog))
#guard 97 ∉ acceptReachable (keptOf (descriptor prog))

/-! THE CLOSURE: the STRENGTHENED scan over the KEPT list reaches BOTH sites — `ForcedS` certifies
the pilot's whole spine over the surviving constraints. -/
#guard 95 ∈ acceptReachableS (keptOf (descriptor prog))
#guard 97 ∈ acceptReachableS (keptOf (descriptor prog))

/-! SECOND DESCRIPTOR: its single site (out 5) is the left child of the accept-root and-node and is
reachable over the kept list by the COMMITTED scan (surviving sibling bit gate) — certifiable via the
committed general path, NOT `atomDesc`, NOT the no-and case. -/
#guard collapseSites secondDescriptor.constraints == [(0, 5, 6)]
#guard 5 ∈ acceptReachable (keptOf secondDescriptor)
#guard 5 ∈ acceptReachableS (keptOf secondDescriptor)

end Concrete

/-! ## 9. Kernel-cleanliness of the general theory. -/

#assert_all_clean [
  andGate_of_mem_andEdges,
  bitGate_of_hasBitGate,
  acceptReachable_sound,
  forced_of_collapseSite,
  frontierCertified_of_kept_reachable,
  frontier_preservation_of_kept_reachable,
  forcedS_field_one,
  ForcedS.mono,
  Forced.toForcedS,
  acceptReachableS_sound,
  frontier_security_row_S,
  frontier_completeness_row_S,
  frontier_security_S,
  frontier_completeness_S,
  frontier_preservation_S,
  frontierCertifiedS_of_kept_reachable,
  frontier_preservation_S_of_kept_reachable
]

end Dregg2.Circuit.PeepholeFrontierScanSound
