/-
# Dregg2.Circuit.PeepholeR2General — the booleanity collapse R2, generalised OFF the pilot.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Nothing here hand-writes a constraint; the
recognizer READS the constraint list any `EffectVmDescriptor2` carries, the collapse rewrites it, and
the soundness core is a machine-checked field-algebra argument over the emitted gate bodies.

## What this closes — the R2 leg of the program-INDEPENDENT peephole family

`PeepholeR2Certified` certifies the booleanity collapse `((x=c₀)∨(x=c₁)) → (x+k₀)(x+k₁)=0` but
PILOT-SPECIFICALLY: `rwR2Descriptor` is a record-update of `descriptor (rootProgramR2 …)`, the pair
gate is over the RAW-input columns (needing the affine base via `peelConst`), and the security leg is
argued about that one emitted shape.  This module generalises R2 the way `PeepholeFrontierScan` /
`PeepholeGeneralBatch` generalised R1 — a SYNTACTIC recognition of the booleanity or-node cluster in
an ARBITRARY descriptor, and a collapse whose soundness is argued from the CONSTRAINT SHAPE.

### The program-INDEPENDENT recognition and collapse

A materialised disjunction `(x₀=0) ∨ (x₁=0)` (two zero-tests feeding an `∨`-node) emits eight gates
at columns `x₀,out₀,inv₀ , x₁,out₂,inv₂ , out₄`:

* `zeroTest x₀ out₀ inv₀` : `out₀·(out₀−1)=0`, `x₀·out₀=0`, `x₀·inv₀+out₀−1=0`;
* `zeroTest x₁ out₂ inv₂` : `out₂·(out₂−1)=0`, `x₁·out₂=0`, `x₁·inv₂+out₂−1=0`;
* `or (col out₀) (col out₂) out₄` : `out₄·(out₄−1)=0`, `out₄ − ((out₀+out₂) − out₀·out₂) = 0`.

When the disjunction is ASSERTED — i.e. `out₄` is forced to `1` by the surviving accept chain — R2
replaces those eight gates by the SINGLE degree-2 gate

    x₀ · x₁ = 0

over the two TESTED columns (NOT the raw affine base: the tested columns are exactly the two
residuals the zero-tests read, and their product vanishes iff one residual is `0`, `mul_eq_zero`).
This is MORE general than the pilot's `(x+k₀)(x+k₁)` — it fires on any or-of-two-zero-tests, with no
`peelConst`, no affine base, no same-term condition; on the pilot's 30 booleanity sites the two tested
columns are the residuals `b_j` and `b_j−1`, so `x₀·x₁ = b_j·(b_j−1)` — exactly booleanity.

### The local, program-INDEPENDENT correctness core (`collapse_security_row`)

The heart is `collapse_security_row`: over ANY site, the CANONICAL zero-test witnesses
(`zeroBit`/`zeroInv` of the two tested residuals, and the `∨`-output pinned to `1`) discharge all
eight elided gates — `mul_eq_zero` / `zero_witness_gate` / `orGate_one_iff` — GIVEN only `x₀·x₁=0` and
`out₄=1`.  This is the generalisation of `PeepholeR2Certified.pairGate_iff_or` from "the pilot's
affine pair" to "the two raw tested columns", proven once, ∀-site.

## The two contract legs

* `collapseR2_completeness` (`CompletenessPreservation`, identity trace map): over EVERY descriptor
  whose site-gates are present and whose `out₄` is `Forced`, the appended pair gate `x₀·x₁=0` is
  DERIVED from the source's or-body, bit and product gates plus the accept-forcing — via
  `PeepholeFrontierScan.forced_field_one` and `orGate_one_iff`.  A genuine ∀-d theorem.

* SECURITY (`SecurityRefinement`, the witness-rebuild direction) is discharged HERE for representative
  descriptors (the single asserted disjunction over `≥2` atom layouts) through `collapse_security_row`
  and `PeepholeR2Certified`-style `satisfied2_transfer`.  The FULLY GENERAL ∀-d security is the NAMED
  residual below.

## Named residuals — what is NOT proven here (no `sorry`, no stand-in)

1. GENERAL ∀-d SECURITY.  The witness rebuild is proven program-independently at the ROW level
   (`collapse_security_row`), but assembling it into a ∀-d `SecurityRefinement` needs three further
   pieces this module does not close over ARBITRARY `d`: (a) a shape-inversion that every DROPPED
   constraint is one of the site's eight gates (the R1 analogue is `FrontierScan.dropped_is_site`);
   (b) a FRESHNESS side-condition that no SURVIVING constraint reads the four rebuilt private columns
   `out₀,inv₀,out₂,inv₂` (trivially true in the emitted layout, where only the removed cluster reads
   them); (c) the `satisfied2_transfer` global-leg nils, which hold for the memory/hash/range-free
   `descriptor` family but not for an arbitrary `EffectVmDescriptor2`.  For the representative
   descriptors all three are discharged; the general certificate is the follow-on — exactly the
   altitude at which `FrontierScan` left its own `FrontierCertified` synthesis open.
2. ITERATION (inherited from R1/R2Certified).  Each collapse fires ONCE, at one recognised site.
   Folding all 30 of the pilot's fires onto the single pilot descriptor — whose constraint list stops
   matching after the first fire — is the same wall the R1 modules named; the pilot is DEMONSTRATED
   here only at the RECOGNITION level (`r2Sites` finds its 30 booleanity or-nodes, via the syntactic
   scan, no `pilot_holds_iff`), exactly as `FrontierScan` demonstrated its own recognition.
3. The forcing of a pilot site's `out₄` runs through the 30-deep `∧`-spine, not a direct accept; the
   representative descriptors force `out₄` directly (`Forced.accept`).  Synthesising the deep-spine
   `Forced` certificates is the same follow-on `FrontierScan` named.

Standalone and additive: imports the frontier scan (for `Forced`/`forced_field_one`/the gate-body
field lemmas), the R2 certificate (for `gate_holds_any`/`field_of_src_gate`/`fieldRep_cast`) and the
pilot (for the recognition demonstration); changes none of them.
-/
import Dregg2.Circuit.PeepholeFrontierScan

namespace Dregg2.Circuit.PeepholeR2General

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (Wire Node gate bitBody subW negW fieldWindow fieldAssignment fieldWire_expr field_zero_of_gate
   fieldWindow_eq_cast witnessCount outputAt nodesAt descriptor graphConstraints acceptConstraint
   memOps_descriptor_nil mapOps_descriptor_nil)
open Dregg2.Circuit.PeepholeFrontierScan
  (Forced forced_field_one acceptGate andGate bitGate prodGate invGate rawGate
   fw_acceptBody fw_andBody fw_bitBody fw_prodBody fw_invBody fw_rawBody
   acceptReachable hasBitGate)
open Dregg2.Circuit.PeepholeGeneralBatch (hasProdGate satisfied2_congr_constraints)
open Dregg2.Circuit.PeepholeR2Certified (gate_holds_any field_of_src_gate fieldRep_cast)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (zeroBit zeroInv zero_witness_gate fieldRep)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false

/-! ## 0. The site and its eight gates. -/

/-- A recognised booleanity or-node cluster: two zero-tests on columns `x0`/`x1` (outputs
`out0`/`out2`, inverse witnesses `inv0`/`inv2`) feeding an `∨`-node with output `out4`. -/
structure R2SiteData where
  x0 : Nat
  out0 : Nat
  inv0 : Nat
  x1 : Nat
  out2 : Nat
  inv2 : Nat
  out4 : Nat
  deriving DecidableEq, Repr

/-- The `∨`-node body over col-children, exactly as the graph emits it:
`out4 − ((out0+out2) − out0·out2)`. -/
def orBody (out0 out2 out4 : Nat) : WindowExpr :=
  subW (.loc out4) (subW (.add (.loc out0) (.loc out2)) (.mul (.loc out0) (.loc out2)))

def orBodyGate (out0 out2 out4 : Nat) : VmConstraint2 := gate (orBody out0 out2 out4)

/-- The eight gates R2 elides, in the emit's own postorder — so for a source `.or (.atom c0) (.atom c1)`
this list IS `graphConstraints` verbatim. -/
def R2SiteData.gates (s : R2SiteData) : List VmConstraint2 :=
  [ bitGate s.out0, prodGate s.x0 s.out0, invGate s.x0 s.out0 s.inv0,
    bitGate s.out2, prodGate s.x1 s.out2, invGate s.x1 s.out2 s.inv2,
    bitGate s.out4, orBodyGate s.out0 s.out2 s.out4 ]

/-- R2's single replacement gate: the product of the two TESTED columns, `x0·x1 = 0`. -/
def pairColBody (s : R2SiteData) : WindowExpr := .mul (.loc s.x0) (.loc s.x1)

def pairColGate (s : R2SiteData) : VmConstraint2 := gate (pairColBody s)

/-! ## 1. Field readings of the two new gate bodies. -/

theorem fw_orBody (env : VmRowEnv) (out0 out2 out4 : Nat) :
    fieldWindow env (orBody out0 out2 out4) =
      fieldAssignment env.loc out4 -
        (fieldAssignment env.loc out0 + fieldAssignment env.loc out2 -
          fieldAssignment env.loc out0 * fieldAssignment env.loc out2) := by
  simp only [orBody, subW, negW, fieldWindow]
  push_cast
  ring

theorem fw_pairColBody (env : VmRowEnv) (s : R2SiteData) :
    fieldWindow env (pairColBody s) =
      fieldAssignment env.loc s.x0 * fieldAssignment env.loc s.x1 := by
  simp only [pairColBody, fieldWindow]

/-! ## 2. THE LOCAL, PROGRAM-INDEPENDENT CORRECTNESS CORE.

Two directions of the pair gate, both pure field algebra over the site's own columns. -/

/-- FORWARD (completeness content): the eight source gates plus `out4 = 1` FORCE `x0·x1 = 0`.  The
bit gates make `out0,out2` Boolean, the or-body reads `out4 = out0+out2−out0·out2 = 1` so one output
is `1`, the product gate zeroes the corresponding tested column, hence the product `x0·x1` vanishes. -/
theorem pair_of_gates (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (s : R2SiteData)
    (hgates : ∀ c ∈ s.gates, c.holdsAt hash tf env f l)
    (hout4 : fieldAssignment env.loc s.out4 = 1) :
    fieldWindow env (pairColBody s) = 0 := by
  have hb0 := field_of_src_gate (hgates (bitGate s.out0) (by simp [R2SiteData.gates]))
  have hp0 := field_of_src_gate (hgates (prodGate s.x0 s.out0) (by simp [R2SiteData.gates]))
  have hb2 := field_of_src_gate (hgates (bitGate s.out2) (by simp [R2SiteData.gates]))
  have hp2 := field_of_src_gate (hgates (prodGate s.x1 s.out2) (by simp [R2SiteData.gates]))
  have hor := field_of_src_gate (hgates (orBodyGate s.out0 s.out2 s.out4)
    (by simp [R2SiteData.gates]))
  rw [fw_bitBody] at hb0 hb2
  rw [fw_prodBody] at hp0 hp2
  rw [fw_orBody, hout4] at hor
  -- Booleanity of the two zero-test outputs
  have hbit0 : Dregg2.Logic.BoolGraph.IsBit (fieldAssignment env.loc s.out0) := hb0
  have hbit2 : Dregg2.Logic.BoolGraph.IsBit (fieldAssignment env.loc s.out2) := hb2
  -- the or-body: out0 = 1 ∨ out2 = 1
  have hog := Dregg2.Logic.BoolGraph.orGate_complete hbit0 hbit2
  have hsum : fieldAssignment env.loc s.out0 + fieldAssignment env.loc s.out2 -
      fieldAssignment env.loc s.out0 * fieldAssignment env.loc s.out2 = 1 := by
    have : (1 : Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.BabyBear) -
        (fieldAssignment env.loc s.out0 + fieldAssignment env.loc s.out2 -
          fieldAssignment env.loc s.out0 * fieldAssignment env.loc s.out2) = 0 := hor
    linear_combination -this
  have hone := (Dregg2.Logic.BoolGraph.orGate_one_iff hog).mp hsum
  rw [fw_pairColBody]
  rcases hone with h0 | h2
  · -- out0 = 1 ⟹ x0 = 0
    rw [h0, mul_one] at hp0
    rw [hp0, zero_mul]
  · rw [h2, mul_one] at hp2
    rw [hp2, mul_zero]

/-- BACKWARD (security content): the canonical zero-test witnesses discharge ALL EIGHT elided gates,
given `x0·x1 = 0` (the pair gate) and `out4 = 1` (accept-forcing).  Program-independent, ∀-site: the
rebuilt row carries `out0 = zeroBit x0`, `inv0 = zeroInv x0`, `out2 = zeroBit x1`, `inv2 = zeroInv x1`,
`out4 = 1`, and every source gate is a field identity of `zero_witness_gate` / `orGate_one_iff`. -/
theorem collapse_security_row (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (s : R2SiteData)
    (hb0 : fieldAssignment env.loc s.out0 = zeroBit (fieldAssignment env.loc s.x0))
    (hi0 : fieldAssignment env.loc s.inv0 = zeroInv (fieldAssignment env.loc s.x0))
    (hb2 : fieldAssignment env.loc s.out2 = zeroBit (fieldAssignment env.loc s.x1))
    (hi2 : fieldAssignment env.loc s.inv2 = zeroInv (fieldAssignment env.loc s.x1))
    (ho4 : fieldAssignment env.loc s.out4 = 1)
    (hpair : fieldAssignment env.loc s.x0 * fieldAssignment env.loc s.x1 = 0) :
    ∀ c ∈ s.gates, c.holdsAt hash tf env f l := by
  have hz0 := zero_witness_gate (fieldAssignment env.loc s.x0)
  have hz1 := zero_witness_gate (fieldAssignment env.loc s.x1)
  obtain ⟨hzb0, hzp0, hzi0⟩ := hz0
  obtain ⟨hzb1, hzp1, hzi1⟩ := hz1
  -- the disjunction of the two tested columns
  have hor : fieldAssignment env.loc s.x0 = 0 ∨ fieldAssignment env.loc s.x1 = 0 :=
    mul_eq_zero.mp hpair
  -- one of the two outputs is 1
  have hone : zeroBit (fieldAssignment env.loc s.x0) = 1 ∨
      zeroBit (fieldAssignment env.loc s.x1) = 1 := by
    rcases hor with h0 | h1
    · exact Or.inl (by simp [zeroBit, h0])
    · exact Or.inr (by simp [zeroBit, h1])
  intro c hc
  simp only [R2SiteData.gates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- bit out0
    refine gate_holds_any hash tf env f l ?_
    rw [fw_bitBody, hb0]; exact hzb0
  · -- prod x0 out0
    refine gate_holds_any hash tf env f l ?_
    rw [fw_prodBody, hb0]; exact hzp0
  · -- inv x0 out0 inv0
    refine gate_holds_any hash tf env f l ?_
    rw [fw_invBody, hb0, hi0]; linear_combination hzi0
  · -- bit out2
    refine gate_holds_any hash tf env f l ?_
    rw [fw_bitBody, hb2]; exact hzb1
  · -- prod x1 out2
    refine gate_holds_any hash tf env f l ?_
    rw [fw_prodBody, hb2]; exact hzp1
  · -- inv x1 out2 inv2
    refine gate_holds_any hash tf env f l ?_
    rw [fw_invBody, hb2, hi2]; linear_combination hzi1
  · -- bit out4
    refine gate_holds_any hash tf env f l ?_
    rw [fw_bitBody, ho4]; ring
  · -- or body
    refine gate_holds_any hash tf env f l ?_
    rw [fw_orBody, hb0, hb2, ho4]
    rcases hone with h0 | h2
    · rw [h0]; ring
    · rw [h2]; ring

/-! ## 3. The collapse and its carrier bookkeeping. -/

/-- Drop a constraint iff it is one of the site's eight gates (matched by SHAPE against the site's
columns).  Structural, decidable, program-independent. -/
def r2Drop (s : R2SiteData) : VmConstraint2 → Bool
  | .windowGate w =>
      if w.onTransition then false else
      match w.body with
      | .mul (.loc a) (.add (.loc b) (.const k)) =>
          a == b && k == (-1 : Int) && (a == s.out0 || a == s.out2 || a == s.out4)
      | .mul (.loc a) (.loc b) =>
          (a == s.x0 && b == s.out0) || (a == s.x1 && b == s.out2)
      | .add (.add (.mul (.loc a) (.loc i)) (.loc o)) (.const k) =>
          k == (-1 : Int) &&
            ((a == s.x0 && i == s.inv0 && o == s.out0) ||
             (a == s.x1 && i == s.inv2 && o == s.out2))
      | .add (.loc o)
          (.mul (.const k1)
            (.add (.add (.loc ll) (.loc rr)) (.mul (.const k2) (.mul (.loc l2) (.loc r2))))) =>
          k1 == (-1 : Int) && k2 == (-1 : Int) && o == s.out4 &&
            ll == s.out0 && rr == s.out2 && l2 == s.out0 && r2 == s.out2
      | _ => false
  | _ => false

/-- THE GENERAL COLLAPSE on descriptors: drop the recognised cluster's eight gates, append the single
pair gate `x0·x1 = 0`.  A record-update of the constraint list; trace geometry, ABI, hash sites,
ranges, memory/map ops untouched. -/
def collapseR2At (d : EffectVmDescriptor2) (s : R2SiteData) : EffectVmDescriptor2 :=
  { d with constraints :=
      d.constraints.filter (fun c => !r2Drop s c) ++ [pairColGate s] }

/-- A dropped constraint is a `windowGate`; the appended pair gate is one too. -/
theorem pairColGate_windowGate (s : R2SiteData) : ∃ w, pairColGate s = .windowGate w := ⟨_, rfl⟩

theorem r2Drop_windowGate {s : R2SiteData} {c : VmConstraint2} (h : r2Drop s c = true) :
    ∃ w, c = .windowGate w := by
  cases c with
  | windowGate w => exact ⟨w, rfl⟩
  | base _ => simp [r2Drop] at h
  | lookup _ => simp [r2Drop] at h
  | memOp _ => simp [r2Drop] at h
  | mapOp _ => simp [r2Drop] at h
  | umemOp _ => simp [r2Drop] at h
  | proofBind _ => simp [r2Drop] at h

/-- Any `filterMap` by a function that is `none` on every gate is invariant under the collapse. -/
theorem filterMap_collapse_eq {β : Type} (f : VmConstraint2 → Option β)
    (hf : ∀ w, f (.windowGate w) = none) (d : EffectVmDescriptor2) (s : R2SiteData) :
    (collapseR2At d s).constraints.filterMap f = d.constraints.filterMap f := by
  show (d.constraints.filter _ ++ [pairColGate s]).filterMap f = _
  rw [List.filterMap_append]
  have hpair : ([pairColGate s]).filterMap f = [] := by
    simp [pairColGate, gate, hf]
  rw [hpair, List.append_nil]
  apply Dregg2.Circuit.PeepholeGeneralBatch.filterMap_filter_of_removed_none
  intro a ha
  have hd : r2Drop s a = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    rw [hne] at ha; simp at ha
  obtain ⟨w, rfl⟩ := r2Drop_windowGate hd
  exact hf w

theorem memOps_collapse (d : EffectVmDescriptor2) (s : R2SiteData) :
    memOpsOf (collapseR2At d s) = memOpsOf d :=
  filterMap_collapse_eq _ (fun _ => rfl) d s

theorem mapOps_collapse (d : EffectVmDescriptor2) (s : R2SiteData) :
    mapOpsOf (collapseR2At d s) = mapOpsOf d :=
  filterMap_collapse_eq _ (fun _ => rfl) d s

theorem bindingSlots_collapse (d : EffectVmDescriptor2) (s : R2SiteData) :
    publicBindingSlots (collapseR2At d s) = publicBindingSlots d :=
  filterMap_collapse_eq bindingSlot? (fun _ => rfl) d s

theorem hashSites_collapse (d : EffectVmDescriptor2) (s : R2SiteData) :
    (collapseR2At d s).hashSites = d.hashSites := rfl

theorem ranges_collapse (d : EffectVmDescriptor2) (s : R2SiteData) :
    (collapseR2At d s).ranges = d.ranges := rfl

theorem piCount_collapse (d : EffectVmDescriptor2) (s : R2SiteData) :
    (collapseR2At d s).piCount = d.piCount := rfl

/-! ## 4. The passive pass and the ∀-d COMPLETENESS leg. -/

/-- THE PASS.  `toTarget` is the identity — R2 changes no surviving column — and `toSource` rebuilds
the elided disjunction witnesses (used by the security leg, discharged for representatives below). -/
noncomputable def collapseR2Pass (d : EffectVmDescriptor2) (s : R2SiteData)
    (toSrc : VmTrace → VmTrace) (htsPub : ∀ t, (toSrc t).pub = t.pub) :
    PassiveOptimization d (collapseR2At d s) where
  toTarget := id
  toSource := toSrc
  publicABI := { piCount_eq := (piCount_collapse d s).symm
                 bindingSlots_eq := (bindingSlots_collapse d s).symm }
  toTarget_pub := by intro t; rfl
  toSource_pub := htsPub

/-- COMPLETENESS over ARBITRARY `d`: a source witness projects (identity) to a target witness.  The
survivors are a sublist of the source, held verbatim; the appended pair gate is DERIVED from the
source's eight site gates plus the accept-forcing (`forced_field_one` gives `out4 = 1`). -/
theorem collapseR2_completeness (d : EffectVmDescriptor2) (s : R2SiteData)
    (toSrc : VmTrace → VmTrace) (htsPub : ∀ t, (toSrc t).pub = t.pub)
    (hsub : s.gates ⊆ d.constraints) (hforced : Forced d.constraints s.out4) :
    CompletenessPreservation (collapseR2Pass d s toSrc htsPub) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_congr_constraints d (collapseR2At d s) rfl rfl
    (memOps_collapse d s) (mapOps_collapse d s) ?_ hsat
  intro i hi c hc
  -- target constraints = survivors ++ [pair gate]
  rcases List.mem_append.1 hc with hkept | hpair
  · exact hsat.rowConstraints i hi c (List.mem_of_mem_filter hkept)
  · simp only [List.mem_singleton] at hpair
    subst hpair
    -- derive the pair gate
    have hall : ∀ g ∈ d.constraints,
        g.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
      hsat.rowConstraints i hi
    have hgates : ∀ g ∈ s.gates,
        g.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
      fun g hg => hall g (hsub hg)
    have hout4 : fieldAssignment (envAt t i).loc s.out4 = 1 :=
      forced_field_one hall hforced
    exact gate_holds_any hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
      (pair_of_gates hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) s hgates hout4)

/-! ## 5. Representative descriptors: FULL both-legs certification, no `pilot_holds_iff`.

`orDesc c0 c1` is the emitted descriptor of a source that is one asserted disjunction
`(atom c0) ∨ (atom c1)` over `n` atoms: its root IS the `∨`-node, forced to `1` by the accept gate
directly.  The collapse fires (8 graph gates + accept → pair gate + accept) and is CERTIFIED both
ways.  This is R2 generalised OFF the pilot: the pair gate is `x0·x1 = 0` over the tested columns,
recognised program-independently — no `rootProgramR2`, no `peelConst`, no affine base. -/

section Representative

open Dregg2.Metatheory.DirectLogicOptimizerCertificate (Formula)

variable {n : Nat}

/-- The single-disjunction source formula. -/
def orFormula (c0 c1 : Fin n) : Formula n := .or (.atom c0) (.atom c1)

/-- Its emitted descriptor. -/
def orDesc (c0 c1 : Fin n) : EffectVmDescriptor2 := descriptor (orFormula c0 c1)

/-- The site this descriptor presents: outputs/inverses at `n, n+1, n+2, n+3, n+4`. -/
def orSite (c0 c1 : Fin n) : R2SiteData :=
  { x0 := c0.val, out0 := n, inv0 := n + 1,
    x1 := c1.val, out2 := n + 2, inv2 := n + 3, out4 := n + 4 }

/-- The descriptor's constraints ARE the site's eight gates followed by the accept gate on `out4`. -/
theorem orDesc_constraints (c0 c1 : Fin n) :
    (orDesc c0 c1).constraints = (orSite c0 c1).gates ++ [acceptGate (n + 4)] := rfl

/-- `out4` is forced to `1` — it is the accept root. -/
theorem orSite_forced (c0 c1 : Fin n) :
    Forced (orDesc c0 c1).constraints (orSite c0 c1).out4 := by
  refine Forced.accept _ ?_
  rw [orDesc_constraints]
  exact List.mem_append_right _ (by simp [orSite])

/-- The eight site gates are all present in the source. -/
theorem orSite_gates_sub (c0 c1 : Fin n) :
    (orSite c0 c1).gates ⊆ (orDesc c0 c1).constraints := by
  rw [orDesc_constraints]
  exact List.subset_append_left _ _

/-- The accept gate SURVIVES the collapse: its body is none of the eight dropped shapes. -/
theorem accept_not_dropped (c0 c1 : Fin n) :
    r2Drop (orSite c0 c1) (acceptGate (n + 4)) = false := rfl

theorem accept_mem_target (c0 c1 : Fin n) :
    acceptGate (n + 4) ∈ (collapseR2At (orDesc c0 c1) (orSite c0 c1)).constraints := by
  refine List.mem_append_left _ (List.mem_filter.2 ⟨?_, ?_⟩)
  · rw [orDesc_constraints]; exact List.mem_append_right _ (by simp)
  · rw [accept_not_dropped]; rfl

theorem pairColGate_mem_target (d : EffectVmDescriptor2) (s : R2SiteData) :
    pairColGate s ∈ (collapseR2At d s).constraints :=
  List.mem_append_right _ (by simp)

end Representative

/-! ## 5b. The witness rebuild, and the SECURITY leg for the representatives.

An accepting TARGET trace says nothing about the four private columns `out0, inv0, out2, inv2` — R2
deleted every constraint that mentioned them.  `r2RebuildRow` restores the CANONICAL zero-test
witnesses; `out4` is NOT rebuilt, because the surviving accept chain already pins it to `1`
(`forced_field_one`).  The eight elided gates are then discharged by the program-independent
`collapse_security_row`. -/

section Rebuild

/-- The canonical rebuild of a site's four private witness columns. -/
noncomputable def r2RebuildRow (s : R2SiteData) (row : Assignment) : Assignment :=
  fun c =>
    if c = s.out0 then fieldRep (zeroBit (fieldAssignment row s.x0))
    else if c = s.inv0 then fieldRep (zeroInv (fieldAssignment row s.x0))
    else if c = s.out2 then fieldRep (zeroBit (fieldAssignment row s.x1))
    else if c = s.inv2 then fieldRep (zeroInv (fieldAssignment row s.x1))
    else row c

noncomputable def r2RebuildTrace (s : R2SiteData) (t : VmTrace) : VmTrace :=
  { rows := t.rows.map (r2RebuildRow s), pub := t.pub, tf := t.tf }

theorem r2RebuildTrace_pub (s : R2SiteData) (t : VmTrace) : (r2RebuildTrace s t).pub = t.pub := rfl

theorem r2RebuildTrace_rows_length (s : R2SiteData) (t : VmTrace) :
    (r2RebuildTrace s t).rows.length = t.rows.length := by simp [r2RebuildTrace]

theorem r2RebuildTrace_loc (s : R2SiteData) (t : VmTrace) (i : Nat) (h : i < t.rows.length) :
    (envAt (r2RebuildTrace s t) i).loc = r2RebuildRow s ((envAt t i).loc) := by
  simp only [envAt, r2RebuildTrace]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  rfl

theorem r2RebuildRow_untouched (s : R2SiteData) (row : Assignment) {c : Nat}
    (h0 : c ≠ s.out0) (h1 : c ≠ s.inv0) (h2 : c ≠ s.out2) (h3 : c ≠ s.inv2) :
    r2RebuildRow s row c = row c := by
  simp [r2RebuildRow, h0, h1, h2, h3]

theorem fa_untouched (s : R2SiteData) (row : Assignment) {c : Nat}
    (h0 : c ≠ s.out0) (h1 : c ≠ s.inv0) (h2 : c ≠ s.out2) (h3 : c ≠ s.inv2) :
    fieldAssignment (r2RebuildRow s row) c = fieldAssignment row c := by
  simp only [fieldAssignment, r2RebuildRow_untouched s row h0 h1 h2 h3]

theorem fa_out0 (s : R2SiteData) (row : Assignment) :
    fieldAssignment (r2RebuildRow s row) s.out0 = zeroBit (fieldAssignment row s.x0) := by
  show ((r2RebuildRow s row s.out0 : ℤ) : Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.BabyBear) = _
  simp only [r2RebuildRow, if_pos rfl]
  exact fieldRep_cast _

theorem fa_inv0 (s : R2SiteData) (row : Assignment) (h : s.inv0 ≠ s.out0) :
    fieldAssignment (r2RebuildRow s row) s.inv0 = zeroInv (fieldAssignment row s.x0) := by
  show ((r2RebuildRow s row s.inv0 : ℤ) : Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.BabyBear) = _
  simp only [r2RebuildRow, if_neg h, if_pos rfl]
  exact fieldRep_cast _

theorem fa_out2 (s : R2SiteData) (row : Assignment) (h0 : s.out2 ≠ s.out0) (h1 : s.out2 ≠ s.inv0) :
    fieldAssignment (r2RebuildRow s row) s.out2 = zeroBit (fieldAssignment row s.x1) := by
  show ((r2RebuildRow s row s.out2 : ℤ) : Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.BabyBear) = _
  simp only [r2RebuildRow, if_neg h0, if_neg h1, if_pos rfl]
  exact fieldRep_cast _

theorem fa_inv2 (s : R2SiteData) (row : Assignment)
    (h0 : s.inv2 ≠ s.out0) (h1 : s.inv2 ≠ s.inv0) (h2 : s.inv2 ≠ s.out2) :
    fieldAssignment (r2RebuildRow s row) s.inv2 = zeroInv (fieldAssignment row s.x1) := by
  show ((r2RebuildRow s row s.inv2 : ℤ) : Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.BabyBear) = _
  simp only [r2RebuildRow, if_neg h0, if_neg h1, if_neg h2, if_pos rfl]
  exact fieldRep_cast _

end Rebuild

section RepresentativeSecurity

open Dregg2.Metatheory.DirectLogicOptimizerCertificate (Formula)

variable {n : Nat}

/-- SECURITY for the representative family: an accepting TARGET trace expands, through the canonical
witness rebuild, to an accepting SOURCE trace.  The eight elided gates come from the ∀-site
`collapse_security_row`; the accept gate survives and pins `out4 = 1` through
`PeepholeFrontierScan.forced_field_one`. -/
theorem orDesc_security (c0 c1 : Fin n) :
    SecurityRefinement
      (collapseR2Pass (orDesc c0 c1) (orSite c0 c1)
        (r2RebuildTrace (orSite c0 c1)) (fun _ => rfl)) := by
  intro hash minit mfin maddrs t hsat
  set s := orSite c0 c1 with hs
  refine Dregg2.Circuit.PeepholePassCertified.satisfied2_transfer (t := t)
    (u := r2RebuildTrace s t)
    (memOps_descriptor_nil _) (mapOps_descriptor_nil _)
    ((memOps_collapse _ _).trans (memOps_descriptor_nil _))
    ((mapOps_collapse _ _).trans (mapOps_descriptor_nil _)) rfl rfl rfl hsat ?_
  intro i hi c hc
  rw [r2RebuildTrace_rows_length] at hi
  have htgt := hsat.rowConstraints i hi
  -- column arithmetic of the representative layout
  have hx0lt : (s.x0 : Nat) < n := c0.isLt
  have hx1lt : (s.x1 : Nat) < n := c1.isLt
  -- the accept gate survives and forces out4 = 1 on the TARGET row
  have hforced : Forced (collapseR2At (orDesc c0 c1) s).constraints s.out4 :=
    Forced.accept _ (accept_mem_target c0 c1)
  have hone : fieldAssignment (envAt t i).loc s.out4 = 1 := forced_field_one htgt hforced
  -- the appended pair gate holds on the TARGET row
  have hpairz := field_of_src_gate (htgt (pairColGate s) (pairColGate_mem_target _ s))
  rw [fw_pairColBody] at hpairz
  -- transport every needed value to the REBUILT row
  have hloc := r2RebuildTrace_loc s t i hi
  have hx0 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x0 =
      fieldAssignment (envAt t i).loc s.x0 := by
    rw [hloc]; exact fa_untouched s _ (by simp [hs, orSite]; omega) (by simp [hs, orSite]; omega)
      (by simp [hs, orSite]; omega) (by simp [hs, orSite]; omega)
  have hx1 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x1 =
      fieldAssignment (envAt t i).loc s.x1 := by
    rw [hloc]; exact fa_untouched s _ (by simp [hs, orSite]; omega) (by simp [hs, orSite]; omega)
      (by simp [hs, orSite]; omega) (by simp [hs, orSite]; omega)
  have ho4 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.out4 = 1 := by
    rw [hloc, fa_untouched s _ (by simp [hs, orSite]) (by simp [hs, orSite]) (by simp [hs, orSite])
      (by simp [hs, orSite])]
    exact hone
  have hb0 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.out0 =
      zeroBit (fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x0) := by
    rw [hx0, hloc]; exact fa_out0 s _
  have hi0 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.inv0 =
      zeroInv (fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x0) := by
    rw [hx0, hloc]; exact fa_inv0 s _ (by simp [hs, orSite])
  have hb2 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.out2 =
      zeroBit (fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x1) := by
    rw [hx1, hloc]; exact fa_out2 s _ (by simp [hs, orSite]) (by simp [hs, orSite])
  have hi2 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.inv2 =
      zeroInv (fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x1) := by
    rw [hx1, hloc]; exact fa_inv2 s _ (by simp [hs, orSite]) (by simp [hs, orSite])
      (by simp [hs, orSite])
  have hpair : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x0 *
      fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x1 = 0 := by
    rw [hx0, hx1]; exact hpairz
  -- discharge every SOURCE constraint on the rebuilt row
  rw [orDesc_constraints] at hc
  rcases List.mem_append.1 hc with hg | ha
  · exact collapse_security_row hash (r2RebuildTrace s t).tf
      (envAt (r2RebuildTrace s t) i) (i == 0) (i + 1 == (r2RebuildTrace s t).rows.length)
      s hb0 hi0 hb2 hi2 ho4 hpair c hg
  · simp only [List.mem_singleton] at ha
    subst ha
    refine gate_holds_any hash (r2RebuildTrace s t).tf (envAt (r2RebuildTrace s t) i)
      (i == 0) (i + 1 == (r2RebuildTrace s t).rows.length) ?_
    show fieldWindow (envAt (r2RebuildTrace s t) i) (subW (Wire.col (n + 4)).expr (.const 1)) = 0
    rw [fw_acceptBody]
    have : (n + 4 : Nat) = s.out4 := rfl
    rw [this, ho4, sub_self]

end RepresentativeSecurity

/-! ## 6. Two concrete representatives, both certified end to end. -/

section Instances

open Dregg2.Metatheory.DirectLogicOptimizerCertificate (Formula)

-- Representative A: `.or (.atom 0) (.atom 1)` over two atoms.
def cA0 : Fin 2 := ⟨0, by omega⟩
def cA1 : Fin 2 := ⟨1, by omega⟩

-- Representative B: `.or (.atom 0) (.atom 2)` over three atoms — a different layout.
def cB0 : Fin 3 := ⟨0, by omega⟩
def cB1 : Fin 3 := ⟨2, by omega⟩

/-- The certified R2 pass on representative A. -/
noncomputable def reprAPass :
    PassiveOptimization (orDesc cA0 cA1) (collapseR2At (orDesc cA0 cA1) (orSite cA0 cA1)) :=
  collapseR2Pass (orDesc cA0 cA1) (orSite cA0 cA1) (r2RebuildTrace (orSite cA0 cA1)) (fun _ => rfl)

noncomputable def reprBPass :
    PassiveOptimization (orDesc cB0 cB1) (collapseR2At (orDesc cB0 cB1) (orSite cB0 cB1)) :=
  collapseR2Pass (orDesc cB0 cB1) (orSite cB0 cB1) (r2RebuildTrace (orSite cB0 cB1)) (fun _ => rfl)

theorem reprA_completeness : CompletenessPreservation reprAPass :=
  collapseR2_completeness (orDesc cA0 cA1) (orSite cA0 cA1) _ _
    (orSite_gates_sub cA0 cA1) (orSite_forced cA0 cA1)

theorem reprB_completeness : CompletenessPreservation reprBPass :=
  collapseR2_completeness (orDesc cB0 cB1) (orSite cB0 cB1) _ _
    (orSite_gates_sub cB0 cB1) (orSite_forced cB0 cB1)

theorem reprA_security : SecurityRefinement reprAPass := orDesc_security cA0 cA1
theorem reprB_security : SecurityRefinement reprBPass := orDesc_security cB0 cB1

/-- BOTH LEGS on representative A — a genuine equisatisfiability-preserving passive pass, discharged
through the PROGRAM-INDEPENDENT recogniser and the ∀-site witness-rebuild core, with NO
`pilot_holds_iff` and no hand-authored target descriptor. -/
theorem reprA_preservation : SatisfiabilityPreservation reprAPass :=
  ⟨reprA_security, reprA_completeness⟩

/-- BOTH LEGS on a SECOND, differently-laid-out descriptor — the same two general theorems. -/
theorem reprB_preservation : SatisfiabilityPreservation reprBPass :=
  ⟨reprB_security, reprB_completeness⟩

theorem reprA_satisfiable_iff (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (orDesc cA0 cA1) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (collapseR2At (orDesc cA0 cA1) (orSite cA0 cA1)) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation reprA_preservation hash minit mfin maddrs

theorem reprB_satisfiable_iff (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (orDesc cB0 cB1) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (collapseR2At (orDesc cB0 cB1) (orSite cB0 cB1)) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation reprB_preservation hash minit mfin maddrs

-- Resource measurement on the certified objects (compiled `==`, no kernel `decide`).
#guard (orDesc cA0 cA1).constraints.length == 9
#guard (collapseR2At (orDesc cA0 cA1) (orSite cA0 cA1)).constraints.length == 2
#guard (orDesc cB0 cB1).constraints.length == 9
#guard (collapseR2At (orDesc cB0 cB1) (orSite cB0 cB1)).constraints.length == 2

end Instances

/-! ## 7. The SYNTACTIC recognizer, and the GENERALITY demonstration on the pilot.

`r2Sites` reads only the constraint SHAPES.  It recognises a booleanity or-node cluster when: an
or-body gate `(out4, out0, out2)` is present with its bit gate, `out4` is accept-reachable (via the
imported `acceptReachable` fixpoint — no source program), and both `out0`/`out2` carry a confirmed
zero-test (inverse + product gate).  On the field-delta pilot it fires on exactly the 30 booleanity
disjunctions — the SAME 30 sites the pilot's hand emit Booleanises — with NO `pilot_holds_iff`. -/

section Recognizer

/-- Or-body edges `(out4, out0, out2)`, read by shape. -/
def orBodyEdges (cs : List VmConstraint2) : List (Nat × Nat × Nat) :=
  cs.filterMap fun c => match c with
    | .windowGate w =>
        if w.onTransition then none else
        match w.body with
        | .add (.loc o)
            (.mul (.const k1)
              (.add (.add (.loc ll) (.loc rr)) (.mul (.const k2) (.mul (.loc l2) (.loc r2))))) =>
            if k1 == (-1 : Int) && k2 == (-1 : Int) && ll == l2 && rr == r2
            then some (o, ll, rr) else none
        | _ => none
    | _ => none

/-- The confirmed zero-test feeding column `out` — its `(x, inv)`, requiring a matching product
gate `x·out`. -/
def findZeroTest (cs : List VmConstraint2) (out : Nat) : Option (Nat × Nat) :=
  cs.findSome? fun c => match c with
    | .windowGate w =>
        if w.onTransition then none else
        match w.body with
        | .add (.add (.mul (.loc x) (.loc inv)) (.loc o)) (.const k) =>
            if k == (-1 : Int) && o == out && hasProdGate cs x out
            then some (x, inv) else none
        | _ => none
    | _ => none

/-- THE RECOGNIZER: every booleanity or-node cluster whose `∨`-output is accept-reachable. -/
def r2Sites (cs : List VmConstraint2) : List R2SiteData :=
  (orBodyEdges cs).filterMap fun e =>
    let out4 := e.1
    let out0 := e.2.1
    let out2 := e.2.2
    if (acceptReachable cs).contains out4 && hasBitGate cs out4 &&
        hasBitGate cs out0 && hasBitGate cs out2 then
      match findZeroTest cs out0, findZeroTest cs out2 with
      | some (x0, inv0), some (x1, inv2) =>
          some { x0 := x0, out0 := out0, inv0 := inv0, x1 := x1, out2 := out2, inv2 := inv2,
                 out4 := out4 }
      | _, _ => none
    else none

end Recognizer

section Generality
open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (descriptor)

-- The recognizer FIRES on the pilot's 30 booleanity or-nodes, via the syntactic scan, no bridge.
#guard (r2Sites (descriptor prog).constraints).length == 30

-- And on representative A it recognises the one asserted disjunction.
#guard (r2Sites (orDesc cA0 cA1).constraints).length == 1

end Generality

#assert_all_clean [
  fw_orBody,
  fw_pairColBody,
  pair_of_gates,
  collapse_security_row,
  memOps_collapse,
  mapOps_collapse,
  bindingSlots_collapse,
  collapseR2_completeness,
  orDesc_constraints,
  orSite_forced,
  orSite_gates_sub,
  accept_mem_target,
  orDesc_security,
  reprA_completeness,
  reprB_completeness,
  reprA_security,
  reprB_security,
  reprA_preservation,
  reprB_preservation,
  reprA_satisfiable_iff,
  reprB_satisfiable_iff
]

end Dregg2.Circuit.PeepholeR2General
