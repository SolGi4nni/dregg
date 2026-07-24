/-
# Dregg2.Circuit.PeepholeFrontierScan — a SYNTACTIC accept-reachability scan that generalises the
full zero-test → raw-affine collapse off the pilot, replacing `pilot_holds_iff`.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Nothing here hand-writes a constraint; the
scan READS the constraint list any `EffectVmDescriptor2` carries and the pass rewrites it, and the
soundness core is a machine-checked field-algebra argument over the emitted gate bodies.

## What this closes — the program-DEPENDENT half named by `PeepholeGeneralBatch`

`PeepholeGeneralBatch.generalBatchPeephole` elides the REDUNDANT booleanity bit gate of every
zero-test, program-independently (374 → 312 on the pilot). `PeepholeBatchCertified` reaches full
parity 33/35/30 but PILOT-SPECIFICALLY: it replaces each frontier zero-test by its RAW affine gate
`x = 0` via `pilot_holds_iff`, a lemma that unfolds `prog.source` and indexes the pilot's atom
registry. The full collapse (drop bit + product + inverse, keep only `x = 0`) is sound only where the
accept path FORCES the zero-test's tested column `x` to 0.

That forcing is SYNTACTICALLY DETECTABLE and here made a machine-checked object:

* the accept gate `out − 1 = 0` forces the root output column to 1;
* an and-node gate `out − l·r = 0` with `out` forced to 1 and a bit-gated sibling forces BOTH
  children to 1 (over the field: `l·r = 1`, `r ∈ {0,1}` ⟹ `r = 1 ∧ l = 1`);
* a zero-test's product gate `x·out = 0` with `out` forced to 1 forces `x = 0`.

`Forced cs c` (§1) is the inductive certificate of "column `c` is forced to 1 by the accept gate,
transitively through and-nodes, using only gates present in `cs`". `forced_field_one` proves it sound
as pure field algebra — the HARD leg (accept-reachability ⟹ residual 0), program-independent, argued
from the constraint SHAPES and NOT from any source-program `Holds` lemma.

`acceptReachable` (§2) is the decidable fixpoint that computes the forced set from the constraint
list. `frontierCollapse d` (§3) drops the {bit, product, inverse} gates of every confirmed zero-test
whose output is forced and appends one raw affine gate `x = 0` — a program-independent
`EffectVmDescriptor2 → EffectVmDescriptor2` rewrite. §5 proves its ∀-d `SatisfiabilityPreservation`
CONDITIONED on a `Forced` certificate for each collapsed site: the collapse is sound over EVERY
descriptor whose collapsed outputs are accept-reachable, with the identity trace map both ways (no
canonical witness rebuild — the elided out/inv columns are already pinned by the surviving
reachability chain).

## Named residual (no `sorry`, no stand-in)

* The ∀-d preservation takes the per-site `Forced` certificate as an explicit hypothesis. Automatic
  SYNTHESIS of those certificates by `acceptReachable` (a scan-completeness bridge
  `out ∈ acceptReachable ⟹ Forced …`) is the named follow-on; the fixpoint already COMPUTES the
  forced set (demonstrated: it fires on exactly the 2 frontier zero-tests of the pilot and the 1
  frontier zero-test of the second descriptor — via the SCAN, no `pilot_holds_iff`).
* Full 33/35/30 parity ALSO needs the disjunction → pair-gate batch (the R2 collapse of
  `PeepholeR2Certified`, still per-site). This module closes the frontier zero-test → raw-affine leg;
  the R2 disjunction batch is the remaining leg for the whole-graph collapse.

Standalone and additive: imports the general batch / recogniser / pilot; changes none of them.
-/
import Dregg2.Circuit.PeepholeGeneralBatch

namespace Dregg2.Circuit.PeepholeFrontierScan

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (Wire Node gate bitBody subW negW fieldWindow fieldAssignment fieldWire_expr field_zero_of_gate)
open Dregg2.Circuit.PeepholeR2Certified (gate_holds_any field_of_src_gate)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false

/-! ## 0. The three emitted gate shapes, as named constructors, and their field readings. -/

/-- The accept gate for a col-rooted formula: `out − 1 = 0`, forcing `out = 1`. -/
def acceptGate (c : Nat) : VmConstraint2 := gate (subW (Wire.col c).expr (.const 1))

/-- An and-node gate with col children: `out − l·r = 0`. -/
def andGate (out l r : Nat) : VmConstraint2 :=
  gate (subW (Wire.col out).expr (.mul (Wire.col l).expr (Wire.col r).expr))

/-- The booleanity bit gate for column `c`: `c·(c−1) = 0`. -/
def bitGate (c : Nat) : VmConstraint2 := gate (bitBody (.col c))

/-- A zero-test's product gate: `x·out = 0`. -/
def prodGate (x out : Nat) : VmConstraint2 := gate (.mul (.loc x) (.loc out))

/-- A zero-test's inverse gate: `x·inv + out − 1 = 0`. -/
def invGate (x out inv : Nat) : VmConstraint2 :=
  gate (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1)))

/-- The raw affine replacement for a frontier zero-test: `x = 0`. -/
def rawGate (x : Nat) : VmConstraint2 := gate (.loc x)

theorem fw_acceptBody (env : VmRowEnv) (c : Nat) :
    fieldWindow env (subW (Wire.col c).expr (.const 1)) = fieldAssignment env.loc c - 1 := by
  simp only [subW, negW, Wire.expr, fieldWindow]
  push_cast
  ring

theorem fw_andBody (env : VmRowEnv) (out l r : Nat) :
    fieldWindow env (subW (Wire.col out).expr (.mul (Wire.col l).expr (Wire.col r).expr)) =
      fieldAssignment env.loc out - fieldAssignment env.loc l * fieldAssignment env.loc r := by
  simp only [subW, negW, Wire.expr, fieldWindow]
  push_cast
  ring

theorem fw_bitBody (env : VmRowEnv) (c : Nat) :
    fieldWindow env (bitBody (.col c)) =
      fieldAssignment env.loc c * (fieldAssignment env.loc c - 1) := by
  simp only [bitBody, Wire.expr, fieldWindow]
  push_cast
  ring

theorem fw_prodBody (env : VmRowEnv) (x out : Nat) :
    fieldWindow env (.mul (.loc x) (.loc out)) =
      fieldAssignment env.loc x * fieldAssignment env.loc out := by
  simp only [fieldWindow]

theorem fw_invBody (env : VmRowEnv) (x out inv : Nat) :
    fieldWindow env (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1))) =
      fieldAssignment env.loc x * fieldAssignment env.loc inv +
        fieldAssignment env.loc out - 1 := by
  simp only [fieldWindow]
  push_cast
  ring

theorem fw_rawBody (env : VmRowEnv) (x : Nat) :
    fieldWindow env (.loc x) = fieldAssignment env.loc x := by
  simp only [fieldWindow]

/-! ## 1. The accept-reachability certificate and its field soundness — THE HARD LEG. -/

/-- `Forced cs c` : column `c` is forced to the field value 1 by the accept gate, transitively
through and-nodes with a bit-gated sibling, using only constraints present in `cs`. This is a
SYNTACTIC certificate — every constructor's premises are gate memberships, no source program. -/
inductive Forced (cs : List VmConstraint2) : Nat → Prop where
  | accept (c : Nat) (h : acceptGate c ∈ cs) : Forced cs c
  | andL (out l r : Nat) (hpar : Forced cs out)
      (hg : andGate out l r ∈ cs) (hrb : bitGate r ∈ cs) : Forced cs l
  | andR (out l r : Nat) (hpar : Forced cs out)
      (hg : andGate out l r ∈ cs) (hlb : bitGate l ∈ cs) : Forced cs r

/-- THE SOUNDNESS CORE. If every gate in `cs` holds on `env`, a `Forced` column carries field value
1. Pure field algebra over the emitted gate bodies — the accept-reachability ⟹ forced-to-1 leg. -/
theorem forced_field_one {cs : List VmConstraint2} {c : Nat}
    {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f l : Bool}
    (hall : ∀ g ∈ cs, g.holdsAt hash tf env f l)
    (cert : Forced cs c) :
    fieldAssignment env.loc c = 1 := by
  induction cert with
  | accept c h =>
      have hz := field_of_src_gate (hall _ h)
      rw [fw_acceptBody] at hz
      -- hz : fieldAssignment env.loc c - 1 = 0
      have := sub_eq_zero.mp hz
      simpa using this
  | andL out l r hpar hg hrb ihpar =>
      -- ihpar : fieldAssignment env.loc out = 1
      have hgz := field_of_src_gate (hall _ hg)
      have hbz := field_of_src_gate (hall _ hrb)
      rw [fw_andBody] at hgz
      rw [fw_bitBody] at hbz
      -- hgz : out - l*r = 0, ihpar : out = 1 ⟹ l*r = 1
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      -- hbz : r*(r-1) = 0 ⟹ r = 0 ∨ r = 1
      rcases mul_eq_zero.mp hbz with hr0 | hr1
      · rw [hr0, mul_zero] at hlr; exact absurd hlr (by norm_num)
      · have hr : fieldAssignment env.loc r = 1 := sub_eq_zero.mp hr1
        rw [hr, mul_one] at hlr; exact hlr
  | andR out l r hpar hg hlb ihpar =>
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

/-- `Forced` is monotone in its constraint list: a certificate over `cs` lifts to any superlist. -/
theorem Forced.mono {cs cs' : List VmConstraint2} (hsub : cs ⊆ cs') {c : Nat}
    (cert : Forced cs c) : Forced cs' c := by
  induction cert with
  | accept c h => exact .accept c (hsub h)
  | andL out l r hpar hg hrb ihpar => exact .andL out l r ihpar (hsub hg) (hsub hrb)
  | andR out l r hpar hg hlb ihpar => exact .andR out l r ihpar (hsub hg) (hsub hlb)

/-! ## 2. The decidable accept-reachability scan (the driver / #guard witness). -/

open Dregg2.Circuit.PeepholeGeneralBatch (hasProdGate isProdGate isProdGate_eq
  filterMap_filter_of_removed_none satisfied2_congr_constraints)

/-- Root columns forced to 1 by an accept gate `out − 1 = 0`, read by shape. -/
def acceptRoots (cs : List VmConstraint2) : List Nat :=
  cs.filterMap fun c => match c with
    | .windowGate w =>
        if w.onTransition then none else
        match w.body with
        | .add (.loc c) (.mul (.const k) (.const k2)) =>
            if k == (-1 : Int) && k2 == (1 : Int) then some c else none
        | _ => none
    | _ => none

/-- The list carries a booleanity bit gate for column `c`. -/
def hasBitGate (cs : List VmConstraint2) (c : Nat) : Bool :=
  cs.any fun d => match d with
    | .windowGate w =>
        !w.onTransition &&
        (match w.body with
         | .mul (.loc a) (.add (.loc b) (.const k)) => a == c && b == c && k == (-1 : Int)
         | _ => false)
    | _ => false

/-- And-node edges `(out, l, r)` for the gate `out − l·r = 0` with col children, read by shape. -/
def andEdges (cs : List VmConstraint2) : List (Nat × Nat × Nat) :=
  cs.filterMap fun c => match c with
    | .windowGate w =>
        if w.onTransition then none else
        match w.body with
        | .add (.loc out) (.mul (.const k) (.mul (.loc l) (.loc r))) =>
            if k == (-1 : Int) then some (out, l, r) else none
        | _ => none
    | _ => none

/-- One reachability step: a forced and-node output with a bit-gated sibling forces both children. -/
def reachStep (cs : List VmConstraint2) (S : List Nat) : List Nat :=
  S ++ (andEdges cs).flatMap fun e =>
    if e.1 ∈ S then
      (if hasBitGate cs e.2.2 then [e.2.1] else []) ++
        (if hasBitGate cs e.2.1 then [e.2.2] else [])
    else []

def reachIter (cs : List VmConstraint2) : Nat → List Nat
  | 0 => acceptRoots cs
  | n + 1 => reachStep cs (reachIter cs n)

/-- THE SCAN: the columns transitively forced to 1 by the accept gate through and-nodes, a bounded
fixpoint over the constraint list. Program-independent and decidable. The chain of and-nodes cannot
be longer than the number of and-nodes, so `(andEdges cs).length + 1` steps reach the fixpoint. -/
def acceptReachable (cs : List VmConstraint2) : List Nat :=
  reachIter cs ((andEdges cs).length + 1)

/-! ## 3. The frontier collapse — drop {bit, product, inverse} of every forced zero-test, append the
raw affine gate `x = 0`. -/

/-- Confirmed frontier zero-test sites `(x, out, inv)`: an inverse gate whose `out` is
accept-reachable and whose matching product gate `x·out` is present. -/
def collapseSites (cs : List VmConstraint2) : List (Nat × Nat × Nat) :=
  let R := acceptReachable cs
  cs.filterMap fun c => match c with
    | .windowGate w =>
        if w.onTransition then none else
        match w.body with
        | .add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const k) =>
            if k == (-1 : Int) && (out ∈ R) && hasProdGate cs x out
            then some (x, out, inv) else none
        | _ => none
    | _ => none

def collapsedOuts (cs : List VmConstraint2) : List Nat := (collapseSites cs).map (·.2.1)

def rawGates (cs : List VmConstraint2) : List VmConstraint2 :=
  (collapseSites cs).map fun s => rawGate s.1

/-- Keep a constraint unless it is exactly one of a confirmed site's three gates. The product and
inverse drops match the SITE'S `x` (not merely `out`), so a stray gate on the same column survives —
soundness holds over arbitrary descriptors. -/
def frontierKeep (cs : List VmConstraint2) : VmConstraint2 → Bool
  | .windowGate w =>
      if w.onTransition then true else
      match w.body with
      | .mul (.loc a) (.add (.loc b) (.const k)) =>
          !(a == b && k == (-1 : Int) && (a ∈ collapsedOuts cs))
      | .mul (.loc x) (.loc out) =>
          !((x, out) ∈ (collapseSites cs).map fun s => (s.1, s.2.1))
      | .add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const k) =>
          !(k == (-1 : Int) && ((x, out, inv) ∈ collapseSites cs))
      | _ => true
  | _ => true

/-- THE GENERAL FRONTIER COLLAPSE on descriptors: replace every accept-reachable zero-test by its raw
affine gate. A record-update of the constraint list; trace geometry, ABI, hash sites, ranges,
memory/map ops untouched. -/
def frontierCollapse (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints :=
      d.constraints.filter (frontierKeep d.constraints) ++ rawGates d.constraints }

/-! ## 4. Shape lemmas — invert the recogniser matches, no `decide` on the descriptor. -/

/-- A raw gate is a `windowGate`. -/
theorem rawGate_windowGate (x : Nat) : ∃ w, rawGate x = .windowGate w := ⟨_, rfl⟩

/-- Every appended raw gate is a `windowGate`. -/
theorem rawGates_windowGate {cs : List VmConstraint2} {c : VmConstraint2}
    (h : c ∈ rawGates cs) : ∃ w, c = .windowGate w := by
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 h
  exact ⟨_, rfl⟩

/-- A dropped constraint is a `windowGate` (only gate shapes are ever dropped). -/
theorem frontierKeep_false_windowGate {cs : List VmConstraint2} {c : VmConstraint2}
    (h : frontierKeep cs c = false) : ∃ w, c = .windowGate w := by
  cases c with
  | windowGate w => exact ⟨w, rfl⟩
  | base _ => simp [frontierKeep] at h
  | lookup _ => simp [frontierKeep] at h
  | memOp _ => simp [frontierKeep] at h
  | mapOp _ => simp [frontierKeep] at h
  | umemOp _ => simp [frontierKeep] at h
  | proofBind _ => simp [frontierKeep] at h

/-- A dropped constraint is one of a confirmed site's three gates, in one of the three shapes. -/
theorem dropped_is_site {cs : List VmConstraint2} {c : VmConstraint2}
    (h : frontierKeep cs c = false) :
    (∃ out, c = bitGate out ∧ out ∈ collapsedOuts cs) ∨
    (∃ x out, c = prodGate x out ∧ (x, out) ∈ (collapseSites cs).map fun s => (s.1, s.2.1)) ∨
    (∃ x out inv, c = invGate x out inv ∧ (x, out, inv) ∈ collapseSites cs) := by
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only [frontierKeep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i honT
      have honT' : onT = false := by cases onT <;> simp_all
      subst honT'
      split at h
      · rename_i a b k
        simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨hab, hk⟩, hmem⟩ := h
        subst hab; subst hk
        exact Or.inl ⟨a, rfl, hmem⟩
      · rename_i x out
        simp only [Bool.not_eq_false', decide_eq_true_eq] at h
        exact Or.inr (Or.inl ⟨x, out, rfl, h⟩)
      · rename_i x inv out k
        simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨hk, hmem⟩ := h
        subst hk
        exact Or.inr (Or.inr ⟨x, out, inv, rfl, hmem⟩)
      · exact absurd h (by simp)
  | base _ => simp [frontierKeep] at h
  | lookup _ => simp [frontierKeep] at h
  | memOp _ => simp [frontierKeep] at h
  | mapOp _ => simp [frontierKeep] at h
  | umemOp _ => simp [frontierKeep] at h
  | proofBind _ => simp [frontierKeep] at h

/-- A confirmed site's matching product gate is present in the original list. -/
theorem collapseSites_hasProd {cs : List VmConstraint2} {x out inv : Nat}
    (h : (x, out, inv) ∈ collapseSites cs) : prodGate x out ∈ cs := by
  obtain ⟨c, hc, hmatch⟩ := List.mem_filterMap.1 h
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only at hmatch
    split at hmatch
    · exact absurd hmatch (by simp)
    · rename_i honT
      split at hmatch
      · rename_i x' inv' out' k
        split at hmatch
        · rename_i hcond
          rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hmatch
          obtain ⟨hx, hout, hinv⟩ := hmatch
          subst hx; subst hout; subst hinv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨-, hprod⟩ := hcond
          obtain ⟨c2, hc2, hp2⟩ := List.any_eq_true.1 hprod
          rw [isProdGate_eq hp2] at hc2
          exact hc2
        · exact absurd hmatch (by simp)
      · exact absurd hmatch (by simp)
  | base _ => simp at hmatch
  | lookup _ => simp at hmatch
  | memOp _ => simp at hmatch
  | mapOp _ => simp at hmatch
  | umemOp _ => simp at hmatch
  | proofBind _ => simp at hmatch

/-- A confirmed `out` witnesses a full site in the list, hence a raw gate `x = 0` in the collapse. -/
theorem collapsedOut_site {cs : List VmConstraint2} {out : Nat} (h : out ∈ collapsedOuts cs) :
    ∃ x inv, (x, out, inv) ∈ collapseSites cs := by
  obtain ⟨s, hs, hout⟩ := List.mem_map.1 h
  obtain ⟨x, out', inv⟩ := s
  simp only at hout
  subst hout
  exact ⟨x, inv, hs⟩

theorem prodPair_site {cs : List VmConstraint2} {x out : Nat}
    (h : (x, out) ∈ (collapseSites cs).map fun s => (s.1, s.2.1)) :
    ∃ inv, (x, out, inv) ∈ collapseSites cs := by
  obtain ⟨s, hs, hxo⟩ := List.mem_map.1 h
  obtain ⟨x', out', inv⟩ := s
  simp only [Prod.mk.injEq] at hxo
  obtain ⟨hx, hout⟩ := hxo
  subst hx; subst hout
  exact ⟨inv, hs⟩

/-- The raw gate of a confirmed site is in the collapsed constraint list. -/
theorem rawGate_mem {cs : List VmConstraint2} {x out inv : Nat}
    (h : (x, out, inv) ∈ collapseSites cs) : rawGate x ∈ rawGates cs :=
  List.mem_map_of_mem (f := fun s => rawGate s.1) h

/-! ## 5. Carrier bookkeeping — the collapse touches only gate shapes. -/

/-- Any `filterMap` by a function that is `none` on every gate is invariant under the collapse: it
drops only gates and appends only gates. -/
theorem filterMap_frontier_eq {β : Type} (f : VmConstraint2 → Option β)
    (hf : ∀ w, f (.windowGate w) = none) (d : EffectVmDescriptor2) :
    (frontierCollapse d).constraints.filterMap f = d.constraints.filterMap f := by
  show (d.constraints.filter _ ++ rawGates d.constraints).filterMap f = _
  rw [List.filterMap_append]
  have hraw : (rawGates d.constraints).filterMap f = [] := by
    rw [List.filterMap_eq_nil_iff]; intro c hc
    obtain ⟨w, rfl⟩ := rawGates_windowGate hc; exact hf w
  rw [hraw, List.append_nil]
  apply filterMap_filter_of_removed_none
  intro a ha; obtain ⟨w, rfl⟩ := frontierKeep_false_windowGate ha; exact hf w

theorem memOps_frontier (d : EffectVmDescriptor2) :
    memOpsOf (frontierCollapse d) = memOpsOf d :=
  filterMap_frontier_eq _ (fun _ => rfl) d

theorem mapOps_frontier (d : EffectVmDescriptor2) :
    mapOpsOf (frontierCollapse d) = mapOpsOf d :=
  filterMap_frontier_eq _ (fun _ => rfl) d

theorem bindingSlots_frontier (d : EffectVmDescriptor2) :
    publicBindingSlots (frontierCollapse d) = publicBindingSlots d :=
  filterMap_frontier_eq bindingSlot? (fun _ => rfl) d

theorem hashSites_frontier (d : EffectVmDescriptor2) :
    (frontierCollapse d).hashSites = d.hashSites := rfl

theorem ranges_frontier (d : EffectVmDescriptor2) :
    (frontierCollapse d).ranges = d.ranges := rfl

theorem piCount_frontier (d : EffectVmDescriptor2) :
    (frontierCollapse d).piCount = d.piCount := rfl

/-! ## 6. The two contract legs, ∀-d, conditioned on a `Forced` certificate per collapsed site.

`FrontierCertified d` is the syntactic side-condition: every collapsed output is accept-reachable,
certified by a `Forced` derivation over the SURVIVING (kept) constraints. This is a SHAPE fact — no
source-program `Holds` lemma — discharged for concrete descriptors by constructing the derivations. -/

/-- The forcing side-condition: each collapsed site's output carries a `Forced` certificate over the
surviving (kept) constraints of `d`. -/
def FrontierCertified (d : EffectVmDescriptor2) : Prop :=
  ∀ x out inv, (x, out, inv) ∈ collapseSites d.constraints →
    Forced (d.constraints.filter (frontierKeep d.constraints)) out

theorem kept_sub_target (d : EffectVmDescriptor2) :
    d.constraints.filter (frontierKeep d.constraints) ⊆ (frontierCollapse d).constraints := by
  intro c hc
  show c ∈ d.constraints.filter _ ++ rawGates d.constraints
  exact List.mem_append_left _ hc

theorem kept_sub_source (d : EffectVmDescriptor2) :
    d.constraints.filter (frontierKeep d.constraints) ⊆ d.constraints :=
  fun _ hc => List.mem_of_mem_filter hc

/-- SECURITY row: every source constraint holds on an accepting target trace. Survivors hold
verbatim; the three dropped gates of each site are re-derived from the surviving raw gate (`x = 0`)
and the `Forced` output (`out = 1`). -/
theorem frontier_security_row (d : EffectVmDescriptor2) (hcert : FrontierCertified d)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (htgt : ∀ c ∈ (frontierCollapse d).constraints, c.holdsAt hash tf env f l)
    (c : VmConstraint2) (hc : c ∈ d.constraints) :
    c.holdsAt hash tf env f l := by
  by_cases hkeep : frontierKeep d.constraints c = true
  · exact htgt c (kept_sub_target d (List.mem_filter.2 ⟨hc, hkeep⟩))
  · simp only [Bool.not_eq_true] at hkeep
    rcases dropped_is_site hkeep with ⟨out, rfl, hout⟩ | ⟨x, out, rfl, hxo⟩ | ⟨x, out, inv, rfl, hs⟩
    · -- bit gate: out is forced to 1
      obtain ⟨x, inv, hs⟩ := collapsedOut_site hout
      have hforced : Forced (frontierCollapse d).constraints out :=
        (hcert x out inv hs).mono (kept_sub_target d)
      have hone : fieldAssignment env.loc out = 1 := forced_field_one htgt hforced
      refine gate_holds_any hash tf env f l ?_
      rw [fw_bitBody, hone]; ring
    · -- product gate x·out: x is 0 from the surviving raw gate
      obtain ⟨inv, hs⟩ := prodPair_site hxo
      have hzero : fieldAssignment env.loc x = 0 := by
        have := field_of_src_gate (htgt _ (List.mem_append_right _ (rawGate_mem hs)))
        rw [fw_rawBody] at this; exact this
      refine gate_holds_any hash tf env f l ?_
      rw [fw_prodBody, hzero, zero_mul]
    · -- inverse gate: x = 0 (raw) and out = 1 (forced)
      have hforced : Forced (frontierCollapse d).constraints out :=
        (hcert x out inv hs).mono (kept_sub_target d)
      have hone : fieldAssignment env.loc out = 1 := forced_field_one htgt hforced
      have hzero : fieldAssignment env.loc x = 0 := by
        have := field_of_src_gate (htgt _ (List.mem_append_right _ (rawGate_mem hs)))
        rw [fw_rawBody] at this; exact this
      refine gate_holds_any hash tf env f l ?_
      rw [fw_invBody, hzero, hone]; ring

/-- COMPLETENESS row: every target constraint holds on an accepting source trace. Survivors are a
sublist of the source; each appended raw gate `x = 0` follows from the source's product gate
(`x·out = 0`) and the `Forced` output (`out = 1`). -/
theorem frontier_completeness_row (d : EffectVmDescriptor2) (hcert : FrontierCertified d)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (hsrc : ∀ c ∈ d.constraints, c.holdsAt hash tf env f l)
    (c : VmConstraint2) (hc : c ∈ (frontierCollapse d).constraints) :
    c.holdsAt hash tf env f l := by
  rcases List.mem_append.1 hc with hkept | hraw
  · exact hsrc c (List.mem_of_mem_filter hkept)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hraw
    obtain ⟨x, out, inv⟩ := s
    have hforced : Forced d.constraints out := (hcert x out inv hs).mono (kept_sub_source d)
    have hone : fieldAssignment env.loc out = 1 := forced_field_one hsrc hforced
    have hprod := field_of_src_gate (hsrc _ (collapseSites_hasProd hs))
    rw [fw_prodBody, hone, mul_one] at hprod
    refine gate_holds_any hash tf env f l ?_
    show fieldWindow env (.loc x) = 0
    rw [fw_rawBody]; exact hprod

/-! ## 7. The certified pass and its ∀-d preservation. -/

/-- THE PASS. Both trace maps are the identity: the rewrite is constraint-only. -/
def frontierPass (d : EffectVmDescriptor2) : PassiveOptimization d (frontierCollapse d) where
  toTarget := id
  toSource := id
  publicABI := { piCount_eq := (piCount_frontier d).symm
                 bindingSlots_eq := (bindingSlots_frontier d).symm }
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

theorem frontier_security (d : EffectVmDescriptor2) (hcert : FrontierCertified d) :
    SecurityRefinement (frontierPass d) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_congr_constraints (frontierCollapse d) d rfl rfl
    (memOps_frontier d).symm (mapOps_frontier d).symm ?_ hsat
  intro i hi c hc
  exact frontier_security_row d hcert hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
    (hsat.rowConstraints i hi) c hc

theorem frontier_completeness (d : EffectVmDescriptor2) (hcert : FrontierCertified d) :
    CompletenessPreservation (frontierPass d) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_congr_constraints d (frontierCollapse d) rfl rfl
    (memOps_frontier d) (mapOps_frontier d) ?_ hsat
  intro i hi c hc
  exact frontier_completeness_row d hcert hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
    (hsat.rowConstraints i hi) c hc

/-- BOTH LEGS: the general frontier collapse is a genuine equisatisfiability-preserving passive pass
on EVERY descriptor whose collapsed outputs are accept-reachable (certified). -/
theorem frontier_preservation (d : EffectVmDescriptor2) (hcert : FrontierCertified d) :
    SatisfiabilityPreservation (frontierPass d) :=
  ⟨frontier_security d hcert, frontier_completeness d hcert⟩

theorem frontier_satisfiable_iff (d : EffectVmDescriptor2) (hcert : FrontierCertified d)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash d minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (frontierCollapse d) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (frontier_preservation d hcert) hash minit mfin maddrs

/-! ## 8. Composition with the certified E1 — end to end, over ARBITRARY certified `d`. -/

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- The frontier collapse then E1, through the framework's own composition. -/
noncomputable def certifiedFrontierPass (d : EffectVmDescriptor2) (floor : Nat) :
    PassiveOptimization d
      (compactE1 (frontierCollapse d) (deadColsE1 (frontierCollapse d) floor)) :=
  (frontierPass d).comp
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPass
      (frontierCollapse d) floor)

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- END TO END over ARBITRARY certified `d`: `E1 ∘ frontierCollapse` preserves satisfaction both
ways. The hypotheses are the frontier certificate and E1's transition-ceiling certificate. -/
theorem certifiedFrontier_preservation (d : EffectVmDescriptor2) (hcert : FrontierCertified d)
    (floor : Nat) (hceiling : transitionCeilingOk (frontierCollapse d) floor = true) :
    SatisfiabilityPreservation (certifiedFrontierPass d floor) :=
  preservation_comp (frontier_preservation d hcert)
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPreservation
      (frontierCollapse d) floor hceiling)

/-! ## 9. Discharging `FrontierCertified` for the direct-accept (depth-0) frontier.

When a descriptor has NO and-nodes, every accept-reachable column is an accept ROOT, so each collapsed
zero-test's output is forced directly by its own accept gate — `Forced.accept`, no propagation. This
covers a root that IS a single zero-test (the source is one asserted atom). -/

/-- Invert `acceptRoots`: a scanned root column carries an accept gate in the list. -/
theorem acceptGate_of_mem_acceptRoots {cs : List VmConstraint2} {c : Nat}
    (h : c ∈ acceptRoots cs) : acceptGate c ∈ cs := by
  obtain ⟨d, hd, hmatch⟩ := List.mem_filterMap.1 h
  cases d with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only at hmatch
    split at hmatch
    · exact absurd hmatch (by simp)
    · rename_i honT
      have honT' : onT = false := by cases onT <;> simp_all
      subst honT'
      split at hmatch
      · rename_i c' k k2
        split at hmatch
        · rename_i hcond
          rw [Option.some.injEq] at hmatch
          subst hmatch
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨hk, hk2⟩ := hcond
          subst hk; subst hk2
          -- the matched gate is exactly `acceptGate c`
          exact hd
        · exact absurd hmatch (by simp)
      · exact absurd hmatch (by simp)
  | base _ => simp at hmatch
  | lookup _ => simp at hmatch
  | memOp _ => simp at hmatch
  | mapOp _ => simp at hmatch
  | umemOp _ => simp at hmatch
  | proofBind _ => simp at hmatch

/-- A collapse site's output is accept-reachable (the scan condition it was recognised under). -/
theorem collapseSites_out_reachable {cs : List VmConstraint2} {x out inv : Nat}
    (h : (x, out, inv) ∈ collapseSites cs) : out ∈ acceptReachable cs := by
  obtain ⟨c, hc, hmatch⟩ := List.mem_filterMap.1 h
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only at hmatch
    split at hmatch
    · exact absurd hmatch (by simp)
    · rename_i honT
      split at hmatch
      · rename_i x' inv' out' k
        split at hmatch
        · rename_i hcond
          rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hmatch
          obtain ⟨hx, hout, hinv⟩ := hmatch
          subst hx; subst hout; subst hinv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          exact hcond.1.2
        · exact absurd hmatch (by simp)
      · exact absurd hmatch (by simp)
  | base _ => simp at hmatch
  | lookup _ => simp at hmatch
  | memOp _ => simp at hmatch
  | mapOp _ => simp at hmatch
  | umemOp _ => simp at hmatch
  | proofBind _ => simp at hmatch

theorem reachStep_nil {cs : List VmConstraint2} (S : List Nat) (h : andEdges cs = []) :
    reachStep cs S = S := by simp [reachStep, h]

theorem reachIter_nil {cs : List VmConstraint2} (h : andEdges cs = []) :
    ∀ n, reachIter cs n = acceptRoots cs
  | 0 => rfl
  | n + 1 => by rw [reachIter, reachIter_nil h n, reachStep_nil _ h]

theorem acceptReachable_eq_acceptRoots {cs : List VmConstraint2} (h : andEdges cs = []) :
    acceptReachable cs = acceptRoots cs := reachIter_nil h _

/-- An accept gate is never dropped (its body is not a bit / product / inverse shape). -/
theorem frontierKeep_acceptGate (cs : List VmConstraint2) (c : Nat) :
    frontierKeep cs (acceptGate c) = true := rfl

/-- DISCHARGE (direct-accept case): a descriptor with no and-nodes is `FrontierCertified` — every
collapsed output is an accept root, forced by its own accept gate. -/
theorem frontierCertified_of_no_and (d : EffectVmDescriptor2)
    (hAE : andEdges d.constraints = []) : FrontierCertified d := by
  intro x out inv h
  have hout : out ∈ acceptReachable d.constraints := collapseSites_out_reachable h
  rw [acceptReachable_eq_acceptRoots hAE] at hout
  have hacc : acceptGate out ∈ d.constraints := acceptGate_of_mem_acceptRoots hout
  exact Forced.accept out
    (List.mem_filter.2 ⟨hacc, frontierKeep_acceptGate d.constraints out⟩)

/-! ## 10. A CONCRETE certified instance and the GENERALITY #guards.

`atomDesc` is the emitted descriptor of a source that is one asserted atom (`.atom 0`): its root IS a
single zero-test, with no and-nodes. The frontier collapse fires (4 → 2 constraints, one raw affine
gate replacing the zero-test) and is CERTIFIED — a genuine `SatisfiabilityPreservation` discharged
with no `pilot_holds_iff`. -/

def atomDesc : EffectVmDescriptor2 :=
  Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.descriptor (n := 1) (.atom ⟨0, by omega⟩)

theorem atomDesc_no_and : andEdges atomDesc.constraints = [] := rfl

theorem atomDesc_certified : FrontierCertified atomDesc :=
  frontierCertified_of_no_and atomDesc atomDesc_no_and

/-- THE CERTIFIED PASS on `atomDesc`, discharged — both legs, no source `Holds` bridge. -/
theorem atomDesc_preservation : SatisfiabilityPreservation (frontierPass atomDesc) :=
  frontier_preservation atomDesc atomDesc_certified

-- The collapse FIRES on `atomDesc`: the single zero-test (3 gates + accept) becomes accept + one raw
-- affine gate `x = 0` — 4 → 2 constraints, elided bit + inverse.
#guard atomDesc.constraints.length == 4
#guard (collapseSites atomDesc.constraints).length == 1
#guard (frontierCollapse atomDesc).constraints.length == 2

/-! ### GENERALITY — the SYNTACTIC scan fires on the pilot and the second descriptor, no pilot bridge.

`collapseSites` reads only the constraint SHAPES; on the field-delta pilot it recognises exactly the 2
frontier zero-tests (the asserted transition + recomposition residuals) and on the independent second
descriptor exactly its 1 frontier zero-test — the SAME collapse `PeepholeBatchCertified` fired via
`pilot_holds_iff`, now via the general accept-reachability scan. -/

section Generality
open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (descriptor)
open Dregg2.Circuit.PeepholeGeneralPass (secondDescriptor)

-- Pilot: 2 frontier zero-tests recognised by the scan (via `acceptReachable`, no `pilot_holds_iff`).
#guard (collapseSites (descriptor prog).constraints).length == 2

-- Second, independent descriptor: 1 frontier zero-test, output column 5 (`boolBase 1 1 3`).
#guard (collapseSites secondDescriptor.constraints).length == 1
#guard (collapseSites secondDescriptor.constraints) == [(0, 5, 6)]

end Generality

#assert_all_clean [
  forced_field_one,
  Forced.mono,
  memOps_frontier,
  mapOps_frontier,
  bindingSlots_frontier,
  frontier_security_row,
  frontier_completeness_row,
  frontier_security,
  frontier_completeness,
  frontier_preservation,
  frontier_satisfiable_iff,
  certifiedFrontier_preservation,
  acceptGate_of_mem_acceptRoots,
  collapseSites_out_reachable,
  frontierCertified_of_no_and,
  atomDesc_certified,
  atomDesc_preservation
]

end Dregg2.Circuit.PeepholeFrontierScan
