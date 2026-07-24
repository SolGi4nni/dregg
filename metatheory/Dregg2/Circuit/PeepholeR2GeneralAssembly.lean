/-
# Dregg2.Circuit.PeepholeR2GeneralAssembly — the ∀-d assembly of R2's SECURITY leg.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.  Nothing here hand-writes a constraint; the
recogniser READS the constraint list an `EffectVmDescriptor2` already carries, the collapse rewrites
it, and every soundness step is a machine-checked field-algebra / list-shape argument over the
EMITTED gate bodies.

## What this closes — residual #1 of `PeepholeR2General`

`PeepholeR2General` proved the R2 witness rebuild PROGRAM-INDEPENDENTLY at the ROW level
(`collapse_security_row`: over ANY `R2SiteData`, the canonical zero-test witnesses discharge all
eight elided gates given `x0·x1 = 0` and `out4 = 1`).  It then named THREE pieces that the ∀-`d`
`SecurityRefinement` assembly still needed.  All three are supplied here:

* **(a) SHAPE INVERSION** — `r2Drop_mem_gates`: every constraint the collapse DROPS is one of the
  site's eight gates.  This is the R2 analogue of `PeepholeFrontierScan.dropped_is_site`, proved the
  same way: invert every `match` arm of the recogniser, no `decide` on a descriptor.  Its converse
  `r2Drop_gates` (every site gate IS dropped) is proved too, and holds over an ARBITRARY site.

* **(b) FRESHNESS** — a SURVIVING constraint must not read the four rebuilt private columns
  `out0, inv0, out2, inv2`.  `avoidsCols` computes that syntactically over a `WindowExpr`;
  `avoids_eval_congr` proves a fresh body evaluates identically on two row windows that agree off
  those columns; `holdsAt_of_fresh` lifts that to `VmConstraint2.holdsAt`.  The rebuild's own
  agreement facts (`rebuild_env_loc` / `rebuild_env_nxt`, covering BOTH the `loc` and the `nxt`
  slice — the rebuild remaps every row, so a survivor reading `nxt` would be disturbed too) close
  the leg.

* **(c) THE GLOBAL-LEG NILS** — `satisfied2_transfer` needs `memOpsOf d = []`, `mapOpsOf d = []`,
  `d.hashSites = []`, `d.ranges = []`.  These are carried as certificate fields and DISCHARGED for
  the memory/hash/range-free `descriptor` family (`memOps_descriptor_nil` / `mapOps_descriptor_nil`
  and two `rfl`s), which is exactly where the emitted booleanity sites live.

Assembled: `R2Certified d s → SatisfiabilityPreservation (r2Pass d s)` — a ∀-`d`, ∀-site theorem.
`R2Certified` is a SYNTACTIC side-condition bundle (site well-formedness, gate presence, a `Forced`
certificate over the SURVIVORS, freshness, the four nils); nothing in it mentions a source program.

## The concrete instantiations (a PROVEN Prop about a CONCRETE descriptor, not a `#guard`)

* `orDesc_certified` / `orDesc_preservation` — the ∀-`n`, ∀-`(c0 c1 : Fin n)` family of asserted
  root disjunctions.  Instantiated at the two pilot-shaped booleanity descriptors `reprA`/`reprB`.
* `deep_certified` / `deep_preservation` — `.and (.or (.atom 0) (.atom 1)) (.atom 2)` over `Fin 3`:
  a NON-ROOT site.  Its `out4` is not an accept root; the `Forced` certificate propagates through
  the surviving and-node (`Forced.andL`, bit-gated sibling), the survivors include a WHOLE unrelated
  zero-test cluster plus the and-node, and freshness is a real (not vacuous) check.  The syntactic
  recogniser independently FINDS exactly this site (`deep_recognized`, a proved equation).

## Named residuals (no `sorry`, no stand-in)

1. `R2Certified.fresh` is a HYPOTHESIS at the ∀-`d` altitude, discharged per descriptor (by the
   layout argument for the `orDesc` family, by a cheap closed Boolean evaluation for `deepDesc`).
   A ∀-`p` freshness THEOREM for `descriptor (p : Formula n)` needs the emit's column-disjointness
   invariant (each `nodesAt base p` writes inside `[base, base + witnessCount p)` and reads only its
   children's outputs) — a real induction over `nodesAt`, not attempted here.
2. `r2Fresh` accepts only `windowGate` survivors (plus the three `holdsAt = True` op kinds).  A
   `base`/`lookup`/`mapOp` survivor is rejected outright rather than analysed; the `descriptor`
   family emits none, so this costs nothing there.
3. ITERATION and the pilot's deep `∧`-spine `Forced` synthesis are inherited from
   `PeepholeR2General` unchanged: each collapse still fires ONCE, at one recognised site.
4. Everything here is refinement of ONE constraint list into another; the FRI/STARK soundness floor
   underneath is untouched and undischarged.

Standalone and additive: imports `PeepholeR2General`; changes no existing module.
-/
import Dregg2.Circuit.PeepholeR2General

namespace Dregg2.Circuit.PeepholeR2GeneralAssembly

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (Wire Node gate bitBody subW negW fieldWindow fieldAssignment descriptor
   memOps_descriptor_nil mapOps_descriptor_nil)
open Dregg2.Circuit.PeepholeFrontierScan
  (Forced forced_field_one acceptGate andGate bitGate prodGate invGate)
open Dregg2.Circuit.PeepholeR2General
open Dregg2.Circuit.PeepholeR2Certified (gate_holds_any field_of_src_gate)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (zeroBit zeroInv)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false

/-! ## 0. The site's four PRIVATE columns and its well-formedness. -/

/-- The four columns `r2RebuildRow` overwrites: the two zero-test outputs and their two inverse
witnesses.  `x0`, `x1` and `out4` are NOT rebuilt — they are read from the target row. -/
def siteCols (s : R2SiteData) : List Nat := [s.out0, s.inv0, s.out2, s.inv2]

theorem not_mem_siteCols {s : R2SiteData} {c : Nat} (hc : c ∉ siteCols s) :
    c ≠ s.out0 ∧ c ≠ s.inv0 ∧ c ≠ s.out2 ∧ c ≠ s.inv2 :=
  ⟨fun h => hc (by simp [siteCols, h]), fun h => hc (by simp [siteCols, h]),
   fun h => hc (by simp [siteCols, h]), fun h => hc (by simp [siteCols, h])⟩

/-- A site is WELL FORMED when its four private columns are pairwise distinct and none of the three
columns the rebuild READS (`x0`, `x1`, `out4`) is one of them.  Purely about column indices; the
emitted layout gives it for free (distinct nodes get distinct witness columns). -/
structure SiteWf (s : R2SiteData) : Prop where
  out0_inv0 : s.out0 ≠ s.inv0
  out0_out2 : s.out0 ≠ s.out2
  out0_inv2 : s.out0 ≠ s.inv2
  inv0_out2 : s.inv0 ≠ s.out2
  inv0_inv2 : s.inv0 ≠ s.inv2
  out2_inv2 : s.out2 ≠ s.inv2
  x0_fresh : s.x0 ∉ siteCols s
  x1_fresh : s.x1 ∉ siteCols s
  out4_fresh : s.out4 ∉ siteCols s

/-! ## 1. LEG (a) — the SHAPE INVERSION, both directions.

`r2Drop` recognises by SHAPE.  Both directions of "recognised ⟺ a site gate" are needed: the
forward one to know the collapse removes nothing else, the backward one to know it removes them all.
Mirrors `PeepholeFrontierScan.dropped_is_site`: every `match` arm inverted, no `decide`. -/

/-- FORWARD: every DROPPED constraint is one of the site's eight gates. -/
theorem r2Drop_mem_gates {s : R2SiteData} {c : VmConstraint2} (h : r2Drop s c = true) :
    c ∈ s.gates := by
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only [r2Drop] at h
    split at h
    · exact absurd h (by simp)
    · rename_i honT
      have honT' : onT = false := by cases onT <;> simp_all
      subst honT'
      split at h
      · -- bit gate shape
        rename_i a b k
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc, or_assoc] at h
        obtain ⟨rfl, rfl, hmem⟩ := h
        rcases hmem with rfl | rfl | rfl <;>
          simp [R2SiteData.gates, bitGate, gate, bitBody, Wire.expr]
      · -- product gate shape
        rename_i x out
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [R2SiteData.gates, prodGate, gate]
      · -- inverse gate shape
        rename_i x i o k
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc] at h
        obtain ⟨rfl, hcase⟩ := h
        rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
          simp [R2SiteData.gates, invGate, gate]
      · -- or-body shape
        rename_i o k1 ll rr k2 l2 r2
        simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        simp [R2SiteData.gates, orBodyGate, orBody, gate, subW, negW]
      · exact absurd h (by simp)
  | base _ => simp [r2Drop] at h
  | lookup _ => simp [r2Drop] at h
  | memOp _ => simp [r2Drop] at h
  | mapOp _ => simp [r2Drop] at h
  | umemOp _ => simp [r2Drop] at h
  | proofBind _ => simp [r2Drop] at h

/-- BACKWARD: every site gate IS dropped, over an ARBITRARY site (each recogniser condition is a
reflexivity of the site's own columns). -/
theorem r2Drop_gates (s : R2SiteData) : ∀ g ∈ s.gates, r2Drop s g = true := by
  intro g hg
  simp only [R2SiteData.gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [r2Drop, bitGate, prodGate, invGate, orBodyGate, orBody, gate, bitBody,
      Wire.expr, subW, negW]

/-! ## 2. LEG (b) — FRESHNESS: a survivor must not read the four rebuilt columns. -/

/-- Syntactic check that a window body reads NO column in `cols` — on EITHER row of the window
(`loc` and `nxt`): the rebuild remaps every row, so a survivor peeking at the next row's `out0`
would be disturbed exactly as one reading the current row's. -/
def avoidsCols (cols : List Nat) : WindowExpr → Bool
  | .loc c => decide (c ∉ cols)
  | .nxt c => decide (c ∉ cols)
  | .const _ => true
  | .add a b => avoidsCols cols a && avoidsCols cols b
  | .mul a b => avoidsCols cols a && avoidsCols cols b

/-- A fresh body evaluates identically on two row windows that agree off `cols`. -/
theorem avoids_eval_congr {cols : List Nat} {env₁ env₂ : VmRowEnv}
    (hloc : ∀ k, k ∉ cols → env₁.loc k = env₂.loc k)
    (hnxt : ∀ k, k ∉ cols → env₁.nxt k = env₂.nxt k) (e : WindowExpr)
    (he : avoidsCols cols e = true) : e.eval env₁ = e.eval env₂ := by
  revert he
  induction e with
  | loc c =>
      intro he
      simp only [avoidsCols, decide_eq_true_eq] at he
      exact hloc c he
  | nxt c =>
      intro he
      simp only [avoidsCols, decide_eq_true_eq] at he
      exact hnxt c he
  | const k => intro _; rfl
  | add a b iha ihb =>
      intro he
      simp only [avoidsCols, Bool.and_eq_true] at he
      simp only [WindowExpr.eval, iha he.1, ihb he.2]
  | mul a b iha ihb =>
      intro he
      simp only [avoidsCols, Bool.and_eq_true] at he
      simp only [WindowExpr.eval, iha he.1, ihb he.2]

/-- A constraint is FRESH for a site when it cannot observe the four rebuilt columns.  The three
op kinds whose `holdsAt` is `True` are fresh ROW-LOCALLY — ⚠ and that is the right altitude to state
it at: `r2Fresh` returns `true` for `.umemOp`/`.proofBind` WITHOUT inspecting their expressions, so
`R2Certified` admits descriptors carrying such ops that DO read the rebuilt private columns through a
global (non-row-local) leg. Every instantiation here is in the boolean-graph `descriptor` emit, which
has no such ops, so nothing in this file is affected — but the certificate must not be applied to a
descriptor carrying umemOp/proofBind without first strengthening `r2Fresh` to inspect them.
`base` / `lookup` / `mapOp` read the
row through denotations this module does not analyse and are rejected (the `descriptor` family
emits none of them). -/
def r2Fresh (s : R2SiteData) : VmConstraint2 → Bool
  | .windowGate w => avoidsCols (siteCols s) w.body
  | .memOp _ => true
  | .umemOp _ => true
  | .proofBind _ => true
  | .base _ => false
  | .lookup _ => false
  | .mapOp _ => false

/-- A fresh constraint that holds on one row window holds on any window agreeing off the four
rebuilt columns. -/
theorem holdsAt_of_fresh {s : R2SiteData} {c : VmConstraint2} {hash : List ℤ → ℤ}
    {tf : TraceFamily} {env₁ env₂ : VmRowEnv} {f l : Bool}
    (hf : r2Fresh s c = true)
    (hloc : ∀ k, k ∉ siteCols s → env₁.loc k = env₂.loc k)
    (hnxt : ∀ k, k ∉ siteCols s → env₁.nxt k = env₂.nxt k)
    (h : c.holdsAt hash tf env₁ f l) : c.holdsAt hash tf env₂ f l := by
  cases c with
  | windowGate w =>
      obtain ⟨body, onT⟩ := w
      have hb : avoidsCols (siteCols s) body = true := hf
      have heq : body.eval env₁ = body.eval env₂ :=
        avoids_eval_congr hloc hnxt body hb
      cases onT with
      | false =>
          show body.eval env₂ ≡ 0 [ZMOD 2013265921]
          rw [← heq]; exact h
      | true =>
          show l = false → body.eval env₂ ≡ 0 [ZMOD 2013265921]
          intro hl; rw [← heq]; exact h hl
  | memOp _ => trivial
  | umemOp _ => trivial
  | proofBind _ => trivial
  | base _ => simp [r2Fresh] at hf
  | lookup _ => simp [r2Fresh] at hf
  | mapOp _ => simp [r2Fresh] at hf

/-! ### The rebuild's own agreement facts. -/

theorem rebuildRow_untouched' (s : R2SiteData) (row : Assignment) {c : Nat}
    (hc : c ∉ siteCols s) : r2RebuildRow s row c = row c := by
  obtain ⟨h0, h1, h2, h3⟩ := not_mem_siteCols hc
  exact r2RebuildRow_untouched s row h0 h1 h2 h3

theorem fa_untouched' (s : R2SiteData) (row : Assignment) {c : Nat} (hc : c ∉ siteCols s) :
    fieldAssignment (r2RebuildRow s row) c = fieldAssignment row c := by
  simp only [fieldAssignment, rebuildRow_untouched' s row hc]

theorem rebuild_getD (s : R2SiteData) (rows : List Assignment) (j : Nat) {k : Nat}
    (hk : k ∉ siteCols s) :
    (rows.map (r2RebuildRow s)).getD j zeroAsg k = (rows.getD j zeroAsg) k := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hj : rows[j]? with
  | none => simp
  | some row => simpa using rebuildRow_untouched' s row hk

theorem rebuild_env_loc (s : R2SiteData) (t : VmTrace) (i : Nat) {k : Nat}
    (hk : k ∉ siteCols s) :
    (envAt (r2RebuildTrace s t) i).loc k = (envAt t i).loc k :=
  rebuild_getD s t.rows i hk

theorem rebuild_env_nxt (s : R2SiteData) (t : VmTrace) (i : Nat) {k : Nat}
    (hk : k ∉ siteCols s) :
    (envAt (r2RebuildTrace s t) i).nxt k = (envAt t i).nxt k :=
  rebuild_getD s t.rows (i + 1) hk

/-! ## 3. LEG (c) + the assembled certificate. -/

/-- The survivors of the collapse: the source constraints the recogniser does NOT drop.  They sit
inside both the source list and the target list, so a `Forced` certificate over them lifts to
either side (`Forced.mono`). -/
def survivors (d : EffectVmDescriptor2) (s : R2SiteData) : List VmConstraint2 :=
  d.constraints.filter (fun c => !r2Drop s c)

theorem survivors_sub_source (d : EffectVmDescriptor2) (s : R2SiteData) :
    survivors d s ⊆ d.constraints := fun _ hc => List.mem_of_mem_filter hc

theorem survivors_sub_target (d : EffectVmDescriptor2) (s : R2SiteData) :
    survivors d s ⊆ (collapseR2At d s).constraints := by
  intro c hc
  show c ∈ d.constraints.filter _ ++ [pairColGate s]
  exact List.mem_append_left _ hc

theorem mem_survivors {d : EffectVmDescriptor2} {s : R2SiteData} {c : VmConstraint2}
    (hc : c ∈ d.constraints) (hd : r2Drop s c = false) : c ∈ survivors d s :=
  List.mem_filter.2 ⟨hc, by rw [hd]; rfl⟩

/-- THE SYNTACTIC CERTIFICATE for the ∀-`d` R2 collapse.  Every field is a shape fact about the
constraint LIST — site well-formedness, the eight gates being present, an accept-forcing derivation
over the SURVIVORS, freshness of every survivor, and the four global-leg nils.  No source program,
no `Holds` bridge. -/
structure R2Certified (d : EffectVmDescriptor2) (s : R2SiteData) : Prop where
  wf : SiteWf s
  gatesPresent : s.gates ⊆ d.constraints
  forced : Forced (survivors d s) s.out4
  fresh : ∀ c ∈ d.constraints, r2Drop s c = false → r2Fresh s c = true
  memNil : memOpsOf d = []
  mapNil : mapOpsOf d = []
  hashNil : d.hashSites = []
  rangeNil : d.ranges = []

/-- THE PASS: the general R2 collapse with the canonical witness rebuild as its `toSource`. -/
noncomputable def r2Pass (d : EffectVmDescriptor2) (s : R2SiteData) :
    PassiveOptimization d (collapseR2At d s) :=
  collapseR2Pass d s (r2RebuildTrace s) (fun _ => rfl)

/-! ## 4. THE ∀-d SECURITY THEOREM — the assembly. -/

/-- SECURITY over ARBITRARY `d` and ARBITRARY recognised site: an accepting TARGET trace expands,
through the canonical rebuild of the four private columns, to an accepting SOURCE trace.

The three legs meet here: a DROPPED source constraint is one of the eight site gates
(`r2Drop_mem_gates`) and is discharged by the program-independent `collapse_security_row`; a
SURVIVING source constraint holds on the target row and transports to the rebuilt row because it is
FRESH (`holdsAt_of_fresh`); the global `Satisfied2` legs come across through `satisfied2_transfer`
on the four nils. -/
theorem r2_security (d : EffectVmDescriptor2) (s : R2SiteData) (hcert : R2Certified d s) :
    SecurityRefinement (r2Pass d s) := by
  intro hash minit mfin maddrs t hsat
  refine Dregg2.Circuit.PeepholePassCertified.satisfied2_transfer (t := t)
    (u := r2RebuildTrace s t)
    hcert.memNil hcert.mapNil
    ((memOps_collapse d s).trans hcert.memNil)
    ((mapOps_collapse d s).trans hcert.mapNil)
    hcert.hashNil hcert.rangeNil rfl hsat ?_
  intro i hi c hc
  rw [r2RebuildTrace_rows_length] at hi ⊢
  have htgt : ∀ g ∈ (collapseR2At d s).constraints,
      g.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    hsat.rowConstraints i hi
  -- the accept chain survives, so `out4 = 1` on the TARGET row
  have hforcedT : Forced (collapseR2At d s).constraints s.out4 :=
    hcert.forced.mono (survivors_sub_target d s)
  have hone : fieldAssignment (envAt t i).loc s.out4 = 1 := forced_field_one htgt hforcedT
  -- the appended pair gate holds on the TARGET row
  have hpairz : fieldAssignment (envAt t i).loc s.x0 * fieldAssignment (envAt t i).loc s.x1 = 0 := by
    have hz := field_of_src_gate (htgt (pairColGate s) (pairColGate_mem_target d s))
    rwa [fw_pairColBody] at hz
  -- transport the three READ columns and install the four REBUILT ones
  have hloc := r2RebuildTrace_loc s t i hi
  have hx0 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x0 =
      fieldAssignment (envAt t i).loc s.x0 := by
    rw [hloc]; exact fa_untouched' s _ hcert.wf.x0_fresh
  have hx1 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x1 =
      fieldAssignment (envAt t i).loc s.x1 := by
    rw [hloc]; exact fa_untouched' s _ hcert.wf.x1_fresh
  have ho4 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.out4 = 1 := by
    rw [hloc, fa_untouched' s _ hcert.wf.out4_fresh]; exact hone
  have hb0 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.out0 =
      zeroBit (fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x0) := by
    rw [hx0, hloc]; exact fa_out0 s _
  have hinv0 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.inv0 =
      zeroInv (fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x0) := by
    rw [hx0, hloc]; exact fa_inv0 s _ (Ne.symm hcert.wf.out0_inv0)
  have hb2 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.out2 =
      zeroBit (fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x1) := by
    rw [hx1, hloc]
    exact fa_out2 s _ (Ne.symm hcert.wf.out0_out2) (Ne.symm hcert.wf.inv0_out2)
  have hinv2 : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.inv2 =
      zeroInv (fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x1) := by
    rw [hx1, hloc]
    exact fa_inv2 s _ (Ne.symm hcert.wf.out0_inv2) (Ne.symm hcert.wf.inv0_inv2)
      (Ne.symm hcert.wf.out2_inv2)
  have hpair : fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x0 *
      fieldAssignment (envAt (r2RebuildTrace s t) i).loc s.x1 = 0 := by
    rw [hx0, hx1]; exact hpairz
  -- and now the case split on the recogniser
  by_cases hdrop : r2Drop s c = true
  · exact collapse_security_row hash (r2RebuildTrace s t).tf (envAt (r2RebuildTrace s t) i)
      (i == 0) (i + 1 == t.rows.length) s hb0 hinv0 hb2 hinv2 ho4 hpair c
      (r2Drop_mem_gates hdrop)
  · simp only [Bool.not_eq_true] at hdrop
    refine holdsAt_of_fresh (s := s) (hcert.fresh c hc hdrop) ?_ ?_
      (htgt c (survivors_sub_target d s (mem_survivors hc hdrop)))
    · intro k hk; exact (rebuild_env_loc s t i hk).symm
    · intro k hk; exact (rebuild_env_nxt s t i hk).symm

/-- COMPLETENESS over ARBITRARY `d` — the `PeepholeR2General` theorem, fed the certificate's own
gate-presence and (mono'd) forcing facts. -/
theorem r2_completeness (d : EffectVmDescriptor2) (s : R2SiteData) (hcert : R2Certified d s) :
    CompletenessPreservation (r2Pass d s) :=
  collapseR2_completeness d s (r2RebuildTrace s) (fun _ => rfl) hcert.gatesPresent
    (hcert.forced.mono (survivors_sub_source d s))

/-- **THE ASSEMBLED ∀-d CONTRACT.**  Over EVERY descriptor and EVERY site carrying the syntactic
certificate, the R2 booleanity collapse is a genuine equisatisfiability-preserving passive pass. -/
theorem r2_preservation (d : EffectVmDescriptor2) (s : R2SiteData) (hcert : R2Certified d s) :
    SatisfiabilityPreservation (r2Pass d s) :=
  ⟨r2_security d s hcert, r2_completeness d s hcert⟩

theorem r2_satisfiable_iff (d : EffectVmDescriptor2) (s : R2SiteData) (hcert : R2Certified d s)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ x, Satisfied2 hash d minit mfin maddrs x) ↔
      (∃ y, Satisfied2 hash (collapseR2At d s) minit mfin maddrs y) :=
  satisfiable_iff_of_preservation (r2_preservation d s hcert) hash minit mfin maddrs

/-! ## 5. A decidable freshness driver (for CONCRETE descriptors). -/

/-- Every constraint is either dropped or fresh — a closed Boolean scan of the constraint list. -/
def freshOk (d : EffectVmDescriptor2) (s : R2SiteData) : Bool :=
  d.constraints.all (fun c => r2Drop s c || r2Fresh s c)

theorem fresh_of_freshOk {d : EffectVmDescriptor2} {s : R2SiteData} (h : freshOk d s = true) :
    ∀ c ∈ d.constraints, r2Drop s c = false → r2Fresh s c = true := by
  intro c hc hd
  have hall := List.all_eq_true.1 h c hc
  simpa [hd] using hall

/-- The accept gate is fresh whenever its column is not one of the four rebuilt ones. -/
theorem r2Fresh_acceptGate {s : R2SiteData} {k : Nat} (h : k ∉ siteCols s) :
    r2Fresh s (acceptGate k) = true := by
  simp [r2Fresh, acceptGate, gate, subW, negW, Wire.expr, avoidsCols, h]

/-! ## 6. INSTANTIATION A — the ∀-n family of asserted root disjunctions.

`orDesc c0 c1 = descriptor (.or (.atom c0) (.atom c1))`: the emitted booleanity site of the pilot's
30 disjunctions, in its own descriptor.  Certified for EVERY `n` and EVERY atom pair. -/

section OrFamily

variable {n : Nat}

theorem orSite_wf (c0 c1 : Fin n) : SiteWf (orSite c0 c1) where
  out0_inv0 := by show (n : Nat) ≠ n + 1; omega
  out0_out2 := by show (n : Nat) ≠ n + 2; omega
  out0_inv2 := by show (n : Nat) ≠ n + 3; omega
  inv0_out2 := by show (n : Nat) + 1 ≠ n + 2; omega
  inv0_inv2 := by show (n : Nat) + 1 ≠ n + 3; omega
  out2_inv2 := by show (n : Nat) + 2 ≠ n + 3; omega
  x0_fresh := by
    have hlt := c0.isLt
    show (c0.val) ∉ [n, n + 1, n + 2, n + 3]
    intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    omega
  x1_fresh := by
    have hlt := c1.isLt
    show (c1.val) ∉ [n, n + 1, n + 2, n + 3]
    intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    omega
  out4_fresh := by
    show (n + 4) ∉ [n, n + 1, n + 2, n + 3]
    intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    omega

/-- The accept gate survives, so `out4` is forced over the SURVIVORS. -/
theorem orSite_forced_survivors (c0 c1 : Fin n) :
    Forced (survivors (orDesc c0 c1) (orSite c0 c1)) (orSite c0 c1).out4 := by
  have hmem : acceptGate (orSite c0 c1).out4 ∈ (orDesc c0 c1).constraints := by
    rw [orDesc_constraints]
    refine List.mem_append_right _ ?_
    show acceptGate (n + 4) ∈ [acceptGate (n + 4)]
    simp
  exact Forced.accept _ (mem_survivors hmem (accept_not_dropped c0 c1))

/-- FRESHNESS for the family: the ONLY survivor is the accept gate on `out4 = n + 4`, and the eight
site gates are all dropped (`r2Drop_gates`). -/
theorem orDesc_fresh (c0 c1 : Fin n) :
    ∀ c ∈ (orDesc c0 c1).constraints, r2Drop (orSite c0 c1) c = false →
      r2Fresh (orSite c0 c1) c = true := by
  intro c hc hdrop
  rw [orDesc_constraints] at hc
  rcases List.mem_append.1 hc with hg | ha
  · exact absurd (r2Drop_gates _ c hg) (by rw [hdrop]; simp)
  · simp only [List.mem_singleton] at ha
    subst ha
    refine r2Fresh_acceptGate ?_
    show (n + 4) ∉ [n, n + 1, n + 2, n + 3]
    intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    omega

theorem orDesc_certified (c0 c1 : Fin n) : R2Certified (orDesc c0 c1) (orSite c0 c1) where
  wf := orSite_wf c0 c1
  gatesPresent := orSite_gates_sub c0 c1
  forced := orSite_forced_survivors c0 c1
  fresh := orDesc_fresh c0 c1
  memNil := memOps_descriptor_nil _
  mapNil := mapOps_descriptor_nil _
  hashNil := rfl
  rangeNil := rfl

/-- BOTH LEGS on the whole `orDesc` family, from the ∀-`d` theorem. -/
theorem orDesc_preservation (c0 c1 : Fin n) :
    SatisfiabilityPreservation (r2Pass (orDesc c0 c1) (orSite c0 c1)) :=
  r2_preservation _ _ (orDesc_certified c0 c1)

end OrFamily

/-- Instantiation at the two representatives `PeepholeR2General` certified by hand — now corollaries
of the ∀-`d` assembly rather than bespoke proofs. -/
theorem reprA_preservation_general :
    SatisfiabilityPreservation (r2Pass (orDesc cA0 cA1) (orSite cA0 cA1)) :=
  orDesc_preservation cA0 cA1

theorem reprB_preservation_general :
    SatisfiabilityPreservation (r2Pass (orDesc cB0 cB1) (orSite cB0 cB1)) :=
  orDesc_preservation cB0 cB1

/-! ## 7. INSTANTIATION B — a NON-ROOT site inside a larger emitted graph.

`deepFormula = .and (.or (.atom 0) (.atom 1)) (.atom 2)` over `Fin 3`.  The recognised disjunction's
output column `7` is NOT an accept root: the accept gate pins column `10`, and the forcing has to
travel through the surviving and-node with its bit-gated sibling.  The survivors also contain a
whole UNRELATED zero-test cluster (columns `2, 8, 9`) — so freshness is a real check, not a vacuous
one, and the collapse is proved not to disturb it. -/

section Deep

open Dregg2.Metatheory.DirectLogicOptimizerCertificate (Formula)

def deepFormula : Formula 3 :=
  .and (.or (.atom ⟨0, by omega⟩) (.atom ⟨1, by omega⟩)) (.atom ⟨2, by omega⟩)

def deepDesc : EffectVmDescriptor2 := descriptor deepFormula

/-- The recognised site: the two atom zero-tests at columns `3,4` / `5,6`, joined at `7`. -/
def deepSite : R2SiteData :=
  { x0 := 0, out0 := 3, inv0 := 4, x1 := 1, out2 := 5, inv2 := 6, out4 := 7 }

/-- The emitted constraint list, read off the emit: the site's eight gates FIRST (postorder puts the
two zero-tests then the `∨`-node), then the unrelated zero-test, the and-node, and the accept gate. -/
theorem deepDesc_constraints :
    deepDesc.constraints =
      deepSite.gates ++
        [bitGate 8, prodGate 2 8, invGate 2 8 9, bitGate 10, andGate 10 7 8, acceptGate 10] := rfl

/-- The SURVIVORS, computed: exactly the six non-site gates. -/
theorem deepSurvivors :
    survivors deepDesc deepSite =
      [bitGate 8, prodGate 2 8, invGate 2 8 9, bitGate 10, andGate 10 7 8, acceptGate 10] := rfl

theorem deepSite_wf : SiteWf deepSite where
  out0_inv0 := by show (3 : Nat) ≠ 4; omega
  out0_out2 := by show (3 : Nat) ≠ 5; omega
  out0_inv2 := by show (3 : Nat) ≠ 6; omega
  inv0_out2 := by show (4 : Nat) ≠ 5; omega
  inv0_inv2 := by show (4 : Nat) ≠ 6; omega
  out2_inv2 := by show (5 : Nat) ≠ 6; omega
  x0_fresh := by show (0 : Nat) ∉ [3, 4, 5, 6]; simp
  x1_fresh := by show (1 : Nat) ∉ [3, 4, 5, 6]; simp
  out4_fresh := by show (7 : Nat) ∉ [3, 4, 5, 6]; simp

/-- THE NON-ROOT FORCING: accept pins column `10`; the surviving and-node `10 = 7·8` with a
bit-gated sibling `8` forces the disjunction's output `7`.  A real `Forced.andL` step — the
representative descriptors of `PeepholeR2General` only ever used `Forced.accept`. -/
theorem deep_forced : Forced (survivors deepDesc deepSite) deepSite.out4 := by
  have hacc : acceptGate 10 ∈ survivors deepDesc deepSite := by rw [deepSurvivors]; simp
  have hand : andGate 10 7 8 ∈ survivors deepDesc deepSite := by rw [deepSurvivors]; simp
  have hbit : bitGate 8 ∈ survivors deepDesc deepSite := by rw [deepSurvivors]; simp
  exact Forced.andL 10 7 8 (Forced.accept 10 hacc) hand hbit

/-- Freshness by a closed Boolean scan of the 14 emitted constraints (compiled `Bool`, no `decide`
on a Prop, no kernel instance blow-up). -/
theorem deep_freshOk : freshOk deepDesc deepSite = true := rfl

theorem deep_certified : R2Certified deepDesc deepSite where
  wf := deepSite_wf
  gatesPresent := by rw [deepDesc_constraints]; exact List.subset_append_left _ _
  forced := deep_forced
  fresh := fresh_of_freshOk deep_freshOk
  memNil := memOps_descriptor_nil _
  mapNil := mapOps_descriptor_nil _
  hashNil := rfl
  rangeNil := rfl

/-- **BOTH LEGS on a CONCRETE, NON-ROOT site** — an instance of the ∀-`d` assembly. -/
theorem deep_preservation : SatisfiabilityPreservation (r2Pass deepDesc deepSite) :=
  r2_preservation _ _ deep_certified

theorem deep_satisfiable_iff (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    (∃ x, Satisfied2 hash deepDesc minit mfin maddrs x) ↔
      (∃ y, Satisfied2 hash (collapseR2At deepDesc deepSite) minit mfin maddrs y) :=
  r2_satisfiable_iff deepDesc deepSite deep_certified hash minit mfin maddrs

/-- The SYNTACTIC recogniser of `PeepholeR2General` independently finds EXACTLY this site — a
proved equation, not a `#guard`: the certificate above is attached to the site the scan produces. -/
theorem deep_recognized : r2Sites deepDesc.constraints = [deepSite] := rfl

/-- WHAT the collapse installs in place of the eight gates: the degree-2 product of the two TESTED
columns, here the two atoms' own residuals. -/
theorem deep_pair_gate : pairColGate deepSite = gate (.mul (.loc 0) (.loc 1)) := rfl

/-! ### MUTATION CANARIES — the freshness scan is not vacuously `true`.

Move any one of the four "private" columns onto a column a SURVIVOR actually reads (`8` and `9` are
the unrelated zero-test's, `7` the and-node's left child, `10` its output) and `freshOk` REJECTS.
Proved equations, so the canary cannot rot into a passing `#guard`. -/

theorem freshOk_rejects_shared_out0 : freshOk deepDesc { deepSite with out0 := 8 } = false := rfl

theorem freshOk_rejects_shared_inv2 : freshOk deepDesc { deepSite with inv2 := 7 } = false := rfl

theorem freshOk_rejects_shared_inv0 : freshOk deepDesc { deepSite with inv0 := 10 } = false := rfl

-- Resource measurement on the certified objects (compiled `==`, no kernel `decide`).
#guard deepDesc.constraints.length == 14
#guard (collapseR2At deepDesc deepSite).constraints.length == 7

end Deep

#assert_all_clean [
  r2Drop_mem_gates,
  r2Drop_gates,
  avoids_eval_congr,
  holdsAt_of_fresh,
  rebuild_env_loc,
  rebuild_env_nxt,
  survivors_sub_target,
  r2_security,
  r2_completeness,
  r2_preservation,
  r2_satisfiable_iff,
  fresh_of_freshOk,
  orSite_wf,
  orSite_forced_survivors,
  orDesc_fresh,
  orDesc_certified,
  orDesc_preservation,
  reprA_preservation_general,
  reprB_preservation_general,
  deepDesc_constraints,
  deepSurvivors,
  deep_forced,
  deep_certified,
  deep_preservation,
  deep_satisfiable_iff,
  deep_recognized,
  deep_pair_gate,
  freshOk_rejects_shared_out0,
  freshOk_rejects_shared_inv2,
  freshOk_rejects_shared_inv0
]

end Dregg2.Circuit.PeepholeR2GeneralAssembly
