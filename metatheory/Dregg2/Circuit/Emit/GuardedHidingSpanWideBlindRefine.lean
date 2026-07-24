/-
# Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine — the refinement for
`guardedHidingSpanWideBlindDesc` (the commit-binds theorems of THE emitted hidden-span
descriptor, over the 5-lane blinding).

`GuardedHidingSpanWideBlindEmit.lean` pins the descriptor + the pure fold model (the blinding
widened from one felt, `|R| ≈ 2^31`, to 5 lanes, `|R| = p⁵ ≈ 2^154.5` — the keyed-ROM hiding bound
`Q/|R|` made meaningful; the narrow descriptor was DELETED in the felt-width cutover). This file
proves the whole-descriptor bridge over the deployed acceptance predicate `Satisfied2`, and keeps
the parse composition INTACT — the weld theorems `m0Template`/`m0_mem`/
`parse_exists_distinct_holes` are REUSED from `GuardedHidingSpanRefine` unchanged, not
re-derived.

## What is PROVEN here (grounded, no gap beyond a sound WIDE chip table)

* `guardedHidingSpanWideBlind_commit_binds` — a `Satisfied2` trace, under a sound WIDE chip table
  (`ChipTableSoundN`, the `chip_lookup_sound_N` floor), carries `span_digest8 = absorb(span lanes)`
  and `hole_commit = holeCommitWideOf absorb span_digest8 C_T (r₀..r₄)` — the published commitment
  is the genuine wide blinded image with ALL 5 blinding lanes in the preimage.
* `guardedHidingSpanWideBlind_two_openings_collide` — BINDING-as-extraction: two accepting
  openings with the SAME published `hole_commit` but DISTINCT hidden
  `(span_digest8, C_T, blinding-vector)` hand back a NAMED full-width `Coll8` collision as DATA.
  Note the widened blinding STRENGTHENS the binding statement too: distinctness in ANY of the 5
  blinding lanes (not just M0's one felt) forces the collision.
* `guardedHidingSpanWideBlind_refines_parse` — the M0 keystone over the widened blinding, welded
  to the UNTOUCHED parse theorem through the reused `m0_mem`.

## What is NOT proven (the honest scope, same as M0)

Hiding-as-ZK is not a theorem here. This file proves the RELATION and BINDING. The hiding claim
is: the keyed-ROM bound `Q/|R|` now has `|R| ≥ 2^128` (byte-pinned + `#guard`ed in the Emit), so
the CONSTRUCTION no longer voids the bound — the bound itself remains conditional on the
Poseidon2 keyed-ROM floor + fresh-uniform blinding + `HidingFriPcs`, and inherits the FRI/STARK
floor. The guard obligation `derives span guard = true` stays a plainly-named hypothesis
(`hGuard`), exactly as in M0; the DFA weld is the M1 target.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW ADDITIVE file; imports read-only
(M0's Emit/Refine and the parse stack are untouched).
-/
import Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit
import Dregg2.Circuit.Emit.GuardedHidingSpanRefine

namespace Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj)
open Dregg2.Circuit.Emit.BlindedMembershipWideEmit (wCols wVal wCols_map wStageIns wStageIns_eval wPermOut)
open Dregg2.Circuit.Emit.GuardedHidingSpanEmit (wideFoldPair piCT piHOLE piGUARD)
open Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit

set_option autoImplicit false

/-! ## §1 — constraint presence: the three lookups + the `hole_commit` pins are genuinely in the
descriptor. -/

theorem mem_spanDigestLookup : spanDigestLookup ∈ guardedHidingSpanWideBlindDesc.constraints := by
  simp only [guardedHidingSpanWideBlindDesc]; exact List.mem_cons_self

theorem mem_commitStage1Lookup :
    commitStage1Lookup ∈ guardedHidingSpanWideBlindDesc.constraints := by
  simp only [guardedHidingSpanWideBlindDesc]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem mem_commitStage2WideLookup :
    commitStage2WideLookup ∈ guardedHidingSpanWideBlindDesc.constraints := by
  simp only [guardedHidingSpanWideBlindDesc]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem mem_holePin (k : Fin 8) :
    VmConstraint2.base (.piBinding .first (gHOLE k) (piHOLE k))
      ∈ guardedHidingSpanWideBlindDesc.constraints := by
  have hin : VmConstraint2.base (.piBinding .first (gHOLE k) (piHOLE k)) ∈ holePins := by
    simp only [holePins, List.mem_map]; exact ⟨k, List.mem_finRange k, rfl⟩
  simp only [guardedHidingSpanWideBlindDesc, List.append_assoc, List.mem_append, List.mem_cons]
  tauto

/-! ## §2 — the wide chip lever, applied to each lookup of a `Satisfied2` witness. -/

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable (absorb : List ℤ → Digest8)

/-- The current-row assignment at row 0. -/
def a0 (t : VmTrace) : Assignment := (envAt t 0).loc

/-- A lookup constraint of the descriptor holds at row 0: its evaluated tuple is a chip row. -/
theorem lookup_mem_at0
    (hsat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) {ins : List EmittedExpr} {cols : List Nat}
    (hc : VmConstraint2.lookup ⟨TableId.poseidon2, chipLookupTupleN ins cols⟩
            ∈ guardedHidingSpanWideBlindDesc.constraints) :
    (chipLookupTupleN ins cols).map (·.eval (a0 t)) ∈ t.tf .poseidon2 := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hrow := hsat.rowConstraints 0 hpos _ hc
  simpa only [VmConstraint2.holdsAt, Lookup.holdsAt, a0] using hrow

/-- **The span-digest binding.** Under a sound wide chip table, `span_digest8` IS the genuine wide
Poseidon2 absorb of the hidden span lanes. -/
theorem span_digest_binds
    (hChip : ChipTableSoundN (wPermOut absorb) (t.tf .poseidon2))
    (hsat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    wVal (a0 t) gDIGEST = absorb (List.ofFn (wVal (a0 t) gSPAN)) := by
  have hmem := lookup_mem_at0 hsat hne mem_spanDigestLookup
  have hlen : spanIns.length ≤ CHIP_RATE := by
    simp [spanIns, wCols, List.length_map, List.length_finRange, CHIP_RATE]
  have h := chip_lookup_sound_N (wPermOut absorb) (t.tf .poseidon2) hChip (a0 t)
    spanIns (wCols gDIGEST) hlen hmem
  rw [wCols_map, spanIns_eval] at h
  exact List.ofFn_inj.mp h

/-- **The stage-1 fold binding.** `MID = A16(span_digest8 ‖ C_T)`. -/
theorem mid_binds
    (hChip : ChipTableSoundN (wPermOut absorb) (t.tf .poseidon2))
    (hsat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    wVal (a0 t) gMID = wideFoldPair absorb (wVal (a0 t) gDIGEST) (wVal (a0 t) gCT) := by
  have hmem := lookup_mem_at0 hsat hne mem_commitStage1Lookup
  have hlen : (wStageIns gDIGEST gCT).length ≤ CHIP_RATE := by
    simp [wStageIns, wCols, List.length_map, List.length_append, List.length_finRange, CHIP_RATE]
  have h := chip_lookup_sound_N (wPermOut absorb) (t.tf .poseidon2) hChip (a0 t)
    (wStageIns gDIGEST gCT) (wCols gMID) hlen hmem
  rw [wCols_map, wStageIns_eval] at h
  exact List.ofFn_inj.mp h

/-- **The stage-2 WIDE-BLIND tooth binding.** `hole_commit = A14(MID ‖ r₀..r₄ ‖ 0)` — all 5
blinding lanes in the preimage, every output lane bound. -/
theorem hole_binds_mid
    (hChip : ChipTableSoundN (wPermOut absorb) (t.tf .poseidon2))
    (hsat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    wVal (a0 t) gHOLE = absorb (packCommitW (wVal (a0 t) gMID) (bVal (a0 t))) := by
  have hmem := lookup_mem_at0 hsat hne mem_commitStage2WideLookup
  have hlen : commitStage2WideIns.length ≤ CHIP_RATE := by
    simp [commitStage2WideIns, bCols, wCols, List.length_map, List.length_append,
      List.length_finRange, CHIP_RATE]
  have h := chip_lookup_sound_N (wPermOut absorb) (t.tf .poseidon2) hChip (a0 t)
    commitStage2WideIns (wCols gHOLE) hlen hmem
  rw [wCols_map, commitStage2WideIns_eval] at h
  exact List.ofFn_inj.mp h

end Extract

/-! ## §3 — Part A: the published commitment IS the genuine wide-blind image. -/

/-- **`guardedHidingSpanWideBlind_commit_binds`** — the same grounded content as M0's
`guardedHidingSpan_commit_binds`, over the WIDENED blinding: a `Satisfied2` witness, under a sound
WIDE chip table, has `span_digest8 = absorb(span lanes)` and
`hole_commit = holeCommitWideOf absorb span_digest8 C_T (bVal …)`. Both 8-felt-wide; the blinding
block is the full 5-lane vector. -/
theorem guardedHidingSpanWideBlind_commit_binds
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (absorb : List ℤ → Digest8)
    (hChip : ChipTableSoundN (wPermOut absorb) (t.tf .poseidon2))
    (hsat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    wVal (a0 t) gDIGEST = absorb (List.ofFn (wVal (a0 t) gSPAN)) ∧
    wVal (a0 t) gHOLE
      = holeCommitWideOf absorb (wVal (a0 t) gDIGEST) (wVal (a0 t) gCT) (bVal (a0 t)) := by
  refine ⟨span_digest_binds absorb hChip hsat hne, ?_⟩
  have hmid := mid_binds absorb hChip hsat hne
  have hhole := hole_binds_mid absorb hChip hsat hne
  rw [hhole, hmid]
  rfl

/-! ## §4 — BINDING as extraction: two openings with equal `hole_commit`, distinct hidden data,
yield a NAMED full-8-felt collision (as DATA).

The widened blinding makes this STRONGER than M0's, not weaker: `hdistinct` ranges over the whole
`(Digest8 × Digest8 × Blind5)` triple, so a difference in ANY of the 5 blinding lanes forces the
named collision. -/

/-- **`guardedHidingSpanWideBlind_two_openings_collide`** — two `Satisfied2` witnesses over the
SAME sound wide chip table, EQUAL published `hole_commit`, DISTINCT hidden
`(span_digest8, C_T, blinding-vector)`: one of two SPECIFIC full-width `Coll8 absorb` collisions —
on the arity-14 stage-2 preimage or the arity-16 stage-1 preimage — handed back as DATA. -/
theorem guardedHidingSpanWideBlind_two_openings_collide
    {hash₁ hash₂ : List ℤ → ℤ} {minit₁ minit₂ : ℤ → ℤ} {mfin₁ mfin₂ : ℤ → ℤ × Nat}
    {maddrs₁ maddrs₂ : List ℤ} {t₁ t₂ : VmTrace}
    (absorb : List ℤ → Digest8)
    (hChip₁ : ChipTableSoundN (wPermOut absorb) (t₁.tf .poseidon2))
    (hChip₂ : ChipTableSoundN (wPermOut absorb) (t₂.tf .poseidon2))
    (hsat₁ : Satisfied2 hash₁ guardedHidingSpanWideBlindDesc minit₁ mfin₁ maddrs₁ t₁)
    (hne₁ : t₁.rows ≠ [])
    (hsat₂ : Satisfied2 hash₂ guardedHidingSpanWideBlindDesc minit₂ mfin₂ maddrs₂ t₂)
    (hne₂ : t₂.rows ≠ [])
    (hcommit : wVal (a0 t₁) gHOLE = wVal (a0 t₂) gHOLE)
    (hdistinct : (wVal (a0 t₁) gDIGEST, wVal (a0 t₁) gCT, bVal (a0 t₁))
                   ≠ (wVal (a0 t₂) gDIGEST, wVal (a0 t₂) gCT, bVal (a0 t₂))) :
    Coll8 absorb
        (packCommitW (wideFoldPair absorb (wVal (a0 t₁) gDIGEST) (wVal (a0 t₁) gCT)) (bVal (a0 t₁)),
         packCommitW (wideFoldPair absorb (wVal (a0 t₂) gDIGEST) (wVal (a0 t₂) gCT)) (bVal (a0 t₂)))
    ∨ Coll8 absorb (pack8 (wVal (a0 t₁) gDIGEST) (wVal (a0 t₁) gCT),
                    pack8 (wVal (a0 t₂) gDIGEST) (wVal (a0 t₂) gCT)) := by
  have hb₁ := (guardedHidingSpanWideBlind_commit_binds absorb hChip₁ hsat₁ hne₁).2
  have hb₂ := (guardedHidingSpanWideBlind_commit_binds absorb hChip₂ hsat₂ hne₂).2
  set mid₁ := wideFoldPair absorb (wVal (a0 t₁) gDIGEST) (wVal (a0 t₁) gCT) with hmid₁
  set mid₂ := wideFoldPair absorb (wVal (a0 t₂) gDIGEST) (wVal (a0 t₂) gCT) with hmid₂
  set r₁ := bVal (a0 t₁)
  set r₂ := bVal (a0 t₂)
  have himg : absorb (packCommitW mid₁ r₁) = absorb (packCommitW mid₂ r₂) := by
    have := hb₁.symm.trans (hcommit.trans hb₂)
    simpa only [holeCommitWideOf, hmid₁, hmid₂] using this
  by_cases hpc : packCommitW mid₁ r₁ = packCommitW mid₂ r₂
  · obtain ⟨hmideq, hreq⟩ := packCommitW_inj hpc
    have himg1 : absorb (pack8 (wVal (a0 t₁) gDIGEST) (wVal (a0 t₁) gCT))
        = absorb (pack8 (wVal (a0 t₂) gDIGEST) (wVal (a0 t₂) gCT)) := by
      simpa only [wideFoldPair, hmid₁, hmid₂] using hmideq
    by_cases hp8 : pack8 (wVal (a0 t₁) gDIGEST) (wVal (a0 t₁) gCT)
        = pack8 (wVal (a0 t₂) gDIGEST) (wVal (a0 t₂) gCT)
    · obtain ⟨hd, hct⟩ := pack8_inj hp8
      exact absurd (by rw [hd, hct, hreq]) hdistinct
    · exact Or.inr ⟨hp8, himg1⟩
  · exact Or.inl ⟨hpc, himg⟩

/-! ## §5 — the WELD to the untouched parse theorem: the parse composition is REUSED, not
re-derived. `m0Template`/`m0_holes_nodup`/`m0_mem` come from `GuardedHidingSpanRefine` verbatim —
hiding (of either blinding width) lives strictly BELOW `mem_language_iff_spans`. -/

open Dregg2.Exec (Value)
open Dregg2.Crypto.Deriv (PredRE)
open Dregg2.Crypto.Deriv.PredRE (derives)
open Dregg2.Crypto.HandlebarsGuarded (GuardedTemplate guardedToGrammar render guardedSafe dataVal)
open Dregg2.Crypto.HandlebarsGuardedUniqueness (noBraceRE)
open Dregg2.Crypto.HandlebarsGuardedParse (parse_exists_distinct_holes)
open Dregg2.Circuit.Emit.GuardedHidingSpanRefine (m0Template m0_holes_nodup m0_mem)

/-- **`guardedHidingSpanWideBlind_refines_parse`** — the M0 keystone over the WIDENED blinding: a
`Satisfied2` witness (sound wide chip table) has its published `hole_commit` the genuine wide-blind
image of the hidden span digest under `C_T` (Part A); given the guard obligation `hGuard`, the
untouched parse theorem fires on the recovered span through the REUSED `m0_mem`. -/
theorem guardedHidingSpanWideBlind_refines_parse
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (absorb : List ℤ → Digest8)
    (hChip : ChipTableSoundN (wPermOut absorb) (t.tf .poseidon2))
    (hsat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (lit0 lit1 s : List Value) (g : PredRE) (hGuard : derives s g = true) :
    (wVal (a0 t) gHOLE
        = holeCommitWideOf absorb (wVal (a0 t) gDIGEST) (wVal (a0 t) gCT) (bVal (a0 t))
      ∧ wVal (a0 t) gDIGEST = absorb (List.ofFn (wVal (a0 t) gSPAN))) ∧
    (∃ d : Nat → List Value, guardedSafe (m0Template lit0 lit1 g) d
        ∧ render (m0Template lit0 lit1 g) d = lit0 ++ s ++ lit1) := by
  have hbind := guardedHidingSpanWideBlind_commit_binds absorb hChip hsat hne
  refine ⟨⟨hbind.2, hbind.1⟩, ?_⟩
  exact parse_exists_distinct_holes (m0Template lit0 lit1 g) (m0_holes_nodup lit0 lit1 g)
    (lit0 ++ s ++ lit1) (m0_mem lit0 lit1 s g hGuard)

/-! ## §6 — NON-VACUITY: a concrete satisfying witness, the refinement FIRING, and the tamper
canaries — including a canary on the LAST blinding lane, showing the widened lanes are
load-bearing in the CONSTRAINTS, not dead padding. -/

open Dregg2.Circuit.Emit.GuardedHidingSpanRefine (hash0 wZeroAbsorb wRow)

/-- The three chip rows the witness's lookups evaluate to. -/
def spanRowW : List ℤ := (chipLookupTupleN spanIns (wCols gDIGEST)).map (·.eval wRow)
def stage1RowW : List ℤ :=
  (chipLookupTupleN (wStageIns gDIGEST gCT) (wCols gMID)).map (·.eval wRow)
def stage2RowW : List ℤ :=
  (chipLookupTupleN commitStage2WideIns (wCols gHOLE)).map (·.eval wRow)

/-- The witness chip table: exactly the three evaluated chip rows on `poseidon2`. -/
def wTfW : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [spanRowW, stage1RowW, stage2RowW]
  | _ => []

/-- The single-row witness trace, all public inputs `0`. -/
def witTraceW : VmTrace := { rows := [wRow], pub := fun _ => 0, tf := wTfW }

theorem memOpsOf_ghsw : memOpsOf guardedHidingSpanWideBlindDesc = [] := by decide
theorem mapOpsOf_ghsw : mapOpsOf guardedHidingSpanWideBlindDesc = [] := by decide
theorem memLog_ghsw (t : VmTrace) : memLog guardedHidingSpanWideBlindDesc t = [] := by
  simp [memLog, memOpsOf_ghsw]
theorem mapLog_ghsw (t : VmTrace) : mapLog guardedHidingSpanWideBlindDesc t = [] := by
  simp [mapLog, mapOpsOf_ghsw]

/-- **The witness PROVABLY satisfies the emitted descriptor** (the "true half" of non-vacuity). -/
theorem witTraceW_satisfies :
    Satisfied2 hash0 guardedHidingSpanWideBlindDesc (fun _ => 0) (fun _ => (0, 0)) [] witTraceW where
  rowConstraints := by
    intro i hi c hc
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [witTraceW] using hi
      omega
    subst hi0
    have hfst : ((0 : Nat) == 0) = true := rfl
    have hlst : ((0 : Nat) + 1 == witTraceW.rows.length) = true := rfl
    rw [hfst, hlst]
    simp only [guardedHidingSpanWideBlindDesc, ctPins, holePins, guardPins, List.append_assoc,
      List.mem_append, List.mem_cons, List.mem_map, List.mem_finRange, List.not_mem_nil,
      or_false, true_and, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact (holdsVm_piFirst_true (envAt witTraceW 0) true (gCT k) (piCT k)).mpr rfl
    · exact (holdsVm_piFirst_true (envAt witTraceW 0) true (gHOLE k) (piHOLE k)).mpr rfl
    · exact (holdsVm_piFirst_true (envAt witTraceW 0) true (gGUARD k) (piGUARD k)).mpr rfl
  rowHashes := by intro i _; trivial
  rowRanges := by
    intro i _ r hr
    simp only [guardedHidingSpanWideBlindDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_ghsw]; simp
  memDisciplined := by rw [memLog_ghsw]; trivial
  memBalanced := by rw [memLog_ghsw]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_ghsw]; rfl
  mapTableFaithful := by rw [mapLog_ghsw]; rfl

/-- **The witness chip table is a SOUND WIDE chip table** for `wZeroAbsorb` — the fold soundness
floor is inhabited, not a vacuous guard. -/
theorem witTfW_chip_sound : ChipTableSoundN (wPermOut wZeroAbsorb) (witTraceW.tf .poseidon2) := by
  intro r hr
  simp only [witTraceW, wTfW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨spanIns.map (·.eval wRow), by decide, by decide⟩
  · exact ⟨(wStageIns gDIGEST gCT).map (·.eval wRow), by decide, by decide⟩
  · exact ⟨commitStage2WideIns.map (·.eval wRow), by decide, by decide⟩

/-- **The refinement FIRES on the witness**: `hole_commit` IS
`holeCommitWideOf wZeroAbsorb span_digest8 C_T (blinding vector)`. -/
theorem witness_commit_binds :
    wVal (a0 witTraceW) gDIGEST = wZeroAbsorb (List.ofFn (wVal (a0 witTraceW) gSPAN)) ∧
    wVal (a0 witTraceW) gHOLE
      = holeCommitWideOf wZeroAbsorb (wVal (a0 witTraceW) gDIGEST) (wVal (a0 witTraceW) gCT)
          (bVal (a0 witTraceW)) :=
  guardedHidingSpanWideBlind_commit_binds wZeroAbsorb witTfW_chip_sound witTraceW_satisfies
    (by decide)

/-! ### §6.1 — TAMPER CANARY 1: a forged `hole_commit` public input is REFUSED. -/

/-- The witness with a FORGED published `hole_commit` (PI[8] flipped to `1`). -/
def mutHoleTrace : VmTrace :=
  { rows := [wRow], pub := fun i => if i = piHOLE 0 then 1 else 0, tf := wTfW }

/-- **A forged `hole_commit` PROVABLY fails `Satisfied2`.** -/
theorem mutHole_not_satisfied :
    ¬ Satisfied2 hash0 guardedHidingSpanWideBlindDesc (fun _ => 0) (fun _ => (0, 0)) []
        mutHoleTrace := by
  intro h
  have hpin := h.rowConstraints 0 (by decide) _ (mem_holePin 0)
  simp only [VmConstraint2.holdsAt] at hpin
  have hmod := (holdsVm_piFirst_true (envAt mutHoleTrace 0)
      (0 + 1 == mutHoleTrace.rows.length) (gHOLE 0) (piHOLE 0)).mp hpin
  have he : (envAt mutHoleTrace 0).loc (gHOLE 0) = 0 := rfl
  have hp : (envAt mutHoleTrace 0).pub (piHOLE 0) = 1 := rfl
  rw [he, hp] at hmod
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hmod.symm
  omega

/-! ### §6.2 — TAMPER CANARY 2: a wrong FIRST blinding lane is REFUSED. -/

/-- The witness row with a wrong first blinding lane (`gBLIND 0 := 1`), chip table UNCHANGED. -/
def mutBlind0Row : Assignment := fun i => if i = gBLIND 0 then 1 else 0
def mutBlind0Trace : VmTrace := { rows := [mutBlind0Row], pub := fun _ => 0, tf := wTfW }

/-- **A wrong first blinding lane PROVABLY fails `Satisfied2`** — the wide-blind tooth reads a
preimage the sound table does not carry. -/
theorem mutBlind0_not_satisfied :
    ¬ Satisfied2 hash0 guardedHidingSpanWideBlindDesc (fun _ => 0) (fun _ => (0, 0)) []
        mutBlind0Trace := by
  intro h
  have hrow := h.rowConstraints 0 (by decide) _ mem_commitStage2WideLookup
  have hmem : (chipLookupTupleN commitStage2WideIns (wCols gHOLE)).map
      (·.eval (envAt mutBlind0Trace 0).loc) ∈ mutBlind0Trace.tf .poseidon2 := by
    simpa only [VmConstraint2.holdsAt, Lookup.holdsAt, commitStage2WideLookup] using hrow
  revert hmem
  decide

/-! ### §6.3 — TAMPER CANARY 3 (the WIDENING's own canary): a wrong LAST blinding lane is
REFUSED. M0 has no analog — this lane does not exist there. It shows the four NEW lanes are
load-bearing in the constraint system: the commitment cannot be re-opened under a blinding vector
differing in ANY lane, so the full `p⁵` space genuinely enters the preimage. -/

/-- The witness row with a wrong LAST blinding lane (`gBLIND 4 := 1`), chip table UNCHANGED. -/
def mutBlind4Row : Assignment := fun i => if i = gBLIND 4 then 1 else 0
def mutBlind4Trace : VmTrace := { rows := [mutBlind4Row], pub := fun _ => 0, tf := wTfW }

/-- **A wrong LAST blinding lane PROVABLY fails `Satisfied2`.** -/
theorem mutBlind4_not_satisfied :
    ¬ Satisfied2 hash0 guardedHidingSpanWideBlindDesc (fun _ => 0) (fun _ => (0, 0)) []
        mutBlind4Trace := by
  intro h
  have hrow := h.rowConstraints 0 (by decide) _ mem_commitStage2WideLookup
  have hmem : (chipLookupTupleN commitStage2WideIns (wCols gHOLE)).map
      (·.eval (envAt mutBlind4Trace 0).loc) ∈ mutBlind4Trace.tf .poseidon2 := by
    simpa only [VmConstraint2.holdsAt, Lookup.holdsAt, commitStage2WideLookup] using hrow
  revert hmem
  decide

/-! ### §6.4 — the parse weld FIRES concretely through the wide-blind keystone (the reused
`Demo` span + guard discharge, on the wide-blind witness trace). -/

open Dregg2.Circuit.Emit.GuardedHidingSpanRefine.Demo in
/-- The full keystone instantiated concretely: the wide-blind witness trace + the reused Demo
span (`s = [dataVal]`, guard discharged by the verified matcher). The parse composition is intact
end-to-end over the widened blinding. -/
theorem witness_refines_parse :
    (wVal (a0 witTraceW) gHOLE
        = holeCommitWideOf wZeroAbsorb (wVal (a0 witTraceW) gDIGEST) (wVal (a0 witTraceW) gCT)
            (bVal (a0 witTraceW))
      ∧ wVal (a0 witTraceW) gDIGEST = wZeroAbsorb (List.ofFn (wVal (a0 witTraceW) gSPAN))) ∧
    (∃ d : Nat → List Value, guardedSafe (m0Template [dataVal] [dataVal] noBraceRE) d
        ∧ render (m0Template [dataVal] [dataVal] noBraceRE) d = [dataVal] ++ s ++ [dataVal]) :=
  guardedHidingSpanWideBlind_refines_parse wZeroAbsorb witTfW_chip_sound witTraceW_satisfies
    (by decide) [dataVal] [dataVal] s noBraceRE s_guard

/-! ## §7 — axiom tripwires (the keystones + the witness + all canaries). -/

#assert_axioms guardedHidingSpanWideBlind_commit_binds
#assert_axioms guardedHidingSpanWideBlind_two_openings_collide
#assert_axioms guardedHidingSpanWideBlind_refines_parse
#assert_axioms witTraceW_satisfies
#assert_axioms witTfW_chip_sound
#assert_axioms witness_commit_binds
#assert_axioms mutHole_not_satisfied
#assert_axioms mutBlind0_not_satisfied
#assert_axioms mutBlind4_not_satisfied
#assert_axioms witness_refines_parse

end Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine
