/-
# Dregg2.Circuit.Emit.GarbledEvalRung2 — the RUNG-2 discharge of the FREE-`hash_out` residual for the
emitted garbled-evaluation descriptor (`garbledEvalDesc`), via the Poseidon2 garbling-hash binding.

## What this file IS

`GarbledEvalRefine.lean` (RUNG 1) proves the whole-descriptor bridge `Satisfied2 ⟹ GarbledEvalRun`,
whose decryption leg (`GateDecrypts`) concludes, per active non-padding row and per output lane `j`,

    output(j) = table_entry(j) − hash_out(j)          (the Yao one-time-pad decryption ALGEBRA).

That is a relation between THREE trace columns — and, crucially, `hash_out` is a FREE WITNESS: the
emitted 56-column descriptor declares NO chip lookup / hash site binding the digest columns
(`hashSites = []`, `tables = []`; see the `GarbledEvalEmit` header, "the columns `hash_out(i)` are
FREE witnesses … computed ENTIRELY in Rust witness-gen, NOT in-circuit"). So `Satisfied2` alone does
NOT force `output` to be the honest decryption: a forger picks ANY `output(j)` and sets
`hash_out(j) := table_entry(j) − output(j)`, and the decryption gate `output − table + hash_out = 0`
still holds. RUNG 1's `GarbledEvalRun` is therefore NOT yet output-label non-forgeability — a genuine
crypto residual remains: the free `hash_out` columns.

RUNG 2 DISCHARGES that residual. The NAMED carrier is `GarblingHashBound gh t` — the executor-verified
Poseidon2 garbling-hash binding (the `GarbledEvalEmit` header's "NAMED, EXECUTOR-VERIFIED CARRIER"):
on each active non-padding row, the digest columns ARE the genuine wide-hash of the gate's input
labels, `hash_out(j) = gh [left‖right‖gate_index] j`. Under it, the free witness is pinned and the
decryption gate collapses to the GENUINE one-time-pad decryption

    output(j) = table_entry(j) − gh [left‖right‖gate_index] j  =  HonestOutput gh (row) j,

the UNIQUE output label a genuine evaluator recovers — no forged output can be exposed
(`garbled_rung2_no_output_forgery`, the field congruence; `garbled_rung2_output_unique`, the unique
canonical representative over ℤ under the range-check envelope `GarbledTraceCanon`). This mirrors
the DFA `Rung 2` posture: there the deployed chip-AIR
supplies `ChipTableSound` and the running-hash binding discharges the terminal-step residual; here the
deployed garbler + verifier-wrapper supplies `GarblingHashBound` (Poseidon2 preimage/collision
resistance is what makes it sound — forging `hash_out` to a chosen value is a Poseidon2 preimage
attack), and it discharges the free-`hash_out` residual. The carrier rides as a NAMED hypothesis,
never a Lean axiom, and `gh` (the genuine garbling hash) is a parameter — the theorem holds for the
real Poseidon2 wide-hash.

## Scope (honest residual)

This discharges OUTPUT-LABEL forgery — the per-gate decryption soundness that the descriptor's
decryption gate is meant to carry. The complementary COMMITMENT-binding dimension (the full 8-felt
`circuit_commitment` / `output_label_hash` = Poseidon2(tables) / Poseidon2(output labels), of which the
descriptor pins only the first 4 felts in-circuit and the rest is the verifier-side struct equality in
`verify_garbled_evaluation_dsl`) rides the SAME Poseidon2 CR carrier off-descriptor by design — it is
NAMED in `GarbledEvalEmit` (the "VERIFIER-WRAPPER TOOTH"), not re-mechanized here.

## Non-vacuity (the anti-scar witnesses, all IN THIS FILE)

* `garbled_honest_fires` — the RUNG-2 conclusion FIRES on the concrete honest trace `t₀` (RUNG 1's own
  satisfying witness) under the genuine carrier `garbled_honest_hashBound`: its exposed `output(0)` is
  the genuine honest decryption `HonestOutput (…) 0 = 0`. So the hypothesis set is jointly satisfiable
  and the conclusion is achievably true (not vacuous).
* `garbled_satisfied2_alone_insufficient` — the LOAD-BEARING-ANCHOR proof. The SAME `t₀` (provably
  `Satisfied2`) FAILS the no-forgery conclusion once the genuine garbling hash is a DIFFERENT one
  (`gh = fun _ _ => 1`): `t₀` exposes `output(0) = 0` but the honest decryption is `0 − 1 = −1`. So a
  hypothetical `Satisfied2 ⟹ output = HonestOutput` (WITHOUT the carrier) is refuted — the anchor is
  genuinely load-bearing, this is not a `P → P` / unsatisfiable-hypothesis theorem.
* `garbled_cheat_not_hashBound` — the carrier is a REAL filter, not `True`: `t₀` `Satisfied2`s yet
  VIOLATES `GarblingHashBound (fun _ _ => 1)` (its `hash_out = 0 ≠ 1`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} (Classical enters only through RUNG 1's
`satisfied2_implies_garbledEvalRun`). The garbling-hash carrier `GarblingHashBound` rides as a NAMED
hypothesis; `gh` is a parameter — never a Lean axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.GarbledEvalRefine

namespace Dregg2.Circuit.Emit.GarbledEvalRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (Satisfied2 VmTrace envAt)
open Dregg2.Circuit.Emit.GarbledEvalEmit
open Dregg2.Circuit.Emit.GarbledEvalRefine
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eqToModEq)

set_option autoImplicit false

/-! ## §1 — The garbling-hash carrier + the genuine one-time-pad decryption. -/

/-- **`GateInputs a`** — the gate's input labels, the preimage the garbling hash absorbs:
`left(0..8) ‖ right(0..8) ‖ gate_index` (17 felts). The genuine Poseidon2 wide-hash of THIS list is
the row's `hash_out` digest (computed in `circuit/src/garbled.rs` witness-gen). -/
def GateInputs (a : Assignment) : List ℤ :=
  (List.range 8).map (fun j => a (LEFT j))
    ++ (List.range 8).map (fun j => a (RIGHT j))
    ++ [a GATE_INDEX]

/-- **`HonestOutput gh a j`** — the genuine one-time-pad decryption of output lane `j`: the committed
garbled-table entry minus the genuine garbling-hash digest of the gate's inputs
(`table_entry(j) − gh [inputs] j`). The UNIQUE label a faithful evaluator recovers. -/
def HonestOutput (gh : List ℤ → Nat → ℤ) (a : Assignment) (j : Nat) : ℤ :=
  a (TABLE_ENTRY j) - gh (GateInputs a) j

/-- **`GarblingHashBound gh t` — THE NAMED CARRIER.** The executor-verified Poseidon2 garbling-hash
binding: on every ACTIVE (non-last), NON-PADDING row, each digest lane is the genuine wide-hash of the
gate's input labels, `hash_out(j) = gh [left‖right‖gate_index] j`. This is the off-descriptor binding
(`GarbledEvalEmit`'s "NAMED, EXECUTOR-VERIFIED CARRIER"): the AIR proves the decryption algebra over
`hash_out`; that `hash_out` IS the genuine Poseidon2 digest is supplied by the garbler + verifier and
underwritten by Poseidon2 preimage/collision resistance. NEVER a Lean axiom — a hypothesis on `t`. -/
def GarblingHashBound (gh : List ℤ → Nat → ℤ) (t : VmTrace) : Prop :=
  ∀ i, i + 1 < t.rows.length → (envAt t i).loc IS_PADDING = 0 →
    ∀ j, j < 8 → (envAt t i).loc (HASH_OUT j) = gh (GateInputs (envAt t i).loc) j

/-! ## §2 — THE RUNG-2 DISCHARGE (no output-label forgery). -/

/-- **`garbled_rung2_no_output_forgery` — THE DISCHARGE.** A trace `t` that `Satisfied2`s the emitted
garbled-evaluation descriptor and rides the NAMED garbling-hash carrier `GarblingHashBound gh` exposes,
on every active non-padding row and output lane `j`, EXACTLY the genuine one-time-pad decryption
`HonestOutput gh (row) j = table_entry(j) − gh [inputs] j` — as the field congruence
`output(j) ≡ HonestOutput gh (row) j [ZMOD p]` (honestly so: `HonestOutput` is an ℤ subtraction that
can be negative, and the deployed pad is the FIELD subtraction). The free-`hash_out` residual RUNG 1
left is discharged; combined with the exposed label's canonicality, the label is the UNIQUE one a
faithful evaluator recovers (`garbled_rung2_output_unique`). -/
theorem garbled_rung2_no_output_forgery
    (gh : List ℤ → Nat → ℤ)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hcanon : GarbledTraceCanon t)
    (hsat : Satisfied2 hash garbledEvalDesc minit mfin maddrs t)
    (hgh : GarblingHashBound gh t) :
    ∀ i, i + 1 < t.rows.length → (envAt t i).loc IS_PADDING = 0 →
      ∀ j, j < 8 →
        (envAt t i).loc (OUTPUT j) ≡ HonestOutput gh (envAt t i).loc j [ZMOD 2013265921] := by
  intro i hact hnp j hj
  have hrun := satisfied2_implies_garbledEvalRun hash minit mfin maddrs t hcanon hsat
  rcases hrun.decrypts i hact with hpad | heq
  · rw [hnp] at hpad; exact absurd hpad (by decide)
  · have h2 := hgh i hact hnp j hj
    show (envAt t i).loc (OUTPUT j)
        ≡ (envAt t i).loc (TABLE_ENTRY j) - gh (GateInputs (envAt t i).loc) j [ZMOD 2013265921]
    rw [← h2]; exact heq j hj

/-- **`garbled_rung2_output_unique` — the no-forgery CROWN over ℤ.** Under the same hypotheses, the
exposed output label is the UNIQUE canonical field element congruent to the genuine one-time-pad
decryption: any candidate label `y` that is canonical and decrypts correctly mod `p` IS the exposed
one. A forger cannot expose a different label — the range-checked representative of
`HonestOutput gh (row) j` is pinned exactly. -/
theorem garbled_rung2_output_unique
    (gh : List ℤ → Nat → ℤ)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hcanon : GarbledTraceCanon t)
    (hsat : Satisfied2 hash garbledEvalDesc minit mfin maddrs t)
    (hgh : GarblingHashBound gh t) :
    ∀ i, i + 1 < t.rows.length → (envAt t i).loc IS_PADDING = 0 →
      ∀ j, j < 8 → ∀ y : ℤ, CanonCell y →
        y ≡ HonestOutput gh (envAt t i).loc j [ZMOD 2013265921] →
        (envAt t i).loc (OUTPUT j) = y := by
  intro i hact hnp j hj y hy hyc
  exact eq_of_modEq_of_canon
    ((garbled_rung2_no_output_forgery gh hash minit mfin maddrs t hcanon hsat hgh
        i hact hnp j hj).trans hyc.symm)
    (hcanon.output i (by omega) j hj) hy

#assert_axioms garbled_rung2_no_output_forgery
#assert_axioms garbled_rung2_output_unique

/-! ## §3 — Non-vacuity, TRUE half: the discharge FIRES on RUNG 1's honest witness `t₀`. -/

/-- The honest trace's digit columns are `0` on the active row, so they equal the genuine garbling
hash `gh = fun _ _ => 0` — the carrier holds. -/
theorem garbled_honest_hashBound : GarblingHashBound (fun _ _ => (0 : ℤ)) t₀ := by
  intro i hact _ j hj
  have hi0 : i = 0 := by
    have h2 : i + 1 < 2 := by rw [show t₀.rows.length = 2 from rfl] at hact; exact hact
    omega
  subst hi0
  rw [envAt0_loc]
  exact honestRow0_hash j hj

/-- **The RUNG-2 discharge FIRES on the genuine witness (the TRUE half).** Feeding the concrete honest
trace `t₀` (RUNG 1's own `garbled_honest_satisfied2`) and the carrier `garbled_honest_hashBound` to the
discharge recovers the genuine decryption on lane 0: the exposed `output(0)` is `0`, and it EQUALS the
honest decryption `HonestOutput (fun _ _ => 0) 0`. The hypothesis set is jointly satisfiable and the
conclusion is achievably true — not vacuous. -/
theorem garbled_honest_fires :
    (envAt t₀ 0).loc (OUTPUT 0) = 0 ∧
    (envAt t₀ 0).loc (OUTPUT 0) = HonestOutput (fun _ _ => (0 : ℤ)) (envAt t₀ 0).loc 0 := by
  have h1 : (envAt t₀ 0).loc (OUTPUT 0) = 0 := by
    rw [envAt0_loc]; exact honestRow0_output 0 (by decide)
  have h2 : HonestOutput (fun _ _ => (0 : ℤ)) (envAt t₀ 0).loc 0 = 0 := by
    show (envAt t₀ 0).loc (TABLE_ENTRY 0) - 0 = 0
    rw [envAt0_loc, honestRow0_table 0 (by decide)]; ring
  have hcong := garbled_rung2_no_output_forgery (fun _ _ => (0 : ℤ)) (fun _ => 0) (fun _ => 0)
    (fun _ => (0, 0)) [] t₀ t₀_canon (garbled_honest_satisfied2 (fun _ => 0))
    garbled_honest_hashBound
    0 (by rw [show t₀.rows.length = 2 from rfl]; decide)
    (by rw [envAt0_loc]; exact honestRow0_padding) 0 (by decide)
  -- collapse the fired congruence with both sides canonical (they are both the small value 0)
  refine ⟨h1, eq_of_modEq_of_canon hcong ?_ ?_⟩
  · rw [h1]; exact ⟨by norm_num, by norm_num⟩
  · rw [h2]; exact ⟨by norm_num, by norm_num⟩

/-! ## §4 — Non-vacuity, FALSE half: the carrier is LOAD-BEARING (and a real filter). -/

/-- **The carrier is a REAL filter, not `True`.** The honest trace `t₀` `Satisfied2`s yet VIOLATES
`GarblingHashBound (fun _ _ => 1)`: its `hash_out(0) = 0 ≠ 1`. So the carrier genuinely bites. -/
theorem garbled_cheat_not_hashBound : ¬ GarblingHashBound (fun _ _ => (1 : ℤ)) t₀ := by
  intro h
  have h0 := h 0 (by rw [show t₀.rows.length = 2 from rfl]; decide)
    (by rw [envAt0_loc]; exact honestRow0_padding) 0 (by decide)
  rw [envAt0_loc, honestRow0_hash 0 (by decide)] at h0
  change (0 : ℤ) = 1 at h0
  exact absurd h0 (by decide)

/-- **`garbled_satisfied2_alone_insufficient` — THE LOAD-BEARING-ANCHOR PROOF.** `Satisfied2` ALONE
cannot force the no-forgery conclusion: the SAME honest trace `t₀` is provably `Satisfied2`, yet under
a DIFFERENT genuine garbling hash (`gh = fun _ _ => 1`) it does NOT satisfy the conclusion — it exposes
`output(0) = 0` while the honest decryption is `table_entry(0) − 1 = −1`. So a hypothetical
`Satisfied2 ⟹ output ≡ HonestOutput [ZMOD p]` (dropping the carrier) is REFUTED — `0 ≢ −1 [ZMOD p]`
(`p ∤ 1`): `GarblingHashBound` is genuinely load-bearing, and the RUNG-2 theorem is not a `P → P` /
unsatisfiable-hypothesis vacuity. -/
theorem garbled_satisfied2_alone_insufficient :
    Satisfied2 (fun _ => 0) garbledEvalDesc (fun _ => 0) (fun _ => (0, 0)) [] t₀ ∧
    ¬ (∀ i, i + 1 < t₀.rows.length → (envAt t₀ i).loc IS_PADDING = 0 →
        ∀ j, j < 8 →
          (envAt t₀ i).loc (OUTPUT j)
            ≡ HonestOutput (fun _ _ => (1 : ℤ)) (envAt t₀ i).loc j [ZMOD 2013265921]) := by
  refine ⟨garbled_honest_satisfied2 (fun _ => 0), fun hconc => ?_⟩
  have h0 := hconc 0 (by rw [show t₀.rows.length = 2 from rfl]; decide)
    (by rw [envAt0_loc]; exact honestRow0_padding) 0 (by decide)
  rw [envAt0_loc, honestRow0_output 0 (by decide)] at h0
  have hval : HonestOutput (fun _ _ => (1 : ℤ)) honestRow0 0 = -1 := by
    show honestRow0 (TABLE_ENTRY 0) - 1 = -1
    rw [honestRow0_table 0 (by decide)]; decide
  rw [hval] at h0
  -- h0 : 0 ≡ −1 [ZMOD p], i.e. p ∣ −1 — impossible.
  obtain ⟨k, hk⟩ := h0.dvd
  omega

#assert_axioms garbled_honest_hashBound
#assert_axioms garbled_honest_fires
#assert_axioms garbled_cheat_not_hashBound
#assert_axioms garbled_satisfied2_alone_insufficient

/-! ## §5 — THE GATE: the last-row `.gate` vacuity WAS a real output-forgery hole; the emit-fix
(`garbledLastRowFix`) closes it, and this is the REGRESSION that proves it.

The audit found the decryption relation emitted as `.base (.gate (decBody i))` — a `when_transition`
constraint, VACUOUS on the last row (`holdsVm … isLast=true (.gate _) = True`,
`EffectVmEmit.lean:465`); on a HEIGHT-1 trace the only row IS last, so decryption went entirely
unchecked. The deployed DSL binds decryption on EVERY row (the `InvertedGated`/`Polynomial` inner ⇒
`is_transition = false` ⇒ `builder.assert_zero`, `dsl_plonky3.rs:168`), so the Lean emit was strictly
WEAKER than the deployed AIR — a genuine regression. `tForge` below is a single, otherwise-well-formed
garbled-gate row whose exposed `output(0) = 5` is NOT the one-time-pad decryption
`table_entry(0) − hash_out(0) = 0`. Under the fix-less CORE (`garbledEvalDescCore`) it is ACCEPTED;
the landed `garbledLastRowFix` — the `.base (.boundary VmRow.last (decBody 0))` counterpart — is
EXACTLY what turns that acceptance into a rejection. -/

open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 memLog mapLog memOpsOf mapOpsOf memCheck_nil)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)

/-- The forged row: an otherwise well-formed AND gate (`is_and = 1`, non-padding, commitment /
output-hash / all lanes bound to the all-zero public input) whose exposed `output(0) = 5` VIOLATES the
Yao decryption `output(0) = table_entry(0) − hash_out(0) = 0`. -/
private def forgeRow : Assignment := fun c =>
  if c = OUTPUT 0 then 5 else if c = IS_AND then 1 else 0

private def forgePub : Assignment := fun _ => 0

/-- A HEIGHT-1 trace: its single row is BOTH the first row (the PI pins / `gate_index_delta` boundary
FIRE) AND the last row (the transition `.gate`s are vacuous — under the CORE the forge's decryption
goes unchecked). -/
private def tForge : VmTrace := { rows := [forgeRow], pub := forgePub, tf := fun _ => [] }

/-- **`garbledEvalDescCore`** — the emitted descriptor WITHOUT the last-row fix (the transition-only
`garbledCoreConstraints`). This is what the emit produced BEFORE `garbledLastRowFix`; it is the
descriptor the forged trace exploits. -/
def garbledEvalDescCore : EffectVmDescriptor2 :=
  { garbledEvalDesc with constraints := garbledCoreConstraints }

theorem forgeRow_commit (j : Nat) (hj : j < 4) :
    forgeRow (CIRCUIT_COMMITMENT + j) = forgePub j := by interval_cases j <;> decide
theorem forgeRow_ohash (j : Nat) (hj : j < 4) :
    forgeRow (OUTPUT_LABEL_HASH + j) = forgePub (4 + j) := by interval_cases j <;> decide

theorem coreForge_memLog_nil : memLog garbledEvalDescCore tForge = [] := by
  simp [memLog, memOpsOf, garbledEvalDescCore, garbledCoreConstraints, commitmentPins,
    outputHashPins, decryptionGates, selectorBinaryGates, chainingGates, gateIndexDeltaBoundary,
    List.filterMap_append, List.filterMap_map]
theorem coreForge_mapLog_nil : mapLog garbledEvalDescCore tForge = [] := by
  simp [mapLog, mapOpsOf, garbledEvalDescCore, garbledCoreConstraints, commitmentPins,
    outputHashPins, decryptionGates, selectorBinaryGates, chainingGates, gateIndexDeltaBoundary,
    List.filterMap_append, List.filterMap_map]

/-- **The forged trace PROVABLY `Satisfied2`s the fix-less CORE descriptor.** On the height-1 trace the
transition `.gate`s (decryption / selectors / exclusivity) and the wire-chaining window are vacuous, so
the forged `output(0) = 5` is UNCHECKED; only the first-row PI pins and `gate_index_delta` boundary
fire, and the forge satisfies those. This is the forgery the deployed every-row `assert_zero` lowering
— now mirrored by `garbledLastRowFix` — closes. -/
theorem garbled_forge_was_satisfied2_core :
    Satisfied2 (fun _ => 0) garbledEvalDescCore (fun _ => 0) (fun _ => (0, 0)) [] tForge := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · intro i hi
    rw [show tForge.rows.length = 1 from rfl] at hi
    interval_cases i
    simp only [garbledEvalDescCore, garbledCoreConstraints]
    refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
      ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
        ⟨List.forall_mem_append.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- commitmentPins: FIRE on the first row
      intro c hc; simp only [commitmentPins, List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact fun _ => eqToModEq (forgeRow_commit j hj)
    · -- outputHashPins: FIRE
      intro c hc; simp only [outputHashPins, List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact fun _ => eqToModEq (forgeRow_ohash j hj)
    · -- decryptionGates: VACUOUS (transition `.gate`, this row is last)
      intro c hc; simp only [decryptionGates, List.mem_map, List.mem_range] at hc
      obtain ⟨j, _, rfl⟩ := hc; exact True.intro
    · -- selectorBinaryGates: VACUOUS
      intro c hc; simp only [selectorBinaryGates, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
    · -- [exclusivityBody]: VACUOUS
      intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact True.intro
    · -- chainingGates: VACUOUS (window on_transition, last row)
      intro c hc; simp only [chainingGates, List.mem_map, List.mem_range] at hc
      obtain ⟨j, _, rfl⟩ := hc; exact fun hcon => absurd hcon (by decide)
    · -- [gateIndexDeltaBoundary]: FIRE on the first row
      intro c hc; simp only [List.mem_singleton] at hc; subst hc
      exact fun _ => by decide
  · intro i _; exact True.intro
  · intro i _ r hr; exact absurd hr (by simp [garbledEvalDescCore, garbledEvalDesc])
  · exact List.nodup_nil
  · intro op hop; rw [coreForge_memLog_nil] at hop; exact absurd hop (by simp)
  · rw [coreForge_memLog_nil]; exact True.intro
  · rw [coreForge_memLog_nil]; exact memCheck_nil _ _
  · rw [coreForge_memLog_nil]; rfl
  · rw [coreForge_mapLog_nil]; rfl

/-- The last-row decryption boundary (lane 0) is a member of the FIXED descriptor's constraint list —
it lives in `garbledLastRowFix`, the part the fix appended. -/
theorem forgeDecBoundary_mem :
    VmConstraint2.base (.boundary VmRow.last (decBody 0)) ∈ garbledEvalDesc.constraints := by
  show _ ∈ garbledCoreConstraints ++ garbledLastRowFix
  refine List.mem_append_right _ ?_
  simp only [garbledLastRowFix]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨0, List.mem_range.mpr (by decide), rfl⟩))

/-- **`garbled_forge_now_refused` — THE REGRESSION / GATE.** The SAME forged trace that `Satisfied2`s
the fix-less CORE is now REJECTED by the real (fixed-emit) `garbledEvalDesc`: its added last-row
decryption boundary `.base (.boundary VmRow.last (decBody 0))` FIRES on the height-1 trace's only row
and its body is `output(0) − table_entry(0) + hash_out(0) = 5 − 0 + 0 = 5 ≠ 0`. This is exactly the
output-label forgery the vacuous `.gate` let through; `garbledLastRowFix` catches it IN the descriptor. -/
theorem garbled_forge_now_refused
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash garbledEvalDesc minit mfin maddrs tForge := by
  intro h
  have h0 := h.rowConstraints 0 (by decide) _ forgeDecBoundary_mem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
    show (0 + 1 == tForge.rows.length) = true from rfl] at h0
  revert h0; decide

/-- The forged output `output(0) = 5` is NOT the genuine one-time-pad decryption
`HonestOutput (fun _ _ => 0) forgeRow 0 = table_entry(0) − 0 = 0`. So the accepted-on-core trace
exposes a forged label — the very output forgery `garbled_rung2_no_output_forgery` forbids, and which
the fix now makes UNSAT. -/
theorem forge_output_not_honest :
    (envAt tForge 0).loc (OUTPUT 0) = 5
    ∧ HonestOutput (fun _ _ => (0 : ℤ)) (envAt tForge 0).loc 0 = 0
    ∧ (envAt tForge 0).loc (OUTPUT 0) ≠ HonestOutput (fun _ _ => (0 : ℤ)) (envAt tForge 0).loc 0 :=
  ⟨by decide, by decide, by decide⟩

/-- **`garbled_lastRowFix_load_bearing`** — the forged trace witnesses that `garbledLastRowFix` is
LOAD-BEARING, not decorative: it `Satisfied2`s the fix-less CORE descriptor (the forged output slips
past the vacuous decryption `.gate`), it exposes a label that is NOT the genuine decryption, AND it is
REJECTED by the fixed real `garbledEvalDesc`. The fix is exactly what turns the accepted forgery into a
rejection. -/
theorem garbled_lastRowFix_load_bearing :
    Satisfied2 (fun _ => 0) garbledEvalDescCore (fun _ => 0) (fun _ => (0, 0)) [] tForge
    ∧ (∀ (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ),
         ¬ Satisfied2 hash garbledEvalDesc minit mfin maddrs tForge)
    ∧ (envAt tForge 0).loc (OUTPUT 0)
        ≠ HonestOutput (fun _ _ => (0 : ℤ)) (envAt tForge 0).loc 0 :=
  ⟨garbled_forge_was_satisfied2_core, garbled_forge_now_refused, forge_output_not_honest.2.2⟩

#assert_axioms garbled_forge_was_satisfied2_core
#assert_axioms garbled_forge_now_refused
#assert_axioms garbled_lastRowFix_load_bearing

end Dregg2.Circuit.Emit.GarbledEvalRung2
