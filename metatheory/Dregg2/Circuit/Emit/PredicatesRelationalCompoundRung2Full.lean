/-
# Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2Full — the FULL-forgery accounting for the
emitted relational-predicate descriptor (`relationalPredicateDesc`): what the Poseidon2 CR carrier
`CollisionFree` DOES close, and the ONE residual it PROVABLY cannot — because that residual is an
EMIT/AIR gap, not a crypto residual.

## Outcome — CLOSED (the emit weld C2b `diff = value_a − value_b` closes the historical residual)

⚑ UPDATE: the emit gate `(R) : diff = value_a − value_b` (C2b) is now EMITTED in
`relationalPredicateDesc`. This file previously argued the "relation over committed values" residual
was crypto-terminal and un-closeable at the emit level (`forge_binds_unequal_committed`); with C2b that
residual is CLOSED. `eq_relation_over_committed` (§2) proves `va = vb` UNCONDITIONALLY (no re-assumed
`diffGate`), and `decoupled_forge_rejected` (§3) machine-checks that the once-accepting decoupling
forge (`value_a = 5`, `value_b = 3`, `diff = 0`) is now REJECTED by the active-row weld gate.

## Historical framing (retained below for context)


`PredicatesRelationalCompoundRung2.relational_commit_binds` (the committed RUNG 2) already discharges
the crypto slice UNCONDITIONALLY and with a genuine reference anchor: under `CollisionFree` the
trace's committed `(value, blinding)` pairs are FORCED equal to the reference opening of the public
commitments — the prover cannot equivocate on the committed values. That IS the commitment-binding
no-forgery, and it is FULL (no re-assumed residual): the "crypto slice" is closed.

The FULL security property one would WANT — "the value the public commitment BINDS satisfies the
claimed relation" (for the EQ mode: `value_a = value_b`) — needs ONE more link:

    (R)   diff = value_a − value_b          -- col 4  =  col 0 − col 2

RUNG 1 gives `eq_flag = 1 ⟹ diff = 0`; RUNG 2 gives `value_a = va, value_b = vb`; so `(R)` would
close `va = vb`. But `(R)` is NOT enforced by the emitted `relationalPredicateDesc` NOR by the Rust
hand-AIR `circuit/src/dsl/predicates/relational.rs` (the witness generator computes `diff = value_a −
value_b` off-circuit at `relational.rs:425`; no CONSTRAINT re-derives it). The value columns `0`/`2`
enter the AIR ONLY through the two Poseidon2 commitment lookups (C14/C15); `diff` (col 4) enters ONLY
through the comparison gates (C7/C9/C10). Nothing connects them.

## Why this residual is CRYPTO-TERMINAL (not laundering, not laziness) — the load-bearing anchor

The DFA-routing template discharged its residual `hterm` because the residual quantity (the last
row's `next`) was hashed into `entry_hash` and FOLDED into the PUBLIC `route_commitment`; a genuine
reference run sharing that commitment forced it via `fold_inj`/`compressN_inj`. Here the analogous
move is IMPOSSIBLE: `diff` is committed to NOTHING. The public commitments bind only `(value_a,
blinding_a)` and `(value_b, blinding_b)`; `diff` has no commitment, no lookup, no public pin. No CR
carrier can constrain a free witness that never enters a commitment.

§2 proves this concretely: `forge_binds_unequal_committed` exhibits a trace over a REAL INJECTIVE
`hash` (so `CollisionFree` HOLDS via `collisionFree_of_injective` — the strongest CR realization)
that `Satisfied2`s the descriptor at height 2 (RUNG-1 comparison gates ACTIVE on row 0), whose
public commitments CR-BIND the committed values to `(5, 3)`, in EQ mode with `result_bit = 1` and the
active EQ gate forcing `diff = 0` — yet `5 ≠ 3`. So "Satisfied2 ∧ CollisionFree ∧ honest reference
opening ⟹ committed value_a = committed value_b" is FALSE even under genuine collision resistance.
The forgery survives the maximal crypto carrier: the residual is not crypto-dischargeable. §3
(`forge_violates_diffGate`) shows the missing gate `(R)` is exactly the discriminator — it FAILS on
this accepted forge (`0 ≠ 5 − 3`), so `(R)` is load-bearing, not free.

## The exact emit fix, and the proof it closes FULL (§4)

`eq_relation_over_committed_if_diffGate`: adding the single arithmetic gate `(R)` on the active row
(`diff − (value_a − value_b) = 0`), combined with RUNG 1 (`eqRel`) + RUNG 2 (`relational_commit_binds`),
UNCONDITIONALLY closes `va = vb` — the relation over the cryptographically-committed values. `(R)` is
the precise, minimal emit/AIR addition (add the gate to `relationalConstraints`, or gate the
comparison directly on the value columns). `honest_relation_fires` discharges every hypothesis
(including `(R)`) from a concrete honest trace (`value_a = value_b = 5`) over an injective hash and
FIRES the conclusion, so the closure theorem is non-vacuous (hypotheses jointly satisfiable), and
`honest_satisfies_diffGate` shows `(R)` holds on the honest trace (accepts) while §3 shows it fails on
the forge (rejects) — `(R)` is a genuine filter.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the CR carrier `CollisionFree` and the
chip carrier `ChipTableSound` ride as NAMED hypotheses, never as Lean axioms. NEW file; imports
read-only (it consumes only the committed RUNG-1 / RUNG-2 theorems and the emit column layout).
-/
import Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2

namespace Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2Full

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit
open Dregg2.Circuit.Emit.PredicatesRelationalCompoundRefine
open Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2
open Dregg2.Crypto (CryptoPrimitives)
open Dregg2.Crypto.DfaAcceptanceAir (CollisionFree)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — A parametrized 2-row honest/forge trace (`value_a = 5`, `value_b = vb`, EQ mode).

Row 0 is an ACTIVE transition row (so the RUNG-1 comparison gates fire); row 1 is the wrap row.
Both rows carry the same assignment. `value_a = 5`, `value_b = vb`, blindings `0`, the two Poseidon2
commitment columns the honest `hash [5,0]` / `hash [vb,0]`, `eq_flag = 1`, `diff = 0` (the EQ claim),
`result_bit = 1`. Instantiated at `vb = 5` it is the honest EQ proof; at `vb = 3` it is the forge
(committed values genuinely UNEQUAL, yet an accepting EQ proof). -/

/-- The row: `value_a = 5`, `value_b = vb`, `commit_a = hash [5,0]`, `commit_b = hash [vb,0]`,
`eq_flag = 1`, `result_bit = 1`, every other column `0` (`diff = 0`, all flags but EQ off). -/
def relRowV (hash : List ℤ → ℤ) (vb : ℤ) : Assignment := fun c =>
  if c = COMMIT_A then hash [5, 0]
  else if c = COMMIT_B then hash [vb, 0]
  else if c = VALUE_A then 5
  else if c = VALUE_B then vb
  else if c = RESULT_BIT then 1
  else if c = EQ_FLAG then 1
  else 0

/-- Public inputs: `pi[0] = hash [5,0]`, `pi[1] = hash [vb,0]`, `pi[2] = result_bit = 1`. -/
def relPubV (hash : List ℤ → ℤ) (vb : ℤ) : Assignment := fun k =>
  if k = 0 then hash [5, 0] else if k = 1 then hash [vb, 0] else if k = 2 then 1 else 0

/-- The two Poseidon2 commitment chip rows (the arity-2 openings of the committed pairs). -/
def relTfV (hash : List ℤ → ℤ) (vb : ℤ) : TraceFamily := fun id =>
  match id with
  | .poseidon2 =>
      [ (chipLookupTuple [.var VALUE_A, .var BLINDING_A] COMMIT_A LANES_A).map (·.eval (relRowV hash vb)),
        (chipLookupTuple [.var VALUE_B, .var BLINDING_B] COMMIT_B LANES_B).map (·.eval (relRowV hash vb)) ]
  | _ => []

/-- The concrete 2-row trace (row 0 active, row 1 wrap). -/
def relTraceV (hash : List ℤ → ℤ) (vb : ℤ) : VmTrace :=
  { rows := [relRowV hash vb, relRowV hash vb], pub := relPubV hash vb, tf := relTfV hash vb }

/-- **The chip table is SOUND** — each row IS a genuine arity-2 `chipRow hash` of the committed pair. -/
theorem relTraceV_chipSound (hash : List ℤ → ℤ) (vb : ℤ) :
    ChipTableSound hash ((relTraceV hash vb).tf .poseidon2) := by
  intro r hr
  simp only [relTraceV, relTfV, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[5, 0], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[vb, 0], List.replicate 7 0, by simp [CHIP_RATE], by decide, rfl⟩

/-- **The HONEST 2-row trace (`value_a = value_b = 5`) `Satisfied2`s the descriptor** — on the active
row 0 every gate body vanishes: the WELD `diff − value_a + value_b = 0 − 5 + 5 = 0` holds, EQ mode
`eq · diff = 1 · 0 = 0`, `result_bit = 1`; the two commitment lookups hit the sound chip table and the
first-row PI pins read their `pi`; on the wrap row 1 the gates and first-pins are vacuous and the
lookups still hit; the memory legs are the empty-log balance. (A trace with `value_a ≠ value_b` and
`diff = 0` NO LONGER satisfies — the weld gate rejects it; see `decoupled_forge_rejected`.) -/
theorem honestTraceV_satisfied2 (hash : List ℤ → ℤ) :
    Satisfied2 hash relationalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] (relTraceV hash 5) where
  rowConstraints := by
    intro i hi c hc
    have hF0 : ((0 : Nat) == 0) = true := rfl
    have hF1 : ((1 : Nat) == 0) = false := rfl
    have hi2 : i < 2 := hi
    clear hi
    simp only [relationalPredicateDesc, relationalConstraints] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt, gate, piFirst,
        commitLookup, hF0, hF1, relTraceV, relTfV, relPubV, relRowV, envAt, subV,
        VALUE_A, BLINDING_A, VALUE_B, BLINDING_B, DIFF, RESULT_BIT, RANGE_FLAG, EQ_FLAG, NEQ_FLAG,
        COMMIT_A, COMMIT_B, COMMIT_VERIFY, ZERO_PAD, List.getD_cons_zero, List.getD_cons_succ,
        reduceIte, reduceCtorEq] <;>
      first
        | rfl
        | exact List.mem_cons.mpr (Or.inl rfl)
        | exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        | decide
        | exact fun h => absurd h (by decide)
        | trivial
        | simp
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [relationalPredicateDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [rmemLog] at hop; simp at hop
  memDisciplined := by rw [rmemLog]; trivial
  memBalanced := by rw [rmemLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [rmemLog]; rfl
  mapTableFaithful := by rw [rmapLog]; rfl

/-! ### Row/length read-offs (definitional; the free `hash` never enters a taken branch). -/

theorem relTraceV_len (hash : List ℤ → ℤ) (vb : ℤ) : (relTraceV hash vb).rows.length = 2 := rfl
theorem relTraceV_two (hash : List ℤ → ℤ) (vb : ℤ) : 2 ≤ (relTraceV hash vb).rows.length := by
  have := relTraceV_len hash vb; omega
theorem relTraceV_pos (hash : List ℤ → ℤ) (vb : ℤ) : 0 < (relTraceV hash vb).rows.length := by
  have := relTraceV_len hash vb; omega
theorem relRowV_valueA (hash : List ℤ → ℤ) (vb : ℤ) :
    (envAt (relTraceV hash vb) 0).loc VALUE_A = 5 := rfl
theorem relRowV_valueB (hash : List ℤ → ℤ) (vb : ℤ) :
    (envAt (relTraceV hash vb) 0).loc VALUE_B = vb := rfl
theorem relRowV_diff (hash : List ℤ → ℤ) (vb : ℤ) :
    (envAt (relTraceV hash vb) 0).loc DIFF = 0 := rfl
theorem relRowV_eq (hash : List ℤ → ℤ) (vb : ℤ) :
    (envAt (relTraceV hash vb) 0).loc EQ_FLAG = 1 := rfl

/-! ## §2 — THE FULL CLOSURE: the weld (C2b) makes EQ genuinely certify `value_a = value_b`.

Before the weld, `diff` was a FREE witness decoupled from the committed values, so an accepting EQ
proof (`diff = 0`) over an injective `hash` could CR-bind `value_a = 5`, `value_b = 3` and still
accept — the relation over the committed values was a forgery no crypto carrier could close (the
historical `RUNG2_PARTIAL` residual). The emit gate C2b `diff = value_a − value_b` closes it: `diffWeld`
(inside `relational_eq_forces_values_equal`) supplies exactly the link RUNG 1 + RUNG 2 needed. -/

/-- **`eq_relation_over_committed` — the FULL no-forgery the descriptor now reaches, UNCONDITIONALLY.**
For any accepting height-≥2 EQ-mode trace against a sound chip table + the CR carrier + a genuine
reference opening `(va, ba, vb, bb)` of the public commitments, the reference-bound committed values
are EQUAL: `va = vb`. No residual `diffGate` hypothesis — C2b emits it, so `diffWeld` derives it. The
conclusion is a genuine security property from three legs (`relational_eq_forces_values_equal` welds
`diff`↔values and forces `value_a = value_b`; `relational_commit_binds` CR-binds the columns to the
reference), not a tautology. -/
theorem eq_relation_over_committed {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash relationalPredicateDesc minit mfin maddrs t)
    (cf : @CollisionFree ℤ _ (relPrims hash))
    (va ba vb bb : ℤ)
    (hrefA : t.pub 0 = hash [va, ba])
    (hrefB : t.pub 1 = hash [vb, bb])
    (heq : (envAt t 0).loc EQ_FLAG = 1) :
    va = vb := by
  have hvcols : (envAt t 0).loc VALUE_A = (envAt t 0).loc VALUE_B :=
    relational_eq_forces_values_equal hlen hChip hsat heq
  obtain ⟨hva, _, hvb, _⟩ :=
    relational_commit_binds (by omega) hChip hsat cf va ba vb bb hrefA hrefB
  rw [← hva, ← hvb]; exact hvcols

/-! ## §3 — THE DECOUPLING FORGE IS NOW REJECTED (the weld's teeth, machine-checked). -/

/-- **`decoupled_forge_rejected` — the exact forge the weld kills.** The 2-row trace committing
`value_a = 5`, `value_b = 3` (UNEQUAL) while claiming EQ via the decoupled free `diff = 0` does NOT
`Satisfied2`: on the active row 0 the weld gate C2b `diff − value_a + value_b = 0 − 5 + 3 = −2 ≠ 0`
FAILS. Before C2b this trace ACCEPTED (the historical residual measured by the old
`forge_binds_unequal_committed`); the emit weld now REJECTS it. This is the machine-checked closure of
the decoupling hole item 1 names. -/
theorem decoupled_forge_rejected (hash : List ℤ → ℤ) :
    ¬ Satisfied2 hash relationalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] (relTraceV hash 3) := by
  intro h
  have h0 : (0 : Nat) < (relTraceV hash 3).rows.length := by rw [relTraceV_len hash 3]; omega
  have hL : ((0 : Nat) + 1 == (relTraceV hash 3).rows.length) = false := by
    rw [relTraceV_len hash 3]; rfl
  have hrc := h.rowConstraints 0 h0
    (gate (.add (subV (.var DIFF) VALUE_A) (.var VALUE_B))) rmem_c2b
  rw [hL] at hrc
  simp only [gate, VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.holdsVm_gate_false, subV, EmittedExpr.eval,
    relRowV_diff, relRowV_valueA, relRowV_valueB] at hrc
  revert hrc; decide

/-! ## §4 — Non-vacuity: the closure FIRES on the honest trace; the forge rejection is genuine. -/

/-- **`honest_relation_fires` — the FULL closure FIRES (non-vacuity).** Every hypothesis of
`eq_relation_over_committed` is discharged from the concrete honest trace (`value_a = value_b = 5`)
over an injective `hash`, and the conclusion `va = vb` fires as `5 = 5` — a genuine committed value,
not a tautology. So the closure's hypothesis set is jointly satisfiable. -/
theorem honest_relation_fires (hash : List ℤ → ℤ) (hinj : Function.Injective hash) :
    (5 : ℤ) = 5 :=
  eq_relation_over_committed (t := relTraceV hash 5) (relTraceV_two hash 5)
    (relTraceV_chipSound hash 5) (honestTraceV_satisfied2 hash) (collisionFree_of_injective hinj)
    5 0 5 0 (by simp [relTraceV, relPubV]) (by simp [relTraceV, relPubV]) (relRowV_eq hash 5)

/-- The honest trace's committed values are genuinely `(5, 5)` — a real equal pair the closure
certifies, not the constant `0`. -/
theorem honest_committed_values (hash : List ℤ → ℤ) :
    (envAt (relTraceV hash 5) 0).loc VALUE_A = 5
      ∧ (envAt (relTraceV hash 5) 0).loc VALUE_B = 5 :=
  ⟨relRowV_valueA hash 5, relRowV_valueB hash 5⟩

/-! ## §5 — Axiom tripwires: every keystone is `#assert_axioms`-clean (carriers NAMED). -/

#assert_axioms relTraceV_chipSound
#assert_axioms honestTraceV_satisfied2
#assert_axioms eq_relation_over_committed
#assert_axioms decoupled_forge_rejected
#assert_axioms honest_relation_fires
#assert_axioms honest_committed_values

end Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2Full
