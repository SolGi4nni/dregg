/-
# Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2 — the RUNG-2 commitment-BINDING discharge
for the emitted relational-predicate descriptor (`relationalPredicateDesc`), via the Poseidon2
collision-resistance carrier `CollisionFree`.

## What this file IS

`PredicatesRelationalCompoundRefine.lean` (RUNG 1) proves the bridge `Satisfied2 ∧ 2 ≤ height ⟹
RelClassified`, whose commitment leg is (against the named `ChipTableSound` carrier)

  * `commitAOpen : COMMIT_A = hash [value_a, blinding_a]`   (the public `pi[0]` OPENS the private pair)
  * `commitBOpen : COMMIT_B = hash [value_b, blinding_b]`

i.e. the public commitment is SOME Poseidon2 hash of the trace's private value/blinding columns. RUNG 2
STRENGTHENS this leg from "opens" to "BINDS": against the standard Poseidon2 CR carrier
`CollisionFree` (its arity-2 face `compress_pair_inj`) and a GENUINE reference opening of the SAME
public commitments — the honest committed values `pi` is a commitment OF — the trace's committed
`(value, blinding)` pairs are FORCED equal to the reference. The prover cannot equivocate on the
committed values: this is the commitment-binding no-forgery for "relation OVER COMMITTED VALUES".

## Why an anchor is genuinely needed (this is NOT laundering)

Unconditional `Satisfied2 ⟹ committed value determined` is FALSE, and provably so (§4): under a
COLLIDING `hash` (e.g. the constant `hash0`, which is NOT collision-free — `hash0_not_collisionFree`),
a prover can commit `value_a = 7` while a reference `(0,0)` opens the SAME public commitment `0 =
hash0 [0,0]`. The trace `Satisfied2`s (`cheatTrace_satisfied2`), both open `pi[0]`, yet `7 ≠ 0`
(`cheat_binds_would_be_false`). The uniqueness of the committed value therefore pivots on the CR
carrier — exactly what `CollisionFree.compress_pair_inj` supplies. So the anchor is a real filter, not
`True`.

## ⚑ UPDATE — the RUNG2_PARTIAL residual is now CLOSED by the emit weld C2b

The residual described below ("the COMMITTED VALUES satisfy the claimed relation") was closed by adding
the emit gate `(R) : diff = value_a − value_b` (C2b) to `relationalPredicateDesc`. On an ACTIVE
(height-≥2) trace the weld gate now REJECTS the decoupling forge — see
`PredicatesRelationalCompoundRung2Full.decoupled_forge_rejected` and the unconditional closure
`eq_relation_over_committed`, and the value-level relations
`PredicatesRelationalCompoundRefine.{relational_eq_forces_values_equal, relational_neq_forces_values_distinct,
relational_range_forces_ge}`. The §5b measurement below survives ONLY on a DEGENERATE 1-row trace
where every transition gate (including the weld) is vacuous (row 0 is the last row); it is retained as
the historical motivation for C2b, not a live gap.

## The (historical) RESIDUAL that RUNG 2 alone does NOT close (named precisely — RUNG2_PARTIAL)

The relational descriptor certifies the comparison on `diff` (col 4), but NOTHING ties `diff` to
`value_a - value_b`: the value columns `0`/`2` enter the AIR ONLY through the two commitment lookups,
and `diff` is a FREE witness (this is true of BOTH the emitted `relationalPredicateDesc` AND the Rust
hand-AIR `circuit/src/dsl/predicates/relational.rs` — the witness generator computes `diff = value_a -
value_b` off-circuit at `relational.rs:425`, but no CONSTRAINT enforces it). So an accepting proof does
NOT certify that the COMMITTED VALUES satisfy the claimed relation — only that they are uniquely bound
(this file), and that the free `diff` satisfies the selected comparison (RUNG 1). Closing "committed
values satisfy the relation" is an EMIT/AIR FIX (add a gate `diff - (value_a - value_b) = 0`, or gate
the comparison directly on the value columns), NOT a crypto residual — NO named carrier discharges a
missing in-circuit arithmetic constraint. Likewise the COMPOUND descriptor's AND/OR/Threshold/Custom
laws route the composed bit through the prover-supplied `and_intermediate`/`gate_output` (never
re-derived in-circuit); only the NOT law is fully in-circuit (`compound_not_computes_negation`, RUNG 1,
DONE) — the AND/OR gaps are the same missing-constraint class, and the compound descriptor carries NO
crypto lookup at all, so there is no Rung-2 carrier discharge for it.

§5b turns this prose into a MACHINE-CHECKED measurement: `fg_accepts_unequal_committed` exhibits an
accepting EQ proof over a REAL INJECTIVE `hash` (perfect CR) whose committed values are FULLY CR-bound
by `relational_commit_binds` to `value_a = 5`, `value_b = 7` — yet `5 ≠ 7`, so the accepting proof's
committed values VIOLATE the claimed EQ relation. The residual therefore SURVIVES the CR carrier; it is
NOT crypto-closable, and any "discharge" that transports the relation from a relation-carrying reference
would ignore every in-circuit comparison gate — a vacuous strengthening, not a Rung-2 carrier
consumption. ⚑ Closing it is the EMIT/AIR fix `diff - (value_a - value_b) = 0` — NOW EMITTED as C2b in
`relationalPredicateDesc` (see the §UPDATE note above); the residual is CLOSED, not partial.

## The named carrier

The binding rides the Poseidon2 collision-resistance carrier `CollisionFree` (arity-2
`compress_pair_inj`), realized on the descriptor's own row `hash` via `relPrims` (`compress a b :=
hash [a, b]`) — the same shape `DfaRoutingRung2.dfaPrims` uses. It enters ONLY as an explicit
hypothesis, never as a Lean axiom; the chip-table faithfulness carrier `ChipTableSound` enters through
`chip_lookup_sound` as in RUNG 1.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the CR carrier `CollisionFree` and the
chip carrier `ChipTableSound` ride as NAMED hypotheses. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PredicatesRelationalCompoundRefine
import Dregg2.Crypto.DfaAcceptanceAir

namespace Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit
open Dregg2.Circuit.Emit.PredicatesRelationalCompoundRefine
open Dregg2.Crypto (CryptoPrimitives)
open Dregg2.Crypto.DfaAcceptanceAir (CollisionFree)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — The Poseidon2 CR primitives realized as the descriptor's arity-2 commitment `hash`. -/

/-- The `CryptoPrimitives ℤ` instance realizing the abstract Poseidon2 arity-2 compression as the
descriptor's own commitment `hash : List ℤ → ℤ`: `compress a b := hash [a, b]` (the `hash_2_to_1`
the two relational commitment lookups bind). The sponge / Pedersen / nullifier carriers are trivial
witnesses (unused by the commitment binding). `@[reducible]` so the abstract `compress` denotation
computes to the `hash`-shaped commitment equation; forced via `letI`. -/
@[reducible] def relPrims (hash : List ℤ → ℤ) : CryptoPrimitives ℤ where
  compress a b := hash [a, b]
  compressN l := hash l
  collisionHard := True
  commit _ _ := 0
  commit_hom := by intro v w r s; simp
  binding := True
  nullifier := id
  unlinkable := True

/-- **The CR carrier is instantiable from `hash` injectivity.** The reference realization that keeps
the RUNG-2 hypothesis set non-vacuous: a genuine Poseidon2 `hash` supplies CR (not literal
injectivity), but injectivity discharges both `CollisionFree` consequences for `relPrims hash`. -/
theorem collisionFree_of_injective {hash : List ℤ → ℤ} (hinj : Function.Injective hash) :
    @CollisionFree ℤ _ (relPrims hash) :=
  letI := relPrims hash
  { compress_pair_inj := fun a b c d h => by
      have hlist : [a, b] = [c, d] := hinj h
      injection hlist with h1 h2
      injection h2 with h3 _
      exact ⟨h1, h3⟩
    compressN_inj := fun _ _ h => hinj h }

/-! ## §2 — The commitment-opening EXTRACTOR (row 0, needs only `0 < height`).

The two commitment lookups are `.lookup`s (enforced on EVERY row, never divided by a zerofier) and
the two commitment PI pins are FIRST-row pins — both fire on row `0` of any non-empty trace. So the
opening leg is available WITHOUT the `2 ≤ height` active-row hypothesis `RelClassified` needs (which
is only for the comparison GATES). This is the leg RUNG 2 upgrades. -/

/-- **`commit_opens`** — against the named `ChipTableSound` carrier, the public commitments `pi[0]`,
`pi[1]` are Poseidon2 openings of the trace's private value/blinding columns on row `0`. -/
theorem commit_opens {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hpos : 0 < t.rows.length)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash relationalPredicateDesc minit mfin maddrs t) :
    t.pub 0 = hash [(envAt t 0).loc VALUE_A, (envAt t 0).loc BLINDING_A]
      ∧ t.pub 1 = hash [(envAt t 0).loc VALUE_B, (envAt t 0).loc BLINDING_B] := by
  have hF : ((0 : Nat) == 0) = true := rfl
  -- lookup A → COMMIT_A = hash [value_a, blinding_a]
  have hla := hsat.rowConstraints 0 hpos (commitLookup VALUE_A BLINDING_A COMMIT_A LANES_A)
    rmem_lookupA
  simp only [commitLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hla
  have hsa := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var VALUE_A, .var BLINDING_A] COMMIT_A LANES_A (by decide) hla
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hsa
  -- pin A → COMMIT_A = pi[0]
  have hpa := hsat.rowConstraints 0 hpos (piFirst COMMIT_A 0) rmem_commitAPin
  rw [hF] at hpa
  simp only [piFirst, VmConstraint2.holdsAt, holdsVm_piFirst_true] at hpa
  -- lookup B → COMMIT_B = hash [value_b, blinding_b]
  have hlb := hsat.rowConstraints 0 hpos (commitLookup VALUE_B BLINDING_B COMMIT_B LANES_B)
    rmem_lookupB
  simp only [commitLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hlb
  have hsb := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var VALUE_B, .var BLINDING_B] COMMIT_B LANES_B (by decide) hlb
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hsb
  -- pin B → COMMIT_B = pi[1]
  have hpb := hsat.rowConstraints 0 hpos (piFirst COMMIT_B 1) rmem_commitBPin
  rw [hF] at hpb
  simp only [piFirst, VmConstraint2.holdsAt, holdsVm_piFirst_true] at hpb
  refine ⟨?_, ?_⟩
  · have hpub : (envAt t 0).pub 0 = t.pub 0 := rfl
    rw [← hpub, ← hpa]; exact hsa
  · have hpub : (envAt t 0).pub 1 = t.pub 1 := rfl
    rw [← hpub, ← hpb]; exact hsb

/-! ## §3 — THE RUNG-2 DISCHARGE: the committed values are BOUND by the public commitments. -/

/-- **`relational_commit_binds` — the Rung-2 commitment-binding no-forgery.** A trace that
`Satisfied2`s `relationalPredicateDesc`, is non-empty, rides a SOUND Poseidon2 chip table (`hChip`),
the CR carrier `cf : CollisionFree`, and a GENUINE reference opening `(va, ba, vb, bb)` of the SAME
public commitments `pi[0]`, `pi[1]` (the honest committed values the commitments are OF) has its
private value/blinding columns FORCED equal to the reference — the prover cannot open the public
commitments to any other values. Consumes `CollisionFree.compress_pair_inj`; the reference is the
honest anchor. -/
theorem relational_commit_binds {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hpos : 0 < t.rows.length)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash relationalPredicateDesc minit mfin maddrs t)
    (cf : @CollisionFree ℤ _ (relPrims hash))
    (va ba vb bb : ℤ)
    (hrefA : t.pub 0 = hash [va, ba])
    (hrefB : t.pub 1 = hash [vb, bb]) :
    (envAt t 0).loc VALUE_A = va ∧ (envAt t 0).loc BLINDING_A = ba
      ∧ (envAt t 0).loc VALUE_B = vb ∧ (envAt t 0).loc BLINDING_B = bb := by
  letI := relPrims hash
  obtain ⟨hoa, hob⟩ := commit_opens hpos hChip hsat
  have hcollA : hash [(envAt t 0).loc VALUE_A, (envAt t 0).loc BLINDING_A] = hash [va, ba] := by
    rw [← hoa]; exact hrefA
  have hcollB : hash [(envAt t 0).loc VALUE_B, (envAt t 0).loc BLINDING_B] = hash [vb, bb] := by
    rw [← hob]; exact hrefB
  have hA := cf.compress_pair_inj ((envAt t 0).loc VALUE_A) ((envAt t 0).loc BLINDING_A) va ba hcollA
  have hB := cf.compress_pair_inj ((envAt t 0).loc VALUE_B) ((envAt t 0).loc BLINDING_B) vb bb hcollB
  exact ⟨hA.1, hA.2, hB.1, hB.2⟩

/-! ## §4 — Non-vacuity, FALSE half: `Satisfied2` + opening alone do NOT force the committed value.

Under the COLLIDING constant `hash0` a prover commits `value_a = 7`, yet the reference `(0,0)` opens
the SAME public commitment `0 = hash0 [0,0]`. The trace `Satisfied2`s (1-row: gates vacuous on the
only/last row, lookups by membership, PI pins met), both open `pi[0]`, yet `7 ≠ 0`. So the RUNG-2
CR anchor is LOAD-BEARING — the binding is impossible from `Satisfied2` + opening alone. -/

/-- The cheating row: `value_a = 7` (nonzero), `eq_flag = 1`, `diff = 0`, `result_bit = 1`; every
commitment/lane column `0`, so `commit_a = commit_b = hash0 [·] = 0`. -/
def cheatRow : Assignment :=
  fun c => if c = VALUE_A then 7 else if c = RESULT_BIT then 1 else if c = EQ_FLAG then 1 else 0

/-- The two Poseidon2 chip rows the commitment lookups target, evaluated on `cheatRow` (both hash to
`hash0 [·] = 0`). -/
def cheatRowA : List ℤ := (chipLookupTuple [.var VALUE_A, .var BLINDING_A] COMMIT_A LANES_A).map
  (·.eval cheatRow)
def cheatRowB : List ℤ := (chipLookupTuple [.var VALUE_B, .var BLINDING_B] COMMIT_B LANES_B).map
  (·.eval cheatRow)

def cheatTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [cheatRowA, cheatRowB]
  | _ => []

/-- The 1-row cheating trace over the colliding `hash0`; `relPub` pins `result_bit = pi[2] = 1`. -/
def cheatTrace : VmTrace := { rows := [cheatRow], pub := relPub, tf := cheatTf }

/-- **The cheat PROVABLY `Satisfied2`s** — gates vacuous on the single (= last) row, the two
commitment lookups hold by membership (`hash0 [7,0] = hash0 [0,0] = 0 = commit`), the PI pins met. -/
theorem cheatTrace_satisfied2 :
    Satisfied2 hash0 relationalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] cheatTrace where
  rowConstraints := by
    intro i hi c hc
    have gL : ((0 : Nat) + 1 == cheatTrace.rows.length) = true := rfl
    have hF : ((0 : Nat) == 0) = true := rfl
    have hi1 : i < 1 := hi
    clear hi
    simp only [relationalPredicateDesc, relationalConstraints] at hc
    interval_cases i
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt, gate, piFirst,
        commitLookup, gL, hF] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [relationalPredicateDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [rmemLog] at hop; simp at hop
  memDisciplined := by rw [rmemLog]; trivial
  memBalanced := by rw [rmemLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [rmemLog]; rfl
  mapTableFaithful := by rw [rmapLog]; rfl

/-- **`hash0` is NOT collision-free** — the exact collision the cheat rides: `hash0 [7,0] = hash0 [0,0]`
with `7 ≠ 0`. So the CR carrier `CollisionFree` is precisely what a genuine `hash` must supply and what
`hash0` lacks — the load-bearing hypothesis. -/
theorem hash0_not_collisionFree : ¬ @CollisionFree ℤ _ (relPrims hash0) := by
  intro cf
  letI := relPrims hash0
  have h : (7 : ℤ) = 0 ∧ (0 : ℤ) = 0 := cf.compress_pair_inj 7 0 0 0 (by decide)
  exact absurd h.1 (by decide)

/-- **The cheat refutes a CR-free binding (the FALSE half):** the trace `Satisfied2`s, the reference
`(0,0)` opens the SAME public commitment `pi[0]`, yet the committed `value_a = 7 ≠ 0`. So no
`Satisfied2`-plus-opening-only theorem could conclude `value_a = va` — the `CollisionFree` anchor is
load-bearing. -/
theorem cheat_binds_would_be_false :
    cheatTrace.pub 0 = hash0 [0, 0]
      ∧ (envAt cheatTrace 0).loc VALUE_A = 7
      ∧ (7 : ℤ) ≠ 0 :=
  ⟨by decide, by decide, by decide⟩

/-! ## §5 — Non-vacuity, TRUE half: the RUNG-2 binding FIRES on a genuine witness.

A 1-row honest relational proof over a REAL injective `hash` (so the CR carrier is discharged from
`Function.Injective hash` via `collisionFree_of_injective`). The committed pair is `(value_a, blinding_a)
= (5, 0)`, `(value_b, blinding_b) = (5, 1)` (genuinely EQ, `diff = 0`); every hypothesis of
`relational_commit_binds` is met and the discharged binding FIRES: the committed values are FORCED equal
to the reference `(5, 0, 5, 1)`. -/

section TrueWitness
variable (hash : List ℤ → ℤ)

/-- The honest committed row: `value_a = value_b = 5`, `blinding_a = 0`, `blinding_b = 1`, `eq_flag =
1`, `diff = 0`, `result_bit = 1`, `commit_a = hash [5,0]`, `commit_b = hash [5,1]`. -/
def bwRow : Assignment := fun c =>
  if c = COMMIT_A then hash [5, 0]
  else if c = COMMIT_B then hash [5, 1]
  else if c = VALUE_A then 5
  else if c = VALUE_B then 5
  else if c = BLINDING_B then 1
  else if c = RESULT_BIT then 1
  else if c = EQ_FLAG then 1
  else 0

/-- Public inputs: `pi[0] = hash [5,0]`, `pi[1] = hash [5,1]`, `pi[2] = result_bit = 1`. -/
def bwPub : Assignment := fun k =>
  if k = 0 then hash [5, 0] else if k = 1 then hash [5, 1] else if k = 2 then 1 else 0

def bwTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 =>
      [ (chipLookupTuple [.var VALUE_A, .var BLINDING_A] COMMIT_A LANES_A).map (·.eval (bwRow hash)),
        (chipLookupTuple [.var VALUE_B, .var BLINDING_B] COMMIT_B LANES_B).map (·.eval (bwRow hash)) ]
  | _ => []

/-- The 1-row genuine trace. -/
def bwTrace : VmTrace := { rows := [bwRow hash], pub := bwPub hash, tf := bwTf hash }

/-- **The chip table is SOUND** — each row IS a genuine `chipRow hash` of the committed pair. -/
theorem bwTf_chipSound : ChipTableSound hash ((bwTrace hash).tf .poseidon2) := by
  intro r hr
  simp only [bwTrace, bwTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[5, 0], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[5, 1], List.replicate 7 0, by decide, by decide, rfl⟩

/-- **The 1-row trace `Satisfied2`s** — gates vacuous on the only/last row, the two commitment
lookups by membership, the PI pins (`result_bit = 1`, `commit_a`/`commit_b` = their `pi`) met. -/
theorem bwTrace_satisfied2 :
    Satisfied2 hash relationalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] (bwTrace hash) where
  rowConstraints := by
    intro i hi c hc
    have gL : ((0 : Nat) + 1 == (bwTrace hash).rows.length) = true := rfl
    have hF : ((0 : Nat) == 0) = true := rfl
    have hi1 : i < 1 := hi
    clear hi
    simp only [relationalPredicateDesc, relationalConstraints] at hc
    interval_cases i
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt, gate, piFirst,
        commitLookup, hF, bwTrace, bwTf, bwPub, bwRow, envAt, VALUE_A, BLINDING_A,
        VALUE_B, BLINDING_B, DIFF, RESULT_BIT, RANGE_FLAG, EQ_FLAG, NEQ_FLAG, COMMIT_A, COMMIT_B,
        COMMIT_VERIFY, ZERO_PAD, List.getD_cons_zero, reduceIte, reduceCtorEq] <;>
      first
        | exact List.mem_cons.mpr (Or.inl rfl)
        | exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        | trivial
        | rfl
        | simp
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [relationalPredicateDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [rmemLog] at hop; simp at hop
  memDisciplined := by rw [rmemLog]; trivial
  memBalanced := by rw [rmemLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [rmemLog]; rfl
  mapTableFaithful := by rw [rmapLog]; rfl

/-- **THE RUNG-2 BINDING FIRES on the genuine witness (the TRUE half).** Feeding the concrete
satisfying trace, its sound chip table, the CR carrier (from `Function.Injective hash`), and the honest
reference `(5, 0, 5, 1)` to `relational_commit_binds` FORCES the committed value/blinding columns equal
to the reference — WITHOUT assuming it. -/
theorem bwTrace_binds_fires (hinj : Function.Injective hash) :
    (envAt (bwTrace hash) 0).loc VALUE_A = 5 ∧ (envAt (bwTrace hash) 0).loc BLINDING_A = 0
      ∧ (envAt (bwTrace hash) 0).loc VALUE_B = 5 ∧ (envAt (bwTrace hash) 0).loc BLINDING_B = 1 :=
  relational_commit_binds (by simp [bwTrace]) (bwTf_chipSound hash) (bwTrace_satisfied2 hash)
    (collisionFree_of_injective hinj) 5 0 5 1 (by simp [bwTrace, bwPub]) (by simp [bwTrace, bwPub])

/-- The bound committed value is the genuine `value_a = 5` (a real committed value, not a constant `0`)
— the conclusion is achievably true, not vacuous. -/
theorem bwTrace_binds_value (hinj : Function.Injective hash) :
    (envAt (bwTrace hash) 0).loc VALUE_A = 5 ∧ (5 : ℤ) ≠ 0 :=
  ⟨(bwTrace_binds_fires hash hinj).1, by decide⟩

end TrueWitness

/-! ## §5b — [HISTORICAL] the RUNG2_PARTIAL residual on a DEGENERATE 1-row trace (now closed by C2b).

⚑ The `fgTrace` below is 1-ROW, so every transition gate — including the emit weld C2b `diff =
value_a − value_b` — is VACUOUS (row 0 is the last row). That is the ONLY reason this decoupled forge
still `Satisfied2`s. On an ACTIVE height-≥2 trace the weld REJECTS exactly this forge
(`PredicatesRelationalCompoundRung2Full.decoupled_forge_rejected`), and the committed-value relation is
now certified UNCONDITIONALLY (`...Rung2Full.eq_relation_over_committed`). This section is retained as
the historical measurement that MOTIVATED the C2b weld; it is not a live soundness gap.

The §4 cheat rides a COLLIDING `hash0` to break the commitment BINDING; that gap
`relational_commit_binds` CLOSES against `CollisionFree`. But the NAMED `RUNG2_PARTIAL` residual — "the
COMMITTED VALUES satisfy the claimed relation" — is NOT a crypto gap: it survives a PERFECT (injective)
`hash`. Here is the machine-checked forgery. An EQ proof commits `value_a = 5`, `value_b = 7` (UNEQUAL),
and sets the FREE difference witness `diff = 0`, so the ONLY comparison tooth on the private difference
(`eq_flag · diff = 0`) passes and the trace `Satisfied2`s. Fed to `relational_commit_binds` over an
INJECTIVE `hash`, its committed columns are FULLY CR-bound to the reference `(5, 0, 7, 1)` — yet
`5 ≠ 7`: the accepting EQ proof's committed values VIOLATE the claimed relation. So NO named crypto
carrier discharges this residual (an injective hash is the strongest CR carrier there is, and the
forgery survives it); ⚑ closing it is the EMIT/AIR fix `diff − (value_a − value_b) = 0` — NOW EMITTED as
the C2b weld. NOTE this 1-row `fgTrace` accepts ONLY because its single row is the last row (all
transition gates, including C2b, vacuous); on an active height-≥2 trace C2b REJECTS this exact forge
(`...Rung2Full.decoupled_forge_rejected`). This section is retained as the historical FALSE-half
measurement that motivated C2b, not a live gap. -/

section ResidualMeasurement
variable (hash : List ℤ → ℤ)

/-- The forging committed row: EQ selected (`eq_flag = 1`), `value_a = 5`, `value_b = 7` (UNEQUAL), the
FREE difference witness `diff = 0` (so `eq_flag · diff = 0` passes), `blinding_a = 0`, `blinding_b = 1`,
`result_bit = 1`, `commit_a = hash [5, 0]`, `commit_b = hash [7, 1]`. -/
def fgRow : Assignment := fun c =>
  if c = COMMIT_A then hash [5, 0]
  else if c = COMMIT_B then hash [7, 1]
  else if c = VALUE_A then 5
  else if c = VALUE_B then 7
  else if c = BLINDING_B then 1
  else if c = RESULT_BIT then 1
  else if c = EQ_FLAG then 1
  else 0

/-- Public inputs: `pi[0] = hash [5,0]`, `pi[1] = hash [7,1]`, `pi[2] = result_bit = 1`. -/
def fgPub : Assignment := fun k =>
  if k = 0 then hash [5, 0] else if k = 1 then hash [7, 1] else if k = 2 then 1 else 0

def fgTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 =>
      [ (chipLookupTuple [.var VALUE_A, .var BLINDING_A] COMMIT_A LANES_A).map (·.eval (fgRow hash)),
        (chipLookupTuple [.var VALUE_B, .var BLINDING_B] COMMIT_B LANES_B).map (·.eval (fgRow hash)) ]
  | _ => []

/-- The 1-row forging trace. -/
def fgTrace : VmTrace := { rows := [fgRow hash], pub := fgPub hash, tf := fgTf hash }

/-- **The chip table is SOUND** — each row IS a genuine `chipRow hash` of the committed pair (the
forgery does not lie about the commitments; it lies about the RELATION via the free `diff`). -/
theorem fgTf_chipSound : ChipTableSound hash ((fgTrace hash).tf .poseidon2) := by
  intro r hr
  simp only [fgTrace, fgTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[5, 0], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[7, 1], List.replicate 7 0, by decide, by decide, rfl⟩

/-- **The 1-row forging trace `Satisfied2`s** — gates vacuous on the only/last row, the two commitment
lookups by membership, and every PI pin met (`result_bit = 1`, `commit_a`/`commit_b` = their `pi`). NO
gate ties `diff` to `value_a − value_b`, so `value_a = 5 ≠ 7 = value_b` with `diff = 0` accepts. -/
theorem fgTrace_satisfied2 :
    Satisfied2 hash relationalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] (fgTrace hash) where
  rowConstraints := by
    intro i hi c hc
    have gL : ((0 : Nat) + 1 == (fgTrace hash).rows.length) = true := rfl
    have hF : ((0 : Nat) == 0) = true := rfl
    have hi1 : i < 1 := hi
    clear hi
    simp only [relationalPredicateDesc, relationalConstraints] at hc
    interval_cases i
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt, gate, piFirst,
        commitLookup, hF, fgTrace, fgTf, fgPub, fgRow, envAt, VALUE_A, BLINDING_A,
        VALUE_B, BLINDING_B, DIFF, RESULT_BIT, RANGE_FLAG, EQ_FLAG, NEQ_FLAG, COMMIT_A, COMMIT_B,
        COMMIT_VERIFY, ZERO_PAD, List.getD_cons_zero, reduceIte, reduceCtorEq] <;>
      first
        | exact List.mem_cons.mpr (Or.inl rfl)
        | exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        | trivial
        | rfl
        | simp
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [relationalPredicateDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [rmemLog] at hop; simp at hop
  memDisciplined := by rw [rmemLog]; trivial
  memBalanced := by rw [rmemLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [rmemLog]; rfl
  mapTableFaithful := by rw [rmapLog]; rfl

/-- **Binding FIRES on the forgery, over a PERFECT injective `hash`.** `relational_commit_binds`
consumes the CR carrier (from `Function.Injective hash`) and forces the committed value/blinding columns
equal to the reference `(5, 0, 7, 1)` — the commitment binding is FULLY discharged even for the
forging trace. -/
theorem fgTrace_binds_fires (hinj : Function.Injective hash) :
    (envAt (fgTrace hash) 0).loc VALUE_A = 5 ∧ (envAt (fgTrace hash) 0).loc BLINDING_A = 0
      ∧ (envAt (fgTrace hash) 0).loc VALUE_B = 7 ∧ (envAt (fgTrace hash) 0).loc BLINDING_B = 1 :=
  relational_commit_binds (by simp [fgTrace]) (fgTf_chipSound hash) (fgTrace_satisfied2 hash)
    (collisionFree_of_injective hinj) 5 0 7 1 (by simp [fgTrace, fgPub]) (by simp [fgTrace, fgPub])

/-- **THE RESIDUAL SURVIVES THE CR CARRIER (the AIR-gap FALSE half).** A `Satisfied2` EQ proof
(`result_bit = 1`), over a PERFECT injective `hash` (so the binding is fully discharged and the
committed values are CR-bound to `value_a = 5`, `value_b = 7`), has `value_a ≠ value_b` — the accepting
proof's committed values VIOLATE the claimed EQ relation. So no `Satisfied2 + CollisionFree`-only
theorem can conclude "committed values satisfy the relation"; that residual is the MISSING in-circuit
constraint `diff − (value_a − value_b) = 0`, an EMIT/AIR fix, NOT a crypto-carrier discharge. -/
theorem fg_accepts_unequal_committed (hinj : Function.Injective hash) :
    Satisfied2 hash relationalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] (fgTrace hash)
      ∧ (envAt (fgTrace hash) 0).loc EQ_FLAG = 1
      ∧ (envAt (fgTrace hash) 0).loc RESULT_BIT = 1
      ∧ (envAt (fgTrace hash) 0).loc DIFF = 0
      ∧ (envAt (fgTrace hash) 0).loc VALUE_A = 5
      ∧ (envAt (fgTrace hash) 0).loc VALUE_B = 7
      ∧ (envAt (fgTrace hash) 0).loc VALUE_A ≠ (envAt (fgTrace hash) 0).loc VALUE_B := by
  obtain ⟨ha, _, hb, _⟩ := fgTrace_binds_fires hash hinj
  refine ⟨fgTrace_satisfied2 hash, ?_, ?_, ?_, ha, hb, ?_⟩
  · show (fgRow hash) EQ_FLAG = 1; rfl
  · show (fgRow hash) RESULT_BIT = 1; rfl
  · show (fgRow hash) DIFF = 0; rfl
  · rw [ha, hb]; decide

end ResidualMeasurement

/-! ## §6 — Axiom tripwires: every keystone is `#assert_axioms`-clean (carriers named). -/

#assert_axioms collisionFree_of_injective
#assert_axioms commit_opens
#assert_axioms relational_commit_binds
#assert_axioms cheatTrace_satisfied2
#assert_axioms hash0_not_collisionFree
#assert_axioms cheat_binds_would_be_false
#assert_axioms bwTf_chipSound
#assert_axioms bwTrace_satisfied2
#assert_axioms bwTrace_binds_fires
#assert_axioms bwTrace_binds_value
#assert_axioms fgTf_chipSound
#assert_axioms fgTrace_satisfied2
#assert_axioms fgTrace_binds_fires
#assert_axioms fg_accepts_unequal_committed

end Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2
