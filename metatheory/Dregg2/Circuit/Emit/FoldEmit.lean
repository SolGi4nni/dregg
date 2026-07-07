/-
# Dregg2.Circuit.Emit.FoldEmit — the emit-from-Lean twin of the DSL FOLD-step AIR.

## What this file IS

A faithful `EffectVmDescriptor2` (IR-v2, byte-pinned) for the attenuation FOLD step — the
production DSL circuit `circuit/src/dsl/fold.rs::fold_circuit_descriptor` ("dregg-fold-dsl-v2"),
which replaced the hand `FoldStarkAir`. The fold trace is a run of REMOVAL rows (`ROW_TYPE = 0`,
one per removed fact) closed by a SUMMARY row (`ROW_TYPE = 1`) that publishes the counts + the
root-transition hash. This descriptor declares, in the graduated IR-v2 grammar, EXACTLY the deployed
in-descriptor constraint set, with the Poseidon2 fact-commitment hash promoted to a REAL in-circuit
`Poseidon2Chip` lookup (the `hash_fact` leaf, an ARITY-7 chip absorb).

## The constraint map (deployed DSL constraint → emitted IR-v2 form)

* `row_type_binary`      `ROW_TYPE*(ROW_TYPE-1)=0`                 → Base `.gate`
* `hash_valid_binary`    `HASH_VALID*(HASH_VALID-1)=0`            → Base `.gate`
* `membership_root_matches` `(1-ROW_TYPE)*(MEMBERSHIP_ROOT-OLD_ROOT)=0` → Base `.gate`
* `removal_hash_required` `(1-ROW_TYPE)*(1-HASH_VALID)=0`         → Base `.gate`
* `fact_hash_correct`    `FACT_HASH = hash_fact(PRED,[t0,t1,t2])`  → **ARITY-7 Poseidon2 chip lookup**
* `old_root_consistent`  `OLD_ROOT = pi[0]` on EVERY row           → Base `.piBinding .first` + window constancy
* `new_root_consistent`  `NEW_ROOT = pi[1]` on EVERY row           → Base `.piBinding .first` + window constancy
* `removal_count_increment` `(1-ROW_TYPE)*(next[RC]-loc[RC+1])=0`  → **`.windowGate` (onTransition)**
* `root_transition_binding` `ROW_TYPE*(MEMBERSHIP_ROOT-pi[4])=0`   → pi4-carrier (`.piBinding .last` + constancy) + Base `.gate`
* boundary last `ROW_TYPE=1`                                        → Base `.boundary .last`
* boundary last `REMOVAL_COUNT=pi[2]`,`CHECK_COUNT=pi[3]`,`MEMBERSHIP_ROOT=pi[4]` → Base `.piBinding .last`

### The arity-7 fact-hash lookup (the family signature)

`hash_fact(pred,[t0,t1,t2])` (`circuit/src/poseidon2.rs:603`) is ONE Poseidon2 permutation over the
state `[pred, t0, t1, t2, 0, 0xFACF, 1, 0…]`, returning `state[0]`. In the chip it is the ARITY-7
absorb (`big = arity == 7`, `descriptor_ir2.rs:3355`): `big` seeds lanes 4/5/6 from the genuine
`in4/in5/in6`, so passing `[pred, t0, t1, t2, 0, 0xFACF, 1]` as the 7 inputs reproduces the fact
state EXACTLY — `chip_absorb_all_lanes(7, [pred,t0,t1,t2,0,0xFACF,1])[0] == hash_fact(pred,[t0,t1,t2])`
(KAT'd in the Rust gate). The `0`/`0xFACF`/`1` domain tags ride as explicit CONSTANT inputs of the
tuple — no `is_fact` bus row, no chip extension. A forged `FACT_HASH` names a digest no genuine chip
row serves → UNSAT.

## Off-descriptor NAMED carriers (kept off-AIR, faithful to the deployed DSL descriptor)

The deployed AIR does NOT reconstruct these in-circuit; they ride as native/host computations and are
preserved off-descriptor here too:
  * the Merkle membership of each removed fact (`RemovedFact::verify_membership`, native trace-gen; the
    AIR only binds `membership_root == old_root` on removal rows);
  * the variable-length `root_transition_hash` sponge (`compute_root_transition_hash`, native); `pi[4]`
    is a witnessed value the summary row binds;
  * the two host validation gates `delta_nonempty` (prove wrapper `fold.rs:839`) and
    `checks_commitment_zero_when_no_checks` (verify wrapper `fold.rs:859`); `pi[5]` (checks_narrow) is
    declared but unconstrained in-descriptor, exactly as deployed.

## One documented completeness-narrowing (not a soundness gap)

An IR-v2 chip `.lookup` fires on EVERY row (it cannot be selector-gated), whereas the deployed
`fact_hash_correct` is gated by `is_removal`. The emitted lookup therefore ALSO constrains
`FACT_HASH` on the non-removal (summary/pad) rows to the genuine `hash_fact` of that row's fact
columns. The honest producer fills `FACT_HASH = hash_fact(PRED,terms)` on EVERY row (a benign
strengthening — on the summary row PRED/terms are 0, so `FACT_HASH = hash_fact(0,[0,0,0])`); the
removal-row tooth is unchanged and STRICTLY biting.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + genuinely-proven, non-vacuous
semantic lemmas over the gate bodies (`#assert_axioms ⊆ {}`, pure `mul_eq_zero`/`omega`). NEW file;
imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.FoldEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup WindowExpr WindowConstraint TableId
   chipLookupTuple siteLaneCols CHIP_RATE CHIP_OUT_LANES emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (main width 21).

Columns 0..12 are the deployed DSL layout (`fold.rs::col`); 13 is the pi[4]-carrier aux; 14..20 are
the 7 exposed chip lanes 1..7 of the fact-hash absorb. -/

def ROW_TYPE : Nat := 0
def FACT_HASH : Nat := 1
def MEMBERSHIP_ROOT : Nat := 2
def OLD_ROOT : Nat := 3
def NEW_ROOT : Nat := 4
def REMOVAL_COUNT : Nat := 5
def CHECK_COUNT : Nat := 6
def FACT_PRED : Nat := 7
def FACT_TERM0 : Nat := 8
def FACT_TERM1 : Nat := 9
def FACT_TERM2 : Nat := 10
def HASH_VALID : Nat := 11
def REMOVAL_COUNT_PLUS_ONE : Nat := 12
/-- Aux carrier pinned to `pi[4]` (the root-transition hash) on every row — the PI leaf the gate
grammar lacks, so the summary-row `ROW_TYPE*(MEMBERSHIP_ROOT-pi[4])` gate reads a column. -/
def PI4_CARRIER : Nat := 13
/-- Base of the 7 fact-hash chip lanes (1..7); lane 0 = out0 = `FACT_HASH`. -/
def FACT_LANE_BASE : Nat := 14

def FOLD_WIDTH : Nat := 21

/-! ## §2 — Public inputs (count 6, deployed layout). -/
def PI_OLD_ROOT : Nat := 0
def PI_NEW_ROOT : Nat := 1
def PI_REMOVAL_COUNT : Nat := 2
def PI_CHECK_COUNT : Nat := 3
def PI_TRANSITION_HASH : Nat := 4
def PI_CHECKS_NARROW : Nat := 5
def FOLD_PI_COUNT : Nat := 6

/-! ## §3 — The gate bodies, as NAMED `EmittedExpr`/`WindowExpr` (so §5 can prove teeth on them). -/

/-- `x*(x-1)` — the binary-selector body (`ROW_TYPE`, `HASH_VALID`). -/
def binaryBody (c : Nat) : EmittedExpr :=
  .mul (.var c) (.add (.var c) (.const (-1)))

/-- `(1-ROW_TYPE)*(MEMBERSHIP_ROOT-OLD_ROOT)` — membership_root_matches (gated on removal rows). -/
def mrmBody : EmittedExpr :=
  .mul (.add (.const 1) (.mul (.const (-1)) (.var ROW_TYPE)))
       (.add (.var MEMBERSHIP_ROOT) (.mul (.const (-1)) (.var OLD_ROOT)))

/-- `(1-ROW_TYPE)*(1-HASH_VALID)` — removal_hash_required (a removal row must carry a valid hash). -/
def removalHashBody : EmittedExpr :=
  .mul (.add (.const 1) (.mul (.const (-1)) (.var ROW_TYPE)))
       (.add (.const 1) (.mul (.const (-1)) (.var HASH_VALID)))

/-- `ROW_TYPE*(MEMBERSHIP_ROOT-PI4_CARRIER)` — root_transition_binding (gated on summary rows;
`PI4_CARRIER` is pinned to `pi[4]` by §4's last-pin + constancy). -/
def rootTransBody : EmittedExpr :=
  .mul (.var ROW_TYPE) (.add (.var MEMBERSHIP_ROOT) (.mul (.const (-1)) (.var PI4_CARRIER)))

/-- The window body `loc c - nxt c` — a column's cross-row constancy. -/
def constancyBody (c : Nat) : WindowExpr :=
  .add (.loc c) (.mul (.const (-1)) (.nxt c))

/-- The removal_count_increment window body `(1-loc ROW_TYPE)*(nxt REMOVAL_COUNT - loc REMOVAL_COUNT_PLUS_ONE)`. -/
def removalIncrBody : WindowExpr :=
  .mul (.add (.const 1) (.mul (.const (-1)) (.loc ROW_TYPE)))
       (.add (.nxt REMOVAL_COUNT) (.mul (.const (-1)) (.loc REMOVAL_COUNT_PLUS_ONE)))

/-- The `ROW_TYPE=1` last-row boundary body `ROW_TYPE - 1`. -/
def lastSummaryBody : EmittedExpr := .add (.var ROW_TYPE) (.const (-1))

/-! ## §4 — The fact-hash chip lookup (arity-7 leaf). -/

/-- `fact_hash_correct` as the ARITY-7 `Poseidon2Chip` absorb of `[PRED,t0,t1,t2, 0, 0xFACF, 1]`,
binding `out0 = FACT_HASH` and lanes 1..7 to `FACT_LANE_BASE..+6`. `0xFACF = 64207` (`FACT_MARK`). -/
def factHashLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple
      [.var FACT_PRED, .var FACT_TERM0, .var FACT_TERM1, .var FACT_TERM2,
       .const 0, .const 64207, .const 1]
      FACT_HASH (siteLaneCols FACT_LANE_BASE)⟩

/-! ## §5 — Assemble the descriptor. -/

def foldConstraints : List VmConstraint2 :=
  [ -- per-row binary + gated-equality gates
    .base (.gate (binaryBody ROW_TYPE))                    -- row_type_binary
  , .base (.gate (binaryBody HASH_VALID))                  -- hash_valid_binary
  , .base (.gate mrmBody)                                  -- membership_root_matches
  , .base (.gate removalHashBody)                          -- removal_hash_required
  , factHashLookup                                         -- fact_hash_correct (arity-7 chip)
    -- old/new root: first-row PI pin + every-row constancy ⇒ `= pi[k]` on every row
  , .base (.piBinding VmRow.first OLD_ROOT PI_OLD_ROOT)
  , .windowGate ⟨constancyBody OLD_ROOT, true⟩
  , .base (.piBinding VmRow.first NEW_ROOT PI_NEW_ROOT)
  , .windowGate ⟨constancyBody NEW_ROOT, true⟩
    -- removal-count increment (cross-row transition)
  , .windowGate ⟨removalIncrBody, true⟩
    -- pi4 carrier (last-pin + constancy) then the summary-gated root-transition binding
  , .base (.piBinding VmRow.last PI4_CARRIER PI_TRANSITION_HASH)
  , .windowGate ⟨constancyBody PI4_CARRIER, true⟩
  , .base (.gate rootTransBody)                            -- root_transition_binding
    -- last-row boundaries
  , .base (.boundary VmRow.last lastSummaryBody)           -- ROW_TYPE == 1
  , .base (.piBinding VmRow.last REMOVAL_COUNT PI_REMOVAL_COUNT)
  , .base (.piBinding VmRow.last CHECK_COUNT PI_CHECK_COUNT)
  , .base (.piBinding VmRow.last MEMBERSHIP_ROOT PI_TRANSITION_HASH) ]

/-- **`foldDesc`** — the FOLD-step descriptor (name `dregg-fold-step-v2`). Tables `[]`: the Poseidon2
chip is Presence-detected from the fact-hash lookup (as the `merkle-membership` / `node8` descriptors
leave it). -/
def foldDesc : EffectVmDescriptor2 :=
  { name        := "dregg-fold-step-v2"
  , traceWidth  := FOLD_WIDTH
  , piCount     := FOLD_PI_COUNT
  , tables      := []
  , constraints := foldConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §6 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/fold_emit_gate.rs` (`GOLDEN_JSON`), decoded there via `parse_vm_descriptor2`,
asserted equal to an independent Rust builder, and proven through the REAL prover. A drift on either
side breaks THIS `#guard` (Lean) or the Rust `assert_eq!` — neither can silently diverge. -/

#guard emitVmJson2 foldDesc ==
  "{\"name\":\"dregg-fold-step-v2\",\"ir\":2,\"trace_width\":21,\"public_input_count\":6,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20}]},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":0},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":3}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":1},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":12}}}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":13,\"pi_index\":4},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":13}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":5,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":6,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":4}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §7 — Shape tripwires. -/
#guard foldDesc.traceWidth == FOLD_WIDTH
#guard foldDesc.piCount == FOLD_PI_COUNT
#guard foldConstraints.length == 17
#guard (foldConstraints.filter (fun c => match c with | .windowGate _ => true | _ => false)).length == 4
#guard (foldConstraints.filter (fun c => match c with | .lookup _ => true | _ => false)).length == 1
#guard (chipLookupTuple [.var FACT_PRED, .var FACT_TERM0, .var FACT_TERM1, .var FACT_TERM2,
          .const 0, .const 64207, .const 1] FACT_HASH (siteLaneCols FACT_LANE_BASE)).length
        == CHIP_RATE + 1 + CHIP_OUT_LANES

/-! ## §8 — The teeth (genuinely-proven, non-vacuous). -/

/-- **membership_root_matches tooth.** Over ℤ (integral domain) the gate body is zero EXACTLY when
the row is a summary row (`ROW_TYPE = 1`) OR the membership root equals the old root — the emitted
face of `(1-ROW_TYPE)*(MEMBERSHIP_ROOT-OLD_ROOT)=0`. A removal row (`ROW_TYPE=0`) with
`MEMBERSHIP_ROOT ≠ OLD_ROOT` violates it. -/
theorem mrm_body_zero_iff (a : Assignment) :
    mrmBody.eval a = 0 ↔ a ROW_TYPE = 1 ∨ a MEMBERSHIP_ROOT = a OLD_ROOT := by
  simp only [mrmBody, EmittedExpr.eval]
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- **root_transition_binding tooth.** Zero EXACTLY when the row is a removal row (`ROW_TYPE=0`) OR
`MEMBERSHIP_ROOT = PI4_CARRIER` (= `pi[4]`). A summary row that publishes a root-transition hash
disagreeing with `pi[4]` violates it. -/
theorem root_trans_body_zero_iff (a : Assignment) :
    rootTransBody.eval a = 0 ↔ a ROW_TYPE = 0 ∨ a MEMBERSHIP_ROOT = a PI4_CARRIER := by
  simp only [rootTransBody, EmittedExpr.eval]
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- **binary-selector tooth.** `x*(x-1)=0 ↔ x=0 ∨ x=1`. -/
theorem binary_body_zero_iff (c : Nat) (a : Assignment) :
    (binaryBody c).eval a = 0 ↔ a c = 0 ∨ a c = 1 := by
  simp only [binaryBody, EmittedExpr.eval]
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

-- Non-vacuity witnesses: each gate ACCEPTS a satisfying row and REJECTS a violating one.
-- membership_root_matches: summary row (ROW_TYPE=1) always OK; removal row with MR≠OR fails.
#guard decide (mrmBody.eval (fun i => if i = ROW_TYPE then 1 else 0) = 0)
#guard decide (mrmBody.eval (fun i => if i = MEMBERSHIP_ROOT ∨ i = OLD_ROOT then 5 else 0) = 0)
#guard decide (¬ (mrmBody.eval (fun i => if i = MEMBERSHIP_ROOT then 5 else 0) = 0))
-- root_transition_binding: removal row OK; summary row with MR≠carrier fails.
#guard decide (rootTransBody.eval (fun _ => 0) = 0)
#guard decide (¬ (rootTransBody.eval (fun i => if i = ROW_TYPE ∨ i = MEMBERSHIP_ROOT then 1 else 0) = 0))
-- binary: 0 and 1 accepted, 2 rejected.
#guard decide ((binaryBody ROW_TYPE).eval (fun _ => 0) = 0)
#guard decide ((binaryBody ROW_TYPE).eval (fun _ => 1) = 0)
#guard decide (¬ ((binaryBody ROW_TYPE).eval (fun _ => 2) = 0))

/-- **removal_count_increment tooth** (the cross-row window). On a removal row (`loc ROW_TYPE = 0`)
the body forces `nxt REMOVAL_COUNT = loc REMOVAL_COUNT_PLUS_ONE`; on a summary row it vanishes. -/
theorem removal_incr_body_zero_iff (env : VmRowEnv) :
    removalIncrBody.eval env = 0 ↔
      env.loc ROW_TYPE = 1 ∨ env.nxt REMOVAL_COUNT = env.loc REMOVAL_COUNT_PLUS_ONE := by
  simp only [removalIncrBody, WindowExpr.eval]
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

-- window non-vacuity: a removal→removal step with the right increment is OK; a wrong one fails.
#guard decide (removalIncrBody.eval
  ⟨fun i => if i = REMOVAL_COUNT_PLUS_ONE then 2 else 0, fun i => if i = REMOVAL_COUNT then 2 else 0, fun _ => 0⟩ = 0)
#guard decide (¬ (removalIncrBody.eval
  ⟨fun i => if i = REMOVAL_COUNT_PLUS_ONE then 2 else 0, fun i => if i = REMOVAL_COUNT then 3 else 0, fun _ => 0⟩ = 0))

#assert_axioms mrm_body_zero_iff
#assert_axioms root_trans_body_zero_iff
#assert_axioms binary_body_zero_iff
#assert_axioms removal_incr_body_zero_iff

end Dregg2.Circuit.Emit.FoldEmit
