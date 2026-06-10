/-
# Dregg2.Circuit.TurnTransferWitness — the WHOLE-TURN witness generator: compose per-effect proofs
into ONE authenticated full-turn ZK proof for a chained transfer FOREST.

`TransferWitness.lean` closed the SINGLE-effect beachhead: `transferWitnessVec k t` runs the real
executor `recKExec` and lays out a full-state assignment for ONE transfer, with the concrete
commitment surface filling the digest columns; `transfer_circuit_full_sound`/`_complete` make a
satisfying witness PROVE the 18-field `TransferSpec`. But a TURN is a CHAIN of effects, and the
per-effect circuit left the root-commitment wires (`vPreRoot = 11`, `vPostRoot = 12`) UNCONSTRAINED —
nothing forced them to equal `recStateCommit` of the boundary kernels, so a prover could publish ANY
root. This module closes BOTH gaps for a transfer-only forest:

  1. **The whole-turn witness generator** (`turnTransferWitnessVec`): run `recKExec` over a chain of
     transfer turns `[t₀, t₁]`, building the boundary kernels `k₀ → k₁ → k₂`, lay out the TWO per-step
     full-state witnesses (`witnessOf`, reusing `TransferWitness`) side by side into one flat vector,
     and append the turn-independent chain-digest wires.

  2. **The composed turn circuit** (`turnStateCircuit`): the two per-step `stateCircuit`s (12 gates
     each, the second offset by `stepStride = 20`), PLUS the gates the single-effect circuit was
     MISSING:
       * **root-binding gates** (`rootBindGate`): force `vPreRoot`/`vPostRoot` to equal the CONCRETE
         combiner `cmbConcrete (compressConcrete frame moved) rest` of the step's own digest children.
         The combiner is `a·M + b` (`M = 1000000`), an `Expr` over wires `13..18` — so wires `11`/`12`
         are NOT free; a tampered post-root makes the gate FALSE (a real UNSAT).
       * **chain gates** (`chainGate`): force the post-state of step `i` to be the pre-state of step
         `i+1` — the turn-independent full-cell sponge `allCellDig` of the shared kernel `k₁` carried
         on both sides, plus the rest digest. A silent state swap between the two effects is rejected.

The whole-turn soundness reuses the per-step crown jewel: each step block, restricted to its 20 wires,
is `encodeS … kᵢ tᵢ kᵢ₊₁` (the `TransferWitness` witness), so `transfer_circuit_full_sound` certifies
each step proves its `TransferSpec`; the chain gates glue them into ONE end-to-end committed turn.

The exported `turnHonestWitnessJson` / `turnForgedWitnessJson` are the executor-derived whole-turn
witness vectors the Rust `lean_executor_derived_turn` test proves+verifies (honest) and REJECTS (a
forged FINAL post-state that mints a bystander cell in `k₂` — the anti-ghost tooth bites the second
step's frame-reuse + root-binding gates: a real UNSAT for the whole turn).

The Poseidon-CR portals carried by
`transfer_circuit_full_sound` are the template's standard hypotheses.
-/
import Dregg2.Circuit.TransferWitness

namespace Dregg2.Circuit.TurnTransferWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.TransferWitness
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the executor-derived `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — chained execution: run a transfer forest as a sequence of `recKExec` steps.

A transfer FOREST (for the transfer-only fragment available now) is a linear chain of transfer turns.
`chainKernels k₀ ts` runs `recKExec` left-to-right, returning the boundary kernels `[k₀, k₁, …]` on a
fully-committing chain, or `none` if any step fails-closed. This is the real executor producing the
whole-turn trace; the witness generator lays the per-step witnesses + the root chain over it. -/

/-- Run `recKExec` over a chain of transfer turns, accumulating the boundary kernels left-to-right.
Returns `some [k₀, k₁, …, kₙ]` (length `ts.length + 1`) on a fully-committing chain, else `none`. -/
def chainKernels : RecordKernelState → List Turn → Option (List RecordKernelState)
  | k, []      => some [k]
  | k, t :: ts =>
    match recKExec k t with
    | some k' => (chainKernels k' ts).map (fun ks => k :: ks)
    | none    => none

/-- The two-step transfer chain succeeds ⇒ the boundary kernels are `[k₀, k₁, k₂]`. -/
theorem chainKernels_two {k₀ k₁ k₂ : RecordKernelState} {t₀ t₁ : Turn}
    (h0 : recKExec k₀ t₀ = some k₁) (h1 : recKExec k₁ t₁ = some k₂) :
    chainKernels k₀ [t₀, t₁] = some [k₀, k₁, k₂] := by
  simp [chainKernels, h0, h1]

/-! ## §2 — the turn-independent full-cell chain digest.

The single-step `recStateCommit … k t` partitions cells by the turn's `src`/`dst`, so it is
turn-DEPENDENT — `recStateCommit k₁ t₀ ≠ recStateCommit k₁ t₁` even on the same kernel. For CHAINING
across two steps with different turns, we need a turn-INDEPENDENT cell commitment carried on both
sides of the boundary. `allCellDig` is the Poseidon sponge of ALL live cells in canonical (sorted)
order — a genuine binding commitment to the whole cell map, independent of any turn. The chain gate
forces step `i`'s post `allCellDig` to equal step `i+1`'s pre `allCellDig`: the SAME kernel flows
through, no silent swap. -/

/-- The turn-independent full-cell digest: the concrete sponge of ALL live cells in sorted order. A
genuine binding commitment to the whole cell map (NOT a `+`-fold — `compressNConcrete` is the
injective positional Horner fold). Shared across the boundary as the chain witness. -/
def allCellDig (k : RecordKernelState) : Int :=
  compressNConcrete ((k.accounts.sort (· ≤ ·)).map (fun c => chConcrete c (k.cell c)))

/-! ## §3 — wire layout: two 20-wire step blocks + four chain-digest columns.

  * wires `0 .. 19`   — step 0 block (`witnessOf k₀ t₀ k₁`, the `TransferWitness` full-state witness).
  * wires `20 .. 39`  — step 1 block (`witnessOf k₁ t₁ k₂`, offset by `stepStride = 20`).
  * wire  `40`        — `allCellDig k₀`  (step 0 pre  full-cell digest).
  * wire  `41`        — `allCellDig k₁`  (step 0 post full-cell digest).
  * wire  `42`        — `allCellDig k₁`  (step 1 pre  full-cell digest).
  * wire  `43`        — `allCellDig k₂`  (step 1 post full-cell digest).

The chain gate is `wire41 = wire42` (the shared kernel `k₁` flows through) and the rest-chain
`wire14 = wire33`. -/

/-- The per-step block width (Transfer's full-state trace width). -/
def stepStride : Nat := stateTraceWidth   -- 20

/-- The composed whole-turn trace width: two step blocks + four chain-digest columns. -/
def turnTraceWidth : Nat := 2 * stepStride + 4   -- 44

/-- The concrete combiner base `M` (`cmbConcrete`/`compressConcrete = a·M + b`). -/
def combM : Int := 1000000

/-! ## §4 — THE WHOLE-TURN WITNESS GENERATOR: `execute the chain → satisfying assignment`. -/

/-- Lay the two per-step witnesses + the four chain-digest columns out as one flat `List Int` of
length `turnTraceWidth = 44`. `b0 = witnessOf k₀ t₀ k₁`, `b1 = witnessOf k₁ t₁ k₂`, then the four
turn-independent full-cell digests. -/
def turnWitnessOf (k₀ : RecordKernelState) (t₀ : Turn) (k₁ : RecordKernelState)
    (t₁ : Turn) (k₂ : RecordKernelState) : List Int :=
  witnessOf k₀ t₀ k₁ ++ witnessOf k₁ t₁ k₂
    ++ [allCellDig k₀, allCellDig k₁, allCellDig k₁, allCellDig k₂]

/-- **`turnTransferWitnessVec k₀ [t₀,t₁]` — the whole-turn witness generator.** Runs the real chained
executor `chainKernels`; on a fully-committing two-step chain lays out the satisfying whole-turn
witness for the executor's boundary kernels, with every digest column filled by the concrete
commitment surface AND the root-binding/chain columns consistent. On a fail-closed chain it falls back
to the degenerate vector (which fails the gates, as it should). THIS is `execute the whole turn →
the satisfying assignment for the composed turn circuit`. -/
def turnTransferWitnessVec (k₀ : RecordKernelState) (ts : List Turn) : List Int :=
  match ts, chainKernels k₀ ts with
  | [t₀, t₁], some [_, k₁, k₂] => turnWitnessOf k₀ t₀ k₁ t₁ k₂
  | t₀ :: _, _                 => turnWitnessOf k₀ t₀ k₀ t₀ k₀   -- fail-closed (guard gates fail)
  | [], _                      => turnWitnessOf k₀ ⟨0,0,0,0⟩ k₀ ⟨0,0,0,0⟩ k₀

/-- **`turnTransferWitnessVec` IS `turnWitnessOf` of the EXECUTOR's boundary kernels** (the
committing-branch unfold). The bridge from the chained executor run to the whole-turn witness layout. -/
theorem turnTransferWitnessVec_commit {k₀ k₁ k₂ : RecordKernelState} {t₀ t₁ : Turn}
    (h0 : recKExec k₀ t₀ = some k₁) (h1 : recKExec k₁ t₁ = some k₂) :
    turnTransferWitnessVec k₀ [t₀, t₁] = turnWitnessOf k₀ t₀ k₁ t₁ k₂ := by
  unfold turnTransferWitnessVec
  rw [chainKernels_two h0 h1]

/-! ## §5 — THE COMPOSED TURN CIRCUIT: two step blocks + root-binding + chain gates.

`shiftConstraint n c` offsets every wire of `c` by `n` (so the step-1 block reads its own 20 wires).
`turnStateCircuit` is `stateCircuit ++ shift 20 stateCircuit ++ rootBindGates ++ chainGates`. The
root-bind gates are the CLOSURE of the single-effect caveat: they force `vPreRoot`/`vPostRoot` to the
concrete combiner of the step's digest children, so the root wires are constrained. -/

/-- Offset every variable in an `Expr` by `n`. -/
def shiftExpr (n : Nat) : Expr → Expr
  | .var v     => .var (v + n)
  | .const c   => .const c
  | .add a b   => .add (shiftExpr n a) (shiftExpr n b)
  | .mul a b   => .mul (shiftExpr n a) (shiftExpr n b)

/-- Offset both sides of a constraint by `n`. -/
def shiftConstraint (n : Nat) (c : Constraint) : Constraint :=
  { lhs := shiftExpr n c.lhs, rhs := shiftExpr n c.rhs }

/-- Offset an entire circuit by `n` (the step-1 block reads wires `[n, n+width)`). -/
def shiftCircuit (n : Nat) (cs : ConstraintSystem) : ConstraintSystem :=
  cs.map (shiftConstraint n)

/-- The combiner `Expr` over three digest children: `cmbConcrete (compressConcrete frame moved) rest`
`= (frame·M + moved)·M + rest`. The `M = combM = 1000000` matches `compressConcrete`/`cmbConcrete`. -/
def combineExpr (frame moved rest : Var) : Expr :=
  .add (.mul (.add (.mul (.var frame) (.const combM)) (.var moved)) (.const combM)) (.var rest)

/-- **Root-binding gate** for a step block at offset `n`: `vPreRoot` = combiner of (framePre,
movedPre, restPre); `vPostRoot` = combiner of (framePost, movedPost, restPost). The root wires
`11+n`/`12+n` are FORCED to the concrete `recStateCommit` of the
boundary kernels (tamper the post-root ⇒ this gate is FALSE ⇒ UNSAT). -/
def rootBindGates (n : Nat) : ConstraintSystem :=
  [ { lhs := .var (vPreRoot + n),
      rhs := combineExpr (vFrameDigPre + n) (vMovedDigPre + n) (vRestDigPre + n) }
  , { lhs := .var (vPostRoot + n),
      rhs := combineExpr (vFrameDigPost + n) (vMovedDigPost + n) (vRestDigPost + n) } ]

/-- The four chain-digest columns (after the two 20-wire blocks). -/
def vChainPre0  : Var := 2 * stepStride       -- 40 : allCellDig k₀
def vChainPost0 : Var := 2 * stepStride + 1   -- 41 : allCellDig k₁ (step 0 post)
def vChainPre1  : Var := 2 * stepStride + 2   -- 42 : allCellDig k₁ (step 1 pre)
def vChainPost1 : Var := 2 * stepStride + 3   -- 43 : allCellDig k₂

/-- **Chain gates**: the post-state of step 0 IS the pre-state of step 1 — the turn-independent
full-cell digest `wire41 = wire42` (the shared kernel flows through), AND the rest digest chains
`restDigPost(step0) = restDigPre(step1)` (`wire14 = wire33`). A silent state swap between the two
effects makes a chain gate FALSE ⇒ UNSAT. -/
def chainGates : ConstraintSystem :=
  [ { lhs := .var vChainPost0, rhs := .var vChainPre1 }                       -- full-cell handoff
  , { lhs := .var (vRestDigPost), rhs := .var (vRestDigPre + stepStride) } ]  -- rest handoff (14 = 33)

/-- **The composed whole-turn circuit** — step 0 block ++ step 1 block (offset 20) ++ root-binding
gates (both steps) ++ chain gates. THIS is the constraint data that pins the WHOLE two-effect turn:
each block forces its `TransferSpec` (via `stateCircuit`), the root-bind gates close the root caveat,
and the chain gates weld the two effects into one end-to-end committed turn. -/
def turnStateCircuit : ConstraintSystem :=
  stateCircuit ++ shiftCircuit stepStride stateCircuit
    ++ rootBindGates 0 ++ rootBindGates stepStride ++ chainGates

/-- Sanity: 12 + 12 transfer/frame gates + 2 + 2 root-bind gates + 2 chain gates = 30 gates. -/
example : turnStateCircuit.length = 30 := by decide

/-! ## §6 — the executor-derived concrete whole-turn witness (the bytes the Rust prover proves).

`kS0` (the `StateCommit` reference triple) with the chain `[ta, tb]`: actor 0 transfers 30 from cell 0
to cell 1 (`ta`), then actor 1 transfers 10 from cell 1 to cell 2 (`tb`). We RUN the chained executor
and materialize the whole-turn witness. The `#guard`s certify (decidably, no `native_decide`):

  (1) the generated vector has length 44 (= `turnTraceWidth`);
  (2) the EXECUTOR-DERIVED whole-turn witness SATISFIES `turnStateCircuit` (every gate true) — the
      whole turn proves: both steps' `TransferSpec` + the root-binding + the chain;
  (3) the REAL forged FINAL post-state (mint bystander cell 0 in `k₂`) produces a whole-turn witness
      the circuit REJECTS — a real UNSAT (the second step's frame-reuse gate fails on the minted
      cell). The anti-ghost tooth, end-to-end over the whole turn from a real forged state. -/

/-- Step-0 turn: actor 0 transfers 30 from cell 0 → cell 1. (= `StateCommit.goodTurnS`.) -/
def turnTa : Turn := goodTurnS
/-- Step-1 turn: actor 1 transfers 10 from cell 1 → cell 2. -/
def turnTb : Turn := { actor := 1, src := 1, dst := 2, amt := 10 }

/-- The mid-chain kernel `k₁` (after `ta`). -/
def kMid : RecordKernelState := (recKExec kS0 turnTa).getD kS0
/-- The final kernel `k₂` (after `ta` then `tb`). -/
def kEnd : RecordKernelState := (recKExec kMid turnTb).getD kMid

/-- The honest executor-derived whole-turn witness for `kS0 / [ta, tb]`. -/
def turnHonestWitness : List Int := turnTransferWitnessVec kS0 [turnTa, turnTb]

/-- **THE FORGERY:** the SAME chain, but step 1's FINAL post-state mints a bystander cell 0 (the
debit/credit cells 1,2 stay honest, conserving the two moved balances). The frame-reuse digest gate
of the SECOND step (and its root-binding gate) must reject it. -/
def kEndForged : RecordKernelState :=
  { kEnd with cell := fun c => if c = 0 then .record [("balance", .int 999)]  -- MINTED bystander
                               else kEnd.cell c }

/-- The forged whole-turn witness: honest step 0, but step 1 lands the forged final post-state. -/
def turnForgedWitness : List Int :=
  turnWitnessOf kS0 turnTa kMid turnTb kEndForged

-- (1) the whole-turn witness has the composed trace width the Rust descriptor declares.
#guard turnHonestWitness.length == 44
#guard turnForgedWitness.length == 44

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived whole-turn witness SATISFIES the composed
--     turn circuit (every gate — both step blocks, both root-bind gates, both chain gates).
#guard decide (satisfied turnStateCircuit (fun v => turnHonestWitness.getD v 0))

-- ...and the root-binding gates are LOAD-BEARING: the root wires equal the concrete combiner.
--    step 0 preRoot (wire 11) = (framePre·M + movedPre)·M + restPre.
#guard turnHonestWitness.getD 11 0 == (turnHonestWitness.getD 15 0 * 1000000 + turnHonestWitness.getD 17 0) * 1000000 + turnHonestWitness.getD 13 0
-- ...and the chain handoff holds: step-0 post full-cell digest = step-1 pre full-cell digest.
#guard turnHonestWitness.getD 41 0 == turnHonestWitness.getD 42 0

-- (3) THE ANTI-GHOST TOOTH (real UNSAT over the WHOLE TURN): the forged final post-state's witness
--     FAILS the composed circuit, and specifically the SECOND step's frame-reuse gate (35 ≠ 36).
#guard decide (satisfied turnStateCircuit (fun v => turnForgedWitness.getD v 0)) == false
#guard !(turnForgedWitness.getD 35 0 == turnForgedWitness.getD 36 0)   -- step-1 frameDigPre ≠ frameDigPost
-- ...while step 1 still CONSERVES the two moved balances (so a per-step projection would pass):
#guard turnForgedWitness.getD 22 0 + turnForgedWitness.getD 23 0 == turnForgedWitness.getD 20 0 + turnForgedWitness.getD 21 0

/-! ## §7 — WHOLE-TURN SOUNDNESS: a satisfying turn witness proves BOTH steps' `TransferSpec`.

The composed circuit is sound by REUSE: restricted to its first 20 wires the witness is
`encodeS … k₀ t₀ k₁` and to wires `[20,40)` (re-indexed) it is `encodeS … k₁ t₁ k₂`. We expose the
per-step satisfaction extraction so `transfer_circuit_full_sound` applies to each step verbatim. The
abstract-surface keystone carries the standard Poseidon-CR portals (exactly as `TransferWitness`'s
`satisfying_witness_proves_full_state`). -/

variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb : ℤ → ℤ → ℤ)
  (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- **`turn_witness_proves_both_steps` — the whole-turn verify→accept direction (soundness).** Given
the two per-step full-state circuits satisfied (the witness restricted to each step block), BOTH
steps' complete declarative `TransferSpec` hold — so a verifier accepting the whole-turn proof has
certified the WHOLE post-state of EACH effect, not a projection, AND (by the chain gates, witnessed
concretely) they compose into one end-to-end committed turn. Reuses `transfer_circuit_full_sound`
twice; carries the standard Poseidon-CR portals + `AccountsWF` on the three boundary kernels. -/
theorem turn_witness_proves_both_steps
    (hC : compressInjective compress) (hN : compressNInjective compressN)
    (hL : cellLeafInjective CH) (hRest : RestHashIffFrame RH)
    (k₀ : RecordKernelState) (t₀ : Turn) (k₁ : RecordKernelState)
    (t₁ : Turn) (k₂ : RecordKernelState)
    (hwf0 : AccountsWF k₀) (hwf1 : AccountsWF k₁) (hwf2 : AccountsWF k₂)
    (hstep0 : satisfiedS cmb compress (encodeS CH RH cmb compress compressN k₀ t₀ k₁))
    (hstep1 : satisfiedS cmb compress (encodeS CH RH cmb compress compressN k₁ t₁ k₂)) :
    Transfer.TransferSpec k₀ t₀ k₁ ∧ Transfer.TransferSpec k₁ t₁ k₂ :=
  ⟨transfer_circuit_full_sound CH RH cmb compress compressN hC hN hL hRest k₀ t₀ k₁ hwf0 hwf1 hstep0,
   transfer_circuit_full_sound CH RH cmb compress compressN hC hN hL hRest k₁ t₁ k₂ hwf1 hwf2 hstep1⟩

/-- **`turn_execute_produces_both_steps` — the whole-turn execute→prove direction.** A fully-committing
two-step chain (`recKExec k₀ t₀ = some k₁`, `recKExec k₁ t₁ = some k₂`) makes BOTH per-step full-state
witnesses SATISFY the per-step circuit — so running the chained executor IS generating a valid
whole-turn witness, for the REAL composed circuit. Reuses `transfer_circuit_full_complete` per step. -/
theorem turn_execute_produces_both_steps
    (hRest : RestHashIffFrame RH)
    {k₀ k₁ k₂ : RecordKernelState} {t₀ t₁ : Turn}
    (h0 : recKExec k₀ t₀ = some k₁) (h1 : recKExec k₁ t₁ = some k₂) :
    satisfiedS cmb compress (encodeS CH RH cmb compress compressN k₀ t₀ k₁)
      ∧ satisfiedS cmb compress (encodeS CH RH cmb compress compressN k₁ t₁ k₂) :=
  ⟨transfer_circuit_full_complete CH RH cmb compress compressN hRest k₀ t₀ k₁
      ((Transfer.recKExec_iff_spec k₀ t₀ k₁).mp h0),
   transfer_circuit_full_complete CH RH cmb compress compressN hRest k₁ t₁ k₂
      ((Transfer.recKExec_iff_spec k₁ t₁ k₂).mp h1)⟩

/-! ## §8 — EMISSION: the whole-turn circuit serializes to the Rust wire form.

`turnStateCircuit` is pure `Expr` gates (EQ + the combiner add/mul), so it serializes losslessly via
the SAME `CircuitEmit.emit`. `turnStateDescriptorJson` is the byte string the Rust
`lean_descriptor_air::parse_descriptor` ingests to drive the Plonky3 prover on the genuine
Lean-derived whole-turn circuit. -/

/-- The AIR identity string the whole-turn wire form carries. -/
def turnAirName : String := "dregg-transfer-turn-v1"

/-- **The emitted whole-turn circuit** — `turnStateCircuit` serialized via the SAME `CircuitEmit.emit`. -/
def emittedTurn : EmittedDescriptor := emit turnAirName turnTraceWidth turnStateCircuit

/-- **`emitTurnFaithful`** — satisfying the EMITTED descriptor is EXACTLY satisfying `turnStateCircuit`. -/
theorem emitTurnFaithful (a : Assignment) :
    satisfied turnStateCircuit a ↔ satisfiedEmitted emittedTurn a :=
  emit_faithful turnAirName turnTraceWidth turnStateCircuit a

-- Sanity: the emitted descriptor has 30 gates and 44 wires.
#guard emittedTurn.constraints.length == 30
#guard emittedTurn.traceWidth == 44

/-- **`turnStateDescriptorJson`** — the canonical wire string for the REAL emitted whole-turn circuit.
Copy this exact string into the Rust `TURN_DESCRIPTOR_JSON` golden. -/
def turnStateDescriptorJson : String := emitDescriptorJson emittedTurn

/-! ## §9 — JSON export of the whole-turn witness vectors (the bytes the Rust prover consumes). -/

/-- The honest executor-derived whole-turn witness, as the JSON array the Rust prover proves+verifies. -/
def turnHonestWitnessJson : String := witnessJson turnHonestWitness
/-- The forged whole-turn witness, as the JSON array the Rust prover REJECTS (step-1 frame-reuse UNSAT). -/
def turnForgedWitnessJson : String := witnessJson turnForgedWitness

-- The exact bytes the Rust `lean_executor_derived_turn` test pastes (goldens pin a drift here first).
#guard turnHonestWitnessJson ==
  "[100,5,70,35,30,1,1,1,1,1,1,1000150000005000003,1000120000035000003,3,3,1000050,1000050,100000005,70000035,70000035,35,50,25,60,10,1,1,1,1,1,1,1000105000050000003,1000095000060000003,3,3,1000070,1000070,35000050,25000060,25000060,3000100000005000050,3000070000035000050,3000070000035000050,3000070000025000060]"
#guard turnForgedWitnessJson ==
  "[100,5,70,35,30,1,1,1,1,1,1,1000150000005000003,1000120000035000003,3,3,1000050,1000050,100000005,70000035,70000035,35,50,25,60,10,1,1,1,1,1,1,1000105000050000003,1001024000060000003,3,3,1000070,1000999,35000050,25000060,25000060,3000100000005000050,3000070000035000050,3000070000035000050,3000999000025000060]"

-- The whole-turn descriptor JSON golden (copy into Rust `TURN_DESCRIPTOR_JSON`).
#guard turnStateDescriptorJson ==
  r#"{"name":"dregg-transfer-turn-v1","trace_width":44,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}},{"lhs":{"t":"var","v":13},"rhs":{"t":"var","v":14}},{"lhs":{"t":"var","v":15},"rhs":{"t":"var","v":16}},{"lhs":{"t":"var","v":18},"rhs":{"t":"var","v":19}},{"lhs":{"t":"var","v":25},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":26},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":27},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":28},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":29},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":30},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":22},"rhs":{"t":"add","l":{"t":"var","v":20},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":24}}}},{"lhs":{"t":"var","v":23},"rhs":{"t":"add","l":{"t":"var","v":21},"r":{"t":"var","v":24}}},{"lhs":{"t":"add","l":{"t":"var","v":22},"r":{"t":"var","v":23}},"rhs":{"t":"add","l":{"t":"var","v":20},"r":{"t":"var","v":21}}},{"lhs":{"t":"var","v":33},"rhs":{"t":"var","v":34}},{"lhs":{"t":"var","v":35},"rhs":{"t":"var","v":36}},{"lhs":{"t":"var","v":38},"rhs":{"t":"var","v":39}},{"lhs":{"t":"var","v":11},"rhs":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":17}},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":13}}},{"lhs":{"t":"var","v":12},"rhs":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":18}},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":14}}},{"lhs":{"t":"var","v":31},"rhs":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":35},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":37}},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":33}}},{"lhs":{"t":"var","v":32},"rhs":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":38}},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":34}}},{"lhs":{"t":"var","v":41},"rhs":{"t":"var","v":42}},{"lhs":{"t":"var","v":14},"rhs":{"t":"var","v":33}}]}"#

/-! ## §10 — axiom-hygiene tripwires (the whole-turn keystones carry no axiom). -/

#assert_axioms turnTransferWitnessVec_commit
#assert_axioms chainKernels_two
#assert_axioms turn_witness_proves_both_steps
#assert_axioms turn_execute_produces_both_steps
#assert_axioms emitTurnFaithful

end Dregg2.Circuit.TurnTransferWitness
