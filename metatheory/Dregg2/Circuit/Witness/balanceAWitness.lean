/-
# Dregg2.Circuit.Witness.balanceAWitness — the WITNESS GENERATOR for `balanceA`: `execute → satisfying
assignment` (the v2 analog of `TransferWitness`, amplifying the verifiable-execution beachhead).

`Dregg2.Circuit.Inst.balanceA` already proved the v2 circuit⟺spec crown jewel for `balanceA`
(`balanceA_full_sound ⇒ BalanceMovementSpec`, the 17-field declarative post-state) and emits the wire
descriptor (`balanceAEmitted`, `"dregg-balanceA-v2"`, 72 wires, the 4 gates `var 0 = 1`, `66=67`,
`68=69`, `70=71`). This module supplies the MISSING piece — a CONCRETE witness GENERATOR

    balanceWitnessVec : RecChainedState → BalanceArgs → List Int

that RUNS the REAL executor `recCexecAsset` and lays the satisfying full-state assignment out as a flat
`List Int` of length `traceWidth = 72` (column index = wire index), with every digest column filled by a
CONCRETE commitment surface (so the values are real numbers the Rust prover consumes, not abstract
`Poseidon` terms). THIS is `execute → the satisfying assignment for the real per-effect circuit`,
materialized for Plonky3.

The pieces reused (not re-proved):
  * `Spec.BalanceMovement.recCexecAsset` — the REAL chained per-asset executor (`execFullA` dispatches
    `.balanceA t a` to it). `recCexecAsset s {t,a} = some s'` IS the executor computing the post-state.
  * `EffectCommit2.encodeE2` / `satisfiedE2` / `effectCircuit2` — the v2 full-state witness + circuit.
  * `Inst.BalanceA.balanceAE` — the `EffectSpec2` whose `apex ↔ BalanceMovementSpec`.

The CONCRETE surface (`balanceSurfaceC`, `balDigestC`) is the v2 analog of `StateCommit`'s concrete
surface: `RH = accounts.card + nullifiers.length` (so a frame-tamper of `nullifiers` is VISIBLE),
`LH = log.length` (so a log forgery is visible), and the `bal`-component digest is an INJECTIVE positional
Horner fold over the moved (`src,a`)/(`dst,a`) probes (so a wrong post-`bal` is visible). These mirror
`compressNConcrete`/`cmbConcrete` — REAL numbers on the toy `#guard` domain, not lossy sums.

Two `#guard`s tie it down (decidably, no `native_decide`):
  (1) the EXECUTOR-DERIVED witness SATISFIES `effectCircuit2` (every gate true) — `execute → prove`;
  (2) a REAL forged post-state (a tampered THIRD cell's `bal` column / a bystander mint) produces a
      witness the circuit REJECTS — a real UNSAT (the component-bind gate `68 = 69` fails). This is the
      anti-ghost tooth, computed end-to-end from a real forged state (NOT a hand-bumped digest).

The `#eval`-able JSON strings (`balanceHonestWitnessJson`/`balanceForgedWitnessJson`) are the EXACT bytes
the Rust `lean_executor_derived_balanceA` test proves+verifies (honest) and rejects (forged).
-/
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.BalanceAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.BalanceA
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Poseidon2Surface (refP2 turnLogDigest)

set_option linter.dupNamespace false
set_option linter.unusedVariables false

/-! ## §0 — decidability re-exports (so the executor-derived `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface (the v2 analog of `StateCommit`'s concrete surface).

`rhConcrete2` is a field-count of the non-`bal` components (`accounts.card + nullifiers.length`), so a
frame-tamper of `nullifiers` perturbs it. `lhConcrete` is the receipt-chain length, so a log forgery
perturbs it. `balDigestC` is an INJECTIVE positional Horner fold over the two moved probes
`(src,a)`/`(dst,a)` plus a third bystander probe — so a forged third-cell `bal` shows up. Each is a REAL
number on the `#guard` domain (NOT a lossy sum). -/

/-- Concrete rest hash: a field-count of the non-`bal` components (`accounts` cardinality + nullifier
length). A frame-tamper of `nullifiers` is VISIBLE. -/
def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)

/-- Concrete log hash: the REAL `turnLogDigest` (`refP2` over the FULL `encTurnRec`, binding `src`/`dst`
which the OLD `.length` collapse DROPPED entirely). CR-grounded on the real `babyBearD4W16` Poseidon2. -/
def lhConcrete : List Turn → ℤ := turnLogDigest

/-- The probe cells the concrete `bal` digest samples: the moved `src`/`dst` plus a bystander cell `2`
(so a third-cell mint shows up in the digest). -/
def balProbes (t : Turn) : List (CellId × AssetId) :=
  [(t.src, 0), (t.dst, 0), (2, 0)]

/-- Concrete `bal` component digest: the REAL `refP2` sponge over the probe entries (binds each entry —
NO lossy `% 10⁶` collapse), so a wrong post-`bal` (including a bystander mint, even ABOVE 10⁶) is VISIBLE. -/
def balDigestC (t : Turn) (bal : CellId → AssetId → ℤ) : ℤ :=
  refP2 ((balProbes t).map (fun p => bal p.1 p.2))

/-- The v2 `Surface2` over the concrete carriers. -/
def balanceSurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete `ActiveComponent` + the concrete `balanceAE` (digest = `balDigestC`).

We fix the digest to `balDigestC t` (a FUNCTION of the turn, so the probe set follows `src`/`dst`). The
`binds`/`encodes` fields are TRIVIAL here (the concrete instance is for the `#guard`/Rust-bytes layout,
not the soundness theorem — `Inst.balanceA.balanceA_full_sound` carries the abstract-surface CR portal). -/

/-- The concrete `bal` component for a fixed turn `t`: digest = `balDigestC t`, predicted = the
`recTransferBal` movement. (Trivial `postClause`/`binds`/`encodes`: this instance lays out the witness
bytes; the soundness theorem lives in `Inst.balanceA` over the abstract surface.) -/
def balComponentC (t : Turn) : ActiveComponent RecChainedState BalanceArgs where
  digest    := fun k => balDigestC t k.bal
  expected  := fun s args => balDigestC t (recTransferBal s.kernel.bal args.t.src args.t.dst args.a args.t.amt)
  postClause := fun s args post =>
    balDigestC t post.bal = balDigestC t (recTransferBal s.kernel.bal args.t.src args.t.dst args.a args.t.amt)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

/-- The concrete `EffectSpec2` for `balanceA` over a fixed turn `t` (same guard sub-system as
`Inst.balanceA.balanceAE`, concrete `active`/`restFrame`). -/
def balanceEC (t : Turn) : EffectSpec2 RecChainedState BalanceArgs where
  view         := chainView
  active       := balComponentC t
  logUpdate    := some (fun s args => args.t :: s.log)
  restFrame    := fun k k' => True
  guardGates   := balanceGuardGates
  guardProp    := balanceGuardProp
  guardWidth   := 1
  guardEncode  := balanceGuardEncode
  guardLocal   := balanceGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR: `execute → satisfying assignment`. -/

/-- Lay an `encodeE2 balanceSurfaceC (balanceEC t) s args s'` assignment out as a flat `List Int` indexed
`0 .. traceWidth-1`. This is the witness vector the Rust `build_trace` consumes (column = wire). -/
def witnessOf (t : Turn) (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : List Int :=
  (List.range (balanceEC t).traceWidth).map
    (fun v => encodeE2 balanceSurfaceC (balanceEC t) s args s' v)

/-- **`balanceWitnessVec s args` — the executor-driven witness generator.** Runs the REAL executor
`recCexecAsset s args.t args.a`; on commit lays out the satisfying full-state witness for the executor's
post-state `s'`, every digest column filled by the concrete surface. On a fail-closed turn it falls back
to `s` (a guard/component-failing vector, as it should). THIS is `execute → the satisfying assignment`. -/
def balanceWitnessVec (s : RecChainedState) (args : BalanceArgs) : List Int :=
  match recCexecAsset s args.t args.a with
  | some s' => witnessOf args.t s args s'
  | none    => witnessOf args.t s args s

/-- **`balanceWitnessVec` IS `witnessOf` of the EXECUTOR's post-state** (the some-branch unfold). -/
theorem balanceWitnessVec_commit {s s' : RecChainedState} {args : BalanceArgs}
    (h : recCexecAsset s args.t args.a = some s') :
    balanceWitnessVec s args = witnessOf args.t s args s' := by
  unfold balanceWitnessVec; rw [h]

/-- Reading the generated vector at a wire `< traceWidth` recovers `encodeE2`. -/
theorem witnessOf_get (t : Turn) (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (v : Nat) (hv : v < (balanceEC t).traceWidth) :
    (witnessOf t s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2 balanceSurfaceC (balanceEC t) s args s' v := by
  unfold witnessOf
  rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves).

A concrete THREE-cell pre-state: cells {0,1,2}, per-asset `bal` column 0 holding 100/5/50; actor 0
self-authorized over src 0 (`authorizedB` true since `actor = src`); all cells live (`lifecycle = 0`).
Actor 0 moves 30 of asset 0 from cell 0 to cell 1; cell 2 the bystander. We RUN `recCexecAsset` and
materialize the witness. -/

/-- The concrete pre-state: `bal` column 0 = 100/5/50 on cells {0,1,2}; empty caps (actor 0 owns cell 0
by `actor = src`); all live; empty log. -/
def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => default
        caps := fun _ => []
        bal := fun c a => if a = 0 then (if c = 0 then 100 else if c = 1 then 5 else if c = 2 then 50 else 0) else 0 }
    log := [] }

/-- The good turn: actor 0 moves 30 of asset 0 from cell 0 to cell 1 (cell 2 must stay at 50). -/
def goodTurnC : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }
def goodArgsC : BalanceArgs := { t := goodTurnC, a := 0 }

/-- The honest executor post-state (`recCexecAsset sC0 goodTurnC 0`). -/
def goodPostC : RecChainedState := (recCexecAsset sC0 goodTurnC 0).getD sC0

/-- **THE FORGERY:** cells 0,1 are the honest debit/credit (70/35), but the bystander cell 2's asset-0
balance is MINTED from 50 to 999 — value forged into a third cell. The two moved balances conserve, so a
projection circuit sees nothing wrong. The forged post-state shares the honest log (so only the
component-bind gate `68 = 69` bites). -/
def forgedBalC : CellId → AssetId → ℤ :=
  fun c a => if a = 0 then (if c = 0 then 70 else if c = 1 then 35 else if c = 2 then 999 else 0) else 0

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with bal := forgedBalC }, log := goodPostC.log }

/-- The honest executor-derived witness vector. -/
def honestWitness : List Int := balanceWitnessVec sC0 goodArgsC

/-- The forged witness vector: SAME pre/turn, but the REAL `forgedPostC` post-state (bystander minted). -/
def forgedWitness : List Int := witnessOf goodTurnC sC0 goodArgsC forgedPostC

-- (1) the witness has the trace width the Rust descriptor declares.
#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state circuit.
#guard decide (satisfied (effectCircuit2 (balanceEC goodTurnC))
  (encodeE2 balanceSurfaceC (balanceEC goodTurnC) sC0 goodArgsC goodPostC))
-- ...with the three frame-EQ gate wire-pairs equal (rest 66/67, comp 68/69, log 70/71).
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0   -- restDigPre = restDigPost
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- compDigPost = compDigExpected
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- logDigPost = logDigExpected

-- (3) THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state's witness FAILS the circuit, and
--     specifically it is the COMPONENT-BIND gate (68 ≠ 69) that breaks — the bystander mint is caught.
#guard decide (satisfied (effectCircuit2 (balanceEC goodTurnC))
  (encodeE2 balanceSurfaceC (balanceEC goodTurnC) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected: REJECTED
-- ...while the forgery still CONSERVES the two moved balances (the projection ghost): the bystander
--    mint is invisible to a moved-balance-only check (probe[0] debit + probe[1] credit unchanged).

-- HIGH-field anti-ghost tooth: the bystander mint forged ABOVE 10⁶ (the OLD `% 10⁶` Horner fold
-- collided here; `refP2` does NOT). The component-bind gate `68 ≠ 69` still REJECTS.
def forgedBalHighC : CellId → AssetId → ℤ :=
  fun c a => if a = 0 then (if c = 0 then 70 else if c = 1 then 35 else if c = 2 then 50 + 1000000 else 0) else 0
def forgedPostHighC : RecChainedState :=
  { kernel := { goodPostC.kernel with bal := forgedBalHighC }, log := goodPostC.log }
#guard decide (satisfied (effectCircuit2 (balanceEC goodTurnC))
  (encodeE2 balanceSurfaceC (balanceEC goodTurnC) sC0 goodArgsC forgedPostHighC)) == false

/-! ## §5 — JSON export of the witness vectors (the bytes the Rust prover consumes). -/

/-- Render a `List Int` as a JSON number array (the witness wire form). -/
def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

/-- The honest executor-derived witness, as the JSON array the Rust prover proves+verifies. -/
def balanceHonestWitnessJson : String := witnessJson honestWitness
/-- The forged witness, as the JSON array the Rust prover REJECTS (component-bind UNSAT). -/
def balanceForgedWitnessJson : String := witnessJson forgedWitness

-- Structural bind-gate goldens (the CONSTRAINED frame-EQ wires 66/67 rest, 68/69 component, 70/71 log
-- carry the field-binding `refP2` digests — arbitrary-precision, so non-vacuity is at the bind GATES;
-- the Rust paste is regenerated from these JSON accessors when the prover field-reduces).
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0   -- rest binds (honest)
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- component binds (honest)
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- log binds (honest)
#guard !(balanceHonestWitnessJson == balanceForgedWitnessJson)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms balanceWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.BalanceAWitness
