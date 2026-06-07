/-
# Dregg2.Circuit.Witness.attenuateAWitness — `execute → satisfying assignment` for `attenuateA` (the
TOTAL authority self-narrowing; v2 family, touched component = `caps`, a `funcComponent`).

The caps-function analog of `burnAWitness`: `attenuateWitnessVec` RUNS the REAL executor
`attenuateStepA` (the arm `execFullA` dispatches `.attenuateA` to — a TOTAL `some …` arm, always
commits) and lays the satisfying 72-wire `encodeE2` assignment out as a flat `List Int` over the
concrete commitment surface (the touched-component digest is now an injective digest over the cap table
`caps : Label → List Cap`, sampled at a probe label set). The honest witness satisfies `effectCircuit2`;
a forged post-state whose `caps` table is TAMPERED (a bystander label given an EXTRA `node` cap — a
privilege escalation the attenuation never authorized) is REJECTED by the component-bind gate `68 ≠ 69`.
`Inst.attenuateA.attenuateA_full_sound` proved the crown jewel (`⇒ AttenuateSpec`).
-/
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.AttenuateAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.AttenuateA
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest turnLogDigest)

set_option linter.dupNamespace false
set_option linter.unusedVariables false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface (caps-function variant). -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
/-- The log hash: the REAL `turnLogDigest` (binds the WHOLE receipt chain; the OLD `.length` collapse
dropped its entire content). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

/-- Field-binding `Auth` index (so endpoint `rights` are bound, not collapsed to `.length`). -/
def authCode : Auth → ℤ
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3 | .reply => 4 | .reset => 5 | .control => 6
/-- **Field-binding** `Cap` encoder: tag + target + the WHOLE rights list. The OLD `capLeaf` reduced
`endpoint t r => 5000 + t*10 + r.length`, dropping WHICH rights (only their COUNT) — fatal for an
ATTENUATION effect, where the precise narrowed rights ARE the soundness content. -/
def encCap : Cap → List ℤ
  | .null            => [0]
  | .node t          => [1, (t : ℤ)]
  | .endpoint t r    => 2 :: (t : ℤ) :: (r.length : ℤ) :: r.map authCode

/-- One label's slot digest: the REAL `refP2` sponge over the field-binding `encCap`. -/
def slotEnc (cs : List Cap) : ℤ := recListDigest encCap cs

/-- The probe labels the concrete `caps` digest samples: the acting label `actor`, plus a bystander
label `1` (so a privilege escalation to a third holder shows up). -/
def capsProbes (actor : CellId) : List CellId := [actor, 1]

/-- Concrete `caps` function digest: the REAL `refP2` sponge over the probe labels' slot digests. -/
def capsDigestC (actor : CellId) (caps : Caps) : ℤ :=
  refP2 ((capsProbes actor).map (fun l => slotEnc (caps l)))

def attenuateSurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete `ActiveComponent` + the concrete `attenuateEC`. -/

def capsComponentC (actor : CellId) : ActiveComponent RecChainedState AttenuateArgs where
  digest    := fun k => capsDigestC actor k.caps
  expected  := fun s args => capsDigestC actor (attenuateSlotF s.kernel.caps args.actor args.idx args.keep)
  postClause := fun s args post =>
    capsDigestC actor post.caps = capsDigestC actor (attenuateSlotF s.kernel.caps args.actor args.idx args.keep)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def attenuateEC (actor : CellId) : EffectSpec2 RecChainedState AttenuateArgs where
  view         := chainView
  active       := capsComponentC actor
  logUpdate    := some (fun s args => authReceipt args.actor :: s.log)
  restFrame    := fun k k' => True
  guardGates   := attenuateGuardGates
  guardProp    := attenuateGuardProp
  guardWidth   := 1
  guardEncode  := attenuateGuardEncode
  guardLocal   := attenuateGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (actor : CellId) (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState) :
    List Int :=
  (List.range (attenuateEC actor).traceWidth).map
    (fun v => encodeE2 attenuateSurfaceC (attenuateEC actor) s args s' v)

/-- **`attenuateWitnessVec s args`** — runs the TOTAL `attenuateStepA` and lays out the witness. -/
def attenuateWitnessVec (s : RecChainedState) (args : AttenuateArgs) : List Int :=
  witnessOf args.actor s args (attenuateStepA s args.actor args.idx args.keep)

theorem attenuateWitnessVec_commit (s : RecChainedState) (args : AttenuateArgs) :
    attenuateWitnessVec s args = witnessOf args.actor s args (attenuateStepA s args.actor args.idx args.keep) :=
  rfl

theorem witnessOf_get (actor : CellId) (s : RecChainedState) (args : AttenuateArgs)
    (s' : RecChainedState) (v : Nat) (hv : v < (attenuateEC actor).traceWidth) :
    (witnessOf actor s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2 attenuateSurfaceC (attenuateEC actor) s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A pre-state where label 0 holds `[node 5, node 9]` (idx 1 = `node 9`); a bystander label 1 holds `[]`.
`attenuateA` narrows label 0's idx-1 cap to `keep = [read]`; the bystander's slot must stay empty. -/

def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => default
        caps := fun x => if x = 0 then [Cap.node 5, Cap.node 9] else [] }
    log := [] }

/-- Narrow label 0's idx-1 cap to `[read]`. -/
def goodArgsC : AttenuateArgs := { actor := 0, idx := 1, keep := [Auth.read] }

def goodPostC : RecChainedState := attenuateStepA sC0 0 1 [Auth.read]

/-- THE FORGERY: the honest narrowing of label 0, BUT bystander label 1 ALSO gains a stolen `node 9`
cap — a privilege escalation the attenuation never authorized. The frame/log stay honest, so a
projection circuit would have passed it; the caps component digest differs. -/
def forgedCapsC : Caps :=
  fun x => if x = 0 then goodPostC.kernel.caps 0
           else if x = 1 then [Cap.node 9]   -- STOLEN cap on bystander
           else goodPostC.kernel.caps x

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with caps := forgedCapsC }, log := goodPostC.log }

def honestWitness : List Int := attenuateWitnessVec sC0 goodArgsC
def forgedWitness : List Int := witnessOf 0 sC0 goodArgsC forgedPostC

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfied (effectCircuit2 (attenuateEC 0))
  (encodeE2 attenuateSurfaceC (attenuateEC 0) sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfied (effectCircuit2 (attenuateEC 0))
  (encodeE2 attenuateSurfaceC (attenuateEC 0) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)

-- RIGHTS-AMPLIFICATION anti-ghost tooth (THE headline for attenuation — the class the OLD rights-COUNT
-- `capLeaf` MISSED). The honest narrowing keeps `[read]`, but the acting label 0's narrowed cap is
-- forged to `endpoint 9 [read, grant]` — an EXTRA `grant` right (same rights-list LENGTH bucket the OLD
-- `r.length` could NOT distinguish from a 2-right keep). `encCap` binds WHICH rights, so the
-- component-bind gate `68 ≠ 69` REJECTS — the surface ENFORCES attenuation.
def forgedAmplifyCapsC : Caps :=
  fun x => if x = 0 then [Cap.node 5, Cap.endpoint 9 [Auth.read, Auth.grant]]
           else goodPostC.kernel.caps x
def forgedAmplifyPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with caps := forgedAmplifyCapsC }, log := goodPostC.log }
#guard decide (satisfied (effectCircuit2 (attenuateEC 0))
  (encodeE2 attenuateSurfaceC (attenuateEC 0) sC0 goodArgsC forgedAmplifyPostC)) == false

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def attenuateHonestWitnessJson : String := witnessJson honestWitness
def attenuateForgedWitnessJson : String := witnessJson forgedWitness

-- Structural component-bind goldens (the field-binding `refP2`/`encCap` digests are arbitrary-precision;
-- non-vacuity is at the bind gates; the Rust paste is regenerated from the JSON accessors).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- caps binds (honest)
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- log binds (honest)
#guard !(attenuateHonestWitnessJson == attenuateForgedWitnessJson)

#assert_axioms attenuateWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.AttenuateAWitness
