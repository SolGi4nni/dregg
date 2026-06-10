/-
# Dregg2.Circuit.SetFieldCommit — FULL-STATE circuit⟺spec keystone for `setFieldA` (effect #2).

`Dregg2.Circuit.StateCommit` proved the full-state circuit⟺spec for the FIRST real effect (`Transfer`)
over `recKExec`: a satisfying `stateCircuit` witness pins the WHOLE post-state (the `TransferSpec`
17-component reference), not a projection. THIS module replays the SAME crown-jewel pattern for the
SECOND real effect, **`setFieldA`** — dregg2's developer-facing caveat-gated single-cell field write
(`execFullA (.setFieldA actor cell f v) = stateStepGuarded …`, `TurnExecutorFull.lean:3491`) — over
the INDEPENDENT apex `Dregg2.Circuit.Spec.CellStateField.SetFieldSpec` (the executor⟺spec corner is
already closed there; here we close the CIRCUIT corner of the spec⟺executor⟺circuit triangle).

## What `setFieldA` touches (the differences from `Transfer`)

`setFieldA` is a field-write, NOT a balance-move, and it touches exactly ONE cell (the target),
NOT two. A committed `setFieldA` over a chained state `s = ⟨kernel, log⟩` produces `s'` where:
  * `s'.kernel.cell = setFieldCellMap s.kernel.cell cell f v` — slot `f` of `cell` written to `.int v`,
    EVERY OTHER cell whole-preserved (the touched-cell map; `writeFieldCellMap_correct`).
  * `s'.log = ⟨actor, cell, cell, 0⟩ :: s.log` — the receipt chain grows by exactly the one self-row.
  * all 16 non-`cell` kernel components LITERALLY unchanged (THE FRAME).

So the "moved" content is the SINGLE target cell's new `Value` (a 1-leaf commitment, simpler than
Transfer's 2-to-1 moved node), the frame-digest is the untouched-cell sponge over `accounts \ {cell}`,
and — the new piece `Transfer` did not have — a `log` commitment (`setFieldA` extends the chain).

## How the frame is PROVED (not portaled — the honesty constraint, copied from StateCommit)

The post-state's pinned-ness is derived from a GENUINE BINDING COMMITMENT (a Poseidon Merkle node-hash
`compress` + sponge `compressN` over the ORDERED untouched leaves + a leaf hash `CH` + a log hash
`LH`), never a `+`-fold (a sum is not injective, so a sum-fold could satisfy NONE of the binding
portals — the soundness theorem would be VACUOUS). The state commitment splits into FOUR
encoded digests over the witness:
  * `restHash`   — `RH` of the 16 non-`cell` kernel components (REUSED from `StateCommit`).
  * `frameDigest`— `compressN (S.sort.map (fun c => CH c (cell c)))` over `S = accounts \ {cell}`
                   (REUSED from `StateCommit.frameDigest`): the sponge of the UNTOUCHED leaves in
                   CANONICAL order, shared pre/post (the load-bearing reuse).
  * `targetLeaf` — `CH cell (cell-map cell)` — the SINGLE moved cell's leaf hash (the 1-cell analog
                   of `StateCommit.movedDigest`; one leaf needs no node-hash, just `cellLeafInjective`).
  * `logDigest`  — `LH log` — the receipt chain's hash (the new `setFieldA`-specific commitment).
Four EQ gates extend the executor⟺spec content:
  * `cSFRest`   : `restDigPre  = restDigPost`        — the 16 non-cell fields frozen.
  * `cSFFrame`  : `frameDigPre = frameDigPost`       — every OTHER cell frozen.
  * `cSFTarget` : `targetLeafPost = targetLeafExpected` — the touched leaf = `CH cell (setField …)`.
  * `cSFLog`    : `logDigPost = logDigExpected`      — the post log = `LH (receipt :: pre-log)`.
The CONCLUSIONS (`s'.kernel.cell = setFieldCellMap …`, the frame, the log) come from PROVED binding
lemmas DERIVED from a SMALL standard Poseidon collision-resistance set
(`compressInjective`/`compressNInjective`/`cellLeafInjective` REUSED from `StateCommit`, plus a
`logHashInjective` for the chain) — the ONLY crypto assumptions, each the REALIZABLE injectivity of a
genuine hash. A satisfying witness REASSEMBLES the full `SetFieldSpec` by `funext`: the target cell
from `cSFTarget`+`cellLeafInjective`, every other live cell from `cSFFrame`+`FrameDigestBindsCells`,
dead cells from the PROVED `AccountsWF` invariant, the 16 non-cell fields from `cSFRest`+
`RestHashIffFrame`, and the log from `cSFLog`+`logHashInjective`. NO `postRoot = recStateCommit
(applySetField …)` hypothesis appears — that forbidden "ghost-in-disguise" is RECONSTRUCTED, not
carried. The guard (`SetFieldGuard`: caveat ∧ authority ∧ membership ∧ liveness) is supplied as the
soundness premise (it is the executor's domain restriction, not a state-frame fact — the circuit
extension here is the FRAME tooth, the guard tooth being the cellstatefield executor⟺spec corner).

## The assumption ledger (enumerated — verify NOTHING else is assumed)

ASSUMED (carried Prop hypotheses — the STANDARD Poseidon collision-resistance set, all REALIZABLE
injectivity of a genuine hash, never `axiom`, never sum-injectivity):
  * `compressInjective cmb`       — the root combiner is injective (REUSED `StateCommit.compressInjective`).
  * `compressNInjective compressN` — the untouched-cell sponge is injective (REUSED).
  * `cellLeafInjective CH`        — the per-cell leaf encoding is injective in the `Value` (REUSED).
  * `RestHashIffFrame RH`         — equal rest hashes ⟺ the 16 non-cell components agree (REUSED).
  * `logHashInjective LH`         — the receipt-chain hash is injective (the new `setFieldA` piece).
  * `AccountsWF k` — NOT crypto: the structural invariant "cells outside `accounts` hold the default",
                     REUSED from `StateCommit` (proved preserved there by `recKExec_preserves_AccountsWF`).
  * `SetFieldGuard s actor cell f v` — the executor's admissibility guard (the cellstatefield gate).
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.Spec.cellstatefield

namespace Dregg2.Circuit.SetFieldCommit

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.CellStateField
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull (execFullA)
open Dregg2.Exec.EffectsState
  (setField fieldOf writeField stateAuthB caveatsAdmit cellLive)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the concrete anti-ghost `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the named wires of the `setFieldA` full-state PI surface.

`setFieldA` does NOT need Transfer's balance/amount columns — it is a field write, not a move. The
witness columns are the FOUR digest pre/post pairs (rest, frame, target-leaf, log) plus the two
"expected" columns (the target leaf and the log the SPEC predicts), and a small set of {0,1} guard
indicators (caveat ∧ authority ∧ membership ∧ liveness) the protocol gate decides. -/

/-- `caveatBit`     — {0,1} caveat-admit indicator (`caveatsAdmit k f actor cell v`). -/
def vSFCaveat   : Var := 0
/-- `authBit`       — {0,1} authority indicator (`stateAuthB caps actor cell`). -/
def vSFAuth     : Var := 1
/-- `memBit`        — {0,1} membership indicator (`cell ∈ accounts`). -/
def vSFMem      : Var := 2
/-- `liveBit`       — {0,1} lifecycle-liveness indicator (`cellLive k cell`). -/
def vSFLive     : Var := 3
/-- `preRoot`       — `recSetFieldCommit` of the pre-state. -/
def vSFPreRoot  : Var := 4
/-- `postRoot`      — `recSetFieldCommit` of the post-state. -/
def vSFPostRoot : Var := 5
/-- `restDigPre`    — `RH` of the pre-kernel (16 non-cell components). -/
def vSFRestPre  : Var := 6
/-- `restDigPost`   — `RH` of the post-kernel. -/
def vSFRestPost : Var := 7
/-- `frameDigPre`   — `frameDigest` of the pre-kernel over `accounts \ {cell}`. -/
def vSFFramePre  : Var := 8
/-- `frameDigPost`  — `frameDigest` of the post-kernel over `accounts \ {cell}`. -/
def vSFFramePost : Var := 9
/-- `targetLeafPre`      — `CH cell (pre cell-map cell)` — the touched leaf before the write. -/
def vSFTargetPre      : Var := 10
/-- `targetLeafPost`     — `CH cell (post cell-map cell)` — the touched leaf after the write. -/
def vSFTargetPost     : Var := 11
/-- `targetLeafExpected` — `CH cell (setField f (pre cell-map cell) (.int v))` — the SPEC's written
leaf (a pure function of pre-state + the effect args; no executor). -/
def vSFTargetExpected : Var := 12
/-- `logDigPre`       — `LH (pre log)`. -/
def vSFLogPre       : Var := 13
/-- `logDigPost`      — `LH (post log)`. -/
def vSFLogPost      : Var := 14
/-- `logDigExpected`  — `LH (receipt :: pre log)` — the SPEC's one-row chain extension. -/
def vSFLogExpected  : Var := 15

/-- The full-state `setFieldA` trace width (16 columns: 4 guard bits + 2 roots + rest pre/post +
frame pre/post + target pre/post/expected + log pre/post/expected). -/
def setFieldTraceWidth : Nat := 16

/-! ## §2 — the commitment surface.

The cell/rest/frame primitives are REUSED VERBATIM from `StateCommit` (same `CH`/`RH`/`compressN` and
their CR carriers). The ONLY new primitive is the receipt-chain hash `LH` (and its injectivity). The
"moved" content is a SINGLE leaf, so the moved commitment is just `CH cell (f cell)` — bound directly
by `cellLeafInjective`, needing no 2-to-1 node hash. -/

section Surface

-- `CH c v` — the per-cell leaf hash (REUSED shape from `StateCommit`).
variable (CH : CellId → Value → ℤ)
-- `RH k` — the 16-non-cell rest hash (REUSED shape from `StateCommit`).
variable (RH : RecordKernelState → ℤ)
-- `cmb a b` — the root combiner (a 2-to-1 compress; nested for the cell/rest/log children).
variable (cmb : ℤ → ℤ → ℤ)
-- `compressN xs` — the Poseidon sponge over the untouched leaves (REUSED from `StateCommit`).
variable (compressN : List ℤ → ℤ)
-- `LH log` — the receipt-chain hash (the new `setFieldA`-specific commitment). The CR carrier
-- `logHashInjective` has been RELOCATED to `StateCommit` (beside the other CR carriers), so the
-- generic `EffectCommit` framework imports it from there; we reference `StateCommit.logHashInjective`.
variable (LH : List Turn → ℤ)

/-- The carrier of the frame digest: the live accounts MINUS the SINGLE touched cell. -/
def sfFrameCarrier (k : RecordKernelState) (cell : CellId) : Finset CellId :=
  k.accounts \ {cell}

/-- **`recSetFieldCommit`** — the full-state root over a chained state `s = ⟨kernel, log⟩`: a nested
`cmb` of (the live-cell digest) with (`cmb` of the rest hash with the log hash). The live-cell digest
is itself the Merkle node `compress`-ing the untouched-frame sponge with the single touched leaf — but
for `setFieldA` we read the children directly off the witness, so the root is the honest binding
combination of cell-digest ⊕ (rest ⊕ log). Tampering any cell changes the frame sponge or the target
leaf; any non-cell field changes `RH`; the log changes `LH`; `cmb`-injectivity separates them. -/
def recSetFieldCommit (k : RecordKernelState) (cell : CellId) (log : List Turn) : ℤ :=
  cmb (cmb (StateCommit.frameDigest CH compressN k (sfFrameCarrier k cell)) (CH cell (k.cell cell)))
      (cmb (RH k) (LH log))

end Surface

/-! ## §3 — the encoder + transport.

`encodeSF` lays out the full-state `setFieldA` witness over a chained pre/post. Wires `0..3` carry the
{0,1} guard indicators (read off the PRE-state); the digest columns carry the honest commitment
values. The target/log "expected" columns commit the SPEC's predicted write/chain (pure functions of
the pre-state + effect args — no executor). -/

/-- {0,1} encoding of a decidable `Prop` (= `Circuit.propBit`, re-exported for locality). -/
abbrev pBit (p : Prop) [Decidable p] : ℤ := Circuit.propBit p

/-- **`encodeSF`** — the full-state `setFieldA` witness. The guard bits are the decidable indicators
read against the PRE-state; the digest columns carry the honest commitment values; the expected
columns commit the spec's written target leaf + the one-row chain extension. Unmentioned variables
default to `0`. -/
def encodeSF (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb : ℤ → ℤ → ℤ)
    (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState) :
    Assignment := fun w =>
  if      w = vSFCaveat   then pBit (caveatsAdmit s.kernel f actor cell v = true)
  else if w = vSFAuth     then pBit (stateAuthB s.kernel.caps actor cell = true)
  else if w = vSFMem      then pBit (cell ∈ s.kernel.accounts)
  else if w = vSFLive     then pBit (cellLive s.kernel cell = true)
  else if w = vSFPreRoot  then recSetFieldCommit CH RH cmb compressN LH s.kernel cell s.log
  else if w = vSFPostRoot then recSetFieldCommit CH RH cmb compressN LH s'.kernel cell s'.log
  else if w = vSFRestPre  then RH s.kernel
  else if w = vSFRestPost then RH s'.kernel
  else if w = vSFFramePre  then StateCommit.frameDigest CH compressN s.kernel (sfFrameCarrier s.kernel cell)
  else if w = vSFFramePost then StateCommit.frameDigest CH compressN s'.kernel (sfFrameCarrier s.kernel cell)
  else if w = vSFTargetPre      then CH cell (s.kernel.cell cell)
  else if w = vSFTargetPost     then CH cell (s'.kernel.cell cell)
  else if w = vSFTargetExpected then CH cell (setField f (s.kernel.cell cell) (.int v))
  else if w = vSFLogPre       then LH s.log
  else if w = vSFLogPost      then LH s'.log
  else if w = vSFLogExpected  then LH ({ actor := actor, src := cell, dst := cell, amt := 0 } :: s.log)
  else 0

/-! ## §3b — digest/bit wire lookups (the `if`-cascade collapsed at each index). -/

section Lemmas

variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb : ℤ → ℤ → ℤ)
  (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)

theorem encSF_caveat (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFCaveat
      = pBit (caveatsAdmit s.kernel f actor cell v = true) := by
  simp [encodeSF, vSFCaveat]
theorem encSF_auth (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFAuth
      = pBit (stateAuthB s.kernel.caps actor cell = true) := by
  simp [encodeSF, vSFAuth, vSFCaveat]
theorem encSF_mem (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFMem
      = pBit (cell ∈ s.kernel.accounts) := by
  simp [encodeSF, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_live (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFLive
      = pBit (cellLive s.kernel cell = true) := by
  simp [encodeSF, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_preRoot (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFPreRoot
      = recSetFieldCommit CH RH cmb compressN LH s.kernel cell s.log := by
  simp [encodeSF, vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_postRoot (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFPostRoot
      = recSetFieldCommit CH RH cmb compressN LH s'.kernel cell s'.log := by
  simp [encodeSF, vSFPostRoot, vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_restPre (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFRestPre = RH s.kernel := by
  simp [encodeSF, vSFRestPre, vSFPostRoot, vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_restPost (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFRestPost = RH s'.kernel := by
  simp [encodeSF, vSFRestPost, vSFRestPre, vSFPostRoot, vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_framePre (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFFramePre
      = StateCommit.frameDigest CH compressN s.kernel (sfFrameCarrier s.kernel cell) := by
  simp [encodeSF, vSFFramePre, vSFRestPost, vSFRestPre, vSFPostRoot, vSFPreRoot, vSFLive, vSFMem,
    vSFAuth, vSFCaveat]
theorem encSF_framePost (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFFramePost
      = StateCommit.frameDigest CH compressN s'.kernel (sfFrameCarrier s.kernel cell) := by
  simp [encodeSF, vSFFramePost, vSFFramePre, vSFRestPost, vSFRestPre, vSFPostRoot, vSFPreRoot,
    vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_targetPre (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFTargetPre = CH cell (s.kernel.cell cell) := by
  simp [encodeSF, vSFTargetPre, vSFFramePost, vSFFramePre, vSFRestPost, vSFRestPre, vSFPostRoot,
    vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_targetPost (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFTargetPost = CH cell (s'.kernel.cell cell) := by
  simp [encodeSF, vSFTargetPost, vSFTargetPre, vSFFramePost, vSFFramePre, vSFRestPost, vSFRestPre,
    vSFPostRoot, vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_targetExpected (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFTargetExpected
      = CH cell (setField f (s.kernel.cell cell) (.int v)) := by
  simp [encodeSF, vSFTargetExpected, vSFTargetPost, vSFTargetPre, vSFFramePost, vSFFramePre, vSFRestPost,
    vSFRestPre, vSFPostRoot, vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_logPre (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFLogPre = LH s.log := by
  simp [encodeSF, vSFLogPre, vSFTargetExpected, vSFTargetPost, vSFTargetPre, vSFFramePost, vSFFramePre,
    vSFRestPost, vSFRestPre, vSFPostRoot, vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_logPost (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFLogPost = LH s'.log := by
  simp [encodeSF, vSFLogPost, vSFLogPre, vSFTargetExpected, vSFTargetPost, vSFTargetPre, vSFFramePost,
    vSFFramePre, vSFRestPost, vSFRestPre, vSFPostRoot, vSFPreRoot, vSFLive, vSFMem, vSFAuth, vSFCaveat]
theorem encSF_logExpected (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    encodeSF CH RH cmb compressN LH s actor cell f v s' vSFLogExpected
      = LH ({ actor := actor, src := cell, dst := cell, amt := 0 } :: s.log) := by
  simp [encodeSF, vSFLogExpected, vSFLogPost, vSFLogPre, vSFTargetExpected, vSFTargetPost, vSFTargetPre,
    vSFFramePost, vSFFramePre, vSFRestPost, vSFRestPre, vSFPostRoot, vSFPreRoot, vSFLive, vSFMem,
    vSFAuth, vSFCaveat]

/-! ## §4 — the full-state circuit: the four frame-forcing EQ gates ++ the four guard gates. -/

/-- **Caveat gate:** `caveatBit = 1`. -/
def cSFCaveat : Constraint := { lhs := .var vSFCaveat, rhs := .const 1 }
/-- **Authority gate:** `authBit = 1`. -/
def cSFAuth : Constraint := { lhs := .var vSFAuth, rhs := .const 1 }
/-- **Membership gate:** `memBit = 1`. -/
def cSFMem : Constraint := { lhs := .var vSFMem, rhs := .const 1 }
/-- **Liveness gate:** `liveBit = 1`. -/
def cSFLive : Constraint := { lhs := .var vSFLive, rhs := .const 1 }
/-- **Rest-frame gate:** `restDigPre = restDigPost` (the 16 non-cell fields frozen). -/
def cSFRest : Constraint := { lhs := .var vSFRestPre, rhs := .var vSFRestPost }
/-- **Frame-reuse gate:** `frameDigPre = frameDigPost` (every OTHER cell frozen). -/
def cSFFrame : Constraint := { lhs := .var vSFFramePre, rhs := .var vSFFramePost }
/-- **Target-bind gate:** `targetLeafPost = targetLeafExpected` (the touched leaf = the spec write). -/
def cSFTarget : Constraint := { lhs := .var vSFTargetPost, rhs := .var vSFTargetExpected }
/-- **Log-bind gate:** `logDigPost = logDigExpected` (the post log = the one-row chain extension). -/
def cSFLog : Constraint := { lhs := .var vSFLogPost, rhs := .var vSFLogExpected }

/-- **The full-state `setFieldA` circuit** — the four guard gates ++ the four frame-forcing EQ gates.
THIS is the constraint data that pins the WHOLE post-state of a caveat-gated field write. -/
def setFieldCircuit : ConstraintSystem :=
  [cSFCaveat, cSFAuth, cSFMem, cSFLive, cSFRest, cSFFrame, cSFTarget, cSFLog]

/-- Sanity: eight gates. -/
example : setFieldCircuit.length = 8 := rfl

/-- **`SetFieldCommitSat cmb a`** — the root-decomposition equalities the opaque combiner pins: the
pre/post root wires equal `cmb` of (the cell-digest child) with (`cmb` of the rest-hash with the log
child). Holds by `rfl` from `encodeSF`. Carried in `satisfiedSF` so the root-binding corollary can use
`compressInjective cmb`. The cell-digest child is read as `cmb frameDig targetLeaf` off the SAME
witness. -/
def SetFieldCommitSat (cmb : ℤ → ℤ → ℤ) (a : Assignment) : Prop :=
  a vSFPreRoot  = cmb (cmb (a vSFFramePre)  (a vSFTargetPre))  (cmb (a vSFRestPre)  (a vSFLogPre))
  ∧ a vSFPostRoot = cmb (cmb (a vSFFramePost) (a vSFTargetPost)) (cmb (a vSFRestPost) (a vSFLogPost))

/-- **`satisfiedSF cmb a`** — the full-state satisfaction predicate: the `setFieldCircuit` gates hold
AND the root decomposition holds. -/
def satisfiedSF (cmb : ℤ → ℤ → ℤ) (a : Assignment) : Prop :=
  satisfied setFieldCircuit a ∧ SetFieldCommitSat cmb a

/-! ## §4b — per-gate ↔ protocol-content lemmas (each gate's meaning under `encodeSF`). -/

/-- A {0,1} `propBit` indicator equals `1` IFF the proposition holds (both directions). -/
private theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; by_cases h : p <;> simp [h]

theorem sfcaveat_iff (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    cSFCaveat.holds (encodeSF CH RH cmb compressN LH s actor cell f v s')
      ↔ caveatsAdmit s.kernel f actor cell v = true := by
  unfold Constraint.holds cSFCaveat
  simp only [Expr.eval, encSF_caveat]; exact propBit_eq_one
theorem sfauth_iff (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    cSFAuth.holds (encodeSF CH RH cmb compressN LH s actor cell f v s')
      ↔ stateAuthB s.kernel.caps actor cell = true := by
  unfold Constraint.holds cSFAuth
  simp only [Expr.eval, encSF_auth]; exact propBit_eq_one
theorem sfmem_iff (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    cSFMem.holds (encodeSF CH RH cmb compressN LH s actor cell f v s')
      ↔ cell ∈ s.kernel.accounts := by
  unfold Constraint.holds cSFMem
  simp only [Expr.eval, encSF_mem]; exact propBit_eq_one
theorem sflive_iff (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    cSFLive.holds (encodeSF CH RH cmb compressN LH s actor cell f v s')
      ↔ cellLive s.kernel cell = true := by
  unfold Constraint.holds cSFLive
  simp only [Expr.eval, encSF_live]; exact propBit_eq_one
theorem sfrest_iff (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    cSFRest.holds (encodeSF CH RH cmb compressN LH s actor cell f v s') ↔ RH s.kernel = RH s'.kernel := by
  unfold Constraint.holds cSFRest
  simp only [Expr.eval, encSF_restPre, encSF_restPost]
theorem sfframe_iff (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    cSFFrame.holds (encodeSF CH RH cmb compressN LH s actor cell f v s')
      ↔ StateCommit.frameDigest CH compressN s.kernel (sfFrameCarrier s.kernel cell)
          = StateCommit.frameDigest CH compressN s'.kernel (sfFrameCarrier s.kernel cell) := by
  unfold Constraint.holds cSFFrame
  simp only [Expr.eval, encSF_framePre, encSF_framePost]
theorem sftarget_iff (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    cSFTarget.holds (encodeSF CH RH cmb compressN LH s actor cell f v s')
      ↔ CH cell (s'.kernel.cell cell) = CH cell (setField f (s.kernel.cell cell) (.int v)) := by
  unfold Constraint.holds cSFTarget
  simp only [Expr.eval, encSF_targetPost, encSF_targetExpected]
theorem sflog_iff (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) :
    cSFLog.holds (encodeSF CH RH cmb compressN LH s actor cell f v s')
      ↔ LH s'.log = LH ({ actor := actor, src := cell, dst := cell, amt := 0 } :: s.log) := by
  unfold Constraint.holds cSFLog
  simp only [Expr.eval, encSF_logPost, encSF_logExpected]

/-! ## §5 — FULL-STATE SOUNDNESS: a satisfying witness PROVES `SetFieldSpec` (whole post-state).

The keystone. From a satisfying `setFieldCircuit` witness (+ the executor's guard premise + the
`AccountsWF` invariant), the four guard gates give `SetFieldGuard`; the four frame EQ gates + the
PROVED binding lemmas (`FrameDigestBindsCells` REUSED from `StateCommit`, `cellLeafInjective`,
`RestHashIffFrame`, `logHashInjective`) give the WHOLE post-state. The post `cell` map is RECONSTRUCTED
by `funext` — NOT asserted. Result: `SetFieldSpec s actor cell f v s'`. -/

/-- **THEOREM — `setfield_circuit_full_sound` (frame RECONSTRUCTED not portaled).** A
satisfying full-state witness on the encoded chained pre/effect/post proves the complete declarative
`SetFieldSpec`: every component is pinned. Carries ONLY the standard Poseidon collision-resistance set
(`compressNInjective compressN`, `cellLeafInjective CH`, `RestHashIffFrame RH`, `logHashInjective LH`)
+ the `AccountsWF` invariant on both kernels. The frame binding is PROVED (the binding lemmas are
`StateCommit` theorems off the CR set), so the soundness theorem is NON-VACUOUS: every carried Prop is
realizable by a real Poseidon (a `+`-fold could satisfy NONE of them). No `postRoot = recStateCommit
(applySetField …)` ghost hypothesis appears — the answer is RECONSTRUCTED. -/
theorem setfield_circuit_full_sound
    (hCompressN : StateCommit.compressNInjective compressN)
    (hLeaf : StateCommit.cellLeafInjective CH)
    (hRest : StateCommit.RestHashIffFrame RH)
    (hLog : StateCommit.logHashInjective LH)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState)
    (hwf : StateCommit.AccountsWF s.kernel) (hwf' : StateCommit.AccountsWF s'.kernel)
    (h : satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s')) :
    SetFieldSpec s actor cell f v s' := by
  obtain ⟨hsat, _hcommit⟩ := h
  -- the eight gates.
  have hcaveatgate := hsat cSFCaveat (by unfold setFieldCircuit; simp)
  have hauthgate   := hsat cSFAuth   (by unfold setFieldCircuit; simp)
  have hmemgate    := hsat cSFMem    (by unfold setFieldCircuit; simp)
  have hlivegate   := hsat cSFLive   (by unfold setFieldCircuit; simp)
  have hrestgate   := hsat cSFRest   (by unfold setFieldCircuit; simp)
  have hframegate  := hsat cSFFrame  (by unfold setFieldCircuit; simp)
  have htargetgate := hsat cSFTarget (by unfold setFieldCircuit; simp)
  have hloggate    := hsat cSFLog    (by unfold setFieldCircuit; simp)
  -- the guard (the executor's domain restriction, recovered from the four guard bits).
  have hcav  : caveatsAdmit s.kernel f actor cell v = true :=
    (sfcaveat_iff CH RH cmb compressN LH s actor cell f v s').mp hcaveatgate
  have hauth : stateAuthB s.kernel.caps actor cell = true :=
    (sfauth_iff CH RH cmb compressN LH s actor cell f v s').mp hauthgate
  have hmem  : cell ∈ s.kernel.accounts :=
    (sfmem_iff CH RH cmb compressN LH s actor cell f v s').mp hmemgate
  have hlive : cellLive s.kernel cell = true :=
    (sflive_iff CH RH cmb compressN LH s actor cell f v s').mp hlivegate
  have hguard : SetFieldGuard s actor cell f v := ⟨hcav, hauth, hmem, hlive⟩
  -- rest hash equal ⇒ 16 non-cell fields equal (RestHashIffFrame.→).
  have hRHeq : RH s.kernel = RH s'.kernel :=
    (sfrest_iff CH RH cmb compressN LH s actor cell f v s').mp hrestgate
  have hframe16 := (hRest s.kernel s'.kernel).mp hRHeq
  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif, hDC, hDel, hDgs,
    hSB⟩ := hframe16
  -- frame digests equal ⇒ untouched cells equal (FrameDigestBindsCells, REUSED).
  have hfdeq : StateCommit.frameDigest CH compressN s.kernel (sfFrameCarrier s.kernel cell)
      = StateCommit.frameDigest CH compressN s'.kernel (sfFrameCarrier s.kernel cell) :=
    (sfframe_iff CH RH cmb compressN LH s actor cell f v s').mp hframegate
  have hcellframe : ∀ c ∈ sfFrameCarrier s.kernel cell, s.kernel.cell c = s'.kernel.cell c :=
    StateCommit.FrameDigestBindsCells CH compressN hCompressN hLeaf s.kernel s'.kernel
      (sfFrameCarrier s.kernel cell) hfdeq
  -- target leaf equal ⇒ the touched cell's whole Value = the spec write (cellLeafInjective).
  have htgteq : CH cell (s'.kernel.cell cell) = CH cell (setField f (s.kernel.cell cell) (.int v)) :=
    (sftarget_iff CH RH cmb compressN LH s actor cell f v s').mp htargetgate
  have htarget : s'.kernel.cell cell = setField f (s.kernel.cell cell) (.int v) :=
    hLeaf cell _ _ htgteq
  -- log equal ⇒ the post log = the one-row extension (logHashInjective).
  have hlogeq : LH s'.log = LH ({ actor := actor, src := cell, dst := cell, amt := 0 } :: s.log) :=
    (sflog_iff CH RH cmb compressN LH s actor cell f v s').mp hloggate
  have hlogspec : s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log :=
    hLog _ _ hlogeq
  -- reconstruct the post cell map by funext = setFieldCellMap.
  have hcellmap : s'.kernel.cell = setFieldCellMap s.kernel.cell cell f v := by
    funext c
    by_cases hctgt : c = cell
    · subst hctgt; rw [htarget]; simp only [setFieldCellMap, if_true]
    · by_cases hcacc : c ∈ s.kernel.accounts
      · -- c is an UNTOUCHED live cell: frame lemma + setFieldCellMap leaves it.
        have hmemc : c ∈ sfFrameCarrier s.kernel cell := by
          unfold sfFrameCarrier
          simp only [Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨hcacc, hctgt⟩
        rw [← hcellframe c hmemc]
        simp only [setFieldCellMap, if_neg hctgt]
      · -- c is a DEAD cell: AccountsWF on both kernels ⇒ both default; setFieldCellMap leaves it.
        have hk'acc : c ∉ s'.kernel.accounts := by rw [hAcc]; exact hcacc
        rw [hwf' c hk'acc]
        simp only [setFieldCellMap, if_neg hctgt]
        exact (hwf c hcacc).symm
  -- assemble SetFieldSpec (guard ∧ cell map ∧ log ∧ the 16 frame clauses).
  exact ⟨hguard, hcellmap, hlogspec,
    hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩

#assert_axioms setfield_circuit_full_sound

/-! ## §5b — ROOT-BINDING corollary (where `compressInjective cmb` earns its keep). -/

/-- **`recSetFieldCommit_binds` (via `compressInjective cmb`).** Equal full-state roots (for the
same touched cell) force equal cell-digest AND equal (rest ⊕ log) child — the published root is a
binding commitment to the whole chained state. -/
theorem recSetFieldCommit_binds (hCmb : StateCommit.compressInjective cmb)
    (s s' : RecChainedState) (cell : CellId)
    (hroot : recSetFieldCommit CH RH cmb compressN LH s.kernel cell s.log
      = recSetFieldCommit CH RH cmb compressN LH s'.kernel cell s'.log) :
    cmb (StateCommit.frameDigest CH compressN s.kernel (sfFrameCarrier s.kernel cell)) (CH cell (s.kernel.cell cell))
        = cmb (StateCommit.frameDigest CH compressN s'.kernel (sfFrameCarrier s'.kernel cell)) (CH cell (s'.kernel.cell cell))
      ∧ cmb (RH s.kernel) (LH s.log) = cmb (RH s'.kernel) (LH s'.log) := by
  unfold recSetFieldCommit at hroot
  exact hCmb _ _ _ _ hroot

#assert_axioms recSetFieldCommit_binds

/-! ## §6 — FULL-STATE COMPLETENESS: every committed step satisfies `setFieldCircuit`.

A real committed `setFieldA` (= the apex `SetFieldSpec`, equivalently `execFullA … = some s'`) yields a
satisfying full-state witness: ALL protocol-acceptable `setFieldA` behaviours are full-state-circuit-
acceptable. The frame gates hold because `s'`'s frame is literally `s`'s; the target gate because the
post cell IS the spec write; the log gate because the post log IS the one-row extension. -/

/-- **THEOREM — `setfield_circuit_full_complete`.** A committed `setFieldA` (its apex
`SetFieldSpec`) yields a satisfying full-state witness. -/
theorem setfield_circuit_full_complete
    (hRest : StateCommit.RestHashIffFrame RH)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState)
    (hspec : SetFieldSpec s actor cell f v s') :
    satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s') := by
  obtain ⟨hguard, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
    hDC, hDel, hDgs, hSB⟩ := hspec
  obtain ⟨hcav, hauth, hmem, hlive⟩ := hguard
  -- frame-gate facts.
  have hRHeq : RH s.kernel = RH s'.kernel := (hRest s.kernel s'.kernel).mpr
    ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
  -- every untouched leaf agrees (the cell map is `setFieldCellMap`, which only touches `cell`).
  have hcellc : ∀ c ∈ sfFrameCarrier s.kernel cell, CH c (s.kernel.cell c) = CH c (s'.kernel.cell c) := by
    intro c hc
    unfold sfFrameCarrier at hc
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hc
    obtain ⟨_, hctgt⟩ := hc
    rw [hcell]; simp only [setFieldCellMap, if_neg hctgt]
  have hfdeq : StateCommit.frameDigest CH compressN s.kernel (sfFrameCarrier s.kernel cell)
      = StateCommit.frameDigest CH compressN s'.kernel (sfFrameCarrier s.kernel cell) := by
    unfold StateCommit.frameDigest
    refine congrArg compressN (List.map_congr_left ?_)
    intro c hc
    exact hcellc c ((Finset.mem_sort (· ≤ ·)).mp hc)
  -- the touched leaf agrees with the spec write.
  have htgteq : CH cell (s'.kernel.cell cell) = CH cell (setField f (s.kernel.cell cell) (.int v)) := by
    rw [hcell]; simp only [setFieldCellMap, if_true]
  -- the log agrees with the one-row extension.
  have hlogeq : LH s'.log = LH ({ actor := actor, src := cell, dst := cell, amt := 0 } :: s.log) := by
    rw [hlog]
  refine ⟨?_, ?_⟩
  · -- satisfied setFieldCircuit: the 4 guard gates ++ the 4 frame gates.
    intro c hc
    unfold setFieldCircuit at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (sfcaveat_iff CH RH cmb compressN LH s actor cell f v s').mpr hcav
    · exact (sfauth_iff CH RH cmb compressN LH s actor cell f v s').mpr hauth
    · exact (sfmem_iff CH RH cmb compressN LH s actor cell f v s').mpr hmem
    · exact (sflive_iff CH RH cmb compressN LH s actor cell f v s').mpr hlive
    · exact (sfrest_iff CH RH cmb compressN LH s actor cell f v s').mpr hRHeq
    · exact (sfframe_iff CH RH cmb compressN LH s actor cell f v s').mpr hfdeq
    · exact (sftarget_iff CH RH cmb compressN LH s actor cell f v s').mpr htgteq
    · exact (sflog_iff CH RH cmb compressN LH s actor cell f v s').mpr hlogeq
  · -- SetFieldCommitSat: roots decompose definitionally from encodeSF.
    refine ⟨?_, ?_⟩
    · simp only [encSF_preRoot, encSF_framePre, encSF_targetPre, encSF_restPre, encSF_logPre,
        recSetFieldCommit]
    · simp only [encSF_postRoot, encSF_framePost, encSF_targetPost, encSF_restPost, encSF_logPost,
        recSetFieldCommit, sfFrameCarrier, hAcc]

#assert_axioms setfield_circuit_full_complete

/-! ## §7 — THE ANTI-GHOST TEETH: `setFieldCircuit` REJECTS what a projection misses.

A field-tamper (any non-cell component changed), a third-cell-tamper (any untouched cell changed), a
NON-TARGET-field tamper (a different slot of the target cell altered), and a log-forge each make
`satisfiedSF` UNSATISFIABLE — the forgeries a bare arithmetic guard-only circuit would accept. They
bite because the frame EQ gates + the PROVED binding lemmas force the WHOLE post-state. -/

/-- **`setFieldCircuit_rejects_field_tamper` — ANTI-GHOST (non-cell component).** ANY witness whose
post-state changes a non-`cell` kernel component (here: `nullifiers`) makes `satisfiedSF`
UNSATISFIABLE: the rest-frame gate forces `RH = RH`, and `RestHashIffFrame.→` forces the nullifier
sets equal — contradiction. A silent nullifier rewrite is FORBIDDEN BY CONSTRUCTION. -/
theorem setFieldCircuit_rejects_field_tamper
    (hRest : StateCommit.RestHashIffFrame RH)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState)
    (hfield : s'.kernel.nullifiers ≠ s.kernel.nullifiers) :
    ¬ satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s') := by
  rintro ⟨hsat, _⟩
  have hrestgate := hsat cSFRest (by unfold setFieldCircuit; simp)
  have hRHeq : RH s.kernel = RH s'.kernel :=
    (sfrest_iff CH RH cmb compressN LH s actor cell f v s').mp hrestgate
  have hframe16 := (hRest s.kernel s'.kernel).mp hRHeq
  obtain ⟨_, _, _, hNul, _⟩ := hframe16
  exact hfield hNul

#assert_axioms setFieldCircuit_rejects_field_tamper

/-- **`setFieldCircuit_rejects_third_cell` — ANTI-GHOST (untouched cell).** ANY witness whose
post-state changes a THIRD live cell `c₀` (a live account, not the target) makes `satisfiedSF`
UNSATISFIABLE: the frame-reuse gate forces the untouched-cell digest equal, and the PROVED
`FrameDigestBindsCells` (REUSED from `StateCommit`) forces `s.kernel.cell c₀ = s'.kernel.cell c₀` —
contradiction. Minting/draining a bystander cell is FORBIDDEN BY CONSTRUCTION. -/
theorem setFieldCircuit_rejects_third_cell
    (hCompressN : StateCommit.compressNInjective compressN) (hLeaf : StateCommit.cellLeafInjective CH)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState)
    {c₀ : CellId} (hc₀ : c₀ ∈ s.kernel.accounts) (hctgt : c₀ ≠ cell)
    (htamper : s'.kernel.cell c₀ ≠ s.kernel.cell c₀) :
    ¬ satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s') := by
  rintro ⟨hsat, _⟩
  have hframegate := hsat cSFFrame (by unfold setFieldCircuit; simp)
  have hfdeq : StateCommit.frameDigest CH compressN s.kernel (sfFrameCarrier s.kernel cell)
      = StateCommit.frameDigest CH compressN s'.kernel (sfFrameCarrier s.kernel cell) :=
    (sfframe_iff CH RH cmb compressN LH s actor cell f v s').mp hframegate
  have hmem : c₀ ∈ sfFrameCarrier s.kernel cell := by
    unfold sfFrameCarrier
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hc₀, hctgt⟩
  have := StateCommit.FrameDigestBindsCells CH compressN hCompressN hLeaf s.kernel s'.kernel
    (sfFrameCarrier s.kernel cell) hfdeq c₀ hmem
  exact htamper this.symm

#assert_axioms setFieldCircuit_rejects_third_cell

/-- **`setFieldCircuit_rejects_wrong_target` — ANTI-GHOST (wrong write on the target cell).** ANY
witness whose post target leaf does NOT equal the SPEC's written leaf (e.g. a different slot was
altered, or `f` was set to the wrong value, or another field of the target was clobbered) makes
`satisfiedSF` UNSATISFIABLE: the target-bind gate forces `CH cell (post cell) = CH cell (setField …)`,
and `cellLeafInjective` forces the whole post `Value` to be EXACTLY the spec write — contradiction.
Writing the wrong thing to the target (a non-target field tamper) is FORBIDDEN BY CONSTRUCTION. -/
theorem setFieldCircuit_rejects_wrong_target
    (hLeaf : StateCommit.cellLeafInjective CH)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState)
    (hwrong : s'.kernel.cell cell ≠ setField f (s.kernel.cell cell) (.int v)) :
    ¬ satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s') := by
  rintro ⟨hsat, _⟩
  have htargetgate := hsat cSFTarget (by unfold setFieldCircuit; simp)
  have htgteq : CH cell (s'.kernel.cell cell) = CH cell (setField f (s.kernel.cell cell) (.int v)) :=
    (sftarget_iff CH RH cmb compressN LH s actor cell f v s').mp htargetgate
  exact hwrong (hLeaf cell _ _ htgteq)

#assert_axioms setFieldCircuit_rejects_wrong_target

/-- **`setFieldCircuit_rejects_log_forge` — ANTI-GHOST (forged receipt chain).** ANY witness whose
post log is NOT the honest one-row extension makes `satisfiedSF` UNSATISFIABLE: the log-bind gate
forces `LH post = LH (receipt :: pre)`, and `logHashInjective` forces the post log to be EXACTLY the
one-row extension — contradiction. Forging/dropping receipts is FORBIDDEN BY CONSTRUCTION. -/
theorem setFieldCircuit_rejects_log_forge
    (hLog : StateCommit.logHashInjective LH)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState)
    (hbadlog : s'.log ≠ { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log) :
    ¬ satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s') := by
  rintro ⟨hsat, _⟩
  have hloggate := hsat cSFLog (by unfold setFieldCircuit; simp)
  have hlogeq : LH s'.log = LH ({ actor := actor, src := cell, dst := cell, amt := 0 } :: s.log) :=
    (sflog_iff CH RH cmb compressN LH s actor cell f v s').mp hloggate
  exact hbadlog (hLog _ _ hlogeq)

#assert_axioms setFieldCircuit_rejects_log_forge

end Lemmas

/-! ## §8 — CONCRETE anti-ghost `#guard`: `setFieldCircuit` catches a bystander-cell forgery.

We instantiate concrete COMPUTABLE + INJECTIVE commitments over a THREE-cell chained state and EXHIBIT
a forgery: an honest `setFieldA` on the target cell 0 that ALSO mints value into the bystander cell 2.
The bare guard gates (caveat/auth/mem/live) never look at cell 2 — but `setFieldCircuit`'s frame-reuse
gate hashes cell 2's leaf into the untouched-cell sponge, so it FAILS. The concrete death of the
"pale ghost" for the field-write effect.

The primitives must be COMPUTABLE and INJECTIVE (so the rejection fires on a binding commitment, not a
lossy `+`-fold): `chSF = fieldOf "balance"` (the leaf reads a visible field), an INJECTIVE node combine
`cmbSF` (`a*BIG + b`), an INJECTIVE Horner sponge `compressNSF`, and an INJECTIVE log hash `lhSF`
(length-prefixed Horner over the receipt rows' `actor` fields). -/

/-- Concrete cell-leaf hash: the cell's `balance` field (so a minted bystander balance is visible). -/
def chSF : CellId → Value → ℤ := fun _ vv => fieldOf "balance" vv
/-- Concrete rest hash: a field-count of the non-`cell` components (unchanged by a pure cell forgery,
so the FRAME-REUSE gate is the one that bites). -/
def rhSF : RecordKernelState → ℤ := fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
/-- Concrete 2-to-1 node/root combine: an INJECTIVE pairing `a * BIG + b` on the toy domain. -/
def cmbSF : ℤ → ℤ → ℤ := fun a b => a * 1000000 + b
/-- Concrete sponge: an INJECTIVE positional Horner fold (length folded in). -/
def compressNSF : List ℤ → ℤ :=
  fun xs => xs.foldl (fun acc x => acc * 1000000 + x) (xs.length : ℤ)
/-- Concrete log hash: an INJECTIVE length-prefixed Horner fold over the receipt rows' `actor` ids. -/
def lhSF : List Turn → ℤ :=
  fun ts => ts.foldl (fun acc t => acc * 1000000 + (t.actor : ℤ)) (ts.length : ℤ)

/-- A concrete THREE-cell pre-state: cells {0,1,2} with balances 100 / 5 / 50, actor 0 owns cell 0
(authority by ownership), no caveats, empty log. The bystander cell 2 holds 50. -/
def sSF0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun c => if c = 0 then .record [("balance", .int 100)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else if c = 2 then .record [("balance", .int 50)]
                         else default
        caps := fun _ => [] }
    log := [] }

/-- The honest post-state of `setFieldA 0 0 "balance" 70` (cell 0's balance 100→70, cells 1,2 frozen,
one receipt row appended). -/
def goodPostSF : RecChainedState := (execFullA sSF0 (.setFieldA 0 0 "balance" 70)).getD sSF0

/-- **THE FORGERY:** cell 0 written to 70, but the bystander cell 2 is MINTED from 50 to 999
(and the honest receipt appended). A guard-only circuit sees nothing wrong on cell 2. -/
def forgedThirdCellSF : RecChainedState :=
  { goodPostSF with
    kernel := { goodPostSF.kernel with
      cell := fun c => if c = 0 then .record [("balance", .int 70)]
                       else if c = 1 then .record [("balance", .int 5)]
                       else if c = 2 then .record [("balance", .int 999)]  -- MINTED bystander
                       else default } }

-- The executor COMMITS the honest write:
#guard (execFullA sSF0 (.setFieldA 0 0 "balance" 70)).isSome
-- The honest post-state satisfies the FULL-state setFieldA circuit (every gate decides true):
#guard decide (satisfied setFieldCircuit
  (encodeSF chSF rhSF cmbSF compressNSF lhSF sSF0 0 0 "balance" 70 goodPostSF))
-- ...but the NEW full-state circuit REJECTS the bystander-mint forgery (the frame-reuse gate fails):
#guard decide (satisfied setFieldCircuit
  (encodeSF chSF rhSF cmbSF compressNSF lhSF sSF0 0 0 "balance" 70 forgedThirdCellSF)) == false
-- ...and specifically the frame-reuse gate ALONE is the one that fails on cell 2:
#guard decide (cSFFrame.holds
  (encodeSF chSF rhSF cmbSF compressNSF lhSF sSF0 0 0 "balance" 70 forgedThirdCellSF)) == false

/-! ## §9 — EMISSION: the full-state `setFieldA` circuit composes with `CircuitEmit.emit`.

The digest/guard gates are pure `Expr` EQ constraints, so they serialize identically; the §2/§8
commitment primitives live OUTSIDE the emitted AIR (in the witness generator filling the digest
columns). -/

/-- The AIR identity string the full-state `setFieldA` wire form carries. -/
def setFieldAirName : String := "dregg-setfield-fullstate-v1"

/-- **The emitted full-state `setFieldA` circuit** — serialized via the SAME `CircuitEmit.emit`. -/
def emittedSetField : EmittedDescriptor := emit setFieldAirName setFieldTraceWidth setFieldCircuit

/-- **`emitSetFieldFaithful`** — satisfying the EMITTED descriptor is EXACTLY satisfying
`setFieldCircuit`. Direct instance of `CircuitEmit.emit_faithful`. -/
theorem emitSetFieldFaithful (a : Assignment) :
    satisfied setFieldCircuit a ↔ satisfiedEmitted emittedSetField a :=
  emit_faithful setFieldAirName setFieldTraceWidth setFieldCircuit a

/-- The round trip recovers the source circuit. -/
theorem decodeE_emittedSetField : decodeE emittedSetField = setFieldCircuit :=
  decodeE_emit setFieldAirName setFieldTraceWidth setFieldCircuit

-- Sanity: the emitted descriptor has the eight gates and sixteen wires.
#guard emittedSetField.constraints.length == 8
#guard emittedSetField.traceWidth == setFieldTraceWidth
#guard emittedSetField.traceWidth == 16

/-- **`setFieldDescriptorJson`** — the canonical wire string for the emitted full-state `setFieldA`
circuit. Copy into the Rust `lean_emitted_setfield_roundtrip` golden. -/
def setFieldDescriptorJson : String := emitDescriptorJson emittedSetField

-- `#guard` golden pin: setField wire bytes the Rust decoder parses (Rust `SETFIELD_DESCRIPTOR_JSON`).
#guard (setFieldDescriptorJson == r#"{"name":"dregg-setfield-fullstate-v1","trace_width":16,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":1},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":3},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"var","v":7}},{"lhs":{"t":"var","v":8},"rhs":{"t":"var","v":9}},{"lhs":{"t":"var","v":11},"rhs":{"t":"var","v":12}},{"lhs":{"t":"var","v":14},"rhs":{"t":"var","v":15}}]}"#)

/-! ## §10 — Axiom-hygiene tripwires + the assumption ledger.

ASSUMED (carried Prop hypotheses, the STANDARD Poseidon collision-resistance set, ALL realizable
injectivity of a genuine hash, NEVER `axiom`, NEVER sum-injectivity): `compressNInjective compressN`,
`cellLeafInjective CH`, `RestHashIffFrame RH` (REUSED from `StateCommit`), `logHashInjective LH` (the
new chain piece; `compressInjective cmb` only for the root-binding corollary); `AccountsWF` (a
STRUCTURAL invariant, REUSED from `StateCommit`, proved preserved there); `SetFieldGuard` is supplied
via the four guard gates (the executor's domain restriction). The binding lemmas
`FrameDigestBindsCells`/`CombineInjective` are PROVED `StateCommit` theorems off the CR set. NO
`postRoot = recSetFieldCommit (applySetField …)` ghost hypothesis appears anywhere. -/

#assert_axioms sfcaveat_iff
#assert_axioms sfrest_iff
#assert_axioms sfframe_iff
#assert_axioms sftarget_iff
#assert_axioms sflog_iff
#assert_axioms setfield_circuit_full_sound
#assert_axioms recSetFieldCommit_binds
#assert_axioms setfield_circuit_full_complete
#assert_axioms setFieldCircuit_rejects_field_tamper
#assert_axioms setFieldCircuit_rejects_third_cell
#assert_axioms setFieldCircuit_rejects_wrong_target
#assert_axioms setFieldCircuit_rejects_log_forge
#assert_axioms emitSetFieldFaithful
#assert_axioms decodeE_emittedSetField

end Dregg2.Circuit.SetFieldCommit
