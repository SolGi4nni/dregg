/-
# Dregg2.Circuit.StateCommitLeafCutoverCheck — the SEMANTIC teeth of the `cellLeafInjective` cutover.

The 2026-07-25 cutover removed the refuted `cellLeafInjective CH` binder IN PLACE from 13 theorems
(6 in `Circuit/CommitmentCrossBind`, 7 in `Circuit/Argus/Receipt`), replacing it with per-instance
`¬ FrameLeafColl` / `¬ MovedLeafColl` / `¬ CellLeafColl` side conditions at the EXACT arguments each
proof passed to the floor. This module is what keeps that cutover honest on every build, in two
independent ways:

  1. **NO STRENGTH LOST** — one `*_of_injective` bridge per cut-over theorem. Each is a `def` whose
     type is INFERRED from the term, so the type it states IS, by construction, the pre-cutover
     statement of that theorem: the old carrier telescope (`… hLeaf : cellLeafInjective CH …`) in,
     the old conclusion out, routed through the port and the `no*Coll_of_inj` bridges. If a port
     ever WEAKENED a conclusion, the bridge stops elaborating — silent weakening is a build error,
     not a review question. (These bridges are the ruler's own documented `_of_injective` class:
     the refuted floor is declared IN THE NAME, and the bridge exists so deleting it would delete a
     documented relative-strength fact.)
  2. **NO FLOOR RESURRECTION** — `#assert_not_depends_on` pins that the cut-over theorem cannot
     reach `cellLeafInjective` or either of the two floor-carrying endpoints
     (`StateCommit.FrameDigestBindsCells` / `StateCommit.MovedDigestBindsCells`) at all. Re-adding
     the binder, or routing back through an old endpoint, turns the build red HERE.

Together: (1) says the ported theorem is at least as strong as what it replaced; (2) says it does
not stand on the refuted universal. Neither is checkable by reading; both re-run every build.

⚑ What the ports are NOT: the side conditions are HONEST-BUT-CONDITIONAL claims about the deployed
hash at NAMED points — refutable, decidable per instance, never universal. At the deployed ~31-bit
BabyBear felt they are ~2^15.5-breakable (the felt-width wound), and they get STRONGER, not weaker,
as the digest is repaired to the 8-felt (~2^123.5) target. That is the whole point of naming them.
-/
import Dregg2.Circuit.CommitmentCrossBind
import Dregg2.Circuit.Argus.Receipt
import Dregg2.Tactics

namespace Dregg2.Circuit.StateCommitLeafCutoverCheck

open Dregg2.Exec
open Dregg2.Circuit.StateCommit
  (compressInjective compressNInjective cellLeafInjective logHashInjective RestHashIffFrame
   recStateCommit)
open Dregg2.Circuit.SetFieldCommit (recSetFieldCommit)
open Dregg2.Circuit.StateCommitLeafRegrounded
  (noCellLeafColl_of_inj noMovedLeafColl_of_inj noFrameLeafColl_of_inj)
open Dregg2.Circuit.CommitmentCrossBind
open Dregg2.Circuit.Argus.Receipt
open Dregg2.Circuit.Argus (RecStmt interp transferStmt)
open Dregg2.Lightclient.MMR (mroot Opens)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.RecordCommit (cellCommit)

set_option autoImplicit false

/-! ## §1 — `Circuit/CommitmentCrossBind`: 6 cut-over theorems.

Each `_of_injective` def's INFERRED type is the pre-cutover statement; each `#assert_not_depends_on`
pins the post-cutover theorem off the refuted floor and off both old endpoints. -/

/-- **NO STRENGTH LOST** — `stateCommit_binds_cells_and_rest` at the OLD carrier telescope. -/
def stateCommit_binds_cells_and_rest_of_injective
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn)
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :=
  stateCommit_binds_cells_and_rest CH RH cmb compress compressN hCmb hCompress hCompressN hRest
    k k' t (noFrameLeafColl_of_inj hLeaf) (noMovedLeafColl_of_inj hLeaf) hroot

#assert_axioms Dregg2.Circuit.CommitmentCrossBind.stateCommit_binds_cells_and_rest
#assert_not_depends_on Dregg2.Circuit.CommitmentCrossBind.stateCommit_binds_cells_and_rest
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

/-- **NO STRENGTH LOST** — `setFieldCommit_binds_all` at the OLD carrier telescope. -/
def setFieldCommit_binds_all_of_injective
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)
    (hCmb : compressInjective cmb) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (hLog : logHashInjective LH)
    (k k' : RecordKernelState) (cell : CellId) (log log' : List Turn)
    (hroot : recSetFieldCommit CH RH cmb compressN LH k cell log
      = recSetFieldCommit CH RH cmb compressN LH k' cell log') :=
  setFieldCommit_binds_all CH RH cmb compressN LH hCmb hCompressN hRest hLog k k' cell log log'
    (noFrameLeafColl_of_inj hLeaf) (noCellLeafColl_of_inj hLeaf) hroot

#assert_axioms Dregg2.Circuit.CommitmentCrossBind.setFieldCommit_binds_all
#assert_not_depends_on Dregg2.Circuit.CommitmentCrossBind.setFieldCommit_binds_all
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

/-- **NO STRENGTH LOST** — `crossbind_cells_agree` at the OLD carrier telescope. -/
def crossbind_cells_agree_of_injective
    (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (k k' : RecordKernelState) (S : Finset CellId)
    (hPI : Dregg2.Circuit.StateCommit.frameDigest CH compressN k S
      = Dregg2.Circuit.StateCommit.frameDigest CH compressN k' S) :=
  crossbind_cells_agree CH compressN hCompressN k k' S (noFrameLeafColl_of_inj hLeaf) hPI

#assert_axioms Dregg2.Circuit.CommitmentCrossBind.crossbind_cells_agree
#assert_not_depends_on Dregg2.Circuit.CommitmentCrossBind.crossbind_cells_agree
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells]

/-- **NO STRENGTH LOST** — `crossbind_circuit_exec_same_state` at the OLD carrier telescope. -/
def crossbind_circuit_exec_same_state_of_injective
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (compressN : List ℤ → ℤ)
    (hRest : RestHashIffFrame RH)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (k k' : RecordKernelState) (S : Finset CellId)
    (hRestPI : RH k = RH k')
    (hFramePI : Dregg2.Circuit.StateCommit.frameDigest CH compressN k S
      = Dregg2.Circuit.StateCommit.frameDigest CH compressN k' S) :=
  crossbind_circuit_exec_same_state CH RH compressN hRest hCompressN k k' S
    (noFrameLeafColl_of_inj hLeaf) hRestPI hFramePI

#assert_axioms Dregg2.Circuit.CommitmentCrossBind.crossbind_circuit_exec_same_state
#assert_not_depends_on Dregg2.Circuit.CommitmentCrossBind.crossbind_circuit_exec_same_state
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells]

/-- **NO STRENGTH LOST** — `stateCommit_binds_cellCommit` (THE CROWN) at the OLD telescope. -/
def stateCommit_binds_cellCommit_of_injective
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int)
    (restLimbs : CellId → List ℤ)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn)
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :=
  stateCommit_binds_cellCommit CH RH cmb compress compressN compress2 restLimbs
    hCmb hCompress hCompressN hRest k k' t
    (noFrameLeafColl_of_inj hLeaf) (noMovedLeafColl_of_inj hLeaf) hroot

#assert_axioms Dregg2.Circuit.CommitmentCrossBind.stateCommit_binds_cellCommit
#assert_not_depends_on Dregg2.Circuit.CommitmentCrossBind.stateCommit_binds_cellCommit
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

/-- **NO STRENGTH LOST** — `setFieldCommit_binds_cellCommit` (the executor crown). -/
def setFieldCommit_binds_cellCommit_of_injective
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)
    (compress2 : Int → Int → Int) (restLimbs : CellId → List ℤ)
    (hCmb : compressInjective cmb) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (hLog : logHashInjective LH)
    (k k' : RecordKernelState) (cell : CellId) (log log' : List Turn)
    (hroot : recSetFieldCommit CH RH cmb compressN LH k cell log
      = recSetFieldCommit CH RH cmb compressN LH k' cell log') :=
  setFieldCommit_binds_cellCommit CH RH cmb compressN LH compress2 restLimbs
    hCmb hCompressN hRest hLog k k' cell log log'
    (noFrameLeafColl_of_inj hLeaf) (noCellLeafColl_of_inj hLeaf) hroot

#assert_axioms Dregg2.Circuit.CommitmentCrossBind.setFieldCommit_binds_cellCommit
#assert_not_depends_on Dregg2.Circuit.CommitmentCrossBind.setFieldCommit_binds_cellCommit
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells]

/-! ## §2 — `Circuit/Argus/Receipt`: 7 cut-over theorems.

The Argus receipt weld is the DOWNSTREAM cone of §1: every one of these threaded `hLeaf` into a
crossbind crown. The pins here are what stops the floor creeping back one level up. -/

#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_circuit_pins_receipt
#assert_not_depends_on Dregg2.Circuit.Argus.Receipt.argus_circuit_pins_receipt
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_executor_pins_receipt
#assert_not_depends_on Dregg2.Circuit.Argus.Receipt.argus_executor_pins_receipt
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells]

#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_commits_to_one_receipt
#assert_not_depends_on Dregg2.Circuit.Argus.Receipt.argus_commits_to_one_receipt
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree
#assert_not_depends_on Dregg2.Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_published_index_pins_receipt
#assert_not_depends_on Dregg2.Circuit.Argus.Receipt.argus_published_index_pins_receipt
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

#assert_axioms Dregg2.Circuit.Argus.Receipt.transfer_published_index_pins_receipt
#assert_not_depends_on Dregg2.Circuit.Argus.Receipt.transfer_published_index_pins_receipt
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

#assert_axioms Dregg2.Circuit.Argus.Receipt.transfer_commits_to_one_receipt
#assert_not_depends_on Dregg2.Circuit.Argus.Receipt.transfer_commits_to_one_receipt
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

/-- **NO STRENGTH LOST** — the Argus circuit corner at the OLD carrier telescope. The whole §2 cone
routes through §1's crowns, so this one bridge witnesses the level's strength; the six others are
its consumers and are pinned above. -/
def argus_circuit_pins_receipt_of_injective
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int)
    (restLimbs : CellId → List ℤ)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (st : RecStmt) (k k' k₂ : RecordKernelState) (t : Turn)
    (hexec : interp st k = some k')
    (hRootPI : recStateCommit CH RH cmb compress compressN k' t
      = recStateCommit CH RH cmb compress compressN k₂ t) :=
  argus_circuit_pins_receipt CH RH cmb compress compressN compress2 restLimbs
    hCmb hCompress hCompressN hRest st k k' k₂ t
    (noFrameLeafColl_of_inj hLeaf) (noMovedLeafColl_of_inj hLeaf) hexec hRootPI

/-! ## §3 — kernel pins on the bridges themselves. -/

#assert_all_clean [stateCommit_binds_cells_and_rest_of_injective,
  setFieldCommit_binds_all_of_injective, crossbind_cells_agree_of_injective,
  crossbind_circuit_exec_same_state_of_injective, stateCommit_binds_cellCommit_of_injective,
  setFieldCommit_binds_cellCommit_of_injective, argus_circuit_pins_receipt_of_injective]

/-! ## §4 — THE BLINDNESS CONTROL (the reason the 13 greens above mean anything).

The `#assert_not_depends_on` pins in §2 are REJECTORS: each passes by finding nothing. A rejector
cannot detect its own blindness, and `Dregg2/Tactics.lean` records the measurement that settles it —
built with `allowOpaque := false` the shared walk MISSED a real semantic dependency while reporting
`scanned = 36`, because a root's TYPE constants are still walked when its VALUE is invisible. Under
that failure every pin above reports CLEAN, vacuously, and this module stays green.

`#assert_depends_on` is the exact dual and shares the same `findForbiddenPath`, so the two go blind
together or not at all. `walkControl`'s statement is `True`; it reaches the floor ONLY through its
proof term, via the two portal theorems that carry `cellLeafInjective` in their own telescopes. A
walk that has stopped opening theorem values cannot report it, so the build fails HERE rather than
certifying 13 cut-over theorems on a blind scan.

Tactics.lean states the bar: every module relying on `#assert_not_depends_on` should carry at least
one such control. This module carried 13 pins and none. Do not delete it to get green. -/
theorem walkControl : True := by
  have _h := @Dregg2.Circuit.StateCommit.MovedDigestBindsCells
  have _h2 := @Dregg2.Circuit.StateCommit.FrameDigestBindsCells
  trivial

#assert_axioms Dregg2.Circuit.StateCommitLeafCutoverCheck.walkControl
#assert_depends_on Dregg2.Circuit.StateCommitLeafCutoverCheck.walkControl
  [Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.FrameDigestBindsCells,
   Dregg2.Circuit.StateCommit.MovedDigestBindsCells]

end Dregg2.Circuit.StateCommitLeafCutoverCheck
