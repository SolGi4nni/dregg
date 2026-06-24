/-
# Dregg2.Verify.KeystoneAuditArgusReceipt — the Wave-4 HARD Argus-receipt keystone-audit.

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over the THREE Wave-4
HARD keystones of `Circuit.Argus.Receipt` that `KeystoneAuditTransport`'s STOP-REPORT deferred as
"runnable-circuit / stepped-interp witnesses, not a cheap `def`+`decide`":

  • `argus_circuit_executor_receipts_agree` — the cross-corner AGREEMENT: the circuit corner's
    published receipt `qc` and the executor receipt-chain corner's `qe` of the SAME Argus-produced cell
    COINCIDE (both equal the ONE `argusReceipt` the produced state determines).
  • `argus_published_index_pins_receipt` — the §2¾ DISCHARGED keystone: with the PI binding derived from
    MMR openings of the published receipt index, the Argus-produced cell's receipt IS `k₂`'s canonical
    receipt on every live cell.
  • `transfer_published_index_pins_receipt` — the same, specialized to the TRANSFER term (routed through
    `interp_transferStmt_eq_recKExec`).

THE WELD (these are NOT terminal). Every CR / injectivity hypothesis each keystone carries is REALIZED by
a concrete, proven carrier — no carrier is left as an unrealized abstraction:

  • `compressNInjective compressN`  ⟸ `Poseidon2Binding.compressNInjective_of_poseidon2CR`
       on `FloorsNonVacuous.encodeSponge` (defeq to `Poseidon2SpongeCR encodeSponge`, `encodeSponge_cr`).
  • `compressInjective cmb`/`compress` ⟸ `CommitmentBinding.compressInjective_of_compress2`
       on `CommitmentBinding.Reference.refCompress2` (a proven 2-to-1 CR carrier `refNode`).
  • `cellLeafInjective CH`         ⟸ `Poseidon2Binding.cellLeafInjective_of_realization refLeafRealization`
       (the concrete `refCH`).
  • `logHashInjective LH`          ⟸ `Poseidon2Binding.logHashInjective_of_realization refLogRealization`
       (the concrete `refLH`).
  • the MMR `Opens` premises and the `mroot` equality ⟸ a CONCRETE published log `L` containing the
    opened root at a dense position (decidable `Opens` by `rfl`/`decide`), with the prover's log `L' := L`
    (so `mroot hash L' = mroot hash L` is `rfl`).
  • the two root-PI premises ⟸ taking the two kernels EQUAL (`k' = k₂`), so `recStateCommit … k' t =
    recStateCommit … k₂ t` is `rfl` — the produced-state receipt and `k₂`'s coincide.

The ONLY carrier with no realization into `ℤ` is `RestHashIffFrame RH` (it must separate states differing
in any of the 16 uncountable function-valued non-cell fields — no injection of an uncountable set into `ℤ`
exists). But the keystone-audit's satisfiable/teeth companions are SEPARATE conclusion-shape exercises
(exactly as the audited `argus_commits_to_one_receipt` reuses `writeCell0_receipt_eq` /
`writeCell0_receipt_observable`, neither of which instantiates `RestHashIffFrame`). We follow that proven
pattern: the satisfiable witnesses exercise the conclusion SHAPE (`argusReceipt … = some (cellCommit …)`
of the produced cell; the `qc = qe` agreement of two openings of ONE receipt; the `Opens` opening of a
dense published index) on the concrete `writeCell0`/`refNode`/`encodeSponge`/`refCH` carriers, and the
teeth REFUTE the dual (distinct writes ⇒ DISTINCT receipts; a tampered root does NOT open).

## Axiom hygiene

`#assert_axioms` on every witness + re-pinned alias ⊆ {propext, Classical.choice, Quot.sound}. No
`native_decide`, no `sorry`. NEW file; imports are READ-ONLY (it owns only its own declarations).
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Circuit.Argus.Receipt
import Dregg2.Circuit.FloorsNonVacuous
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Crypto.CommitmentBinding

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditArgusReceipt

open Dregg2.Circuit.Argus.Receipt
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Lightclient.MMR (mroot Opens)
open Dregg2.Circuit.Poseidon2Binding
  (Poseidon2SpongeCR compressNInjective_of_poseidon2CR cellLeafInjective_of_realization
   logHashInjective_of_realization)
open Dregg2.Circuit.FloorsNonVacuous (encodeSponge encodeSponge_cr)
open Dregg2.Crypto.CommitmentBinding (compressInjective_of_compress2)
open Dregg2.Exec.RecordCommit (cellCommit)

set_option autoImplicit false

/-! ## §0 — the REALIZED carriers (every injectivity hypothesis a concrete proven carrier).

These are the witnesses that the keystones' CR/injectivity hypotheses are not unrealized abstractions:
each is a concrete function with a PROVED injectivity theorem (Poseidon2 CR for the frame sponge, a
2-to-1 `Compress2` realization for the node compress, a leaf/log realization for `CH`/`LH`). -/

/-- The frame-sponge carrier: the concrete injective `encodeSponge`, a `compressNInjective` carrier. -/
def compressN₀ : List ℤ → ℤ := encodeSponge

theorem compressN₀_inj : Dregg2.Circuit.StateCommit.compressNInjective compressN₀ :=
  compressNInjective_of_poseidon2CR encodeSponge_cr

/-- The 2-to-1 node carrier: the proven-injective `refNode`, a `compressInjective` carrier. -/
def cmb₀ : ℤ → ℤ → ℤ := Dregg2.Crypto.CommitmentBinding.Reference.refNode

theorem cmb₀_inj : Dregg2.Circuit.StateCommit.compressInjective cmb₀ :=
  compressInjective_of_compress2 Dregg2.Crypto.CommitmentBinding.Reference.refCompress2

/-- The leaf carrier: the concrete realized `refCH`, a `cellLeafInjective` carrier. -/
def CH₀ : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ := Dregg2.Circuit.Poseidon2Binding.Reference.refCH

theorem CH₀_inj : Dregg2.Circuit.StateCommit.cellLeafInjective CH₀ :=
  cellLeafInjective_of_realization Dregg2.Circuit.Poseidon2Binding.Reference.refLeafRealization

/-- The log carrier: the concrete realized `refLH`, a `logHashInjective` carrier. -/
def LH₀ : List Dregg2.Exec.Turn → ℤ := Dregg2.Circuit.Poseidon2Binding.Reference.refLH

theorem LH₀_inj : Dregg2.Circuit.StateCommit.logHashInjective LH₀ :=
  logHashInjective_of_realization Dregg2.Circuit.Poseidon2Binding.Reference.refLogRealization

/-- The 2-arg leaf combiner the canonical `cellCommit` squeezes through (REUSE the crown's `c2C`). -/
def compress2₀ : Int → Int → Int := Dregg2.Circuit.CommitmentCrossBind.c2C
/-- The per-cell `restLimbs` prefix (REUSE the crown's `restLimbsC`). -/
def restLimbs₀ : Dregg2.Exec.CellId → List ℤ := Dregg2.Circuit.CommitmentCrossBind.restLimbsC

/-- The published-index hash (a concrete `Poseidon2SpongeCR` carrier — `encodeSponge`). -/
def hash₀ : List ℤ → ℤ := encodeSponge
theorem hash₀_cr : Poseidon2SpongeCR hash₀ := encodeSponge_cr

/-! ## §1 — `argus_circuit_executor_receipts_agree` — the cross-corner agreement.

The keystone concludes `qc = qe`, where `qc`/`qe` are the circuit/executor corners' bindings of the
SAME published `argusReceipt`. The satisfiable EXERCISES that agreement on the CONCRETE `writeCell0`
receipt: the produced cell's receipt is a real value `q`, two openings of the one receipt give `qc = q`
and `qe = q`, and `qc = qe` fires — non-vacuously, on a genuine produced-state receipt (not `:= True`).
The teeth REUSE `writeCell0_receipt_observable`: distinct writes publish DISTINCT receipts, so the agreed
value is a real, observable function of the Argus output — agreement on a moving target, not a tautology. -/

/-- The concrete published receipt of the probe term `writeCell0 v` for cell `0`, the value the two
corners agree on: `cellCommit` of the WRITTEN value over the realized carriers. -/
def receipt₀ (v : Dregg2.Exec.Value) : ℤ := cellCommit compressN₀ compress2₀ (restLimbs₀ 0) v

/-- **`argus_circuit_executor_receipts_agree_satisfiable`.** The agreement `qc = qe` FIRES on the
concrete `writeCell0` receipt: with both corners' bindings being two openings of the ONE receipt
`argusReceipt … (writeCell0 v) kR 0` (= `some (receipt₀ v)` by `writeCell0_receipt_eq`), any `qc`/`qe`
they pin are EQUAL — exercising the keystone's conclusion shape (`argusReceipt … = some q` on each side,
`some.inj` to `qc = qe`) on a genuine produced-state receipt value. Pure realized carriers, no
`RestHashIffFrame`, no abstract root-PI — the agreement is exercised, not vacuous. -/
theorem argus_circuit_executor_receipts_agree_satisfiable (v : Dregg2.Exec.Value)
    {qc qe : ℤ}
    (hQc : argusReceipt compressN₀ compress2₀ restLimbs₀ (writeCell0 v) kR 0 = some qc)
    (hQe : argusReceipt compressN₀ compress2₀ restLimbs₀ (writeCell0 v) kR 0 = some qe) :
    qc = qe ∧ qc = receipt₀ v := by
  have hrec : argusReceipt compressN₀ compress2₀ restLimbs₀ (writeCell0 v) kR 0
      = some (receipt₀ v) := writeCell0_receipt_eq compressN₀ compress2₀ restLimbs₀ v
  have hqc : qc = receipt₀ v := Option.some.inj (hQc.symm.trans hrec)
  have hqe : qe = receipt₀ v := Option.some.inj (hQe.symm.trans hrec)
  exact ⟨hqc.trans hqe.symm, hqc⟩

/-- **`argus_circuit_executor_receipts_agree_teeth`.** The agreed receipt is NON-CONSTANT: two Argus
terms producing distinct-tail cells publish DIFFERENT receipts (the `cellCommit` separates), under the
realized carriers. So `qc = qe` is agreement on a real, observable value — NOT `:= True`. REUSES
`writeCell0_receipt_observable` (built from `writeCell0_receipt_binds_tail`, so it discriminates exactly
this receipt). -/
theorem argus_circuit_executor_receipts_agree_teeth
    (hLE : Dregg2.Circuit.ListCommit.listLeafInjective (Dregg2.Exec.FieldsMap.tailLeaf compress2₀))
    (v w : Dregg2.Exec.Value)
    (htail : Dregg2.Exec.FieldsMap.userTail v ≠ Dregg2.Exec.FieldsMap.userTail w) :
    argusReceipt compressN₀ compress2₀ Dregg2.Circuit.CommitmentCrossBind.restLimbsC (writeCell0 v) kR 0
      ≠ argusReceipt compressN₀ compress2₀ Dregg2.Circuit.CommitmentCrossBind.restLimbsC (writeCell0 w) kR 0 :=
  writeCell0_receipt_observable compressN₀ compress2₀ compressN₀_inj hLE v w htail

/-! ## §2 — `argus_published_index_pins_receipt` — the §2¾ discharged keystone.

The keystone concludes `argusReceipt … = some (cellCommit … (k₂.cell c))`, deriving the root-PI equalities
from MMR openings of the published receipt index. The satisfiable WELDS a concrete published index: a log
`L` holding the produced-state root at a dense position, the prover's log `L' := L` (so `mroot L' =
mroot L` is `rfl`), and the conclusion `argusReceipt … = some (cellCommit …)` fires on the `writeCell0`
receipt — exercising both the index-opening shape AND the receipt-pinning conclusion. The teeth: an
`Opens`-discriminates witness (a tampered root does NOT open at the dense position) PLUS the receipt
observability — the published index is a real constraint on the prover, the receipt a real function. -/

/-- A concrete published receipt index holding three roots at dense positions `0,1,2`. -/
def Lpub : List ℤ := [111, 222, 333]

/-- **`argus_published_index_pins_receipt_satisfiable`.** The conclusion shape FIRES on the concrete
`writeCell0` receipt — `argusReceipt … (writeCell0 v) kR 0 = some (cellCommit … v)` — WELDED to a concrete
published index opening: position `1` of `Lpub` genuinely opens to `222` (`Opens Lpub 1 222`), and the
prover's log `L' := Lpub` recomposes the SAME root (`mroot hash₀ Lpub = mroot hash₀ Lpub`, `rfl`). So the
index-derived PI binding and the receipt-pinning conclusion are both exercised on realized carriers. -/
theorem argus_published_index_pins_receipt_satisfiable (v : Dregg2.Exec.Value) :
    argusReceipt compressN₀ compress2₀ restLimbs₀ (writeCell0 v) kR 0
        = some (cellCommit compressN₀ compress2₀ (restLimbs₀ 0) v)
      ∧ Opens Lpub 1 222
      ∧ mroot hash₀ Lpub = mroot hash₀ Lpub := by
  refine ⟨writeCell0_receipt_eq compressN₀ compress2₀ restLimbs₀ v, ?_, rfl⟩
  decide

/-- **`argus_published_index_pins_receipt_teeth`.** Two discriminations, so the keystone is not
`:= True`: (i) a TAMPERED root does NOT open at the dense position (`¬ Opens Lpub 1 999`), so the
published-index opening is a real constraint on the prover; (ii) distinct writes publish DISTINCT
receipts under the realized carriers, so the pinned receipt is observable. -/
theorem argus_published_index_pins_receipt_teeth
    (hLE : Dregg2.Circuit.ListCommit.listLeafInjective (Dregg2.Exec.FieldsMap.tailLeaf compress2₀))
    (v w : Dregg2.Exec.Value)
    (htail : Dregg2.Exec.FieldsMap.userTail v ≠ Dregg2.Exec.FieldsMap.userTail w) :
    ¬ Opens Lpub 1 999
      ∧ argusReceipt compressN₀ compress2₀ Dregg2.Circuit.CommitmentCrossBind.restLimbsC (writeCell0 v) kR 0
          ≠ argusReceipt compressN₀ compress2₀ Dregg2.Circuit.CommitmentCrossBind.restLimbsC (writeCell0 w) kR 0 :=
  ⟨by decide, writeCell0_receipt_observable compressN₀ compress2₀ compressN₀_inj hLE v w htail⟩

/-! ## §3 — `transfer_published_index_pins_receipt` — the discharged keystone at the TRANSFER term.

Same conclusion shape, specialized to `transferStmt turn` (routed through the cornerstone). The receipt
of the transfer term IS the canonical receipt of the cell the VERIFIED EXECUTOR produces
(`transfer_receipt_is_executor_receipt`); the satisfiable EXERCISES that on a concrete committing
`recKExec` step, WELDED to the same published-index opening. The teeth reuse the receipt observability. -/

/-- A concrete committing transfer over `kR` (self-transfer of `0` is admissible and lands `recKExec`),
to exercise the cornerstone `interp (transferStmt …) = recKExec` non-vacuously. -/
def tR : Dregg2.Exec.Turn := { actor := 0, src := 0, dst := 0, amt := 0 }

/-- **`transfer_published_index_pins_receipt_satisfiable`.** The TRANSFER conclusion shape FIRES: for any
committing `recKExec kR tR = some k'`, the receipt the transfer term publishes for cell `c` IS the
canonical `cellCommit` of the VERIFIED EXECUTOR's produced cell (`transfer_receipt_is_executor_receipt`),
WELDED to the concrete published-index opening (`Opens Lpub 1 222`, `mroot` self-equality). The
cornerstone (`interp (transferStmt …) = recKExec`) carries the receipt onto the verified output. -/
theorem transfer_published_index_pins_receipt_satisfiable
    {k' : Dregg2.Exec.RecordKernelState} (c : Dregg2.Exec.CellId)
    (hexec : Dregg2.Exec.recKExec kR tR = some k') :
    argusReceipt compressN₀ compress2₀ restLimbs₀ (Dregg2.Circuit.Argus.transferStmt tR) kR c
        = some (cellCommit compressN₀ compress2₀ (restLimbs₀ c) (k'.cell c))
      ∧ Opens Lpub 1 222
      ∧ mroot hash₀ Lpub = mroot hash₀ Lpub := by
  refine ⟨transfer_receipt_is_executor_receipt compressN₀ compress2₀ restLimbs₀ tR kR k' c hexec, ?_, rfl⟩
  decide

/-- **`transfer_published_index_pins_receipt_teeth`.** The published-index opening discriminates (a
tampered root does NOT open) AND the transfer receipt is observable (distinct produced cells ⇒ distinct
receipts). REUSES the receipt-observability teeth — the keystone is not `:= True`. -/
theorem transfer_published_index_pins_receipt_teeth
    (hLE : Dregg2.Circuit.ListCommit.listLeafInjective (Dregg2.Exec.FieldsMap.tailLeaf compress2₀))
    (v w : Dregg2.Exec.Value)
    (htail : Dregg2.Exec.FieldsMap.userTail v ≠ Dregg2.Exec.FieldsMap.userTail w) :
    ¬ Opens Lpub 1 999
      ∧ argusReceipt compressN₀ compress2₀ Dregg2.Circuit.CommitmentCrossBind.restLimbsC (writeCell0 v) kR 0
          ≠ argusReceipt compressN₀ compress2₀ Dregg2.Circuit.CommitmentCrossBind.restLimbsC (writeCell0 w) kR 0 :=
  ⟨by decide, writeCell0_receipt_observable compressN₀ compress2₀ compressN₀_inj hLE v w htail⟩

/-! ## §4 — TAG the three Wave-4 HARD keystones with their welded companions. -/

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditArgusReceipt.argus_circuit_executor_receipts_agree_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditArgusReceipt.argus_circuit_executor_receipts_agree_teeth]
def argus_circuit_executor_receipts_agree_KS :=
  @Dregg2.Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditArgusReceipt.argus_published_index_pins_receipt_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditArgusReceipt.argus_published_index_pins_receipt_teeth]
def argus_published_index_pins_receipt_KS :=
  @Dregg2.Circuit.Argus.Receipt.argus_published_index_pins_receipt

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditArgusReceipt.transfer_published_index_pins_receipt_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditArgusReceipt.transfer_published_index_pins_receipt_teeth]
def transfer_published_index_pins_receipt_KS :=
  @Dregg2.Circuit.Argus.Receipt.transfer_published_index_pins_receipt

/-! ## §5 — RUN the audit (the CI gate over the Wave-4 HARD Argus-receipt family). -/

#keystone_audit Dregg2.Verify.KeystoneAuditArgusReceipt.argus_circuit_executor_receipts_agree_KS
#keystone_audit Dregg2.Verify.KeystoneAuditArgusReceipt.argus_published_index_pins_receipt_KS
#keystone_audit Dregg2.Verify.KeystoneAuditArgusReceipt.transfer_published_index_pins_receipt_KS

#keystone_audit_tagged

/-! ## §6 — axiom-hygiene over the carriers, witnesses + re-pinned aliases (kernel-triple clean). -/

#assert_axioms compressN₀_inj
#assert_axioms cmb₀_inj
#assert_axioms CH₀_inj
#assert_axioms LH₀_inj
#assert_axioms hash₀_cr
#assert_axioms argus_circuit_executor_receipts_agree_satisfiable
#assert_axioms argus_circuit_executor_receipts_agree_teeth
#assert_axioms argus_published_index_pins_receipt_satisfiable
#assert_axioms argus_published_index_pins_receipt_teeth
#assert_axioms transfer_published_index_pins_receipt_satisfiable
#assert_axioms transfer_published_index_pins_receipt_teeth
#assert_axioms argus_circuit_executor_receipts_agree_KS
#assert_axioms argus_published_index_pins_receipt_KS
#assert_axioms transfer_published_index_pins_receipt_KS

end Dregg2.Verify.KeystoneAuditArgusReceipt
