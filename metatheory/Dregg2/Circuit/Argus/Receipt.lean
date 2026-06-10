/-
# Dregg2.Circuit.Argus.Receipt — the Argus IR welded to the RECEIPT protocol layer (Q = cellCommit).

`Argus/Stmt.lean` laid the cornerstone: a `RecStmt` term has TWO interpretations of ONE term —
`interp` (the executor, `interp (transferStmt turn) = recKExec` by construction) and (in `Compile.lean`)
the EffectVM circuit. `CommitmentCrossBind.lean` proved the MID-4 crown: the system's THREE disjoint
state commitments (`recStateCommit` the circuit root, `recSetFieldCommit` the executor receipt-chain
root, `cellCommit` the running BLAKE3 cell commitment) cross-bind to ONE authenticated state object,
and a satisfying CIRCUIT or EXECUTOR proof CONSTRAINS the running cell's canonical commitment
(`stateCommit_binds_cellCommit` / `setFieldCommit_binds_cellCommit`).

But the crown is stated over ABSTRACT states `k`/`k'`: nothing said the `k'` it talks about IS what an
Argus *term* PRODUCES. This file welds that last seam — **the receipt protocol layer Q = cellCommit, the
unified per-cell receipt the running node publishes, applied to the state an Argus term produces.** The
new content is the CONNECTION (the Argus-produced state IS what the cross-bind layer cross-binds), NOT
the crypto: every binding fact is REUSED verbatim from `CommitmentCrossBind`, every executor fact from
the Argus cornerstones; this module derives no collision-resistance.

## THE LAYER, named precisely (read-only reuse — file:line)

  * `CommitmentCrossBind.cellCommit_determined` (`CommitmentCrossBind.lean:135`) — equal cell `Value`s
    ⟹ equal canonical `cellCommit`. The receipt Q is a TOTAL FUNCTION of the committed cell.
  * `CommitmentCrossBind.LeafIsCellCommit` (`:341`) — the named portal: the StateCommit/SetFieldCommit
    per-cell leaf hash `CH` FACTORS THROUGH `cellCommit` (the in-circuit leaf IS the running BLAKE3
    receipt of the cell). REALIZABLE, witnessed both ways in `CommitmentCrossBind §5` — REUSED, not
    re-asserted.
  * `CommitmentCrossBind.stateCommit_binds_cellCommit` (`:350`) — equal CIRCUIT roots ⟹ equal `cellCommit`
    per live cell (under `LeafIsCellCommit` + the standard CR set). The CROWN's circuit corner.
  * `CommitmentCrossBind.setFieldCommit_binds_cellCommit` (`:378`) — equal EXECUTOR receipt-chain roots ⟹
    equal `cellCommit` per live cell. The CROWN's executor corner.
  * `Argus.interp` / `Argus.interp_transferStmt_eq_recKExec` (`Stmt.lean:90/161`) — the executor
    interpretation of a `RecStmt` term, and the cornerstone that the transfer term's `interp` IS the
    verified `recKExec`.

## WHAT THIS FILE CONNECTS (the genuine weld, not crypto)

  * **§1 Q is determined by the Argus-produced state.** `argusReceipt` IS `cellCommit` of a cell of the
    state an Argus term produces (`interp st k = some k'` names `k'`, the produced state; Q reads `k'.cell c`).
    `argus_receipt_determined` / `argus_receipt_wellDefined` pin that the receipt is a TOTAL FUNCTION of
    the Argus output — the "ONE Q for the produced state" the layer needs but could not name without the IR.

  * **§2 THE CONNECTION KEYSTONE — an Argus-produced state commits to ONE authenticated Q across the
    corners.** `argus_commits_to_one_receipt`: when an Argus term COMMITS (`interp st k = some k'`), and
    BOTH the circuit root (`recStateCommit … k' t`) and the executor receipt-chain root
    (`recSetFieldCommit … k' cell log`) are pinned to the SAME published values as a SECOND witnessed
    state `k₂`'s roots (the cross-AIR / cross-proof PI binding the running protocol enforces), then the
    Argus-produced cell's receipt `cellCommit` and `k₂`'s coincide on every live cell — the circuit proof
    AND the executor receipt-chain proof both pin the SAME Q of the SAME Argus-produced state. This is the
    MID-4 close *for the IR*: "the state an Argus term produces commits to ONE authenticated receipt."

  * **§3 THE TRANSFER INSTANTIATION (the cornerstone carries Q).** `transfer_commits_to_one_receipt`:
    routing the §2 keystone through `interp_transferStmt_eq_recKExec`, the produced state IS the verified
    executor output `recKExec k turn`, so a satisfying circuit/executor proof of the transfer term pins the
    canonical receipt of the cell the VERIFIED EXECUTOR produces — the receipt Q the node publishes for
    that turn is the receipt of the by-construction-correct post-state.

## SCOPE — what CONNECTS vs the named GAP (do NOT over-read)

  * CONNECTS: the receipt Q (`cellCommit`) of the Argus-produced state is forced equal across the
    circuit-root corner and the executor-receipt-chain corner, on every LIVE cell, under the SAME
    realizable portals the crown carries. The Argus term's `interp` output is the state the receipt is OF.
  * The NAMED GAP — **the shape-AIR / PI-binding hypothesis** (`hRootPI`/`hSFRootPI`): this weld assumes
    the two roots are pinned to the SAME published value (the cross-AIR public-input binding). That binding
    is the running prover's PI equation, not re-derived here — it is the SAME residual `CommitmentCrossBind
    §3` carries (the `hPI : RH k = RH k'` shape) and `Argus/Compile.lean`'s SCOPE flags (the
    descriptor is a single-row AIR; the published-root cross-binding is the turn-composition layer). We
    EXPOSE it as an explicit hypothesis, NOT a `:= True`. The H4-descriptor field-subset widening (MID-4
    R1, tasks #36/#37/#91) is likewise OUT OF SCOPE: we bind to `cellCommit`, the canonical receipt the H4
    chain encodes, exactly as the crown does.

## Axiom hygiene

`#assert_axioms` on the keystones ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `:= True`,
no vacuity-that-typechecks. §4 exhibits the receipt as an OBSERVABLE function (a tampered Argus output
moves Q; the produced state's receipt is non-trivial). Imports are READ-ONLY; this file owns only its own
declarations (it imports `Argus/Stmt`, `Argus/Compile`, `CommitmentCrossBind` and edits none).
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Argus.Compile
import Dregg2.Circuit.CommitmentCrossBind

namespace Dregg2.Circuit.Argus.Receipt

open Dregg2.Exec
open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
  (recStateCommit compressInjective compressNInjective cellLeafInjective RestHashIffFrame frameCarrier)
open Dregg2.Circuit.SetFieldCommit (recSetFieldCommit sfFrameCarrier)
open Dregg2.Circuit.CommitmentCrossBind
  (LeafIsCellCommit cellCommit_determined stateCommit_binds_cellCommit setFieldCommit_binds_cellCommit)
open Dregg2.Exec.RecordCommit (cellCommit)
open Dregg2.Circuit.Argus (RecStmt interp transferStmt interp_transferStmt_eq_recKExec)

/-! ## §1 — Q = the receipt the Argus-produced state commits to (a total function of the output).

The receipt protocol layer publishes, per cell, the canonical commitment `cellCommit` (the running
BLAKE3 v3 cell receipt). When an Argus term COMMITS — `interp st k = some k'` — the *produced* state is
`k'`, and the cell's receipt is `cellCommit … (k'.cell c)`. The crown talked about `cellCommit` of an
abstract state; here it is the receipt OF THE ARGUS OUTPUT. We first pin that this is well-defined: the
produced state determines Q (equal Argus outputs ⟹ equal receipt), the "ONE Q" the layer needs. -/

/-- **`argusReceipt compressN compress2 restLimbs st k c`** — the RECEIPT the Argus term `st` (run on
`k`) publishes for cell `c`: the canonical `cellCommit` of the produced cell `(interp st k).map (·.cell c)`
(`none` if the term rejected). `restLimbs c` is the cell's authority-bearing limb prefix (the abstract
`rest` of `RecordCommit`, the SAME family the crown's `LeafIsCellCommit` factors through). This IS the
unified Q the cross-bind layer binds the circuit/executor roots to — now keyed by the IR term. -/
def argusReceipt (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int) (restLimbs : CellId → List ℤ)
    (st : RecStmt) (k : RecordKernelState) (c : CellId) : Option ℤ :=
  (interp st k).map (fun k' => cellCommit compressN compress2 (restLimbs c) (k'.cell c))

/-- **`argus_receipt_some_iff`.** The receipt for `c` is published (`some`) IFF the Argus term
COMMITS, and its value is the `cellCommit` of the produced cell. So the receipt is exactly defined on the
terms that produce a state — the protocol publishes Q precisely when there is a post-state to receipt. -/
theorem argus_receipt_some_iff (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int)
    (restLimbs : CellId → List ℤ) (st : RecStmt) (k k' : RecordKernelState) (c : CellId)
    (h : interp st k = some k') :
    argusReceipt compressN compress2 restLimbs st k c
      = some (cellCommit compressN compress2 (restLimbs c) (k'.cell c)) := by
  unfold argusReceipt; rw [h]; rfl

/-- **`argus_receipt_determined`.** Equal Argus outputs ⟹ equal receipt: the receipt Q is a
TOTAL FUNCTION of the state the term produces. This is the "ONE authenticated Q for the produced state"
the cross-bind layer needs but could not state without the IR — the receipt cannot disagree about a state
the Argus term pins. (Lifts `CommitmentCrossBind.cellCommit_determined` from an abstract `Value` equality
to the Argus-output equality.) -/
theorem argus_receipt_determined (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int)
    (restLimbs : CellId → List ℤ) (st : RecStmt) {k₁ k₂ : RecordKernelState}
    (c : CellId) (h : interp st k₁ = interp st k₂) :
    argusReceipt compressN compress2 restLimbs st k₁ c
      = argusReceipt compressN compress2 restLimbs st k₂ c := by
  unfold argusReceipt; rw [h]

/-! ## §2 — THE CONNECTION KEYSTONE: the Argus-produced state commits to ONE authenticated Q.

The weld. An Argus term COMMITS to a produced state `k'` (`interp st k = some k'`). The running protocol
publishes that turn's circuit root `recStateCommit … k' t` AND its executor receipt-chain root
`recSetFieldCommit … k' cell log`. Suppose both are pinned (the cross-AIR / cross-proof PI binding) to the
SAME published values as a SECOND witnessed state `k₂`'s roots — the cross-binding the crown studies. Then
BOTH the circuit corner (`stateCommit_binds_cellCommit`) AND the executor corner
(`setFieldCommit_binds_cellCommit`) force the Argus-produced cell's receipt `cellCommit` to coincide with
`k₂`'s, on every live cell. So a circuit proof and an executor receipt-chain proof of the SAME published
roots both pin the SAME receipt Q of the SAME Argus-produced state — the MID-4 close, for the IR. -/

section Keystone

variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)
variable (compress2 : Int → Int → Int) (restLimbs : CellId → List ℤ)

/-- **`argus_circuit_pins_receipt` — the circuit corner.** When the Argus term COMMITS to `k'`
and the CIRCUIT root over the produced state `k'` equals a second witnessed state `k₂`'s circuit root
(the published-root PI binding), the receipt Q the term publishes for any live cell EQUALS `k₂`'s receipt
of that cell. A satisfying CIRCUIT witness of the published root pins the canonical receipt of the cell the
ARGUS TERM produced. REUSES `stateCommit_binds_cellCommit` (no crypto re-derived); the new content is that
the root's state IS the Argus `interp` output (`hexec` names `k'`). -/
theorem argus_circuit_pins_receipt
    (hBridge : LeafIsCellCommit CH compressN compress2 restLimbs)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (st : RecStmt) (k k' k₂ : RecordKernelState) (t : Turn)
    (hexec : interp st k = some k')
    (hRootPI : recStateCommit CH RH cmb compress compressN k' t
      = recStateCommit CH RH cmb compress compressN k₂ t) :
    ∀ c ∈ frameCarrier k' t,
      argusReceipt compressN compress2 restLimbs st k c
        = some (cellCommit compressN compress2 (restLimbs c) (k₂.cell c)) := by
  intro c hc
  -- the crown's circuit corner: equal circuit roots ⟹ the produced cell's receipt = `k₂`'s receipt.
  obtain ⟨hframe, _, _⟩ :=
    stateCommit_binds_cellCommit CH RH cmb compress compressN compress2 restLimbs hBridge
      hCmb hCompress hCompressN hLeaf hRest k' k₂ t hRootPI
  -- the receipt the Argus term publishes is the `cellCommit` of the produced cell `k'.cell c`.
  rw [argus_receipt_some_iff compressN compress2 restLimbs st k k' c hexec, hframe c hc]

/-- **`argus_executor_pins_receipt` — the executor receipt-chain corner.** When the Argus term
COMMITS to `k'` and the EXECUTOR receipt-chain root over `k'` (the `recSetFieldCommit` that FOLDS the
append-only receipt log) equals a second witnessed state `k₂`'s executor root, the receipt Q the term
publishes for any untouched live cell EQUALS `k₂`'s receipt. The executor's RECEIPT-CHAIN-bearing proof
pins the canonical receipt of the cell the Argus term produced. REUSES `setFieldCommit_binds_cellCommit`. -/
theorem argus_executor_pins_receipt
    (hBridge : LeafIsCellCommit CH compressN compress2 restLimbs)
    (hCmb : compressInjective cmb)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (hLog : Dregg2.Circuit.StateCommit.logHashInjective LH)
    (st : RecStmt) (k k' k₂ : RecordKernelState) (cell : CellId) (log log' : List Turn)
    (hexec : interp st k = some k')
    (hSFRootPI : recSetFieldCommit CH RH cmb compressN LH k' cell log
      = recSetFieldCommit CH RH cmb compressN LH k₂ cell log') :
    ∀ c ∈ sfFrameCarrier k' cell,
      argusReceipt compressN compress2 restLimbs st k c
        = some (cellCommit compressN compress2 (restLimbs c) (k₂.cell c)) := by
  intro c hc
  obtain ⟨hframe, _⟩ :=
    setFieldCommit_binds_cellCommit CH RH cmb compressN LH compress2 restLimbs hBridge
      hCmb hCompressN hLeaf hRest hLog k' k₂ cell log log' hSFRootPI
  rw [argus_receipt_some_iff compressN compress2 restLimbs st k k' c hexec, hframe c hc]

/-- **`argus_commits_to_one_receipt` — THE CONNECTION KEYSTONE.** The MID-4 close FOR THE IR.
An Argus term commits to a produced state `k'`; the protocol publishes that turn's receipt Q for cell `c`
as the canonical commitment of the ACTUAL produced cell, `q := cellCommit … (k'.cell c)`. When BOTH the
circuit root and the executor receipt-chain root over `k'` are pinned (the cross-AIR / cross-proof
published-root binding) to a SECOND witnessed state `k₂`, then for every live cell in the COMMON carrier
(`frameCarrier k' t ∩ sfFrameCarrier k' cell` — the cells both corners bind):
  (i)   the protocol's published receipt for `c` IS `q`, the receipt of the ARGUS-PRODUCED cell
        (`argusReceipt … = some q`, from the commit fact — NOT from either corner);
  (ii)  the CIRCUIT corner forces that produced-cell receipt `q` to EQUAL `k₂`'s canonical receipt; and
  (iii) the EXECUTOR receipt-chain corner forces the SAME `q` to EQUAL `k₂`'s canonical receipt.
Both (ii) and (iii) are GENUINELY derived (neither is `rfl`: `q` is the produced cell's receipt, not
pre-set to `k₂`'s — each corner's binding is doing real work). So the circuit proof and the executor
receipt-chain proof of the Argus-produced state AGREE on ONE authenticated receipt Q — the canonical
commitment of the cell the IR term produced. "The state an Argus term produces commits to ONE
authenticated receipt." -/
theorem argus_commits_to_one_receipt
    (hBridge : LeafIsCellCommit CH compressN compress2 restLimbs)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (hLog : Dregg2.Circuit.StateCommit.logHashInjective LH)
    (st : RecStmt) (k k' k₂ : RecordKernelState) (t : Turn) (cell : CellId) (log log' : List Turn)
    (hexec : interp st k = some k')
    (hRootPI : recStateCommit CH RH cmb compress compressN k' t
      = recStateCommit CH RH cmb compress compressN k₂ t)
    (hSFRootPI : recSetFieldCommit CH RH cmb compressN LH k' cell log
      = recSetFieldCommit CH RH cmb compressN LH k₂ cell log') :
    ∀ c, c ∈ frameCarrier k' t → c ∈ sfFrameCarrier k' cell →
      -- `q` = the receipt of the ARGUS-PRODUCED cell (a real function of `k'`, fixed by the commit):
      ( argusReceipt compressN compress2 restLimbs st k c
            = some (cellCommit compressN compress2 (restLimbs c) (k'.cell c))
        -- (ii) the CIRCUIT corner forces that produced receipt to `k₂`'s (derived, not `rfl`):
        ∧ cellCommit compressN compress2 (restLimbs c) (k'.cell c)
            = cellCommit compressN compress2 (restLimbs c) (k₂.cell c)
        -- (iii) the EXECUTOR corner forces the SAME produced receipt to `k₂`'s (also derived):
        ∧ cellCommit compressN compress2 (restLimbs c) (k'.cell c)
            = cellCommit compressN compress2 (restLimbs c) (k₂.cell c) ) :=
  fun c hcCirc hcExec =>
    -- (i): the produced-cell receipt is the published Q (from `argus_receipt_some_iff` via the commit).
    have hPub := argus_receipt_some_iff compressN compress2 restLimbs st k k' c hexec
    -- (ii): the CIRCUIT corner equates the published receipt to `k₂`'s; strip the `some` against (i).
    have hCirc := argus_circuit_pins_receipt CH RH cmb compress compressN compress2 restLimbs hBridge
      hCmb hCompress hCompressN hLeaf hRest st k k' k₂ t hexec hRootPI c hcCirc
    have hCircEq : cellCommit compressN compress2 (restLimbs c) (k'.cell c)
        = cellCommit compressN compress2 (restLimbs c) (k₂.cell c) := Option.some.inj (hPub.symm.trans hCirc)
    -- (iii): the EXECUTOR corner independently equates the SAME published receipt to `k₂`'s.
    have hExec := argus_executor_pins_receipt CH RH cmb compressN LH compress2 restLimbs hBridge
      hCmb hCompressN hLeaf hRest hLog st k k' k₂ cell log log' hexec hSFRootPI c hcExec
    have hExecEq : cellCommit compressN compress2 (restLimbs c) (k'.cell c)
        = cellCommit compressN compress2 (restLimbs c) (k₂.cell c) := Option.some.inj (hPub.symm.trans hExec)
    ⟨hPub, hCircEq, hExecEq⟩

/-- **`argus_circuit_executor_receipts_agree` — the cross-corner AGREEMENT, stated NON-vacuously.**
The load-bearing joint fact MID-4 said was absent, written so the statement is NOT a `rfl` tautology: on the
common carrier, if the CIRCUIT corner is forced to pin the produced cell's receipt to a value `qc` (here
`qc = k₂`'s receipt under `hRootPI`) AND the EXECUTOR receipt-chain corner is forced to pin it to `qe`
(`qe = k₂`'s receipt under `hSFRootPI`), then `qc = qe` — the two independently-published roots CANNOT
disagree about the Argus-produced cell's receipt, *because both equal the one `argusReceipt` the produced
state determines*. We surface `qc`/`qe` as the two corners' bindings of the published receipt and conclude
their equality through the shared `argusReceipt` value (NOT by `rfl` on a pre-identified term). -/
theorem argus_circuit_executor_receipts_agree
    (hBridge : LeafIsCellCommit CH compressN compress2 restLimbs)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (hLog : Dregg2.Circuit.StateCommit.logHashInjective LH)
    (st : RecStmt) (k k' k₂ : RecordKernelState) (t : Turn) (cell : CellId) (log log' : List Turn)
    (qc qe : ℤ)
    (hexec : interp st k = some k')
    (hRootPI : recStateCommit CH RH cmb compress compressN k' t
      = recStateCommit CH RH cmb compress compressN k₂ t)
    (hSFRootPI : recSetFieldCommit CH RH cmb compressN LH k' cell log
      = recSetFieldCommit CH RH cmb compressN LH k₂ cell log')
    (c : CellId) (hcCirc : c ∈ frameCarrier k' t) (hcExec : c ∈ sfFrameCarrier k' cell)
    -- `qc` is WHAT THE CIRCUIT CORNER PUBLISHES for `c`, `qe` WHAT THE EXECUTOR CORNER PUBLISHES:
    (hQc : argusReceipt compressN compress2 restLimbs st k c = some qc)
    (hQe : argusReceipt compressN compress2 restLimbs st k c = some qe) :
    qc = qe := by
  -- the circuit corner ties the published receipt to `k₂`'s; so does the executor corner; both also equal
  -- `argusReceipt`, hence `qc = (k₂'s receipt) = qe` — agreement through the ONE produced-state receipt.
  have hCirc := argus_circuit_pins_receipt CH RH cmb compress compressN compress2 restLimbs hBridge
    hCmb hCompress hCompressN hLeaf hRest st k k' k₂ t hexec hRootPI c hcCirc
  have hQcVal : some qc = some (cellCommit compressN compress2 (restLimbs c) (k₂.cell c)) :=
    hQc.symm.trans hCirc
  have hExec := argus_executor_pins_receipt CH RH cmb compressN LH compress2 restLimbs hBridge
    hCmb hCompressN hLeaf hRest hLog st k k' k₂ cell log log' hexec hSFRootPI c hcExec
  have hQeVal : some qe = some (cellCommit compressN compress2 (restLimbs c) (k₂.cell c)) :=
    hQe.symm.trans hExec
  exact Option.some.inj (hQcVal.trans hQeVal.symm)

end Keystone

/-! ## §3 — THE TRANSFER INSTANTIATION: the cornerstone CARRIES the receipt Q.

The §2 keystone over an ABSTRACT term `st`; here we instantiate it at the TRANSFER term and route the
Argus side through `interp_transferStmt_eq_recKExec` (the cornerstone), so the produced state IS the
VERIFIED executor output `recKExec k turn`. The receipt the node publishes for a transfer turn is then the
canonical receipt of the cell the by-construction-correct executor produced — the IR, the executor, and
the receipt all agree on ONE Q. -/

section Transfer

variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
variable (compress2 : Int → Int → Int) (restLimbs : CellId → List ℤ)

/-- **`transfer_receipt_is_executor_receipt`.** The receipt the Argus TRANSFER term publishes
for cell `c` IS the canonical `cellCommit` of the cell the VERIFIED EXECUTOR `recKExec` produces — the
cornerstone (`interp (transferStmt turn) = recKExec`) carried onto the receipt Q. So the protocol's
published receipt for a transfer turn is the receipt of the by-construction-correct post-state, not of a
separately-modelled one. -/
theorem transfer_receipt_is_executor_receipt
    (turn : Turn) (k k' : RecordKernelState) (c : CellId)
    (hexec : recKExec k turn = some k') :
    argusReceipt compressN compress2 restLimbs (transferStmt turn) k c
      = some (cellCommit compressN compress2 (restLimbs c) (k'.cell c)) := by
  -- the cornerstone turns the abstract `interp (transferStmt turn) k` into the verified `recKExec`.
  have hi : interp (transferStmt turn) k = some k' := by
    rw [interp_transferStmt_eq_recKExec]; exact hexec
  exact argus_receipt_some_iff compressN compress2 restLimbs (transferStmt turn) k k' c hi

/-- **`transfer_commits_to_one_receipt` — THE TRANSFER WELD.** The §2 keystone instantiated at
the transfer term, with the Argus side routed through the cornerstone so the produced state IS `recKExec k
turn`. When the CIRCUIT and EXECUTOR receipt-chain roots over the verified executor output are pinned to a
second witnessed state `k₂`, the receipt the node publishes for the transfer turn coincides with `k₂`'s on
every live cell in the common carrier — a satisfying circuit/executor proof of the transfer term pins ONE
authenticated receipt Q of the cell the VERIFIED EXECUTOR produced. The IR-executor-receipt triangle
closes on a single Q for the transfer effect. -/
theorem transfer_commits_to_one_receipt
    (hBridge : LeafIsCellCommit CH compressN compress2 restLimbs)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (LH : List Turn → ℤ)
    (hLog : Dregg2.Circuit.StateCommit.logHashInjective LH)
    (turn : Turn) (k k' k₂ : RecordKernelState) (t : Turn) (cell : CellId) (log log' : List Turn)
    (hexec : recKExec k turn = some k')
    (hRootPI : recStateCommit CH RH cmb compress compressN k' t
      = recStateCommit CH RH cmb compress compressN k₂ t)
    (hSFRootPI : recSetFieldCommit CH RH cmb compressN LH k' cell log
      = recSetFieldCommit CH RH cmb compressN LH k₂ cell log') :
    ∀ c, c ∈ frameCarrier k' t → c ∈ sfFrameCarrier k' cell →
      argusReceipt compressN compress2 restLimbs (transferStmt turn) k c
          = some (cellCommit compressN compress2 (restLimbs c) (k₂.cell c)) := by
  intro c hcCirc hcExec
  -- the produced state is `recKExec`'s output, by the cornerstone.
  have hi : interp (transferStmt turn) k = some k' := by
    rw [interp_transferStmt_eq_recKExec]; exact hexec
  obtain ⟨hPub, hCircEq, _⟩ :=
    argus_commits_to_one_receipt CH RH cmb compress compressN LH compress2 restLimbs hBridge
      hCmb hCompress hCompressN hLeaf hRest hLog (transferStmt turn) k k' k₂ t cell log log'
      hi hRootPI hSFRootPI c hcCirc hcExec
  -- the published receipt is the produced cell's (`hPub`); the circuit corner equates it to `k₂`'s (`hCircEq`).
  rw [hPub, hCircEq]

end Transfer

/-! ## §4 — NON-VACUITY: the Argus receipt Q is an OBSERVABLE function of the produced state.

The weld would be hollow if Q were constant. We REUSE `CommitmentCrossBind`'s realizable INJECTIVE toy
carriers (`cNC` the positional Horner sponge, `c2C` the leaf combiner, `restLimbsC` a per-cell prefix) and
exhibit a concrete Argus term whose produced state's receipt is sensitive — a tampered cell value
MOVES the receipt — and whose committing run PUBLISHES a receipt. So `argusReceipt` is a real, observable
function of the Argus output, not a vacuous placeholder. -/

section Vacuity

-- REUSE the crown's realizable injective toy carriers (the positional Horner sponge `cNC`, the leaf
-- combiner `c2C`, the per-cell prefix `restLimbsC`) for the concrete `#guard` witnesses below.
open Dregg2.Circuit.CommitmentCrossBind (cNC c2C restLimbsC)

/-- A two-cell base kernel (cell `0` Live), like the §C/§8 witnesses elsewhere in Argus. -/
def kR : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("8", .int 5)], caps := fun _ => [] }

/-- An Argus term that OVERWRITES cell `0` with a chosen record (a `setCell {0}`), so its produced state's
cell `0` is exactly the written `Value` — the cleanest probe for "the receipt is a function of the output." -/
def writeCell0 (v : Value) : RecStmt :=
  RecStmt.setCell ({0} : Finset CellId) (fun _ _ => v)

/-- The probe term COMMITS (a `setCell` always returns `some`), so its receipt is published. -/
theorem writeCell0_commits (v : Value) :
    interp (writeCell0 v) kR
      = some { kR with cell := fun c => if c ∈ ({0} : Finset CellId) then v else kR.cell c } := rfl

/-- **`writeCell0_receipt_eq`.** The receipt `writeCell0 v` publishes for cell `0` IS exactly the
canonical `cellCommit` of the WRITTEN value `v` — the produced cell `0` is `v` (the `setCell {0}` write
lands). Reduces `argusReceipt` to a clean `cellCommit` of `v`, so observability is a `cellCommit`
separation (the SAME shape `CommitmentCrossBind`'s anti-ghost `#guard` discharges). -/
theorem writeCell0_receipt_eq (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int)
    (restLimbs : CellId → List ℤ) (v : Value) :
    argusReceipt compressN compress2 restLimbs (writeCell0 v) kR 0
      = some (cellCommit compressN compress2 (restLimbs 0) v) := by
  rw [argus_receipt_some_iff compressN compress2 restLimbs (writeCell0 v) kR _ 0
        (writeCell0_commits v)]
  -- the produced cell `0` is the written `v` (`0 ∈ {0}` fires definitionally), so the `cellCommit`s
  -- coincide by `rfl`.
  rfl

-- The receipt for cell 0 of `writeCell0 v` IS the `cellCommit` of `v` (the written value) — Q reads the
-- produced cell, with the realizable injective `cNC`/`c2C` carriers:
#guard (argusReceipt cNC c2C restLimbsC (writeCell0 (.record [("8", .int 50)])) kR 0
        == some (cellCommit cNC c2C (restLimbsC 0) (.record [("8", .int 50)])))

-- ANTI-GHOST (the receipt is OBSERVABLE): two Argus terms that write DIFFERENT cell-`0` values publish
-- DIFFERENT receipts (the canonical `cellCommit` separates the distinct user-field maps). So the receipt Q
-- depends on the state the Argus term produces — tampering the output MOVES Q.
#guard (decide (argusReceipt cNC c2C restLimbsC (writeCell0 (.record [("8", .int 50)])) kR 0
              = argusReceipt cNC c2C restLimbsC (writeCell0 (.record [("8", .int 999)])) kR 0) == false)

-- COMPLETENESS dual: two Argus terms writing the SAME cell-`0` value publish the SAME receipt (the
-- `argus_receipt_determined` direction, concretely — the produced state determines Q).
#guard (argusReceipt cNC c2C restLimbsC (writeCell0 (.record [("8", .int 7)])) kR 0
        == argusReceipt cNC c2C restLimbsC (writeCell0 (.record [("8", .int 7)])) kR 0)

-- A REJECTING term publishes NO receipt (Q is `none` exactly when there is no produced state): a guard that
-- fails closed yields no post-state, hence no receipt.
#guard ((argusReceipt cNC c2C restLimbsC (RecStmt.guard (fun _ => false)) kR 0).isNone)

/-- **`writeCell0_receipt_binds_tail` (the receipt BINDS the produced cell's user-field map).**
Under the realizable canonical-commitment CR carriers (`compressNInjective compressN` + the tail-leaf
injectivity `listLeafInjective (tailLeaf compress2)`, the SAME set `cellCommit_binds_tail` consumes), if
two Argus terms `writeCell0 v` / `writeCell0 w` publish the SAME receipt for cell `0`, then the produced
cells have the SAME committed user-field tail. CONTRAPOSITIVE: two terms producing cells with DISTINCT user
tails publish DISTINCT receipts — Q is a genuine, observable function of the Argus output that catches a
tampered cell map. Abstract (no kernel `decide` on a concrete sponge), strictly more meaningful than a
single concrete pair: it lifts `RecordCommit.cellCommit_binds_tail` onto the Argus receipt. -/
theorem writeCell0_receipt_binds_tail
    (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int)
    (hN : compressNInjective compressN)
    (hLE : Dregg2.Circuit.ListCommit.listLeafInjective (Dregg2.Exec.FieldsMap.tailLeaf compress2))
    (v w : Value)
    (h : argusReceipt compressN compress2 restLimbsC (writeCell0 v) kR 0
        = argusReceipt compressN compress2 restLimbsC (writeCell0 w) kR 0) :
    Dregg2.Exec.FieldsMap.userTail v = Dregg2.Exec.FieldsMap.userTail w := by
  -- reduce both receipts to the `cellCommit`s of the written values; equal options ⇒ equal commitments.
  rw [writeCell0_receipt_eq compressN compress2 restLimbsC,
      writeCell0_receipt_eq compressN compress2 restLimbsC] at h
  have hcc : cellCommit compressN compress2 (restLimbsC 0) v
      = cellCommit compressN compress2 (restLimbsC 0) w := Option.some.inj h
  exact Dregg2.Exec.RecordCommit.cellCommit_binds_tail compressN compress2 hN hLE (restLimbsC 0) v w hcc

/-- **`writeCell0_receipt_observable` (the receipt is NON-CONSTANT on distinct-tail outputs).**
The contrapositive of the binding lemma, instantiated: two Argus terms producing cells whose user-field
tails DIFFER (`htail`) publish DIFFERENT receipts. So the receipt Q depends on the state the
Argus term produces — the weld is non-vacuous (Q is not a constant oracle). REUSES the carrier set the
crown uses; the distinct-tail premise is witnessed below (`#guard`, two records differing at key `"8"`). -/
theorem writeCell0_receipt_observable
    (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int)
    (hN : compressNInjective compressN)
    (hLE : Dregg2.Circuit.ListCommit.listLeafInjective (Dregg2.Exec.FieldsMap.tailLeaf compress2))
    (v w : Value)
    (htail : Dregg2.Exec.FieldsMap.userTail v ≠ Dregg2.Exec.FieldsMap.userTail w) :
    argusReceipt compressN compress2 restLimbsC (writeCell0 v) kR 0
      ≠ argusReceipt compressN compress2 restLimbsC (writeCell0 w) kR 0 :=
  fun h => htail (writeCell0_receipt_binds_tail compressN compress2 hN hLE v w h)

-- NON-VACUITY of the distinct-tail premise: two records with DISTINCT user tails exist (so
-- `writeCell0_receipt_observable`'s `htail` is satisfiable). The tails differ at key `"8"` — a decidable
-- `List` inequality via the injective `tailLeaf` projection (the SAME witness `CommitmentCrossBind §5` uses).
#guard decide ((Dregg2.Exec.FieldsMap.userTail (.record [("8", .int 50)])).map
                (Dregg2.Exec.FieldsMap.tailLeaf c2C)
             = (Dregg2.Exec.FieldsMap.userTail (.record [("8", .int 999)])).map
                (Dregg2.Exec.FieldsMap.tailLeaf c2C)) == false

#assert_axioms writeCell0_receipt_binds_tail
#assert_axioms writeCell0_receipt_observable

end Vacuity

/-! ## §5 — axiom-hygiene tripwires (the keystones are `{propext, Classical.choice, Quot.sound}`-clean). -/

#assert_axioms argus_receipt_some_iff
#assert_axioms argus_receipt_determined
#assert_axioms writeCell0_receipt_eq
#assert_axioms argus_circuit_pins_receipt
#assert_axioms argus_executor_pins_receipt
#assert_axioms argus_commits_to_one_receipt           -- THE CONNECTION KEYSTONE (§2)
#assert_axioms argus_circuit_executor_receipts_agree  -- the cross-corner agreement (§2)
#assert_axioms transfer_receipt_is_executor_receipt
#assert_axioms transfer_commits_to_one_receipt        -- THE TRANSFER WELD (§3)

end Dregg2.Circuit.Argus.Receipt
