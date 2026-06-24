/-
# Dregg2.Exec.FFI.Refine — the EXPORT-REFINES-THE-MODEL theorem (assurance §5 Stage 1, CRITICAL-2).

The node invokes the `@[export dregg_exec_full_forest_auth]` String→String entry
`Dregg2.Exec.FFI.Wide.execFullForestAuthStep`. Its proved theorems live one type-boundary in, over the
abstract `FullForestG`/`runGatedForestTurnStatus`. The wire codec sitting between them
(`parseWWire`/`liftForestG`/`encodeWStatusOut`) was labelled "TCB, not proved" at `FFI.lean:92`.

`Dregg2.Exec.CodecRoundtrip` already discharged the codec ROUND-TRIP (`parseWWire_encode`: encode∘parse
= id on well-formed wires — the codec is the genuine left inverse). THIS module supplies the missing
companion the §5 roadmap calls for: a theorem that the String→String export **refines** the model — i.e.
the FFI body the node runs computes exactly `encode (model (decode w))` on the wire boundary, with the
decode/encode steps INSIDE the proof rather than the TCB.

The model the deployed export computes is NOT bare `execFullForestG`: it is the admission-wrapped, status-
bearing, fee-distributing `runGatedForestTurnStatus` over the lifted gated forest (the production entry
runs `Admission.runTurn` IN FRONT of `execFullForestG`, then encodes the three-way `TurnStatus`). We name
that model exactly (`runModel`) and the encode half exactly (`encodeResult`), and prove:

  * `export_refines_on_parseable` — for every parseable `input` (`parseWWire input = some w`),
    `execFullForestAuthStep input = encodeResult w (runModel w)`. The codec is now inside the proof: the
    FFI String→String body IS `decode ⨾ runModel ⨾ encode`, the model being the proved gated turn.
  * `export_refines_endToEnd` — composing with `CodecRoundtrip.parseWWire_encode`, for every well-formed
    `w`, `execFullForestAuthStep (encodeWWire w) = encodeResult w (runModel w)`: literally
    `export ∘ encode = encode ∘ model`, the form the roadmap states ("export(w) = encode(model(decode w))").
  * `export_rejects_unparseable` — the fail-closed leg: an unparseable wire is the rejected sentinel.

The model `runModel` is the SAME `runGatedForestTurnStatus` whose keystones
(`execFullForestG_conserves_per_asset`/`_no_amplify`/`_each_attests`/`_unauthorized_fails`, the admission
prologue, the bug-1/bug-2 fixes) are proved elsewhere; this module is the BRIDGE that ties the export's
output bytes to those keystones through the codec, not new executor content.

Disjoint from `Dregg2.Circuit`/`Dregg2.Circuit.Emit` (the proof-wire the rotation cutover is changing):
this concerns ONLY the turn/effect codec on the FFI boundary.
-/
import Dregg2.Exec.FFI
import Dregg2.Exec.CodecRoundtrip.Wire

namespace Dregg2.Exec.FFI.Wide

open Dregg2.Exec
open Dregg2.Exec.Admission (AdmCtx TurnHdr)
open Dregg2.Exec.TurnAdmission (runGatedForestTurnStatus runGatedForestTurn TurnStatus)
open Dregg2.Exec.AdmissionWire (turnHdrOf)
open Dregg2.Exec.StarbridgeGated (DForest)

/-! ## §R1 — the model and the encode half, named exactly as the export computes them.

The export body (`FFI.lean:3314`) is `parseWWire ⨾ (build ctx/hdr/forest) ⨾ runGatedForestTurnStatus ⨾
encodeWStatusOut`. We factor the two non-codec halves so the refinement is a literal `decode ⨾ model ⨾
encode`. -/

/-- **The host `AdmCtx` the deployed export builds** — bug-1: from the HOST-fed context, never the turn.
(Exactly the export's `admCtxOfHost w.host`.) -/
def runCtx (w : WWire) : AdmCtx := admCtxOfHost w.host

/-- **The admission header the deployed export builds** — agent/nonce/fee/validUntil/prev + the write-set
of the AUTH-erased structural tree (`eraseAuth w.turn.root`). (Exactly the export's `turnHdrOf …`.) -/
def runHdr (w : WWire) : TurnHdr :=
  turnHdrOf w.turn.agent (eraseAuth w.turn.root) w.turn.nonce w.turn.fee w.turn.validUntil w.turn.prevHash

/-- **The gated forest the deployed export executes** — the wire tree lifted to the gated `DForest` (the
WHO/caveats carried into the gate, child edges gating on `keep`/`parentCap`). (`liftForestG w.turn.root`.) -/
def runForest (w : WWire) : DForest := liftForestG w.turn.root

/-- **THE MODEL the deployed turn export computes.** The admission-wrapped, status-bearing gated turn:
`runGatedForestTurnStatus` runs `Admission.runTurn` (the bug-1 host-fed prologue) IN FRONT of the proved
`execFullForestG` over the lifted forest, distributes the fee on commit, and reports the three-way
`TurnStatus`. This is the production entry's denotation — NOT bare `execFullForestG`. -/
def runModel (w : WWire) : TurnStatus × Option RecChainedState :=
  runGatedForestTurnStatus (runCtx w) (runHdr w)
    { kernel := stateOfWState w.state, log := [] } (runForest w)

/-- **The encode half the deployed export computes.** Reads the post-state cells/caps/bal back at the
INPUT's orderings (so the wire is deterministic + positionally comparable), with the receipt-log length
and the three-way status; on a body-rollback (`res = none`) it echoes the UNCHANGED input state with
`loglen:0`. (Exactly the export's two `encodeWStatusOut …` arms.) -/
def encodeResult (w : WWire) (sr : TurnStatus × Option RecChainedState) : String :=
  let cellIds := w.state.cells.map Prod.fst
  let capLabels := w.state.caps.map Prod.fst
  let balKeys := balKeysOf w.state
  -- the theorem-backed refusal reason, computed from the SAME host-fed ctx/hdr/pre-state as the model
  -- (`AdmissionReason.reasonCode (admissionReason …)`) — exactly the export's `reason` let-binding.
  let reason := AdmissionReason.reasonCode (AdmissionReason.admissionReason
    (runCtx w) (runHdr w) { kernel := stateOfWState w.state, log := [] })
  match sr.2 with
  | some s' => encodeWStatusReasonOut (wstateOfState cellIds capLabels balKeys s'.kernel) s'.log.length sr.1 reason
  | none    => encodeWStatusReasonOut (wstateOfState cellIds capLabels balKeys
                  ({ kernel := stateOfWState w.state, log := [] } : RecChainedState).kernel) 0 sr.1 reason

/-! ## §R2 — the refinement theorems. -/

/-- **EXPORT REFINES THE MODEL on parseable inputs (CRITICAL-2 apex).** For every wire the node decodes
(`parseWWire input = some w`), the String→String export computes EXACTLY `encode (model (decode input))`:
the gated turn `runModel w` re-encoded by `encodeResult w`. The codec (`parseWWire`/`liftForestG`/
`encodeWStatusOut`) is now INSIDE the proof — the FFI body the node invokes provably equals
`decode ⨾ runModel ⨾ encode`, the model being the PROVED admission-wrapped gated forest, so the
keystones over `runGatedForestTurnStatus` bind the export's output bytes.

The proof is by unfolding the export and rewriting its `parseWWire input` match with the hypothesis: the
two remaining `encodeWStatusOut` arms are `encodeResult`'s two arms verbatim (the `let`s and the
`runGatedForestTurnStatus` call are definitionally `runModel`/`encodeResult`). -/
theorem export_refines_on_parseable (input : String) (w : WWire)
    (hparse : parseWWire input = some w) :
    execFullForestAuthStep input = encodeResult w (runModel w) := by
  unfold execFullForestAuthStep
  rw [hparse]
  -- the `some w` arm: its `let`-bound ctx/hdr/forest + `runGatedForestTurnStatus` are `runModel w`, and
  -- the two `encodeWStatusOut` arms are `encodeResult w (runModel w)` — the destructured pair matches.
  -- `encodeResult`/`runModel` unfold to the export's body definitionally (the export's `let (st,res) :=`
  -- pair-destructure and `encodeResult`'s `match sr.2` are the same `casesOn` on the pair).
  show _ = encodeResult w (runModel w)
  rfl

/-- **The fail-closed leg.** An unparseable wire is the rejected sentinel (empty 11-field state, `status:0`,
`ok:0`) — a malformed wire can NEVER produce a turn (`runModel` is not even reached). -/
theorem export_rejects_unparseable (input : String) (hparse : parseWWire input = none) :
    execFullForestAuthStep input = encodeWStatusReasonOut emptyWState 0 TurnStatus.rejected 0 := by
  unfold execFullForestAuthStep
  rw [hparse]

/-- **EXPORT REFINES THE MODEL end-to-end (codec fully inside the proof).** Composing
`export_refines_on_parseable` with `CodecRoundtrip.parseWWire_encode` (encode∘parse = id on well-formed
wires): for every well-formed `w`, feeding the export the ENCODED wire yields EXACTLY the encoded model —

    execFullForestAuthStep (encodeWWire w) = encodeResult w (runModel w)

i.e. `export ∘ encode = encode ∘ model`. This is the roadmap's literal Stage-1 statement
("export(w) = encode(model(decode w))") with BOTH codec halves (decode AND encode) discharged by theorem,
not asserted by differential — the wire codec is no longer in the trusted base for this entry.

The well-formedness hypotheses are the codec boundary `CodecRoundtrip` proved its round-trip under: the
cell payloads are escape-free with `< 2^256` digests (`WfCells`), the turn's credentials/caveats/actions
and `prev` digest are in-range (`WfTurn`), and the expiry uses the chain clock at height 0 (the deployed
`block_height = 0` shape). They are satisfiable (`CodecRoundtrip.wireWitness` witnesses a populated,
delegation-bearing instance) — the theorem is non-vacuous. -/
theorem export_refines_endToEnd (w : WWire)
    (hcells : CodecRoundtrip.WfCells w.state.cells)
    (hturn : CodecRoundtrip.WfTurn w.turn)
    (hblock : w.turn.blockHeight = 0) :
    execFullForestAuthStep (encodeWWire w) = encodeResult w (runModel w) := by
  -- `CodecRoundtrip.encodeWWire` is byte-identical to the FFI `Wide.encodeWWire` (both
  -- `{"host":…,"state":…,"turn":…}`), so the round-trip lemma applies to the export's own encoder.
  have hcodec : parseWWire (encodeWWire w) = some w := by
    have h := CodecRoundtrip.parseWWire_encode w hcells hturn hblock
    -- bridge the two definitionally-equal encoders (same string), then reuse the corpus round-trip.
    rwa [show (encodeWWire w) = CodecRoundtrip.encodeWWire w from by
          obtain ⟨host, state, turn⟩ := w
          rfl]
  exact export_refines_on_parseable (encodeWWire w) w hcodec

/-! ## §R3 — the model projects to `runGatedForestTurn` (the state half) — tying §R2 to the keystones.

`runModel`'s STATE projection is `runGatedForestTurn` (admission ∘ `execFullForestG`), the object the
`FullForestAuth` keystones are stated over. So the export's post-state bytes are an encoding of the proved
gated turn's result — the bridge from the String boundary to conservation/no-amplification/attestation. -/

/-- **The model's state projection IS the gated turn.** `(runModel w).2 = runGatedForestTurn (ctx) (hdr)
s0 (lifted forest)` — by `runGatedForestTurnStatus_state`. The export's encoded post-state is therefore an
encoding of the PROVED `runGatedForestTurn` output, whose `_conserves`/`_no_amplify`/`_each_attests`
keystones (over `execFullForestG`) now bind the deployed turn through §R2. -/
theorem runModel_state (w : WWire) :
    (runModel w).2
      = runGatedForestTurn (runCtx w) (runHdr w)
          { kernel := stateOfWState w.state, log := [] } (runForest w) :=
  Dregg2.Exec.TurnAdmission.runGatedForestTurnStatus_state _ _ _ _

/-! ## §R4 — NON-VACUITY: the refinement fires on a real committed turn AND a forged-credential rollback.

These `#guard`s exhibit the refinement's two endpoints CONCRETELY: a genuine-credential transfer (the body
commits, `status:2`/`ok:1`) and a forged-credential transfer (the gate fail-closes, body rolls back,
`status:1`/`ok:0`). For each, the export output equals `encodeResult w (runModel w)` — the theorem's RHS
computed on the SAME wire — so the refinement is witnessed, not vacuous. (The `gatedDemoInput`/
`forgedGatedInput` literals are the export's own demo corpus, defined alongside `execFullForestAuthStep`.) -/

-- A genuine-credential gated turn: export = encodeResult ∘ runModel (committed body, ok:1).
#guard ((match parseWWire gatedDemoInput with
         | some w => execFullForestAuthStep gatedDemoInput == encodeResult w (runModel w)
         | none   => false))  --  true (refinement holds on the committed turn)
#guard (wireOk1 (execFullForestAuthStep gatedDemoInput))  --  body committed

-- A forged-credential gated turn: export = encodeResult ∘ runModel (body rolls back, ok:0/status:1).
#guard ((match parseWWire forgedGatedInput with
         | some w => execFullForestAuthStep forgedGatedInput == encodeResult w (runModel w)
         | none   => false))  --  true (refinement holds on the rollback)
#guard (wireOk0 (execFullForestAuthStep forgedGatedInput))  --  body rolled back
#guard (wireStatusIs 1 (execFullForestAuthStep forgedGatedInput))  --  prologue-only

-- the fail-closed leg: a malformed wire is the rejected sentinel (parseWWire = none).
#guard ((parseWWire "garbage").isNone)  --  true (unparseable ⇒ export_rejects_unparseable fires)

/-! ## §R5 — axiom-hygiene pins (the kernel triple). -/

#assert_axioms runModel
#assert_axioms encodeResult
#assert_axioms export_refines_on_parseable
#assert_axioms export_rejects_unparseable
#assert_axioms export_refines_endToEnd
#assert_axioms runModel_state

end Dregg2.Exec.FFI.Wide
