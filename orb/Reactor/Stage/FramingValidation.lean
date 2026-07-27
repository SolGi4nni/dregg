import Reactor.Stage.RequestValidation

/-!
# Reactor.Stage.FramingValidation — the message-framing + field-strictness gate

The wave-5 EXTENDED RFC conformance probe (`docs/engine/review/CONFORMANCE-EXT.md`,
`conformance/rfc_conformance_ext.py`) found three further request-phase MUSTs the
deployed serve violated — all at the EDGES of the verified core, the same missing
request-validation gate the base C-group / `RequestValidation` covers, extended into
the message-framing layer:

* **L1 — Transfer-Encoding, chunked-not-final (RFC 7230 §3.3.3, MUST + security).**
  A request whose `Transfer-Encoding` is present but whose FINAL transfer-coding is
  not `chunked` (the probe: `Transfer-Encoding: chunked, gzip`) has a body length
  that "cannot be determined reliably" — the server **MUST** answer `400` and close.
  Decoding it anyway is a request-smuggling vector through any intermediary that
  frames it differently. The deployed serve returned `200`.

* **J2 — unsupported Expect (RFC 7231 §5.1.1, MUST).** The only defined expectation
  is `100-continue`; any OTHER expectation (the probe: `Expect: drorb-nonsense-99`)
  **MUST** draw `417 Expectation Failed`. The deployed serve ignored the field and
  returned `200`. (A `100-continue` expectation PASSES this gate — the inner serve
  answers it with a final response directly, which §5.1.1 permits; see
  `Proto.Expect100Proven`.)

* **M1 — whitespace before the colon (RFC 7230 §3.2.4, MUST).** A field-name is a
  token and carries NO whitespace; `Host : x` (space before `:`) **MUST** be
  rejected with `400`. The request-head parser splits the name on the first colon, so
  a space-before-colon lands as TRAILING whitespace inside the parsed field-NAME
  (`"Host "`). This gate rejects any header whose name contains `SP`/`HT`. The
  deployed serve returned `404` (the malformed line silently dropped `Host` and the
  request mis-routed instead of being cleanly rejected).

This stage runs in the request phase AFTER `Reactor.Stage.RequestValidation`
(version/method/Host) and BEFORE the routing fold, short-circuiting the first
violation with its `4xx`. It is a pure decision on the PARSED `Request` — no new
effect, no core change; the framing the core proves (chunked/multi-CL/pipelining)
is untouched.

## What is proven (headline, non-vacuous on concrete witnesses)

* `framingValidationStage_rejects_te_not_final` — TE final-coding ≠ chunked ⇒ `400`.
* `framingValidationStage_rejects_bad_expect` — unsupported Expect ⇒ `417`.
* `framingValidationStage_rejects_bad_field_name` — whitespace in a field-name ⇒ `400`.
* `framingValidationStage_passes` — a clean request `.continue`s unchanged.
* Concrete witnesses: `teNotFinalCtx` (`chunked, gzip`) ⇒ `400`; `badExpectCtx`
  (`drorb-nonsense-99`) ⇒ `417`; `wsNameCtx` (`Host ` name) ⇒ `400`; and the
  NON-VACUITY contrast `okFramingCtx` (`gzip, chunked` final = chunked +
  `Expect: 100-continue` + clean names) ⇒ `.continue`.

Every guard fact is `by decide` on explicit ASCII byte lists (no `native_decide`).
-/

namespace Reactor.Stage.FramingValidation

open Reactor.Pipeline
open Proto (Bytes Request)
open Reactor.Stage.RequestValidation (strBytes badRequestResp)

/-! ## ASCII helpers (kernel-reducible) -/

/-- `SP` (space). -/ def bSP : UInt8 := 32
/-- `HT` (horizontal tab). -/ def bHT : UInt8 := 9
/-- `,` (comma — the transfer-coding list separator). -/ def bCOMMA : UInt8 := 44

/-- Is a byte optional whitespace (`SP`/`HT`)? -/
def isOWS (b : UInt8) : Bool := b == bSP || b == bHT

/-- Lowercase one ASCII byte (`A`–`Z` → `a`–`z`), else identity. Used for the
case-INSENSITIVE header-name / token comparisons HTTP requires (RFC 7230 §3.2). -/
def lowerByte (b : UInt8) : UInt8 :=
  if decide (65 ≤ b) && decide (b ≤ 90) then b + 32 else b

/-- Lowercase a whole byte string. -/
def lowerBytes (bs : Bytes) : Bytes := bs.map lowerByte

/-- Drop leading, then trailing, `OWS` (RFC 7230 §3.2.3 field-value trimming). -/
def trimOWS (bs : Bytes) : Bytes :=
  ((bs.dropWhile isOWS).reverse.dropWhile isOWS).reverse

/-- Split a byte string on a separator byte into its (possibly empty) parts. -/
def splitOn (sep : UInt8) : Bytes → List Bytes
  | [] => [[]]
  | b :: bs =>
    if b == sep then [] :: splitOn sep bs
    else match splitOn sep bs with
         | [] => [[b]]
         | x :: xs => (b :: x) :: xs

/-! ## The tokens (explicit ASCII so every decision reduces in the kernel) -/

/-- `transfer-encoding` (lowercase). -/
def teNameLower : Bytes :=
  [116, 114, 97, 110, 115, 102, 101, 114, 45, 101, 110, 99, 111, 100, 105, 110, 103]
/-- `chunked`. -/
def chunkedTok : Bytes := [99, 104, 117, 110, 107, 101, 100]

/-- `expect` (lowercase). -/
def expectNameLower : Bytes := [101, 120, 112, 101, 99, 116]
/-- `100-continue`. -/
def continueTok : Bytes := [49, 48, 48, 45, 99, 111, 110, 116, 105, 110, 117, 101]

/-! ## M1 — field-name strictness (whitespace before colon) -/

/-- A field-name is malformed if it carries any `SP`/`HT` (RFC 7230 §3.2.4: the
name is a token; a space before the colon parses as trailing whitespace here). -/
def nameHasWS (name : Bytes) : Bool := name.contains bSP || name.contains bHT

/-- **M1.** Any request header whose NAME carries whitespace ⇒ reject. -/
def anyBadFieldName (req : Request) : Bool :=
  req.headers.any (fun kv => nameHasWS kv.1)

/-! ## L1 — Transfer-Encoding, chunked must be the final coding -/

/-- The transfer-coding list of the request: every `Transfer-Encoding` header's
value, split on comma, each token `OWS`-trimmed and lowercased, concatenated in
header/list order. -/
def teCodings (req : Request) : List Bytes :=
  (req.headers.filter (fun kv => lowerBytes kv.1 == teNameLower)).flatMap
    (fun kv => (splitOn bCOMMA kv.2).map (fun t => lowerBytes (trimOWS t)))

/-- **L1.** `Transfer-Encoding` is present and its FINAL coding is not `chunked`
(RFC 7230 §3.3.3 — body length undeterminable ⇒ `400`). No TE header ⇒ not bad. -/
def teFinalBad (req : Request) : Bool :=
  match (teCodings req).reverse with
  | [] => false
  | last :: _ => last != chunkedTok

/-! ## J2 — Expect must be `100-continue` (the only defined expectation) -/

/-- The `Expect` field values, `OWS`-trimmed and lowercased. -/
def expectValues (req : Request) : List Bytes :=
  (req.headers.filter (fun kv => lowerBytes kv.1 == expectNameLower)).map
    (fun kv => lowerBytes (trimOWS kv.2))

/-- **J2.** Any `Expect` value other than `100-continue` (RFC 7231 §5.1.1 ⇒ `417`). -/
def expectBad (req : Request) : Bool :=
  (expectValues req).any (fun v => v != continueTok)

/-! ## The rejection response (417); the 400 reuses `RequestValidation.badRequestResp` -/

/-- `417 Expectation Failed` — an unsupported `Expect` (J2). -/
def expectationFailedResp : Response :=
  { status := 417, reason := strBytes "Expectation Failed", headers := []
    body := strBytes "expectation failed\n" }

theorem expectationFailedResp_status : expectationFailedResp.status = 417 := rfl

/-! ## The stage -/

/-- **The framing-validation gate.** Request phase, in order: field-name strictness
(M1 ⇒ `400`), Transfer-Encoding final-coding (L1 ⇒ `400`), Expect (J2 ⇒ `417`). The
first violation short-circuits; a clean request `.continue`s unchanged. Response
phase transparent. -/
def framingValidationStage : Stage where
  name := "framing-validation"
  onRequest := fun c =>
    if anyBadFieldName c.req then .respond badRequestResp
    else if teFinalBad c.req then .respond badRequestResp
    else if expectBad c.req then .respond expectationFailedResp
    else .continue c
  onResponse := fun _ b => b

theorem framingValidationStage_statusStable : Stage.statusStable framingValidationStage :=
  fun _ _ => rfl

/-! ## Rejection theorems (general, then witnessed) -/

/-- **M1.** A header-name-whitespace request `.respond`s the `400`. -/
theorem framingValidationStage_rejects_bad_field_name (c : Ctx)
    (h : anyBadFieldName c.req = true) :
    framingValidationStage.onRequest c = .respond badRequestResp := by
  show (if anyBadFieldName c.req then StageStep.respond badRequestResp else _) = _
  rw [h]; simp only [if_true]

/-- **L1.** A clean-name request whose TE final coding ≠ `chunked` `.respond`s the
`400`. -/
theorem framingValidationStage_rejects_te_not_final (c : Ctx)
    (hn : anyBadFieldName c.req = false) (ht : teFinalBad c.req = true) :
    framingValidationStage.onRequest c = .respond badRequestResp := by
  show (if anyBadFieldName c.req then _
        else if teFinalBad c.req then StageStep.respond badRequestResp else _) = _
  rw [hn, ht]; simp only [Bool.false_eq_true, if_false, if_true]

/-- **J2.** A clean-name, well-framed request with an unsupported `Expect`
`.respond`s the `417`. -/
theorem framingValidationStage_rejects_bad_expect (c : Ctx)
    (hn : anyBadFieldName c.req = false) (ht : teFinalBad c.req = false)
    (he : expectBad c.req = true) :
    framingValidationStage.onRequest c = .respond expectationFailedResp := by
  show (if anyBadFieldName c.req then _
        else if teFinalBad c.req then _
        else if expectBad c.req then StageStep.respond expectationFailedResp else _) = _
  rw [hn, ht, he]; simp only [Bool.false_eq_true, if_false, if_true]

/-- **Passes.** A request clearing all three checks `.continue`s unchanged. -/
theorem framingValidationStage_passes (c : Ctx)
    (hn : anyBadFieldName c.req = false) (ht : teFinalBad c.req = false)
    (he : expectBad c.req = false) :
    framingValidationStage.onRequest c = .continue c := by
  show (if anyBadFieldName c.req then _
        else if teFinalBad c.req then _
        else if expectBad c.req then _ else StageStep.continue c) = _
  rw [hn, ht, he]; simp only [Bool.false_eq_true, if_false]

/-! ## Gate composition — the rejection status survives a status-stable inner onion -/

/-- The `400` (TE-not-final) survives a status-stable inner onion. -/
theorem framingValidationStage_te_status (c : Ctx) (rest : List Stage)
    (handler : Ctx → Response) (hn : anyBadFieldName c.req = false)
    (ht : teFinalBad c.req = true) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (framingValidationStage :: rest) handler c).build).status = 400 := by
  have := pipeline_gate_status framingValidationStage rest handler c badRequestResp
    (framingValidationStage_rejects_te_not_final c hn ht) hst
  rw [this]; rfl

/-- The `417` (unsupported Expect) survives a status-stable inner onion. -/
theorem framingValidationStage_expect_status (c : Ctx) (rest : List Stage)
    (handler : Ctx → Response) (hn : anyBadFieldName c.req = false)
    (ht : teFinalBad c.req = false) (he : expectBad c.req = true)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (framingValidationStage :: rest) handler c).build).status = 417 := by
  have := pipeline_gate_status framingValidationStage rest handler c expectationFailedResp
    (framingValidationStage_rejects_bad_expect c hn ht he) hst
  rw [this]; rfl

/-- A rejected (bad-Expect) request never reaches the handler. -/
theorem framingValidationStage_expect_skips_handler (c : Ctx) (rest : List Stage)
    (handler handler' : Ctx → Response) (hn : anyBadFieldName c.req = false)
    (ht : teFinalBad c.req = false) (he : expectBad c.req = true) :
    runPipeline (framingValidationStage :: rest) handler c
      = runPipeline (framingValidationStage :: rest) handler' c :=
  pipeline_gate_ignores_handler framingValidationStage rest handler handler' c
    expectationFailedResp (framingValidationStage_rejects_bad_expect c hn ht he)

/-! ## Concrete non-vacuity witnesses (evaluate on real bytes) -/

/-- `/health` origin-form target. -/
def hpath : Bytes := [47, 104, 101, 97, 108, 116, 104]
/-- `HTTP/1.1`. -/
def v11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]
/-- `GET`. -/
def mGET : Bytes := [71, 69, 84]
/-- `Host` (clean field-name). -/
def hostName : Bytes := [72, 111, 115, 116]
/-- `Transfer-Encoding` (as sent, mixed case). -/
def teNameWire : Bytes :=
  [84, 114, 97, 110, 115, 102, 101, 114, 45, 69, 110, 99, 111, 100, 105, 110, 103]
/-- `Expect` (as sent). -/
def expectNameWire : Bytes := [69, 120, 112, 101, 99, 116]

/-- **L1 witness.** `Transfer-Encoding: chunked, gzip` — chunked is NOT final. -/
def teNotFinalCtx : Ctx :=
  { input := [], req :=
      { method := mGET, target := hpath, version := v11
        headers := [(hostName, [120]),
                    -- "chunked, gzip"
                    (teNameWire, [99, 104, 117, 110, 107, 101, 100, 44, 32,
                                  103, 122, 105, 112])] } }

/-- **L1 non-vacuity contrast.** `Transfer-Encoding: gzip, chunked` — chunked IS
final (a legitimately framed request). -/
def teFinalOkCtx : Ctx :=
  { input := [], req :=
      { method := mGET, target := hpath, version := v11
        headers := [(hostName, [120]),
                    -- "gzip, chunked"
                    (teNameWire, [103, 122, 105, 112, 44, 32,
                                  99, 104, 117, 110, 107, 101, 100])] } }

/-- **J2 witness.** `Expect: drorb-nonsense-99` — an unsupported expectation. -/
def badExpectCtx : Ctx :=
  { input := [], req :=
      { method := mGET, target := hpath, version := v11
        headers := [(hostName, [120]),
                    -- "drorb-nonsense-99"
                    (expectNameWire, [100, 114, 111, 114, 98, 45, 110, 111, 110,
                                      115, 101, 110, 115, 101, 45, 57, 57])] } }

/-- **J2 non-vacuity contrast.** `Expect: 100-continue` — the one defined
expectation (passes this gate; the inner serve answers it). -/
def okExpectCtx : Ctx :=
  { input := [], req :=
      { method := mGET, target := hpath, version := v11
        headers := [(hostName, [120]),
                    (expectNameWire, [49, 48, 48, 45, 99, 111, 110, 116, 105,
                                      110, 117, 101])] } }

/-- **M1 witness.** A header whose NAME is `Host ` (trailing space — the parse of
`Host : x`, space before the colon). -/
def wsNameCtx : Ctx :=
  { input := [], req :=
      { method := mGET, target := hpath, version := v11
        headers := [([72, 111, 115, 116, 32], [120])] } }  -- "Host " : x

/-- **Clean request** — clean names, `gzip, chunked` TE (final = chunked), and
`Expect: 100-continue`. Clears all three checks. -/
def okFramingCtx : Ctx :=
  { input := [], req :=
      { method := mGET, target := hpath, version := v11
        headers := [(hostName, [120]),
                    (teNameWire, [103, 122, 105, 112, 44, 32,
                                  99, 104, 117, 110, 107, 101, 100]),
                    (expectNameWire, [49, 48, 48, 45, 99, 111, 110, 116, 105,
                                      110, 117, 101])] } }

/-! ### The guard facts (`decide` — reduces on explicit bytes) -/

theorem teNotFinal_clean_names : anyBadFieldName teNotFinalCtx.req = false := by decide
theorem teNotFinal_bad : teFinalBad teNotFinalCtx.req = true := by decide
theorem teFinalOk_ok : teFinalBad teFinalOkCtx.req = false := by decide

theorem badExpect_clean_names : anyBadFieldName badExpectCtx.req = false := by decide
theorem badExpect_te_ok : teFinalBad badExpectCtx.req = false := by decide
theorem badExpect_bad : expectBad badExpectCtx.req = true := by decide
theorem okExpect_ok : expectBad okExpectCtx.req = false := by decide

theorem wsName_bad : anyBadFieldName wsNameCtx.req = true := by decide

theorem okFraming_names_ok : anyBadFieldName okFramingCtx.req = false := by decide
theorem okFraming_te_ok : teFinalBad okFramingCtx.req = false := by decide
theorem okFraming_expect_ok : expectBad okFramingCtx.req = false := by decide

/-! ### The stage genuinely rejects / accepts each witness -/

/-- **L1.** `chunked, gzip` ⇒ the gate answers `400`. -/
theorem teNotFinal_rejected :
    framingValidationStage.onRequest teNotFinalCtx = .respond badRequestResp :=
  framingValidationStage_rejects_te_not_final teNotFinalCtx teNotFinal_clean_names teNotFinal_bad

/-- **J2.** `drorb-nonsense-99` ⇒ the gate answers `417`. -/
theorem badExpect_rejected :
    framingValidationStage.onRequest badExpectCtx = .respond expectationFailedResp :=
  framingValidationStage_rejects_bad_expect badExpectCtx
    badExpect_clean_names badExpect_te_ok badExpect_bad

/-- **M1.** `Host ` (whitespace in the name) ⇒ the gate answers `400`. -/
theorem wsName_rejected :
    framingValidationStage.onRequest wsNameCtx = .respond badRequestResp :=
  framingValidationStage_rejects_bad_field_name wsNameCtx wsName_bad

/-- **Passes.** The clean request `.continue`s unchanged. -/
theorem okFraming_passes :
    framingValidationStage.onRequest okFramingCtx = .continue okFramingCtx :=
  framingValidationStage_passes okFramingCtx okFraming_names_ok okFraming_te_ok okFraming_expect_ok

/-- **Non-vacuity contrast.** The same gate `.continue`s the clean request but
`.respond`s a `400`/`417` on the malformed ones — it genuinely discriminates. -/
theorem gate_discriminates :
    (framingValidationStage.onRequest okFramingCtx = .continue okFramingCtx)
    ∧ (framingValidationStage.onRequest teNotFinalCtx = .respond badRequestResp)
    ∧ (framingValidationStage.onRequest badExpectCtx = .respond expectationFailedResp)
    ∧ (framingValidationStage.onRequest wsNameCtx = .respond badRequestResp) :=
  ⟨okFraming_passes, teNotFinal_rejected, badExpect_rejected, wsName_rejected⟩

/-! ### Executable sanity checks (evaluate on real bytes) -/

def decideStatus : StageStep → Nat
  | .respond r => r.status
  | .continue _ => 200

#guard decideStatus (framingValidationStage.onRequest teNotFinalCtx) == 400
#guard decideStatus (framingValidationStage.onRequest badExpectCtx) == 417
#guard decideStatus (framingValidationStage.onRequest wsNameCtx) == 400
#guard decideStatus (framingValidationStage.onRequest okFramingCtx) == 200
#guard decideStatus (framingValidationStage.onRequest teFinalOkCtx) == 200
#guard decideStatus (framingValidationStage.onRequest okExpectCtx) == 200

/-! ## Axiom audit -/

#print axioms framingValidationStage_rejects_bad_field_name
#print axioms framingValidationStage_rejects_te_not_final
#print axioms framingValidationStage_rejects_bad_expect
#print axioms framingValidationStage_passes
#print axioms framingValidationStage_te_status
#print axioms framingValidationStage_expect_status
#print axioms framingValidationStage_expect_skips_handler
#print axioms teNotFinal_rejected
#print axioms badExpect_rejected
#print axioms wsName_rejected
#print axioms okFraming_passes
#print axioms gate_discriminates

end Reactor.Stage.FramingValidation
