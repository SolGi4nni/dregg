import Reactor.Pipeline

/-!
# Reactor.Stage.RequestValidation — the request-line + Host validation gate

The deployed serve dispatches on the request *path* and does not validate the
request line or headers (the wave-4 RFC conformance probe,
`docs/engine/review/CONFORMANCE-PROBE.md`: "the request-validation layer is
absent"). This stage is the missing gate, run FIRST in the request phase (before
the routing fold), enforcing the RFC 7230/7231 request-line MUSTs the probe
found violated:

* **C1 / C2 — Host (RFC 7230 §5.4, MUST ×2).** An HTTP/1.1 request MUST carry
  *exactly one* `Host` header. Zero (`C1`) or more than one (`C2`) ⇒ `400`.
* **B2 — method (RFC 7231 §4.1).** An unrecognized request method ⇒ `501 Not
  Implemented` (rather than being silently served as `GET`).
* **G1 — version (RFC 7230 §2.6).** An unsupported HTTP version (anything but
  `HTTP/1.1` / `HTTP/1.0`) ⇒ `505 HTTP Version Not Supported`.
* **C3 — request-target (RFC 7230 §5.3.2, MUST).** A server MUST *accept* the
  absolute-form request-target and route it like origin-form. This stage
  NORMALIZES `http://authority/path` → `/path` on the passed-through context so
  the downstream path matcher keys on the origin-form. (NB: the driving task
  described C3 as "reject absolute-form ⇒ 400"; that is the opposite of §5.3.2
  and of the probe's own C3 pass-condition — `results_rfc.json` requires
  `absolute-form status == origin-form status == 200`. Rejecting would leave C3
  red. This stage does the RFC-correct thing: accept + normalize. See the report
  residual.)

## What is proven (headline, non-vacuous on concrete witnesses)

* `validationStage_rejects_bad_version` — bad version ⇒ `.respond` the `505`.
* `validationStage_rejects_unknown_method` — unknown method ⇒ `.respond` the `501`.
* `validationStage_rejects_bad_host` — zero/dup `Host` ⇒ `.respond` the `400`
  (instantiated by `missingHost_rejected` / `dupHost_rejected`).
* `validationStage_passes_valid` — a well-formed request `.continue`s with its
  target normalized to origin-form.
* `normalize_absolute_form` — the absolute-form target `http://x/health`
  normalizes to `/health` (the C3 fix, computed on concrete bytes).
* Gate composition: `validationStage_rejects_*_status` carry the `4xx/5xx`
  through a status-stable inner onion; `validationStage_skips_handler` shows the
  handler never runs on a rejected request.

Witness non-vacuity: every guard fact is `by decide` on explicit ASCII byte
lists (no `native_decide`, no opaque `String.toUTF8` in a decided position).
-/

namespace Reactor.Stage.RequestValidation

open Reactor.Pipeline
open Proto (Bytes Request)

/-- A string literal as its UTF-8 wire bytes (used only for response reason/body
text — never forced in a `decide`d position). -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## Tokens (explicit ASCII bytes so every decision reduces in the kernel) -/

/-- `Host` header name. -/
def hostName : Bytes := [72, 111, 115, 116]

/-- `HTTP/1.1`. -/
def httpV11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]
/-- `HTTP/1.0`. -/
def httpV10 : Bytes := [72, 84, 84, 80, 47, 49, 46, 48]

/-- `GET`. -/ def mGET     : Bytes := [71, 69, 84]
/-- `POST`. -/ def mPOST    : Bytes := [80, 79, 83, 84]
/-- `HEAD`. -/ def mHEAD    : Bytes := [72, 69, 65, 68]
/-- `PUT`. -/ def mPUT      : Bytes := [80, 85, 84]
/-- `DELETE`. -/ def mDELETE : Bytes := [68, 69, 76, 69, 84, 69]
/-- `PATCH`. -/ def mPATCH   : Bytes := [80, 65, 84, 67, 72]
/-- `OPTIONS`. -/ def mOPTIONS : Bytes := [79, 80, 84, 73, 79, 78, 83]
/-- `TRACE`. -/ def mTRACE   : Bytes := [84, 82, 65, 67, 69]
/-- `CONNECT`. -/ def mCONNECT : Bytes := [67, 79, 78, 78, 69, 67, 84]

/-! ## The decisions -/

/-- The HTTP versions this endpoint serves. Anything else ⇒ `505` (G1). -/
def supportedVersions : List Bytes := [httpV11, httpV10]

/-- Whether the request's version token is supported. -/
def versionSupported (v : Bytes) : Bool := supportedVersions.contains v

/-- The recognized request methods (RFC 7231 §4.1 registry, minus obsoletes).
An unrecognized method ⇒ `501` (B2). -/
def knownMethods : List Bytes :=
  [mGET, mPOST, mHEAD, mPUT, mDELETE, mPATCH, mOPTIONS, mTRACE, mCONNECT]

/-- Whether the request method is recognized. -/
def methodKnown (m : Bytes) : Bool := knownMethods.contains m

/-- Number of `Host` header fields in the request. -/
def hostCount (req : Request) : Nat :=
  (req.headers.filter (fun nv => nv.1 == hostName)).length

/-- **The Host discipline (RFC 7230 §5.4).** An HTTP/1.1 request MUST carry
exactly one `Host`; an HTTP/1.0 request may carry at most one. Anything else is
a violation (C1: count 0; C2: count ≥ 2). -/
def hostOk (req : Request) : Bool :=
  if req.version == httpV11 then hostCount req == 1 else hostCount req ≤ 1

/-! ## Absolute-form → origin-form normalization (C3, RFC 7230 §5.3.2) -/

/-- The suffix of `bs` immediately AFTER the first occurrence of `pat`, or `none`
if `pat` never occurs. -/
def afterSubstr (pat : Bytes) : Bytes → Option Bytes
  | [] => none
  | x :: xs =>
    if pat.isPrefixOf (x :: xs) then some ((x :: xs).drop pat.length)
    else afterSubstr pat xs

/-- From a byte string, the suffix starting at the first `/` (ASCII 47); `"/"` if
there is none. Applied to the authority+path of an absolute-form target it yields
the origin-form path. -/
def pathFrom : Bytes → Bytes
  | [] => [47]
  | x :: xs => if x == 47 then x :: xs else pathFrom xs

/-- **Normalize an absolute-form request-target to origin-form.** `http://x/health`
→ `/health`; an already-origin-form (or asterisk-form) target — one with no
`"://"` — is returned unchanged. This is the §5.3.2 "accept absolute-form and
reconstruct the effective target" step the path matcher was missing. -/
def normalizeTarget (t : Bytes) : Bytes :=
  match afterSubstr [58, 47, 47] t with        -- "://"
  | some rest => pathFrom rest
  | none => t

/-! ## The rejection responses -/

/-- `400 Bad Request` — the Host violation (C1/C2). -/
def badRequestResp : Response :=
  { status := 400, reason := strBytes "Bad Request", headers := []
    body := strBytes "bad request\n" }

/-- `501 Not Implemented` — an unrecognized method (B2). -/
def notImplementedResp : Response :=
  { status := 501, reason := strBytes "Not Implemented", headers := []
    body := strBytes "not implemented\n" }

/-- `505 HTTP Version Not Supported` — an unsupported version (G1). -/
def badVersionResp : Response :=
  { status := 505, reason := strBytes "HTTP Version Not Supported", headers := []
    body := strBytes "http version not supported\n" }

theorem badRequestResp_status : badRequestResp.status = 400 := rfl
theorem notImplementedResp_status : notImplementedResp.status = 501 := rfl
theorem badVersionResp_status : badVersionResp.status = 505 := rfl

/-! ## The stage -/

/-- **The request-validation gate.** Request phase, in order: version (G1),
method (B2), Host (C1/C2). The first violation short-circuits with its `4xx/5xx`.
A request that clears all three passes with its target normalized to origin-form
(C3). Response phase transparent. -/
def validationStage : Stage where
  name := "request-validation"
  onRequest := fun c =>
    if versionSupported c.req.version then
      if methodKnown c.req.method then
        if hostOk c.req then
          .continue { c with req := { c.req with target := normalizeTarget c.req.target } }
        else .respond badRequestResp
      else .respond notImplementedResp
    else .respond badVersionResp
  onResponse := fun _ b => b

theorem validationStage_statusStable : Stage.statusStable validationStage := fun _ _ => rfl

/-! ## Rejection theorems (general, then witnessed) -/

/-- **G1.** An unsupported version makes the gate `.respond` the `505`. -/
theorem validationStage_rejects_bad_version (c : Ctx)
    (hv : versionSupported c.req.version = false) :
    validationStage.onRequest c = .respond badVersionResp := by
  show (if versionSupported c.req.version then _ else StageStep.respond badVersionResp) = _
  rw [hv]; simp only [Bool.false_eq_true, if_false]

/-- **B2.** A recognized-version request with an unknown method `.respond`s the
`501`. -/
theorem validationStage_rejects_unknown_method (c : Ctx)
    (hv : versionSupported c.req.version = true)
    (hm : methodKnown c.req.method = false) :
    validationStage.onRequest c = .respond notImplementedResp := by
  show (if versionSupported c.req.version then
          (if methodKnown c.req.method then _ else StageStep.respond notImplementedResp)
        else _) = _
  rw [hv, hm]; simp only [Bool.false_eq_true, if_false, if_true]

/-- **C1/C2.** A recognized-version, known-method request whose `Host` discipline
fails (zero or duplicate `Host`) `.respond`s the `400`. -/
theorem validationStage_rejects_bad_host (c : Ctx)
    (hv : versionSupported c.req.version = true)
    (hm : methodKnown c.req.method = true)
    (hh : hostOk c.req = false) :
    validationStage.onRequest c = .respond badRequestResp := by
  show (if versionSupported c.req.version then
          (if methodKnown c.req.method then
            (if hostOk c.req then _ else StageStep.respond badRequestResp)
           else _)
        else _) = _
  rw [hv, hm, hh]; simp only [Bool.false_eq_true, if_false, if_true]

/-- **Passes.** A request clearing version/method/Host `.continue`s with its
target normalized to origin-form (C3). -/
theorem validationStage_passes_valid (c : Ctx)
    (hv : versionSupported c.req.version = true)
    (hm : methodKnown c.req.method = true)
    (hh : hostOk c.req = true) :
    validationStage.onRequest c
      = .continue { c with req := { c.req with target := normalizeTarget c.req.target } } := by
  show (if versionSupported c.req.version then
          (if methodKnown c.req.method then
            (if hostOk c.req then
              StageStep.continue { c with req := { c.req with target := normalizeTarget c.req.target } }
             else _)
           else _)
        else _) = _
  rw [hv, hm, hh]; simp only [if_true]

/-! ## Gate composition — the rejection status survives the inner onion -/

/-- The `505` survives a status-stable inner onion. -/
theorem validationStage_bad_version_status (c : Ctx) (rest : List Stage)
    (handler : Ctx → Response) (hv : versionSupported c.req.version = false)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (validationStage :: rest) handler c).build).status = 505 := by
  have := pipeline_gate_status validationStage rest handler c badVersionResp
    (validationStage_rejects_bad_version c hv) hst
  rw [this]; rfl

/-- The `501` survives a status-stable inner onion. -/
theorem validationStage_unknown_method_status (c : Ctx) (rest : List Stage)
    (handler : Ctx → Response) (hv : versionSupported c.req.version = true)
    (hm : methodKnown c.req.method = false)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (validationStage :: rest) handler c).build).status = 501 := by
  have := pipeline_gate_status validationStage rest handler c notImplementedResp
    (validationStage_rejects_unknown_method c hv hm) hst
  rw [this]; rfl

/-- The `400` survives a status-stable inner onion. -/
theorem validationStage_bad_host_status (c : Ctx) (rest : List Stage)
    (handler : Ctx → Response) (hv : versionSupported c.req.version = true)
    (hm : methodKnown c.req.method = true) (hh : hostOk c.req = false)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (validationStage :: rest) handler c).build).status = 400 := by
  have := pipeline_gate_status validationStage rest handler c badRequestResp
    (validationStage_rejects_bad_host c hv hm hh) hst
  rw [this]; rfl

/-- A rejected request never reaches the handler (swapping the handler is a
no-op). Instantiated here on the missing-Host case. -/
theorem validationStage_bad_host_skips_handler (c : Ctx) (rest : List Stage)
    (handler handler' : Ctx → Response)
    (hv : versionSupported c.req.version = true)
    (hm : methodKnown c.req.method = true) (hh : hostOk c.req = false) :
    runPipeline (validationStage :: rest) handler c
      = runPipeline (validationStage :: rest) handler' c :=
  pipeline_gate_ignores_handler validationStage rest handler handler' c
    badRequestResp (validationStage_rejects_bad_host c hv hm hh)

/-! ## Concrete non-vacuity witnesses -/

/-- A well-formed HTTP/1.1 `GET /health` with exactly one `Host`. -/
def okCtx : Ctx :=
  { input := [], req := { method := mGET, target := [47, 104, 101, 97, 108, 116, 104]
                          version := httpV11, headers := [(hostName, [120])] } }

/-- Missing `Host` (C1): HTTP/1.1 `GET /health`, no `Host` header. -/
def missingHostCtx : Ctx :=
  { input := [], req := { method := mGET, target := [47, 104, 101, 97, 108, 116, 104]
                          version := httpV11, headers := [] } }

/-- Duplicate `Host` (C2): two `Host` header fields. -/
def dupHostCtx : Ctx :=
  { input := [], req := { method := mGET, target := [47, 104, 101, 97, 108, 116, 104]
                          version := httpV11
                          headers := [(hostName, [97]), (hostName, [98])] } }

/-- Unknown method (B2): `FOOBAR /health`. -/
def unknownMethodCtx : Ctx :=
  { input := [], req := { method := [70, 79, 79, 66, 65, 82]
                          target := [47, 104, 101, 97, 108, 116, 104]
                          version := httpV11, headers := [(hostName, [120])] } }

/-- Bad version (G1): `HTTP/9.9`. -/
def badVersionCtx : Ctx :=
  { input := [], req := { method := mGET, target := [47, 104, 101, 97, 108, 116, 104]
                          version := [72, 84, 84, 80, 47, 57, 46, 57]
                          headers := [(hostName, [120])] } }

/-- Absolute-form target `http://x/health` — the bytes of a real absolute-form
request-target (C3). -/
def absTarget : Bytes :=
  [104, 116, 116, 112, 58, 47, 47, 120, 47, 104, 101, 97, 108, 116, 104]

/-- `/health` origin-form target. -/
def originTarget : Bytes := [47, 104, 101, 97, 108, 116, 104]

/-- Absolute-form request (C3), otherwise well-formed. -/
def absFormCtx : Ctx :=
  { input := [], req := { method := mGET, target := absTarget
                          version := httpV11, headers := [(hostName, [120])] } }

/-! ### The guard facts (`decide` — reduces on explicit bytes) -/

theorem missingHost_bad : hostOk missingHostCtx.req = false := by decide
theorem dupHost_bad : hostOk dupHostCtx.req = false := by decide
theorem unknownMethod_unknown : methodKnown unknownMethodCtx.req.method = false := by decide
theorem badVersion_unsupported : versionSupported badVersionCtx.req.version = false := by decide
theorem okCtx_version_ok : versionSupported okCtx.req.version = true := by decide
theorem okCtx_method_ok : methodKnown okCtx.req.method = true := by decide
theorem okCtx_host_ok : hostOk okCtx.req = true := by decide
theorem absCtx_version_ok : versionSupported absFormCtx.req.version = true := by decide
theorem absCtx_method_ok : methodKnown absFormCtx.req.method = true := by decide
theorem absCtx_host_ok : hostOk absFormCtx.req = true := by decide

/-! ### The stage genuinely rejects / accepts each witness -/

/-- **C1.** Missing `Host` ⇒ the gate answers `400`. -/
theorem missingHost_rejected :
    validationStage.onRequest missingHostCtx = .respond badRequestResp :=
  validationStage_rejects_bad_host missingHostCtx (by decide) (by decide) missingHost_bad

/-- **C2.** Duplicate `Host` ⇒ the gate answers `400`. -/
theorem dupHost_rejected :
    validationStage.onRequest dupHostCtx = .respond badRequestResp :=
  validationStage_rejects_bad_host dupHostCtx (by decide) (by decide) dupHost_bad

/-- **B2.** Unknown method ⇒ the gate answers `501`. -/
theorem unknownMethod_rejected :
    validationStage.onRequest unknownMethodCtx = .respond notImplementedResp :=
  validationStage_rejects_unknown_method unknownMethodCtx (by decide) unknownMethod_unknown

/-- **G1.** Unsupported version ⇒ the gate answers `505`. -/
theorem badVersion_rejected :
    validationStage.onRequest badVersionCtx = .respond badVersionResp :=
  validationStage_rejects_bad_version badVersionCtx badVersion_unsupported

/-- **C3.** The absolute-form target `http://x/health` normalizes to `/health`. -/
theorem normalize_absolute_form : normalizeTarget absTarget = originTarget := by decide

/-- **C3, end to end.** A well-formed absolute-form request `.continue`s with its
target rewritten to the origin-form `/health` — so the downstream path matcher
routes it exactly like `GET /health` (⇒ `200`), which is what §5.3.2 / the probe
C3 pass-condition require. -/
theorem absForm_normalized :
    validationStage.onRequest absFormCtx
      = .continue { absFormCtx with req := { absFormCtx.req with target := originTarget } } := by
  rfl

/-- **Non-vacuity contrast.** The same gate `.continue`s a valid request but
`.respond`s a `400` on the missing-Host one — it genuinely discriminates. -/
theorem gate_discriminates :
    (validationStage.onRequest okCtx
      = .continue { okCtx with req := { okCtx.req with target := normalizeTarget okCtx.req.target } })
    ∧ validationStage.onRequest missingHostCtx = .respond badRequestResp :=
  ⟨validationStage_passes_valid okCtx okCtx_version_ok okCtx_method_ok okCtx_host_ok,
   missingHost_rejected⟩

/-! ### Executable sanity checks (evaluate on real bytes) -/

/-- The decisions compute the expected verdicts. -/
def decideStatus : StageStep → Nat
  | .respond r => r.status
  | .continue _ => 200

#guard decideStatus (validationStage.onRequest missingHostCtx) == 400
#guard decideStatus (validationStage.onRequest dupHostCtx) == 400
#guard decideStatus (validationStage.onRequest unknownMethodCtx) == 501
#guard decideStatus (validationStage.onRequest badVersionCtx) == 505
#guard decideStatus (validationStage.onRequest okCtx) == 200
#guard decideStatus (validationStage.onRequest absFormCtx) == 200
#guard normalizeTarget absTarget == originTarget
#guard normalizeTarget originTarget == originTarget

/-! ## Axiom audit -/

#print axioms validationStage_rejects_bad_version
#print axioms validationStage_rejects_unknown_method
#print axioms validationStage_rejects_bad_host
#print axioms validationStage_passes_valid
#print axioms validationStage_bad_host_status
#print axioms validationStage_bad_host_skips_handler
#print axioms missingHost_rejected
#print axioms dupHost_rejected
#print axioms unknownMethod_rejected
#print axioms badVersion_rejected
#print axioms normalize_absolute_form
#print axioms absForm_normalized
#print axioms gate_discriminates

end Reactor.Stage.RequestValidation
