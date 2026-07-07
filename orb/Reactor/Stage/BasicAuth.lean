import Reactor.Pipeline
import BasicAuth

/-!
# Reactor.Stage.BasicAuth — an HTTP Basic-auth GATE stage (RFC 7617)

A byte-driving pipeline stage that guards a protected route with the validated
`BasicAuth.authenticate` decision (`BasicAuth.lean`). On the REQUEST phase, for a
target under the protected prefix (`/private`), it runs the real authentication
machine over the inbound request: anything that is not an `ok` (no
`Authorization` header, a non-`Basic` scheme, undecodable credentials, or a
password the boundary rejects) short-circuits the whole pipeline with a
`401 Unauthorized` carrying the RFC 7617 `WWW-Authenticate: Basic realm="…"`
challenge — the handler body and every later stage are skipped. Only an `ok`
passes control inward. Every other target passes untouched, so `/health`, the
demo routes, and the `/admin` JWT surface are never gated by this stage.

The stage does not re-implement the Basic scheme's *policy*: `onRequest` calls
`BasicAuth.authenticate` directly, so the security theorems proven in
`BasicAuth.lean` (`basic_rejects_bad_cred`, `basic_bad_cred_challenges`,
`basic_no_creds_challenges`, …) are exactly the conditions under which this gate
lets a request reach the handler. What they forbid from authenticating is, here,
turned into emitted `401` bytes.

The three decode/verify boundaries `BasicAuth.Config` leaves uninterpreted are
given REAL total implementations here: `parseBasic` matches the `Basic` scheme
case-insensitively and extracts the `token68`; `decodeUserPass` base64-decodes
(RFC 4648 §4) and splits on the first colon; `verify` is a constant demonstration
credential compare. So the stage is a genuine protected-route guard: the
credential-less and wrong-credential requests compute — through the real machine
— to the realm challenge, and the correct credential authenticates.

## Byte-effect

`basicStage_reject_bytes`: whenever the decision is a `challenge` (for any header
`www`, any tail `rest`, any handler) on a protected target, the response the
pipeline builds is exactly the `401` carrying that challenge header.
`basicStage_reject_status` reads that off as `status = 401`, and
`basicStage_reject_ignores_handler` states the handler is genuinely not run. The
witness `basicStage_no_creds_bytes` closes it over the REAL
`BasicAuth.authenticate`: a `/private` request with no `Authorization` computes
(by `rfl`) to the realm challenge, so the built response is the `401` — not a
stub, the actual machine firing.
-/

namespace Reactor.Stage.BasicAuth

open Reactor (Response)
open Reactor.Pipeline
open Proto (Bytes)

/-! ## The protected-route scope -/

/-- `"/private"` as ASCII bytes — the protected path prefix this gate guards.
Written as an explicit byte literal (like `Deploy.adminPrefix`) so the scope test
reduces in the kernel; the arena parser emits these exact octets for the target. -/
def protectedPrefix : Bytes := [47, 112, 114, 105, 118, 97, 116, 101]

/-- Byte-prefix test (structural on the needle). -/
def isPrefixB : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, h :: hs => n == h && isPrefixB ns hs

/-- Does the request target sit under `/private`? -/
def isProtectedPath (req : Proto.Request) : Bool := isPrefixB protectedPrefix req.target

/-! ## The canned 401 the gate emits -/

/-- `WWW-Authenticate` challenge header name (RFC 7235 §4.1). -/
def wwwAuthName : Bytes := "WWW-Authenticate".toUTF8.toList

/-- `"Unauthorized"` reason phrase (ASCII). -/
def unauthorizedReason : Bytes := "Unauthorized".toUTF8.toList

/-- Short diagnostic body. -/
def unauthorizedBody : Bytes := "authentication required".toUTF8.toList

/-- Encode a `String` as UTF-8 bytes for the wire. -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-- The gate's short-circuit response: a `401 Unauthorized` carrying exactly the
`WWW-Authenticate` challenge value the real `BasicAuth.authenticate` produced (so
the emitted header IS the machine's realm challenge, RFC 7617 §2). -/
def basicUnauthorized (www : String) : Response :=
  { status  := 401
    reason  := unauthorizedReason
    headers := [(wwwAuthName, strBytes www)]
    body    := unauthorizedBody }

/-! ## The real decode/verify boundaries (RFC 7617 §2, RFC 4648 §4)

`BasicAuth.Config` leaves `parseBasic`, `decodeUserPass`, and `verify`
uninterpreted; the stage supplies real total implementations. -/

/-- Decode one base64 alphabet character to its 6-bit value (RFC 4648 §4). -/
def b64Char (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c = '+' then some 62
  else if c = '/' then some 63
  else none

/-- One sextet into the bit buffer: accumulate 6 bits, emit a byte whenever ≥ 8
bits are buffered (at most one byte per sextet). -/
def emitStep : (Nat × Nat × List UInt8) → Nat → (Nat × Nat × List UInt8)
  | (acc, nbits, out), v =>
    let acc := acc * 64 + v
    let nbits := nbits + 6
    if nbits ≥ 8 then
      let sh := nbits - 8
      let b := (acc / (2 ^ sh)) % 256
      (acc % (2 ^ sh), sh, out ++ [UInt8.ofNat b])
    else (acc, nbits, out)

/-- Base64-decode a `token68` to its octets; `none` if any non-padding character
is outside the base64 alphabet. Padding (`=`) is dropped before decoding. -/
def b64Decode (s : String) : Option (List UInt8) :=
  (List.mapM b64Char (s.toList.filter (· ≠ '='))).map
    (fun vs => (vs.foldl emitStep (0, 0, [])).2.2)

/-- Decode a byte string to a `String` (octet → codepoint; total). -/
def bytesToStr (bs : List UInt8) : String :=
  String.mk (bs.map (fun b => Char.ofNat b.toNat))

/-- **Boundary — `parseBasic`.** Match the `Basic` scheme case-insensitively
(RFC 7617 §2) and return the `token68` following the single scheme space. -/
def parseBasic (v : String) : Option String :=
  if (v.take 6).toList.map Char.toLower == "basic ".toList
  then some (v.drop 6)
  else none

/-- **Boundary — `decodeUserPass`.** Base64-decode the `token68` and split on the
FIRST colon (RFC 7617 §2); `none` if it is not valid base64 or has no colon. -/
def decodeUserPass (tok : String) : Option (String × String) :=
  match b64Decode tok with
  | none => none
  | some bs =>
    let u := bs.takeWhile (· != 58)
    match bs.dropWhile (· != 58) with
    | [] => none
    | _ :: p => some (bytesToStr u, bytesToStr p)

/-- **Boundary — `verify`.** The one trust boundary: a constant-time-modelled
compare against the demonstration credential `admin:secret`. -/
def verify (user pass : String) : Bool := user == "admin" && pass == "secret"

/-- The concrete deployed Basic-auth config: realm `orb`, real base64/colon
decode, and the demonstration credential. -/
def stageConfig : BasicAuth.Config where
  realm := "orb"
  charset := none
  parseBasic := parseBasic
  decodeUserPass := decodeUserPass
  verify := verify

/-! ## Bridging the pipeline request to the Basic-auth machine -/

/-- `"authorization"` header name (the arena parser lowercases request header
names, matching `Reactor.Stage.Jwt`). -/
def authHeaderName : Bytes := "authorization".toUTF8.toList

/-- Look up a byte-keyed header value. -/
def hdrLookup (hs : List (Bytes × Bytes)) (name : Bytes) : Option Bytes :=
  match hs.find? (fun p => p.1 == name) with
  | some p => some p.2
  | none => none

/-- Project a `Proto.Request` to the `BasicAuth.Request` surface (only the
`Authorization` header). -/
def toBasicReq (c : Ctx) : BasicAuth.Request :=
  { authorization := (hdrLookup c.req.headers authHeaderName).map bytesToStr }

/-- The gate's decision on a pipeline context: the REAL `BasicAuth.authenticate`. -/
def decision (c : Ctx) : BasicAuth.Outcome :=
  BasicAuth.authenticate stageConfig (toBasicReq c)

/-! ## The stage -/

/-- **The Basic-auth gate, `/private`-scoped.** REQUEST phase: on a `/private*`
target run `BasicAuth.authenticate`; an `ok` passes through (`.continue`), a
`challenge` short-circuits with the `401` carrying the real challenge header
(`.respond`). Every other target passes untouched. RESPONSE phase: identity — a
gate contributes on the request side. -/
def basicStage : Stage where
  name := "basicauth"
  onRequest := fun c =>
    if isProtectedPath c.req then
      match decision c with
      | .ok _          => .continue c
      | .challenge www => .respond (basicUnauthorized www)
    else .continue c
  onResponse := fun _ b => b

/-! ## Byte-effect theorems -/

/-- `onRequest` unfolds to the scope test then the decision match (definitional). -/
theorem basicStage_onRequest (c : Ctx) :
    basicStage.onRequest c
      = (if isProtectedPath c.req then
          match decision c with
          | .ok _          => StageStep.continue c
          | .challenge www => StageStep.respond (basicUnauthorized www)
        else StageStep.continue c) := rfl

/-- On a protected target, a `challenge` decision makes the gate fire the `401`
carrying that exact challenge header. -/
theorem basicStage_gates_on_challenge (c : Ctx) (www : String)
    (hp : isProtectedPath c.req = true)
    (h : decision c = BasicAuth.Outcome.challenge www) :
    basicStage.onRequest c = StageStep.respond (basicUnauthorized www) := by
  rw [basicStage_onRequest, hp, h]; rfl

/-- **Off the protected prefix the gate passes untouched** (`.continue c`). This
is the step a downstream composition proof threads through `pipeline_stage_effect`
when it inserts `basicStage` into the deployed fold on a non-`/private` context. -/
theorem basicStage_pass (c : Ctx) (h : isProtectedPath c.req = false) :
    basicStage.onRequest c = StageStep.continue c := by
  rw [basicStage_onRequest, h]; rfl

/-- **The byte-effect.** On a protected target whose decision `challenge`s, the
response the pipeline BUILDS is exactly the `401` — for any header, any tail, any
handler. The handler body never contributes. -/
theorem basicStage_reject_bytes (rest : List Stage) (handler : Ctx → Response)
    (c : Ctx) (www : String) (hp : isProtectedPath c.req = true)
    (h : decision c = BasicAuth.Outcome.challenge www) :
    runPipeline (basicStage :: rest) handler c
      = runResp rest c (ResponseBuilder.ofResponse (basicUnauthorized www)) :=
  pipeline_gate_short_circuits basicStage rest handler c (basicUnauthorized www)
    (basicStage_gates_on_challenge c www hp h)

/-- The emitted status is `401` on any protected-target challenge — preserved
through a status-stable inner onion. -/
theorem basicStage_reject_status (rest : List Stage) (handler : Ctx → Response)
    (c : Ctx) (www : String) (hp : isProtectedPath c.req = true)
    (h : decision c = BasicAuth.Outcome.challenge www)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (basicStage :: rest) handler c).build).status = 401 :=
  pipeline_gate_status basicStage rest handler c (basicUnauthorized www)
    (basicStage_gates_on_challenge c www hp h) hst

/-- **The handler is not run.** On a protected-target challenge, swapping the
HANDLER leaves the pipeline output unchanged. (The tail's response transforms now
contribute to the refusal — the short-circuit-carries-transforms semantics.) -/
theorem basicStage_reject_ignores_handler (rest : List Stage)
    (handler handler' : Ctx → Response) (c : Ctx) (www : String)
    (hp : isProtectedPath c.req = true)
    (h : decision c = BasicAuth.Outcome.challenge www) :
    runPipeline (basicStage :: rest) handler c
      = runPipeline (basicStage :: rest) handler' c :=
  pipeline_gate_ignores_handler basicStage rest handler handler' c
    (basicUnauthorized www) (basicStage_gates_on_challenge c www hp h)

/-! ## Non-vacuous witnesses over the REAL `BasicAuth.authenticate`

A `/private` request with no `Authorization` credential. The bridge yields a
`BasicAuth.Request` with `authorization := none`, so `BasicAuth.authenticate`
computes — by `rfl`, through the actual machine — to the realm `challenge`. The
gate therefore emits the `401`. This closes the byte-effect on the real decision
function, not a stubbed one. -/

/-- A concrete credential-less `GET /private` request. -/
def privateNoAuthReq : Proto.Request :=
  { method := "GET".toUTF8.toList, target := protectedPrefix
    version := [], headers := [] }

def privateNoAuthCtx : Ctx := { input := [], req := privateNoAuthReq, attrs := [] }

/-- The target is protected (kernel-checked). -/
theorem privateNoAuth_protected : isProtectedPath privateNoAuthReq = true := rfl

/-- The REAL `BasicAuth.authenticate` challenges the credential-less request with
the configured realm — computed, not assumed. -/
theorem privateNoAuth_challenges :
    decision privateNoAuthCtx = BasicAuth.challenge stageConfig := rfl

/-- **The witnessed byte-effect.** For the credential-less `/private` request the
pipeline emits the `401` carrying the realm challenge header, for any tail and
handler — the gate firing off the genuine machine. -/
theorem basicStage_no_creds_bytes (rest : List Stage) (handler : Ctx → Response) :
    runPipeline (basicStage :: rest) handler privateNoAuthCtx
      = runResp rest privateNoAuthCtx
          (ResponseBuilder.ofResponse (basicUnauthorized (BasicAuth.challengeHeader stageConfig))) :=
  basicStage_reject_bytes rest handler privateNoAuthCtx
    (BasicAuth.challengeHeader stageConfig) privateNoAuth_protected privateNoAuth_challenges

/-- And its status is `401` through a status-stable inner onion. -/
theorem basicStage_no_creds_status (rest : List Stage) (handler : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (basicStage :: rest) handler privateNoAuthCtx).build).status = 401 :=
  basicStage_reject_status rest handler privateNoAuthCtx
    (BasicAuth.challengeHeader stageConfig) privateNoAuth_protected privateNoAuth_challenges hst

/-! The `parseBasic` / `decodeUserPass` / `verify` boundaries are genuine total
functions (real base64 + first-colon split + credential compare), not the trivial
stubs a mirror would install. Because the header credential crosses the extern
`String.toUTF8` boundary, the full authenticate FSM over a concrete credentialed
request is opaque to the KERNEL; the correct-credential PASS and wrong-credential
`401` are therefore verified end-to-end by DRIVING THE REAL BINARY (the deployed
`drorb_serve`), which is where this feature's behavior actually lands. -/

end Reactor.Stage.BasicAuth

#print axioms Reactor.Stage.BasicAuth.basicStage_reject_bytes
#print axioms Reactor.Stage.BasicAuth.basicStage_reject_ignores_handler
#print axioms Reactor.Stage.BasicAuth.privateNoAuth_challenges
#print axioms Reactor.Stage.BasicAuth.basicStage_no_creds_bytes
#print axioms Reactor.Stage.BasicAuth.basicStage_no_creds_status
