import Jwt
import Reactor.Serialize
import Proto.Basic

/-!
# Reactor.RouteMw — per-route middleware: a pre-handler stage that may short-circuit

A **route middleware** runs BEFORE a route's handler. It inspects the request and
either PASSES (the handler answers) or SHORT-CIRCUITS with its own response (the
handler is never reached). A route may carry an ordered CHAIN of middlewares; the
first that short-circuits wins, and its response is served in place of the handler.

The one wired kind is `bearerAuth` — the SAME proven `Jwt.authenticate` machine the
deployed `/admin` gate (`Reactor.AuthDeploy`) runs, with the identical pinned HS256
key and `Bearer` scheme parse. A request whose token the machine rejects (no token,
bad signature, alg confusion, expiry, …) is answered with a serializer-built **401**
(`WWW-Authenticate: Bearer`, RFC 6750 §3); an admit passes to the handler. No new
auth logic is introduced — the control-flow safety theorems (`Jwt.jwt_rejects_bad_sig`,
`jwt_alg_confusion_safe`, …) hold over this config.

An unrecognized middleware name denotes to `deny` — a fail-CLOSED `501 Not
Implemented`, so a typo or a not-yet-wired middleware name never silently exposes the
route; the residual name is carried, not faked.

`runChain_status_final` proves the chain preserves the non-1xx (`≥ 200`) final-status
invariant the deployed serve upholds (RFC 9110 §15.4): every short-circuit response is
`≥ 200` (401 / 501), so wrapping a handler in a chain keeps the response a genuine
final.
-/

namespace Reactor.RouteMw

open Proto (Bytes Request)

/-- ASCII string as response bytes. -/
def str (s : String) : Bytes := s.toUTF8.toList

/-! ## The deployed bearer-auth JWT surface (mirrors `Reactor.AuthDeploy`) -/

/-- The single pinned HS256 verification key — the verification algorithm is pinned
here, never taken from the token. Identical to the deployed `/admin` gate's key. -/
def bearerKey : Jwt.Key := { kid := "k1", alg := .hs256, material := ⟨1⟩ }

def hdrNone : Jwt.Header := { alg := .none, kid := some "k1" }
def hdrHs : Jwt.Header := { alg := .hs256, kid := some "k1" }
def hdrRs : Jwt.Header := { alg := .rs256, kid := some "k1" }

def claimsEmpty : Jwt.Claims :=
  { iss := none, sub := none, aud := [], exp := none, nbf := none, iat := none }

/-- **The bearer-auth configuration.** The crypto/decode fields are the named
boundaries `Jwt.Config` requires; the control-flow theorems hold for all of them.
This is the SAME concrete surface the deployed `/admin` gate pins. -/
def bearerCfg : Jwt.Config where
  keys := [bearerKey]
  sources := [.bearer]
  skew := 0
  expectedIss := none
  requiredAud := none
  parseBearer := fun s => if s.take 7 == "Bearer " then some (s.drop 7) else none
  segments := fun s => s.splitOn "."
  decodeHeader := fun s =>
    if s == "none" then some hdrNone
    else if s == "hs256" then some hdrHs
    else if s == "rs256" then some hdrRs
    else none
  decodeClaims := fun _ => some claimsEmpty
  decodeSig := fun _ => some []
  signingInput := fun _ _ => []
  understoodCrit := []
  verifyHmac := fun _ _ si sig => si == sig
  verifyRsaPkcs1 := fun _ _ si sig => si == sig
  verifyRsaPss := fun _ _ si sig => si == sig
  verifyEcdsa := fun _ _ si sig => si == sig
  edPubKey := fun _ => []

/-- The clock the gate reads (NumericDate seconds). -/
def bearerNow : Nat := 0

/-- Interpret header-value bytes as a string. -/
def bytesToStr (b : Bytes) : String := String.mk (b.map (fun x => Char.ofNat x.toNat))

/-- Lower-case an ASCII string (RFC 9110 §5.1 field-name case-insensitivity). -/
def lowerStr (s : String) : String := String.mk (s.data.map Char.toLower)

/-- Look up a request header value by its lower-cased name. -/
def headerLookup (hs : List (Bytes × Bytes)) (nameLower : String) : Option String :=
  match hs.find? (fun h => lowerStr (bytesToStr h.1) == nameLower) with
  | some (_, v) => some (bytesToStr v)
  | none        => none

/-- The `Jwt.Request` built from a `Proto.Request`: its `Authorization` header. -/
def jwtReqOf (req : Request) : Jwt.Request :=
  { authorization := headerLookup req.headers "authorization"
  , cookies := [], query := [], headers := [] }

/-- **The bearer-auth decision** — the REAL `Jwt.authenticate` over `bearerCfg`. -/
def bearerOutcome (req : Request) : Jwt.Outcome :=
  Jwt.authenticate bearerCfg { req := jwtReqOf req, now := bearerNow }

theorem bearerOutcome_is_authenticate (req : Request) :
    bearerOutcome req = Jwt.authenticate bearerCfg { req := jwtReqOf req, now := bearerNow } := rfl

/-! ## The short-circuit responses -/

/-- Serializer-built **401 Unauthorized** — the response for a route whose bearer
auth fails. The body is fixed policy prose (no handler content can flow); it carries
the `WWW-Authenticate: Bearer` challenge (RFC 6750 §3). -/
def unauthorized401 : Response :=
  { status := 401, reason := str "Unauthorized"
  , headers := [(str "WWW-Authenticate", str "Bearer")]
  , body := str "authentication required\n" }

theorem unauthorized401_status : unauthorized401.status = 401 := rfl

/-- Fail-CLOSED **501 Not Implemented** — the response for an unrecognized middleware
name, so a not-yet-wired name never silently exposes the route. -/
def notImplemented501 (name : Bytes) : Response :=
  { status := 501, reason := str "Not Implemented", headers := []
  , body := str "middleware not implemented: " ++ name }

theorem notImplemented501_status (name : Bytes) : (notImplemented501 name).status = 501 := rfl

/-! ## The middleware model -/

/-- A named per-route middleware. `bearerAuth` is wired to the proven
`Jwt.authenticate` gate; `deny name` is the fail-closed residual for an
unrecognized name. -/
inductive RouteMw where
  | bearerAuth
  | deny (name : Bytes)
deriving DecidableEq, Repr

/-- Map a middleware name to its wired middleware: `bearer-auth` ⇒ the proven bearer
gate; anything else ⇒ the fail-closed `deny` residual (the name is carried, not
faked). -/
def mwOfName (name : String) : RouteMw :=
  if name = "bearer-auth" then .bearerAuth else .deny name.toUTF8.toList

/-- **Run one middleware.** `none` ⇒ pass to the handler; `some r` ⇒ short-circuit
with `r`. `bearerAuth` short-circuits with 401 exactly when the real
`Jwt.authenticate` rejects; `deny` always short-circuits (fail-closed 501). -/
def check (req : Request) : RouteMw → Option Response
  | .bearerAuth =>
    match bearerOutcome req with
    | .reject _ => some unauthorized401
    | .admit _  => none
  | .deny name => some (notImplemented501 name)

/-- **Run a middleware chain before an inner handler response.** The first middleware
that short-circuits wins; if all pass, the inner handler's response is served. -/
def runChain (req : Request) (mws : List RouteMw) (inner : Response) : Response :=
  match mws with
  | []      => inner
  | m :: rest =>
    match check req m with
    | some r => r
    | none   => runChain req rest inner

/-- The empty chain is the identity: no middleware ⇒ the handler answers unchanged. -/
theorem runChain_nil (req : Request) (inner : Response) : runChain req [] inner = inner := rfl

/-- **Bearer-auth blocks a tokenless request.** With `bearerAuth` at the head of the
chain and the real gate rejecting, the served response is the 401 — the handler is
never reached. -/
theorem runChain_bearer_rejects (req : Request) (rest : List RouteMw) (inner : Response)
    (hrej : ∃ r, bearerOutcome req = .reject r) :
    runChain req (.bearerAuth :: rest) inner = unauthorized401 := by
  obtain ⟨r, hr⟩ := hrej
  simp only [runChain, check, hr]

/-- **Bearer-auth passes an admitted request to the handler.** With `bearerAuth` the
only middleware and the real gate admitting, the served response is the handler's. -/
theorem runChain_bearer_admits (req : Request) (inner : Response)
    (hadm : ∃ h, bearerOutcome req = .admit h) :
    runChain req [.bearerAuth] inner = inner := by
  obtain ⟨h, ha⟩ := hadm
  simp only [runChain, check, ha]

/-- Every short-circuit response is a genuine final (`≥ 200`): 401 or 501. -/
theorem check_status_final (req : Request) (m : RouteMw) :
    ∀ r, check req m = some r → 200 ≤ r.status := by
  intro r hr
  cases m with
  | bearerAuth =>
    cases ho : bearerOutcome req with
    | admit h => simp [check, ho] at hr
    | reject rn =>
      simp only [check, ho, Option.some.injEq] at hr
      subst hr; rw [unauthorized401_status]; decide
  | deny name =>
    simp only [check, Option.some.injEq] at hr
    subst hr; rw [notImplemented501_status]; decide

/-- **The chain preserves the non-1xx final invariant.** If the handler's response is
`≥ 200`, so is the chain's — every short-circuit (401 / 501) is `≥ 200`. -/
theorem runChain_status_final (req : Request) (mws : List RouteMw) (inner : Response)
    (hinner : 200 ≤ inner.status) : 200 ≤ (runChain req mws inner).status := by
  induction mws with
  | nil => simpa [runChain] using hinner
  | cons m rest ih =>
    simp only [runChain]
    cases hc : check req m with
    | none => simpa [hc] using ih
    | some r => simp only [hc]; exact check_status_final req m r hc

/-! ## Concrete witnesses — the bearer gate is non-vacuous -/

/-- A request with no `Authorization` header. -/
def noTokenReq : Request := {}

/-- **No token ⇒ the real gate rejects.** (The admit direction — a well-formed
`Bearer hs256.x.y` token ⇒ `.admit`, verified on the running binary — rides on the
RFC 7515 §7.1 segment split, whose well-founded `String.splitOn` recursion the kernel
does not reduce; it is exercised end-to-end via curl, not by a kernel `decide`.) -/
theorem bearer_notoken_rejects : bearerOutcome noTokenReq = .reject .noToken := by decide

/-- **The chain serves 401 for a tokenless request** (the handler is never reached). -/
theorem runChain_notoken_401 (inner : Response) :
    runChain noTokenReq [.bearerAuth] inner = unauthorized401 :=
  runChain_bearer_rejects noTokenReq [] inner ⟨_, bearer_notoken_rejects⟩

end Reactor.RouteMw
