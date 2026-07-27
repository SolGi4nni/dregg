import Reactor.Pipeline
import Reactor.Stage.CookieSecure

/-!
# Reactor.Stage.SessionCookie — deployed session-cookie issuance (PARITY-LEDGER ck.1)

The response half of ck.1 was PARTIAL-inert: `Reactor.Stage.CookieSecure` proved the
`Set-Cookie` hardener (`Secure`/`HttpOnly`/`SameSite=Lax` appended to every weak
cookie), but NO deployed route ever produced a `Set-Cookie` for it to harden — wiring
the hardener alone would have been provably inert. This module supplies the missing
half as two stages:

* `sessionGateStage` — a request-phase gate: `GET /login` (method + target scoped)
  is answered `200` (the session-issue route). Everything else passes through.
* `setCookieStage` — a response-phase stamp: on `GET /login`, push the WEAK session
  cookie (`sid=…`, name=value only, no security attributes) onto the finalized
  response. Placed OUTSIDE the deployed rewrite onion, so the pair reaches the
  wire; the deployed `cookieSecureStage` (placed outermost) then hardens it — the
  previously-inert proven leaf goes live.

## What is proved here (all pure kernel)

* `sessionGate_fires` / `sessionGate_passes` — the gate answers exactly the
  method+target scope and nothing else.
* `setCookieStage_effect` / `setCookieStage_noop` — the stamp appends exactly
  `(Set-Cookie, weakCookie)` in scope and is the identity off the target.
* `hardenHeader_weak` — the deployed hardener maps the stamped pair to
  `(Set-Cookie, harden weakCookie)`; with `harden_has_secure`/`_httpOnly`/`_sameSite`
  the wire cookie provably carries all three attributes.
* `demo_issue_and_harden` — a concrete single-pipeline witness: the composed
  three-stage pipeline serves `GET /login` with the HARDENED cookie.

The composition over the REAL deployed fold lives in `Reactor.DeployPlus5`.
-/

namespace Reactor.Stage.SessionCookie

open Reactor.Pipeline
open Proto (Bytes)

/-- ASCII `"GET"`. -/
def getBytes : Bytes := [71, 69, 84]

/-- ASCII `"/login"` — the session-issue route. -/
def loginTarget : Bytes := [47, 108, 111, 103, 105, 110]

/-- ASCII `"Set-Cookie"`. -/
def setCookieName : Bytes := [83, 101, 116, 45, 67, 111, 111, 107, 105, 101]

/-- The weak session cookie the route issues (ASCII `"sid=7f3a9c"`): name=value ONLY,
none of the three security attributes — the exact shape the deployed hardener
repairs. -/
def weakCookie : Bytes := [115, 105, 100, 61, 55, 102, 51, 97, 57, 99]

/-- ASCII `"OK"`. -/
def okReason : Bytes := [79, 75]

/-- ASCII `"ok"`. -/
def loginBody : Bytes := [111, 107]

/-- The route's guard: method `GET`, target `/login`. -/
def inScope (c : Ctx) : Bool :=
  c.req.method == getBytes && c.req.target == loginTarget

/-- The login route's bare response. NO headers: the cookie is stamped by
`setCookieStage` (response phase, outside the rewrite onion) and hardened by the
deployed `cookieSecureStage`; a header-less seed also keeps the deployed
content-type-gated body rewrite a passthrough. -/
def loginResp : Reactor.Response :=
  { status := 200, reason := okReason, headers := [], body := loginBody }

/-- **The session-issue gate.** Answers `GET /login` with the bare `200`; passes
everything else through untouched. -/
def sessionGateStage : Stage where
  name := "session-issue"
  onRequest := fun c => if inScope c then .respond loginResp else .continue c
  onResponse := fun _ b => b

/-- **The weak-cookie stamp.** Response phase: on `GET /login`, push
`(Set-Cookie, weakCookie)` onto the finalized response; identity elsewhere. -/
def setCookieStage : Stage where
  name := "session-cookie-stamp"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if inScope c then b.addHeader (setCookieName, weakCookie) else b

/-! ## The guard -/

theorem inScope_true (c : Ctx) (hm : c.req.method = getBytes)
    (ht : c.req.target = loginTarget) : inScope c = true := by
  unfold inScope
  rw [hm, ht]
  rfl

theorem inScope_false_of_target (c : Ctx) (h : ¬ c.req.target = loginTarget) :
    inScope c = false := by
  unfold inScope
  have hf : (c.req.target == loginTarget) = false := by
    cases hb : c.req.target == loginTarget
    · rfl
    · exact absurd (eq_of_beq hb) h
  rw [hf, Bool.and_false]

/-! ## Gate behaviour -/

/-- The gate fires on `GET /login`. -/
theorem sessionGate_fires (c : Ctx) (hm : c.req.method = getBytes)
    (ht : c.req.target = loginTarget) :
    sessionGateStage.onRequest c = .respond loginResp := by
  show (if inScope c then StageStep.respond loginResp else StageStep.continue c) = _
  rw [inScope_true c hm ht]
  rfl

/-- The gate passes any non-login target through untouched. -/
theorem sessionGate_passes (c : Ctx) (h : ¬ c.req.target = loginTarget) :
    sessionGateStage.onRequest c = .continue c := by
  show (if inScope c then StageStep.respond loginResp else StageStep.continue c) = _
  rw [inScope_false_of_target c h]
  rfl

/-- The gate's response phase is the identity. -/
theorem sessionGate_statusStable : Stage.statusStable sessionGateStage :=
  fun _ _ => rfl

/-! ## Stamp behaviour -/

/-- **The stamp's byte-effect.** On `GET /login` the finalized pipeline is the
tail's with `(Set-Cookie, weakCookie)` appended — for ANY tail/handler. -/
theorem setCookieStage_effect (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (hm : c.req.method = getBytes) (ht : c.req.target = loginTarget) :
    runPipeline (setCookieStage :: rest) h c
      = (runPipeline rest h c).addHeader (setCookieName, weakCookie) := by
  rw [pipeline_stage_effect setCookieStage rest h c c rfl]
  show (if inScope c then (runPipeline rest h c).addHeader (setCookieName, weakCookie)
        else runPipeline rest h c) = _
  rw [inScope_true c hm ht]
  rfl

/-- Off the login target the stamp is the identity. -/
theorem setCookieStage_noop (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (ht : ¬ c.req.target = loginTarget) :
    runPipeline (setCookieStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect setCookieStage rest h c c rfl]
  show (if inScope c then (runPipeline rest h c).addHeader (setCookieName, weakCookie)
        else runPipeline rest h c) = _
  rw [inScope_false_of_target c ht]
  rfl

/-- The stamp never changes the built status (either branch). -/
theorem setCookieStage_statusStable : Stage.statusStable setCookieStage := by
  intro c b
  show ((if inScope c then b.addHeader (setCookieName, weakCookie) else b).build).status
       = b.build.status
  by_cases h : inScope c = true
  · rw [if_pos h]; rfl
  · rw [if_neg h]

/-! ## The hardener composition (the previously-inert leaf, made live) -/

open Reactor.Stage.CookieSecure (harden hardenHeader isSetCookie
  harden_has_secure harden_has_httpOnly harden_has_sameSite
  secureTok httpOnlyTok sameSiteTok containsTok)

/-- The stamped name IS a `Set-Cookie` (case-insensitive), so the deployed hardener
rewrites it. Kernel-decided on the explicit bytes. -/
theorem isSetCookie_stamped : isSetCookie setCookieName = true := by decide

/-- **The hardener maps the stamped weak pair to the hardened pair.** -/
theorem hardenHeader_weak :
    hardenHeader (setCookieName, weakCookie) = (setCookieName, harden weakCookie) := by
  show (if isSetCookie setCookieName then (setCookieName, harden weakCookie)
        else (setCookieName, weakCookie)) = _
  rw [if_pos isSetCookie_stamped]

/-- The hardened wire cookie carries ALL THREE security attributes
(case-insensitive) — instantiating the hardener's general theorems on the deployed
weak cookie. -/
theorem hardened_weak_attrs :
    containsTok secureTok (harden weakCookie) = true
  ∧ containsTok httpOnlyTok (harden weakCookie) = true
  ∧ containsTok sameSiteTok (harden weakCookie) = true :=
  ⟨harden_has_secure weakCookie, harden_has_httpOnly weakCookie,
   harden_has_sameSite weakCookie⟩

/-! ## A concrete end-to-end witness -/

/-- A bare `GET /login` request context. -/
def loginCtx : Ctx :=
  { input := []
    req := { method := getBytes, target := loginTarget, version := [], headers := [] }
    attrs := [] }

/-- **Issue-and-harden, end to end.** The three-stage pipeline (hardener outermost,
stamp, then the gate) answers the `GET /login` context `200` carrying the HARDENED
`Set-Cookie` — the issuance and the previously-inert hardener composed, concrete
and non-vacuous. -/
theorem demo_issue_and_harden :
    ((runPipeline
      [Reactor.Stage.CookieSecure.cookieSecureStage, setCookieStage, sessionGateStage]
      (fun _ => loginResp) loginCtx).build).status = 200
  ∧ (setCookieName, harden weakCookie)
      ∈ ((runPipeline
        [Reactor.Stage.CookieSecure.cookieSecureStage, setCookieStage, sessionGateStage]
        (fun _ => loginResp) loginCtx).build).headers := by
  decide

end Reactor.Stage.SessionCookie

#print axioms Reactor.Stage.SessionCookie.sessionGate_fires
#print axioms Reactor.Stage.SessionCookie.setCookieStage_effect
#print axioms Reactor.Stage.SessionCookie.hardenHeader_weak
#print axioms Reactor.Stage.SessionCookie.hardened_weak_attrs
#print axioms Reactor.Stage.SessionCookie.demo_issue_and_harden
