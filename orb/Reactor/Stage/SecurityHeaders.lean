import Reactor.Pipeline
import SecurityHeaders

/-!
# Reactor.Stage.SecurityHeaders — the security-header response-transform stage

A byte-driving pipeline `Stage` that stamps the real response security-header set
(HSTS / X-Frame-Options / X-Content-Type-Options / Referrer-Policy) onto every
response, wiring the actual `SecurityHeaders.render` function from
`SecurityHeaders.lean` (RFC 6797 HSTS + companions) — NOT a stub.

The stage always passes the request phase (`.continue`) and, on the response
phase, folds every header `SecurityHeaders.render` emits for the deployed policy
onto the affine `ResponseBuilder` with `addHeader` (one in-place `headers.push`
per header, not a `Response` realloc per stage).

The byte-effect (`securityheadersStage_hsts_present`): the
`Strict-Transport-Security` header — name AND the RFC-6797-rendered value the real
`hstsRender` produces — genuinely appears in the BUILT pipeline output, for ANY
tail and handler. It rides on `pipeline_stage_effect` + `build_addHeaders`.
-/

namespace Reactor.Stage.SecurityHeaders

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)

/-! ## The deployed policy — the REAL `SecurityHeaders` members -/

/-- The deployed HSTS policy: one year, subdomains, preload (RFC 6797 §6.1.1). -/
def hstsPolicy : _root_.SecurityHeaders.Hsts where
  maxAge := 31536000
  includeSubDomains := true
  preload := true

/-- The deployed response-security policy: HSTS + `X-Frame-Options: DENY`
+ `X-Content-Type-Options: nosniff` + `Referrer-Policy: no-referrer`. -/
def policy : _root_.SecurityHeaders.Policy where
  hsts := some hstsPolicy
  csp := none
  xfo := some .deny
  noSniff := true
  referrerPolicy := some "no-referrer"

/-! ## Wire encoding — the `String` header set to `Bytes × Bytes` -/

/-- One `SecurityHeaders` (name, value) pair rendered to wire bytes (UTF-8). -/
def toWireHeader (kv : String × String) : Bytes × Bytes :=
  (kv.1.toUTF8.toList, kv.2.toUTF8.toList)

/-- The full security-header set for `policy`, as wire header pairs — driven off
the REAL `SecurityHeaders.render`. -/
def wireHeaders (p : _root_.SecurityHeaders.Policy) : List (Bytes × Bytes) :=
  (_root_.SecurityHeaders.render p).map toWireHeader

/-- The HSTS header name on the wire (`Strict-Transport-Security`). -/
def hstsHeaderName : Bytes := "Strict-Transport-Security".toUTF8.toList

/-- The HSTS header value on the wire — the exact bytes the real RFC-6797
`hstsRender` produces for the deployed policy (`max-age=31536000;
includeSubDomains; preload`). -/
def hstsHeaderVal : Bytes := (_root_.SecurityHeaders.hstsRender hstsPolicy).toUTF8.toList

/-! ## The stage -/

/-- **The security-header stage.** A response-transform: always passes the
request phase, then folds the real rendered security-header set onto the affine
builder (`addHeader` = one in-place `headers.push` per header). -/
def securityheadersStage : Stage where
  name := "securityheaders"
  onRequest := fun c => .continue c
  onResponse := fun _ b => (wireHeaders policy).foldl ResponseBuilder.addHeader b

/-! ## The byte-effect -/

/-- The stage factors through `pipeline_stage_effect`: its `onResponse` folds the
whole security-header set onto the tail builder. -/
theorem securityheadersStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (securityheadersStage :: rest) h c
      = (wireHeaders policy).foldl ResponseBuilder.addHeader (runPipeline rest h c) :=
  pipeline_stage_effect securityheadersStage rest h c c rfl

/-- The HSTS wire header is the head of the rendered set — the deployed policy
carries an HSTS member, so `SecurityHeaders.render` leads with it. -/
theorem hsts_in_wireHeaders :
    (hstsHeaderName, hstsHeaderVal) ∈ wireHeaders policy := by
  have hhead : _root_.SecurityHeaders.render policy
      = ("Strict-Transport-Security", _root_.SecurityHeaders.hstsRender hstsPolicy)
        :: (_root_.SecurityHeaders.render policy).tail := rfl
  show (hstsHeaderName, hstsHeaderVal) ∈ (_root_.SecurityHeaders.render policy).map toWireHeader
  rw [hhead, List.map_cons]
  exact List.mem_cons_self

/-- **The byte-effect.** The real `Strict-Transport-Security` header — name and the
RFC-6797-rendered value — genuinely appears in the BUILT pipeline output, for ANY
tail and handler. A true byte-driver: `build_addHeaders` carries the affine fold
into the finalized `Response` the serializer renders. -/
theorem securityheadersStage_hsts_present (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (hstsHeaderName, hstsHeaderVal)
      ∈ ((runPipeline (securityheadersStage :: rest) h c).build).headers := by
  rw [securityheadersStage_effect, build_addHeaders]
  exact List.mem_append.mpr (Or.inr hsts_in_wireHeaders)

/-! ## The config-generalized stage (Track 1 · Phase 1 stone)

`securityheadersStage` folds the module const `policy`. `securityHeadersStageOf`
generalizes it to fold a CFG-SUPPLIED `SecurityHeaders.Policy`, so an operator
config decides the emitted security-header VALUE set. At the deployed `policy` it
is byte-identical to `securityheadersStage` (`securityHeadersStageOf_default_eq`,
a THEOREM — the no-regression anchor). -/

/-- **The config-parameterized security-header stage.** Always passes the request
phase, then folds the real rendered header set for the CFG-supplied policy `p` onto
the affine builder (`addHeader` = one in-place `headers.push` per header). -/
def securityHeadersStageOf (p : _root_.SecurityHeaders.Policy) : Stage where
  name := "securityheaders"
  onRequest := fun c => .continue c
  onResponse := fun _ b => (wireHeaders p).foldl ResponseBuilder.addHeader b

/-- **NO-REGRESSION anchor.** At the deployed `policy` the generalized stage IS the
deployed `securityheadersStage`, byte-for-byte — a THEOREM, not a redefinition. -/
theorem securityHeadersStageOf_default_eq :
    securityHeadersStageOf policy = securityheadersStage := rfl

/-- The generalized stage factors through `pipeline_stage_effect`: its `onResponse`
folds the whole rendered header set for `p` onto the tail builder. -/
theorem securityHeadersStageOf_effect (p : _root_.SecurityHeaders.Policy)
    (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (securityHeadersStageOf p :: rest) h c
      = (wireHeaders p).foldl ResponseBuilder.addHeader (runPipeline rest h c) :=
  pipeline_stage_effect (securityHeadersStageOf p) rest h c c rfl

/-- The HSTS wire header of a policy carrying an HSTS member is the head of its
rendered set — the value is the RFC-6797 `hstsRender` of THAT policy's HSTS. -/
theorem hsts_in_wireHeadersOf (p : _root_.SecurityHeaders.Policy)
    (hh : _root_.SecurityHeaders.Hsts) (hp : p.hsts = some hh) :
    (hstsHeaderName, (_root_.SecurityHeaders.hstsRender hh).toUTF8.toList) ∈ wireHeaders p := by
  have hmem : ("Strict-Transport-Security", _root_.SecurityHeaders.hstsRender hh)
      ∈ _root_.SecurityHeaders.render p := by
    unfold _root_.SecurityHeaders.render; rw [hp]; simp
  have hmap := List.mem_map_of_mem (f := toWireHeader) hmem
  simpa only [wireHeaders, toWireHeader, hstsHeaderName] using hmap

/-- **The config-driven byte-effect (∀ p with HSTS).** For ANY policy `p` carrying
an HSTS member `hh`, the `Strict-Transport-Security` header — name AND the exact
RFC-6797 `hstsRender hh` VALUE the CFG denotes — genuinely appears in the BUILT
pipeline output, for ANY tail and handler. The value in the conclusion is
`hstsRender hh`: spec(cfg), not X=X. -/
theorem securityHeadersStageOf_hsts_present (p : _root_.SecurityHeaders.Policy)
    (hh : _root_.SecurityHeaders.Hsts) (hp : p.hsts = some hh)
    (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (hstsHeaderName, (_root_.SecurityHeaders.hstsRender hh).toUTF8.toList)
      ∈ ((runPipeline (securityHeadersStageOf p :: rest) h c).build).headers := by
  rw [securityHeadersStageOf_effect, build_addHeaders]
  exact List.mem_append.mpr (Or.inr (hsts_in_wireHeadersOf p hh hp))

/-! ### Non-vacuity: the emitted header set genuinely DEPENDS on the cfg -/

/-- `wireHeaders` of the empty policy is empty (no member ⇒ no header). -/
theorem wireHeaders_empty :
    wireHeaders ({} : _root_.SecurityHeaders.Policy) = [] := rfl

/-- **The pre-state where the conclusion is FALSE.** Deployed with the EMPTY policy,
the CFG contributes NO security headers — in particular NO `Strict-Transport-Security`
of ANY value. Together with `securityHeadersStageOf_hsts_present` (present exactly
when the cfg carries HSTS) this witnesses that the emitted header set is genuinely
cfg-dependent: the header is TRUE under an HSTS cfg and FALSE under the empty cfg. -/
theorem hsts_absent_when_empty (v : Bytes) :
    (hstsHeaderName, v) ∉ wireHeaders ({} : _root_.SecurityHeaders.Policy) := by
  rw [wireHeaders_empty]; simp

/-- **Present exactly when configured.** The HSTS value the cfg denotes appears in
the cfg-contributed header set iff the cfg carries an HSTS member — the value is
`hstsRender hh`, the operator's chosen policy rendered. -/
theorem hsts_present_when_configured (hh : _root_.SecurityHeaders.Hsts) :
    (hstsHeaderName, (_root_.SecurityHeaders.hstsRender hh).toUTF8.toList)
      ∈ wireHeaders ({ hsts := some hh } : _root_.SecurityHeaders.Policy) :=
  hsts_in_wireHeadersOf _ hh rfl


/-! ## Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}. -/
#print axioms securityHeadersStageOf_default_eq
#print axioms securityHeadersStageOf_hsts_present
#print axioms hsts_absent_when_empty
#print axioms hsts_present_when_configured

end Reactor.Stage.SecurityHeaders
