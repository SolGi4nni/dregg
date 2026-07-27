import Reactor.Pipeline

/-!
# Reactor.Stage.AuthRequest — subrequest / forward-auth GATE

A byte-driving `Stage` for the extensible serve fold. Before the handler runs, an
external authorization service is consulted (the subrequest); its status decides the
request's fate:

* **2xx** — allow: the request passes through to the handler;
* **401** — deny with `401 Unauthorized`;
* **403** — deny with `403 Forbidden`;
* **anything else** — the auth service misbehaved: fail closed with `500 Internal
  Server Error`.

This is the subrequest / forward-auth pattern. In the sans-IO serve the
subrequest is performed by the accept path (or a prior stage), which stashes the auth
service's status in the attribute bag under `authStatusKey`; this stage reads it and
applies the decision. Configured *exclude paths* (health checks, public assets) skip
auth entirely by a prefix match on the request target.

## The decision core

`decideAuth status` maps the auth status to one of four outcomes; `outcomeResp`
turns a denying outcome into its response. Its truth table (`decide_allow_2xx`,
`decide_deny_401`, `decide_deny_403`, `decide_error_other`) is proven directly and is
genuinely non-vacuous — different statuses take different branches.

## The byte effect

* `authStage_denies_401` / `authStage_denies_403` / `authStage_error_500` — a denying
  auth status forces the corresponding refusal onto the wire, skipping the handler;
* `authStage_allows` — a 2xx auth status passes the handler's bytes through untouched;
* `authStage_excluded_skips` — an excluded path bypasses the gate regardless of auth;
* `authStage_changes_bytes` — same handler, an allowed and a denied request emit
  different status bytes.
-/

namespace Reactor.Stage.AuthRequest

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## The refusal responses -/

def reason401 : Bytes := "Unauthorized".toUTF8.toList
def reason403 : Bytes := "Forbidden".toUTF8.toList
def reason500 : Bytes := "Internal Server Error".toUTF8.toList
def denyBody  : Bytes := "auth subrequest denied\n".toUTF8.toList
def errBody   : Bytes := "auth subrequest failed\n".toUTF8.toList

/-- `401 Unauthorized`. -/
def resp401 : Response := error4xx 401 reason401 denyBody
/-- `403 Forbidden`. -/
def resp403 : Response := error4xx 403 reason403 denyBody
/-- `500 Internal Server Error` — fail-closed for a misbehaving auth service. -/
def resp500 : Response := error4xx 500 reason500 errBody

/-! ## The decision core -/

/-- The outcome of consulting the auth service. -/
inductive Outcome where
  /-- 2xx: allow the request through to the handler. -/
  | allow
  /-- 401: deny unauthorized. -/
  | deny401
  /-- 403: deny forbidden. -/
  | deny403
  /-- Any other status: fail closed with a 500. -/
  | error500
deriving DecidableEq, Repr

/-- **The auth decision.** 2xx → allow; 401 → deny401; 403 → deny403; otherwise the
auth service misbehaved → fail closed (error500). Total. -/
def decideAuth (status : Nat) : Outcome :=
  if 200 ≤ status ∧ status ≤ 299 then .allow
  else if status = 401 then .deny401
  else if status = 403 then .deny403
  else .error500

/-- The response a denying/erroring outcome serves (`allow` has none). -/
def outcomeResp : Outcome → Option Response
  | .allow    => none
  | .deny401  => some resp401
  | .deny403  => some resp403
  | .error500 => some resp500

/-! ### Truth table (non-vacuity) -/

/-- A 2xx auth status allows. -/
theorem decide_allow_2xx {status : Nat} (h : 200 ≤ status ∧ status ≤ 299) :
    decideAuth status = .allow := by simp [decideAuth, h]

/-- A 200 allows (concrete). -/
theorem decide_allow_200 : decideAuth 200 = .allow := by decide

/-- A 401 denies unauthorized. -/
theorem decide_deny_401 : decideAuth 401 = .deny401 := by decide

/-- A 403 denies forbidden. -/
theorem decide_deny_403 : decideAuth 403 = .deny403 := by decide

/-- A 302 (or any non-2xx, non-401/403) fails closed with a 500. -/
theorem decide_error_302 : decideAuth 302 = .error500 := by decide

/-- A 500 auth status fails closed. -/
theorem decide_error_500 : decideAuth 500 = .error500 := by decide

/-! ## Exclude-path prefix match -/

/-- `needle` is a prefix of `hay`. -/
def isPrefix : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, h :: hs => n == h && isPrefix ns hs

/-- The configured exclude prefixes: paths that bypass auth (health probe).
`/healthz` as explicit ASCII bytes so prefix matching reduces in the kernel. -/
def excludePrefixes : List Bytes :=
  [ [47, 104, 101, 97, 108, 116, 104, 122] ]

/-- Whether the request target starts with any configured exclude prefix. -/
def excluded (req : Request) : Bool :=
  excludePrefixes.any (fun p => isPrefix p req.target)

/-! ## Reading the auth status off the context -/

/-- Attribute key holding the auth subrequest's status (its byte-length = the status
code the accept path recorded from the auth service). -/
def authStatusKey : String := "auth.status"

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The auth status reconstructed from the attribute bag (`0` when absent — no auth
result, which fails closed). -/
def authStatusOf (c : Ctx) : Nat := (lookupBytes c authStatusKey).length

/-! ## The stage -/

/-- **The forward-auth gate stage.** Request phase: an excluded path `.continue`s
(auth bypassed); otherwise apply the real decision to the auth status — `allow`
→ `.continue`, a denying/erroring outcome → `.respond` its refusal (short-circuit).
Response phase: transparent. -/
def authStage : Stage where
  name := "auth-request"
  onRequest := fun c =>
    if excluded c.req then .continue c
    else match outcomeResp (decideAuth (authStatusOf c)) with
      | some r => .respond r
      | none   => .continue c
  onResponse := fun _ b => b

/-! ## Request-phase decisions -/

/-- A denying auth status (via `outcomeResp = some r`) on a non-excluded path gates. -/
theorem authStage_onReq_respond (c : Ctx) (hex : excluded c.req = false)
    {r : Response} (hr : outcomeResp (decideAuth (authStatusOf c)) = some r) :
    authStage.onRequest c = .respond r := by
  simp only [authStage, hex, Bool.false_eq_true, if_false, hr]

/-- An allowing auth status (via `outcomeResp = none`) on a non-excluded path passes. -/
theorem authStage_onReq_continue (c : Ctx) (hex : excluded c.req = false)
    (hr : outcomeResp (decideAuth (authStatusOf c)) = none) :
    authStage.onRequest c = .continue c := by
  simp only [authStage, hex, Bool.false_eq_true, if_false, hr]

/-- An excluded path passes regardless of auth. -/
theorem authStage_onReq_excluded (c : Ctx) (hex : excluded c.req = true) :
    authStage.onRequest c = .continue c := by
  simp only [authStage, hex, if_true]

/-! ## Byte-effect theorems -/

/-- **Gate byte-effect (deny/error).** A refusing auth outcome forces its refusal
onto the wire — for ANY tail and handler, the handler is skipped. -/
theorem authStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hex : excluded c.req = false) {r : Response}
    (hr : outcomeResp (decideAuth (authStatusOf c)) = some r) :
    runPipeline (authStage :: rest) h c = runResp rest c (ResponseBuilder.ofResponse r) :=
  pipeline_gate_short_circuits authStage rest h c r (authStage_onReq_respond c hex hr)

/-- The gate's refusal status is preserved through a status-stable inner onion. -/
theorem authStage_gate_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hex : excluded c.req = false) {r : Response}
    (hr : outcomeResp (decideAuth (authStatusOf c)) = some r)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (authStage :: rest) h c).build).status = r.status :=
  pipeline_gate_status authStage rest h c r (authStage_onReq_respond c hex hr) hst

/-- **Pass-through byte-effect.** An allowed request passes the handler's bytes. -/
theorem authStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hex : excluded c.req = false)
    (hr : outcomeResp (decideAuth (authStatusOf c)) = none) :
    runPipeline (authStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect authStage rest h c c (authStage_onReq_continue c hex hr)]
  rfl

/-! ## Concrete contexts (non-vacuity) -/

/-- Build an attr value of a given byte-length (encodes a status via its length). -/
def statusAttr (n : Nat) : Bytes := List.replicate n (0 : UInt8)

/-- A request the auth service allowed (status 200), not excluded. -/
def allowCtx : Ctx := { input := [], req := {}, attrs := [(authStatusKey, statusAttr 200)] }

/-- A request the auth service denied unauthorized (status 401). -/
def denyCtx : Ctx := { input := [], req := {}, attrs := [(authStatusKey, statusAttr 401)] }

/-- A request the auth service denied forbidden (status 403). -/
def forbidCtx : Ctx := { input := [], req := {}, attrs := [(authStatusKey, statusAttr 403)] }

/-- A request the auth service answered oddly (status 302) — fail closed. -/
def oddCtx : Ctx := { input := [], req := {}, attrs := [(authStatusKey, statusAttr 302)] }

/-- A request to an excluded health path (`/healthz`, explicit bytes) — auth bypassed. -/
def healthCtx : Ctx :=
  { input := [], req := { target := [47, 104, 101, 97, 108, 116, 104, 122] }, attrs := [] }

theorem allowCtx_status : authStatusOf allowCtx = 200 := by
  have : lookupBytes allowCtx authStatusKey = statusAttr 200 := by
    simp [lookupBytes, allowCtx, authStatusKey]
  rw [authStatusOf, this, statusAttr, List.length_replicate]
theorem denyCtx_status  : authStatusOf denyCtx  = 401 := by
  have : lookupBytes denyCtx authStatusKey = statusAttr 401 := by
    simp [lookupBytes, denyCtx, authStatusKey]
  rw [authStatusOf, this, statusAttr, List.length_replicate]
theorem forbidCtx_status : authStatusOf forbidCtx = 403 := by
  have : lookupBytes forbidCtx authStatusKey = statusAttr 403 := by
    simp [lookupBytes, forbidCtx, authStatusKey]
  rw [authStatusOf, this, statusAttr, List.length_replicate]
theorem oddCtx_status   : authStatusOf oddCtx   = 302 := by
  have : lookupBytes oddCtx authStatusKey = statusAttr 302 := by
    simp [lookupBytes, oddCtx, authStatusKey]
  rw [authStatusOf, this, statusAttr, List.length_replicate]

theorem allowCtx_notExcluded : excluded allowCtx.req = false := by decide
theorem denyCtx_notExcluded  : excluded denyCtx.req  = false := by decide

/-- **A 401 auth status forces a `401` onto the wire** (status-stable onion). -/
theorem authStage_denies_401 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (authStage :: rest) h denyCtx).build).status = 401 := by
  have hr : outcomeResp (decideAuth (authStatusOf denyCtx)) = some resp401 := by
    rw [denyCtx_status]; rfl
  have := authStage_gate_status rest h denyCtx denyCtx_notExcluded hr hst
  simpa using this

/-- **A 403 auth status forces a `403` onto the wire.** -/
theorem authStage_denies_403 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (authStage :: rest) h forbidCtx).build).status = 403 := by
  have hr : outcomeResp (decideAuth (authStatusOf forbidCtx)) = some resp403 := by
    rw [forbidCtx_status]; rfl
  have hex : excluded forbidCtx.req = false := by decide
  have := authStage_gate_status rest h forbidCtx hex hr hst
  simpa using this

/-- **An odd auth status fails closed with a `500`.** -/
theorem authStage_error_500 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (authStage :: rest) h oddCtx).build).status = 500 := by
  have hr : outcomeResp (decideAuth (authStatusOf oddCtx)) = some resp500 := by
    rw [oddCtx_status]; rfl
  have hex : excluded oddCtx.req = false := by decide
  have := authStage_gate_status rest h oddCtx hex hr hst
  simpa using this

/-- **An allowed (2xx) request passes the handler through unchanged.** -/
theorem authStage_allows (h : Ctx → Response) :
    (runPipeline [authStage] h allowCtx).build = h allowCtx := by
  have hr : outcomeResp (decideAuth (authStatusOf allowCtx)) = none := by
    rw [allowCtx_status]; rfl
  rw [authStage_pass [] h allowCtx allowCtx_notExcluded hr, pipeline_empty, build_ofResponse]

/-- **An excluded path bypasses the gate** — even were the auth status denying. -/
theorem authStage_excluded_skips (h : Ctx → Response) :
    (runPipeline [authStage] h healthCtx).build = h healthCtx := by
  have hex : excluded healthCtx.req = true := by decide
  rw [pipeline_stage_effect authStage [] h healthCtx healthCtx
        (authStage_onReq_excluded healthCtx hex)]
  show (runPipeline [] h healthCtx).build = h healthCtx
  rw [pipeline_empty, build_ofResponse]

/-- **The gate genuinely drives the wire.** Same handler, a denied and an allowed
request emit different status bytes: the denied one is forced to `401`, the allowed
one keeps the handler's status. -/
theorem authStage_changes_bytes (body : Bytes) :
    ((runPipeline [authStage] (fun _ => Reactor.ok200 body) denyCtx).build).status = 401
    ∧ ((runPipeline [authStage] (fun _ => Reactor.ok200 body) allowCtx).build).status = 200 := by
  refine ⟨authStage_denies_401 [] _ (by intro t ht; exact absurd ht (List.not_mem_nil)), ?_⟩
  rw [authStage_allows]; rfl

/-! ## Axiom audit -/

#print axioms decide_allow_200
#print axioms decide_deny_401
#print axioms decide_deny_403
#print axioms decide_error_302
#print axioms authStage_gate_build
#print axioms authStage_denies_401
#print axioms authStage_denies_403
#print axioms authStage_error_500
#print axioms authStage_allows
#print axioms authStage_excluded_skips
#print axioms authStage_changes_bytes

end Reactor.Stage.AuthRequest
