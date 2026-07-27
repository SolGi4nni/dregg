import Reactor.Pipeline

/-!
# Reactor.Stage.ForwardAuth — forward-auth / subrequest auth ROUNDTRIP

`Reactor.Stage.AuthRequest` gates on a bare auth *status* stashed in the context.
This stage models the full **forward-auth roundtrip**: the auth service answers the
subrequest with a whole *response* (a status AND a header set), and on success the
configured subset of those auth-response headers is *copied upstream* — appended to
the request the handler will see. This is the nginx `auth_request` + `auth_request_set`
/ Traefik `authResponseHeaders` pattern: the auth service does not merely say yes/no,
it enriches the request with identity claims (`x-auth-user`, `x-auth-role`, …) that
downstream handlers read.

## The roundtrip decision

`evaluate cfg auth` maps the subrequest outcome to an `AuthResult`:

* **service failure** (`none` — unreachable / timeout) — fail closed: `failClosed`;
* **2xx** — allow, carrying `collectHeaders` of the auth response (the configured
  header names, filtered out of the auth response's headers);
* **401** — `deny 401`; **403** — `deny 403`;
* **any other status** — the auth service misbehaved — fail closed.

Fail-closed is the DEFAULT (`none` and every unexpected status route to it): a
forward-auth gate must never fail open.

## Header copying is a WHITELIST (the security-load-bearing part)

`collectHeaders names hs` keeps exactly the auth-response headers whose name is in the
configured `names` list. A header the auth service returns that is NOT configured is
NOT copied upstream (`forward_auth_no_smuggle`) — the auth service cannot inject
arbitrary headers into the upstream request, only the ones the operator whitelisted.

## What is proven (headline)

* `forward_auth_allows` — a 2xx auth response makes the stage `.continue` with the
  request whose headers are the original ones followed by the copied auth headers;
  `forward_auth_forwards` puts that augmented request in front of the real handler in
  the pipeline; `forward_auth_copies` — a configured header present in the auth
  response reaches the handler's request.
* `forward_auth_denies` — a 401/403 auth response makes the stage `.respond` the
  matching refusal (status = the auth status), the handler is skipped
  (`forward_auth_denies_skips_handler`), and the status survives the response onion
  (`forward_auth_denies_status`).
* `forward_auth_fail_closed` — a service failure (`none`) or any unexpected status
  makes the stage `.respond` a `500`, denied and status-preserved
  (`forward_auth_fail_closed_status`).

Non-vacuity: `forward_auth_roundtrip_table` walks every branch on distinct inputs;
`forward_auth_copies` / `forward_auth_no_smuggle` show a whitelisted header IS copied
and a non-whitelisted one is NOT; `forward_auth_changes_bytes` shows allow and deny
drive different status bytes onto the wire.
-/

namespace Reactor.Stage.ForwardAuth

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## The auth subrequest response and the config -/

/-- The auth service's answer to the subrequest: a status code and the headers it
returned (the source of the claims copied upstream on success). -/
structure AuthResponse where
  status  : Nat
  headers : List (Bytes × Bytes) := []
deriving Repr

/-- Forward-auth configuration. `respHeaders` is the WHITELIST of auth-response header
names copied upstream on a 2xx; `excludePrefixes` are request-target prefixes that
bypass auth entirely (health probes, public assets). -/
structure Config where
  /-- Header names copied from the auth response to the upstream request on allow. -/
  respHeaders     : List Bytes := []
  /-- Request-target prefixes that skip auth. -/
  excludePrefixes : List Bytes := []
deriving Repr

/-! ## The refusal responses -/

def denyBody : Bytes := "auth subrequest denied\n".toUTF8.toList
def errBody  : Bytes := "auth subrequest failed\n".toUTF8.toList

/-- The reason phrase for a denying status. -/
def reasonOf : Nat → Bytes
  | 401 => "Unauthorized".toUTF8.toList
  | 403 => "Forbidden".toUTF8.toList
  | _   => "Forbidden".toUTF8.toList

/-- The refusal a `deny status` serves — status carried through by `error4xx`. -/
def denyResp (status : Nat) : Response := error4xx status (reasonOf status) denyBody

/-- `500 Internal Server Error` — the fail-closed response. -/
def resp500 : Response := error4xx 500 "Internal Server Error".toUTF8.toList errBody

/-! ## Header whitelist copy -/

/-- Copy the whitelisted headers out of the auth response: keep exactly the headers
whose name is one of `names`. Order and multiplicity are the auth response's; a
non-whitelisted header is dropped. -/
def collectHeaders (names : List Bytes) (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  hs.filter (fun nv => names.contains nv.1)

/-- **Whitelist soundness.** Every copied header was in the auth response and is
whitelisted. -/
theorem collect_sound {names : List Bytes} {hs : List (Bytes × Bytes)} {nv : Bytes × Bytes}
    (h : nv ∈ collectHeaders names hs) :
    nv ∈ hs ∧ names.contains nv.1 = true := by
  unfold collectHeaders at h
  rw [List.mem_filter] at h
  exact h

/-- **Whitelist completeness.** A whitelisted header present in the auth response is
copied. -/
theorem collect_complete {names : List Bytes} {hs : List (Bytes × Bytes)} {nv : Bytes × Bytes}
    (hmem : nv ∈ hs) (hwl : names.contains nv.1 = true) :
    nv ∈ collectHeaders names hs := by
  unfold collectHeaders
  rw [List.mem_filter]
  exact ⟨hmem, hwl⟩

/-! ## The decision core -/

/-- The outcome of the forward-auth roundtrip. -/
inductive AuthResult where
  /-- Allow; carry the whitelisted headers copied out of the auth response. -/
  | allow (copied : List (Bytes × Bytes))
  /-- Deny with the auth service's status (401 or 403). -/
  | deny (status : Nat)
  /-- Fail closed with a 500 (service failure or unexpected status). -/
  | failClosed
deriving DecidableEq, Repr

/-- **The roundtrip decision.** No response (service failure) fails closed; a 2xx
allows and copies the whitelisted headers; 401/403 deny with that status; any other
status fails closed. Total. -/
def evaluate (cfg : Config) : Option AuthResponse → AuthResult
  | none => .failClosed
  | some r =>
    if 200 ≤ r.status ∧ r.status ≤ 299 then .allow (collectHeaders cfg.respHeaders r.headers)
    else if r.status = 401 then .deny 401
    else if r.status = 403 then .deny 403
    else .failClosed

/-! ### Decision truth table (non-vacuity) -/

/-- A 2xx allows, carrying the whitelisted headers. -/
theorem evaluate_allow (cfg : Config) {r : AuthResponse}
    (h : 200 ≤ r.status ∧ r.status ≤ 299) :
    evaluate cfg (some r) = .allow (collectHeaders cfg.respHeaders r.headers) := by
  simp [evaluate, h]

/-- A 401 denies with 401. -/
theorem evaluate_deny_401 (cfg : Config) {r : AuthResponse} (h : r.status = 401) :
    evaluate cfg (some r) = .deny 401 := by
  simp [evaluate, h]

/-- A 403 denies with 403. -/
theorem evaluate_deny_403 (cfg : Config) {r : AuthResponse} (h : r.status = 403) :
    evaluate cfg (some r) = .deny 403 := by
  have h2 : ¬ (200 ≤ r.status ∧ r.status ≤ 299) := by rw [h]; omega
  have h1 : r.status ≠ 401 := by rw [h]; decide
  simp [evaluate, h, h2, h1]

/-- A service failure fails closed. -/
theorem evaluate_none (cfg : Config) : evaluate cfg none = .failClosed := rfl

/-- An unexpected status (here 500) fails closed. -/
theorem evaluate_unexpected (cfg : Config) {r : AuthResponse}
    (hlo : ¬ (200 ≤ r.status ∧ r.status ≤ 299)) (h1 : r.status ≠ 401) (h3 : r.status ≠ 403) :
    evaluate cfg (some r) = .failClosed := by
  simp [evaluate, hlo, h1, h3]

/-! ## Exclude-path prefix match -/

/-- `needle` is a prefix of `hay`. -/
def isPrefix : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, h :: hs => n == h && isPrefix ns hs

/-- Whether the request target starts with any configured exclude prefix. -/
def excluded (cfg : Config) (req : Request) : Bool :=
  cfg.excludePrefixes.any (fun p => isPrefix p req.target)

/-! ## The stage -/

/-- The upstream request after copying the whitelisted auth headers. -/
def withCopied (cfg : Config) (r : AuthResponse) (req : Request) : Request :=
  { req with headers := req.headers ++ collectHeaders cfg.respHeaders r.headers }

/-- **The forward-auth gate stage.** `auth` is the subrequest outcome the accept path
supplies (`none` = the auth service failed). Request phase: an excluded target passes;
otherwise apply the roundtrip decision — `allow` `.continue`s with the request carrying
the copied auth headers, `deny s`/`failClosed` `.respond` their refusal (short-circuit,
handler skipped). Response phase: transparent. -/
def forwardAuthStage (cfg : Config) (auth : Option AuthResponse) : Stage where
  name := "forward-auth"
  onRequest := fun c =>
    if excluded cfg c.req then .continue c
    else match evaluate cfg auth with
      | .allow copied => .continue { c with req := { c.req with headers := c.req.headers ++ copied } }
      | .deny s       => .respond (denyResp s)
      | .failClosed   => .respond resp500
  onResponse := fun _ b => b

/-- The gate's `onResponse` is the identity, so it is status-stable (needed to carry
its own refusal status through when it is the OUTER stage — not used below, but it
makes the stage composable in a status-stable onion). -/
theorem forwardAuthStage_statusStable (cfg : Config) (auth : Option AuthResponse) :
    Stage.statusStable (forwardAuthStage cfg auth) := by
  intro c b; rfl

/-! ## Allow: continue with the request enriched by the copied headers -/

/-- **`forward_auth_allows`.** On a non-excluded request with a 2xx auth response, the
stage passes (`.continue`) with the upstream request whose headers are the original
ones followed by the whitelisted auth-response headers — the copy-upstream effect. -/
theorem forward_auth_allows (cfg : Config) (r : AuthResponse) (c : Ctx)
    (hex : excluded cfg c.req = false) (h2xx : 200 ≤ r.status ∧ r.status ≤ 299) :
    (forwardAuthStage cfg (some r)).onRequest c
      = .continue { c with req := withCopied cfg r c.req } := by
  show (if excluded cfg c.req then _ else _) = _
  rw [hex]
  simp only [Bool.false_eq_true, if_false]
  rw [evaluate_allow cfg h2xx]
  rfl

/-- **`forward_auth_forwards`.** The pipeline runs the real handler on the enriched
upstream request (the transparent response phase adds nothing) — the allowed request
is genuinely forwarded, carrying its copied headers, for ANY tail and handler. -/
theorem forward_auth_forwards (cfg : Config) (r : AuthResponse) (c : Ctx)
    (rest : List Stage) (handler : Ctx → Response)
    (hex : excluded cfg c.req = false) (h2xx : 200 ≤ r.status ∧ r.status ≤ 299) :
    runPipeline (forwardAuthStage cfg (some r) :: rest) handler c
      = runPipeline rest handler { c with req := withCopied cfg r c.req } := by
  rw [pipeline_stage_effect (forwardAuthStage cfg (some r)) rest handler c
        { c with req := withCopied cfg r c.req } (forward_auth_allows cfg r c hex h2xx)]
  rfl

/-- **`forward_auth_copies`.** A whitelisted header the auth service returned is present
in the upstream request handed to the handler. The claim copy actually lands. -/
theorem forward_auth_copies (cfg : Config) (r : AuthResponse) (c : Ctx) (nv : Bytes × Bytes)
    (hmem : nv ∈ r.headers) (hwl : cfg.respHeaders.contains nv.1 = true) :
    nv ∈ (withCopied cfg r c.req).headers := by
  unfold withCopied
  simp only [List.mem_append]
  exact Or.inr (collect_complete hmem hwl)

/-! ## Deny: respond the auth status, skip the handler -/

/-- `evaluate` on a 401/403 gives `deny` with exactly that status. -/
theorem evaluate_deny (cfg : Config) {r : AuthResponse} (h : r.status = 401 ∨ r.status = 403) :
    evaluate cfg (some r) = .deny r.status := by
  cases h with
  | inl h => rw [h]; exact evaluate_deny_401 cfg h
  | inr h => rw [h]; exact evaluate_deny_403 cfg h

/-- **`forward_auth_denies`.** On a non-excluded request with a 401/403 auth response,
the stage `.respond`s the matching refusal, whose status is the auth status. -/
theorem forward_auth_denies (cfg : Config) (r : AuthResponse) (c : Ctx)
    (hex : excluded cfg c.req = false) (hdeny : r.status = 401 ∨ r.status = 403) :
    (forwardAuthStage cfg (some r)).onRequest c = .respond (denyResp r.status) := by
  show (if excluded cfg c.req then _ else _) = _
  rw [hex]
  simp only [Bool.false_eq_true, if_false]
  rw [evaluate_deny cfg hdeny]

/-- **`forward_auth_denies_status`.** The refusal keeps the auth status through a
status-stable inner onion — a 401 stays a 401, a 403 stays a 403 on the wire. -/
theorem forward_auth_denies_status (cfg : Config) (r : AuthResponse) (c : Ctx)
    (rest : List Stage) (handler : Ctx → Response)
    (hex : excluded cfg c.req = false) (hdeny : r.status = 401 ∨ r.status = 403)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (forwardAuthStage cfg (some r) :: rest) handler c).build).status = r.status := by
  have := pipeline_gate_status (forwardAuthStage cfg (some r)) rest handler c (denyResp r.status)
    (forward_auth_denies cfg r c hex hdeny) hst
  rw [this]; rfl

/-- **`forward_auth_denies_skips_handler`.** The request is NOT forwarded: swapping the
handler leaves the output unchanged — the handler never runs on a denied request. -/
theorem forward_auth_denies_skips_handler (cfg : Config) (r : AuthResponse) (c : Ctx)
    (rest : List Stage) (handler handler' : Ctx → Response)
    (hex : excluded cfg c.req = false) (hdeny : r.status = 401 ∨ r.status = 403) :
    runPipeline (forwardAuthStage cfg (some r) :: rest) handler c
      = runPipeline (forwardAuthStage cfg (some r) :: rest) handler' c :=
  pipeline_gate_ignores_handler (forwardAuthStage cfg (some r)) rest handler handler' c
    (denyResp r.status) (forward_auth_denies cfg r c hex hdeny)

/-! ## Fail closed: service failure / unexpected status -/

/-- **`forward_auth_fail_closed`.** Whenever the roundtrip evaluates to `failClosed`
(a service failure `none`, or an unexpected status), a non-excluded request is refused
with `500`. -/
theorem forward_auth_fail_closed (cfg : Config) (auth : Option AuthResponse) (c : Ctx)
    (hex : excluded cfg c.req = false) (hfail : evaluate cfg auth = .failClosed) :
    (forwardAuthStage cfg auth).onRequest c = .respond resp500 := by
  show (if excluded cfg c.req then _ else _) = _
  rw [hex]
  simp only [Bool.false_eq_true, if_false]
  rw [hfail]

/-- **`forward_auth_fail_closed_status`.** The fail-closed response is a `500`, kept
through a status-stable onion. -/
theorem forward_auth_fail_closed_status (cfg : Config) (auth : Option AuthResponse) (c : Ctx)
    (rest : List Stage) (handler : Ctx → Response)
    (hex : excluded cfg c.req = false) (hfail : evaluate cfg auth = .failClosed)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (forwardAuthStage cfg auth :: rest) handler c).build).status = 500 := by
  have := pipeline_gate_status (forwardAuthStage cfg auth) rest handler c resp500
    (forward_auth_fail_closed cfg auth c hex hfail) hst
  rw [this]; rfl

/-- A service failure (`none`) fails closed with a 500 — the default posture. -/
theorem forward_auth_service_failure (cfg : Config) (c : Ctx)
    (rest : List Stage) (handler : Ctx → Response)
    (hex : excluded cfg c.req = false) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (forwardAuthStage cfg none :: rest) handler c).build).status = 500 :=
  forward_auth_fail_closed_status cfg none c rest handler hex (evaluate_none cfg) hst

/-! ## Excluded path bypass -/

/-- **An excluded target passes regardless of the auth outcome.** -/
theorem forward_auth_excluded (cfg : Config) (auth : Option AuthResponse) (c : Ctx)
    (hex : excluded cfg c.req = true) :
    (forwardAuthStage cfg auth).onRequest c = .continue c := by
  show (if excluded cfg c.req then _ else _) = _
  rw [hex]; rfl

/-! ## Concrete non-vacuity: whitelist copy vs smuggle -/

/-- Whitelisted header name `u` (single ASCII byte, so proofs reduce in the kernel). -/
def userName   : Bytes := [117]
/-- Its value. -/
def userVal    : Bytes := [65]
/-- A header the auth service returns but the operator did NOT whitelist. -/
def secretName : Bytes := [115]
def secretVal  : Bytes := [66]

/-- Config whitelisting only `userName`. -/
def demoCfg : Config := { respHeaders := [userName], excludePrefixes := [] }

/-- A 2xx auth response returning both a whitelisted and a non-whitelisted header. -/
def okAuth : AuthResponse := { status := 200, headers := [(userName, userVal), (secretName, secretVal)] }

/-- A fresh context with an empty request. -/
def freshCtx : Ctx := { input := [], req := {} }

theorem freshCtx_notExcluded : excluded demoCfg freshCtx.req = false := by decide

/-- **The whitelisted header is copied upstream.** -/
theorem forward_auth_copies_concrete :
    (userName, userVal) ∈ (withCopied demoCfg okAuth freshCtx.req).headers := by
  apply forward_auth_copies demoCfg okAuth freshCtx (userName, userVal)
  · decide
  · decide

/-- **`forward_auth_no_smuggle`.** The NON-whitelisted header the auth service returned
is NOT copied upstream — the auth service cannot inject arbitrary headers into the
request; only whitelisted claims pass. -/
theorem forward_auth_no_smuggle :
    (secretName, secretVal) ∉ collectHeaders demoCfg.respHeaders okAuth.headers := by
  decide

/-- The allowed upstream request contains the whitelisted header and not the smuggled
one — the copy is a genuine whitelist. -/
theorem forward_auth_copy_is_whitelist :
    (userName, userVal) ∈ (withCopied demoCfg okAuth freshCtx.req).headers
    ∧ (secretName, secretVal) ∉ (withCopied demoCfg okAuth freshCtx.req).headers := by
  refine ⟨forward_auth_copies_concrete, ?_⟩
  unfold withCopied
  simp only [List.mem_append]
  intro h
  cases h with
  | inl h => exact absurd h (by decide)
  | inr h => exact forward_auth_no_smuggle h

/-! ## Concrete non-vacuity: allow vs deny drive different bytes -/

/-- A denied (401) auth response. -/
def denyAuth : AuthResponse := { status := 401, headers := [] }

/-- **`forward_auth_changes_bytes`.** Same handler: a denied request is forced to `401`
on the wire; an allowed one runs the handler (status 200). The gate genuinely drives
the response. -/
theorem forward_auth_changes_bytes (body : Bytes) :
    ((runPipeline [forwardAuthStage demoCfg (some denyAuth)]
        (fun _ => Reactor.ok200 body) freshCtx).build).status = 401
    ∧ ((runPipeline [forwardAuthStage demoCfg (some okAuth)]
        (fun _ => Reactor.ok200 body) freshCtx).build).status = 200 := by
  constructor
  · have hd : denyAuth.status = 401 ∨ denyAuth.status = 403 := Or.inl rfl
    have := forward_auth_denies_status demoCfg denyAuth freshCtx [] (fun _ => Reactor.ok200 body)
      freshCtx_notExcluded hd (by intro t ht; exact absurd ht (List.not_mem_nil))
    simpa using this
  · have h2xx : 200 ≤ okAuth.status ∧ okAuth.status ≤ 299 := by decide
    rw [forward_auth_forwards demoCfg okAuth freshCtx [] (fun _ => Reactor.ok200 body)
          freshCtx_notExcluded h2xx]
    rfl

/-! ## The roundtrip truth table (every branch, distinct inputs) -/

/-- **`forward_auth_roundtrip_table`.** The four branches on four distinct inputs:
service failure → failClosed; 2xx → allow (copied headers); 401 → deny 401; 403 →
deny 403; an unexpected 500 → failClosed. Non-vacuous: each input takes a different
branch. -/
theorem forward_auth_roundtrip_table (cfg : Config) :
    evaluate cfg none = .failClosed
    ∧ evaluate cfg (some { status := 204, headers := [] })
        = .allow (collectHeaders cfg.respHeaders [])
    ∧ evaluate cfg (some { status := 401, headers := [] }) = .deny 401
    ∧ evaluate cfg (some { status := 403, headers := [] }) = .deny 403
    ∧ evaluate cfg (some { status := 500, headers := [] }) = .failClosed := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · exact evaluate_allow cfg (by decide)
  · exact evaluate_deny_401 cfg rfl
  · exact evaluate_deny_403 cfg rfl
  · exact evaluate_unexpected cfg (by decide) (by decide) (by decide)

/-! ## Axiom audit -/

#print axioms forward_auth_allows
#print axioms forward_auth_forwards
#print axioms forward_auth_copies
#print axioms forward_auth_denies
#print axioms forward_auth_denies_status
#print axioms forward_auth_denies_skips_handler
#print axioms forward_auth_fail_closed
#print axioms forward_auth_fail_closed_status
#print axioms forward_auth_copy_is_whitelist
#print axioms forward_auth_no_smuggle
#print axioms forward_auth_changes_bytes
#print axioms forward_auth_roundtrip_table

end Reactor.Stage.ForwardAuth
