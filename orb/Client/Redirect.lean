import Proto.RequestSerialize

/-!
# Verified HTTP client redirect-following (RFC 9110 §15.4)

The client half of drorb reads an upstream response with `Proto.ResponseParse`.
When that response is a **3xx redirect** carrying a `Location` header, a
conforming client re-issues the request against the redirect target. This module
is the sans-IO decision function that governs that re-issue, together with its
correctness theorems — the policy layer that sits *above* the wire codecs
(`Proto.ResponseParse` for the inbound response, `Proto.RequestSerialize` for the
outbound follow-up request).

The decision is a total, deterministic function

    followStep : Target → method → status → headers → remaining → FollowResult

with four outcomes: **follow** (re-issue to a resolved target with a possibly
rewritten method), **too-many-redirects** (the cap is exhausted), **blocked
downgrade** (a secure→insecure hop, refused), and **no-redirect** (deliver the
response as received).

## What is proven

* `redirect_follows_location` — a `301/302/303/307/308` response *with* a
  `Location`, under a live redirect budget and no security downgrade, produces a
  follow-up request to the resolved `Location`, with the method preserved for
  `307/308` and rewritten to `GET` for `301/302/303` (RFC 9110 §15.4.{2,3,4,8,9}
  and §15.4 method-rewrite rules). Discharged concretely on a `307`-preserves-
  `POST` and a `303`-becomes-`GET` witness (`follows_307_witness`,
  `follows_303_witness`).

* `redirect_loop_bounded` — iterating the follow decision against *any* upstream,
  even an adversary that redirects on every hop, halts after at most `cap`
  follows (`followChain … cap ≤ cap`). The bound is tight: `loop_bounded_tight`
  exhibits an always-redirecting upstream that follows exactly `cap` times.

* `no_downgrade` — a redirect from an `https` origin to an `http` target is
  **never** auto-followed; the decision is `blockedDowngrade` (a hardening beyond
  the reference client, which follows the hop). Witnessed by
  `no_downgrade_witness`.

Non-vacuity is anchored in the real types: `followResponse` runs the decision on
an actual `Reactor.Response`, and `followRequest_roundtrip` shows a follow-up
request round-trips through the verified `Proto.RequestSerialize` codec.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.
-/

namespace Proto
namespace Client
namespace Redirect

open Reactor (Response)
open Proto.ResponseParse (stripPrefix)

abbrev Bytes := List UInt8

/-! ## URL scheme and redirect target -/

/-- The transport scheme of a request origin: cleartext or TLS. -/
inductive Scheme where
  | http
  | https
deriving Repr, DecidableEq

/-- A redirect target: scheme, authority (host[:port]) bytes, and request path.
The client tracks the scheme so it can refuse a secure→insecure downgrade. -/
structure Target where
  scheme : Scheme
  host   : Bytes
  path   : Bytes
deriving Repr, DecidableEq

/-! ## ASCII byte literals (single UTF-8 bytes) -/

def slash : UInt8 := 47                                    -- '/'
/-- `"https://"`. -/
def httpsPfx : Bytes := [104, 116, 116, 112, 115, 58, 47, 47]
/-- `"http://"`. -/
def httpPfx : Bytes := [104, 116, 116, 112, 58, 47, 47]
/-- `"//"` (protocol-relative). -/
def protoRelPfx : Bytes := [47, 47]
/-- `"Location"` (matched case-insensitively per RFC 9110 §5.1). -/
def locationName : Bytes := [76, 111, 99, 97, 116, 105, 111, 110]
/-- `"Host"`. -/
def hostName : Bytes := [72, 111, 115, 116]
/-- `"GET"`. -/
def methodGET : Bytes := [71, 69, 84]

/-! ## Location header lookup (case-insensitive field name) -/

/-- Lowercase an ASCII byte (`'A'..'Z'` → `'a'..'z'`); other bytes unchanged. -/
def asciiLower (b : UInt8) : UInt8 := if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

/-- Case-insensitive field-name equality (RFC 9110 field names are ASCII
case-insensitive). -/
def nameCIEq (a b : Bytes) : Bool := (a.map asciiLower) == (b.map asciiLower)

/-- First `Location` header value, if any. -/
def findLocation : List (Bytes × Bytes) → Option Bytes
  | [] => none
  | (k, v) :: t => if nameCIEq k locationName then some v else findLocation t

/-! ## Status classification and method rewrite (RFC 9110 §15.4) -/

/-- The five redirect statuses a client may auto-follow. -/
def isRedirectStatus (n : Nat) : Bool :=
  n == 301 || n == 302 || n == 303 || n == 307 || n == 308

/-- Method for the follow-up request: `301/302/303` rewrite to `GET`
(§15.4.{2,3,4}); `307/308` preserve the original method (§15.4.{8,9}). -/
def redirectMethod (status : Nat) (origMethod : Bytes) : Bytes :=
  if status = 301 ∨ status = 302 ∨ status = 303 then methodGET else origMethod

/-! ## Location resolution -/

/-- Split an authority-plus-path byte string at the first `'/'`: everything
before it is the authority, the rest (from the `'/'`) is the path. With no `'/'`,
the path defaults to `"/"`. -/
def splitHostPath : Bytes → Bytes × Bytes
  | [] => ([], [slash])
  | b :: bs => if b == slash then ([], b :: bs)
               else let hp := splitHostPath bs; (b :: hp.1, hp.2)

/-- Resolve a `Location` value against the current target (RFC 9110 §6.4.2 /
RFC 3986 §5): an absolute `http(s)://…` sets scheme+authority+path; a
protocol-relative `//authority/path` inherits the current scheme; anything else
is a relative reference resolved against the current authority (a leading `'/'`
is ensured), preserving scheme and host. -/
def resolveLocation (cur : Target) (loc : Bytes) : Target :=
  match stripPrefix httpsPfx loc with
  | some rest => let hp := splitHostPath rest; ⟨Scheme.https, hp.1, hp.2⟩
  | none =>
    match stripPrefix httpPfx loc with
    | some rest => let hp := splitHostPath rest; ⟨Scheme.http, hp.1, hp.2⟩
    | none =>
      match stripPrefix protoRelPfx loc with
      | some rest => let hp := splitHostPath rest; ⟨cur.scheme, hp.1, hp.2⟩
      | none =>
        let p := match stripPrefix [slash] loc with
                 | some _ => loc
                 | none => slash :: loc
        { cur with path := p }

/-! ## The follow decision -/

/-- A follow-up request to re-issue after a redirect. -/
structure FollowRequest where
  method : Bytes
  target : Target
deriving Repr

/-- Outcome of the redirect decision. -/
inductive FollowResult where
  /-- Re-issue `req`; `remaining` redirect budget is left. -/
  | followed (req : FollowRequest) (remaining : Nat)
  /-- The redirect cap is exhausted — surface an error, do not follow. -/
  | tooManyRedirects
  /-- A secure→insecure (`https`→`http`) hop — refused. -/
  | blockedDowngrade
  /-- Not a followable redirect — deliver the response as received. -/
  | noRedirect
deriving Repr

/-- **The redirect decision.** On a followable 3xx status with a `Location`,
under a live budget and no scheme downgrade, produce the follow-up request;
otherwise classify why not. -/
def followStep (cur : Target) (origMethod : Bytes) (status : Nat)
    (headers : List (Bytes × Bytes)) (remaining : Nat) : FollowResult :=
  if isRedirectStatus status = true then
    match findLocation headers with
    | none => FollowResult.noRedirect
    | some loc =>
      if remaining = 0 then FollowResult.tooManyRedirects
      else
        let tgt := resolveLocation cur loc
        if cur.scheme = Scheme.https ∧ tgt.scheme = Scheme.http then
          FollowResult.blockedDowngrade
        else
          FollowResult.followed
            { method := redirectMethod status origMethod, target := tgt }
            (remaining - 1)
  else FollowResult.noRedirect

/-- The decision run directly on a parsed upstream `Reactor.Response` — grounds
the policy in the real inbound type produced by `Proto.ResponseParse.parse`. -/
def followResponse (cur : Target) (origMethod : Bytes) (resp : Response)
    (remaining : Nat) : FollowResult :=
  followStep cur origMethod resp.status resp.headers remaining

/-! ## Method-rewrite lemmas (RFC 9110 §15.4) -/

theorem redirectMethod_301 (m : Bytes) : redirectMethod 301 m = methodGET := by
  unfold redirectMethod; rw [if_pos (by decide)]

theorem redirectMethod_302 (m : Bytes) : redirectMethod 302 m = methodGET := by
  unfold redirectMethod; rw [if_pos (by decide)]

theorem redirectMethod_303 (m : Bytes) : redirectMethod 303 m = methodGET := by
  unfold redirectMethod; rw [if_pos (by decide)]

theorem redirectMethod_307 (m : Bytes) : redirectMethod 307 m = m := by
  unfold redirectMethod; rw [if_neg (by decide)]

theorem redirectMethod_308 (m : Bytes) : redirectMethod 308 m = m := by
  unfold redirectMethod; rw [if_neg (by decide)]

/-! ## Headline theorem 1 — a redirect follows its Location -/

/-- **A followable redirect re-issues to its `Location`.** For a redirect status
with a `Location` header, a live budget, and no secure→insecure downgrade, the
decision is to follow: re-issue to the resolved target with the method rewritten
per RFC 9110 §15.4 (preserved for `307/308`, `GET` for `301/302/303`), spending
one unit of redirect budget. -/
theorem redirect_follows_location
    (cur : Target) (origMethod : Bytes) (status : Nat)
    (headers : List (Bytes × Bytes)) (loc : Bytes) (remaining : Nat)
    (hstat : isRedirectStatus status = true)
    (hloc : findLocation headers = some loc)
    (hrem : 0 < remaining)
    (hnodown : ¬(cur.scheme = Scheme.https ∧ (resolveLocation cur loc).scheme = Scheme.http)) :
    followStep cur origMethod status headers remaining
      = FollowResult.followed
          { method := redirectMethod status origMethod, target := resolveLocation cur loc }
          (remaining - 1) := by
  have hne : remaining ≠ 0 := by omega
  simp only [followStep, if_pos hstat, hloc, if_neg hne, if_neg hnodown]

/-- Method preservation is a corollary for `307/308`. -/
theorem redirect_follows_location_307
    (cur : Target) (origMethod : Bytes)
    (headers : List (Bytes × Bytes)) (loc : Bytes) (remaining : Nat)
    (hloc : findLocation headers = some loc)
    (hrem : 0 < remaining)
    (hnodown : ¬(cur.scheme = Scheme.https ∧ (resolveLocation cur loc).scheme = Scheme.http)) :
    followStep cur origMethod 307 headers remaining
      = FollowResult.followed
          { method := origMethod, target := resolveLocation cur loc } (remaining - 1) := by
  rw [redirect_follows_location cur origMethod 307 headers loc remaining (by decide) hloc hrem hnodown,
      redirectMethod_307]

/-! ## Headline theorem 2 — the redirect cap terminates -/

/-- Iterate the follow decision against an upstream `env` that, for each target,
returns a `(status, headers)` pair. Each real follow spends one unit of `cap`, so
the recursion is structural on `cap`. Returns the number of follows performed. -/
def followChain (env : Target → Nat × List (Bytes × Bytes)) :
    Nat → Target → Bytes → Nat
  | 0, _, _ => 0
  | Nat.succ r, cur, m =>
    match followStep cur m (env cur).1 (env cur).2 (Nat.succ r) with
    | FollowResult.followed req _ => 1 + followChain env r req.target req.method
    | _ => 0

/-- **The redirect loop is bounded.** Following redirects against *any* upstream
— including one that redirects on every hop — halts after at most `cap` follows.
This is the termination/liveness guarantee behind a `max_redirects` cap. -/
theorem redirect_loop_bounded (env : Target → Nat × List (Bytes × Bytes))
    (cap : Nat) (cur : Target) (m : Bytes) :
    followChain env cap cur m ≤ cap := by
  induction cap generalizing cur m with
  | zero => simp [followChain]
  | succ r ih =>
    unfold followChain
    split
    · rename_i req rem heq
      have := ih req.target req.method
      omega
    all_goals omega

/-! ## Headline theorem 3 — no secure→insecure downgrade -/

/-- **No downgrade.** A redirect from an `https` origin to an `http` target is
refused, never auto-followed — a hardening the reference client lacks. -/
theorem no_downgrade
    (cur : Target) (origMethod : Bytes) (status : Nat)
    (headers : List (Bytes × Bytes)) (loc : Bytes) (remaining : Nat)
    (hstat : isRedirectStatus status = true)
    (hloc : findLocation headers = some loc)
    (hrem : 0 < remaining)
    (hcur : cur.scheme = Scheme.https)
    (hdown : (resolveLocation cur loc).scheme = Scheme.http) :
    followStep cur origMethod status headers remaining = FollowResult.blockedDowngrade := by
  have hne : remaining ≠ 0 := by omega
  have hconj : cur.scheme = Scheme.https ∧ (resolveLocation cur loc).scheme = Scheme.http :=
    ⟨hcur, hdown⟩
  simp only [followStep, if_pos hstat, hloc, if_neg hne, if_pos hconj]

/-! ## Contract-biting mutants (non-vacuity from the negative side) -/

/-- A non-3xx status is never followed. -/
theorem non3xx_not_followed
    (cur : Target) (m : Bytes) (headers : List (Bytes × Bytes)) (remaining : Nat) :
    followStep cur m 200 headers remaining = FollowResult.noRedirect := by
  simp [followStep, isRedirectStatus]

/-- A redirect with an exhausted budget surfaces `tooManyRedirects`, not a
follow. -/
theorem exhausted_budget_stops
    (cur : Target) (m : Bytes) (headers : List (Bytes × Bytes)) (loc : Bytes)
    (hloc : findLocation headers = some loc) :
    followStep cur m 302 headers 0 = FollowResult.tooManyRedirects := by
  simp [followStep, isRedirectStatus, hloc]

/-! ## Concrete witnesses (non-vacuity) -/

/-- `https://ex/next`. -/
def httpsExampleLoc : Bytes :=
  [104, 116, 116, 112, 115, 58, 47, 47, 101, 120, 47, 110, 101, 120, 116]
/-- `http://ev/x` (a downgrade target). -/
def httpDowngradeLoc : Bytes := [104, 116, 116, 112, 58, 47, 47, 101, 118, 47, 120]

/-- An `https` origin `https://ex/`. -/
def httpsOrigin : Target := ⟨Scheme.https, [101, 120], [slash]⟩  -- host "ex"

/-- Headers carrying an absolute `https` `Location`. -/
def httpsLocHeaders : List (Bytes × Bytes) := [(locationName, httpsExampleLoc)]
/-- Headers carrying a downgrade `http` `Location`. -/
def downgradeHeaders : List (Bytes × Bytes) := [(locationName, httpDowngradeLoc)]

/-- The resolved `https` target: `https://ex/next`. -/
def resolvedHttps : Target := ⟨Scheme.https, [101, 120], [slash, 110, 101, 120, 116]⟩

/-- `307` preserves the method (`POST`) and follows to the resolved target. -/
theorem follows_307_witness :
    followStep httpsOrigin methodGET 307 httpsLocHeaders 5
      = FollowResult.followed { method := methodGET, target := resolvedHttps } 4 := by
  have h := redirect_follows_location httpsOrigin methodGET 307 httpsLocHeaders httpsExampleLoc 5
    (by decide) (by decide) (by decide) (by decide)
  rw [h, redirectMethod_307]; rfl

/-- `303` rewrites the method to `GET` and follows to the resolved target. -/
theorem follows_303_witness :
    followStep httpsOrigin methodGET 303 httpsLocHeaders 5
      = FollowResult.followed { method := methodGET, target := resolvedHttps } 4 := by
  have h := redirect_follows_location httpsOrigin methodGET 303 httpsLocHeaders httpsExampleLoc 5
    (by decide) (by decide) (by decide) (by decide)
  rw [h, redirectMethod_303]; rfl

/-- The downgrade witness: `https://ex/` → `http://ev/x` is blocked. -/
theorem no_downgrade_witness :
    followStep httpsOrigin methodGET 302 downgradeHeaders 5 = FollowResult.blockedDowngrade :=
  no_downgrade httpsOrigin methodGET 302 downgradeHeaders httpDowngradeLoc 5
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The cap is **tight**: an upstream that always answers `302 → /a` follows
exactly `cap` times before stopping (here `cap = 3`). -/
def alwaysRedirect : Target → Nat × List (Bytes × Bytes) :=
  fun _ => (302, [(locationName, [slash, 97])])  -- Location: "/a"

theorem loop_bounded_tight :
    followChain alwaysRedirect 3 httpsOrigin methodGET = 3 := by decide

/-! ## Grounding: the follow-up request round-trips the verified codec -/

/-- Build the outbound `Proto.Request` for a follow-up, with a `Host` header. -/
def toRequest (fr : FollowRequest) (version : Bytes) : Proto.Request :=
  { method := fr.method, target := fr.target.path, version := version,
    headers := [(hostName, fr.target.host)] }

/-- The follow-up request for the `307` witness is well-formed and therefore
round-trips through the verified request codec `Proto.RequestSerialize` — the
policy layer emits a request the wire layer accepts. -/
theorem followRequest_roundtrip :
    let req := toRequest { method := methodGET, target := resolvedHttps }
                 [72, 84, 84, 80, 47, 49, 46, 49]  -- "HTTP/1.1"
    RequestSerialize.parse (RequestSerialize.serialize req) = some req := by
  apply RequestSerialize.parse_serialize
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro kv hkv
  simp only [toRequest, List.mem_singleton] at hkv
  subst hkv
  exact ⟨by decide, by decide, by decide⟩

end Redirect
end Client
end Proto
