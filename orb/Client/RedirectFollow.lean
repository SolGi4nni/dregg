import Client.Fetch

/-!
# `Client.RedirectFollow` — the deployed redirect-follow policy, proven (LEDGER cl.4)

The deployed `fetch-client` (`Client.FetchMain`, `lean_exe fetch-client`) drives a
real outbound HTTP/1.1 fetch over sockets. Its `--recv` mode parses the upstream
response with the verified `Proto.ResponseParse.parse` and then calls exactly one
decision function to decide whether/where to follow a redirect:

    Client.Redirect.followStep cur method status headers remaining

and prints `FOLLOW <scheme> <host> <path> <method>` / `DELIVER` /
`DECISION=blocked-downgrade` / `DECISION=too-many-redirects` off its result. The
in-process `--demo` mode runs the composed `Client.Fetch.fetchLoop`, which threads
`followStep` under a redirect budget.

This module proves the three redirect-follow guarantees the deployed client relies
on, stated over the *same* `followStep` / `fetchLoop` the exe calls, so the wire
behavior a `--recv`/`--demo` run exhibits is the behavior proven here:

* `redirect_follows_3xx` — a `301/302/303/307/308` response carrying a `Location`,
  under a live redirect budget and no secure→insecure downgrade, is followed to
  the resolved `Location`; the request method is **preserved** for `307/308` and
  **rewritten to `GET`** for `301/302/303` (RFC 9110 §15.4). Concrete byte-level
  witnesses (`follows_307_post`, `follows_303_get`, `live_follow_witness`) match
  the exact `FOLLOW …` line the exe prints.

* `redirect_loop_bounded` — following redirects against *any* upstream, even one
  that redirects on every hop, halts after at most `cap` follows; the deployed
  `fetchLoop` emits at most `fuel + 1` requests (`fetch_chain_bounded`). No
  infinite follow.

* `redirect_no_downgrade` — a redirect from an `https` origin to an `http` target
  is never auto-followed; the decision is `blockedDowngrade`
  (`live_downgrade_witness` matches the exe's `DECISION=blocked-downgrade`).

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`. Every hypothesis is
a real precondition (a redirect status, a present `Location`, a live budget); the
witnesses discharge them on concrete bytes by `decide`, so nothing is vacuous.
-/

namespace Proto
namespace Client
namespace RedirectFollow

open Reactor (Response)
open Proto.Client.Redirect (Target Scheme FollowRequest FollowResult followStep
  followResponse resolveLocation findLocation isRedirectStatus redirectMethod
  redirect_follows_location no_downgrade followChain locationName methodGET slash)
open Proto.Client.Fetch (fetchLoop fetch_redirect_terminates)

abbrev Bytes := List UInt8

/-! ## Theorem 1 — a 3xx with a `Location` is followed (method rewritten per RFC 9110 §15.4) -/

/-- **`redirect_follows_3xx`.** For any of the five auto-followable statuses with a
`Location`, a live budget, and no secure→insecure downgrade, `followStep` — the
decision the deployed `fetch-client --recv` runs — follows to `resolveLocation cur
loc`, spending one unit of budget, with the method preserved for `307/308` and
rewritten to `GET` for `301/302/303`. -/
theorem redirect_follows_3xx
    (cur : Target) (m : Bytes) (status : Nat)
    (headers : List (Bytes × Bytes)) (loc : Bytes) (remaining : Nat)
    (h3xx : status = 301 ∨ status = 302 ∨ status = 303 ∨ status = 307 ∨ status = 308)
    (hloc : findLocation headers = some loc)
    (hrem : 0 < remaining)
    (hnodown : ¬(cur.scheme = Scheme.https ∧ (resolveLocation cur loc).scheme = Scheme.http)) :
    followStep cur m status headers remaining
      = FollowResult.followed
          { method := (if status = 301 ∨ status = 302 ∨ status = 303 then methodGET else m),
            target := resolveLocation cur loc }
          (remaining - 1) := by
  have hstat : isRedirectStatus status = true := by
    rcases h3xx with h | h | h | h | h <;> subst h <;> decide
  have hfollow := redirect_follows_location cur m status headers loc remaining hstat hloc hrem hnodown
  simpa [redirectMethod] using hfollow

/-- `307` **preserves** the request method (RFC 9110 §15.4.8): a `POST` stays a
`POST` on the follow-up. -/
theorem redirect_307_preserves_method
    (cur : Target) (m : Bytes) (headers : List (Bytes × Bytes)) (loc : Bytes) (remaining : Nat)
    (hloc : findLocation headers = some loc) (hrem : 0 < remaining)
    (hnodown : ¬(cur.scheme = Scheme.https ∧ (resolveLocation cur loc).scheme = Scheme.http)) :
    followStep cur m 307 headers remaining
      = FollowResult.followed { method := m, target := resolveLocation cur loc } (remaining - 1) := by
  have h := redirect_follows_location cur m 307 headers loc remaining (by decide) hloc hrem hnodown
  rwa [Redirect.redirectMethod_307] at h

/-- `303` **rewrites** the request method to `GET` (RFC 9110 §15.4.4). -/
theorem redirect_303_becomes_get
    (cur : Target) (m : Bytes) (headers : List (Bytes × Bytes)) (loc : Bytes) (remaining : Nat)
    (hloc : findLocation headers = some loc) (hrem : 0 < remaining)
    (hnodown : ¬(cur.scheme = Scheme.https ∧ (resolveLocation cur loc).scheme = Scheme.http)) :
    followStep cur m 303 headers remaining
      = FollowResult.followed { method := methodGET, target := resolveLocation cur loc } (remaining - 1) := by
  have h := redirect_follows_location cur m 303 headers loc remaining (by decide) hloc hrem hnodown
  rwa [Redirect.redirectMethod_303] at h

/-! ## Theorem 2 — the redirect chain is bounded (no infinite follow) -/

/-- **`redirect_loop_bounded`.** Iterating the follow decision against *any*
upstream `env` — including an adversary that returns a redirect on every hop —
performs at most `cap` follows. This is the termination guarantee behind the
client's `max_redirects` cap; the proof is a structural induction on the budget,
each real follow spending one unit. -/
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

/-- The deployed loop analogue: `Client.Fetch.fetchLoop` — the `--demo` transaction
— emits at most `fuel + 1` requests, so a fetch under budget `fuel` never issues an
unbounded chain of requests. -/
theorem fetch_chain_bounded
    (up : Proto.Client.Fetch.Upstream) (setC : Response → List Client.Session.Cookie)
    (reqOf : Target → Client.Session.Req) (fuel : Nat) (jar : List Client.Session.Cookie)
    (cur : Target) (m : Bytes) :
    (fetchLoop up setC reqOf fuel jar cur m).emitted.length ≤ fuel + 1 :=
  fetch_redirect_terminates up setC reqOf fuel jar cur m

/-! ## Theorem 3 — no silent https→http downgrade -/

/-- **`redirect_no_downgrade`.** A redirect from an `https` origin to an `http`
target is refused — `followStep` returns `blockedDowngrade`, never a follow. This
is the decision the deployed `fetch-client --recv` surfaces as
`DECISION=blocked-downgrade`. -/
theorem redirect_no_downgrade
    (cur : Target) (m : Bytes) (status : Nat)
    (headers : List (Bytes × Bytes)) (loc : Bytes) (remaining : Nat)
    (h3xx : status = 301 ∨ status = 302 ∨ status = 303 ∨ status = 307 ∨ status = 308)
    (hloc : findLocation headers = some loc)
    (hrem : 0 < remaining)
    (hcur : cur.scheme = Scheme.https)
    (hdown : (resolveLocation cur loc).scheme = Scheme.http) :
    followStep cur m status headers remaining = FollowResult.blockedDowngrade := by
  have hstat : isRedirectStatus status = true := by
    rcases h3xx with h | h | h | h | h <;> subst h <;> decide
  exact no_downgrade cur m status headers loc remaining hstat hloc hrem hcur hdown

/-! ## Concrete witnesses — the exact wire the deployed `fetch-client` exhibits

Each witness is a fully concrete `followStep`/`followResponse` on real bytes,
matching the line `Client.FetchMain` prints on that input. The live run
(`--recv …` piped from a redirecting server) re-exhibits exactly these. -/

section Witnesses

/-- `"127.0.0.1"`. -/
def loopbackHost : Bytes := [49, 50, 55, 46, 48, 46, 48, 46, 49]
/-- `"/"`. -/
def rootPath : Bytes := [slash]
/-- `"/next"` — a relative `Location`. -/
def nextLoc : Bytes := [47, 110, 101, 120, 116]
/-- `"POST"`. -/
def methodPOST : Bytes := [80, 79, 83, 84]

/-- Headers carrying `Location: /next` (the relative form the live server sends). -/
def relNextHeaders : List (Bytes × Bytes) := [(locationName, nextLoc)]

/-- The `http://127.0.0.1/` origin the live driver dials. -/
def loopbackOrigin : Target := ⟨Scheme.http, loopbackHost, rootPath⟩
/-- The resolved follow-up target `http://127.0.0.1/next`. -/
def loopbackNext : Target := ⟨Scheme.http, loopbackHost, nextLoc⟩

/-- **The live follow witness.** `302` + `Location: /next` on the `http://127.0.0.1/`
origin, GET, budget 10 → `FOLLOW http 127.0.0.1 /next GET` — the exact line the
deployed `fetch-client --recv http 127.0.0.1 / GET` prints against the redirecting
server. -/
theorem live_follow_witness :
    followStep loopbackOrigin methodGET 302 relNextHeaders 10
      = FollowResult.followed { method := methodGET, target := loopbackNext } 9 := by
  have hres : resolveLocation loopbackOrigin nextLoc = loopbackNext := by decide
  have h := redirect_follows_location loopbackOrigin methodGET 302 relNextHeaders nextLoc 10
    (by decide) (by decide) (by decide) (by decide)
  rw [Redirect.redirectMethod_302, hres] at h
  exact h

/-- `307` preserves `POST` on a concrete redirect (RFC 9110 §15.4.8). -/
theorem follows_307_post :
    followStep loopbackOrigin methodPOST 307 relNextHeaders 10
      = FollowResult.followed { method := methodPOST, target := loopbackNext } 9 := by
  have hres : resolveLocation loopbackOrigin nextLoc = loopbackNext := by decide
  have h := redirect_307_preserves_method loopbackOrigin methodPOST relNextHeaders nextLoc 10
    (by decide) (by decide) (by decide)
  rw [hres] at h
  exact h

/-- `303` rewrites `POST` to `GET` on a concrete redirect (RFC 9110 §15.4.4). -/
theorem follows_303_get :
    followStep loopbackOrigin methodPOST 303 relNextHeaders 10
      = FollowResult.followed { method := methodGET, target := loopbackNext } 9 := by
  have hres : resolveLocation loopbackOrigin nextLoc = loopbackNext := by decide
  have h := redirect_303_becomes_get loopbackOrigin methodPOST relNextHeaders nextLoc 10
    (by decide) (by decide) (by decide)
  rw [hres] at h
  exact h

/-- `"http://evil/x"` — an absolute `http` downgrade `Location`. -/
def httpDowngradeLoc : Bytes := [104, 116, 116, 112, 58, 47, 47, 101, 118, 105, 108, 47, 120]
/-- Headers carrying the downgrade `Location`. -/
def downgradeHeaders : List (Bytes × Bytes) := [(locationName, httpDowngradeLoc)]
/-- An `https://127.0.0.1/` origin. -/
def httpsOrigin : Target := ⟨Scheme.https, loopbackHost, rootPath⟩

/-- **The live downgrade witness.** `302` + `Location: http://evil/x` on an `https`
origin, budget 10 → `blockedDowngrade` — the exact `DECISION=blocked-downgrade` the
deployed `fetch-client --recv https 127.0.0.1 / GET` prints. -/
theorem live_downgrade_witness :
    followStep httpsOrigin methodGET 302 downgradeHeaders 10 = FollowResult.blockedDowngrade :=
  redirect_no_downgrade httpsOrigin methodGET 302 downgradeHeaders httpDowngradeLoc 10
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A non-3xx status is delivered, never followed — the `DELIVER` line (the second
hop of the live run, `200 OK` on `/next`). -/
theorem delivers_200 :
    followStep loopbackNext methodGET 200 [] 10 = FollowResult.noRedirect :=
  Redirect.non3xx_not_followed loopbackNext methodGET [] 10

/-- The tight-loop witness: an always-`302`→`/a` upstream follows exactly `cap`
times (`cap = 4`) before stopping — the bound of `redirect_loop_bounded` is
attained, not merely an over-estimate. -/
def alwaysRedirect : Target → Nat × List (Bytes × Bytes) :=
  fun _ => (302, [(locationName, [slash, 97])])   -- Location: "/a"

theorem loop_bound_tight :
    followChain alwaysRedirect 4 loopbackOrigin methodGET = 4 := by decide

end Witnesses

end RedirectFollow
end Client
end Proto
