/-
Client.CookieJar — the full RFC 6265 client cookie STORE, layered on the
sendability matcher of `Client.Session` (§5.1.3 / §5.1.4 / §5.4) and the expiry /
eviction policy of `Client.CookieExpiry` (§5.2 / §5.3). Those two modules proved,
respectively, WHICH stored cookies a request may see and WHEN a stored cookie
stops being sent / HOW the jar stays bounded. What a real client still needs — and
what this module adds — is the STORE side of §5.3: the `Set-Cookie` intake path,
the round-trip guarantee that a cookie you store is a cookie you get back, and the
one storage rule that is a pure security guard rather than an accounting rule:

  * §5.3 step 5, the **public-suffix / "supercookie" rejection**: a `Domain`
    cookie whose domain-attribute is a public suffix (`com`, `co.uk`, …) is
    rejected outright, so no origin can plant a cookie that every site under a
    registry would then send. This is the rule that stops cross-site supercookies;
    it has no analogue in the matcher (a supercookie domain-MATCHES everything —
    the whole point is to never let it into the store in the first place).

The Public Suffix List is external, mutable data (not a mathematical object and
not crypto), so it is modelled as an OPAQUE oracle: the jar carries a predicate
`psl : Labels → Bool` and every theorem is universally quantified over it. The
decision LOGIC around the oracle — accept iff host-only or not-a-public-suffix,
and the fact that this logic keeps supercookies out — is what is proven; the
oracle's contents are never invented.

`Client.Session` and `Client.CookieExpiry` are imported UNMODIFIED: the real
`Cookie`, `Req`, `cookieMatches`, `StoredCookie`, `resolveExpiry`, `reap`,
`enforce`, and the expiry-aware `jarSend` are reused, so the store composes with
the genuine matcher and expiry gate rather than a stand-in.

## The jar

A `Jar` is a public-suffix oracle, a pair of storage caps, and the stored
cookies. `store` is the `Set-Cookie` intake: it resolves the wire expiry against
the clock, applies the public-suffix guard, and (if accepted) inserts the cookie
newest-first. `get` is the outgoing selection at a clock instant: the expiry-aware
`jarSend`, which drops expired cookies and returns only the live matches. `enforced`
is the §5.3 storage-limit GC, reusing the proven `enforce`.

  * `jar_store_get` — a `Set-Cookie` that is accepted, live at `now`, and matches
    the request is retrieved by `get` (store→get round-trip; the matcher's
    domain/path/Secure conditions are exactly what `cookieMatches` decides).
  * `jar_evicts_expired` — a cookie expired at `now` is NEVER returned by `get`,
    for any request (the expiry gate dominates the matcher).
  * `jar_public_suffix` — a `Domain` cookie for a public-suffix domain is rejected:
    `store` leaves the jar unchanged, so `get` can never yield it. No supercookie.
  * `jar_size_bounded` — after `enforced` the jar holds at most `total` cookies and
    at most `perDomain` for any single domain.

Each theorem is accompanied by a concrete witness and, where a guard is the point
(the public-suffix rule, the expiry gate), a mutant that drops the guard and
thereby admits the attack — so none of the theorems are vacuous.
-/
import Client.Session
import Client.CookieExpiry

namespace Client.CookieJar

open Client.Session
open Client.CookieExpiry

/-! ############################################################################
    ## The jar and its operations
    ########################################################################## -/

/-- The client cookie store: an external Public Suffix List oracle `psl`, the
RFC 6265 §5.3 storage caps, and the stored cookies (newest first). The oracle is
abstract data — `psl d = true` means the label sequence `d` is a public suffix
(a registry-controlled domain such as `com` or `co.uk`); its contents are never
assumed, only its type. -/
structure Jar where
  psl : Labels → Bool
  caps : Caps
  cookies : List StoredCookie

/-- Build the stored form of a `Set-Cookie`: the matcher cookie, its expiry
instant resolved against the clock `now` per §5.2, and a creation stamp. -/
def mkStored (now created : Nat) (attr : ExpiryAttr) (c : Cookie) : StoredCookie :=
  { cookie := c, expiry := resolveExpiry now attr, created := created }

/-- RFC 6265 §5.3 step 5 decision (the supercookie guard). A cookie is
domain-acceptable iff it is host-only (no `Domain` attribute, so scoped to the
exact origin and immune by construction) OR its domain-attribute is not a public
suffix. A `Domain` cookie whose domain the oracle flags as a public suffix is
rejected. -/
def Jar.accept (jar : Jar) (c : Cookie) : Bool :=
  c.hostOnly || !jar.psl c.domain

/-- `Set-Cookie` intake. Resolve the wire expiry against `now`; if the domain
guard admits the cookie, insert it newest-first; otherwise leave the jar
untouched (the cookie is ignored, per §5.3 step 5). -/
def Jar.store (jar : Jar) (now created : Nat) (attr : ExpiryAttr) (c : Cookie) : Jar :=
  if jar.accept c then
    { jar with cookies := mkStored now created attr c :: jar.cookies }
  else jar

/-- Outgoing selection at clock `now`: the expiry-aware `jarSend` from
`Client.CookieExpiry` (drops expired cookies, keeps live matches). -/
def Jar.get (jar : Jar) (now : Nat) (r : Req) : List StoredCookie :=
  CookieExpiry.jarSend jar.cookies now r

/-- §5.3 storage-limit enforcement: reuse the proven cap-enforcing `enforce`. -/
def Jar.enforced (jar : Jar) : Jar :=
  { jar with cookies := enforce jar.caps jar.cookies }

/-! ############################################################################
    ## Store → get round-trip
    ########################################################################## -/

/-- **A STORED COOKIE IS RETRIEVED.** A `Set-Cookie` that the domain guard accepts,
that is still live at `now`, and whose domain / path / Secure conditions match the
request (exactly what `cookieMatches` decides) is returned by `get` on the jar it
was stored into. The store→get round-trip closes: what you put in, matching, you
get out. -/
theorem jar_store_get (jar : Jar) (now created : Nat) (attr : ExpiryAttr)
    (c : Cookie) (r : Req)
    (haccept : jar.accept c = true)
    (hlive : (mkStored now created attr c).expiredAt now = false)
    (hmatch : cookieMatches c r = true) :
    mkStored now created attr c ∈ (jar.store now created attr c).get now r := by
  unfold Jar.store Jar.get
  rw [if_pos haccept]
  rw [CookieExpiry.jarSend, List.mem_filter]
  refine ⟨List.mem_cons_self, ?_⟩
  unfold sendableNow
  rw [hlive]
  -- the stored cookie's matcher cookie is `c`, which matches
  have : (mkStored now created attr c).cookie = c := rfl
  rw [this, hmatch]
  rfl

/-! ############################################################################
    ## Expiry gate: expired cookies are never returned
    ########################################################################## -/

/-- **AN EXPIRED COOKIE IS NEVER RETURNED.** A cookie expired at `now` is not in
`get`'s result for ANY request — the expiry gate dominates the domain / path /
Secure matcher. -/
theorem jar_evicts_expired (jar : Jar) (now : Nat) (r : Req) (sc : StoredCookie)
    (hexp : sc.expiredAt now = true) : sc ∉ jar.get now r := by
  unfold Jar.get
  exact CookieExpiry.cookie_expired_not_sent jar.cookies now r sc hexp

/-! ############################################################################
    ## Public-suffix rejection (RFC 6265 §5.3 step 5) — no supercookie
    ########################################################################## -/

/-- **NO SUPERCOOKIE.** A `Domain` cookie (not host-only) whose domain the oracle
flags as a public suffix is REJECTED: `store` leaves the jar's cookie set
unchanged, so a supercookie can never enter the store. -/
theorem jar_public_suffix (jar : Jar) (now created : Nat) (attr : ExpiryAttr)
    (c : Cookie) (hdom : c.hostOnly = false) (hps : jar.psl c.domain = true) :
    (jar.store now created attr c).cookies = jar.cookies := by
  have hrej : jar.accept c = false := by
    unfold Jar.accept; rw [hdom, hps]; rfl
  unfold Jar.store
  rw [if_neg (by rw [hrej]; exact Bool.noConfusion)]

/-- Consequence of the rejection: `get` is unaffected by a supercookie `store`,
for every clock and every request — the supercookie is never retrievable through
this jar. -/
theorem jar_public_suffix_get (jar : Jar) (now created now' : Nat) (attr : ExpiryAttr)
    (c : Cookie) (r : Req) (hdom : c.hostOnly = false) (hps : jar.psl c.domain = true) :
    (jar.store now created attr c).get now' r = jar.get now' r := by
  unfold Jar.get
  rw [jar_public_suffix jar now created attr c hdom hps]

/-! ############################################################################
    ## Size bounding (RFC 6265 §5.3 steps 11–12)
    ########################################################################## -/

/-- **THE JAR IS SIZE-BOUNDED.** After storage-limit enforcement the jar holds at
most `total` cookies overall and at most `perDomain` cookies for any single
domain. Both caps hold simultaneously. -/
theorem jar_size_bounded (jar : Jar) :
    jar.enforced.cookies.length ≤ jar.caps.total
    ∧ ∀ d : Labels, domCount d jar.enforced.cookies ≤ jar.caps.perDomain :=
  CookieExpiry.jar_size_bounded jar.caps jar.cookies

/-! ############################################################################
    ## Non-vacuity: real cookies, both directions, load-bearing guards
    ########################################################################## -/

/-- Public-suffix oracle for the concrete checks: `com = [0]` and `co.uk = [7, 8]`
are public suffixes; everything else is registrable. -/
def demoPsl : Labels → Bool := fun d => decide (d = [0]) || decide (d = [7, 8])

/-- example.com = [1, 0]; sub.example.com = [2, 1, 0]; com = [0]. -/
def demoJar : Jar :=
  { psl := demoPsl, caps := { perDomain := 2, total := 2 }, cookies := [] }

/-- An ordinary `Domain` cookie for example.com (registrable, so accepted). -/
def exampleCookie : Cookie :=
  { name := 1, value := 42, domain := [1, 0], path := [], secure := false, hostOnly := false }

/-- A SUPERCOOKIE attempt: a `Domain` cookie for the public suffix `com`. -/
def superCookie : Cookie :=
  { name := 9, value := 9, domain := [0], path := [], secure := false, hostOnly := false }

/-- A request to sub.example.com over HTTPS. -/
def subReq : Req := { host := [2, 1, 0], path := [], https := true, hostIsIp := false }

-- The registrable example.com cookie is accepted; the supercookie is rejected.
example : demoJar.accept exampleCookie = true := by decide
example : demoJar.accept superCookie = false := by decide
-- A host-only cookie whose host IS a public suffix is still accepted: the guard is
-- Domain-scoped (host-only cookies are immune by construction), per §5.3 step 5.
example :
    demoJar.accept
      { name := 5, value := 5, domain := [0], path := [], secure := false, hostOnly := true }
      = true := by decide

-- Round-trip: storing the example.com cookie with a future Max-Age makes it
-- retrievable at sub.example.com (domain-match) while still live.
example :
    mkStored 10 0 (.maxAge 100) exampleCookie
      ∈ (demoJar.store 10 0 (.maxAge 100) exampleCookie).get 50 subReq := by decide
-- After it expires (now = 200 > 10 + 100), the very same store no longer yields it
-- — the matcher still matches, so this is the expiry gate, not a match failure.
example :
    (demoJar.store 10 0 (.maxAge 100) exampleCookie).get 200 subReq = [] := by decide

-- The supercookie store is a NO-OP: the jar is unchanged and nothing is retrievable.
example : (demoJar.store 0 0 .session superCookie).cookies = demoJar.cookies := by decide
example : (demoJar.store 0 0 .session superCookie).get 0 subReq = [] := by decide

/-! ### The public-suffix guard is load-bearing -/

/-- A MUTANT store that DROPS the §5.3-step-5 guard (accepts every cookie,
supercookie or not). -/
def badStore (jar : Jar) (now created : Nat) (attr : ExpiryAttr) (c : Cookie) : Jar :=
  { jar with cookies := mkStored now created attr c :: jar.cookies }

-- The mutant admits the supercookie and would then SEND it to sub.example.com
-- (and, being a `com` cookie, to every registrant under `com`) — exactly the
-- cross-site supercookie the real guard prevents. So the guard has teeth.
example :
    mkStored 0 0 .session superCookie
      ∈ (badStore demoJar 0 0 .session superCookie).get 0 subReq
    ∧ (demoJar.store 0 0 .session superCookie).get 0 subReq = [] := by decide

/-! ### The expiry gate is load-bearing (a live cookie IS returned) -/

-- Sanity that `jar_store_get`'s hypotheses are satisfiable: the example.com cookie
-- with a future lifetime is live and matches, and is indeed returned.
example :
    (mkStored 10 0 (.maxAge 100) exampleCookie).expiredAt 50 = false
    ∧ cookieMatches exampleCookie subReq = true := by decide

/-! ### Size bounding has teeth -/

def c3 : StoredCookie :=
  { cookie := { name := 3, value := 3, domain := [1, 0], path := [], secure := false, hostOnly := true },
    expiry := none, created := 3 }
def c2 : StoredCookie :=
  { cookie := { name := 2, value := 2, domain := [1, 0], path := [], secure := false, hostOnly := true },
    expiry := none, created := 2 }
def c1 : StoredCookie :=
  { cookie := { name := 1, value := 1, domain := [1, 0], path := [], secure := false, hostOnly := true },
    expiry := none, created := 1 }

-- Enforcement's admission engine (`enforceOrder`, offered newest-first) keeps the
-- two NEWEST (c3, c2) and evicts the OLDEST (c1); the length is capped at total = 2
-- and the per-domain count is 2. (`Jar.enforced` sorts newest-first via `mergeSort`
-- and then runs exactly this engine; `mergeSort`'s well-founded recursion does not
-- reduce under the kernel `decide`, so the witness pins the admission engine — the
-- Jar-level guarantee is the proven `jar_size_bounded`.)
example : enforceOrder { perDomain := 2, total := 2 } [c3, c2, c1] = [c3, c2] := by decide
example : (enforceOrder { perDomain := 2, total := 2 } [c3, c2, c1]).length = 2 := by decide
example : domCount [1, 0] (enforceOrder { perDomain := 2, total := 2 } [c3, c2, c1]) = 2 := by decide

end Client.CookieJar
