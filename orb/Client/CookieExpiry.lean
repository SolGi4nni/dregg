/-
Client.CookieExpiry — verified cookie EXPIRY and jar-eviction policy, layered on
top of the RFC 6265 §5.4 sendability matcher in `Client.Session`.

`Client.Session` proved WHICH stored cookies a request may see (domain / path /
Secure matching). This module adds the two remaining halves of the RFC 6265 §5.3
storage model that a real client needs and that a matcher alone does not give:

  * WHEN a stored cookie stops being sent — its persistence lifetime, computed
    from the `Max-Age` (§5.2.2) and `Expires` (§5.2.1) attributes and checked
    against the clock at send time (§5.4 step 1: expired cookies are removed and
    never returned).
  * HOW the jar stays bounded — the §5.3 storage limits: a per-domain cookie cap
    and a global cap, both enforced by evicting the OLDEST cookies first.

Each capability is specified as an INDEPENDENT contract, in this module's own
vocabulary, with no appeal to the executable decision functions; the executable
functions are proven to meet it, and a mutant / concrete witness is exhibited so
the theorems are not vacuous. The `Client.Session` module is imported UNMODIFIED
— the real `Cookie`, `Req`, and `cookieMatches` matcher are reused, so the
expiry gate composes with the genuine matcher rather than a stand-in.

## Expiry (RFC 6265 §5.2.1 / §5.2.2 / §5.3)

A stored cookie carries a resolved expiry INSTANT (`none` for a session cookie,
which has no persistent lifetime and never time-expires). `resolveExpiry` turns
the wire attribute into that instant: an absolute `Expires` time is taken as-is;
a `Max-Age` of `Δ` seconds resolves to `now + Δ`, and — per §5.2.2 — a `Max-Age`
of zero or less resolves to the earliest representable instant, i.e. the cookie
is already expired. A stored cookie is expired at `now` iff it has an expiry
instant `e` with `e ≤ now`.

  * `cookie_expired_not_sent` — a cookie that is expired at `now` is NEVER in the
    outgoing set, regardless of how perfectly it domain/path/Secure-matches. The
    time gate dominates the matcher.

## Jar eviction (RFC 6265 §5.3 step 1 + steps 11–12)

  * `jar_evicts_expired` — the reaper's surviving set is EXACTLY the cookies that
    are not expired at `now`: every expired cookie is dropped and every fresh one
    is kept (both directions).
  * `jar_size_bounded` — after enforcement the jar holds at most `total` cookies,
    and at most `perDomain` cookies for any single domain. Enforcement admits
    cookies greedily in NEWEST-FIRST order and rejects once a cap is hit, so the
    cookies it drops are the OLDEST; `enforce_keeps_newest` pins this down: when
    the per-domain cap does not bind first, the survivors are precisely the
    `total` newest cookies (the older tail is evicted).
-/
import Client.Session

namespace Client.CookieExpiry

open Client.Session

/-! ############################################################################
    ## Expiry lifetime (RFC 6265 §5.2.1 / §5.2.2)
    ########################################################################## -/

/-- The `Expires`/`Max-Age` attribute as it arrives on the wire. `session` is the
absence of both (a session cookie); `expiresAt t` is an absolute §5.2.1 instant;
`maxAge Δ` is a §5.2.2 relative lifetime in seconds (may be zero or negative). -/
inductive ExpiryAttr
  | session
  | expiresAt (t : Nat)
  | maxAge (delta : Int)
deriving Repr, DecidableEq

/-- RFC 6265 §5.2.1 / §5.2.2 attribute resolution against the current clock
`now`. `Max-Age` takes precedence over `Expires` on the wire, so a resolved
attribute already encodes that choice. A `Max-Age ≤ 0` yields the earliest
representable instant `0` (the cookie is already expired); a positive `Max-Age Δ`
yields `now + Δ`; an absolute `Expires t` is kept as `t`. -/
def resolveExpiry (now : Nat) : ExpiryAttr → Option Nat
  | .session      => none
  | .expiresAt t  => some t
  | .maxAge delta => some (if delta ≤ 0 then 0 else now + delta.toNat)

/-- A stored cookie: the RFC 6265 matcher's `Cookie` (reused unmodified from
`Client.Session`), its resolved expiry instant (`none` = session cookie), and a
monotonic creation stamp — a larger `created` means the cookie was stored more
recently, which is the order the jar evicts by (oldest = smallest `created`). -/
structure StoredCookie where
  cookie : Cookie
  expiry : Option Nat
  created : Nat
deriving Repr, DecidableEq

/-! ### The expiry contract (independent specification) -/

/-- RFC 6265 §5.3 / §5.4: a stored cookie is EXPIRED at `now` iff it carries an
expiry instant `e` that is at or before `now`. A session cookie (no instant) is
never expired by the clock. -/
def Expired (sc : StoredCookie) (now : Nat) : Prop :=
  ∃ e, sc.expiry = some e ∧ e ≤ now

/-! ### The executable expiry check -/

/-- Executable expiry test (dual of `Expired`). -/
def StoredCookie.expiredAt (sc : StoredCookie) (now : Nat) : Bool :=
  match sc.expiry with
  | none   => false
  | some e => decide (e ≤ now)

/-- The executable expiry test meets the `Expired` contract. -/
theorem expiredAt_iff (sc : StoredCookie) (now : Nat) :
    sc.expiredAt now = true ↔ Expired sc now := by
  unfold StoredCookie.expiredAt Expired
  cases he : sc.expiry with
  | none => simp
  | some e => simp [he, decide_eq_true_eq]

/-! ############################################################################
    ## The expiry-aware sender (RFC 6265 §5.4 step 1)
    ########################################################################## -/

/-- A stored cookie is sendable at `now` iff it is NOT expired AND it matches the
request under the genuine `Client.Session` matcher. The `!expiredAt` guard is
RFC 6265 §5.4 step 1: expired cookies are removed before matching. -/
def sendableNow (now : Nat) (r : Req) (sc : StoredCookie) : Bool :=
  !sc.expiredAt now && cookieMatches sc.cookie r

/-- The cookies a jar sends on a request at clock `now`: those live and matching. -/
def jarSend (jar : List StoredCookie) (now : Nat) (r : Req) : List StoredCookie :=
  jar.filter (sendableNow now r)

/-- **AN EXPIRED COOKIE IS NEVER SENT.** A cookie that is expired at `now` is not
in the outgoing set for ANY request — the time gate dominates the domain / path /
Secure matcher entirely. -/
theorem cookie_expired_not_sent (jar : List StoredCookie) (now : Nat) (r : Req)
    (sc : StoredCookie) (h : sc.expiredAt now = true) : sc ∉ jarSend jar now r := by
  intro hc
  rw [jarSend, List.mem_filter] at hc
  have hsend := hc.2
  unfold sendableNow at hsend
  rw [h] at hsend
  simp at hsend

/-- A LIVE, matching cookie IS sent — the send set is not empty for the wrong
reason. (Companion to `cookie_expired_not_sent`; witnesses the other direction.) -/
theorem cookie_live_sent (jar : List StoredCookie) (now : Nat) (r : Req)
    (sc : StoredCookie) (hlive : sc.expiredAt now = false)
    (hmatch : cookieMatches sc.cookie r = true) (hmem : sc ∈ jar) :
    sc ∈ jarSend jar now r := by
  rw [jarSend, List.mem_filter]
  refine ⟨hmem, ?_⟩
  unfold sendableNow
  rw [hlive, hmatch]
  simp

/-! ############################################################################
    ## The reaper (RFC 6265 §5.3 step 1)
    ########################################################################## -/

/-- The reaper: drop every cookie that is expired at `now`, keep the rest. -/
def reap (now : Nat) (jar : List StoredCookie) : List StoredCookie :=
  jar.filter (fun sc => !sc.expiredAt now)

/-- **THE REAPER DROPS EXACTLY THE EXPIRED COOKIES.** A cookie survives the reaper
iff it was in the jar and is not expired at `now` — every expired cookie is
removed, every fresh one is kept, in both directions. -/
theorem jar_evicts_expired (now : Nat) (jar : List StoredCookie) (sc : StoredCookie) :
    sc ∈ reap now jar ↔ (sc ∈ jar ∧ sc.expiredAt now = false) := by
  rw [reap, List.mem_filter]
  constructor
  · rintro ⟨hmem, hkeep⟩
    exact ⟨hmem, by simpa using hkeep⟩
  · rintro ⟨hmem, hfresh⟩
    exact ⟨hmem, by simp [hfresh]⟩

/-- Corollary: an expired cookie does not survive the reaper. -/
theorem reap_drops_expired (now : Nat) (jar : List StoredCookie) (sc : StoredCookie)
    (h : sc.expiredAt now = true) : sc ∉ reap now jar := by
  rw [jar_evicts_expired]
  rintro ⟨_, hfresh⟩
  rw [h] at hfresh
  exact Bool.noConfusion hfresh

/-! ############################################################################
    ## Size bounding by oldest-eviction (RFC 6265 §5.3 steps 11–12)
    ########################################################################## -/

/-- Storage limits: at most `perDomain` cookies per domain, at most `total`
overall. -/
structure Caps where
  perDomain : Nat
  total : Nat
deriving Repr

/-- Number of cookies in `l` whose cookie-domain is exactly `d`. -/
def domCount (d : Labels) (l : List StoredCookie) : Nat :=
  l.countP (fun sc => decide (sc.cookie.domain = d))

/-- Admit `sc` into the accumulator iff neither cap would be exceeded: its domain
is below the per-domain cap AND the jar is below the total cap. Otherwise reject
it. Cookies are offered NEWEST-FIRST, so a rejected cookie is older than every
cookie already admitted — the drops are the oldest. -/
def admitCookie (caps : Caps) (acc : List StoredCookie) (sc : StoredCookie) :
    List StoredCookie :=
  if domCount sc.cookie.domain acc < caps.perDomain ∧ acc.length < caps.total then
    acc ++ [sc]
  else acc

/-- Fold the admission rule over an already-ordered cookie stream (newest first). -/
def enforceOrder (caps : Caps) (order : List StoredCookie) : List StoredCookie :=
  order.foldl (admitCookie caps) []

/-- Order cookies newest-first (largest `created` first). -/
def byNewest (a b : StoredCookie) : Bool := decide (b.created ≤ a.created)

/-- Enforce the storage caps on a jar: sort newest-first, then greedily admit. -/
def enforce (caps : Caps) (jar : List StoredCookie) : List StoredCookie :=
  enforceOrder caps (jar.mergeSort byNewest)

/-! ### The two cap bounds -/

/-- The total cap is an invariant of the admission fold. -/
theorem enforceOrder_total_le (caps : Caps) :
    ∀ (order acc : List StoredCookie),
      acc.length ≤ caps.total →
      (order.foldl (admitCookie caps) acc).length ≤ caps.total := by
  intro order
  induction order with
  | nil => intro acc h; simpa using h
  | cons sc rest ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    unfold admitCookie
    by_cases hc : domCount sc.cookie.domain acc < caps.perDomain ∧ acc.length < caps.total
    · rw [if_pos hc, List.length_append]
      have : acc.length < caps.total := hc.2
      simp only [List.length_singleton]
      omega
    · rw [if_neg hc]; exact h

/-- The per-domain cap is an invariant of the admission fold, for every domain. -/
theorem enforceOrder_domCount_le (caps : Caps) (d : Labels) :
    ∀ (order acc : List StoredCookie),
      domCount d acc ≤ caps.perDomain →
      domCount d (order.foldl (admitCookie caps) acc) ≤ caps.perDomain := by
  intro order
  induction order with
  | nil => intro acc h; simpa using h
  | cons sc rest ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    unfold admitCookie
    by_cases hc : domCount sc.cookie.domain acc < caps.perDomain ∧ acc.length < caps.total
    · rw [if_pos hc]
      unfold domCount
      rw [List.countP_append, List.countP_singleton]
      by_cases hd : sc.cookie.domain = d
      · -- the added cookie is in domain d: use the per-domain guard
        have hguard : domCount sc.cookie.domain acc < caps.perDomain := hc.1
        rw [hd] at hguard
        simp only [decide_eq_true_eq]
        rw [if_pos hd]
        unfold domCount at hguard h
        omega
      · -- the added cookie is in another domain: count for d is unchanged
        rw [if_neg (by simpa using hd)]
        unfold domCount at h
        simpa using h
    · rw [if_neg hc]; exact h

/-- **THE JAR IS SIZE-BOUNDED.** After enforcement the jar holds at most `total`
cookies overall, and at most `perDomain` cookies for any single domain `d`. Both
caps hold simultaneously, for every jar and every domain. -/
theorem jar_size_bounded (caps : Caps) (jar : List StoredCookie) :
    (enforce caps jar).length ≤ caps.total
    ∧ ∀ d : Labels, domCount d (enforce caps jar) ≤ caps.perDomain := by
  refine ⟨?_, ?_⟩
  · unfold enforce enforceOrder
    exact enforceOrder_total_le caps _ [] (by simp)
  · intro d
    unfold enforce enforceOrder
    exact enforceOrder_domCount_le caps d _ [] (by simp [domCount])

/-! ### The evicted cookies are the OLDEST -/

/-- The total-cap-only admission step: admit while under the total cap. -/
def totalStep (k : Nat) (acc : List StoredCookie) (sc : StoredCookie) :
    List StoredCookie :=
  if acc.length < k then acc ++ [sc] else acc

/-- When the per-domain cap can never bind before the total cap
(`total ≤ perDomain`), the admission rule reduces to the total-cap-only step:
the domain guard is automatically satisfied whenever there is total headroom
(a domain's count is at most the total count, which is below `total ≤ perDomain`).
-/
theorem admitCookie_eq_totalStep (caps : Caps) (htp : caps.total ≤ caps.perDomain)
    (acc : List StoredCookie) (sc : StoredCookie) :
    admitCookie caps acc sc = totalStep caps.total acc sc := by
  unfold admitCookie totalStep
  by_cases hlen : acc.length < caps.total
  · have hdom : domCount sc.cookie.domain acc < caps.perDomain := by
      have h1 : domCount sc.cookie.domain acc ≤ acc.length := by
        unfold domCount; exact List.countP_le_length
      omega
    rw [if_pos ⟨hdom, hlen⟩, if_pos hlen]
  · rw [if_neg (fun h => hlen h.2), if_neg hlen]

/-- Fold-level version: over any order, the two folds agree under `total ≤ perDomain`. -/
theorem foldl_admit_eq_totalStep (caps : Caps) (htp : caps.total ≤ caps.perDomain) :
    ∀ (order acc : List StoredCookie),
      order.foldl (admitCookie caps) acc = order.foldl (totalStep caps.total) acc := by
  intro order
  induction order with
  | nil => intro acc; rfl
  | cons sc rest ih =>
    intro acc
    rw [List.foldl_cons, List.foldl_cons, admitCookie_eq_totalStep caps htp acc sc]
    exact ih _

/-- Once the accumulator is full, the total-cap step is inert. -/
theorem totalStep_saturated (k : Nat) :
    ∀ (order acc : List StoredCookie),
      k ≤ acc.length → order.foldl (totalStep k) acc = acc := by
  intro order
  induction order with
  | nil => intro acc _; rfl
  | cons sc rest ih =>
    intro acc h
    rw [List.foldl_cons]
    have : totalStep k acc sc = acc := by
      unfold totalStep; rw [if_neg (by omega)]
    rw [this]; exact ih acc h

/-- The total-cap fold keeps a PREFIX: from an accumulator of length `≤ k`, it
appends exactly the next `k - acc.length` cookies of the stream and drops the
rest. -/
theorem totalStep_eq_take (k : Nat) :
    ∀ (order acc : List StoredCookie),
      acc.length ≤ k →
      order.foldl (totalStep k) acc = acc ++ order.take (k - acc.length) := by
  intro order
  induction order with
  | nil => intro acc _; simp
  | cons sc rest ih =>
    intro acc h
    rw [List.foldl_cons]
    by_cases hlt : acc.length < k
    · have hstep : totalStep k acc sc = acc ++ [sc] := by
        unfold totalStep; rw [if_pos hlt]
      rw [hstep, ih (acc ++ [sc]) (by rw [List.length_append]; simp; omega)]
      rw [List.length_append, List.length_singleton]
      have hk : k - acc.length = (k - (acc.length + 1)) + 1 := by omega
      rw [hk, List.take_succ_cons, List.append_assoc]
      rfl
  -- acc is already full
    · have heq : acc.length = k := by omega
      have : totalStep k acc sc = acc := by unfold totalStep; rw [if_neg hlt]
      rw [this, totalStep_saturated k rest acc (by omega)]
      simp [heq]

/-- **THE EVICTED COOKIES ARE THE OLDEST.** When the per-domain cap does not bind
before the total cap (`total ≤ perDomain`), enforcement keeps EXACTLY the `total`
newest cookies of the jar; the cookies it drops are precisely the older tail. -/
theorem enforce_keeps_newest (caps : Caps) (htp : caps.total ≤ caps.perDomain)
    (jar : List StoredCookie) :
    enforce caps jar = (jar.mergeSort byNewest).take caps.total := by
  unfold enforce enforceOrder
  rw [foldl_admit_eq_totalStep caps htp, totalStep_eq_take caps.total _ [] (by simp)]
  simp

/-! ############################################################################
    ## Non-vacuity: real cookies, both directions, load-bearing guards
    ########################################################################## -/

/-- example.com = [1,0]; sub.example.com = [2,1,0]. -/
def httpsReq : Req := { host := [1, 0], path := [], https := true, hostIsIp := false }

/-- A host-only cookie for example.com, matching `httpsReq`, that EXPIRES at t=100. -/
def expiringCookie : StoredCookie :=
  { cookie := { name := 1, value := 1, domain := [1, 0], path := [],
                secure := false, hostOnly := true },
    expiry := some 100, created := 0 }

/-- A session cookie (never time-expires) for the same origin. -/
def sessionCookie : StoredCookie :=
  { cookie := { name := 2, value := 2, domain := [1, 0], path := [],
                secure := false, hostOnly := true },
    expiry := none, created := 1 }

-- Max-Age resolution: Δ = 30 at now = 10 gives instant 40.
example : resolveExpiry 10 (.maxAge 30) = some 40 := by decide
-- Max-Age ≤ 0 resolves to the earliest instant (already expired).
example : resolveExpiry 10 (.maxAge 0) = some 0 := by decide
example : resolveExpiry 10 (.maxAge (-5)) = some 0 := by decide
-- A session cookie has no expiry instant.
example : resolveExpiry 10 .session = none := by decide

-- The expiring cookie IS expired at t = 100 and t = 150 …
example : expiringCookie.expiredAt 100 = true := by decide
example : expiringCookie.expiredAt 150 = true := by decide
-- … but NOT before it expires.
example : expiringCookie.expiredAt 99 = false := by decide
-- A session cookie is never expired.
example : sessionCookie.expiredAt 1000000 = false := by decide

-- Before expiry the cookie is sent to its origin …
example : jarSend [expiringCookie] 50 httpsReq = [expiringCookie] := by decide
-- … and AFTER expiry the very same cookie is gone (the matcher still matches,
-- so this is the expiry gate at work, not a match failure).
example : jarSend [expiringCookie] 150 httpsReq = [] := by decide
-- while the session cookie beside it survives.
example : jarSend [expiringCookie, sessionCookie] 150 httpsReq = [sessionCookie] := by decide

-- The reaper drops the expired cookie and keeps the session cookie.
example : reap 150 [expiringCookie, sessionCookie] = [sessionCookie] := by decide
-- Before the deadline the reaper keeps both.
example : reap 50 [expiringCookie, sessionCookie] = [expiringCookie, sessionCookie] := by decide

/-! ### Eviction non-vacuity: the OLDEST are dropped -/

def demoCaps : Caps := { perDomain := 2, total := 2 }

/-- Three cookies for one domain, offered newest-first (created 3, 2, 1). -/
def c3 : StoredCookie :=
  { cookie := { name := 3, value := 3, domain := [1, 0], path := [], secure := false, hostOnly := true },
    expiry := none, created := 3 }
def c2 : StoredCookie :=
  { cookie := { name := 2, value := 2, domain := [1, 0], path := [], secure := false, hostOnly := true },
    expiry := none, created := 2 }
def c1 : StoredCookie :=
  { cookie := { name := 1, value := 1, domain := [1, 0], path := [], secure := false, hostOnly := true },
    expiry := none, created := 1 }

-- With a per-domain / total cap of 2, admitting [c3, c2, c1] newest-first keeps
-- the two NEWEST (c3, c2) and evicts the OLDEST (c1) — the eviction order has teeth.
example : enforceOrder demoCaps [c3, c2, c1] = [c3, c2] := by decide
-- The total cap alone binds identically when the domains differ: still keeps the
-- two newest offered.
example :
    enforceOrder { perDomain := 5, total := 2 } [c3, c2, c1] = [c3, c2] := by decide
-- A per-domain cap of 1 keeps only the single newest of the domain even with
-- total headroom — the per-domain cap is load-bearing.
example :
    enforceOrder { perDomain := 1, total := 5 } [c3, c2, c1] = [c3] := by decide

end Client.CookieExpiry
