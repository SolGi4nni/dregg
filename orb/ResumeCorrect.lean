import Resume.Ticket
import Resume.Ocsp
import Reactor.Pki

/-!
# ResumeCorrect — correctness of TLS session resumption and OCSP stapling

This file states, **independently of the implementation**, what the standards
require of the two acceptance decisions the running server makes when a
returning client resumes a session, and then proves that the *deployed*
decision functions the reactor invokes agree with that specification.

The specifications are transcribed directly from the RFCs:

* **Session-resumption tickets** — RFC 8446 (TLS 1.3) §2.2 *Resumption and
  Pre-Shared Key* and §4.6.1 *New Session Ticket Message*.  A server hands a
  returning client an opaque ticket that names a PSK derived from the earlier
  handshake; on return the client offers that ticket, and the server resumes
  **iff** (a) the ticket is still within its `ticket_lifetime` window measured
  from when it was issued — RFC 8446 §4.6.1: the lifetime is a bound in seconds
  and a ticket is discarded once it elapses, with an optional clock-skew
  allowance (§8.2) — and (b) the opaque handle resolves to a PSK the server
  still holds (§2.2: "the server … determines whether it is willing to accept …
  by looking up the … identity").

* **OCSP stapling** — RFC 6960 §2.2 *Response* and §4.2.1 *ASN.1 Specification
  of the OCSP Response*.  A stapled response is acceptable **iff** (a) its
  `certStatus` is `good` (§2.2 — not `revoked`, not `unknown`), (b) the current
  time lies in its `[thisUpdate, nextUpdate)` freshness window, and (c) the
  `certID` in the response identifies the certificate being served (§4.2.1 /
  §3.2: "the certificate identified in a received response corresponds to the
  certificate that was identified in the corresponding request").

The deployed functions are `Resume.accept` (ticket window + key generation) and
`Resume.Staple.accepts` (status `good` ∧ freshness window ∧ `certID` matches the
served certificate), which the reactor invokes at the one place the handshake
completes via `Reactor.PkiWire.resumeOk` / `ocspOk`
(`Reactor.PkiWire.wiredPkiConfig`).  This file binds *those* functions, not a
wrapper.

## Result

* **Tickets** — a full, non-vacuous refinement: `Resume.accept` accepts a ticket
  **iff** the RFC-8446 resumption predicate holds, with the clock-skew allowance
  instantiated at `0` (the conservative choice — the deployed server grants no
  skew and so never resumes an over-lifetime ticket; `accept_sound_any_skew`
  shows every deployed acceptance still lies inside the spec window for *any*
  skew ≥ 0) and the "handle resolves to a stored PSK" gate realized as the
  ticket's key generation being current (`epoch = t.epoch`).

* **OCSP staples — a full, non-vacuous refinement (finding closed).**  The
  deployed `Resume.Staple` now carries `certStatus` (RFC 6960 §2.2) and `certId`
  (§4.2.1), and the deployed decision `Resume.Staple.accepts` (hence
  `Reactor.PkiWire.ocspOk`) requires the certificate status to be `good`, the
  response to be fresh, *and* its `certID` to name the served certificate
  (`pcfg.servedCertId`).  `serve_refines_stapleValid` / `ocspOk_refines_stapleValid`
  prove the deployed gate accepts a staple **iff** the RFC-6960 staple-validity
  predicate `StapleValid` holds.  Non-vacuity: `revoked_fresh_staple_rejected`
  shows a revoked-but-fresh staple now yields **no** acceptance, and
  `mismatched_fresh_staple_rejected` the same for a fresh `good` staple issued
  for a different certificate; `good_fresh_matching_accepted_and_valid` shows a
  genuinely valid staple is accepted.
-/

namespace ResumeCorrect

/-! ## Part 1 — session-resumption tickets (RFC 8446 §2.2, §4.6.1)

The specification is written over an abstract *resumption offer* with no
reference to the implementation's `Ticket` structure or its `accept` function.
-/

/-- An offer to resume, as the standard frames it: when the ticket was issued,
its `ticket_lifetime`, the current server clock, and whether the opaque handle
resolves to a PSK the server still holds (RFC 8446 §2.2 / §4.6.1). -/
structure ResumptionOffer where
  /-- Server time at which the ticket was minted — the basis for ticket age. -/
  issued : Nat
  /-- `ticket_lifetime` (RFC 8446 §4.6.1): the validity duration in seconds. -/
  lifetime : Nat
  /-- The current server clock. -/
  now : Nat
  /-- The opaque handle resolves to a PSK the server still holds (§2.2). -/
  handleResolves : Bool

/-- **RFC 8446 §2.2 / §4.6.1 resumption predicate.**  A returning client's
ticket may be resumed iff the age is non-negative and within `lifetime + skew`,
and the opaque handle resolves to a stored PSK.  `skew` is the optional
clock-skew allowance of §8.2. -/
def Resumes (o : ResumptionOffer) (skew : Nat) : Prop :=
  o.issued ≤ o.now ∧ o.now < o.issued + o.lifetime + skew ∧ o.handleResolves = true

/-- The deployed function realizes an offer from the ticket, the clock, and the
current key generation: the ticket's issue time and lifetime, no clock skew, and
the "handle resolves to a stored PSK" gate realized as *the ticket's key
generation is the one currently accepted* (`epoch = t.epoch`) — a key rotation
drops every prior-generation PSK from the store at once. -/
def deployedOffer (t : Resume.Ticket) (now epoch : Nat) : ResumptionOffer :=
  { issued := t.issued, lifetime := t.lifetime, now := now,
    handleResolves := decide (epoch = t.epoch) }

/-- **Refinement (tickets).**  The deployed `Resume.accept` accepts a ticket
exactly when the RFC-8446 resumption predicate holds for the realized offer,
with the clock-skew allowance at `0`.  This binds the function the reactor
invokes (`Reactor.PkiWire.resumeOk` → `Resume.accept`), not a wrapper. -/
theorem accept_refines_spec (t : Resume.Ticket) (now epoch : Nat) :
    Resume.accept t now epoch = true ↔ Resumes (deployedOffer t now epoch) 0 := by
  rw [Resume.accept_iff]
  simp only [Resume.Ticket.Accepts, Resumes, deployedOffer, Resume.Ticket.expiry,
    Nat.add_zero, decide_eq_true_eq]

/-- **Deployed acceptance is sound for every skew.**  If `Resume.accept`
accepts, the RFC predicate holds for *any* clock-skew allowance `skew ≥ 0` — the
deployed verdict never resumes a ticket the standard would reject, whatever skew
the standard permits. -/
theorem accept_sound_any_skew (t : Resume.Ticket) (now epoch skew : Nat)
    (h : Resume.accept t now epoch = true) : Resumes (deployedOffer t now epoch) skew := by
  obtain ⟨h1, h2, h3⟩ := (accept_refines_spec t now epoch).mp h
  exact ⟨h1, by simp only [deployedOffer] at h2 ⊢; omega, h3⟩

/-! ### The deployed reactor gate calls exactly `Resume.accept` -/

/-- The reactor's resumption gate, when a ticket is presented, **is** the
deployed `Resume.accept` on that ticket at the server clock and current key
epoch — this is the value `Reactor.PkiWire.wiredPkiConfig` runs on the accept
path. -/
theorem resumeOk_eq_accept (pcfg : Reactor.PkiWire.PkiCfg)
    (tc : Proto.TlsConn) (buf : Proto.Bytes) (t : Resume.Ticket)
    (ht : pcfg.ticketOf tc buf = some t) :
    Reactor.PkiWire.resumeOk pcfg tc buf = Resume.accept t pcfg.now pcfg.resumeEpoch := by
  simp only [Reactor.PkiWire.resumeOk, ht]

/-- **Refinement, at the reactor gate.**  The engine-invoked resumption gate
accepts a presented ticket iff the RFC-8446 resumption predicate holds. -/
theorem resumeOk_refines_spec (pcfg : Reactor.PkiWire.PkiCfg)
    (tc : Proto.TlsConn) (buf : Proto.Bytes) (t : Resume.Ticket)
    (ht : pcfg.ticketOf tc buf = some t) :
    Reactor.PkiWire.resumeOk pcfg tc buf = true ↔
      Resumes (deployedOffer t pcfg.now pcfg.resumeEpoch) 0 := by
  rw [resumeOk_eq_accept pcfg tc buf t ht]; exact accept_refines_spec t pcfg.now pcfg.resumeEpoch

/-! ### Non-vacuity (tickets): expired / wrong-handle refused, valid accepted -/

/-- An **expired** ticket (issued 0, lifetime 10, presented at 20) is refused by
the deployed function. -/
theorem expired_ticket_refused :
    Resume.accept ⟨0, 10, 0⟩ 20 0 = false := by decide

/-- …and the specification agrees it is not resumable. -/
theorem expired_ticket_spec_invalid :
    ¬ Resumes (deployedOffer ⟨0, 10, 0⟩ 20 0) 0 := by
  rw [← accept_refines_spec]; decide

/-- A ticket whose opaque handle does **not** resolve to a stored PSK (its key
generation `5` is not the current epoch `0`) is refused even while fresh. -/
theorem wrong_handle_refused :
    Resume.accept ⟨0, 10, 5⟩ 5 0 = false := by decide

/-- A fresh ticket under the current key generation **is** resumed — the
refinement is not vacuously satisfied by rejecting everything. -/
theorem fresh_ticket_accepted :
    Resume.accept ⟨0, 10, 0⟩ 5 0 = true := by decide

/-- …and the specification agrees it is resumable. -/
theorem fresh_ticket_spec_valid :
    Resumes (deployedOffer ⟨0, 10, 0⟩ 5 0) 0 :=
  (accept_refines_spec _ _ _).mp fresh_ticket_accepted

/-! ## Part 2 — OCSP stapling (RFC 6960 §2.2, §4.2.1)

Again the specification is written over an abstract *staple offer*, with no
reference to the implementation's `Staple` structure. -/

/-- The three OCSP certificate statuses (RFC 6960 §2.2 `CertStatus`) — the same
type the deployed `Resume.Staple` carries. -/
abbrev CertStatus := Resume.CertStatus

/-- A stapled OCSP response, as the standard frames it: its validity window
`[thisUpdate, nextUpdate)`, the current time, the certificate `status`, and
whether the response's `certID` identifies the certificate being served. -/
structure StapleOffer where
  thisUpdate : Nat
  nextUpdate : Nat
  now : Nat
  /-- RFC 6960 §2.2 `CertStatus`. -/
  status : CertStatus
  /-- RFC 6960 §4.2.1 / §3.2: the response's `certID` matches the served cert. -/
  certMatches : Bool

/-- **RFC 6960 §2.2 / §4.2.1 / §3.2 staple-validity predicate.**  A stapled
response is acceptable iff its status is `good`, the current time is inside the
`[thisUpdate, nextUpdate)` freshness window, and its `certID` identifies the
served certificate. -/
def StapleValid (o : StapleOffer) : Prop :=
  o.status = Resume.CertStatus.good ∧ o.thisUpdate ≤ o.now ∧ o.now < o.nextUpdate ∧ o.certMatches = true

/-- The offer the deployed `Resume.Staple` realizes at the server clock and the
served-certificate identity `servedCertId`.  Every field is now read off the
deployed decision's own inputs: the window and `certStatus` from the `Staple`,
and `certMatches` as *the deployed `certID` equals the served certificate's id* —
exactly the fact `Resume.Staple.accepts` decides. -/
def deployedStapleOffer (s : Resume.Staple) (now servedCertId : Nat) : StapleOffer :=
  { thisUpdate := s.thisUpdate, nextUpdate := s.nextUpdate, now := now,
    status := s.certStatus, certMatches := decide (s.certId = servedCertId) }

/-- **The deployed acceptance is exactly the RFC-6960 predicate.**  The deployed
`Resume.Staple.accepts` (status `good` ∧ fresh ∧ `certID` matches) holds iff the
realized offer satisfies `StapleValid`.  This is the algebraic core of the
staple refinement. -/
theorem accepts_iff_stapleValid (s : Resume.Staple) (now servedCertId : Nat) :
    s.accepts now servedCertId = true ↔ StapleValid (deployedStapleOffer s now servedCertId) := by
  rw [Resume.accepts_iff]
  simp only [StapleValid, deployedStapleOffer, decide_eq_true_eq, and_assoc]

/-- **Refinement (staples).**  The deployed single-staple serve decision accepts
a staple **iff** the RFC-6960 staple-validity predicate holds for the realized
offer.  Unlike the ticket case this binds `serve?` directly, and the finding is
now *closed*: a revoked or wrong-certificate staple is on the `none` side. -/
theorem serve_refines_stapleValid (s : Resume.Staple) (now servedCertId : Nat) :
    Resume.serve? s now servedCertId = some s
      ↔ StapleValid (deployedStapleOffer s now servedCertId) := by
  unfold Resume.serve?
  by_cases ha : s.accepts now servedCertId = true
  · rw [if_pos ha]
    exact ⟨fun _ => (accepts_iff_stapleValid s now servedCertId).mp ha, fun _ => rfl⟩
  · rw [if_neg ha]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd ((accepts_iff_stapleValid s now servedCertId).mpr h) ha

/-- The reactor's OCSP gate, when a staple is configured, **is** the deployed
`Resume.Staple.accepts` on that staple at the server clock and the served-cert
identity — the value `Reactor.PkiWire.wiredPkiConfig` runs. -/
theorem ocspOk_eq_accepts (pcfg : Reactor.PkiWire.PkiCfg) (s : Resume.Staple)
    (hs : pcfg.staple = some s) :
    Reactor.PkiWire.ocspOk pcfg = s.accepts pcfg.now pcfg.servedCertId := by
  simp only [Reactor.PkiWire.ocspOk, hs]

/-- **Refinement, at the reactor gate.**  The engine-invoked OCSP gate accepts a
configured staple **iff** the RFC-6960 staple-validity predicate holds — the
deployed decision the running server makes is exactly the standard's. -/
theorem ocspOk_refines_stapleValid (pcfg : Reactor.PkiWire.PkiCfg) (s : Resume.Staple)
    (hs : pcfg.staple = some s) :
    Reactor.PkiWire.ocspOk pcfg = true
      ↔ StapleValid (deployedStapleOffer s pcfg.now pcfg.servedCertId) := by
  rw [ocspOk_eq_accepts pcfg s hs]; exact accepts_iff_stapleValid s pcfg.now pcfg.servedCertId

/-! ### Non-vacuity (staples): revoked / wrong-cert / stale REJECTED, valid accepted

The finding is closed: the previous witnesses that the deployed gate *accepted*
a revoked or wrong-certificate staple are replaced by witnesses that it now
*rejects* them.  All use a staple fresh at the check time (`[0,10)` at `now = 5`)
so freshness is not what does the rejecting.  A `Staple` is
`⟨thisUpdate, nextUpdate, certStatus, certId, body⟩`; the served certificate here
has identity `7`. -/

/-- **Revoked, though fresh, is now REJECTED.**  A staple for a **revoked**
certificate — fresh, `certID` matching the served cert `7` — yields no
acceptance, and the spec agrees it is invalid (RFC 6960 §2.2). -/
theorem revoked_fresh_staple_rejected :
    Resume.serve? ⟨0, 10, Resume.CertStatus.revoked, 7, 0⟩ 5 7 = none
  ∧ ¬ StapleValid (deployedStapleOffer ⟨0, 10, Resume.CertStatus.revoked, 7, 0⟩ 5 7) := by
  refine ⟨by decide, ?_⟩
  intro h; exact absurd h.1 (by decide)

/-- **Wrong certificate, though fresh and `good`, is now REJECTED.**  A fresh,
`good` staple whose `certID` (`9`) does **not** identify the served certificate
(`7`) yields no acceptance, and the spec agrees it is invalid (RFC 6960
§4.2.1 / §3.2). -/
theorem mismatched_fresh_staple_rejected :
    Resume.serve? ⟨0, 10, Resume.CertStatus.good, 9, 0⟩ 5 7 = none
  ∧ ¬ StapleValid (deployedStapleOffer ⟨0, 10, Resume.CertStatus.good, 9, 0⟩ 5 7) := by
  refine ⟨by decide, ?_⟩
  intro h; exact absurd h.2.2.2 (by decide)

/-- A **stale** staple (window `[0,10)` at `now = 15`), even `good` and matching,
is refused — the freshness conjunct is still enforced. -/
theorem stale_staple_refused :
    Resume.serve? ⟨0, 10, Resume.CertStatus.good, 7, 0⟩ 15 7 = none := by decide

/-- A genuinely valid staple (`good`, fresh, `certID` matching the served cert
`7`) is both accepted by the deployed decision and RFC-valid — the refinement is
not vacuously satisfied by rejecting everything. -/
theorem good_fresh_matching_accepted_and_valid :
    Resume.serve? ⟨0, 10, Resume.CertStatus.good, 7, 0⟩ 5 7
        = some ⟨0, 10, Resume.CertStatus.good, 7, 0⟩
  ∧ StapleValid (deployedStapleOffer ⟨0, 10, Resume.CertStatus.good, 7, 0⟩ 5 7) := by
  refine ⟨by decide, rfl, by decide, by decide, rfl⟩

end ResumeCorrect
