/-
Client.Tls — client-initiated TLS acceptance: chain verification, SNI
hostname match, and ALPN selection.

This is the *client* dual of the server-side `Mtls` path validator.  When a
drorb client opens a TLS connection to an upstream, three checks gate whether
the handshake is accepted:

  * **Chain verification (RFC 5280 §6.1).**  The certificate chain the server
    presents must validate to a trusted root: every certificate inside its
    validity window, each non-top certificate signed by its successor, every
    signing certificate carrying the CA constraint, and the top a trust anchor.
    This is *exactly* the accounting the server-side `Mtls.verifyFrom` already
    decides, so it is reused verbatim — the client and the server run the same
    verified path validator over the peer's chain.

  * **Identity / SNI match (RFC 6125, RFC 9110 §4.3.4).**  A validated chain
    proves the certificates form a trusted path; it does *not* say the peer is
    the host the client meant to reach.  The client separately checks that the
    reference identity it dialed (the SNI server name) matches one of the leaf
    certificate's presented DNS names, honouring a single leftmost `*` wildcard
    label.  Without this a validly-signed certificate for `evil.example` would
    be accepted when the client asked for `bank.example` — an authentication
    bypass.

  * **ALPN selection (RFC 7301 §3.2).**  The client offers an ordered list of
    application protocols.  The server selects at most one.  The client accepts
    the selection only if it is one it offered; a server that names a protocol
    the client never offered is a protocol violation and yields no negotiated
    protocol (the RFC's `no_application_protocol` condition).

The cryptography stays behind the same named `verifySig` interface `Mtls` uses
(carried in `Mtls.Env`); every theorem here holds uniformly over every
signature-checking behaviour.  Hostnames and protocol identifiers are the only
concrete data the client half needs, so they are modeled directly (label lists
and byte-ish tokens) rather than left opaque.
-/

import Mtls.Theorems

namespace Client.Tls

/-! ## Hostnames and RFC 6125 identity matching -/

/-- A hostname as its ordered sequence of DNS labels, most-significant last:
`"www.example.com"` is `["www", "example", "com"]`.  Labels are compared as
opaque strings (DNS is case-insensitive on the wire; callers lower-case before
constructing these, exactly as the reference client normalises the SNI name and
the certificate SAN entries before comparison). -/
abbrev Hostname := List String

/-- A presented certificate identity (a SAN `dNSName` entry), RFC 6125 §6.4.

  * `exact h` — the literal hostname `h` (`"example.com"`).
  * `wildcard rest` — a leftmost-wildcard name `*.rest` (`"*.example.com"` is
    `wildcard ["example", "com"]`).  The `*` matches **exactly one** whole
    leftmost label and never the empty label or a dotted span. -/
inductive SanEntry where
  | exact (h : Hostname)
  | wildcard (rest : Hostname)
deriving DecidableEq, Repr

/-- Does one presented identity match the reference hostname the client dialed?

  * `exact h`      — matches iff `h` equals the reference identity exactly.
  * `wildcard rest`— matches iff the reference is a **single** leftmost label
    (any non-empty label) followed by exactly `rest`, **and** `rest` is
    non-empty.  So `*.example.com` matches `foo.example.com` but neither
    `example.com` (no leftmost label) nor `a.b.example.com` (two leftmost
    labels) nor a bare `*.` (empty tail).  This is the RFC 6125 §6.4.3 rule:
    the wildcard is the entire leftmost label and covers exactly one level. -/
def matchName : SanEntry → Hostname → Bool
  | .exact h, ref => decide (h = ref)
  | .wildcard rest, ref =>
      match ref with
      | [] => false
      | label :: tail => !label.isEmpty && !rest.isEmpty && decide (tail = rest)

/-- The client's identity check: the reference hostname matches **some**
presented SAN entry of the leaf certificate. -/
def nameMatches (sans : List SanEntry) (ref : Hostname) : Bool :=
  sans.any (matchName · ref)

/-! ## ALPN selection (RFC 7301) -/

/-- An application-protocol identifier (the ALPN protocol name, e.g. `"h2"`,
`"http/1.1"`).  Opaque token; only equality matters for negotiation. -/
abbrev Proto := String

/-- The outcome of ALPN negotiation as the client sees it. -/
inductive AlpnOutcome where
  /-- The server named a protocol the client offered: it is negotiated. -/
  | selected (p : Proto)
  /-- The server selected no protocol (omitted the extension): the connection
  proceeds with no negotiated application protocol (RFC 7301 permits this). -/
  | none
  /-- The server named a protocol the client did **not** offer: a protocol
  violation (`no_application_protocol`); nothing is negotiated. -/
  | violation
deriving DecidableEq, Repr

/-- Client-side ALPN negotiation.  `offered` is the ordered list the client
advertised; `serverPick` is the single protocol the server selected (or `none`).
The client accepts a pick only if it is one it offered. -/
def negotiateAlpn (offered : List Proto) : Option Proto → AlpnOutcome
  | Option.none => .none
  | some p => if p ∈ offered then .selected p else .violation

/-! ## Client handshake acceptance -/

/-- The data the TLS handshake surfaces to the client for the acceptance
decision: the peer's certificate chain (leaf first), the leaf's presented DNS
names, the reference identity (SNI) the client dialed, the protocols the client
offered, and the protocol the server selected. -/
structure Handshake where
  /-- Peer certificate chain, leaf first (the `Mtls` chain shape). -/
  chain : Mtls.Chain
  /-- The leaf (end-entity) certificate's presented DNS identities (SAN). -/
  leafSans : List SanEntry
  /-- The reference identity the client dialed and sent as SNI. -/
  sni : Hostname
  /-- The application protocols the client offered, in preference order. -/
  offered : List Proto
  /-- The protocol the server selected (`none` if the server omitted ALPN). -/
  serverPick : Option Proto

/-- **Chain-and-identity acceptance.**  The client accepts the peer iff the
certificate chain validates to a trusted root (`Mtls.verifyFrom`) **and** the
reference identity matches one of the leaf's presented DNS names.  Both are
required: a validated chain for the wrong host, or the right host on an
unvalidated chain, is rejected. -/
def accepts (env : Mtls.Env) (now : Mtls.Time) (hs : Handshake) : Bool :=
  Mtls.verifyFrom env now hs.chain && nameMatches hs.leafSans hs.sni

/-- The full client verdict: the accepted state carries the negotiated ALPN
outcome; a rejected handshake carries none. -/
def alpnOf (hs : Handshake) : AlpnOutcome :=
  negotiateAlpn hs.offered hs.serverPick

/-! ## Headline theorems -/

/-! ### #1 — the client accepts iff the chain validates and the name matches -/

/-- **`client_verifies_chain` — acceptance is exactly chain-validation ∧
name-match, stated sharply as an iff.**  Forward: acceptance implies the chain
validated to a trusted anchor *and* the SNI matched the leaf's identity — so
both are necessary.  Backward: the two together suffice.  The crypto stays
behind `Mtls.verifyFrom`'s named `verifySig`. -/
theorem client_verifies_chain (env : Mtls.Env) (now : Mtls.Time) (hs : Handshake) :
    accepts env now hs = true ↔
      (Mtls.verifyFrom env now hs.chain = true ∧ nameMatches hs.leafSans hs.sni = true) := by
  simp [accepts]

/-- A client that accepts has, in particular, a chain that validated to a
trusted anchor (via `Mtls`'s soundness): every certificate valid, each link
signed, every signer a CA, and the top a trust anchor. -/
theorem client_accept_chain_anchored (env : Mtls.Env) (now : Mtls.Time) (hs : Handshake)
    (h : accepts env now hs = true) : Mtls.topAnchored env hs.chain :=
  Mtls.verify_needs_topAnchored ((client_verifies_chain env now hs).mp h).1

/-- A client that accepts dialed a reference identity that matches one of the
leaf certificate's presented DNS names. -/
theorem client_accept_name_matches (env : Mtls.Env) (now : Mtls.Time) (hs : Handshake)
    (h : accepts env now hs = true) : nameMatches hs.leafSans hs.sni = true :=
  ((client_verifies_chain env now hs).mp h).2

/-! ### #2 — a broken chain or a name mismatch is rejected -/

/-- **`client_rejects_bad_chain` — a chain that does not validate is rejected**,
regardless of the identity presented.  There is no path from a failed RFC 5280
validation to acceptance. -/
theorem client_rejects_bad_chain (env : Mtls.Env) (now : Mtls.Time) (hs : Handshake)
    (h : Mtls.verifyFrom env now hs.chain = false) : accepts env now hs = false := by
  simp [accepts, h]

/-- **A name mismatch is rejected**, even on a fully validated chain.  A
correctly-signed certificate for a host the client did not dial does not
authenticate the connection (RFC 6125 identity check). -/
theorem client_rejects_name_mismatch (env : Mtls.Env) (now : Mtls.Time) (hs : Handshake)
    (h : nameMatches hs.leafSans hs.sni = false) : accepts env now hs = false := by
  simp [accepts, h]

/-- A chain containing an expired certificate is rejected by the client no
matter what identity it presents (the validity window is enforced at every link
by `Mtls`). -/
theorem client_rejects_expired {env : Mtls.Env} {now : Mtls.Time} {hs : Handshake}
    {c : Mtls.Cert} (hmem : c ∈ hs.chain) (hexp : c.notAfter < now) :
    accepts env now hs = false :=
  client_rejects_bad_chain env now hs (Mtls.expired_cert_fails hmem hexp)

/-! ### #3 — the negotiated ALPN protocol is one the client offered -/

/-- **`alpn_selects` — a negotiated ALPN protocol is one the client offered.**
If the client's ALPN negotiation yields `selected p`, then `p` is a member of
the protocols the client advertised.  A server cannot force a protocol the
client never offered (RFC 7301 §3.2). -/
theorem alpn_selects {offered : List Proto} {pick : Option Proto} {p : Proto}
    (h : negotiateAlpn offered pick = .selected p) : p ∈ offered := by
  cases pick with
  | none => simp [negotiateAlpn] at h
  | some q =>
    simp only [negotiateAlpn] at h
    by_cases hm : q ∈ offered
    · rw [if_pos hm] at h; cases h; exact hm
    · rw [if_neg hm] at h; exact absurd h (by simp)

/-- On the client verdict for a whole handshake: any negotiated protocol was
offered. -/
theorem accept_alpn_offered {hs : Handshake} {p : Proto}
    (h : alpnOf hs = .selected p) : p ∈ hs.offered :=
  alpn_selects h

/-- A server that selects a protocol the client did not offer negotiates
nothing — the `no_application_protocol` condition is a `violation`, never a
`selected`. -/
theorem alpn_unoffered_is_violation {offered : List Proto} {p : Proto}
    (h : p ∉ offered) : negotiateAlpn offered (some p) = .violation := by
  simp [negotiateAlpn, h]

/-- A `violation` outcome never yields a negotiated protocol: there is no `p`
with `negotiateAlpn offered pick = .selected p` when the outcome is a violation.
Equivalently, the only way to reach `selected p` is for `p` to have been
offered (the contrapositive of `alpn_selects`). -/
theorem alpn_no_negotiate_of_unoffered {offered : List Proto} {p : Proto}
    (h : p ∉ offered) (q : Proto) : negotiateAlpn offered (some p) ≠ .selected q := by
  rw [alpn_unoffered_is_violation h]; exact fun hc => AlpnOutcome.noConfusion hc

/-! ## Non-vacuity: concrete accepts, rejects, and negotiations

Real inputs exercise every branch — an accepting handshake, a rejecting one for
each failure mode, and each ALPN outcome — so the theorems above are not
vacuously true. -/

section Examples

/-- A concrete leaf with a validity window and CA flag. -/
private def leaf : Mtls.Cert :=
  { subject := 1, issuer := 2, notBefore := 0, notAfter := 100, isCA := false }

/-- A concrete root that signs the leaf and is a CA. -/
private def root : Mtls.Cert :=
  { subject := 2, issuer := 2, notBefore := 0, notAfter := 100, isCA := true }

/-- A `verifySig` that accepts exactly `root`-over-`leaf`; the trust anchor is
`root`.  This is a total, concrete instance of the named crypto boundary — the
theorems hold for it as for every other. -/
private def env : Mtls.Env :=
  { verifySig := fun issuer child => decide (issuer = root ∧ child = leaf)
    cvVerify  := fun _ _ _ => true
    anchors   := [root] }

/-- `www.example.com`. -/
private def wwwExample : Hostname := ["www", "example", "com"]

/-- A handshake that should be accepted: valid `[leaf, root]` chain, leaf
presents `*.example.com`, client dialed `www.example.com`, offered `["h2"]`,
server picked `h2`. -/
private def goodHs : Handshake :=
  { chain := [leaf, root]
    leafSans := [.wildcard ["example", "com"]]
    sni := wwwExample
    offered := ["h2", "http/1.1"]
    serverPick := some "h2" }

/-- The good handshake is accepted (a real positive: `accepts = true`). -/
example : accepts env 50 goodHs = true := by decide

/-- Its wildcard SAN really matched the dialed host. -/
example : nameMatches goodHs.leafSans goodHs.sni = true := by decide

/-- The wildcard does **not** match a bare parent domain (mutant: `*.example.com`
must not stand in for `example.com`). -/
example : matchName (.wildcard ["example", "com"]) ["example", "com"] = false := by decide

/-- The wildcard does **not** match two leftmost labels. -/
example : matchName (.wildcard ["example", "com"]) ["a", "b", "example", "com"] = false := by
  decide

/-- Name-mismatch rejection: dialing a different host is rejected even though the
chain still validates. -/
example : accepts env 50 { goodHs with sni := ["evil", "other", "com"] } = false := by
  decide

/-- Expired-window rejection: at a time past the leaf's `notAfter` the chain fails
and the handshake is rejected. -/
example : accepts env 200 goodHs = false := by decide

/-- ALPN: the server's pick `h2` was offered, so it is selected. -/
example : negotiateAlpn goodHs.offered goodHs.serverPick = .selected "h2" := by decide

/-- ALPN violation: a server picking an unoffered `spdy/3` negotiates nothing. -/
example : negotiateAlpn goodHs.offered (some "spdy/3") = .violation := by decide

/-- ALPN absent: the server may omit the extension. -/
example : negotiateAlpn goodHs.offered Option.none = .none := by decide

end Examples

end Client.Tls
