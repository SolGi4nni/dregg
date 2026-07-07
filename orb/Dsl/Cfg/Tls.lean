import Tls.Basic
import Reactor.Tls
import Dsl.Component

/-!
# Dsl.Cfg.Tls — the TLS-termination dimension of a deployment

A deployment declares zero or more **TLS profiles**: a named termination policy a
listener (`Dsl.Cfg.Listener.tlsProfile`) references by name, and — within a
profile — a per-SNI certificate selector matrix. A profile fixes the whole
handshake-configuration surface a front end terminates with:

* the offered protocol-version window (`minVersion`/`maxVersion`, RFC wire values);
* the cipher-suite preference (a named `CipherPreset` or an explicit suite list);
* the offered ALPN protocol set (`Tls.Alpn` identifiers, in preference order);
* the client-authentication mode (`ClientAuth`: none / requested / required — the
  mTLS switch) together with the trust anchors a required mode verifies against;
* the session-resumption surface (tickets, 0-RTT / early-data acceptance and its
  window size) — `ResumptionCfg`;
* the OCSP stapling surface (`OcspCfg`: staple / must-staple);
* the Certificate-Transparency surface (`CtCfg`: SCT requirement and count);
* the per-SNI certificate selectors (`CertSelector`: hostname → cert/key refs).

This file owns ONLY that dimension, as standalone structures, so a lane growing
TLS configuration edits this file alone.

## Where the dimension lands

TLS termination happens at the IO / handshake boundary (`Reactor.Tls`,
`TlsHandshake`), NOT inside the pure `Bytes → Bytes` middleware fold — so the TLS
dimension contributes **no** stages to `instantiate`'s stage-list output. Instead
it *selects* the options of the real, sans-IO TLS record machine: `applyProfile`
resolves a profile against a base `Tls.Config`, overriding exactly the two
record-layer toggles the machine exposes as data — kernel offload (`Tls.Config.ktls`)
and early-data / 0-RTT acceptance (`Tls.Config.earlyDataAccepted`) — and leaving
every crypto function-field untouched (a config transformer, in the shape of
`Reactor.TlsWire.wireTls`). `TlsCfg.tlsConfigFor` is the accept-boundary entry
point: given the listener's profile name, it produces the resolved `Tls.Config`.

## The transition-system guarantee

Profile *selection* is modeled as a `Dsl.Component` (`tlsSelector`): a labelled
transition system whose input is an SNI / profile-name query and whose state is
the currently negotiated profile. Its well-formedness invariant is that a
negotiated profile is always `WellFormed` — a decidable coherence predicate that
rules out ill-formed handshake configurations (an inverted version window, a
0-RTT profile without resumption tickets or below TLS 1.3, must-staple without
stapling, required-mTLS without a trust anchor, a terminator with no certificate).
Because the selector only ever lands on profiles it filtered for well-formedness,
the invariant is preserved on every step, and `Dsl.Component.reachable_inv` lifts
it to *every reachable negotiation*: a deployment can never negotiate an
ill-formed TLS configuration. Co-hosting two listeners is the parallel product of
two selectors (`Component.prod`); `prod_preserves` shows the conjoined invariant
survives, so neither listener's negotiation corrupts the other's.
-/

namespace Dsl.Cfg

/-! ## Named protocol-version constants (RFC 8446 / RFC 5246 wire values) -/

/-- TLS 1.2 legacy record version wire value. -/
def tls12 : Nat := 0x0303
/-- TLS 1.3 record version wire value. -/
def tls13 : Nat := 0x0304

/-! ## The sub-surfaces of a profile -/

/-- Cipher-suite preference policy. The named presets are the common hardened
tiers; `custom` carries an explicit ordered suite-id list. -/
inductive CipherPreset where
  /-- TLS 1.3 AEAD suites only (the modern tier). -/
  | modern
  /-- Modern plus widely-compatible TLS 1.2 ECDHE-AEAD suites. -/
  | intermediate
  /-- A broad-compatibility tier (legacy interop). -/
  | old
  /-- An explicit ordered list of cipher-suite wire ids. -/
  | custom (suites : List Nat)
deriving Repr, DecidableEq

/-- Client-certificate authentication (mTLS) mode for a listener terminating with
this profile. -/
inductive ClientAuth where
  /-- No client certificate is requested. -/
  | none
  /-- A client certificate is requested but the handshake proceeds without one
  (optional mTLS). -/
  | requested
  /-- A valid client certificate is mandatory; the handshake fails without one
  (required mTLS). -/
  | required
deriving Repr, DecidableEq

/-- Does a mode make a client certificate mandatory? -/
def ClientAuth.isRequired : ClientAuth → Bool
  | .required => true
  | _ => false

/-- The session-resumption surface: stateless tickets, and the 0-RTT
(early-data) acceptance window. -/
structure ResumptionCfg where
  /-- Offer session tickets (RFC 8446 NewSessionTicket) for stateless resumption. -/
  tickets : Bool := true
  /-- Accept 0-RTT early application data on a resumed handshake. Gated by
  well-formedness on `tickets` and a TLS-1.3 floor. -/
  earlyData : Bool := false
  /-- Maximum accepted early-data unit size (bytes); must be positive when
  `earlyData` is set. -/
  maxEarlyDataSize : Nat := 0
deriving Repr, DecidableEq

/-- The OCSP stapling surface. -/
structure OcspCfg where
  /-- Staple an OCSP response in the handshake (RFC 6066 status_request). -/
  staple : Bool := false
  /-- Advertise OCSP must-staple; requires `staple`. -/
  mustStaple : Bool := false
deriving Repr, DecidableEq

/-- The Certificate-Transparency surface. -/
structure CtCfg where
  /-- Require Signed Certificate Timestamps (RFC 6962) in the handshake. -/
  requireScts : Bool := false
  /-- Minimum number of independent SCTs demanded when `requireScts` is set. -/
  minScts : Nat := 0
deriving Repr, DecidableEq

/-- One per-SNI certificate selector: a hostname (exact, or the wildcard `"*"`)
mapped to the certificate and private-key material refs the terminator presents. -/
structure CertSelector where
  /-- The SNI hostname this selector serves (`"*"` matches any). -/
  sni : String
  /-- Reference to the certificate chain to present for this SNI. -/
  certRef : String
  /-- Reference to the private key for this SNI. -/
  keyRef : String
deriving Repr, DecidableEq

/-! ## The profile -/

/-- One named TLS termination profile: the full handshake-configuration surface a
listener terminates with. -/
structure TlsProfile where
  /-- The profile name a listener references (`ListenerCfg.tlsProfile`). -/
  name : String
  /-- Minimum offered protocol version (RFC wire value; `tls13` = `0x0304`). -/
  minVersion : Nat := tls13
  /-- Maximum offered protocol version (RFC wire value). -/
  maxVersion : Nat := tls13
  /-- Cipher-suite preference policy. -/
  cipher : CipherPreset := .modern
  /-- Offered ALPN protocol identifiers, in preference order. -/
  alpn : List Tls.Alpn := []
  /-- Client-authentication (mTLS) mode. -/
  clientAuth : ClientAuth := .none
  /-- Trust-anchor refs a required/requested client-auth mode verifies against. -/
  caRefs : List String := []
  /-- The session-resumption / 0-RTT surface. -/
  resumption : ResumptionCfg := {}
  /-- The OCSP stapling surface. -/
  ocsp : OcspCfg := {}
  /-- The Certificate-Transparency surface. -/
  ct : CtCfg := {}
  /-- Per-SNI certificate selectors (at least one — the terminator needs a cert). -/
  certs : List CertSelector := []
  /-- Attempt kernel record-layer offload after the handshake completes
  (`Tls.Config.ktls`). -/
  ktls : Bool := false
deriving Repr, DecidableEq

/-- Whether this profile accepts 0-RTT early data (drives
`Tls.Config.earlyDataAccepted`). -/
def TlsProfile.zeroRtt (p : TlsProfile) : Bool := p.resumption.earlyData

/-- **The coherence predicate (decidable, as a `Bool`).** A profile is well-formed
when its handshake configuration is internally consistent:

* the version window is ordered and within `[tls12, tls13]`;
* it selects at least one certificate (a terminator must present one);
* 0-RTT is only enabled with resumption tickets, a TLS-1.3 minimum, and a positive
  early-data window;
* OCSP must-staple implies stapling is on;
* requiring SCTs implies demanding at least one;
* required mTLS implies at least one configured trust anchor.

These are exactly the constraints whose violation would produce a downgrade
window, a replay-exposed 0-RTT surface, an unsatisfiable staple/CT promise, or an
mTLS gate that can never admit — the negation of each is a real misconfiguration. -/
def TlsProfile.wf (p : TlsProfile) : Bool :=
  Nat.ble tls12 p.minVersion
  && Nat.ble p.minVersion p.maxVersion
  && Nat.ble p.maxVersion tls13
  && !p.certs.isEmpty
  && (!p.resumption.earlyData
      || (p.resumption.tickets && (p.minVersion == tls13)
          && Nat.ble 1 p.resumption.maxEarlyDataSize))
  && (!p.ocsp.mustStaple || p.ocsp.staple)
  && (!p.ct.requireScts || Nat.ble 1 p.ct.minScts)
  && (!p.clientAuth.isRequired || !p.caRefs.isEmpty)

/-- Well-formedness as a `Prop` (the `Component` invariant carrier). -/
def TlsProfile.WellFormed (p : TlsProfile) : Prop := p.wf = true

instance (p : TlsProfile) : Decidable p.WellFormed := by
  unfold TlsProfile.WellFormed; infer_instance

/-- The certificate selector this profile presents for an SNI hostname: the exact
match if present, otherwise the wildcard `"*"` selector, otherwise none. Always a
member of `p.certs`. -/
def TlsProfile.certFor (p : TlsProfile) (host : String) : Option CertSelector :=
  match p.certs.find? (fun c => c.sni == host) with
  | some c => some c
  | none => p.certs.find? (fun c => c.sni == "*")

/-! ## The TLS dimension -/

/-- The TLS dimension: the set of named termination profiles a deployment offers.
Empty for a cleartext deployment. -/
structure TlsCfg where
  /-- The named profiles listeners select by name. -/
  profiles : List TlsProfile := []
deriving Repr

/-- Look a profile up by name (raw — may be ill-formed). -/
def TlsCfg.byName (cfg : TlsCfg) (name : String) : Option TlsProfile :=
  cfg.profiles.find? (fun p => p.name == name)

/-- **The well-formed resolver.** Select a profile by name, admitting it only if
it is well-formed. This is the sole way a profile enters a negotiation, so every
negotiated profile is well-formed by construction. -/
def TlsCfg.resolveWF (cfg : TlsCfg) (name : String) : Option TlsProfile :=
  cfg.profiles.find? (fun p => p.name == name && p.wf)

/-- Any profile the well-formed resolver returns is well-formed. -/
theorem TlsCfg.resolveWF_wf (cfg : TlsCfg) (name : String) {p : TlsProfile}
    (h : cfg.resolveWF name = some p) : p.WellFormed := by
  unfold TlsCfg.resolveWF at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true] at hp
  exact hp.2

/-! ## Honoring the dimension at the accept boundary: profile → `Tls.Config`

The sans-IO TLS record machine (`Tls.Config`) exposes its record-layer policy as
two data toggles — `ktls` (kernel offload) and `earlyDataAccepted` (0-RTT) —
alongside its uninterpreted crypto function-fields. A profile *selects* those
toggles; the crypto behind them is the terminator's, untouched. This is the
`instantiate`-honoring seam for the TLS dimension: it adds no pipeline stage, it
resolves the accept-boundary record config. -/

/-- Override a base `Tls.Config`'s record-layer toggles from a profile, leaving
every crypto function-field untouched (a config transformer). -/
def applyProfile (p : TlsProfile) (base : Tls.Config) : Tls.Config :=
  { base with ktls := p.ktls, earlyDataAccepted := p.zeroRtt }

@[simp] theorem applyProfile_ktls (p : TlsProfile) (base : Tls.Config) :
    (applyProfile p base).ktls = p.ktls := rfl

@[simp] theorem applyProfile_earlyData (p : TlsProfile) (base : Tls.Config) :
    (applyProfile p base).earlyDataAccepted = p.zeroRtt := rfl

/-- The crypto function-fields are untouched — the profile selects toggles, never
the cipher. -/
theorem applyProfile_hsFeed (p : TlsProfile) (base : Tls.Config) :
    (applyProfile p base).hsFeed = base.hsFeed := rfl
theorem applyProfile_recOpen (p : TlsProfile) (base : Tls.Config) :
    (applyProfile p base).recOpen = base.recOpen := rfl
theorem applyProfile_recSeal (p : TlsProfile) (base : Tls.Config) :
    (applyProfile p base).recSeal = base.recSeal := rfl
theorem applyProfile_extractSecrets (p : TlsProfile) (base : Tls.Config) :
    (applyProfile p base).extractSecrets = base.extractSecrets := rfl

/-- **The accept-boundary entry point.** Given a listener's TLS profile name,
resolve the deployment's TLS dimension against a base `Tls.Config`: a well-formed
named profile selects its record-layer toggles; an unknown/ill-formed name falls
back to the base config unchanged. This is what a `DeploymentConfig`-level
`tlsConfigFor` (or `instantiate`'s TLS projection) invokes. -/
def TlsCfg.tlsConfigFor (cfg : TlsCfg) (base : Tls.Config) (name : String) : Tls.Config :=
  match cfg.resolveWF name with
  | some p => applyProfile p base
  | none => base

/-! ## Profile selection as a component of the composition calculus -/

/-- The selection invariant on a negotiation state: a negotiated profile is always
well-formed. -/
def SelInv : Option TlsProfile → Prop
  | none => True
  | some p => p.WellFormed

/-- **The TLS profile selector as a `Dsl.Component`.** State: the currently
negotiated profile (`none` before the first handshake). Input: an SNI /
profile-name query. Step: resolve the query through `resolveWF` — which admits
only well-formed profiles — and emit the selection. The invariant `SelInv` (a
negotiated profile is well-formed) is preserved on every step, so
`Component.reachable_inv` proves every reachable negotiation is well-formed. -/
def tlsSelector (cfg : TlsCfg) : Dsl.Component where
  State := Option TlsProfile
  Input := String
  Output := Option TlsProfile
  inv := SelInv
  init := none
  step := fun _ name => let r := cfg.resolveWF name; (r, [r])
  init_wf := trivial
  step_wf := by
    intro _ name _
    show SelInv (cfg.resolveWF name)
    cases h : cfg.resolveWF name with
    | none => exact trivial
    | some p => exact cfg.resolveWF_wf name h

/-- **Every reachable negotiation is well-formed.** The invariant methodology
(`reachable_inv`) applied to the selector: no matter what sequence of SNI queries
a deployment services, it never negotiates an ill-formed TLS configuration. -/
theorem tlsSelector_reachable_wf (cfg : TlsCfg) {s : Option TlsProfile}
    (h : (tlsSelector cfg).Reachable s) : SelInv s :=
  (tlsSelector cfg).reachable_inv h

/-- **The punchline, in profile terms.** Any profile the selector lands on after
*any* sequence of queries is well-formed. -/
theorem tlsSelector_selected_wf (cfg : TlsCfg) (queries : List String)
    {p : TlsProfile} (h : (tlsSelector cfg).runState none queries = some p) :
    p.WellFormed := by
  have hreach : (tlsSelector cfg).Reachable (some p) := ⟨queries, h⟩
  exact tlsSelector_reachable_wf cfg hreach

/-- **Co-hosting two listeners is the parallel product of their selectors.** -/
def dualListenerSelector (a b : TlsCfg) : Dsl.Component :=
  (tlsSelector a).prod (tlsSelector b)

/-- **Two co-hosted listeners compose.** The product step preserves the conjoined
invariant: neither listener's negotiation can drive the other into an ill-formed
profile. -/
theorem dualListener_preserves (a b : TlsCfg) (s : (dualListenerSelector a b).State)
    (i : (dualListenerSelector a b).Input)
    (h : (dualListenerSelector a b).inv s) :
    (dualListenerSelector a b).inv ((dualListenerSelector a b).step s i).1 :=
  Dsl.prod_preserves (tlsSelector a) (tlsSelector b) s i h

/-- **A reachable co-hosted negotiation is well-formed on both listeners.** A
reachable product state is reachable in each factor (`prod_reachable`), and each
factor's reachable state is well-formed (`reachable_inv`). -/
theorem dualListener_reachable_wf (a b : TlsCfg)
    {s : (dualListenerSelector a b).State}
    (h : (dualListenerSelector a b).Reachable s) :
    SelInv s.1 ∧ SelInv s.2 := by
  obtain ⟨ha, hb⟩ := Dsl.prod_reachable (tlsSelector a) (tlsSelector b) s h
  exact ⟨(tlsSelector a).reachable_inv ha, (tlsSelector b).reachable_inv hb⟩

/-! ## A deployment the hardcoded serve could not express

The deployed serve terminates TLS with a single hardcoded `Reactor.TlsWire.demoTlsCfg`
whose record-layer toggles are pinned (`ktls = false`, `earlyDataAccepted = false`),
with no per-listener or per-SNI variation. The declarative dimension expresses a
whole TLS matrix. `dualStackTls` below carries two distinct profiles:

* `internalMtls` — TLS 1.3 only, `h2` only, **required mTLS**, kernel offload on,
  **0-RTT** accepted, must-staple + CT-required, two SNI certificate selectors; and
* `publicWeb` — TLS 1.2–1.3, `h2` + `http/1.1`, no client auth, no 0-RTT, stapling
  on, a single wildcard certificate.

Both are well-formed; each resolves to a *different* `Tls.Config` — something a
single pinned literal cannot do. -/

/-- The internal, mutually-authenticated, 0-RTT + kernel-offload profile. -/
def internalMtls : TlsProfile where
  name := "internal-mtls"
  minVersion := tls13
  maxVersion := tls13
  cipher := .modern
  alpn := [.h2]
  clientAuth := .required
  caRefs := ["internal-ca"]
  resumption := { tickets := true, earlyData := true, maxEarlyDataSize := 16384 }
  ocsp := { staple := true, mustStaple := true }
  ct := { requireScts := true, minScts := 2 }
  certs :=
    [ { sni := "svc.internal", certRef := "svc-cert", keyRef := "svc-key" }
    , { sni := "admin.internal", certRef := "admin-cert", keyRef := "admin-key" } ]
  ktls := true

/-- The public-facing, dual-version, dual-ALPN profile. -/
def publicWeb : TlsProfile where
  name := "public-web"
  minVersion := tls12
  maxVersion := tls13
  cipher := .intermediate
  alpn := [.h2, .h1]
  clientAuth := .none
  resumption := { tickets := true, earlyData := false }
  ocsp := { staple := true }
  certs := [ { sni := "*", certRef := "wildcard-cert", keyRef := "wildcard-key" } ]
  ktls := false

/-- The two-profile deployment TLS dimension. -/
def dualStackTls : TlsCfg := { profiles := [internalMtls, publicWeb] }

/-- Both declared profiles are well-formed. -/
theorem internalMtls_wf : internalMtls.WellFormed := by decide
theorem publicWeb_wf : publicWeb.WellFormed := by decide

/-- The resolver selects each profile by name. -/
theorem dualStack_resolves_internal :
    dualStackTls.resolveWF "internal-mtls" = some internalMtls := by decide
theorem dualStack_resolves_public :
    dualStackTls.resolveWF "public-web" = some publicWeb := by decide

/-- The per-SNI certificate selector picks the matching cert; the public profile's
wildcard selector serves any host. -/
theorem internal_certFor_admin :
    internalMtls.certFor "admin.internal"
      = some { sni := "admin.internal", certRef := "admin-cert", keyRef := "admin-key" } := by
  decide
theorem public_certFor_wildcard :
    publicWeb.certFor "anything.example"
      = some { sni := "*", certRef := "wildcard-cert", keyRef := "wildcard-key" } := by
  decide

/-- **The expressiveness gap, made concrete.** The deployed hardcoded TLS config
pins both record-layer toggles off; it cannot express a 0-RTT + kernel-offload
listener. -/
theorem demo_toggles_pinned :
    Reactor.TlsWire.demoTlsCfg.earlyDataAccepted = false
    ∧ Reactor.TlsWire.demoTlsCfg.ktls = false := ⟨rfl, rfl⟩

/-- Resolving the `internal-mtls` profile against that same base config yields a
`Tls.Config` with 0-RTT **and** kernel offload enabled — the exact configuration
the hardcoded literal cannot produce. -/
theorem internal_enables_0rtt_and_ktls :
    (dualStackTls.tlsConfigFor Reactor.TlsWire.demoTlsCfg "internal-mtls").earlyDataAccepted = true
    ∧ (dualStackTls.tlsConfigFor Reactor.TlsWire.demoTlsCfg "internal-mtls").ktls = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- The two profiles resolve to *different* record configs off the same base —
per-listener TLS variation the single pinned literal cannot express. `public-web`
keeps 0-RTT off while `internal-mtls` turns it on. -/
theorem per_listener_variation :
    (dualStackTls.tlsConfigFor Reactor.TlsWire.demoTlsCfg "public-web").earlyDataAccepted = false
    ∧ (dualStackTls.tlsConfigFor Reactor.TlsWire.demoTlsCfg "internal-mtls").earlyDataAccepted = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- The crypto boundary is preserved: selecting a profile never rewrites the base
config's handshake/record functions. -/
theorem tlsConfigFor_preserves_crypto :
    (dualStackTls.tlsConfigFor Reactor.TlsWire.demoTlsCfg "internal-mtls").hsFeed
      = Reactor.TlsWire.demoTlsCfg.hsFeed := rfl

end Dsl.Cfg
