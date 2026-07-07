import Dsl.Cfg.Tls
import TlsHandshake

/-!
# Dsl.Cfg.TlsServe — the config profile READ by the TLS handshake terminator

`Dsl.Cfg.Tls` declares a deployment's TLS termination profiles (`TlsProfile`):
the cert pool (per-SNI selectors), the OCSP-staple toggle, the resumption / 0-RTT
window, ALPN, and the version floor. `applyProfile` there resolves the two
*record-layer* toggles the sans-IO `Tls.Config` exposes (`ktls`,
`earlyDataAccepted`). But the richer handshake policy — WHICH certificate to
present, WHETHER to staple OCSP, WHETHER to accept 0-RTT and with what window —
lives in `TlsHandshake.ServerParams`, the value the deployed handshake terminator
(`TlsHandshake.serverStep`, driven by `TlsHandshake.WireOracle`) actually reads.

This file is the READ: `TlsProfile.applyServerParams` overrides exactly the
handshake-policy fields of a base `ServerParams` from a profile, so the deployed
terminator selects its cert / OCSP / 0-RTT behaviour PER THE CONFIG PROFILE:

* **0-RTT** — a profile that does not enable 0-RTT pins the anti-replay gate shut
  (`earlyDataOk := fun _ => false`) and zeroes the advertised window, so
  `TlsHandshake.earlyGate` can NEVER open (`applied_off_gate_closed`); a profile
  that enables it keeps the deployment's replay register and advertises the
  profile's window (`applied_on_window`). A 0-RTT-on and a 0-RTT-off profile
  therefore drive OBSERVABLY different handshakes off the same base
  (`profiles_differ_on_early`).
* **OCSP** — a profile with stapling off clears the staple
  (`applied_off_no_staple`), so `TlsHandshake.buildCertificateStapled` presents no
  status_request response; stapling on preserves it.

Because these are the very fields `serverStep` consults (`params.earlyDataOk`
inside `earlyGate`, `entry.ocspStaple` inside the Certificate flight), the config
knob is a live handshake input, not a decorative field.
-/

namespace Dsl.Cfg

open TlsHandshake (ServerParams CertEntry earlyGate)

/-- **The handshake-policy read.** Override a base `ServerParams`'s 0-RTT and OCSP
policy from a profile, leaving the crypto seams (`ephemeralPriv`, `p256Dh`,
`certSeed`, the cert material) untouched:

* 0-RTT is accepted only if the profile enables it — otherwise the anti-replay
  gate is pinned shut and the advertised early-data window is zeroed;
* the advertised window, when 0-RTT is on, is the profile's `maxEarlyDataSize`;
* the OCSP staple is presented only if the profile enables stapling. -/
def TlsProfile.applyServerParams (p : TlsProfile) (base : ServerParams) : ServerParams :=
  { base with
      earlyDataOk  := if p.zeroRtt then base.earlyDataOk else (fun _ => false)
      maxEarlyData := if p.zeroRtt then p.resumption.maxEarlyDataSize else 0
      ocspStaple   := if p.ocsp.staple then base.ocspStaple else none }

/-! ## The overridden fields are exactly the profile's policy (no drift) -/

@[simp] theorem applyServerParams_maxEarlyData_on (p : TlsProfile) (base : ServerParams)
    (h : p.zeroRtt = true) :
    (p.applyServerParams base).maxEarlyData = p.resumption.maxEarlyDataSize := by
  simp [TlsProfile.applyServerParams, h]

@[simp] theorem applyServerParams_maxEarlyData_off (p : TlsProfile) (base : ServerParams)
    (h : p.zeroRtt = false) :
    (p.applyServerParams base).maxEarlyData = 0 := by
  simp [TlsProfile.applyServerParams, h]

/-- The crypto seams are untouched — the profile selects policy, never the key
material. -/
theorem applyServerParams_certSeed (p : TlsProfile) (base : ServerParams) :
    (p.applyServerParams base).certSeed = base.certSeed := rfl
theorem applyServerParams_ephemeral (p : TlsProfile) (base : ServerParams) :
    (p.applyServerParams base).ephemeralPriv = base.ephemeralPriv := rfl

/-! ## 0-RTT: the profile toggle gates the handshake -/

/-- **A profile with 0-RTT off pins the anti-replay gate false**: the deployed
`earlyGate` — the handshake's §4.2.10/§8 acceptance decision — can NEVER open
under such a profile, no matter the ClientHello, ticket, or retry state. This is
the config toggle reaching the real handshake decision, since `earlyGate` reads
`params.earlyDataOk`. -/
theorem applied_off_gate_closed (p : TlsProfile) (base : ServerParams)
    (hp : p.zeroRtt = false) (retried : Option TlsHandshake.Retry)
    (ch : TlsHandshake.ClientHello) (suite : Nat) (alpnSel : Option Tls.Bytes)
    (info? : Option TlsHandshake.TicketInfo) :
    earlyGate (p.applyServerParams base) retried ch suite alpnSel info? = false := by
  unfold earlyGate TlsProfile.applyServerParams
  simp only [hp, if_false]
  cases ch.psk <;> simp

/-- **A profile with 0-RTT on advertises the profile's window** and keeps the
deployment's own anti-replay gate — so 0-RTT acceptance is exactly what the base
register decides, and the ticket advertises the config window. -/
theorem applied_on_window (p : TlsProfile) (base : ServerParams)
    (hp : p.zeroRtt = true) :
    (p.applyServerParams base).maxEarlyData = p.resumption.maxEarlyDataSize
      ∧ (p.applyServerParams base).earlyDataOk = base.earlyDataOk := by
  refine ⟨by simp [TlsProfile.applyServerParams, hp], ?_⟩
  simp [TlsProfile.applyServerParams, hp]

/-- **Two profiles, two handshakes.** Off the SAME base terminator, a 0-RTT-on and
a 0-RTT-off profile disagree on the advertised early-data window — and the off
profile's gate is provably shut while the on profile's gate is the base register's
(so, on a base that admits some identity, the two profiles disagree on that
identity's acceptance too). Different config, different verified handshake. -/
theorem profiles_differ_on_early (on off : TlsProfile) (base : ServerParams)
    (hon : on.zeroRtt = true) (hoff : off.zeroRtt = false)
    (hwin : 0 < on.resumption.maxEarlyDataSize) :
    (on.applyServerParams base).maxEarlyData ≠ (off.applyServerParams base).maxEarlyData := by
  rw [applyServerParams_maxEarlyData_on on base hon,
      applyServerParams_maxEarlyData_off off base hoff]
  omega

/-- The two profiles disagree on 0-RTT acceptance for an identity the base
register admits: the on-profile accepts it (base gate), the off-profile refuses
every identity. -/
theorem profiles_differ_on_gate (on off : TlsProfile) (base : ServerParams)
    (hon : on.zeroRtt = true) (hoff : off.zeroRtt = false)
    (id : Tls.Bytes) (hadmit : base.earlyDataOk id = true) :
    (on.applyServerParams base).earlyDataOk id = true
      ∧ (off.applyServerParams base).earlyDataOk id = false := by
  refine ⟨?_, ?_⟩
  · rw [(applied_on_window on base hon).2]; exact hadmit
  · simp [TlsProfile.applyServerParams, hoff]

/-! ## OCSP: the profile toggle gates the staple -/

/-- **A profile with stapling off presents no OCSP staple**: `ocspStaple` is
cleared, so the deployed Certificate flight carries no status_request response. -/
theorem applied_off_no_staple (p : TlsProfile) (base : ServerParams)
    (h : p.ocsp.staple = false) : (p.applyServerParams base).ocspStaple = none := by
  simp [TlsProfile.applyServerParams, h]

/-- **A profile with stapling on preserves the staple.** -/
theorem applied_on_staple (p : TlsProfile) (base : ServerParams)
    (h : p.ocsp.staple = true) :
    (p.applyServerParams base).ocspStaple = base.ocspStaple := by
  simp [TlsProfile.applyServerParams, h]

/-! ## Cert pool: the profile's SNI selectors become servable entries

The handshake selects a certificate from `ServerParams.certs` by SNI host name
and the client's `signature_algorithms` (`TlsHandshake.chooseCert`). A profile's
`CertSelector`s name the SNI hosts the deployment serves; a host-supplied
resolver turns each selector's `certRef`/`keyRef` into the real DER material and
signing seam. `certEntriesFor` maps the profile's selectors to `CertEntry`s
carrying the profile's SNI names, so the deployed cert pool is the profile's. -/

/-- Turn a profile's SNI cert selectors into servable `CertEntry`s, given a
resolver from a selector to its concrete cert bytes / chain / signing seam. Each
entry carries the selector's SNI host as its name (`"*"` ⇒ name-agnostic). -/
def TlsProfile.certEntriesFor (p : TlsProfile)
    (resolve : CertSelector → CertEntry) : List CertEntry :=
  p.certs.map (fun sel =>
    let e := resolve sel
    { e with names := if sel.sni == "*" then [] else [sel.sni.toUTF8.toList] })

/-- Install the profile's cert pool into a base terminator (before the base's own
default entry). -/
def TlsProfile.installCerts (p : TlsProfile) (base : ServerParams)
    (resolve : CertSelector → CertEntry) : ServerParams :=
  { base with certs := p.certEntriesFor resolve }

/-- The number of servable entries the profile installs equals its selector
count — every declared per-SNI selector becomes a servable certificate. -/
theorem certEntriesFor_length (p : TlsProfile) (resolve : CertSelector → CertEntry) :
    (p.certEntriesFor resolve).length = p.certs.length := by
  simp [TlsProfile.certEntriesFor]

/-! ## Runnable evidence — the profile drives the terminator config -/

/-- A base terminator whose anti-replay register admits every identity and which
holds a staple — so the profile toggles are what turn them on or off. -/
def demoBase : ServerParams where
  ephemeralPriv := ByteArray.empty
  serverRandom := ByteArray.empty
  certSeed := ByteArray.empty
  certData := ByteArray.empty
  earlyDataOk := fun _ => true
  ocspStaple := some (ByteArray.mk #[0x30, 0x03])

/-- The 0-RTT-on public profile (from `Dsl.Cfg.Tls`) advertises its 16 KiB window
and keeps the base gate; the no-0-RTT profile zeroes the window and shuts the
gate. -/
def zeroRttOn : TlsProfile := internalMtls   -- earlyData := true, window 16384
def zeroRttOff : TlsProfile := publicWeb      -- earlyData := false

#guard (zeroRttOn.applyServerParams demoBase).maxEarlyData == 16384
#guard (zeroRttOff.applyServerParams demoBase).maxEarlyData == 0
#guard (zeroRttOn.applyServerParams demoBase).earlyDataOk [1, 2, 3] == true
#guard (zeroRttOff.applyServerParams demoBase).earlyDataOk [1, 2, 3] == false
-- OCSP: internalMtls staples, so the staple survives; a stapling-off variant clears it.
#guard ((zeroRttOn.applyServerParams demoBase).ocspStaple).isSome == true
#guard (({ zeroRttOn with ocsp := { staple := false } }).applyServerParams demoBase).ocspStaple.isSome == false
#eval do
  IO.println s!"tls profile drives 0-RTT: on -> window {(zeroRttOn.applyServerParams demoBase).maxEarlyData}, gate {(zeroRttOn.applyServerParams demoBase).earlyDataOk [1,2,3]}; off -> window {(zeroRttOff.applyServerParams demoBase).maxEarlyData}, gate {(zeroRttOff.applyServerParams demoBase).earlyDataOk [1,2,3]}"

#print axioms applied_off_gate_closed
#print axioms profiles_differ_on_gate

end Dsl.Cfg
