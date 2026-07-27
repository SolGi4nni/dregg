/-
# Proxy.ConnectMitm — PARITY row conn.2: CONNECT MITM interception (TLS termination)

Row conn.1 (`ProxyConnectTunnel`) covers the *blind* CONNECT tunnel: once the
`200` is sent the edge forwards bytes verbatim in both directions and never
inspects them. Row conn.2 is the opposite disposition of the same CONNECT: when
the target is on the MITM allowlist, the edge does **not** blind-relay — it
*terminates* the client's TLS locally (so the proxy holds the plaintext for
inspection), then *re-establishes* a distinct TLS session to the real upstream
and re-encrypts. A target that is **not** configured for interception falls back
to the row-conn.1 blind relay, unchanged.

This leaf models the interception *decision and session structure* — which
disposition a CONNECT takes, and that an intercepted tunnel is genuinely two
distinct TLS legs with the proxy in the clear between them. It proves:

  * `connect_mitm_terminates_tls` — a target on the MITM allowlist is
    intercepted (not blind-relayed): the outcome is a terminated client leg with
    the proxy holding the decrypted plaintext (`plaintextVisible = true`).
  * `connect_mitm_reencrypts` — the intercepted tunnel is two *distinct* TLS
    sessions: the client-facing leg and the upstream-facing leg carry different
    session ids, both established, and the upstream leg terminates against the
    real target host (the proxy re-encrypts to the genuine upstream).
  * `connect_mitm_only_configured` — a target absent from the allowlist is
    *blind-relayed*, not intercepted: the outcome is the row-conn.1 opened
    `Tunnel`, whose relay is byte-verbatim (reusing `open_relay_faithful_up`),
    and never an intercepted tunnel.

No crypto is modeled: "TLS terminated at the proxy" is the decision plus the
plaintext-visibility flag; "distinct sessions" is distinct session ids by
construction; the handshake bytes, cert minting, and key exchange are the host's
(the leaf-cert minting orchestration is proven separately in the forward-proxy
module). The two legs' session ids are derived (`2·seed`, `2·seed+1`) so their
distinctness is a *proved* fact, not an assumption.
-/

import Reactor.Proxy.Connect

namespace Proxy.ConnectMitm

open Reactor.Proxy.Connect

/-- The MITM policy: the set of hosts the edge is configured to intercept. A
CONNECT whose target host is on this list has its TLS terminated at the proxy;
any other host is blind-relayed (row conn.1). Modeled as the `include` list of
the forward-proxy MITM config. -/
structure MitmPolicy where
  hosts : List String
deriving Repr

/-- Is this target configured for interception? Exact-host membership of the
allowlist. (Glob/suffix matching is a config-surface extension, not load-bearing
here — the disposition hinges only on membership.) -/
def MitmPolicy.intercepts (p : MitmPolicy) (t : Target) : Bool :=
  p.hosts.contains t.host

/-- One TLS leg of an intercepted tunnel: which peer it terminates against, its
distinct session id, and whether the handshake has completed. -/
structure TlsLeg where
  peer : String
  sessionId : Nat
  established : Bool
deriving DecidableEq, Repr

/-- An intercepted CONNECT: the client-facing TLS leg (terminated *at the
proxy*), the upstream-facing TLS leg (a fresh session to the real host), and the
fact that the proxy holds the decrypted application plaintext in between. -/
structure MitmTunnel where
  target : Target
  clientLeg : TlsLeg
  upstreamLeg : TlsLeg
  plaintextVisible : Bool
deriving DecidableEq, Repr

/-- The disposition of a CONNECT: either intercepted (TLS terminated at the
proxy) or blind-relayed via the row-conn.1 opened `Tunnel`. -/
inductive Outcome where
  | intercepted (m : MitmTunnel)
  | relayed (tun : Tunnel)
deriving DecidableEq, Repr

/-- Build the two-legged intercepted tunnel for `t` from a session `seed`. The
client leg is the proxy↔client session (`2·seed`); the upstream leg is a *fresh*
proxy↔upstream session (`2·seed+1`) whose peer is the genuine target host. Both
legs are established and the proxy sees the plaintext. The odd/even split makes
the two session ids distinct by construction. -/
def buildIntercept (t : Target) (seed : Nat) : MitmTunnel :=
  { target := t
    clientLeg := { peer := "client", sessionId := 2 * seed, established := true }
    upstreamLeg := { peer := t.host, sessionId := 2 * seed + 1, established := true }
    plaintextVisible := true }

/-- **The conn.2 disposition.** A CONNECT to a target on the MITM allowlist is
intercepted (its TLS terminated at the proxy, two distinct sessions built); any
other target is blind-relayed with the row-conn.1 opened `Tunnel`. -/
def handleConnect (p : MitmPolicy) (t : Target) (seed : Nat) : Outcome :=
  if p.intercepts t then .intercepted (buildIntercept t seed)
  else .relayed Tunnel.opened

/-! ## conn.2 theorems -/

/-- **conn.2 — a configured CONNECT terminates TLS at the proxy.** When the
target is on the MITM allowlist, the CONNECT is *intercepted*: the outcome is a
terminated tunnel whose client leg is established at the proxy and whose proxy
holds the decrypted plaintext for inspection — it is not the blind relay of row
conn.1. The `intercepts t = true` hypothesis is a real allowlist-membership fact
(the mutant below shows the disposition genuinely depends on it), not `P → P`. -/
theorem connect_mitm_terminates_tls {p : MitmPolicy} {t : Target} {seed : Nat}
    (hcfg : p.intercepts t = true) :
    ∃ m, handleConnect p t seed = .intercepted m
      ∧ m.plaintextVisible = true
      ∧ m.clientLeg.established = true
      ∧ (∀ tun, handleConnect p t seed ≠ .relayed tun) := by
  refine ⟨buildIntercept t seed, ?_, rfl, rfl, ?_⟩
  · simp [handleConnect, hcfg]
  · intro tun; simp [handleConnect, hcfg]

/-- **conn.2 — re-encryption to the upstream is a distinct session.** An
intercepted CONNECT is two *different* TLS sessions: the client-facing leg and
the upstream-facing leg carry different session ids, both handshakes complete,
and the upstream leg terminates against the genuine target host — i.e. the proxy
does not splice one session end-to-end, it decrypts and re-encrypts across two.
The `intercepts t = true` hypothesis is load-bearing (an unconfigured target has
no such tunnel — see `connect_mitm_only_configured`). -/
theorem connect_mitm_reencrypts {p : MitmPolicy} {t : Target} {seed : Nat}
    (hcfg : p.intercepts t = true) :
    ∃ m, handleConnect p t seed = .intercepted m
      ∧ m.clientLeg.sessionId ≠ m.upstreamLeg.sessionId
      ∧ m.clientLeg.established = true
      ∧ m.upstreamLeg.established = true
      ∧ m.upstreamLeg.peer = t.host := by
  refine ⟨buildIntercept t seed, ?_, ?_, rfl, rfl, rfl⟩
  · simp [handleConnect, hcfg]
  · simp only [buildIntercept]; omega

/-- **conn.2 — only configured targets are intercepted.** A target *absent* from
the MITM allowlist is blind-relayed, not intercepted: the outcome is exactly the
row-conn.1 opened `Tunnel` (whose relay is byte-verbatim, reusing
`open_relay_faithful_up`), and it is never an intercepted tunnel — the proxy
never holds that target's plaintext. The `intercepts t = false` hypothesis is a
real non-membership fact. -/
theorem connect_mitm_only_configured {p : MitmPolicy} {t : Target} {seed : Nat}
    (hnot : p.intercepts t = false) :
    handleConnect p t seed = .relayed Tunnel.opened
      ∧ (∀ m, handleConnect p t seed ≠ .intercepted m)
      ∧ ∀ b : List UInt8, (Tunnel.opened.pumpUp b).c2u = b := by
  refine ⟨?_, ?_, ?_⟩
  · simp [handleConnect, hnot]
  · intro m; simp [handleConnect, hnot]
  · intro b; exact open_relay_faithful_up b

/-! ## Mutant — the allowlist is load-bearing

A mutant handler that intercepts *every* target (ignoring the policy) would
break `connect_mitm_only_configured`: it would hold the plaintext of a target the
policy never authorized for interception. We witness that the real handler's
disposition genuinely depends on the allowlist. -/

/-- The mutant: intercept regardless of policy. -/
def handleConnectMutant (t : Target) (seed : Nat) : Outcome :=
  .intercepted (buildIntercept t seed)

/-- **The allowlist is load-bearing.** For a target *not* on the allowlist, the
real handler blind-relays while the policy-ignoring mutant intercepts — they
disagree exactly where the policy says "do not intercept". (If instead the target
were configured, both would intercept the same tunnel and agree — so the
`intercepts t = false` hypothesis is essential, i.e. non-vacuous.) -/
theorem policy_load_bearing {p : MitmPolicy} {t : Target} {seed : Nat}
    (hnot : p.intercepts t = false) :
    handleConnect p t seed ≠ handleConnectMutant t seed := by
  simp [handleConnect, handleConnectMutant, hnot]

/-! ## Non-vacuity: concrete intercept / relay dispositions

These witnesses are discharged by kernel `decide`: no `native_decide`, no
`Lean.ofReduceBool`. (An earlier note here justified `native_decide` by claiming
String host equality "does not reduce in the kernel". That was false — `String.decEq`
on literals reduces in the kernel fine. The real kernel walls in this repo are
`ByteArray.toList` and the well-founded `String` worker loops, documented in
`Proto.Kernel.Shortcuts`; these witnesses touch neither.) They remain only witnesses —
the load-bearing content is the four theorems above, proven by `simp`/`omega` over
abstract membership hypotheses. -/

/-- A policy that intercepts only `corp.internal`. -/
def demoPolicy : MitmPolicy := { hosts := ["corp.internal"] }

/-- A configured target is genuinely on the allowlist. -/
example : demoPolicy.intercepts { host := "corp.internal", port := 443 } = true := by
  decide

/-- An unconfigured target is genuinely off the allowlist. -/
example : demoPolicy.intercepts { host := "bank.example", port := 443 } = false := by
  decide

/-- A configured target is intercepted, with the proxy holding the plaintext and
two distinct sessions (`0` client / `1` upstream from seed `0`). -/
example :
    handleConnect demoPolicy { host := "corp.internal", port := 443 } 0
      = .intercepted
        { target := { host := "corp.internal", port := 443 }
          clientLeg := { peer := "client", sessionId := 0, established := true }
          upstreamLeg := { peer := "corp.internal", sessionId := 1, established := true }
          plaintextVisible := true } := by decide

/-- An unconfigured target is blind-relayed with the row-conn.1 opened tunnel —
the proxy never sees its plaintext. -/
example :
    handleConnect demoPolicy { host := "bank.example", port := 443 } 0
      = .relayed Tunnel.opened := by decide

end Proxy.ConnectMitm
