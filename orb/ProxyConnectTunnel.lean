/-
# ProxyConnectTunnel — PARITY row conn.1: CONNECT tunnel (blind)

This leaf states the parity-ledger headline properties for the HTTP `CONNECT`
method (RFC 9110 §9.3.6) directly against the committed CONNECT model in
`Reactor.Proxy.Connect` (the admission gate + the blind bidirectional relay).
It adds no new model: it names, over the real proven definitions, the three
row-conn.1 obligations and a mutant that shows the gate is load-bearing.

  * `connect_authority_parsed` — the CONNECT request target is parsed into a
    structured `host:port` authority.
  * `connect_tunnel_blind` — a connected tunnel relays bytes verbatim in both
    directions, and nothing crosses before the tunnel is connected (i.e. the
    edge forwards application data blind after the `200`, and reads none before).
  * `connect_relay_verbatim` — the blindness core: for *any* connected tunnel,
    each pump appends the input bytes verbatim (no inspection, drop, or rewrite).
  * `connect_403_on_deny` — a target the ACL refuses yields `refused 403` and
    never a tunnel.

The transport (DNS, TCP handshake, the byte pump loop) is the host's; the model
is over structured targets and byte lists, per the committed module's boundary.
-/

import Reactor.Proxy.Connect

namespace ProxyConnectTunnel

open Reactor.Proxy.Connect

/-- **conn.1 — authority parsed.** When the request-line target splits on the
authority colon into a host and a numeric port, `parseTarget` recovers the
structured `host:port`. The hypotheses are the actual split/parse facts (a real
authority), not a tautology. -/
theorem connect_authority_parsed {s h p : String} {n : Nat}
    (hsplit : s.splitOn ":" = [h, p]) (hport : p.toNat? = some n) :
    parseTarget s = some { host := h, port := n } := by
  simp [parseTarget, hsplit, hport]

set_option cbv.maxSteps 20000 in
/-- Concrete non-vacuity witness for the parse, discharged in the pure kernel: the
authority split runs through the `Proto.Kernel.Shortcuts` §3 `splitOnAux` step kit, and
the port parse is call-by-value KERNEL evaluation (`cbv`, under an explicit step budget).
Both are kernel reduction — the compiler is nowhere, so no `Lean.ofReduceBool` enters the
TCB. It instantiates the hypotheses of `connect_authority_parsed` on a real authority — a
live sanity check that the general theorem is not vacuous.
Axioms ⊆ {propext, Classical.choice, Quot.sound}. -/
theorem connect_authority_parsed_witness :
    parseTarget "api.internal:443" = some { host := "api.internal", port := 443 } := by
  have hsplit : "api.internal:443".splitOn ":" = ["api.internal", "443"] := by
    simp (config := { decide := true }) only [String.splitOn,
      Proto.Kernel.Shortcuts.splitOnAux_stop, Proto.Kernel.Shortcuts.splitOnAux_matchend,
      Proto.Kernel.Shortcuts.splitOnAux_miss]
  have hport : "443".toNat? = some 443 := by cbv
  exact connect_authority_parsed hsplit hport

/-- **Blindness core.** For *any* connected tunnel, pumping bytes appends them
verbatim in each direction — the relay never inspects, filters, or rewrites the
application data. The `connected = true` hypothesis is load-bearing. -/
theorem connect_relay_verbatim (tun : Tunnel) (b : List UInt8)
    (hc : tun.connected = true) :
    (tun.pumpUp b).c2u = tun.c2u ++ b ∧ (tun.pumpDown b).u2c = tun.u2c ++ b := by
  refine ⟨?_, ?_⟩ <;> simp [Tunnel.pumpUp, Tunnel.pumpDown, hc]

/-- **conn.1 — blind bidirectional tunnel.** Once the tunnel is connected the
edge relays exactly the bytes it is handed, in both directions (`c2u`/`u2c`),
and before it is connected no application byte crosses. This is RFC 9110's
"blind forwarding of data, in both directions": the proxy reads no application
data of its own after the `200`, and none is forwarded before it. -/
theorem connect_tunnel_blind (b : List UInt8) :
    (Tunnel.gated.pumpUp b).c2u = [] ∧
    (Tunnel.gated.pumpDown b).u2c = [] ∧
    (Tunnel.opened.pumpUp b).c2u = b ∧
    (Tunnel.opened.pumpDown b).u2c = b := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Tunnel.pumpUp, Tunnel.pumpDown, Tunnel.gated, Tunnel.opened]

/-- **conn.1 — deny ⇒ 403, not tunneled.** A target the ACL refuses
(`check t = false`) decides to `refused 403` and to no tunnel whatsoever. The
`check t = false` hypothesis is a real admission fact, not `P → P`. -/
theorem connect_403_on_deny {a : Acl} {t : Target} (hdeny : a.check t = false) :
    Reactor.Proxy.Connect.decide a t = .refused 403 ∧
    ∀ t', Reactor.Proxy.Connect.decide a t ≠ .tunnel t' := by
  have hd : Reactor.Proxy.Connect.decide a t = .refused 403 := by
    simp [Reactor.Proxy.Connect.decide, hdeny]
  refine ⟨hd, ?_⟩
  intro t'; rw [hd]; intro h; exact Verdict.noConfusion h

/-! ## Mutant — the gate is load-bearing

If the gate were mutated to open a tunnel on a denied target,
`connect_403_on_deny` would be false. This witnesses that it is not vacuous: the
default-deny ACL genuinely refuses (a tunnel here would be the mutant), while a
matching allow genuinely tunnels — the verdict actually depends on admission. -/

/-- The denied target under the default ACL is refused — a tunnel would be the
mutant (decidable, evaluates without `native_decide`). -/
theorem connect_deny_mutant :
    Reactor.Proxy.Connect.decide Acl.denyAll { host := "evil.example", port := 22 }
      ≠ .tunnel { host := "evil.example", port := 22 } := by decide

/-- Dually, a matching allow does open the tunnel — so the refusal above is a
real decision, not a constant. -/
example : Reactor.Proxy.Connect.decide Acl.httpsOnly { host := "api.internal", port := 443 }
    = .tunnel { host := "api.internal", port := 443 } := rfl

end ProxyConnectTunnel

#print axioms ProxyConnectTunnel.connect_authority_parsed
#print axioms ProxyConnectTunnel.connect_authority_parsed_witness
#print axioms ProxyConnectTunnel.connect_relay_verbatim
#print axioms ProxyConnectTunnel.connect_tunnel_blind
#print axioms ProxyConnectTunnel.connect_403_on_deny
#print axioms ProxyConnectTunnel.connect_deny_mutant
