import Policy.Model

/-!
# Dsl.Cfg.Listener — the listener dimension of a deployment

A deployment binds one or more **listeners**: an accept surface (address/port),
the protocols it offers, and the admission state that gates the requests arriving
on it. This file owns ONLY that dimension, as a standalone structure, so a grow
lane extending listener configuration (new bind options, per-listener protocol
toggles, an admission surface) edits this file and no other.

The two load-bearing fields for the deployed serve are `id` (the listener
identity the `Policy` admission layer attributes a request to — `AppConfig.lid`)
and `policy` (the live `Policy.Running` snapshot admission decisions read). The
remaining fields are the declarative accept surface: they describe HOW the
listener is bound by the IO boundary and are not consulted by the pure
byte-pipeline, so they are skeletons the transport grow lanes fill.
-/

namespace Dsl.Cfg

/-! ## The layer-4 passthrough kind

Most listeners parse HTTP and drive the request pipeline. A **layer-4 listener**
does not: it accepts a connection (or a datagram), asks the load balancer for an
upstream, and moves bytes verbatim to it — the `mode tcp` / `stream {}` posture
of a general-purpose proxy, for protocols the HTTP engine has no business reading
(databases, message queues, TLS-passthrough SNI backends, bespoke wire
protocols). The proven forwarding model is `Reactor.L4`; the running host shell
is `crates/dataplane/src/l4.rs`; the upstream CHOICE is the same proven
`Proxy.selectChain` pick the reverse proxy uses (`Reactor.ProxyDial`). -/

/-- The transport a layer-4 passthrough listener splices. -/
inductive L4Mode where
  /-- Raw TCP stream passthrough: accept, dial the pick, splice both directions
  verbatim until each side finishes (`Reactor.L4.stepTcp`). -/
  | tcp
  /-- UDP datagram passthrough: each client datagram goes boundary-preserved to
  the pick, replies return to the client (`Reactor.L4.udpStep`). -/
  | udp
deriving Repr, DecidableEq

/-- A layer-4 passthrough binding: the named upstream pool (`Dsl.Cfg.UpstreamPool.name`)
the balancer selects over, and the transport spliced. No HTTP is parsed on an L4
listener — bytes move verbatim, and the only decision is which upstream to dial,
made by the proven pick. -/
structure L4Passthrough where
  /-- The upstream pool this listener forwards to (by `UpstreamPool.name`). -/
  upstream : String
  /-- Raw TCP stream or UDP datagram passthrough. -/
  mode : L4Mode := .tcp
deriving Repr

/-- One listener in a deployment: an admission identity + state plus the
declarative accept surface. `id`/`policy` feed the `AppConfig` admission seam;
the accept-surface fields are the extension point for the transport lanes.

When `l4` is `some p`, this listener is a **layer-4 passthrough** to the named
upstream pool `p.upstream`: it parses no HTTP, and the running dataplane binds it
via `crates/dataplane/src/l4.rs`, dialing the proven `Reactor.ProxyDial` pick and
splicing bytes verbatim. When `l4` is `none` it is an ordinary HTTP listener and
`id`/`policy`/the accept surface below apply as before. -/
structure ListenerCfg where
  /-- The listener identity the policy layer attributes requests to (→ `AppConfig.lid`). -/
  id : Nat
  /-- The live admission state (→ `AppConfig.policy`). -/
  policy : Policy.Running
  /-- Declarative bind address (accept surface; filled by the transport lane). -/
  addr : String := ""
  /-- Declarative bind port (accept surface; filled by the transport lane). -/
  port : Nat := 0
  /-- Offer HTTP/2 (`h2`/`h2c`) on this listener. -/
  offerH2 : Bool := true
  /-- Offer HTTP/3 (QUIC) on this listener. -/
  offerH3 : Bool := false
  /-- The name of the TLS profile (see `Dsl.Cfg.Tls`) this listener terminates
  with, if any; `none` is a cleartext listener. -/
  tlsProfile : Option String := none
  /-- When `some p`, this is a layer-4 passthrough listener to upstream pool
  `p.upstream` (no HTTP parsing); when `none`, an ordinary HTTP listener. -/
  l4 : Option L4Passthrough := none

/-- Is this a layer-4 passthrough listener (raw TCP/UDP, no HTTP parsing)? -/
def ListenerCfg.isL4 (l : ListenerCfg) : Bool := l.l4.isSome

/-- The upstream pool name a layer-4 listener forwards to, if it is one. -/
def ListenerCfg.l4Upstream (l : ListenerCfg) : Option String := l.l4.map (·.upstream)

/-- A default HTTP listener carries no L4 binding, so `isL4` is `false` — the
existing deployment surface is unchanged unless a listener sets `l4`. -/
@[simp] theorem isL4_none (l : ListenerCfg) (h : l.l4 = none) : l.isL4 = false := by
  simp [ListenerCfg.isL4, h]

/-- An L4 listener's declared upstream is exactly the pool named in its binding. -/
@[simp] theorem l4Upstream_some (l : ListenerCfg) (p : L4Passthrough) (h : l.l4 = some p) :
    l.l4Upstream = some p.upstream := by
  simp [ListenerCfg.l4Upstream, h]

end Dsl.Cfg
