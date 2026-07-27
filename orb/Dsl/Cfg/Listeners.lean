import Policy.Model
import Policy.Invariant
import Dsl.Component
import Dsl.Cfg.Listener

/-!
# Dsl.Cfg.Listeners — the multi-listener accept dimension of a deployment

A real deployment binds **many** listeners at once: a plaintext HTTP port, a
TLS-terminating HTTPS port, an HTTP/3 (QUIC) port, a local Unix-socket admin
endpoint — each with its own bind address, its own offered protocol set, its own
TLS binding, and its own per-listener admission bound. The seed's single
`Dsl.Cfg.ListenerCfg` names exactly one accept surface; this file grows that one
dimension into the full declarative surface: an *array* of listener specs, each
carrying the pkl surface (`address`/`port` or a Unix path, a protocol set drawn
from `{h1, h2, h2c, h3, ws}`, and a per-listener TLS profile reference).

This file owns ONLY that dimension. It does two things beyond the declarative
record:

* **It folds the array into the REAL admission model.** Each `ListenerSpec`
  projects to a `Policy.ListenerCfg`; the whole array projects to a
  `Policy.Config` whose `listeners` field is the multi-listener surface, and
  `boundRunning` adopts every declared listener into a live `Policy.Running`.
  The real `Policy.serveDecision` gate then attributes / admits / refuses
  requests per listener — so a TLS-required listener genuinely refuses a
  plaintext response (never downgrades) and an undeclared listener is refused,
  neither of which a single hardcoded cleartext listener could express.

* **It proves the array's admission is cap-safe via the component calculus.**
  Each listener is a `Dsl.Component` whose invariant is its per-listener
  connection cap; the array is their parallel product (`Component.prod`); and
  `Component.reachable_inv` gives — through the kernel, with no bespoke
  induction — that on every reachable admission state every listener is within
  its declared cap. The per-listener step is exactly `Policy.accept`'s cap gate
  (`accept_live_eq_capStep`), so the component is a faithful abstraction of the
  deployed model, not a parallel toy.

`ListenersCfg` is a conservative extension of the singular dimension: `single`
embeds one `ListenerCfg` with `primaryId`/`policy` preserved on the nose
(`single_primaryId`/`single_policy`), so welding the plural dimension into
`instantiate` cannot regress the deployed serve.
-/

namespace Dsl.Cfg

open Dsl (Component)

/-! ## The declarative surface -/

/-- An application/transport protocol a listener may offer. The set a listener
advertises is the ALPN / upgrade surface the transport lane negotiates. -/
inductive Proto where
  /-- HTTP/1.1 over the raw stream. -/
  | h1
  /-- HTTP/2 over TLS (ALPN `h2`). -/
  | h2
  /-- HTTP/2 cleartext (prior-knowledge / `h2c` upgrade). -/
  | h2c
  /-- HTTP/3 over QUIC. -/
  | h3
  /-- WebSocket (RFC 6455 `Upgrade`). -/
  | ws
deriving Repr, DecidableEq

/-- A listener's bind address: a TCP host/port, or a Unix-domain socket path. -/
inductive BindAddr where
  /-- Bind a TCP socket on `host:port`. -/
  | tcp (host : String) (port : Nat)
  /-- Bind a Unix-domain stream socket at `path`. -/
  | unix (path : String)
deriving Repr, DecidableEq

/-- The TCP port a bind address exposes (`0` for a Unix socket, which has none). -/
def BindAddr.port : BindAddr → Nat
  | .tcp _ p => p
  | .unix _  => 0

/-- Whether this is a Unix-domain bind (no TCP port). -/
def BindAddr.isUnix : BindAddr → Bool
  | .tcp _ _ => false
  | .unix _  => true

/-- One listener in a deployment: its bind address, the protocol set it offers,
the TLS profile it terminates with (by name; `none` = cleartext), and its
per-listener admission bound. `id` is the stable identity the `Policy` layer
attributes a request arriving on this listener to. -/
structure ListenerSpec where
  /-- The stable listener identity (`Policy.ListenerCfg.id` / `AppConfig.lid`). -/
  id : Nat
  /-- The bind address: TCP `host:port` or a Unix-socket path. -/
  bind : BindAddr
  /-- The protocol set this listener offers (drawn from `{h1,h2,h2c,h3,ws}`). -/
  protocols : List Proto := [.h1]
  /-- The name of the `Dsl.Cfg.TlsProfile` this listener terminates with; `none`
  is a cleartext listener. Its presence is the enforce-TLS flag. -/
  tlsProfile : Option String := none
  /-- The per-listener admission bound (max concurrent live connections). -/
  connCap : Nat := 1024
deriving Repr

/-- A listener enforces TLS exactly when it references a TLS profile. This is the
`Policy.ListenerCfg.tlsRequired` flag: a listener with a profile refuses a
plaintext response. -/
def ListenerSpec.tlsRequired (s : ListenerSpec) : Bool := s.tlsProfile.isSome

/-- Whether this listener offers a given protocol. -/
def ListenerSpec.offers (s : ListenerSpec) (p : Proto) : Bool := s.protocols.contains p

/-- Project a listener spec onto the REAL `Policy.ListenerCfg` admission entry.
The bind port carries across; the Policy `addr` field is opaque to the gate
(declarative only) and is set to `0`; the TLS-profile reference becomes the
`tlsRequired` enforce flag; the cap carries across verbatim. -/
def ListenerSpec.toPolicy (s : ListenerSpec) : Policy.ListenerCfg :=
  { id := s.id
    addr := 0
    port := s.bind.port
    tlsRequired := s.tlsRequired
    connCap := s.connCap }

/-- **The multi-listener dimension.** The full declarative listener array, plus
the admission-attribution identity the single-pipeline `AppConfig` reads
(`primaryId`) and the live admission snapshot it reads (`policy`). The array is
the accept surface the transport lanes bind; `primaryId`/`policy` are the two
values the pure byte pipeline's `AppConfig` needs (mirroring the singular
`ListenerCfg`'s `id`/`policy`). -/
structure ListenersCfg where
  /-- The declarative listener array (the accept surface). -/
  listeners : List ListenerSpec
  /-- The listener identity a pipeline dispatch is attributed to (→ `AppConfig.lid`). -/
  primaryId : Nat
  /-- The live admission snapshot (→ `AppConfig.policy`). -/
  policy : Policy.Running

/-! ## Folding the array into the real admission model -/

/-- Adopt (bind) a list of listener ids into a running state, left to right. Each
`Policy.adopt` reuses the declared identity and gives a TLS-required listener an
active TLS context. -/
def adoptAll (ids : List Nat) (st : Policy.Running) : Policy.Running :=
  ids.foldl (fun s lid => Policy.adopt lid s) st

/-- The `Policy.Config` a listener array declares, given the deployment's route
surface: every listener projects to a `Policy.ListenerCfg`, and the routes carry
through. This is the declared admission surface the real gate reads. -/
def declaredConfig (specs : List ListenerSpec) (routes : List Policy.RouteCfg) :
    Policy.Config :=
  { listeners := specs.map ListenerSpec.toPolicy
    routes := routes }

/-- The live admission snapshot for a listener array: cold boot on the declared
surface, then adopt every declared listener. Reachable from `init` by a run of
`adopt` steps, so the REAL declared-surface invariant `Policy.Wf` holds of it
(`boundRunning_reachable` / `boundRunning_wf`). -/
def boundRunning (specs : List ListenerSpec) (routes : List Policy.RouteCfg) :
    Policy.Running :=
  adoptAll (specs.map ListenerSpec.id) (Policy.init (declaredConfig specs routes))

/-- Adopting a list of ids from a reachable state stays reachable (each fold step
is a real `Policy.Step.adopt`). -/
theorem adoptAll_reachable {c : Policy.Config} (ids : List Nat) {st : Policy.Running}
    (h : Policy.Reachable c st) : Policy.Reachable c (adoptAll ids st) := by
  induction ids generalizing st with
  | nil => exact h
  | cons lid rest ih =>
    exact ih (Policy.Reachable.step h (Policy.Step.adopt lid st))

/-- `boundRunning` is reachable from a cold boot on its declared surface. -/
theorem boundRunning_reachable (specs : List ListenerSpec) (routes : List Policy.RouteCfg) :
    Policy.Reachable (declaredConfig specs routes) (boundRunning specs routes) :=
  adoptAll_reachable _ Policy.Reachable.init

/-- **The multi-listener admission state is well-formed.** The REAL declared-
surface invariant `Policy.Wf` holds of the array's bound running state — it is
not asserted, it is inherited from reachability of the real model. -/
theorem boundRunning_wf (specs : List ListenerSpec) (routes : List Policy.RouteCfg) :
    Policy.Wf (boundRunning specs routes) :=
  Policy.reachable_wf (boundRunning_reachable specs routes)

/-- **Smart constructor.** Build a `ListenersCfg` from a listener array and a
route surface: the admission-attribution identity is the head listener's id and
the live snapshot is `boundRunning` — the array itself GENERATES the admission
state, rather than the deployment handing one in. `fallbackId` attributes the
degenerate empty array. -/
def ListenersCfg.ofSpecs (specs : List ListenerSpec) (routes : List Policy.RouteCfg)
    (fallbackId : Nat := 0) : ListenersCfg :=
  { listeners := specs
    primaryId := (specs.head?.map ListenerSpec.id).getD fallbackId
    policy := boundRunning specs routes }

/-! ## Conservative extension of the singular dimension -/

/-- Embed a single `Dsl.Cfg.ListenerCfg` (the seed's singular dimension) as a
one-element array, preserving its `id`/`policy` as the primary attribution and
live snapshot. This is the bridge that makes the plural dimension a drop-in
richer replacement: instantiate reads `primaryId`/`policy`, which for a `single`
config are exactly the singular's `id`/`policy`. -/
def ListenersCfg.single (l : ListenerCfg) : ListenersCfg :=
  { listeners := [{ id := l.id, bind := .tcp l.addr l.port,
                    tlsProfile := l.tlsProfile }]
    primaryId := l.id
    policy := l.policy }

/-- **No admission-id regression.** A `single`-embedded listener attributes to
exactly the singular listener's id. -/
@[simp] theorem ListenersCfg.single_primaryId (l : ListenerCfg) :
    (ListenersCfg.single l).primaryId = l.id := rfl

/-- **No admission-state regression.** A `single`-embedded listener carries
exactly the singular listener's live policy snapshot. -/
@[simp] theorem ListenersCfg.single_policy (l : ListenerCfg) :
    (ListenersCfg.single l).policy = l.policy := rfl

/-! ## The component calculus: per-listener cap safety composes

Each listener's admission is a `Dsl.Component` whose state is its live connection
count and whose invariant is its declared cap. The array's admission is the
parallel product of these components; `Component.reachable_inv` then delivers —
through the kernel, no bespoke induction — that every reachable admission state
keeps every listener within its cap. -/

/-- One listener's admission as a component: state is the live count, the
invariant is the per-listener cap, and a step is one accept attempt that admits
(increments) only while strictly below the cap — exactly `Policy.accept`'s gate.
The output records whether the connection was admitted. -/
def capComponent (cap : Nat) : Component where
  State := Nat
  Input := Unit
  Output := Bool
  inv := fun s => s ≤ cap
  init := 0
  step := fun s _ => if s < cap then (s + 1, [true]) else (s, [false])
  init_wf := Nat.zero_le cap
  step_wf := by
    intro s _ h
    show (if s < cap then (s + 1, [true]) else (s, [false])).1 ≤ cap
    split <;> omega

/-- The trivial component (unit state, vacuous invariant): the base of the
array's product fold. -/
def unitComponent : Component where
  State := Unit
  Input := Unit
  Output := Bool
  inv := fun _ => True
  init := ()
  step := fun _ _ => ((), [true])
  init_wf := trivial
  step_wf := by intro _ _ _; trivial

/-- The array's admission component: the parallel product of the per-listener cap
components, folded over the declared caps. Its invariant is the CONJUNCTION of
the per-listener cap bounds — the deployment-wide "no listener exceeds its cap"
predicate. -/
def listenersComponent : List Nat → Component
  | []      => unitComponent
  | c :: cs => (capComponent c).prod (listenersComponent cs)

/-- The declared caps of a listener array. -/
def ListenersCfg.caps (cfg : ListenersCfg) : List Nat :=
  cfg.listeners.map ListenerSpec.connCap

/-- The admission component of a deployment's listener array. -/
def ListenersCfg.admissionComponent (cfg : ListenersCfg) : Component :=
  listenersComponent cfg.caps

/-- **Cap safety composes (the kernel, applied).** On every reachable admission
state of the listener array, the conjoined per-listener cap invariant holds —
i.e. no listener exceeds its declared cap. This is `Component.reachable_inv` on
the parallel product `listenersComponent`; the composition law comes from the
kernel's `prod_preserves`, not a bespoke induction over the array. -/
theorem listeners_cap_safe (caps : List Nat)
    {s : (listenersComponent caps).State}
    (h : (listenersComponent caps).Reachable s) :
    (listenersComponent caps).inv s :=
  Component.reachable_inv _ h

/-- The same, stated over a deployment's actual listener array. -/
theorem ListenersCfg.admission_cap_safe (cfg : ListenersCfg)
    {s : cfg.admissionComponent.State}
    (h : cfg.admissionComponent.Reachable s) :
    cfg.admissionComponent.inv s :=
  Component.reachable_inv _ h

/-- **A reachable array-admission state is reachable in each listener.** The
composed admission surface manufactures no live count unreachable in the
individual listener it belongs to (`Component.prod_reachable`, the kernel). -/
theorem listeners_factor_reachable (c : Nat) (cs : List Nat)
    (s : ((capComponent c).prod (listenersComponent cs)).State)
    (h : ((capComponent c).prod (listenersComponent cs)).Reachable s) :
    (capComponent c).Reachable s.1 ∧ (listenersComponent cs).Reachable s.2 :=
  Dsl.prod_reachable _ _ s h

/-! ### The per-listener component is faithful to `Policy.accept` -/

/-- **The cap component's step IS `Policy.accept`'s gate.** For a bound listener,
`Policy.accept` moves its live count exactly as `capComponent`'s step moves the
component state — increment while below the cap, hold at the cap. So the
component is a faithful abstraction of the deployed admission model, not a
parallel invention. -/
theorem accept_live_eq_capStep (lid : Nat) (st : Policy.Running) (l : Policy.ListenerCfg)
    (hl : st.cfg.listener? lid = some l) (hb : lid ∈ st.bound) :
    (Policy.accept lid st).live lid
      = ((capComponent l.connCap).step (st.live lid) ()).1 := by
  have hstep : ((capComponent l.connCap).step (st.live lid) ()).1
      = if st.live lid < l.connCap then st.live lid + 1 else st.live lid := by
    show (if st.live lid < l.connCap then (st.live lid + 1, [true])
          else (st.live lid, [false])).1 = _
    split <;> rfl
  rw [hstep]
  unfold Policy.accept
  rw [hl]
  by_cases hc : st.live lid < l.connCap
  · simp [hb, hc, Policy.bumpAt_self]
  · simp [hc]

/-! ## A concrete multi-listener deployment the hardcoded serve could not express

The deployed literal declares exactly ONE cleartext listener (`deployLid`, port
8080). The array below declares three: a public cleartext HTTP/1.1+h2c port, a
TLS-terminating HTTPS port offering h2 and h3, and a Unix-socket admin endpoint.
The REAL `Policy.serveDecision` gate then admits and refuses per listener — a
plaintext response on the TLS listener is refused (never downgrade), an
undeclared listener is refused — decisions the single hardcoded listener has no
vocabulary to make. -/

/-- The public cleartext HTTP listener: TCP `0.0.0.0:8080`, offering HTTP/1.1 and
h2c, no TLS. -/
def demoPublicHttp : ListenerSpec :=
  { id := 0, bind := .tcp "0.0.0.0" 8080, protocols := [.h1, .h2c], connCap := 1024 }

/-- The public TLS listener: TCP `0.0.0.0:8443`, offering h2 and h3 over the
`secure` TLS profile (so it enforces TLS). -/
def demoPublicHttps : ListenerSpec :=
  { id := 1, bind := .tcp "0.0.0.0" 8443, protocols := [.h2, .h3],
    tlsProfile := some "secure", connCap := 2048 }

/-- The local admin listener: a Unix-domain socket, HTTP/1.1 + WebSocket, tightly
capped. A Unix bind has no TCP port — inexpressible with a port-only listener. -/
def demoAdminUnix : ListenerSpec :=
  { id := 2, bind := .unix "/run/orb/admin.sock", protocols := [.h1, .ws],
    connCap := 16 }

/-- The three-listener array. -/
def demoListeners : List ListenerSpec := [demoPublicHttp, demoPublicHttps, demoAdminUnix]

/-- The demo route surface: one declared route key. -/
def demoRoutes : List Policy.RouteCfg := [⟨⟨0, 0⟩, 0⟩]

/-- The demo deployment's listener dimension, admission state generated from the
array. -/
def demoCfg : ListenersCfg := ListenersCfg.ofSpecs demoListeners demoRoutes

/-- The live admission snapshot: all three listeners bound. -/
def demoRunning : Policy.Running := boundRunning demoListeners demoRoutes

/-- The demo admission state satisfies the REAL declared-surface invariant. -/
theorem demoRunning_wf : Policy.Wf demoRunning := boundRunning_wf _ _

/-- **The cleartext public listener admits a plaintext response** on the declared
route — the real gate records the observation. -/
theorem demo_admits_cleartext :
    Policy.serveDecision 0 ⟨0, 0⟩ true demoRunning = some ⟨0, ⟨0, 0⟩, true⟩ := by
  decide

/-- **The TLS listener refuses to downgrade.** A plaintext response on the
TLS-required listener is refused by the SAME real gate — never a downgrade. The
single hardcoded cleartext listener cannot state this. -/
theorem demo_tls_refuses_plaintext :
    Policy.serveDecision 1 ⟨0, 0⟩ true demoRunning = none := by decide

/-- **The TLS listener serves over TLS.** With `plaintext := false` the same
listener admits (its TLS context is active — `Policy.adopt` gave it one because
it is TLS-required) on the declared route. -/
theorem demo_tls_admits_encrypted :
    Policy.serveDecision 1 ⟨0, 0⟩ false demoRunning = some ⟨1, ⟨0, 0⟩, false⟩ := by
  decide

/-- **The Unix admin listener admits** a plaintext response on the declared route
— a Unix-socket accept surface the port-only hardcoded listener could not bind. -/
theorem demo_admin_admits :
    Policy.serveDecision 2 ⟨0, 0⟩ true demoRunning = some ⟨2, ⟨0, 0⟩, true⟩ := by
  decide

/-- **An undeclared listener is refused** by the same real gate — the multi-
listener surface is a closed set, not an open door. -/
theorem demo_refuses_undeclared :
    Policy.serveDecision 9 ⟨0, 0⟩ true demoRunning = none := by decide

/-- **An undeclared route is refused** even on a bound listener. -/
theorem demo_refuses_undeclared_route :
    Policy.serveDecision 0 ⟨7, 7⟩ true demoRunning = none := by decide

/-- The demo array's caps are exactly the three declared per-listener bounds — so
`admission_cap_safe` guarantees `[1024, 2048, 16]`-safety compositionally. -/
theorem demoCfg_caps : demoCfg.caps = [1024, 2048, 16] := rfl

end Dsl.Cfg
