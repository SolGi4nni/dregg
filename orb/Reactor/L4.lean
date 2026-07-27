import Reactor.Proxy
import Reactor.ProxyDial

/-!
# Reactor.L4 — raw TCP/UDP passthrough (layer-4 forwarding)

Everything above this file forwards *requests*: the reactor parses HTTP, emits
`dispatch`, and the reverse-proxy handler picks an upstream for the parsed
request. A layer-4 passthrough is the mode below that: the listener never
parses the stream at all. Accept a connection, ask the load balancer for an
upstream, dial it, and from then on move bytes verbatim in both directions
until each side finishes — the conventional `mode tcp` / `stream {}` posture of
a general-purpose proxy, applied to protocols the HTTP engine has no business
reading (databases, message queues, TLS-passthrough SNI backends, bespoke
wire protocols).

Two machines live here, sharing one `Config` (a `ProxyPool` + selection `Ctx`):

  * **The TCP splice machine** (`stepTcp`) — a per-connection state machine
    over the reactor's own submission vocabulary (`RingSubmission`):

      - `idle` + `accept` → run the REAL `Proxy.selectChain` (via
        `Reactor.Proxy.chooseUpstream`, nothing re-implemented) and emit
        `connectUpstream` to its pick; no eligible backend closes the client.
      - `connecting` — the dial is in flight. Client bytes that arrive early
        are *buffered*, never dropped, and flushed in one piece the moment
        `connected fd` lands. A client that gives up (EOF) before the upstream
        answers aborts the dial (the abort-on-early-close rule: no upstream
        work on behalf of a client that already left).
      - `established` — the splice: every client chunk becomes exactly one
        `submitSendUpstream fd`, every upstream chunk exactly one `submitSend`,
        payloads verbatim, order preserved.
      - half-close is honored per direction: client EOF stops the upstream-bound
        lane but keeps draining upstream→client (`drainDown`); upstream EOF the
        mirror (`drainUp`); the second EOF closes the socket.

  * **The UDP datagram forwarder** (`udpStep`) — each client datagram goes,
    boundary-preserved and payload-verbatim, to the balancer's pick; replies
    return to the client. Datagram *session affinity* (a per-client table with
    stable bindings, reply correlation, idle eviction) is the `Udp` library's
    proven machinery; this forwarder supplies the seam it lacked — the upstream
    *target* chosen by the health-filtered `Proxy.selectChain` rather than by a
    fresh counter. With the `rendezvousHash` policy and the flow hash in
    `Ctx.key`, the pick is per-flow stable with minimal disruption on pool
    change (`Proxy.Rendezvous`).

## The theorems

**LB seam** — `accept_dials_healthy`: the dialed address is `addrOf b` for
exactly the backend `b` the real `Proxy.selectChain` chose, and `b` is a
healthy, administratively active pool member in the best nonempty tier
(`Proxy.selectChain_eligible`, transported). `accept_none_closes` pins the
no-eligible-backend case: close, dial nothing.

**Stream faithfulness (client→upstream)** — `runTcp_up_faithful`: over any
event trace that never feeds a client chunk to a state that cannot accept one
(`goodUp`, a decidable guard the driver upholds by construction — a socket
that is closed or EOF-drained produces no more `fromClient` events), the bytes
sent upstream, *plus the bytes still buffered*, equal the concatenation of the
client's chunks, in order. `session_up_exact` is the corollary for a finished
session (nothing left buffered): bytes in = bytes out, verbatim. The buffering
is load-bearing: a machine that dropped pre-connect bytes, reordered chunks, or
invented traffic would each break the equation.

**Stream faithfulness (upstream→client)** — `runTcp_down_faithful`: the mirror
lane has no buffer, so it is exact everywhere: bytes delivered to the client =
the concatenation of upstream chunks, in order.

**No traffic before a tunnel** — `no_send_without_fd`: a state without a
connected upstream never emits `submitSendUpstream` (the only event that can is
the `connected` completion itself, which *is* the tunnel coming up — it flushes
the buffer). Together with `established_send_uses_fd`, every upstream send
rides the session's own fd.

**UDP faithfulness** — `udpRun_faithful`: the forwarded datagram *list* (not
its flattening — boundaries are datagram semantics) equals the client's
datagram list, every one targeted at `addrOf b` for the balancer's proven-
eligible pick `b`; `udpStep_none` pins the no-backend case (drop, never
misroute); `udpRun_down_faithful` the reply lane.

`demo_*` drives a whole session concretely over the shared `demoPool` (backend
0 unhealthy): the splice dials backend 2 — the healthy least-connections winner
— buffers the early chunk, flushes it on connect, splices both directions, and
closes after both EOFs, with the exact submission stream checked by `decide`.
-/

namespace Reactor.L4

open Proto (Bytes Addr)
open Reactor.Proxy (ProxyPool chooseUpstream addrOf)

/-! ## The shared configuration -/

/-- An L4 listener's forwarding configuration: the upstream pool (with live
health/admin verdicts snapshotted in) and the selection context. Same
vocabulary as the L7 reverse proxy — the balancer is shared, not forked. -/
structure Config where
  /-- The upstream pool the balancer selects over. -/
  pool : ProxyPool
  /-- Per-connection (TCP) / per-flow (UDP) selection context. -/
  ctx  : Proxy.Ctx

/-! ## The TCP splice machine -/

/-- Per-connection splice state. `pend` in `connecting` is the client data that
arrived before the upstream dial completed — buffered, flushed on `connected`. -/
inductive TcpState where
  /-- Accepted nothing yet. -/
  | idle
  /-- Dialing backend `b`; `pend` buffers early client bytes. -/
  | connecting (b : Proxy.Backend) (pend : Bytes)
  /-- Tunnel up on upstream fd `fd`; both directions splice. -/
  | established (b : Proxy.Backend) (fd : Nat)
  /-- Client sent EOF; only upstream→client still drains. -/
  | drainDown (b : Proxy.Backend) (fd : Nat)
  /-- Upstream sent EOF; only client→upstream still drains. -/
  | drainUp (b : Proxy.Backend) (fd : Nat)
  /-- Connection over. -/
  | closed
deriving Repr

/-- Per-connection splice events, as the ring reports them. -/
inductive TcpEvent where
  /-- A client connection was accepted on the L4 listener. -/
  | accept
  /-- The upstream dial completed; the tunnel's fd. -/
  | connected (fd : Nat)
  /-- The upstream dial failed. -/
  | connectFailed
  /-- A chunk of client bytes. -/
  | fromClient (data : Bytes)
  /-- A chunk of upstream bytes. -/
  | fromUpstream (data : Bytes)
  /-- The client half-closed (no more client bytes will arrive). -/
  | clientEof
  /-- The upstream half-closed. -/
  | upstreamEof
deriving Repr

/-- **The splice step.** One event against one connection's state; emits into
the reactor's own submission vocabulary. Selection is the REAL
`Proxy.selectChain` (`chooseUpstream`); bytes are moved verbatim, chunk for
chunk; early client bytes are buffered and flushed on connect; each direction
half-closes independently; a client EOF during the dial aborts it. Events that
cannot occur for the current state (the driver owns the socket lifecycle) are
ignored. -/
def stepTcp (cfg : Config) : TcpState → TcpEvent → TcpState × List RingSubmission
  | .idle, .accept =>
    match chooseUpstream cfg.pool cfg.ctx with
    | some b => (.connecting b [], [.connectUpstream (addrOf b)])
    | none   => (.closed, [.closeSock])
  | .connecting b pend, .fromClient d => (.connecting b (pend ++ d), [])
  | .connecting b pend, .connected fd =>
    (.established b fd,
     match pend with
     | [] => []
     | _  => [.submitSendUpstream fd pend])
  | .connecting _ _, .connectFailed => (.closed, [.closeSock])
  | .connecting _ _, .clientEof     => (.closed, [.closeSock])
  | .established b fd, .fromClient d   => (.established b fd, [.submitSendUpstream fd d])
  | .established b fd, .fromUpstream d => (.established b fd, [.submitSend d])
  | .established b fd, .clientEof      => (.drainDown b fd, [])
  | .established b fd, .upstreamEof    => (.drainUp b fd, [])
  | .drainDown b fd, .fromUpstream d => (.drainDown b fd, [.submitSend d])
  | .drainDown _ _, .upstreamEof     => (.closed, [.closeSock])
  | .drainUp b fd, .fromClient d => (.drainUp b fd, [.submitSendUpstream fd d])
  | .drainUp _ _, .clientEof     => (.closed, [.closeSock])
  | s, _ => (s, [])

/-- Run a whole event trace from a state, concatenating the submissions. -/
def runTcp (cfg : Config) : TcpState → List TcpEvent → TcpState × List RingSubmission
  | s, [] => (s, [])
  | s, e :: evs =>
    ((runTcp cfg (stepTcp cfg s e).1 evs).1,
     (stepTcp cfg s e).2 ++ (runTcp cfg (stepTcp cfg s e).1 evs).2)

/-! ## Byte-accounting projections -/

/-- Every byte sent toward the upstream, in submission order. -/
def upSent : List RingSubmission → Bytes
  | [] => []
  | .submitSendUpstream _ d :: rest => d ++ upSent rest
  | _ :: rest => upSent rest

/-- Every byte sent back toward the client, in submission order. -/
def downSent : List RingSubmission → Bytes
  | [] => []
  | .submitSend d :: rest => d ++ downSent rest
  | _ :: rest => downSent rest

/-- The client bytes an event carries (empty for non-data events). -/
def fromClientBytes : TcpEvent → Bytes
  | .fromClient d => d
  | _ => []

/-- The upstream bytes an event carries. -/
def fromUpstreamBytes : TcpEvent → Bytes
  | .fromUpstream d => d
  | _ => []

/-- Every client byte a trace delivers, in order. -/
def clientInput : List TcpEvent → Bytes
  | [] => []
  | e :: evs => fromClientBytes e ++ clientInput evs

/-- Every upstream byte a trace delivers, in order. -/
def upstreamInput : List TcpEvent → Bytes
  | [] => []
  | e :: evs => fromUpstreamBytes e ++ upstreamInput evs

/-- The bytes a state still holds (the pre-connect buffer; empty elsewhere). -/
def pending : TcpState → Bytes
  | .connecting _ p => p
  | _ => []

theorem upSent_append (xs ys : List RingSubmission) :
    upSent (xs ++ ys) = upSent xs ++ upSent ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [upSent, ih]

theorem downSent_append (xs ys : List RingSubmission) :
    downSent (xs ++ ys) = downSent xs ++ downSent ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [downSent, ih]

/-! ## The LB seam -/

/-- On `accept`, the machine dials exactly the balancer's pick and buffers
nothing yet. Selection is the real `Proxy.selectChain`, untouched. -/
theorem accept_dials_choice (cfg : Config) {b : Proxy.Backend}
    (h : chooseUpstream cfg.pool cfg.ctx = some b) :
    stepTcp cfg .idle .accept
      = (.connecting b [], [.connectUpstream (addrOf b)]) := by
  simp [stepTcp, h]

/-- **The L4 LB seam.** The dialed upstream is `addrOf b` for the backend `b`
the REAL `Proxy.selectChain` chose — and `b` is a healthy, administratively
active member of the pool sitting in the best nonempty tier
(`Proxy.selectChain_eligible`, transported to the L4 listener). -/
theorem accept_dials_healthy (cfg : Config) {b : Proxy.Backend}
    (h : chooseUpstream cfg.pool cfg.ctx = some b) :
    stepTcp cfg .idle .accept
        = (.connecting b [], [.connectUpstream (addrOf b)])
      ∧ b ∈ cfg.pool.backends
      ∧ b.eligible = true
      ∧ Proxy.bestTier cfg.pool.backends = some b.tier :=
  ⟨accept_dials_choice cfg h, Proxy.selectChain_eligible h⟩

/-- No eligible backend: the listener closes the client and dials nothing. -/
theorem accept_none_closes (cfg : Config)
    (h : chooseUpstream cfg.pool cfg.ctx = none) :
    stepTcp cfg .idle .accept = (.closed, [.closeSock]) := by
  simp [stepTcp, h]

/-! ## No traffic before a tunnel -/

/-- Does the state hold a connected upstream fd? -/
def hasFd : TcpState → Bool
  | .established _ _ => true
  | .drainDown _ _ => true
  | .drainUp _ _ => true
  | _ => false

/-- Is this submission an upstream-bound send? -/
def isUpSend : RingSubmission → Bool
  | .submitSendUpstream _ _ => true
  | _ => false

/-- **No upstream send without a tunnel.** From a state with no connected fd,
no event other than the connect completion itself can emit an upstream-bound
send. (The completion may: it *is* the tunnel coming up, and it flushes the
pre-connect buffer on the fd it just delivered.) -/
theorem no_send_without_fd (cfg : Config) (s : TcpState) (e : TcpEvent)
    (hs : hasFd s = false) (he : ∀ fd, e ≠ .connected fd) :
    (stepTcp cfg s e).2.filter isUpSend = [] := by
  cases s with
  | established b fd => simp [hasFd] at hs
  | drainDown b fd => simp [hasFd] at hs
  | drainUp b fd => simp [hasFd] at hs
  | idle =>
    cases e with
    | connected fd => exact absurd rfl (he fd)
    | accept =>
      simp only [stepTcp]
      cases chooseUpstream cfg.pool cfg.ctx <;> rfl
    | _ => rfl
  | connecting b pend =>
    cases e with
    | connected fd => exact absurd rfl (he fd)
    | _ => rfl
  | closed =>
    cases e with
    | connected fd => exact absurd rfl (he fd)
    | _ => rfl

/-- An established splice sends each client chunk on the session's own fd. -/
theorem established_send_uses_fd (cfg : Config) (b : Proxy.Backend) (fd : Nat)
    (d : Bytes) :
    stepTcp cfg (.established b fd) (.fromClient d)
      = (.established b fd, [.submitSendUpstream fd d]) := rfl

/-! ## Stream faithfulness, client → upstream -/

/-- The client-byte-conservation guard for one event against one state: `false`
exactly when the event would lose client bytes — a chunk fed to a state that
cannot accept one (closed, never-opened, or already client-EOF'd), or an abort
(`connectFailed` / early `clientEof`) while bytes sit in the pre-connect
buffer. A driver that only reports `fromClient` for a live client socket and
never aborts a session it still owes bytes satisfies it by construction; it is
decidable, so a trace can also be checked outright. -/
def okUp : TcpState → TcpEvent → Bool
  | .idle, .fromClient _ => false
  | .closed, .fromClient _ => false
  | .drainDown _ _, .fromClient _ => false
  | .connecting _ pend, .connectFailed => pend.isEmpty
  | .connecting _ pend, .clientEof => pend.isEmpty
  | _, _ => true

/-- The guard over a trace: every step conserves client bytes. -/
def goodUp (cfg : Config) : TcpState → List TcpEvent → Bool
  | _, [] => true
  | s, e :: evs => okUp s e && goodUp cfg (stepTcp cfg s e).1 evs

/-- One conserving step's exact ledger: bytes sent upstream plus bytes still
buffered afterward = bytes buffered before plus the event's client bytes. -/
theorem stepTcp_up (cfg : Config) (s : TcpState) (e : TcpEvent)
    (h : okUp s e = true) :
    upSent (stepTcp cfg s e).2 ++ pending (stepTcp cfg s e).1
      = pending s ++ fromClientBytes e := by
  cases s with
  | idle =>
    cases e <;> simp_all [okUp, stepTcp, upSent, pending, fromClientBytes]
    case accept =>
      cases chooseUpstream cfg.pool cfg.ctx <;> simp [upSent, pending]
  | connecting b pend =>
    cases e <;>
      simp_all [okUp, stepTcp, upSent, pending, fromClientBytes, List.isEmpty_iff]
    case connected fd =>
      cases pend <;> simp [upSent, pending]
  | established b fd =>
    cases e <;> simp_all [okUp, stepTcp, upSent, pending, fromClientBytes]
  | drainDown b fd =>
    cases e <;> simp_all [okUp, stepTcp, upSent, pending, fromClientBytes]
  | drainUp b fd =>
    cases e <;> simp_all [okUp, stepTcp, upSent, pending, fromClientBytes]
  | closed =>
    cases e <;> simp_all [okUp, stepTcp, upSent, pending, fromClientBytes]

/-- **Client→upstream stream faithfulness.** Over any conserving trace, the
bytes sent upstream plus the bytes still buffered equal the concatenation of
the client's chunks — in order, verbatim, nothing dropped, nothing invented.
(The pre-connect buffer is exactly the correction term; a finished session has
none — `session_up_exact`.) -/
theorem runTcp_up_faithful (cfg : Config) (s : TcpState) (evs : List TcpEvent)
    (h : goodUp cfg s evs = true) :
    upSent (runTcp cfg s evs).2 ++ pending (runTcp cfg s evs).1
      = pending s ++ clientInput evs := by
  induction evs generalizing s with
  | nil => simp [runTcp, clientInput, upSent]
  | cons e evs ih =>
    rw [goodUp, Bool.and_eq_true] at h
    have hstep := stepTcp_up cfg s e h.1
    have hrest := ih (stepTcp cfg s e).1 h.2
    simp only [runTcp, clientInput, upSent_append, List.append_assoc]
    rw [hrest, ← List.append_assoc, hstep, List.append_assoc]

/-- **A finished session forwards the client stream exactly.** When the trace
ends with nothing buffered (any closed or established-and-flushed end state),
bytes upstream = bytes from the client, byte for byte, in order. -/
theorem session_up_exact (cfg : Config) (evs : List TcpEvent)
    (h : goodUp cfg .idle evs = true)
    (hend : pending (runTcp cfg .idle evs).1 = []) :
    upSent (runTcp cfg .idle evs).2 = clientInput evs := by
  have hrun := runTcp_up_faithful cfg .idle evs h
  rw [hend, List.append_nil] at hrun
  simpa [pending] using hrun

/-! ## Stream faithfulness, upstream → client -/

/-- The mirror guard: an upstream chunk must arrive on a state whose downstream
lane is open (established or draining down). -/
def okDown : TcpState → TcpEvent → Bool
  | .established _ _, .fromUpstream _ => true
  | .drainDown _ _, .fromUpstream _ => true
  | _, .fromUpstream _ => false
  | _, _ => true

/-- The mirror guard over a trace. -/
def goodDown (cfg : Config) : TcpState → List TcpEvent → Bool
  | _, [] => true
  | s, e :: evs => okDown s e && goodDown cfg (stepTcp cfg s e).1 evs

/-- One conserving step relays the upstream bytes exactly (this path
has no buffer, so the step ledger is already exact). -/
theorem stepTcp_down (cfg : Config) (s : TcpState) (e : TcpEvent)
    (h : okDown s e = true) :
    downSent (stepTcp cfg s e).2 = fromUpstreamBytes e := by
  cases s with
  | idle =>
    cases e <;> simp_all [okDown, stepTcp, downSent, fromUpstreamBytes]
    case accept =>
      cases chooseUpstream cfg.pool cfg.ctx <;> simp [downSent]
  | connecting b pend =>
    cases e <;> simp_all [okDown, stepTcp, downSent, fromUpstreamBytes]
    case connected fd =>
      cases pend <;> simp [downSent]
  | established b fd =>
    cases e <;> simp_all [okDown, stepTcp, downSent, fromUpstreamBytes]
  | drainDown b fd =>
    cases e <;> simp_all [okDown, stepTcp, downSent, fromUpstreamBytes]
  | drainUp b fd =>
    cases e <;> simp_all [okDown, stepTcp, downSent, fromUpstreamBytes]
  | closed =>
    cases e <;> simp_all [okDown, stepTcp, downSent, fromUpstreamBytes]

/-- **Upstream→client stream faithfulness.** Over any conserving trace the
bytes delivered to the client are exactly the concatenation of the upstream's
chunks — in order, verbatim. No buffer on this path, so no correction term. -/
theorem runTcp_down_faithful (cfg : Config) (s : TcpState) (evs : List TcpEvent)
    (h : goodDown cfg s evs = true) :
    downSent (runTcp cfg s evs).2 = upstreamInput evs := by
  induction evs generalizing s with
  | nil => simp [runTcp, upstreamInput, downSent]
  | cons e evs ih =>
    rw [goodDown, Bool.and_eq_true] at h
    simp only [runTcp, upstreamInput, downSent_append]
    rw [stepTcp_down cfg s e h.1, ih (stepTcp cfg s e).1 h.2]

/-! ## The UDP datagram forwarder -/

/-- L4 datagram events for one client flow. -/
inductive UdpEvent where
  /-- A datagram from the client. -/
  | fromClient (data : Bytes)
  /-- A reply datagram from the upstream. -/
  | fromUpstream (data : Bytes)
deriving Repr

/-- The forwarder's wire effects. Datagrams are addressed (no connection), so
the upstream target rides on every send. -/
inductive UdpEffect where
  /-- Send `data` to upstream `a`, one datagram. -/
  | toUpstream (a : Addr) (data : Bytes)
  /-- Send `data` back to the client, one datagram. -/
  | toClient (data : Bytes)
deriving Repr, DecidableEq

/-- **The datagram step.** A client datagram goes verbatim to the balancer's
pick (the REAL `Proxy.selectChain`; drop when no backend is eligible — never
misroute); a reply goes verbatim back to the client. One datagram in, at most
one datagram out: boundaries are preserved, never split or coalesced.

Per-flow affinity is by configuration, not by state: `cfg.ctx.key` carries the
flow hash, so under `rendezvousHash` every datagram of a flow picks the same
backend (`Proxy.Rendezvous`, minimal disruption on pool change). The richer
per-client session table (stable bindings, reply correlation, idle eviction)
is the `Udp` library's proven relay; this step is the balancer seam that
chooses its upstream target. -/
def udpStep (cfg : Config) : UdpEvent → List UdpEffect
  | .fromClient d =>
    match chooseUpstream cfg.pool cfg.ctx with
    | some b => [.toUpstream (addrOf b) d]
    | none   => []
  | .fromUpstream d => [.toClient d]

/-- Run a datagram trace, concatenating effects. -/
def udpRun (cfg : Config) : List UdpEvent → List UdpEffect
  | [] => []
  | e :: evs => udpStep cfg e ++ udpRun cfg evs

/-- The upstream-bound datagrams of an effect list (boundaries kept). -/
def upDatagrams : List UdpEffect → List Bytes
  | [] => []
  | .toUpstream _ d :: rest => d :: upDatagrams rest
  | _ :: rest => upDatagrams rest

/-- The client-bound datagrams of an effect list. -/
def downDatagrams : List UdpEffect → List Bytes
  | [] => []
  | .toClient d :: rest => d :: downDatagrams rest
  | _ :: rest => downDatagrams rest

/-- The client datagrams of an event trace. -/
def clientDatagrams : List UdpEvent → List Bytes
  | [] => []
  | .fromClient d :: evs => d :: clientDatagrams evs
  | _ :: evs => clientDatagrams evs

/-- The upstream reply datagrams of an event trace. -/
def upstreamDatagrams : List UdpEvent → List Bytes
  | [] => []
  | .fromUpstream d :: evs => d :: upstreamDatagrams evs
  | _ :: evs => upstreamDatagrams evs

theorem upDatagrams_append (xs ys : List UdpEffect) :
    upDatagrams (xs ++ ys) = upDatagrams xs ++ upDatagrams ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [upDatagrams, ih]

theorem downDatagrams_append (xs ys : List UdpEffect) :
    downDatagrams (xs ++ ys) = downDatagrams xs ++ downDatagrams ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [downDatagrams, ih]

/-- One client datagram forwards verbatim to the balancer's pick — which is a
healthy, active, best-tier member of the pool. -/
theorem udpStep_targets_lb (cfg : Config) {b : Proxy.Backend} (d : Bytes)
    (h : chooseUpstream cfg.pool cfg.ctx = some b) :
    udpStep cfg (.fromClient d) = [.toUpstream (addrOf b) d]
      ∧ b ∈ cfg.pool.backends
      ∧ b.eligible = true
      ∧ Proxy.bestTier cfg.pool.backends = some b.tier :=
  ⟨by simp [udpStep, h], Proxy.selectChain_eligible h⟩

/-- No eligible backend: the datagram is dropped, never sent anywhere. -/
theorem udpStep_none (cfg : Config) (d : Bytes)
    (h : chooseUpstream cfg.pool cfg.ctx = none) :
    udpStep cfg (.fromClient d) = [] := by
  simp [udpStep, h]

/-- **UDP forward faithfulness.** When the balancer picks `b`, the forwarded
datagram list is EXACTLY the client's datagram list — boundaries preserved,
payloads verbatim, order kept, every one addressed to `addrOf b`. -/
theorem udpRun_faithful (cfg : Config) {b : Proxy.Backend}
    (h : chooseUpstream cfg.pool cfg.ctx = some b) (evs : List UdpEvent) :
    upDatagrams (udpRun cfg evs)
      = clientDatagrams evs
    ∧ ∀ eff ∈ udpRun cfg evs, ∀ a d, eff = .toUpstream a d → a = addrOf b := by
  induction evs with
  | nil => exact ⟨rfl, by intro eff heff; cases heff⟩
  | cons e evs ih =>
    refine ⟨?_, ?_⟩
    · cases e with
      | fromClient d =>
        simp only [udpRun, udpStep, h, clientDatagrams, List.cons_append,
          List.nil_append, upDatagrams]
        exact congrArg (d :: ·) ih.1
      | fromUpstream d =>
        simp only [udpRun, udpStep, clientDatagrams, List.cons_append,
          List.nil_append, upDatagrams]
        exact ih.1
    · intro eff heff a d heq
      cases e with
      | fromClient p =>
        simp only [udpRun, udpStep, h, List.cons_append, List.nil_append,
          List.mem_cons] at heff
        rcases heff with heff | heff
        · rw [heff] at heq; cases heq; rfl
        · exact ih.2 eff heff a d heq
      | fromUpstream p =>
        simp only [udpRun, udpStep, List.cons_append, List.nil_append,
          List.mem_cons] at heff
        rcases heff with heff | heff
        · rw [heff] at heq; cases heq
        · exact ih.2 eff heff a d heq

/-- **UDP reply faithfulness.** Replies return to the client verbatim,
boundary-preserved, in order — regardless of the pool. -/
theorem udpRun_down_faithful (cfg : Config) (evs : List UdpEvent) :
    downDatagrams (udpRun cfg evs) = upstreamDatagrams evs := by
  induction evs with
  | nil => rfl
  | cons e evs ih =>
    cases e with
    | fromClient d =>
      simp only [udpRun, udpStep, upstreamDatagrams]
      cases chooseUpstream cfg.pool cfg.ctx <;>
        simp [downDatagrams_append, downDatagrams, ih]
    | fromUpstream d =>
      simp [udpRun, udpStep, downDatagrams_append, downDatagrams,
        upstreamDatagrams, ih]

/-! ## A whole session, concretely

The shared demo pool (`Reactor.Proxy.demoPool`): backend 0 is unhealthy,
backends 1 and 2 are healthy, least-connections picks backend 2. The splice
dials it, buffers the chunk that raced the dial, flushes it on connect,
splices both directions verbatim, and closes after both EOFs. -/

/-- The demo listener config: the shared pool and context. -/
def demoCfg : Config := ⟨Reactor.Proxy.demoPool, Reactor.Proxy.demoCtx⟩

/-- A full session trace: accept; an early client chunk (races the dial);
connect completion; a second client chunk; an upstream reply; both EOFs. -/
def demoTrace : List TcpEvent :=
  [ .accept,
    .fromClient [104, 101]        -- "he", arrives before the tunnel is up
  , .connected 7
  , .fromClient [108, 108, 111]   -- "llo"
  , .fromUpstream [111, 107]      -- "ok"
  , .clientEof
  , .upstreamEof ]

/-- The demo trace conserves both lanes. -/
theorem demoTrace_good :
    goodUp demoCfg .idle demoTrace = true
      ∧ goodDown demoCfg .idle demoTrace = true := by decide

/-- The session dials the healthy least-connections winner (backend 2) — the
unhealthy backend 0 is never targeted. -/
theorem demo_dials_b2 :
    Reactor.Proxy.targetedUpstream (runTcp demoCfg .idle demoTrace).2
      = some (addrOf Reactor.Proxy.demoB2) := by decide

/-- The full client stream reaches the upstream verbatim ("hello" — the early
chunk was buffered, not lost), and the upstream reply reaches the client
verbatim ("ok"). -/
theorem demo_streams_exact :
    upSent (runTcp demoCfg .idle demoTrace).2 = [104, 101, 108, 108, 111]
      ∧ downSent (runTcp demoCfg .idle demoTrace).2 = [111, 107] := by decide

/-- The session ends closed with nothing buffered. -/
theorem demo_ends_closed :
    pending (runTcp demoCfg .idle demoTrace).1 = [] := by decide

/-! ## The DEPLOYED seam: the L4 splice dials exactly `drorb_proxy_pick`

The running dataplane's L4 host shell (`crates/dataplane/src/l4.rs`) never selects
a backend itself — it crosses the exported `drorb_proxy_pick`
(`Reactor.ProxyDial.pick`: `Proxy.selectChain` over the live-health-masked fleet)
per connection, exactly as the reverse-proxy hop does, then dials the id it
returns. This section pins that the L4 forwarding MODEL, when handed the very same
fleet the export runs, chooses the very same backend — so the proven conservation
above is transported onto the deployed pick, not a parallel re-implementation. -/

/-- The L4 forwarding config the deployed host runs: the pool is the
`Reactor.ProxyDial` live-health-masked fleet under its `rendezvousHash` policy
chain, and the selection context carries the connection's affinity key with the
runnable `dialHash`. This is the exact input `drorb_proxy_pick` decodes from
`(mask, key)`. -/
def deployedCfg (mask key : Nat) : Config :=
  { pool := { policies := Reactor.ProxyDial.dialPolicies
              backends := Reactor.ProxyDial.fleet mask }
    ctx  := Reactor.ProxyDial.mkCtx key }

/-- **The model's pick IS the deployed pick.** `chooseUpstream` over the deployed
config is definitionally `Reactor.ProxyDial.pickBackend` — the same
`Proxy.selectChain` the host calls through `drorb_proxy_pick`. No wrapper, no
re-selection. -/
theorem deployed_pick_matches (mask key : Nat) :
    chooseUpstream (deployedCfg mask key).pool (deployedCfg mask key).ctx
      = Reactor.ProxyDial.pickBackend mask key := rfl

/-- **The deployed L4 accept dials the proven pick's backend.** When
`drorb_proxy_pick` (`Reactor.ProxyDial.pick`) returns backend id `i`, the L4
splice machine over the same fleet dials `addrOf` of exactly that backend — and
that backend is a healthy, active, best-tier pool member (`pickBackend_eligible`
transported). A host that dialed anything but the pick's backend, or a pick that
returned an ineligible one, would break this. -/
theorem deployed_accept_dials_pick (mask key : Nat) {b : Proxy.Backend}
    (h : Reactor.ProxyDial.pickBackend mask key = some b) :
    stepTcp (deployedCfg mask key) .idle .accept
        = (.connecting b [], [.connectUpstream (addrOf b)])
      ∧ b ∈ Reactor.ProxyDial.fleet mask
      ∧ b.eligible = true :=
  ⟨accept_dials_choice _ ((deployed_pick_matches mask key).trans h),
   Reactor.ProxyDial.pickBackend_eligible h⟩

/-- **The deployed UDP forward targets the proven pick's backend.** The same tie
for the datagram lane: one client datagram forwards verbatim to `addrOf` of the
`drorb_proxy_pick` backend. -/
theorem deployed_udp_targets_pick (mask key : Nat) {b : Proxy.Backend} (d : Bytes)
    (h : Reactor.ProxyDial.pickBackend mask key = some b) :
    udpStep (deployedCfg mask key) (.fromClient d) = [.toUpstream (addrOf b) d] := by
  have hc : chooseUpstream (deployedCfg mask key).pool (deployedCfg mask key).ctx = some b :=
    (deployed_pick_matches mask key).trans h
  simp [udpStep, hc]

/-- **No eligible backend ⇒ the deployed L4 listener closes, dials nothing.**
When `drorb_proxy_pick` returns empty (whole fleet down / breaker-open), the L4
accept closes the client — the running-path meaning of "no healthy upstream". -/
theorem deployed_accept_none_closes (mask key : Nat)
    (h : Reactor.ProxyDial.pickBackend mask key = none) :
    stepTcp (deployedCfg mask key) .idle .accept = (.closed, [.closeSock]) :=
  accept_none_closes _ ((deployed_pick_matches mask key).trans h)

/-- Concretely: with all three fleet bits up, affinity key 4 homes the L4 splice
to backend 0 (the same deterministic choice `Reactor.ProxyDial`'s runnable checks
pin), dialing `addrOf ⟨0,…⟩`. Ejecting backend 0 (its mask bit clears) moves the
same key to backend 1 — the proven health eject, on the L4 path. -/
example :
    Reactor.Proxy.targetedUpstream (stepTcp (deployedCfg 0b111 4) .idle .accept).2
        = some (addrOf ⟨0,1,0,0,true,.active⟩)
  ∧ Reactor.Proxy.targetedUpstream (stepTcp (deployedCfg 0b110 4) .idle .accept).2
        = some (addrOf ⟨1,1,0,0,true,.active⟩)
  ∧ Reactor.Proxy.targetedUpstream (stepTcp (deployedCfg 0b000 4) .idle .accept).2
        = none := by decide

end Reactor.L4
