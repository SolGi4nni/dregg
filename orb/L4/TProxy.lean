/-!
# L4.TProxy — transparent L4 proxy with original-destination preservation

A *transparent* layer-4 proxy sits inline on a redirected flow: a client opens a
connection to some server address `D`, and the kernel steers it to the proxy
(netfilter REDIRECT recovering `D` with `SO_ORIGINAL_DST`, or a TPROXY rule with
`IP_TRANSPARENT`). The client never learns a proxy is present — it believes it is
talking to `D`. The proxy recovers `D` (the *original destination*), dials it,
and from then on moves bytes verbatim in both directions, exactly the blind
splice of a raw layer-4 forwarder. The one thing that differs from a
load-balanced forwarder is where the upstream target comes from: not a balancer
pick, but the destination the client itself chose, recovered from the kernel.

Three properties separate a genuine transparent proxy from a man-in-the-middle:

  * **`l4_tproxy_preserves_dst`** — the original destination is captured once, at
    accept, and stays the address dialed and the address the client believes it
    reached. It is never rewritten as the stream flows: the select happens at
    accept and no later relay event moves it. A transparent listener (one whose
    remap table is empty) dials exactly the recovered original destination.

  * **`l4_tproxy_bidi`** — the stream is a blind, verbatim, order-preserving
    relay in both directions: the bytes forwarded upstream are exactly the
    client's chunks concatenated in order, and the bytes returned to the client
    are exactly the upstream's — nothing stripped, transformed, reordered, or
    invented.

  * **`l4_tproxy_no_spoof`** — the source address presented to the upstream is
    honest: either the proxy's own address (kernel NAT, the REDIRECT case) or the
    genuine client address the kernel handed us (IP_TRANSPARENT, the TPROXY
    case). It is one of exactly those two authorized values, never a third,
    forged address the upstream might mis-attribute to a peer it trusts.

The model is self-contained: an `Addr` (host bytes + port), a per-connection
relay state, and a small event vocabulary. It re-derives nothing from the wire —
it is a state machine whose transitions are the relay itself.
-/

namespace L4.TProxy

/-- A byte string. -/
abbrev Bytes := List UInt8

/-- A transport address: host bytes (v4/v6 octets, uninterpreted) and a port. -/
structure Addr where
  /-- Host octets, exactly as the kernel reports them. -/
  host : Bytes
  /-- Transport port. -/
  port : Nat
deriving DecidableEq, Repr

/-- How the flow was intercepted, which fixes the source-address posture toward
the upstream. `redirect` (netfilter REDIRECT + `SO_ORIGINAL_DST`) is NATed: the
upstream sees the proxy. `tproxy` (`IP_TRANSPARENT`) spoofs the genuine client:
the upstream sees the real client address the kernel handed the proxy. -/
inductive TMode where
  /-- REDIRECT / `SO_ORIGINAL_DST`: upstream sees the proxy's own address. -/
  | redirect
  /-- TPROXY / `IP_TRANSPARENT`: upstream sees the genuine client address. -/
  | tproxy
deriving DecidableEq, Repr

/-- A relay event: a verbatim chunk of client bytes to forward upstream, or a
verbatim chunk of upstream bytes to forward back to the client. -/
inductive Event where
  /-- Client bytes bound for the upstream, forwarded verbatim. -/
  | clientData (d : Bytes)
  /-- Upstream bytes bound for the client, forwarded verbatim. -/
  | upstreamData (d : Bytes)
deriving DecidableEq, Repr

/-- A transparent connection's relay state. `origDst` and `clientSrc` are
captured from the kernel at accept and never touched again; `mode` fixes the
source posture; `upSent`/`downSent` accumulate the two verbatim byte lanes. -/
structure Conn where
  /-- The original destination the client dialed (recovered from the kernel). -/
  origDst   : Addr
  /-- The genuine client source address the kernel handed the proxy. -/
  clientSrc : Addr
  /-- The interception mode (REDIRECT vs TPROXY). -/
  mode      : TMode
  /-- Bytes forwarded upstream so far, in order. -/
  upSent    : Bytes
  /-- Bytes forwarded to the client so far, in order. -/
  downSent  : Bytes
deriving DecidableEq, Repr

/-- One relay step: append the chunk to its direction's lane, verbatim. The
destination, client source, and mode are never read or written here — the
relay is byte-transport only. -/
def step (c : Conn) : Event → Conn
  | .clientData d   => { c with upSent := c.upSent ++ d }
  | .upstreamData d => { c with downSent := c.downSent ++ d }

/-- Run a whole event trace against a connection. -/
def run (c : Conn) (evs : List Event) : Conn := evs.foldl step c

/-! ## Byte-accounting projections -/

/-- The client bytes a trace carries toward the upstream, in order. -/
def clientPayload : List Event → Bytes
  | [] => []
  | .clientData d :: r => d ++ clientPayload r
  | .upstreamData _ :: r => clientPayload r

/-- The upstream bytes a trace carries toward the client, in order. -/
def upstreamPayload : List Event → Bytes
  | [] => []
  | .upstreamData d :: r => d ++ upstreamPayload r
  | .clientData _ :: r => upstreamPayload r

/-! ## The upstream select

A transparent listener may carry a `remap` override table — but a *transparent*
listener has an empty one, so it dials the recovered original destination
itself. `dial` is the whole dependence of the upstream target on the flow: the
original destination, optionally overridden. -/

/-- A transparent listener. `remap` is an optional per-destination override; a
genuinely transparent listener leaves it empty (`fun _ => none`). -/
structure Listener where
  /-- Optional override for an original destination; `none` = dial it directly. -/
  remap : Addr → Option Addr

/-- Dial an upstream for an original destination: the override if present, else
the original destination itself (the transparent default). -/
def dial (l : Listener) (origDst : Addr) : Addr :=
  match l.remap origDst with
  | some a => a
  | none   => origDst

/-- The address the client believes it reached: on a transparent flow, the
original destination it dialed — the proxy never announces itself. -/
def apparentServer (c : Conn) : Addr := c.origDst

/-! ## The source posture -/

/-- The source address the proxy presents to the upstream, by interception mode:
the proxy's own address under REDIRECT (NAT), the genuine client under TPROXY. -/
def presentedSrc (proxyAddr : Addr) (c : Conn) : Addr :=
  match c.mode with
  | .redirect => proxyAddr
  | .tproxy   => c.clientSrc

/-- The two addresses a transparent proxy is authorized to source from: its own,
and the genuine client the kernel handed it. -/
def authorizedSources (proxyAddr : Addr) (c : Conn) : List Addr :=
  [proxyAddr, c.clientSrc]

/-! ## Relay invariants -/

/-- A relay step never touches the original destination. -/
theorem step_origDst (c : Conn) (e : Event) : (step c e).origDst = c.origDst := by
  cases e <;> rfl

/-- **The original destination is fixed at accept.** No relay event moves it, so
after any trace it is exactly what was captured. -/
theorem run_origDst (c : Conn) (evs : List Event) :
    (run c evs).origDst = c.origDst := by
  induction evs generalizing c with
  | nil => rfl
  | cons e evs ih =>
    show (run (step c e) evs).origDst = c.origDst
    rw [ih (step c e), step_origDst]

/-- Every client chunk lands verbatim on the upstream lane, in order (append
form: the lane afterward is what it held plus the trace's client payload). -/
theorem run_upSent (c : Conn) (evs : List Event) :
    (run c evs).upSent = c.upSent ++ clientPayload evs := by
  induction evs generalizing c with
  | nil => simp [run, clientPayload]
  | cons e evs ih =>
    show (run (step c e) evs).upSent = c.upSent ++ clientPayload (e :: evs)
    rw [ih (step c e)]
    cases e <;> simp [step, clientPayload, List.append_assoc]

/-- Every upstream chunk lands verbatim on the client lane, in order. -/
theorem run_downSent (c : Conn) (evs : List Event) :
    (run c evs).downSent = c.downSent ++ upstreamPayload evs := by
  induction evs generalizing c with
  | nil => simp [run, upstreamPayload]
  | cons e evs ih =>
    show (run (step c e) evs).downSent = c.downSent ++ upstreamPayload (e :: evs)
    rw [ih (step c e)]
    cases e <;> simp [step, upstreamPayload, List.append_assoc]

/-! ## The theorems -/

/-- **Original destination preserved.** For a transparent listener (empty remap
table) over any relay trace: the connection's original destination is unchanged
by the relay, the address the listener dials for it is exactly that original
destination, and the address the client believes it reached is that same
original destination. The transparency hypothesis is load-bearing — a listener
with a nonempty remap could dial elsewhere and break the middle conjunct. -/
theorem l4_tproxy_preserves_dst (l : Listener) (c : Conn) (evs : List Event)
    (htrans : ∀ a, l.remap a = none) :
    (run c evs).origDst = c.origDst
      ∧ dial l (run c evs).origDst = c.origDst
      ∧ apparentServer (run c evs) = c.origDst := by
  have ho := run_origDst c evs
  refine ⟨ho, ?_, ?_⟩
  · rw [ho]; simp [dial, htrans]
  · simp [apparentServer, ho]

/-- **Bidirectional verbatim relay.** For a freshly accepted connection (both
byte lanes empty), after any trace the bytes forwarded upstream are exactly the
client's chunks concatenated in order, and the bytes forwarded to the client are
exactly the upstream's — nothing stripped, transformed, reordered, or invented
in either direction. -/
theorem l4_tproxy_bidi (c : Conn) (evs : List Event)
    (hu : c.upSent = []) (hd : c.downSent = []) :
    (run c evs).upSent = clientPayload evs
      ∧ (run c evs).downSent = upstreamPayload evs := by
  refine ⟨?_, ?_⟩
  · rw [run_upSent, hu, List.nil_append]
  · rw [run_downSent, hd, List.nil_append]

/-- **No source spoof.** The source presented to the upstream is one of exactly
the two addresses the proxy is authorized to use: its own address, or the
genuine client address the kernel captured. It is never a third, forged
address. -/
theorem l4_tproxy_no_spoof (proxyAddr : Addr) (c : Conn) :
    presentedSrc proxyAddr c ∈ authorizedSources proxyAddr c := by
  unfold presentedSrc authorizedSources
  cases c.mode
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_self)

/-- **No source spoof, exclusion form.** Any address that is neither the proxy's
own nor the genuine client's is never presented to the upstream — a concrete
witness that the two-element authorization is exhaustive, not vacuous. The two
inequality hypotheses are the whole content: drop either and the claim is
false. -/
theorem l4_tproxy_no_spoof_excludes (proxyAddr evil : Addr) (c : Conn)
    (h1 : evil ≠ proxyAddr) (h2 : evil ≠ c.clientSrc) :
    presentedSrc proxyAddr c ≠ evil := by
  unfold presentedSrc
  cases c.mode
  · exact fun he => h1 he.symm
  · exact fun he => h2 he.symm

/-! ## A concrete session

A transparent flow to `93.184.216.34:443` from client `10.0.0.7:51000`,
intercepted in TPROXY mode. The relay splices a TLS `ClientHello` prefix up, a
`ServerHello` prefix down, and more client bytes up — verbatim — while the
original destination never moves. -/

/-- A demo transparent connection: freshly accepted, TPROXY mode. -/
def demoConn : Conn :=
  { origDst   := ⟨[93, 184, 216, 34], 443⟩
    clientSrc := ⟨[10, 0, 0, 7], 51000⟩
    mode      := .tproxy
    upSent    := []
    downSent  := [] }

/-- A demo relay trace. -/
def demoTrace : List Event :=
  [ .clientData [22, 3, 1]      -- TLS record header, client → upstream
  , .upstreamData [22, 3, 3]    -- TLS record header, upstream → client
  , .clientData [1, 2, 3] ]     -- more client bytes

/-- The upstream lane is the client chunks verbatim, in order; the client lane
is the upstream chunks verbatim; the original destination is unmoved. -/
example :
    (run demoConn demoTrace).upSent = [22, 3, 1, 1, 2, 3]
      ∧ (run demoConn demoTrace).downSent = [22, 3, 3]
      ∧ (run demoConn demoTrace).origDst = demoConn.origDst := by decide

/-- In TPROXY mode the source presented to the upstream is the genuine client. -/
example : presentedSrc ⟨[10, 0, 0, 1], 0⟩ demoConn = ⟨[10, 0, 0, 7], 51000⟩ := by
  decide

/-- A transparent listener dials the original destination directly. -/
example :
    dial ⟨fun _ => none⟩ demoConn.origDst = ⟨[93, 184, 216, 34], 443⟩ := by decide

end L4.TProxy
