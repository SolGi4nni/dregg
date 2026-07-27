/-!
# L4.UdpRelay — connectionless (UDP) layer-4 datagram relay

The TCP L4 splice moves a *stream*: accept, dial an upstream, then move an
ordered byte stream verbatim in both directions until each half closes. UDP has
no connection and no stream — it moves *datagrams*, each an independent,
boundary-preserved message with no ordering guarantee between them. A UDP L4
relay is therefore built around a **session table** rather than a per-connection
state machine: the listener keys each client by its transport flow, binds that
flow to a freshly chosen upstream target (with its own upstream socket `fd`),
and from then on every datagram of that flow is forwarded, verbatim and boundary
preserved, to the same upstream — replies coming back on that `fd` return to the
originating client flow.

Three properties are proven here, over the relay's own datagram step:

* **`udp_relay_faithful`** — the relay is verbatim in *both* directions. Over any
  trace, the list of datagrams forwarded upstream is exactly the list of client
  datagrams (payload for payload, boundaries preserved, order kept), and the list
  of datagrams returned to the client is exactly the list of upstream replies. A
  relay that split, coalesced, dropped, reordered, or rewrote a datagram would
  break one of these two equalities. (The reply direction is stated over the
  well-formed traces where every reply arrives on a `fd` the relay actually
  opened — replies from an unbound `fd` are dropped, never misdelivered.)

* **`udp_relay_flow`** — a transport flow maps to *one* consistent upstream. The
  first datagram of a flow binds it to a chosen upstream `fd`; every later
  datagram of the *same* flow forwards to that same `fd` and upstream target,
  never re-choosing. So the datagrams of one flow all reach one backend — session
  affinity, proven, not a fresh pick per packet.

* **`udp_relay_no_amplification`** — the relay never sends more bytes upstream
  than it received from the client. Each client datagram forwards to at most one
  upstream datagram carrying the *same* payload, and nothing else emits an
  upstream datagram, so the total upstream byte count is bounded by the total
  client byte count. A relay that duplicated, padded, or retransmitted a datagram
  could be turned into a traffic amplifier; this rules that out.

The relay is parametric in an upstream `Pool`; the concrete selection here is a
round-robin over the pool keyed by a per-new-flow generation counter (any pure
selection would do — the affinity theorem holds regardless, because the *binding*
pins the choice, not the selector).
-/

namespace L4.UdpRelay

/-- A datagram payload: a raw byte string. -/
abbrev Bytes := List UInt8

/-! ## Flows, upstreams, and the session table -/

/-- A transport **flow** — the 5-tuple that identifies a client's datagram
stream: source and destination address/port plus the transport protocol. For a
UDP listener `proto` is fixed, but it is carried so the key is a genuine 5-tuple
(a relay that also fronts other datagram protocols keys on the same shape). -/
structure Flow where
  srcIp   : Nat
  srcPort : Nat
  dstIp   : Nat
  dstPort : Nat
  proto   : Nat
deriving DecidableEq, Repr

/-- An upstream datagram target: an address and a port. -/
structure Upstream where
  host : Nat
  port : Nat
deriving DecidableEq, Repr

/-- The upstream pool the relay forwards to. -/
structure Pool where
  backends : List Upstream
deriving Repr

/-- Choose an upstream for a new flow: round-robin over the pool keyed by the
`gen` counter (bumped once per newly seen flow). `none` exactly when the pool is
empty — no backend to forward to. -/
def Pool.pick (p : Pool) (gen : Nat) : Option Upstream :=
  p.backends[gen % p.backends.length]?

/-- A session-table entry: a client `flow`, the upstream socket `fd` opened for
it, and the `upstream` target that `fd` talks to. -/
structure Binding where
  flow     : Flow
  fd       : Nat
  upstream : Upstream
deriving DecidableEq, Repr

/-- The relay's mutable state: the upstream `pool`, the round-robin `gen`
counter, the next upstream socket `fd` to hand out, and the session `bindings`
built so far (most recent first). -/
structure Relay where
  pool     : Pool
  gen      : Nat
  fdNext   : Nat
  bindings : List Binding
deriving Repr

/-- Find the session bound to a client `flow`, if any. -/
def Relay.lookup (r : Relay) (f : Flow) : Option Binding :=
  r.bindings.find? (fun b => decide (b.flow = f))

/-- Find the session that owns an upstream `fd`, if any (reply routing). -/
def Relay.lookupFd (r : Relay) (fd : Nat) : Option Binding :=
  r.bindings.find? (fun b => decide (b.fd = fd))

/-! ## The datagram step -/

/-- The relay's wire effects. Datagrams are addressed, not connected, so the
upstream `fd`/target rides on every upstream send, and the client `flow` on every
reply. -/
inductive Effect where
  /-- Forward `payload` to upstream `up` over socket `fd`, one datagram. -/
  | toUpstream (fd : Nat) (up : Upstream) (payload : Bytes)
  /-- Return `payload` to the client `flow`, one datagram. -/
  | toClient   (flow : Flow) (payload : Bytes)
deriving DecidableEq, Repr

/-- A relay event: a datagram from a client flow, or a reply on an upstream fd. -/
inductive Event where
  /-- A client datagram on `flow` carrying `payload`. -/
  | client   (flow : Flow) (payload : Bytes)
  /-- An upstream reply datagram on socket `fd` carrying `payload`. -/
  | upstream (fd : Nat) (payload : Bytes)
deriving Repr

/-- **The client-datagram step.** If the flow is already bound, forward the
datagram verbatim on its existing `fd`/upstream — no re-selection. Otherwise pick
an upstream (round-robin), open the next `fd`, record the binding, and forward.
An empty pool drops the datagram (no misroute). One datagram in, at most one
out. -/
def stepClient (r : Relay) (f : Flow) (d : Bytes) : Relay × List Effect :=
  match r.lookup f with
  | some b => (r, [.toUpstream b.fd b.upstream d])
  | none   =>
    match r.pool.pick r.gen with
    | some up =>
      let b : Binding := ⟨f, r.fdNext, up⟩
      ({ r with gen := r.gen + 1, fdNext := r.fdNext + 1, bindings := b :: r.bindings },
       [.toUpstream b.fd up d])
    | none => (r, [])

/-- **The upstream-reply step.** A reply on `fd` returns verbatim to the flow that
owns `fd`; a reply on an unknown `fd` is dropped (never misdelivered). -/
def stepUpstream (r : Relay) (fd : Nat) (d : Bytes) : Relay × List Effect :=
  match r.lookupFd fd with
  | some b => (r, [.toClient b.flow d])
  | none   => (r, [])

/-- One event against the relay state. -/
def step (r : Relay) : Event → Relay × List Effect
  | .client f d   => stepClient r f d
  | .upstream fd d => stepUpstream r fd d

/-- Run a whole event trace, threading the state and concatenating effects. -/
def run (r : Relay) : List Event → Relay × List Effect
  | [] => (r, [])
  | e :: es =>
    ((run (step r e).1 es).1, (step r e).2 ++ (run (step r e).1 es).2)

/-! ## Datagram projections -/

/-- Upstream-bound datagram payloads, in order, boundaries kept (a *list*, not a
flattening — datagram boundaries are UDP semantics). -/
def upPayloads : List Effect → List Bytes
  | [] => []
  | .toUpstream _ _ d :: r => d :: upPayloads r
  | _ :: r => upPayloads r

/-- Client-bound (reply) datagram payloads, in order, boundaries kept. -/
def downPayloads : List Effect → List Bytes
  | [] => []
  | .toClient _ d :: r => d :: downPayloads r
  | _ :: r => downPayloads r

/-- The client datagrams an event trace carries, in order. -/
def clientPayloads : List Event → List Bytes
  | [] => []
  | .client _ d :: es => d :: clientPayloads es
  | _ :: es => clientPayloads es

/-- The upstream reply datagrams an event trace carries, in order. -/
def upstreamPayloads : List Event → List Bytes
  | [] => []
  | .upstream _ d :: es => d :: upstreamPayloads es
  | _ :: es => upstreamPayloads es

/-- Total bytes forwarded upstream. -/
def upBytes : List Effect → Nat
  | [] => 0
  | .toUpstream _ _ d :: r => d.length + upBytes r
  | _ :: r => upBytes r

/-- Total client bytes received over a trace. -/
def clientBytesIn : List Event → Nat
  | [] => 0
  | .client _ d :: es => d.length + clientBytesIn es
  | _ :: es => clientBytesIn es

theorem upPayloads_append (xs ys : List Effect) :
    upPayloads (xs ++ ys) = upPayloads xs ++ upPayloads ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [upPayloads, ih]

theorem downPayloads_append (xs ys : List Effect) :
    downPayloads (xs ++ ys) = downPayloads xs ++ downPayloads ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [downPayloads, ih]

theorem upBytes_append (xs ys : List Effect) :
    upBytes (xs ++ ys) = upBytes xs + upBytes ys := by
  induction xs with
  | nil => simp [upBytes]
  | cons x rest ih => cases x <;> simp [upBytes, ih, Nat.add_assoc]

/-! ## Structural facts about the step -/

/-- The upstream pool is never touched by a step (only `gen`/`fdNext`/`bindings`
change) — so pool-nonemptiness is preserved for free. -/
theorem step_pool (r : Relay) (e : Event) : (step r e).1.pool = r.pool := by
  cases e with
  | client f d =>
    show (stepClient r f d).1.pool = r.pool
    unfold stepClient
    cases r.lookup f with
    | some b => rfl
    | none => cases r.pool.pick r.gen <;> rfl
  | upstream fd d =>
    show (stepUpstream r fd d).1.pool = r.pool
    unfold stepUpstream
    cases r.lookupFd fd <;> rfl

/-- A nonempty pool always yields a pick. -/
theorem pick_isSome (p : Pool) (gen : Nat) (h : p.backends ≠ []) :
    (p.pick gen).isSome := by
  have hlen : 0 < p.backends.length := List.length_pos_iff.mpr h
  have hi : gen % p.backends.length < p.backends.length := Nat.mod_lt _ hlen
  simp [Pool.pick, List.getElem?_eq_getElem hi]

/-! ## Faithfulness, client → upstream -/

/-- With a backend available, one client datagram forwards verbatim upstream and
emits nothing downstream. -/
theorem stepClient_forwards (r : Relay) (f : Flow) (d : Bytes)
    (h : r.pool.backends ≠ []) :
    upPayloads (stepClient r f d).2 = [d]
      ∧ downPayloads (stepClient r f d).2 = [] := by
  unfold stepClient
  cases hl : r.lookup f with
  | some b => simp [upPayloads, downPayloads]
  | none =>
    obtain ⟨up, hp⟩ := Option.isSome_iff_exists.mp (pick_isSome r.pool r.gen h)
    simp [hp, upPayloads, downPayloads]

/-- An upstream reply contributes no upstream-bound datagrams. -/
theorem stepUpstream_no_up (r : Relay) (fd : Nat) (d : Bytes) :
    upPayloads (stepUpstream r fd d).2 = [] := by
  unfold stepUpstream
  cases r.lookupFd fd <;> simp [upPayloads]

/-- **Client→upstream faithfulness.** Over any trace (with a nonempty pool so no
datagram is dropped), the datagrams forwarded upstream are EXACTLY the client's
datagrams — payload for payload, boundaries preserved, order kept. -/
theorem run_up_faithful (r : Relay) (evs : List Event) (h : r.pool.backends ≠ []) :
    upPayloads (run r evs).2 = clientPayloads evs := by
  induction evs generalizing r with
  | nil => rfl
  | cons e es ih =>
    have hpool : (step r e).1.pool.backends ≠ [] := by rw [step_pool]; exact h
    simp only [run, upPayloads_append]
    cases e with
    | client f d =>
      have hstep := (stepClient_forwards r f d h).1
      rw [ih (step r (.client f d)).1 hpool]
      simp only [step] at hstep ⊢
      rw [hstep]; rfl
    | upstream fd d =>
      have hstep := stepUpstream_no_up r fd d
      rw [ih (step r (.upstream fd d)).1 hpool]
      simp only [step] at hstep ⊢
      rw [hstep]; rfl

/-! ## Faithfulness, upstream → client -/

/-- A reply is well-formed exactly when its `fd` names an open session (client
datagrams are always well-formed). Replies on unknown `fd`s are dropped. -/
def replyOk (r : Relay) : Event → Bool
  | .upstream fd _ => (r.lookupFd fd).isSome
  | .client _ _    => true

/-- The reply guard over a trace (threaded through the evolving state). -/
def goodReplies (r : Relay) : List Event → Bool
  | [] => true
  | e :: es => replyOk r e && goodReplies (step r e).1 es

/-- A client datagram contributes no client-bound (reply) datagrams. -/
theorem stepClient_no_down (r : Relay) (f : Flow) (d : Bytes) :
    downPayloads (stepClient r f d).2 = [] := by
  unfold stepClient
  cases r.lookup f with
  | some b => simp [downPayloads]
  | none => cases r.pool.pick r.gen <;> simp [downPayloads]

/-- A well-formed reply returns its payload verbatim to the owning flow. -/
theorem stepUpstream_down (r : Relay) (fd : Nat) (d : Bytes) (b : Binding)
    (h : r.lookupFd fd = some b) :
    downPayloads (stepUpstream r fd d).2 = [d] := by
  unfold stepUpstream
  simp [h, downPayloads]

/-- **Upstream→client faithfulness.** Over any well-formed trace (every reply on a
`fd` the relay opened), the datagrams returned to the client are EXACTLY the
upstream replies — payload for payload, boundaries preserved, order kept. -/
theorem run_down_faithful (r : Relay) (evs : List Event)
    (h : goodReplies r evs = true) :
    downPayloads (run r evs).2 = upstreamPayloads evs := by
  induction evs generalizing r with
  | nil => rfl
  | cons e es ih =>
    rw [goodReplies, Bool.and_eq_true] at h
    simp only [run, downPayloads_append]
    cases e with
    | client f d =>
      have hstep := stepClient_no_down r f d
      rw [ih (step r (.client f d)).1 h.2]
      simp only [step, upstreamPayloads] at hstep ⊢
      rw [hstep]; rfl
    | upstream fd d =>
      have hok : (r.lookupFd fd).isSome = true := by
        have := h.1; simpa [replyOk] using this
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hok
      have hstep := stepUpstream_down r fd d b hb
      rw [ih (step r (.upstream fd d)).1 h.2]
      simp only [step, upstreamPayloads] at hstep ⊢
      rw [hstep]; rfl

/-- **Datagram relay faithfulness, both directions.** Client datagrams reach the
upstream verbatim and boundary-preserved; upstream replies reach the client the
same way. Nothing is split, coalesced, dropped, reordered, or rewritten. -/
theorem udp_relay_faithful (r : Relay) (evs : List Event)
    (hpool : r.pool.backends ≠ [])
    (hreplies : goodReplies r evs = true) :
    upPayloads (run r evs).2 = clientPayloads evs
      ∧ downPayloads (run r evs).2 = upstreamPayloads evs :=
  ⟨run_up_faithful r evs hpool, run_down_faithful r evs hreplies⟩

/-! ## Flow affinity: one flow, one upstream -/

/-- A bound flow stays bound to the *same* session across any step — a client
step for that flow reuses the binding (state unchanged); a step for a different
flow only ever prepends a fresh, distinct-keyed entry; a reply step never touches
the table. So the binding a flow got on its first datagram is the binding it keeps. -/
theorem lookup_stable (r : Relay) (e : Event) (f : Flow) (b : Binding)
    (h : r.lookup f = some b) :
    (step r e).1.lookup f = some b := by
  cases e with
  | client g d =>
    show (stepClient r g d).1.lookup f = some b
    unfold stepClient
    cases hg : r.lookup g with
    | some b' => simpa [hg] using h
    | none =>
      cases hp : r.pool.pick r.gen with
      | some up =>
        have hgf : decide (g = f) = false := by
          rw [decide_eq_false_iff_not]
          intro heq; subst heq
          rw [h] at hg; exact absurd hg (Option.some_ne_none b)
        simp only [hp, Relay.lookup, List.find?]
        simp only [hgf]
        simpa [Relay.lookup] using h
      | none => simpa [hp] using h
  | upstream fd d =>
    show (stepUpstream r fd d).1.lookup f = some b
    unfold stepUpstream
    cases r.lookupFd fd with
    | some b' => simpa using h
    | none => simpa using h

/-- A client datagram on an already-bound flow forwards on that flow's own
`fd`/upstream, leaving the state untouched. -/
theorem stepClient_bound (r : Relay) (f : Flow) (d : Bytes) (b : Binding)
    (h : r.lookup f = some b) :
    step r (.client f d) = (r, [.toUpstream b.fd b.upstream d]) := by
  simp [step, stepClient, h]

/-- Over a trace of client datagrams all on one already-bound flow, every
forwarded datagram targets that flow's single `fd`/upstream. -/
theorem run_flow_consistent (r : Relay) (f : Flow) (b : Binding) (ds : List Bytes)
    (h : r.lookup f = some b) :
    ∀ eff ∈ (run r (ds.map (fun d => Event.client f d))).2,
      ∃ d, eff = .toUpstream b.fd b.upstream d := by
  induction ds generalizing r with
  | nil => intro eff hmem; simp [run] at hmem
  | cons d ds ih =>
    intro eff hmem
    simp only [List.map_cons, run] at hmem
    rw [stepClient_bound r f d b h] at hmem
    simp only [List.singleton_append, List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · exact ⟨d, heq⟩
    · exact ih r h eff hmem

/-- **Flow affinity.** The datagrams of a single client flow all reach ONE
upstream. The first datagram binds the flow to a chosen `fd`/upstream; every
datagram of that flow — including the first — forwards to exactly that same `fd`
and upstream, never re-choosing per packet. (Nonempty pool, so the first datagram
binds rather than drops.) -/
theorem udp_relay_flow (r : Relay) (f : Flow) (d0 : Bytes) (ds : List Bytes)
    (hpool : r.pool.backends ≠ []) :
    ∃ b : Binding, ∀ eff ∈ (run r ((d0 :: ds).map (fun d => Event.client f d))).2,
      ∃ d, eff = .toUpstream b.fd b.upstream d := by
  -- The first datagram either finds an existing binding or creates one; either
  -- way the flow is bound to a single session `b` afterward, and the first
  -- forwarded datagram targets it.
  obtain ⟨b, hb, heff0⟩ :
      ∃ b, (step r (.client f d0)).1.lookup f = some b
         ∧ (step r (.client f d0)).2 = [Effect.toUpstream b.fd b.upstream d0] := by
    show ∃ b, (stepClient r f d0).1.lookup f = some b
           ∧ (stepClient r f d0).2 = [Effect.toUpstream b.fd b.upstream d0]
    unfold stepClient
    cases hl : r.lookup f with
    | some b => exact ⟨b, by simp [hl], by simp [hl]⟩
    | none =>
      obtain ⟨up, hp⟩ := Option.isSome_iff_exists.mp (pick_isSome r.pool r.gen hpool)
      refine ⟨⟨f, r.fdNext, up⟩, ?_, by simp [hp]⟩
      simp [hp, Relay.lookup, List.find?]
  refine ⟨b, ?_⟩
  intro eff hmem
  simp only [List.map_cons, run] at hmem
  rw [heff0] at hmem
  simp only [List.singleton_append, List.mem_cons] at hmem
  rcases hmem with heq | hmem
  · exact ⟨d0, heq⟩
  · exact run_flow_consistent (step r (.client f d0)).1 f b ds hb eff hmem

/-! ## No amplification -/

/-- A client datagram forwards at most its own bytes upstream. -/
theorem stepClient_upBytes (r : Relay) (f : Flow) (d : Bytes) :
    upBytes (stepClient r f d).2 ≤ d.length := by
  unfold stepClient
  cases r.lookup f with
  | some b => simp [upBytes]
  | none => cases r.pool.pick r.gen <;> simp [upBytes]

/-- An upstream reply forwards zero bytes upstream. -/
theorem stepUpstream_upBytes (r : Relay) (fd : Nat) (d : Bytes) :
    upBytes (stepUpstream r fd d).2 = 0 := by
  unfold stepUpstream
  cases r.lookupFd fd <;> simp [upBytes]

/-- **No amplification.** Over any trace, the total bytes the relay forwards
upstream never exceed the total bytes it received from clients. Each client
datagram forwards to at most one upstream datagram with the same payload, and no
other event emits upstream, so a relay cannot be turned into a byte amplifier. -/
theorem udp_relay_no_amplification (r : Relay) (evs : List Event) :
    upBytes (run r evs).2 ≤ clientBytesIn evs := by
  induction evs generalizing r with
  | nil => simp [run, upBytes, clientBytesIn]
  | cons e es ih =>
    simp only [run, upBytes_append]
    cases e with
    | client f d =>
      have h1 := stepClient_upBytes r f d
      have h2 := ih (step r (.client f d)).1
      simp only [step, clientBytesIn] at h1 h2 ⊢
      omega
    | upstream fd d =>
      have h1 := stepUpstream_upBytes r fd d
      have h2 := ih (step r (.upstream fd d)).1
      simp only [step, clientBytesIn] at h1 h2 ⊢
      omega

/-! ## Non-vacuity: the hypotheses are jointly satisfiable

A concrete relay over a real two-backend pool and a real trace — a client
datagram (binds the flow to `fd 100`), an upstream reply on that `fd`, then a
second client datagram of the same flow — satisfies both faithfulness
hypotheses, so the theorems above are not vacuous. -/

/-- A concrete relay: two backends, no sessions yet, fds handed out from 100. -/
def demoRelay : Relay :=
  ⟨⟨[⟨0x0a000001, 5300⟩, ⟨0x0a000002, 5300⟩]⟩, 0, 100, []⟩

/-- A concrete flow (a UDP 5-tuple, `proto = 17`). -/
def demoFlow : Flow := ⟨0xc0a80001, 41000, 0x0a000000, 53, 17⟩

/-- A real trace: forward, reply on the opened fd, forward again. -/
def demoTrace : List Event :=
  [ .client demoFlow [0x01, 0x02, 0x03]
  , .upstream 100 [0x09, 0x09]
  , .client demoFlow [0x04] ]

/-- The faithfulness hypotheses hold for the concrete trace (nonempty pool, every
reply on an opened fd) — witnessing non-vacuity. -/
theorem demo_hyps :
    demoRelay.pool.backends ≠ [] ∧ goodReplies demoRelay demoTrace = true := by
  refine ⟨by decide, by decide⟩

/-- Applied concretely: both client datagrams reach the upstream verbatim and
boundary-preserved, and the reply reaches the client verbatim. -/
theorem demo_relayed :
    upPayloads (run demoRelay demoTrace).2 = [[0x01, 0x02, 0x03], [0x04]]
      ∧ downPayloads (run demoRelay demoTrace).2 = [[0x09, 0x09]] := by
  refine ⟨by decide, by decide⟩

/-! ## Bounded, single-pass execution: a crash-safe tail-recursive runner

`run` above is the *specification*: clean to reason about, but structurally
non-tail-recursive — it rebuilds each suffix's effect list with `++` *after* the
recursive call, so the control stack grows with the trace length — and it names
the recursive call `run (step r e).1 es` twice, so kernel / `decide` reduction
re-evaluates each suffix and blows up exponentially. A relay is driven by an
adversarial client that sends an unbounded datagram trace; the same
non-tail-recursion class that crashes a naive byte-loop crashes this reducer.

`runTail` is the operational runner: one left-to-right pass with a
reverse-accumulator — tail-recursive (constant control stack, no matter how long
the trace) and linear (each event stepped exactly once, no re-evaluation). It is
proven *equal* to `run` (`runTail_eq_run`), so every faithfulness / flow-affinity
/ no-amplification guarantee transfers to it verbatim: the crash-safe fast path
and the specified path are literally the same function. -/

/-- Tail-recursive worker: thread the relay state left to right, pushing each
step's effects (reversed) onto `acc`. Sole recursive call is in tail position;
each event is stepped once. -/
def runAcc (r : Relay) (acc : List Effect) : List Event → Relay × List Effect
  | [] => (r, acc.reverse)
  | e :: es => runAcc (step r e).1 ((step r e).2.reverseAux acc) es

/-- The operational, crash-safe runner: a single bounded pass over the trace. -/
def runTail (r : Relay) (evs : List Event) : Relay × List Effect :=
  runAcc r [] evs

/-- The worker computes `run`'s state and, in the accumulator, `run`'s effects
prefixed by whatever was already accumulated (stored reversed). The bridge that
makes the fast path equal to the spec. -/
theorem runAcc_spec (r : Relay) (acc : List Effect) (evs : List Event) :
    runAcc r acc evs = ((run r evs).1, acc.reverse ++ (run r evs).2) := by
  induction evs generalizing r acc with
  | nil => simp [runAcc, run]
  | cons e es ih =>
    rw [runAcc, ih (step r e).1 ((step r e).2.reverseAux acc)]
    simp only [run]
    simp [List.reverseAux_eq, List.reverse_append, List.append_assoc]

/-- **The tail-recursive runner is the specification.** `runTail` — a single
bounded, tail-recursive pass — computes exactly `run`. All guarantees below are
therefore guarantees about the crash-safe operational runner. -/
theorem runTail_eq_run (r : Relay) (evs : List Event) :
    runTail r evs = run r evs := by
  simp [runTail, runAcc_spec]

/-- **Crash-safe by construction in COMPILED code.** `runTail_eq_run` alone only
rewrites *proofs*; the code generator still emitted the non-tail-recursive `run`
body (whose control stack grows with the trace and whose doubled recursive call
re-evaluates each suffix) for every native / leanc caller of `run`. This
`@[csimp]` lemma installs `runTail` as `run`'s compiled implementation, so an
adversarial client streaming an unbounded datagram trace drives a constant-stack,
single-pass loop — the same non-tail-recursion crash class the `Body.Chunked`
audit closed, closed here for the datagram relay. Kernel reduction / `decide` on
`run` is untouched (the proofs still see the spec body). -/
@[csimp] theorem run_eq_runTail : @run = @runTail := by
  funext r evs; exact (runTail_eq_run r evs).symm

/-- **Faithfulness, on the crash-safe runner.** Client datagrams reach the
upstream verbatim and boundary-preserved; upstream replies reach the client the
same way — under a single bounded pass. -/
theorem udp_relay_faithful_tail (r : Relay) (evs : List Event)
    (hpool : r.pool.backends ≠ [])
    (hreplies : goodReplies r evs = true) :
    upPayloads (runTail r evs).2 = clientPayloads evs
      ∧ downPayloads (runTail r evs).2 = upstreamPayloads evs := by
  rw [runTail_eq_run]; exact udp_relay_faithful r evs hpool hreplies

/-- **No amplification, on the crash-safe runner.** Bytes forwarded upstream never
exceed bytes received from clients — under a single bounded pass. -/
theorem udp_relay_no_amplification_tail (r : Relay) (evs : List Event) :
    upBytes (runTail r evs).2 ≤ clientBytesIn evs := by
  rw [runTail_eq_run]; exact udp_relay_no_amplification r evs

/-- **Flow affinity, on the crash-safe runner.** The datagrams of a single client
flow all reach ONE upstream — under a single bounded pass. -/
theorem udp_relay_flow_tail (r : Relay) (f : Flow) (d0 : Bytes) (ds : List Bytes)
    (hpool : r.pool.backends ≠ []) :
    ∃ b : Binding, ∀ eff ∈ (runTail r ((d0 :: ds).map (fun d => Event.client f d))).2,
      ∃ d, eff = .toUpstream b.fd b.upstream d := by
  rw [runTail_eq_run]; exact udp_relay_flow r f d0 ds hpool

/-- The crash-safe runner, evaluated *in the kernel* on the concrete demo trace:
both client datagrams reach the upstream verbatim and the reply returns verbatim.
`decide` reduces `runTail` itself, exercising the tail-recursive path end to end
(the exponential `run` reducer is never invoked here). -/
theorem demo_runTail_effects :
    upPayloads (runTail demoRelay demoTrace).2 = [[0x01, 0x02, 0x03], [0x04]]
      ∧ downPayloads (runTail demoRelay demoTrace).2 = [[0x09, 0x09]] := by
  refine ⟨by decide, by decide⟩


end L4.UdpRelay
