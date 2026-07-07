import Crypto

/-!
# WireGuard: the Noise IK handshake FSM and the anti-replay data plane

A sans-IO model of one WireGuard peer: the Noise IK handshake lifecycle
(handshake initiation → handshake response → transport) and the
data-plane per-message counter with its sliding-window anti-replay
filter. Derived from the WireGuard whitepaper (Donenfeld, "WireGuard:
Next Generation Kernel Network Tunnel"), specifically:

* §5.4 "First Message: Initiator to Responder" and §5.4.3 "Second
  Message: Responder to Initiator" — the two-message Noise IK handshake
  and the four message types (1 initiation, 2 response, 3 cookie,
  4 transport data). Cookie/MAC and load-shedding are out of scope here.
* §5.4.6 "Subsequent Messages: Transport Data Messages" — the 64-bit
  monotone nonce counter carried in each transport message.
* §5.4.7 "Sliding Window" — the anti-replay filter: a counter strictly
  ahead of the window is accepted and slides it forward, a counter too
  far behind is dropped, and a counter inside the window is accepted
  only if it has not already been seen. The concrete algorithm modeled
  is the RFC 6479 "next / bitmap" formulation used by every WireGuard
  implementation (a `next` high-water mark plus a bounded window).

## The machine

    step : Config → St → Input → St × List Output

is total and deterministic. In the *transport FSM*, cryptography is an
uninterpreted total boundary: `Config` carries named function-valued
fields for accepting a handshake message, deriving the session keys, and
AEAD sealing/opening transport data, and every FSM theorem holds uniformly
over every crypto behavior — the theorems are about the state machine, not
the cipher.

The `Noise` section below then *fills in* that boundary with the actual
Noise IKpsk2 key schedule, computed on the verified HACL*/EverCrypt
primitives exposed by `Crypto` (X25519, HKDF-SHA-256, ChaCha20-Poly1305).
`wg_handshake_real` proves the two peers derive one shared chaining key —
and hence identical transport keys — through the real Diffie–Hellman
chain, so the FSM's abstract `deriveKeys` boundary is discharged by real
crypto rather than assumed.

## Theorems

* `wg_no_transport_before_handshake` — no data-plane output
  (`sendTransport` on the wire, `deliver` to the application) is ever
  produced except from an `established` phase, and `established` is
  entered only by a completing handshake transition (a valid response
  accepted by an initiator, or a valid initiation accepted by a
  responder). No transport data before the handshake completes.
* `wg_replay_rejected` — in every reachable state, a transport counter
  already accepted, or one that has fallen below the window, is
  rejected: it produces no `deliver` and does not disturb the window.
  This is the whole point of the anti-replay filter.
* `wg_counter_monotone` — the window high-water mark (`next`, one past
  the highest accepted counter) never decreases across any step; the
  outbound send counter never decreases either.
* `wg_replay_window_correct` — the full anti-replay decision: a counter is
  accepted *iff* it is ahead of the window or fresh inside it (with
  `wg_window_accepts_ahead` / `wg_window_accepts_fresh` the accept side).
* `Noise.wg_handshake_real` — the real Noise IK handshake on verified
  crypto: both peers derive the same chaining key (and transport keys) via
  the X25519 Diffie–Hellman chain (`wg_transport_keys_agree`,
  `wg_static_key_authenticated` for the AEAD-sealed static key).
* `Rekey.wg_rekey_before_reject` — a session crosses the rekey threshold
  before it can ever hit the hard reject threshold (§6.1 timers).
* `Cookie.wg_cookie_mitigates` — under load, an initiation without a valid
  cookie MAC2 is never admitted to the handshake (§5.3 DoS mitigation).
* `Wire.wg_initiation_refines` / `Wire.wg_response_refines` /
  `Wire.wg_wire_handshake_agrees` — the byte-level handshake refinement:
  what an honest peer *emits* (`mkInitiation`/`mkResponse`), the other peer
  *accepts* (`consumeInitiationCore`/`consumeResponseCore`), recovering the
  exact sealed static key, timestamp, chaining key and transcript hash,
  through real X25519 agreement + AEAD roundtrip — over the mandated
  BLAKE2s ratchet and transcript chain.
* `Wire.parse_serialize_initiation` / `Wire.parse_serialize_response` —
  the 148-byte / 92-byte message codecs roundtrip.
* `Wire.wg_transport_wire_roundtrip` / `Wire.wg_transport_nonce_injective`
  — the type-4 transport wire format (counter in the clear, nonce
  `0^4 ‖ LE64(counter)`) opens to what was sealed, and the counter↦nonce
  map is injective (no nonce reuse under the proven counter monotonicity).
* `Wire.wg_timestamp_monotone` / `Wire.wg_initiation_replay_rejected` —
  TAI64N encoding orders by (seconds, nanoseconds); a replayed initiation
  fails the strictly-greater freshness rule.
* `Wire.wg_mac1_exact`, `Wire.wg_alloc_injective`, `Wire.wg_route_*` —
  keyed-BLAKE2s mac1 admission, 32-bit index allocation, session routing.

## Boundary / UNCLOSED

* The BLAKE2s hash, transcript chain, and `mac1`/`HMAC`/`KDF_n` ratchet are
  defined in pure Lean here (RFC 7693), anchored to the RFC test vectors and
  live cross-checks; the AEAD and X25519 primitives stay on the verified
  HACL*/EverCrypt seam. This matches the assurance posture of the `Crypto`
  module (vector-anchored primitives, algebraic laws named as axioms).
* The `Noise` section proves key *agreement* and AEAD roundtrip; it does
  not re-derive X25519 hardness or AEAD IND-CPA — those are the
  discharged-upstream `Crypto.Assumptions` axioms (X25519 agreement, AEAD
  authenticity), the intended trust boundary.
* `mac2` / the cookie reply (message type 3) need XChaCha20-Poly1305, which
  the crypto seam does not yet expose; the admission *logic* is proven
  abstractly (`Cookie`), the XChaCha primitive is the named boundary.
* The transport FSM's `Config` crypto fields remain abstract there (the
  FSM theorems are cipher-independent); the `Noise`/`Wire` sections are what
  realize them on real crypto.
* The window is modeled with a ghost `seen` set of accepted counters
  rather than a fixed-width bitmap; a real implementation stores only
  the last `windowSize` bits. The acceptance decision modeled here is
  exactly the bounded-window decision, so the anti-replay property is
  faithful; bitmap storage is the implementation boundary.
-/

namespace Wireguard

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-! ## Handshake and transport messages (opaque contents) -/

/-- A Noise IK handshake initiation (message type 1). Its encrypted
static key and timestamp live behind the crypto boundary. -/
structure Initiation where
  raw : Bytes
deriving Repr, DecidableEq

/-- A Noise IK handshake response (message type 2). -/
structure Response where
  raw : Bytes
deriving Repr, DecidableEq

/-- A transport data message (message type 4): the 64-bit nonce counter
in the clear and the AEAD-sealed payload. -/
structure TransportMsg where
  counter : Nat
  payload : Bytes
deriving Repr, DecidableEq

/-- Opaque derived session-key material (both directions). -/
structure Keys where
  id : Nat
deriving Repr, DecidableEq

/-- Which end of the handshake this peer played. -/
inductive Role where
  | initiator
  | responder
deriving Repr, DecidableEq

/-! ## The sliding-window anti-replay filter (whitepaper §5.4.7) -/

/-- Window width. WireGuard's stock filter reorders up to a few thousand
packets; the exact width is irrelevant to the anti-replay property so
long as it is positive. Modeled here as one 64-bit word. -/
def windowSize : Nat := 64

/-- The receive-side anti-replay state: `next` is one past the highest
counter accepted so far (the RFC 6479 high-water mark), and `seen` is
the ghost set of every counter accepted. A real implementation keeps
only a `windowSize`-bit bitmap of the counters below `next`. -/
structure Window where
  next : Nat
  seen : List Nat
deriving Repr

/-- A fresh window: nothing received yet. -/
def Window.fresh : Window := { next := 0, seen := [] }

/-- The acceptance decision of §5.4.7, in the RFC 6479 formulation:
* a counter at or beyond `next` is always accepted (the window is
  growing, so no replay is possible);
* a counter more than `windowSize` behind `next` is too old — dropped;
* a counter inside the window is accepted only if it is not already in
  `seen`. -/
def Window.willAccept (w : Window) (c : Nat) : Bool :=
  if c ≥ w.next then true
  else if c + windowSize < w.next then false
  else !(w.seen.contains c)

/-- Record an accepted counter: advance `next` past it if it is the new
high-water mark, and add it to the seen set. Only ever applied to a
counter the filter accepted. -/
def Window.mark (w : Window) (c : Nat) : Window :=
  { next := if c ≥ w.next then c + 1 else w.next,
    seen := c :: w.seen }

/-- The window invariant: every accepted counter is strictly below the
high-water mark. Maintained by construction and needed to prove that a
previously accepted counter is rejected on replay. -/
def Window.Inv (w : Window) : Prop :=
  ∀ c, w.seen.contains c = true → c < w.next

theorem Window.inv_fresh : Window.Inv Window.fresh := by
  intro c h
  simp [Window.fresh] at h

theorem Window.inv_mark (w : Window) (c : Nat) (h : Window.Inv w) :
    Window.Inv (w.mark c) := by
  intro x hx
  simp only [Window.mark, List.contains_cons] at hx
  rcases Bool.or_eq_true _ _ |>.mp hx with he | he
  · have hxc : x = c := eq_of_beq he
    subst hxc
    simp only [Window.mark]
    by_cases hc : x ≥ w.next <;> simp [hc] <;> omega
  · have hxlt : x < w.next := h x he
    simp only [Window.mark]
    by_cases hc : c ≥ w.next <;> simp [hc] <;> omega

/-- `mark` never lowers the high-water mark. -/
theorem Window.mark_next_ge (w : Window) (c : Nat) :
    w.next ≤ (w.mark c).next := by
  simp only [Window.mark]
  by_cases hc : c ≥ w.next <;> simp [hc]
  omega

/-- **Too-old rejection.** A counter more than `windowSize` behind the
high-water mark is rejected outright — no history needed. -/
theorem Window.too_old_rejected (w : Window) (c : Nat)
    (h : c + windowSize < w.next) : w.willAccept c = false := by
  have hge : ¬ (c ≥ w.next) := by omega
  simp [Window.willAccept, hge, h]

/-- **Replay rejection.** Under the invariant, a counter already
accepted is rejected: `willAccept` returns `false`. This is the
anti-replay guarantee at the filter level. -/
theorem Window.replay_rejected (w : Window) (c : Nat)
    (hInv : Window.Inv w) (hc : w.seen.contains c = true) :
    w.willAccept c = false := by
  have hlt : c < w.next := hInv c hc
  have hge : ¬ (c ≥ w.next) := by omega
  simp only [Window.willAccept, hge, if_false]
  by_cases h2 : c + windowSize < w.next
  · simp [h2]
  · rw [if_neg h2, hc]; rfl

/-! ## The peer FSM -/

/-- The per-peer handshake/transport phase. -/
inductive Phase where
  /-- Idle: no handshake in progress. -/
  | start
  /-- Initiator: sent the handshake initiation, awaiting the response.
  No transport data may flow yet. -/
  | initSent (m : Initiation)
  /-- Handshake complete: session keys derived, transport data flows.
  Carries the role, keys, the receive anti-replay window, and the
  outbound send counter. -/
  | established (role : Role) (keys : Keys) (win : Window) (sendCtr : Nat)
  /-- Terminal / torn down. -/
  | dead
deriving Repr

/-- Inputs the environment can deliver. -/
inductive Input where
  /-- Application asks to start a handshake as the initiator. -/
  | initiate
  /-- A handshake initiation arrived (responder path). -/
  | recvInitiation (m : Initiation)
  /-- A handshake response arrived (initiator path). -/
  | recvResponse (m : Response)
  /-- Application asks to send transport plaintext. -/
  | appSend (data : Bytes)
  /-- A transport data message arrived. -/
  | recvTransport (m : TransportMsg)
  /-- Session expiry / rekey trigger. -/
  | expire
deriving Repr

/-- Outputs the machine can emit. -/
inductive Output where
  /-- A handshake initiation to the wire. -/
  | sendInitiation (m : Initiation)
  /-- A handshake response to the wire. -/
  | sendResponse (m : Response)
  /-- A transport data message to the wire (data plane). -/
  | sendTransport (m : TransportMsg)
  /-- Decrypted inbound transport plaintext to the application (data
  plane). -/
  | deliver (data : Bytes)
deriving Repr, DecidableEq

/-- The data-plane outputs: exactly the two that carry transport
payload. The no-transport-before-handshake theorem is about these. -/
def Output.isDataPlane : Output → Bool
  | .sendTransport _ => true
  | .deliver _ => true
  | _ => false

/-- Static configuration and the named crypto-effect vocabulary. Every
function-valued field is an uninterpreted total function: the theorems
about `step` hold for all of them. -/
structure Config where
  /-- The initiation this peer emits when it starts a handshake. -/
  makeInitiation : Initiation
  /-- Responder: does this initiation authenticate (decrypt + MAC + the
  §5.1 timestamp check)? -/
  acceptInitiation : Initiation → Bool
  /-- Initiator: does this response authenticate? -/
  acceptResponse : Response → Bool
  /-- Responder: the response emitted for an accepted initiation. -/
  makeResponse : Initiation → Response
  /-- Initiator: derive session keys from the accepted response. -/
  deriveInitiatorKeys : Response → Keys
  /-- Responder: derive session keys from the accepted initiation. -/
  deriveResponderKeys : Initiation → Keys
  /-- AEAD-seal outbound plaintext at a counter. -/
  sealTransport : Keys → Nat → Bytes → TransportMsg
  /-- AEAD-open an inbound transport message; `none` on auth failure. -/
  openTransport : Keys → TransportMsg → Option Bytes

/-- Machine state is just the phase (all history lives in the window's
ghost `seen` set). -/
structure St where
  phase : Phase
deriving Repr

/-- Initial state: idle. -/
def init : St := { phase := .start }

/-- Handle a transport message in the established phase: consult the
window, and only on acceptance (and successful AEAD-open) advance the
window and deliver plaintext. A rejected or unauthentic message is
dropped with the window untouched. -/
def recvData (cfg : Config) (role : Role) (keys : Keys) (win : Window)
    (sendCtr : Nat) (m : TransportMsg) : Phase × List Output :=
  if win.willAccept m.counter then
    match cfg.openTransport keys m with
    | some pt =>
      (.established role keys (win.mark m.counter) sendCtr, [.deliver pt])
    | none =>
      (.established role keys win sendCtr, [])
  else
    (.established role keys win sendCtr, [])

/-- The phase transition: a total match on phase × input. -/
def stepPhase (cfg : Config) : Phase → Input → Phase × List Output
  -- ── idle ──
  | .start, .initiate =>
    (.initSent cfg.makeInitiation, [.sendInitiation cfg.makeInitiation])
  | .start, .recvInitiation m =>
    if cfg.acceptInitiation m then
      (.established .responder (cfg.deriveResponderKeys m) Window.fresh 0,
       [.sendResponse (cfg.makeResponse m)])
    else
      (.start, [])
  | .start, _ => (.start, [])
  -- ── initiator: awaiting response ──
  | .initSent m, .recvResponse r =>
    if cfg.acceptResponse r then
      (.established .initiator (cfg.deriveInitiatorKeys r) Window.fresh 0, [])
    else
      (.initSent m, [])
  | .initSent m0, .recvInitiation m =>
    -- A crossing initiation: responder role wins, keys re-derived.
    if cfg.acceptInitiation m then
      (.established .responder (cfg.deriveResponderKeys m) Window.fresh 0,
       [.sendResponse (cfg.makeResponse m)])
    else
      (.initSent m0, [])
  | .initSent _, .expire => (.start, [])
  | .initSent m, _ => (.initSent m, [])
  -- ── established: transport data flows ──
  | .established role keys win sendCtr, .appSend data =>
    (.established role keys win (sendCtr + 1),
     [.sendTransport (cfg.sealTransport keys sendCtr data)])
  | .established role keys win sendCtr, .recvTransport m =>
    recvData cfg role keys win sendCtr m
  | .established _ _ _ _, .expire => (.start, [])
  | .established role keys win sendCtr, _ =>
    (.established role keys win sendCtr, [])
  -- ── dead ──
  | .dead, _ => (.dead, [])

/-- The total transition. -/
def step (cfg : Config) (s : St) (i : Input) : St × List Output :=
  ({ phase := (stepPhase cfg s.phase i).1 }, (stepPhase cfg s.phase i).2)

/-- Fold the step over an input trace, collecting every step's output. -/
def run (cfg : Config) (s : St) : List Input → St × List (List Output)
  | [] => (s, [])
  | i :: is =>
    ((run cfg (step cfg s i).1 is).1,
     (step cfg s i).2 :: (run cfg (step cfg s i).1 is).2)

/-- States reachable from the initial state under some input. -/
inductive Reachable (cfg : Config) : St → Prop where
  | init : Reachable cfg init
  | step {s : St} (h : Reachable cfg s) (i : Input) :
      Reachable cfg (step cfg s i).1

/-! ## Totality and determinism -/

/-- The step relation induced by the step function. -/
def Steps (cfg : Config) (s : St) (i : Input) (s' : St)
    (o : List Output) : Prop :=
  step cfg s i = (s', o)

theorem step_total (cfg : Config) (s : St) (i : Input) :
    ∃ s' o, Steps cfg s i s' o :=
  ⟨(step cfg s i).1, (step cfg s i).2, rfl⟩

theorem step_deterministic (cfg : Config) (s : St) (i : Input)
    {s₁ s₂ : St} {o₁ o₂ : List Output}
    (h₁ : Steps cfg s i s₁ o₁) (h₂ : Steps cfg s i s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  have h := h₁.symm.trans h₂
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## No transport before the handshake completes -/

/-- `true` exactly on the established phase. -/
def Phase.isEstablished : Phase → Bool
  | .established _ _ _ _ => true
  | _ => false

/-- `recvData` only ever emits `deliver`, never a wire send, and only
from an established successor. -/
theorem recvData_dataplane (cfg : Config) (role : Role) (keys : Keys)
    (win : Window) (sendCtr : Nat) (m : TransportMsg) :
    ∀ o ∈ (recvData cfg role keys win sendCtr m).2,
      ∃ d, o = .deliver d := by
  intro o ho
  unfold recvData at ho
  split at ho
  · split at ho
    · simp at ho; exact ⟨_, ho⟩
    · simp at ho
  · simp at ho

/-- **No transport before handshake**, step form: any data-plane output
of a step comes from a step whose *starting* phase is already
`established`. Every other phase — idle, initiation-sent, dead — emits
only handshake control messages, never transport data. -/
theorem wg_no_transport_before_handshake (cfg : Config) (s : St)
    (i : Input) (o : Output)
    (ho : o ∈ (step cfg s i).2) (hd : o.isDataPlane = true) :
    s.phase.isEstablished = true := by
  rcases s with ⟨p⟩
  cases p <;> cases i <;>
    simp_all [step, stepPhase, Phase.isEstablished, Output.isDataPlane]
  all_goals (
    first
    | (split at ho <;> simp_all [Output.isDataPlane])
    | (rename_i m;
       rcases recvData_dataplane cfg _ _ _ _ m o ho with ⟨d, rfl⟩;
       simp [Output.isDataPlane]))

/-- **Entering `established` is a handshake completion.** If a step
moves from a non-established phase into `established`, then the input
was a handshake message that the crypto boundary *accepted*: either an
initiator accepting a valid response, or a responder accepting a valid
initiation. There is no other door into the transport phase. -/
theorem wg_established_needs_handshake (cfg : Config) (s : St)
    (i : Input) {role : Role} {keys : Keys} {win : Window} {sc : Nat}
    (hpre : s.phase.isEstablished = false)
    (hpost : (step cfg s i).1.phase = .established role keys win sc) :
    (∃ r, i = .recvResponse r ∧ cfg.acceptResponse r = true) ∨
    (∃ m, i = .recvInitiation m ∧ cfg.acceptInitiation m = true) := by
  rcases s with ⟨p⟩
  cases p with
  | start =>
    cases i with
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · exact Or.inr ⟨m, rfl, by assumption⟩
      · simp at hpost
    | _ => simp only [step, stepPhase] at hpost; simp at hpost
  | initSent m0 =>
    cases i with
    | recvResponse r =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · exact Or.inl ⟨r, rfl, by assumption⟩
      · simp at hpost
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · exact Or.inr ⟨m, rfl, by assumption⟩
      · simp at hpost
    | _ => simp only [step, stepPhase] at hpost; simp at hpost
  | established r0 k0 w0 s0 =>
    simp [Phase.isEstablished] at hpre
  | dead =>
    cases i <;> (simp only [step, stepPhase] at hpost; simp at hpost)

/-! ## The reachable-window invariant -/

/-- Every reachable established state carries a window satisfying the
anti-replay invariant. -/
def WinInv (s : St) : Prop :=
  ∀ role keys win sc, s.phase = .established role keys win sc →
    Window.Inv win

theorem winInv_init : WinInv init := by
  intro role keys win sc h
  simp [init] at h

theorem winInv_step (cfg : Config) (s : St) (i : Input)
    (h : WinInv s) : WinInv (step cfg s i).1 := by
  rcases s with ⟨p⟩
  intro role keys win sc hpost
  cases p with
  | start =>
    cases i with
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · injection hpost with _ _ hw _; subst hw; exact Window.inv_fresh
      · simp at hpost
    | _ => simp only [step, stepPhase] at hpost; simp at hpost
  | initSent m0 =>
    cases i with
    | recvResponse r =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · injection hpost with _ _ hw _; subst hw; exact Window.inv_fresh
      · simp at hpost
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      split at hpost
      · injection hpost with _ _ hw _; subst hw; exact Window.inv_fresh
      · simp at hpost
    | _ => simp only [step, stepPhase] at hpost; simp at hpost
  | established r0 k0 w0 s0 =>
    have hw0 : Window.Inv w0 := h r0 k0 w0 s0 rfl
    cases i with
    | appSend data =>
      simp only [step, stepPhase] at hpost
      injection hpost with _ _ hw _; subst hw; exact hw0
    | recvTransport m =>
      simp only [step, stepPhase, recvData] at hpost
      split at hpost
      · split at hpost
        · injection hpost with _ _ hw _; subst hw
          exact Window.inv_mark _ _ hw0
        · injection hpost with _ _ hw _; subst hw; exact hw0
      · injection hpost with _ _ hw _; subst hw; exact hw0
    | expire => simp only [step, stepPhase] at hpost; simp at hpost
    | initiate =>
      simp only [step, stepPhase] at hpost
      injection hpost with _ _ hw _; subst hw; exact hw0
    | recvInitiation m =>
      simp only [step, stepPhase] at hpost
      injection hpost with _ _ hw _; subst hw; exact hw0
    | recvResponse r =>
      simp only [step, stepPhase] at hpost
      injection hpost with _ _ hw _; subst hw; exact hw0
  | dead =>
    cases i <;> (simp only [step, stepPhase] at hpost; simp at hpost)

theorem winInv_reachable (cfg : Config) {s : St}
    (h : Reachable cfg s) : WinInv s := by
  induction h with
  | init => exact winInv_init
  | step _ i ih => exact winInv_step cfg _ i ih

/-! ## Anti-replay at the FSM level -/

/-- **Replay rejected.** In every reachable state, feeding a transport
message whose counter was already accepted (or has dropped below the
window) delivers nothing and leaves the window unchanged. A replayed
packet has no effect. -/
theorem wg_replay_rejected (cfg : Config) {s : St}
    (hr : Reachable cfg s) {role : Role} {keys : Keys} {win : Window}
    {sc : Nat} (hph : s.phase = .established role keys win sc)
    (m : TransportMsg) (hseen : win.seen.contains m.counter = true) :
    (step cfg s (.recvTransport m)).2 = [] ∧
    (step cfg s (.recvTransport m)).1.phase
      = .established role keys win sc := by
  have hInv : Window.Inv win := winInv_reachable cfg hr role keys win sc hph
  have hrej : win.willAccept m.counter = false :=
    Window.replay_rejected win m.counter hInv hseen
  rcases s with ⟨p⟩
  simp only at hph
  subst hph
  simp only [step, stepPhase, recvData, hrej, if_false]
  exact ⟨rfl, rfl⟩

/-- **Too-old rejected.** Same conclusion for a counter that has fallen
more than a window behind the high-water mark — no history needed. -/
theorem wg_too_old_rejected (cfg : Config) (s : St)
    {role : Role} {keys : Keys} {win : Window} {sc : Nat}
    (hph : s.phase = .established role keys win sc)
    (m : TransportMsg) (hold : m.counter + windowSize < win.next) :
    (step cfg s (.recvTransport m)).2 = [] ∧
    (step cfg s (.recvTransport m)).1.phase
      = .established role keys win sc := by
  have hrej : win.willAccept m.counter = false :=
    Window.too_old_rejected win m.counter hold
  rcases s with ⟨p⟩
  simp only at hph
  subst hph
  simp only [step, stepPhase, recvData, hrej, if_false]
  exact ⟨rfl, rfl⟩

/-! ## Counter monotonicity -/

/-- The window high-water mark of an established phase, or 0 elsewhere.
One past the highest transport counter ever accepted. -/
def Phase.recvHighWater : Phase → Nat
  | .established _ _ win _ => win.next
  | _ => 0

/-- The outbound send counter of an established phase, or 0 elsewhere. -/
def Phase.sendCounter : Phase → Nat
  | .established _ _ _ sc => sc
  | _ => 0

/-- **Receive counter monotone.** While a peer stays established, the
receive high-water mark never decreases: an accepted transport message
only advances it, and every non-transport step leaves it fixed. -/
theorem wg_counter_monotone (cfg : Config) (s : St) (i : Input)
    {role : Role} {keys : Keys} {win : Window} {sc : Nat}
    (hpre : s.phase = .established role keys win sc)
    {role' : Role} {keys' : Keys} {win' : Window} {sc' : Nat}
    (hpost : (step cfg s i).1.phase = .established role' keys' win' sc') :
    win.next ≤ win'.next := by
  rcases s with ⟨p⟩
  simp only at hpre
  subst hpre
  cases i with
  | appSend data =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ hw _; exact Nat.le_of_eq (congrArg Window.next hw)
  | recvTransport m =>
    simp only [step, stepPhase, recvData] at hpost
    split at hpost
    · split at hpost
      · injection hpost with _ _ hw _; subst hw
        exact Window.mark_next_ge win m.counter
      · injection hpost with _ _ hw _
        exact Nat.le_of_eq (congrArg Window.next hw)
    · injection hpost with _ _ hw _
      exact Nat.le_of_eq (congrArg Window.next hw)
  | expire => simp only [step, stepPhase] at hpost; simp at hpost
  | initiate =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ hw _; exact Nat.le_of_eq (congrArg Window.next hw)
  | recvInitiation m =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ hw _; exact Nat.le_of_eq (congrArg Window.next hw)
  | recvResponse r =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ hw _; exact Nat.le_of_eq (congrArg Window.next hw)

/-- **Send counter monotone.** The outbound counter never decreases
while the peer stays established (it advances by one on each send). -/
theorem wg_send_counter_monotone (cfg : Config) (s : St) (i : Input)
    {role : Role} {keys : Keys} {win : Window} {sc : Nat}
    (hpre : s.phase = .established role keys win sc)
    {role' : Role} {keys' : Keys} {win' : Window} {sc' : Nat}
    (hpost : (step cfg s i).1.phase = .established role' keys' win' sc') :
    sc ≤ sc' := by
  rcases s with ⟨p⟩
  simp only at hpre
  subst hpre
  cases i with
  | appSend data =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ _ hs; omega
  | recvTransport m =>
    simp only [step, stepPhase, recvData] at hpost
    split at hpost
    · split at hpost
      · injection hpost with _ _ _ hs; omega
      · injection hpost with _ _ _ hs; omega
    · injection hpost with _ _ _ hs; omega
  | expire => simp only [step, stepPhase] at hpost; simp at hpost
  | initiate =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ _ hs; omega
  | recvInitiation m =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ _ hs; omega
  | recvResponse r =>
    simp only [step, stepPhase] at hpost
    injection hpost with _ _ _ hs; omega

/-! ## The sliding window, fully characterized

`Window.replay_rejected` and `Window.too_old_rejected` give one direction:
a replayed or stale counter is refused. The data-plane guarantee needs the
whole decision, both ways — a counter is accepted *iff* it is either ahead
of the window or fresh inside it. These theorems close that. -/

/-- **Accepts ahead of the window.** A counter at or beyond the high-water
mark is always accepted — the window only ever grew past accepted
counters, so nothing ahead of it can be a replay. -/
theorem wg_window_accepts_ahead (w : Window) (c : Nat) (h : w.next ≤ c) :
    w.willAccept c = true := by
  unfold Window.willAccept
  rw [if_pos h]

/-- **Accepts a fresh in-window counter.** A counter inside the window
(not more than `windowSize` behind the mark) that has not been seen before
is accepted — legitimate reordering is not mistaken for a replay. -/
theorem wg_window_accepts_fresh (w : Window) (c : Nat)
    (h1 : w.next ≤ c + windowSize) (h2 : w.seen.contains c = false) :
    w.willAccept c = true := by
  unfold Window.willAccept
  by_cases hc : c ≥ w.next
  · rw [if_pos hc]
  · rw [if_neg hc, if_neg (by omega : ¬ c + windowSize < w.next), h2]; rfl

/-- **The window decision, exactly.** `willAccept` returns `true` precisely
when the counter is ahead of the window, or is inside the window and has
not been seen. This is the complete acceptance predicate of §5.4.7 — every
other counter (already seen, or fallen off the back of the window) is
rejected. Combined with the invariant, this is the full anti-replay
characterization: accepted ⇔ in-window-and-unseen (or ahead). -/
theorem wg_replay_window_correct (w : Window) (c : Nat) :
    w.willAccept c = true ↔
      (w.next ≤ c) ∨ (w.next ≤ c + windowSize ∧ w.seen.contains c = false) := by
  unfold Window.willAccept
  by_cases h1 : c ≥ w.next
  · rw [if_pos h1]
    constructor
    · intro _; exact Or.inl h1
    · intro _; rfl
  · rw [if_neg h1]
    by_cases h2 : c + windowSize < w.next
    · rw [if_pos h2]
      constructor
      · intro h; simp at h
      · rintro (h | ⟨hle, _⟩)
        · exact absurd h h1
        · exact absurd h2 (Nat.not_lt.mpr hle)
    · rw [if_neg h2]
      constructor
      · intro h
        have hcon : w.seen.contains c = false := by
          cases hh : w.seen.contains c with
          | false => rfl
          | true => rw [hh] at h; simp at h
        exact Or.inr ⟨by omega, hcon⟩
      · rintro (h | ⟨_, hcon⟩)
        · exact absurd h h1
        · rw [hcon]; rfl

/-! ## BLAKE2s (RFC 7693), as a pure Lean definition

WireGuard mandates BLAKE2s for every hash in the protocol: the chaining-key
ratchet (`HMAC`/`KDF_n`), the transcript hash `H`, and the keyed 16-byte
`mac1`/`mac2`. The AEAD and Diffie–Hellman primitives stay on the verified
HACL*/EverCrypt seam (`Crypto`); the hash is defined *here*, in Lean, as the
RFC 7693 algorithm itself — an executable definition the proofs can talk
about directly, with no new `@[extern]` surface. Its byte-exactness against
RFC 7693 is anchored by the published test vectors (and live cross-checks
against independent implementations), the same way the C seam's primitives
are anchored by their RFC vectors. -/

namespace Blake2s

/-- The BLAKE2s IV (the SHA-256 IV, RFC 7693 §2.6). -/
def iv : Array UInt32 :=
  #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

/-- The message-word permutation table, flattened: row `r` (of 10) at
`sigma[16*r + i]` (RFC 7693 §2.7). -/
def sigma : Array Nat :=
  #[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
    14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3,
    11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4,
     7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8,
     9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13,
     2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9,
    12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11,
    13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10,
     6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5,
    10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]

/-- 32-bit right rotation. -/
def rotr (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> UInt32.ofNat n) ||| (x <<< UInt32.ofNat (32 - n))

/-- The G mixing function (RFC 7693 §3.1), on the 16-word work vector. -/
def g (v : Array UInt32) (a b c d : Nat) (x y : UInt32) : Array UInt32 :=
  let va := v[a]! + v[b]! + x
  let vd := rotr (v[d]! ^^^ va) 16
  let vc := v[c]! + vd
  let vb := rotr (v[b]! ^^^ vc) 12
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((v.set! a va).set! b vb).set! c vc).set! d vd

/-- One of the ten rounds: eight G applications on the column/diagonal
schedule, message words permuted by `sigma`. -/
def round (r : Nat) (m : Array UInt32) (v : Array UInt32) : Array UInt32 :=
  let s := fun i => sigma[16 * (r % 10) + i]!
  let v := g v 0 4  8 12 m[s 0]! m[s 1]!
  let v := g v 1 5  9 13 m[s 2]! m[s 3]!
  let v := g v 2 6 10 14 m[s 4]! m[s 5]!
  let v := g v 3 7 11 15 m[s 6]! m[s 7]!
  let v := g v 0 5 10 15 m[s 8]! m[s 9]!
  let v := g v 1 6 11 12 m[s 10]! m[s 11]!
  let v := g v 2 7  8 13 m[s 12]! m[s 13]!
  g v 3 4  9 14 m[s 14]! m[s 15]!

/-- Little-endian 32-bit word at byte offset `i` (reads past the end as 0;
callers always pass a full 64-byte block). -/
def word32 (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 |||
  ((b.get! (i+1)).toUInt32 <<< 8) |||
  ((b.get! (i+2)).toUInt32 <<< 16) |||
  ((b.get! (i+3)).toUInt32 <<< 24)

/-- The compression function F (RFC 7693 §3.2): `h` the 8-word state,
`blk` a full 64-byte block, `t` the byte-offset counter, `last` the
final-block flag. -/
def compress (h : Array UInt32) (blk : ByteArray) (t : UInt64) (last : Bool) :
    Array UInt32 :=
  let m : Array UInt32 := (List.range 16).toArray.map fun i => word32 blk (4*i)
  let v := h ++ iv
  let v := v.set! 12 (v[12]! ^^^ t.toUInt32)
  let v := v.set! 13 (v[13]! ^^^ (t >>> 32).toUInt32)
  let v := if last then v.set! 14 (v[14]! ^^^ 0xFFFFFFFF) else v
  let v := (List.range 10).foldl (fun v r => round r m v) v
  (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i+8]!

/-- Zero-pad a partial block to the 64-byte block size. -/
def padBlock (b : ByteArray) : ByteArray :=
  b ++ ⟨Array.mkArray (64 - b.size) 0⟩

/-- Split into 64-byte blocks; always at least one (possibly empty) block,
and the last block carries the remainder (RFC 7693 §3.3 `dd`). -/
def blocks (b : ByteArray) : List ByteArray :=
  let n := max 1 ((b.size + 63) / 64)
  (List.range n).map fun i => b.extract (64*i) (min (64*(i+1)) b.size)

/-- Fold the compression over the block list: non-final blocks at
`t = bytes so far`, the final block zero-padded with `t = total length`
and the finalization flag set. -/
def foldBlocks : Array UInt32 → List ByteArray → UInt64 → Array UInt32
  | h, [], _ => h
  | h, [b], t => compress h (padBlock b) (t + UInt64.ofNat b.size) true
  | h, b :: rest, t => foldBlocks (compress h b (t + 64) false) rest (t + 64)

/-- Serialize the first `nn` bytes of the state, little-endian. -/
def out (h : Array UInt32) (nn : Nat) : ByteArray :=
  ⟨((List.range nn).map fun j =>
      (h[j/4]! >>> UInt32.ofNat (8 * (j % 4))).toUInt8).toArray⟩

/-- BLAKE2s: digest length `nn` (1–32), optional key (0–32 bytes; a
non-empty key is fed as a padded first block, RFC 7693 §3.3). -/
def blake2s (nn : Nat) (key msg : ByteArray) : ByteArray :=
  let h0 := iv.set! 0
    (iv[0]! ^^^ (0x01010000 : UInt32) ^^^ (UInt32.ofNat key.size <<< 8) ^^^
      UInt32.ofNat nn)
  let data := if key.size = 0 then msg else padBlock key ++ msg
  out (foldBlocks h0 (blocks data) 0) nn

/-- The whitepaper's `HASH(x)`: unkeyed BLAKE2s-256. -/
def hash (m : ByteArray) : ByteArray := blake2s 32 ByteArray.empty m

/-- The whitepaper's `MAC(k, x)`: keyed BLAKE2s with a 16-byte digest
(`mac1`/`mac2`). -/
def mac (key m : ByteArray) : ByteArray := blake2s 16 key m

/-- XOR every byte with a pad constant (HMAC inner/outer pads). -/
def xorPad (b : ByteArray) (x : UInt8) : ByteArray := ⟨b.data.map (· ^^^ x)⟩

/-- The whitepaper's `HMAC(k, x)`: RFC 2104 over BLAKE2s-256
(block size 64). -/
def hmac (key msg : ByteArray) : ByteArray :=
  let k := if key.size > 64 then hash key else key
  let kp := padBlock k
  hash (xorPad kp 0x5c ++ hash (xorPad kp 0x36 ++ msg))

end Blake2s

/-! ## XChaCha20-Poly1305 (the cookie AEAD, whitepaper §5.4.7)

The cookie reply (message type 3) is sealed with XChaCha20-Poly1305: a
24-byte random nonce, too wide for the ChaCha20-Poly1305 AEAD. XChaCha is
the standard extension (draft-irtf-cfrg-xchacha): derive a subkey with
HChaCha20 from the key and the first 16 nonce bytes, then run ordinary
ChaCha20-Poly1305 under that subkey with the 8 remaining nonce bytes
(prefixed by 4 zero bytes). HChaCha20 is a pure keystream-free key
derivation — 20 ChaCha rounds with no feed-forward — defined here in Lean
the same way BLAKE2s is (an executable RFC-exact definition, anchored to
the published test vectors and live cross-checks); the AEAD itself stays on
the verified HACL*/EverCrypt seam, so the XChaCha roundtrip/authenticity
theorems inherit directly from the ChaCha20-Poly1305 assumptions. -/

namespace XChaCha

/-- 32-bit left rotation. -/
def rotl (x : UInt32) (n : Nat) : UInt32 :=
  (x <<< UInt32.ofNat n) ||| (x >>> UInt32.ofNat (32 - n))

/-- The ChaCha quarter round (RFC 8439 §2.1) on the 16-word state. -/
def qr (v : Array UInt32) (a b c d : Nat) : Array UInt32 :=
  let va := v[a]! + v[b]!
  let vd := rotl (v[d]! ^^^ va) 16
  let vc := v[c]! + vd
  let vb := rotl (v[b]! ^^^ vc) 12
  let va := va + vb
  let vd := rotl (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotl (vb ^^^ vc) 7
  (((v.set! a va).set! b vb).set! c vc).set! d vd

/-- One ChaCha double round: four column rounds then four diagonal rounds. -/
def doubleRound (v : Array UInt32) : Array UInt32 :=
  let v := qr v 0 4  8 12
  let v := qr v 1 5  9 13
  let v := qr v 2 6 10 14
  let v := qr v 3 7 11 15
  let v := qr v 0 5 10 15
  let v := qr v 1 6 11 12
  let v := qr v 2 7  8 13
  qr v 3 4  9 14

/-- The ChaCha constants, "expand 32-byte k". -/
def consts : Array UInt32 := #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- HChaCha20 (draft-irtf-cfrg-xchacha §2.2): 20 ChaCha rounds over
`consts ‖ key ‖ nonce₁₆`, output = words 0–3 and 12–15, little-endian —
no feed-forward, which is what makes it a PRF-style subkey derivation
rather than a keystream block. -/
def hchacha20 (key nonce16 : ByteArray) : ByteArray :=
  let st := consts
    ++ ((List.range 8).toArray.map fun i => Blake2s.word32 key (4*i))
    ++ ((List.range 4).toArray.map fun i => Blake2s.word32 nonce16 (4*i))
  let v := (List.range 10).foldl (fun v _ => doubleRound v) st
  Blake2s.out #[v[0]!, v[1]!, v[2]!, v[3]!, v[12]!, v[13]!, v[14]!, v[15]!] 32

/-- XChaCha20-Poly1305 seal: subkey = HChaCha20(key, nonce[0:16]), inner
nonce = 0⁴ ‖ nonce[16:24], then the verified ChaCha20-Poly1305 seam. -/
def xseal (key nonce24 ad pt : ByteArray) : Option ByteArray :=
  Crypto.chachaSeal (hchacha20 key (nonce24.extract 0 16))
    (⟨Array.mkArray 4 0⟩ ++ nonce24.extract 16 24) ad pt

/-- XChaCha20-Poly1305 open — the same derivation, then the verified open. -/
def xopen (key nonce24 ad ct : ByteArray) : Option ByteArray :=
  Crypto.chachaOpen (hchacha20 key (nonce24.extract 0 16))
    (⟨Array.mkArray 4 0⟩ ++ nonce24.extract 16 24) ad ct

/-- **XChaCha roundtrip.** Both sides derive the identical subkey and inner
nonce from the same 24-byte nonce (a deterministic computation), so the
roundtrip is exactly the ChaCha20-Poly1305 roundtrip under that subkey. -/
theorem wg_xchacha_roundtrip (key nonce24 ad pt ct : ByteArray)
    (h : xseal key nonce24 ad pt = some ct) :
    xopen key nonce24 ad ct = some pt :=
  Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _ h

/-- **XChaCha authenticity.** The only ciphertext that opens is the one
sealed for that exact key/nonce/ad — inherited AEAD forgery resistance. -/
theorem wg_xchacha_authentic (key nonce24 ad ct pt : ByteArray)
    (h : xopen key nonce24 ad ct = some pt) :
    xseal key nonce24 ad pt = some ct :=
  Crypto.Assumptions.chacha_open_authentic _ _ _ _ _ h

end XChaCha

/-! ## The real Noise IK handshake (whitepaper §5.4), on verified crypto

Everything above treats the handshake itself as an uninterpreted boundary
(`Config.acceptInitiation`, `deriveInitiatorKeys`, …) so the FSM theorems
hold for every cipher. This section fills that boundary in with the
*actual* Noise IKpsk2 key schedule, computed on the HACL*/EverCrypt
primitives exposed by `Crypto`:

* X25519 (`Crypto.x25519`, `Crypto.x25519Base`) for the Diffie–Hellman
  chain — the four shared secrets `es, ss, ee, se`;
* HMAC-BLAKE2s (`Blake2s.hmac`, the pure Lean RFC 7693 definition above)
  for the chaining-key ratchet — the whitepaper's `HMAC`/`KDF_n`, on the
  mandated hash, byte-for-byte what a wire peer computes;
* ChaCha20-Poly1305 (`Crypto.chachaSeal` / `Crypto.chachaOpen`) for the
  AEAD-sealed static key and timestamp.

The message layout follows §5.4 exactly, under the mandated construction
string `Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s`.

The payoff (`wg_handshake_real`) is that the two peers, computing their
secrets from opposite ends, derive the *same* chaining key and hence the
same transport keys — because at each of the four DH steps the initiator's
`x25519 a (base b)` equals the responder's `x25519 b (base a)`
(`Crypto.Assumptions.x25519_dh_agree`). This is the real crypto agreement,
not an assumed `deriveKeys` function. -/

namespace Noise

/-- A party's keypair: a 32-byte X25519 private scalar and its public
point. `WF` says the public point really is the scalar's base multiple —
the one fact the agreement proof consumes. -/
structure KeyPair where
  priv : ByteArray
  pub  : ByteArray

def KeyPair.WF (kp : KeyPair) : Prop := Crypto.x25519Base kp.priv = some kp.pub

/-- `KDF1` (whitepaper §5.4): `t0 = HMAC(ck, input)`, `t1 = HMAC(t0, 0x1)`.
Total — the ratchet is a pure Lean computation on BLAKE2s. -/
def kdf1 (ck input : ByteArray) : ByteArray :=
  let t0 := Blake2s.hmac ck input
  Blake2s.hmac t0 ⟨#[1]⟩

/-- `KDF2`: `(t1, t2)` with `t2 = HMAC(t0, t1 ‖ 0x2)`. The first component
is the next chaining key; the second is the step's AEAD key `κ`. -/
def kdf2 (ck input : ByteArray) : ByteArray × ByteArray :=
  let t0 := Blake2s.hmac ck input
  let t1 := Blake2s.hmac t0 ⟨#[1]⟩
  (t1, Blake2s.hmac t0 (t1.push 2))

/-- `KDF3`: `(t1, t2, t3)` — the preshared-key step of IKpsk2 (`ck`, the
hash input `τ`, and the AEAD key `κ`). -/
def kdf3 (ck input : ByteArray) : ByteArray × ByteArray × ByteArray :=
  let t0 := Blake2s.hmac ck input
  let t1 := Blake2s.hmac t0 ⟨#[1]⟩
  let t2 := Blake2s.hmac t0 (t1.push 2)
  (t1, t2, Blake2s.hmac t0 (t2.push 3))

/-- Mix a public value (an unencrypted ephemeral, or the preshared key)
into the chaining key: `ck ← KDF1(ck, m)`. -/
def mixKey (ck : Option ByteArray) (m : ByteArray) : Option ByteArray :=
  ck.map fun c => kdf1 c m

/-- Mix a Diffie–Hellman shared secret into the chaining key. The secret
is an `Option` (X25519 rejects low-order points, RFC 7748 §6.1), so a
failure at any DH step collapses the chain to `none`. -/
def mixDH (ck secret : Option ByteArray) : Option ByteArray :=
  match ck, secret with
  | some c, some s => some (kdf1 c s)
  | _, _ => none

/-- The construction identifier (§5.4.1) — WireGuard's, verbatim. -/
def construction : ByteArray :=
  "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s".toUTF8

/-- The initial chaining key `Ci = Hash(CONSTRUCTION)` (§5.4.1). A fixed
constant, identical on both peers. -/
def ckInit : ByteArray := Blake2s.hash construction

/-- The chaining-key ratchet through a full IK handshake, as a function of
the two *public* ephemerals, the preshared key, and the four
Diffie–Hellman shared secrets in whitepaper order: `es`, `ss` (initiation)
then `ee`, `se` (response), with the preshared key mixed last (the `psk2`
of IKpsk2). This is exactly the sequence of `KDF1` applications producing
the final chaining key; the transport keys derive from its output. Written
once and applied by both peers — they differ only in *how* they compute
the four secrets. -/
def chainingKey (epubI epubR psk : ByteArray)
    (es ss ee se : Option ByteArray) : Option ByteArray :=
  let ck := some ckInit
  let ck := mixKey ck epubI      -- unencrypted initiator ephemeral (§5.4.2)
  let ck := mixDH  ck es         -- es = DH(ei, sr)
  let ck := mixDH  ck ss         -- ss = DH(si, sr)
  let ck := mixKey ck epubR      -- unencrypted responder ephemeral (§5.4.3)
  let ck := mixDH  ck ee         -- ee = DH(ei, er)
  let ck := mixDH  ck se         -- se = DH(si, er)
  let ck := mixKey ck psk        -- preshared key
  ck

/-- The transport-key material, `KDF2(ck, ε)` (§5.4.5): 64 bytes carrying
`(T_send_i, T_recv_i)`. The responder derives the same 64 bytes and uses
them with the two directions swapped, so agreement on `ck` is agreement on
both directions' keys. -/
def transportKeys (ck : Option ByteArray) : Option ByteArray :=
  ck.map fun c => let (t1, t2) := kdf2 c ByteArray.empty; t1 ++ t2

/-- The initiator's chaining key. It holds `si, ei`, was told the
responder's static public `spubR`, learns the responder's ephemeral public
`epubR` from the response, and computes its four secrets from its own
private scalars. `epubI` is its own ephemeral public (also on the wire). -/
def initiatorChainingKey (si ei epubI spubR epubR psk : ByteArray) :
    Option ByteArray :=
  chainingKey epubI epubR psk
    (Crypto.x25519 ei spubR)   -- es = DH(ei, sr)
    (Crypto.x25519 si spubR)   -- ss = DH(si, sr)
    (Crypto.x25519 ei epubR)   -- ee = DH(ei, er)
    (Crypto.x25519 si epubR)   -- se = DH(si, er)

/-- The responder's chaining key. It holds `sr, er`, learns the
initiator's static public `spubI` (by decrypting the initiation) and
ephemeral public `epubI` (in the clear), and computes the *same* four
secrets from the opposite end. -/
def responderChainingKey (sr er spubI epubI epubR psk : ByteArray) :
    Option ByteArray :=
  chainingKey epubI epubR psk
    (Crypto.x25519 sr epubI)   -- es = DH(sr, ei)
    (Crypto.x25519 sr spubI)   -- ss = DH(sr, si)
    (Crypto.x25519 er epubI)   -- ee = DH(er, ei)
    (Crypto.x25519 er spubI)   -- se = DH(er, si)

/-- **The handshake derives one shared chaining key via the real DH
chain.** Given well-formed keypairs (each public point is its scalar's
base multiple), the initiator and responder — computing their four
Diffie–Hellman secrets from opposite ends — arrive at the *same* chaining
key. Each equality `x25519 a (base b) = x25519 b (base a)` is discharged
by the X25519 agreement axiom; the ratchet is otherwise a deterministic
fold of identical public inputs, so the results coincide. This is the
Noise IK guarantee on verified crypto, replacing the FSM's abstract
`deriveInitiatorKeys` / `deriveResponderKeys` boundary. -/
theorem wg_handshake_real
    (si ei sr er spubI epubI spubR epubR psk : ByteArray)
    (hSI : Crypto.x25519Base si = some spubI)
    (hEI : Crypto.x25519Base ei = some epubI)
    (hSR : Crypto.x25519Base sr = some spubR)
    (hER : Crypto.x25519Base er = some epubR) :
    initiatorChainingKey si ei epubI spubR epubR psk
      = responderChainingKey sr er spubI epubI epubR psk := by
  unfold initiatorChainingKey responderChainingKey
  rw [Crypto.Assumptions.x25519_dh_agree ei sr epubI spubR hEI hSR,
      Crypto.Assumptions.x25519_dh_agree si sr spubI spubR hSI hSR,
      Crypto.Assumptions.x25519_dh_agree ei er epubI epubR hEI hER,
      Crypto.Assumptions.x25519_dh_agree si er spubI epubR hSI hER]

/-- **Both peers derive identical transport keys.** An immediate corollary:
the 64-byte `KDF2(ck, ε)` transport material is the same on both ends, so
the initiator's send key is the responder's receive key and vice versa. -/
theorem wg_transport_keys_agree
    (si ei sr er spubI epubI spubR epubR psk : ByteArray)
    (hSI : Crypto.x25519Base si = some spubI)
    (hEI : Crypto.x25519Base ei = some epubI)
    (hSR : Crypto.x25519Base sr = some spubR)
    (hER : Crypto.x25519Base er = some epubR) :
    transportKeys (initiatorChainingKey si ei epubI spubR epubR psk)
      = transportKeys (responderChainingKey sr er spubI epubI epubR psk) :=
  congrArg transportKeys
    (wg_handshake_real si ei sr er spubI epubI spubR epubR psk hSI hEI hSR hER)

/-! ### The AEAD-sealed static key and timestamp, on real ChaCha20-Poly1305

The initiation (§5.4.2) carries the initiator's static public key and a
TAI64N timestamp, each AEAD-sealed under a key derived from the chaining
key at that step, with the running transcript hash as associated data. The
responder, having derived the *same* key (from the proven-equal chaining
key) and the same transcript, recovers them. These are the real AEAD
roundtrip and forgery-resistance, not a boolean `acceptInitiation`. -/

/-- The all-zero 96-bit AEAD nonce the Noise counter starts at (`0` for the
first message under each key). -/
def nonce0 : ByteArray := ⟨Array.mkArray 12 (0 : UInt8)⟩

/-- Seal the initiator's static public key (§5.4.2, `encrypted_static`):
`AEAD(k, 0, spubI, hash)`. -/
def sealStatic (k hash spubI : ByteArray) : Option ByteArray :=
  Crypto.chachaSeal k nonce0 hash spubI

/-- **The responder recovers the initiator's static key.** With the same
derived key and transcript hash, opening `encrypted_static` yields exactly
the initiator's static public key — the real AEAD roundtrip. -/
theorem wg_static_key_authenticated (k hash spubI ct : ByteArray)
    (hseal : sealStatic k hash spubI = some ct) :
    Crypto.chachaOpen k nonce0 hash ct = some spubI :=
  Crypto.Assumptions.chacha_open_seal_roundtrip k nonce0 hash spubI ct hseal

/-- **No forged static key is ever accepted.** The only ciphertext that
opens to a given static key under this key/hash is the one the genuine
initiator sealed — AEAD forgery-resistance. A responder that admits an
initiation only on `chachaOpen … = some spubI` therefore only ever admits
a peer that actually holds the shared key material. -/
theorem wg_static_key_unforgeable (k hash spubI ct : ByteArray)
    (hopen : Crypto.chachaOpen k nonce0 hash ct = some spubI) :
    Crypto.chachaSeal k nonce0 hash spubI = some ct :=
  Crypto.Assumptions.chacha_open_authentic k nonce0 hash ct spubI hopen

end Noise

/-! ## The wire format (whitepaper §5.4.2, §5.4.3, §5.4.6)

The byte-exact message layer: the 148-byte handshake initiation (type 1),
the 92-byte handshake response (type 2), and the variable-length transport
data message (type 4), together with the transcript-hash chain `H` the AEAD
fields are bound to, the keyed-BLAKE2s `mac1`, the TAI64N timestamp, and
the 32-bit session indices.

Every serializer is paired with a parser and a proved roundtrip; the
handshake construction (`mkInitiation`/`mkResponse`) is paired with the
consumption the *other* peer runs (`consumeInitiationCore`/
`consumeResponseCore`) and a proved refinement: what one honest peer emits,
the other accepts, recovering exactly the sealed values and arriving at the
same chaining key and transcript hash — through the real X25519 agreement
and AEAD roundtrip assumptions, not an abstract accept function.

`mac2` and the cookie reply (message type 3) remain the named boundary: they
need XChaCha20-Poly1305, which the crypto seam does not yet expose; the
admission *logic* is proven abstractly in the `Cookie` section below. -/

namespace Wire

/-- The `List UInt8` view of a `ByteArray` (via its backing array, so the
roundtrip with `List.toArray` is definitional). -/
def bytesOf (b : ByteArray) : Bytes := b.data.toList

@[simp] theorem bytesOf_length (b : ByteArray) :
    (bytesOf b).length = b.size := Array.length_toList

@[simp] theorem bytesOf_mk_toArray (l : Bytes) : bytesOf ⟨l.toArray⟩ = l :=
  Array.toList_toArray l

@[simp] theorem mk_toArray_bytesOf (b : ByteArray) :
    (⟨(bytesOf b).toArray⟩ : ByteArray) = b := by
  show ByteArray.mk b.data.toList.toArray = b
  rw [Array.toArray_toList]

/-! ### Little/big-endian integers, with decode lemmas -/

/-- `len` bytes, little-endian, value `n` (mod `256^len`). -/
def leList : Nat → Nat → Bytes
  | _, 0 => []
  | n, len+1 => UInt8.ofNat (n % 256) :: leList (n / 256) len

/-- The numeric value of a little-endian byte string. -/
def leVal : Bytes → Nat
  | [] => 0
  | x :: r => x.toNat + 256 * leVal r

@[simp] theorem leList_length (n len : Nat) : (leList n len).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ k ih => simp [leList, ih]

theorem leVal_leList (n len : Nat) (h : n < 256 ^ len) :
    leVal (leList n len) = n := by
  induction len generalizing n with
  | zero => simp only [leList, leVal]; simp at h; omega
  | succ k ih =>
    have hlt : n / 256 < 256 ^ k := by
      rw [Nat.pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    simp only [leList, leVal, ih _ hlt, UInt8.toNat_ofNat]
    omega

theorem leVal_append (a b : Bytes) :
    leVal (a ++ b) = leVal a + 256 ^ a.length * leVal b := by
  induction a with
  | nil => simp [leVal]
  | cons x xs ih =>
    show x.toNat + 256 * leVal (xs ++ b) = _
    rw [ih]
    simp only [leVal, List.length_cons, Nat.pow_succ]
    have hassoc : 256 ^ xs.length * 256 * leVal b
        = 256 * (256 ^ xs.length * leVal b) := by
      rw [Nat.mul_comm (256 ^ xs.length) 256, Nat.mul_assoc]
    rw [Nat.mul_add, hassoc]
    omega

/-- Big-endian (network order): the reversed little-endian bytes. -/
def beList (n len : Nat) : Bytes := (leList n len).reverse

/-- The numeric value of a big-endian byte string (byte-lexicographic
order on equal lengths coincides with numeric order). -/
def beVal (l : Bytes) : Nat := leVal l.reverse

@[simp] theorem beList_length (n len : Nat) : (beList n len).length = len := by
  simp [beList]

theorem beVal_beList (n len : Nat) (h : n < 256 ^ len) :
    beVal (beList n len) = n := by
  simp [beVal, beList, leVal_leList n len h]

/-! ### TAI64N timestamps (whitepaper §5.4.2)

12 bytes: the 8-byte big-endian label `2^62 + seconds`, then the 4-byte
big-endian nanosecond count. The responder keeps the greatest value seen
per peer and requires each initiation's timestamp to exceed it — this is
what makes a *replayed* initiation (a valid, honestly-MAC'd message 1
captured off the wire) inert. -/

/-- Encode a TAI64N timestamp. -/
def tai64n (secs : UInt64) (nanos : UInt32) : Bytes :=
  beList (2 ^ 62 + secs.toNat) 8 ++ beList nanos.toNat 4

/-- The numeric value of a 12-byte timestamp (BE, so lexicographic =
numeric). -/
def tsVal (t : Bytes) : Nat := beVal t

@[simp] theorem tai64n_length (secs : UInt64) (nanos : UInt32) :
    (tai64n secs nanos).length = 12 := by
  simp [tai64n]

theorem tsVal_tai64n (secs : UInt64) (nanos : UInt32)
    (h : secs.toNat < 2 ^ 62) :
    tsVal (tai64n secs nanos) = (2 ^ 62 + secs.toNat) * 2 ^ 32 + nanos.toNat := by
  have hn : nanos.toNat < 256 ^ 4 := nanos.toBitVec.isLt
  have hs : 2 ^ 62 + secs.toNat < 256 ^ 8 := by
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega
  unfold tsVal tai64n beVal beList
  rw [List.reverse_append, List.reverse_reverse, List.reverse_reverse,
      leVal_append, leList_length,
      leVal_leList _ 4 hn, leVal_leList _ 8 hs]
  have h4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rw [h4]
  omega

/-- **Timestamp monotonicity.** A later (seconds, nanoseconds) reading
encodes to a strictly greater timestamp value, so the responder's
greater-than-last check orders honestly-generated initiations correctly.
(`secs < 2^62` holds for every physical clock until the year ~1.4·10^11.) -/
theorem wg_timestamp_monotone (s₁ s₂ : UInt64) (n₁ n₂ : UInt32)
    (hb₁ : s₁.toNat < 2 ^ 62) (hb₂ : s₂.toNat < 2 ^ 62)
    (h : s₁.toNat < s₂.toNat ∨ (s₁.toNat = s₂.toNat ∧ n₁.toNat < n₂.toNat)) :
    tsVal (tai64n s₁ n₁) < tsVal (tai64n s₂ n₂) := by
  rw [tsVal_tai64n s₁ n₁ hb₁, tsVal_tai64n s₂ n₂ hb₂]
  have hn₁ : n₁.toNat < 2 ^ 32 := n₁.toBitVec.isLt
  have hn₂ : n₂.toNat < 2 ^ 32 := n₂.toBitVec.isLt
  rcases h with h | ⟨he, hn⟩ <;> omega

/-- The responder's freshness rule (§5.1): accept only a timestamp
strictly greater than the last accepted one. -/
def tsFresh (last : Nat) (t : Bytes) : Bool := decide (last < tsVal t)

/-- **Initiation replay is inert.** Replaying the exact bytes of an
already-accepted initiation fails the freshness rule — its timestamp is
not greater than itself. -/
theorem wg_initiation_replay_rejected (t : Bytes) :
    tsFresh (tsVal t) t = false := by
  simp [tsFresh]

/-! ### Chunked reading, for the parsers -/

/-- Read exactly `n` bytes; `none` if the input is shorter. -/
def readN (n : Nat) (l : Bytes) : Option (Bytes × Bytes) :=
  if n ≤ l.length then some (l.take n, l.drop n) else none

theorem readN_exact {n : Nat} (a b : Bytes) (h : a.length = n) :
    readN n (a ++ b) = some (a, b) := by
  subst h
  simp [readN, List.take_left, List.drop_left]

/-- Stepping form: read `a` off the front of `a ++ b` and continue. -/
theorem readN_bind {β : Type} (n : Nat) (a b : Bytes) (h : a.length = n)
    (f : Bytes × Bytes → Option β) :
    (readN n (a ++ b)) >>= f = f (a, b) := by
  rw [readN_exact a b h]; rfl

/-! ### The transcript-hash chain (whitepaper §5.4.1) -/

/-- `IDENTIFIER`, mixed into the initial transcript hash. -/
def identifier : ByteArray := "WireGuard v1 zx2c4 Jason@zx2c4.com".toUTF8

/-- `Hi := HASH(Ci ‖ IDENTIFIER)` — the transcript hash before either
peer's static key is mixed in. A fixed constant. -/
def hInit : ByteArray := Blake2s.hash (Noise.ckInit ++ identifier)

/-- `H := HASH(H ‖ m)` — bind a wire value into the transcript. Every
AEAD in the handshake authenticates the transcript so far via this
chain (it is the associated data of each seal). -/
def mixHash (h m : ByteArray) : ByteArray := Blake2s.hash (h ++ m)

/-! ### mac1 (whitepaper §5.4.4) -/

def labelMac1 : ByteArray := "mac1----".toUTF8
def labelCookie : ByteArray := "cookie--".toUTF8

/-- The mac1 key: `HASH(LABEL-MAC1 ‖ S_pub)` of the *receiver's* static
public key. -/
def mac1Key (spub : ByteArray) : ByteArray := Blake2s.hash (labelMac1 ++ spub)

/-- `mac1 := MAC(HASH(LABEL-MAC1 ‖ S_pub), msgα)` — keyed BLAKE2s-128 over
the message bytes up to (excluding) the mac1 field. -/
def mac1Of (spub : ByteArray) (msgAlpha : Bytes) : ByteArray :=
  Blake2s.mac (mac1Key spub) ⟨msgAlpha.toArray⟩

/-- All-zero bytes (the mac2 field when no cookie is in force). -/
def zeros (n : Nat) : ByteArray := ⟨Array.mkArray n 0⟩

/-! ### The two handshake messages -/

/-- Handshake initiation (message type 1; 148 bytes on the wire). -/
structure InitiationMsg where
  sender    : UInt32
  ephemeral : ByteArray  -- 32: the initiator's unencrypted ephemeral
  encStatic : ByteArray  -- 48: AEAD(κ, 0, S_i.pub, H)
  encTs     : ByteArray  -- 28: AEAD(κ, 0, TAI64N, H)
  mac1      : ByteArray  -- 16
  mac2      : ByteArray  -- 16

/-- Handshake response (message type 2; 92 bytes on the wire). -/
structure ResponseMsg where
  sender    : UInt32
  receiver  : UInt32
  ephemeral : ByteArray  -- 32
  encEmpty  : ByteArray  -- 16: AEAD(κ, 0, ε, H)
  mac1      : ByteArray  -- 16
  mac2      : ByteArray  -- 16

/-- The initiation bytes covered by mac1 (type ‖ reserved ‖ sender ‖
ephemeral ‖ encrypted_static ‖ encrypted_timestamp). -/
def initAlphaOf (sender : UInt32) (eph encS encT : ByteArray) : Bytes :=
  [1, 0, 0, 0] ++ leList sender.toNat 4 ++ bytesOf eph ++ bytesOf encS ++
    bytesOf encT

def InitiationMsg.alpha (m : InitiationMsg) : Bytes :=
  initAlphaOf m.sender m.ephemeral m.encStatic m.encTs

/-- Serialize message 1: `α ‖ mac1 ‖ mac2` (148 bytes). -/
def serializeInitiation (m : InitiationMsg) : Bytes :=
  m.alpha ++ bytesOf m.mac1 ++ bytesOf m.mac2

def respAlphaOf (sender receiver : UInt32) (eph encE : ByteArray) : Bytes :=
  [2, 0, 0, 0] ++ leList sender.toNat 4 ++ leList receiver.toNat 4 ++
    bytesOf eph ++ bytesOf encE

def ResponseMsg.alpha (m : ResponseMsg) : Bytes :=
  respAlphaOf m.sender m.receiver m.ephemeral m.encEmpty

/-- Serialize message 2: `α ‖ mac1 ‖ mac2` (92 bytes). -/
def serializeResponse (m : ResponseMsg) : Bytes :=
  m.alpha ++ bytesOf m.mac1 ++ bytesOf m.mac2

def parseInitiation (l : Bytes) : Option InitiationMsg := do
  let (ty, l) ← readN 4 l
  let (snd, l) ← readN 4 l
  let (eph, l) ← readN 32 l
  let (est, l) ← readN 48 l
  let (ets, l) ← readN 28 l
  let (m1, l) ← readN 16 l
  let (m2, l) ← readN 16 l
  if ty = [1, 0, 0, 0] ∧ l = [] then
    some { sender := UInt32.ofNat (leVal snd), ephemeral := ⟨eph.toArray⟩,
           encStatic := ⟨est.toArray⟩, encTs := ⟨ets.toArray⟩,
           mac1 := ⟨m1.toArray⟩, mac2 := ⟨m2.toArray⟩ }
  else none

def parseResponse (l : Bytes) : Option ResponseMsg := do
  let (ty, l) ← readN 4 l
  let (snd, l) ← readN 4 l
  let (rcv, l) ← readN 4 l
  let (eph, l) ← readN 32 l
  let (ee, l) ← readN 16 l
  let (m1, l) ← readN 16 l
  let (m2, l) ← readN 16 l
  if ty = [2, 0, 0, 0] ∧ l = [] then
    some { sender := UInt32.ofNat (leVal snd),
           receiver := UInt32.ofNat (leVal rcv), ephemeral := ⟨eph.toArray⟩,
           encEmpty := ⟨ee.toArray⟩, mac1 := ⟨m1.toArray⟩,
           mac2 := ⟨m2.toArray⟩ }
  else none

@[simp] theorem serializeInitiation_length (m : InitiationMsg)
    (he : m.ephemeral.size = 32) (hs : m.encStatic.size = 48)
    (ht : m.encTs.size = 28) (h1 : m.mac1.size = 16) (h2 : m.mac2.size = 16) :
    (serializeInitiation m).length = 148 := by
  simp [serializeInitiation, InitiationMsg.alpha, initAlphaOf,
        he, hs, ht, h1, h2]

@[simp] theorem serializeResponse_length (m : ResponseMsg)
    (he : m.ephemeral.size = 32) (hee : m.encEmpty.size = 16)
    (h1 : m.mac1.size = 16) (h2 : m.mac2.size = 16) :
    (serializeResponse m).length = 92 := by
  simp [serializeResponse, ResponseMsg.alpha, respAlphaOf, he, hee, h1, h2]

/-- Roundtrip: parsing a serialized initiation recovers it exactly (the
field-size hypotheses are the wire widths; the constructors below emit
them by construction). -/
theorem parse_serialize_initiation (m : InitiationMsg)
    (he : m.ephemeral.size = 32) (hs : m.encStatic.size = 48)
    (ht : m.encTs.size = 28) (h1 : m.mac1.size = 16) (h2 : m.mac2.size = 16) :
    parseInitiation (serializeInitiation m) = some m := by
  obtain ⟨snd, eph, est, ets, m1, m2⟩ := m
  simp only at he hs ht h1 h2
  have hsnd : UInt32.ofNat (leVal (leList snd.toNat 4)) = snd := by
    rw [leVal_leList snd.toNat 4
      (by have : snd.toNat < 2 ^ 32 := snd.toBitVec.isLt
          have h4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
          omega)]
    exact UInt32.ofNat_toNat
  simp only [serializeInitiation, InitiationMsg.alpha, initAlphaOf,
    List.append_assoc, parseInitiation]
  rw [readN_bind 4 [1,0,0,0] _ (by rfl)]; dsimp only
  rw [readN_bind 4 (leList snd.toNat 4) _ (by simp)]; dsimp only
  rw [readN_bind 32 (bytesOf eph) _ (by simp [he])]; dsimp only
  rw [readN_bind 48 (bytesOf est) _ (by simp [hs])]; dsimp only
  rw [readN_bind 28 (bytesOf ets) _ (by simp [ht])]; dsimp only
  rw [readN_bind 16 (bytesOf m1) _ (by simp [h1])]; dsimp only
  rw [show (bytesOf m2 : Bytes) = bytesOf m2 ++ [] by simp,
      readN_bind 16 (bytesOf m2) _ (by simp [h2])]; dsimp only
  simp [hsnd]

/-- Roundtrip for the response message. -/
theorem parse_serialize_response (m : ResponseMsg)
    (he : m.ephemeral.size = 32) (hee : m.encEmpty.size = 16)
    (h1 : m.mac1.size = 16) (h2 : m.mac2.size = 16) :
    parseResponse (serializeResponse m) = some m := by
  obtain ⟨snd, rcv, eph, ee, m1, m2⟩ := m
  simp only at he hee h1 h2
  have hv : ∀ x : UInt32, UInt32.ofNat (leVal (leList x.toNat 4)) = x := by
    intro x
    rw [leVal_leList x.toNat 4
      (by have : x.toNat < 2 ^ 32 := x.toBitVec.isLt
          have h4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
          omega)]
    exact UInt32.ofNat_toNat
  simp only [serializeResponse, ResponseMsg.alpha, respAlphaOf,
    List.append_assoc, parseResponse]
  rw [readN_bind 4 [2,0,0,0] _ (by rfl)]; dsimp only
  rw [readN_bind 4 (leList snd.toNat 4) _ (by simp)]; dsimp only
  rw [readN_bind 4 (leList rcv.toNat 4) _ (by simp)]; dsimp only
  rw [readN_bind 32 (bytesOf eph) _ (by simp [he])]; dsimp only
  rw [readN_bind 16 (bytesOf ee) _ (by simp [hee])]; dsimp only
  rw [readN_bind 16 (bytesOf m1) _ (by simp [h1])]; dsimp only
  rw [show (bytesOf m2 : Bytes) = bytesOf m2 ++ [] by simp,
      readN_bind 16 (bytesOf m2) _ (by simp [h2])]; dsimp only
  simp [hv]

/-- mac1 verification: recompute the keyed MAC over `α` and compare. -/
def checkMac1Init (spubR : ByteArray) (m : InitiationMsg) : Bool :=
  bytesOf m.mac1 == bytesOf (mac1Of spubR m.alpha)

def checkMac1Resp (spubI : ByteArray) (m : ResponseMsg) : Bool :=
  bytesOf m.mac1 == bytesOf (mac1Of spubI m.alpha)

/-- **mac1 is required, exactly.** The check passes iff the message's mac1
field equals the keyed BLAKE2s of its own α bytes under the receiver's
static-key-derived MAC key — the §5.4.4 admission condition. -/
theorem wg_mac1_exact (spubR : ByteArray) (m : InitiationMsg) :
    checkMac1Init spubR m = true ↔
      bytesOf m.mac1 = bytesOf (mac1Of spubR m.alpha) := by
  simp [checkMac1Init]

/-! ### Building and consuming the handshake messages

The construction each peer runs, per §5.4.2/§5.4.3, on the real
primitives: `Blake2s` for the ratchet and transcript, `Crypto.x25519`
for the DH chain, `Crypto.chachaSeal/Open` for the sealed fields. -/

/-- Post-message-1 handshake state: the chaining key and transcript hash. -/
structure HsState where
  ck : ByteArray
  h  : ByteArray

/-- Initiator builds message 1 (§5.4.2). `none` only if a DH is degenerate
(low-order point) or the AEAD seam rejects a size. -/
def mkInitiation (si spubI ei epubI spubR ts : ByteArray) (sender : UInt32) :
    Option (InitiationMsg × HsState) :=
  let ck1 := Noise.kdf1 Noise.ckInit epubI
  let h1 := mixHash (mixHash hInit spubR) epubI
  match Crypto.x25519 ei spubR, Crypto.x25519 si spubR with
  | some es, some ss =>
    let p2 := Noise.kdf2 ck1 es
    match Crypto.chachaSeal p2.2 Noise.nonce0 h1 spubI with
    | some encS =>
      let h2 := mixHash h1 encS
      let p3 := Noise.kdf2 p2.1 ss
      match Crypto.chachaSeal p3.2 Noise.nonce0 h2 ts with
      | some encT =>
        some ({ sender, ephemeral := epubI, encStatic := encS, encTs := encT,
                mac1 := mac1Of spubR (initAlphaOf sender epubI encS encT),
                mac2 := zeros 16 },
              ⟨p3.1, mixHash h2 encT⟩)
      | none => none
    | none => none
  | _, _ => none

/-- Responder consumes message 1 (§5.4.2, §5.4.4): verifies mac1, runs the
same ratchet from its own end, opens the sealed static key and timestamp.
Returns `(S_i.pub, timestamp, state)`. -/
def consumeInitiationCore (sr spubR : ByteArray) (m : InitiationMsg) :
    Option (ByteArray × ByteArray × HsState) :=
  if checkMac1Init spubR m then
    let ck1 := Noise.kdf1 Noise.ckInit m.ephemeral
    let h1 := mixHash (mixHash hInit spubR) m.ephemeral
    match Crypto.x25519 sr m.ephemeral with
    | some es =>
      let p2 := Noise.kdf2 ck1 es
      match Crypto.chachaOpen p2.2 Noise.nonce0 h1 m.encStatic with
      | some spubI =>
        let h2 := mixHash h1 m.encStatic
        match Crypto.x25519 sr spubI with
        | some ss =>
          let p3 := Noise.kdf2 p2.1 ss
          match Crypto.chachaOpen p3.2 Noise.nonce0 h2 m.encTs with
          | some ts => some (spubI, ts, ⟨p3.1, mixHash h2 m.encTs⟩)
          | none => none
        | none => none
      | none => none
    | none => none
  else none

/-- Wire-level consumption: parse, then consume. -/
def consumeInitiation (sr spubR : ByteArray) (l : Bytes) :
    Option (InitiationMsg × ByteArray × ByteArray × HsState) :=
  (parseInitiation l).bind fun m =>
    (consumeInitiationCore sr spubR m).map fun r => (m, r)

/-- Responder builds message 2 (§5.4.3), from the post-initiation state:
mixes its ephemeral, `ee`, `se`, then the preshared key (KDF3), and seals
the empty buffer bound to the final transcript. `receiver` must be the
initiation's sender index. -/
def mkResponse (er epubR epubI spubI psk : ByteArray)
    (sender receiver : UInt32) (st : HsState) :
    Option (ResponseMsg × HsState) :=
  let ck4 := Noise.kdf1 st.ck epubR
  let h4 := mixHash st.h epubR
  match Crypto.x25519 er epubI, Crypto.x25519 er spubI with
  | some ee, some se =>
    let ck6 := Noise.kdf1 (Noise.kdf1 ck4 ee) se
    let p := Noise.kdf3 ck6 psk
    let h5 := mixHash h4 p.2.1
    match Crypto.chachaSeal p.2.2 Noise.nonce0 h5 ByteArray.empty with
    | some encE =>
      some ({ sender, receiver, ephemeral := epubR, encEmpty := encE,
              mac1 := mac1Of spubI (respAlphaOf sender receiver epubR encE),
              mac2 := zeros 16 },
            ⟨p.1, mixHash h5 encE⟩)
    | none => none
  | _, _ => none

/-- Initiator consumes message 2 (§5.4.3): verifies mac1, mirrors the
ratchet with its own scalars, and requires the sealed-empty AEAD to open —
that is what authenticates the responder. -/
def consumeResponseCore (si ei spubI psk : ByteArray) (m : ResponseMsg)
    (st : HsState) : Option HsState :=
  if checkMac1Resp spubI m then
    let ck4 := Noise.kdf1 st.ck m.ephemeral
    let h4 := mixHash st.h m.ephemeral
    match Crypto.x25519 ei m.ephemeral, Crypto.x25519 si m.ephemeral with
    | some ee, some se =>
      let ck6 := Noise.kdf1 (Noise.kdf1 ck4 ee) se
      let p := Noise.kdf3 ck6 psk
      let h5 := mixHash h4 p.2.1
      match Crypto.chachaOpen p.2.2 Noise.nonce0 h5 m.encEmpty with
      | some _ => some ⟨p.1, mixHash h5 m.encEmpty⟩
      | none => none
    | _, _ => none
  else none

/-- Wire-level consumption: parse, then consume. -/
def consumeResponse (si ei spubI psk : ByteArray) (l : Bytes)
    (st : HsState) : Option (ResponseMsg × HsState) :=
  (parseResponse l).bind fun m =>
    (consumeResponseCore si ei spubI psk m st).map fun st' => (m, st')

/-- The transport-key pair `KDF2(ck, ε)` (§5.4.5): the initiator uses it
as `(T_send, T_recv)`, the responder swapped. -/
def sessionKeys (st : HsState) : ByteArray × ByteArray :=
  Noise.kdf2 st.ck ByteArray.empty

/-! ### The handshake refinement theorems -/

/-- **What an honest initiator emits, the responder accepts — and recovers
exactly the sealed values.** If `mkInitiation` produced message `m` (so the
DH chain was non-degenerate and both seals succeeded), then the responder's
`consumeInitiationCore` on `m` succeeds and returns precisely the
initiator's static public key, the sealed timestamp, and the *same*
chaining key and transcript hash. The two peers compute their DH secrets
from opposite ends (`x25519_dh_agree`), and each sealed field opens by AEAD
correctness (`chacha_open_seal_roundtrip`). -/
theorem wg_initiation_refines
    {si ei sr spubI epubI spubR ts : ByteArray} {sender : UInt32}
    (hSI : Crypto.x25519Base si = some spubI)
    (hEI : Crypto.x25519Base ei = some epubI)
    (hSR : Crypto.x25519Base sr = some spubR)
    {m : InitiationMsg} {st : HsState}
    (h : mkInitiation si spubI ei epubI spubR ts sender = some (m, st)) :
    consumeInitiationCore sr spubR m = some (spubI, ts, st) := by
  unfold mkInitiation at h
  cases hes : Crypto.x25519 ei spubR with
  | none => rw [hes] at h; cases hss : Crypto.x25519 si spubR <;>
      rw [hss] at h <;> exact absurd h (by simp)
  | some es =>
  cases hss : Crypto.x25519 si spubR with
  | none => rw [hes, hss] at h; exact absurd h (by simp)
  | some ss =>
  rw [hes, hss] at h
  simp only at h
  cases hseal1 : Crypto.chachaSeal
      (Noise.kdf2 (Noise.kdf1 Noise.ckInit epubI) es).2 Noise.nonce0
      (mixHash (mixHash hInit spubR) epubI) spubI with
  | none => rw [hseal1] at h; exact absurd h (by simp)
  | some encS =>
  rw [hseal1] at h
  simp only at h
  cases hseal2 : Crypto.chachaSeal
      (Noise.kdf2 (Noise.kdf2 (Noise.kdf1 Noise.ckInit epubI) es).1 ss).2
      Noise.nonce0 (mixHash (mixHash (mixHash hInit spubR) epubI) encS) ts with
  | none => rw [hseal2] at h; exact absurd h (by simp)
  | some encT =>
  rw [hseal2] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hm, hst⟩ := h
  subst hm hst
  have hd1 : Crypto.x25519 sr epubI = some es := by
    rw [← Crypto.Assumptions.x25519_dh_agree ei sr epubI spubR hEI hSR]
    exact hes
  have hd2 : Crypto.x25519 sr spubI = some ss := by
    rw [← Crypto.Assumptions.x25519_dh_agree si sr spubI spubR hSI hSR]
    exact hss
  have hopen1 := Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _ hseal1
  have hopen2 := Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _ hseal2
  unfold consumeInitiationCore
  rw [if_pos (by simp [checkMac1Init, InitiationMsg.alpha])]
  simp only
  rw [hd1]
  simp only
  rw [hopen1]
  simp only
  rw [hd2]
  simp only
  rw [hopen2]

/-- **What an honest responder emits, the initiator accepts.** Same shape
for message 2: given the responder's `mkResponse` from state `st`, the
initiator's `consumeResponseCore` on the same state succeeds and arrives at
the same final chaining key and transcript hash — hence (`sessionKeys`)
identical transport keys, used in opposite directions. -/
theorem wg_response_refines
    {si ei er spubI epubI epubR psk : ByteArray} {sender receiver : UInt32}
    (hSI : Crypto.x25519Base si = some spubI)
    (hEI : Crypto.x25519Base ei = some epubI)
    (hER : Crypto.x25519Base er = some epubR)
    {st : HsState} {m : ResponseMsg} {st' : HsState}
    (h : mkResponse er epubR epubI spubI psk sender receiver st
          = some (m, st')) :
    consumeResponseCore si ei spubI psk m st = some st' := by
  unfold mkResponse at h
  cases hee : Crypto.x25519 er epubI with
  | none => rw [hee] at h; cases hse : Crypto.x25519 er spubI <;>
      rw [hse] at h <;> exact absurd h (by simp)
  | some ee =>
  cases hse : Crypto.x25519 er spubI with
  | none => rw [hee, hse] at h; exact absurd h (by simp)
  | some se =>
  rw [hee, hse] at h
  simp only at h
  cases hseal : Crypto.chachaSeal
      (Noise.kdf3 (Noise.kdf1 (Noise.kdf1 (Noise.kdf1 st.ck epubR) ee) se)
        psk).2.2 Noise.nonce0
      (mixHash (mixHash st.h epubR)
        (Noise.kdf3 (Noise.kdf1 (Noise.kdf1 (Noise.kdf1 st.ck epubR) ee) se)
          psk).2.1) ByteArray.empty with
  | none => rw [hseal] at h; exact absurd h (by simp)
  | some encE =>
  rw [hseal] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hm, hst⟩ := h
  subst hm hst
  have hd1 : Crypto.x25519 ei epubR = some ee := by
    rw [← Crypto.Assumptions.x25519_dh_agree er ei epubR epubI hER hEI]
    exact hee
  have hd2 : Crypto.x25519 si epubR = some se := by
    rw [← Crypto.Assumptions.x25519_dh_agree er si epubR spubI hER hSI]
    exact hse
  have hopen := Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _ hseal
  unfold consumeResponseCore
  rw [if_pos (by simp [checkMac1Resp, ResponseMsg.alpha])]
  simp only
  rw [hd1, hd2]
  simp only
  rw [hopen]

/-- **The full byte-level handshake converges.** Composing the two
refinements: an honest initiation is accepted by the responder with the
initiator's exact static key, timestamp, and state; the responder's
response from that state is accepted by the initiator with the responder's
exact final state. Both ends hold the same `HsState`, so `sessionKeys`
yields the same 64 bytes of transport-key material on both sides (used in
opposite directions, §5.4.5). -/
theorem wg_wire_handshake_agrees
    {si ei sr er spubI epubI spubR epubR ts psk : ByteArray}
    {sender receiver : UInt32}
    (hSI : Crypto.x25519Base si = some spubI)
    (hEI : Crypto.x25519Base ei = some epubI)
    (hSR : Crypto.x25519Base sr = some spubR)
    (hER : Crypto.x25519Base er = some epubR)
    {m₁ : InitiationMsg} {stI : HsState}
    (h₁ : mkInitiation si spubI ei epubI spubR ts sender = some (m₁, stI))
    {m₂ : ResponseMsg} {stF : HsState}
    (h₂ : mkResponse er epubR epubI spubI psk receiver sender stI
           = some (m₂, stF)) :
    consumeInitiationCore sr spubR m₁ = some (spubI, ts, stI) ∧
    consumeResponseCore si ei spubI psk m₂ stI = some stF :=
  ⟨wg_initiation_refines hSI hEI hSR h₁,
   wg_response_refines hSI hEI hER h₂⟩

/-! ### Transport data messages (whitepaper §5.4.6) -/

/-- The AEAD nonce of a transport message: 4 zero bytes then the 64-bit
little-endian send counter. -/
def nonceOf (ctr : UInt64) : ByteArray :=
  ⟨(leList 0 4 ++ leList ctr.toNat 8).toArray⟩

/-- Nonce decode: the counter is recoverable, so distinct counters give
distinct nonces. -/
theorem nonceOf_val (ctr : UInt64) :
    leVal (bytesOf (nonceOf ctr)) = 2 ^ 32 * ctr.toNat := by
  have hc : ctr.toNat < 256 ^ 8 := by
    have : ctr.toNat < 2 ^ 64 := ctr.toBitVec.isLt
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega
  simp only [nonceOf, bytesOf_mk_toArray]
  rw [leVal_append, leVal_leList _ 8 hc, leList_length]
  have : leVal (leList 0 4) = 0 := leVal_leList 0 4 (by decide)
  rw [this]
  have h4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  omega

/-- **Nonce uniqueness.** The counter↦nonce map is injective: the proven
counter monotonicity/anti-replay of the FSM window therefore guarantees no
AEAD nonce ever repeats under a transport key — the §5.4.6 requirement. -/
theorem wg_transport_nonce_injective (c₁ c₂ : UInt64)
    (h : nonceOf c₁ = nonceOf c₂) : c₁ = c₂ := by
  have hv := congrArg (fun b => leVal (bytesOf b)) h
  simp only [nonceOf_val] at hv
  have : c₁.toNat = c₂.toNat := by omega
  exact UInt64.toNat.inj this

/-- Seal a transport data message (type 4): header ‖ AEAD(T, ctr, P, ε).
The associated data is empty; the transcript binding lives in the key. -/
def sealPacket (key : ByteArray) (receiver : UInt32) (ctr : UInt64)
    (payload : ByteArray) : Option Bytes :=
  (Crypto.chachaSeal key (nonceOf ctr) ByteArray.empty payload).map fun ct =>
    [4, 0, 0, 0] ++ leList receiver.toNat 4 ++ leList ctr.toNat 8 ++
      bytesOf ct

/-- Parse + AEAD-open a transport data message. Returns
`(receiver index, counter, plaintext)`. -/
def openPacket (key : ByteArray) (l : Bytes) :
    Option (UInt32 × UInt64 × ByteArray) :=
  match readN 4 l with
  | some (ty, l) =>
    if ty = [4, 0, 0, 0] then
      match readN 4 l with
      | some (rcv, l) =>
        match readN 8 l with
        | some (ctr, ct) =>
          let ctrN := UInt64.ofNat (leVal ctr)
          (Crypto.chachaOpen key (nonceOf ctrN) ByteArray.empty
            ⟨ct.toArray⟩).map fun pt =>
              (UInt32.ofNat (leVal rcv), ctrN, pt)
        | none => none
      | none => none
    else none
  | none => none

/-- **Transport wire roundtrip.** A sealed packet opens under the same key
to exactly the receiver index, counter, and plaintext that were sealed —
the counter travels in the clear and reconstructs the same nonce, and the
AEAD opens by correctness. -/
theorem wg_transport_wire_roundtrip
    (key payload : ByteArray) (receiver : UInt32) (ctr : UInt64)
    {l : Bytes} (h : sealPacket key receiver ctr payload = some l) :
    openPacket key l = some (receiver, ctr, payload) := by
  unfold sealPacket at h
  cases hseal : Crypto.chachaSeal key (nonceOf ctr) ByteArray.empty payload with
  | none => rw [hseal] at h; exact absurd h (by simp)
  | some ct =>
  rw [hseal] at h
  simp only [Option.map, Option.some.injEq] at h
  subst h
  have hctr : ctr.toNat < 256 ^ 8 := by
    have : ctr.toNat < 2 ^ 64 := ctr.toBitVec.isLt
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega
  have hrcv : receiver.toNat < 256 ^ 4 := by
    have : receiver.toNat < 2 ^ 32 := receiver.toBitVec.isLt
    have h4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
    omega
  unfold openPacket
  rw [show ([4, 0, 0, 0] ++ leList receiver.toNat 4 ++ leList ctr.toNat 8 ++
        bytesOf ct : Bytes)
      = [4, 0, 0, 0] ++ (leList receiver.toNat 4 ++ (leList ctr.toNat 8 ++
        bytesOf ct)) by simp [List.append_assoc]]
  rw [readN_exact [4,0,0,0] _ (by rfl)]
  simp only [if_pos rfl]
  rw [readN_exact (leList receiver.toNat 4) _ (by simp)]
  dsimp only
  rw [readN_exact (leList ctr.toNat 8) _ (by simp)]
  dsimp only
  rw [leVal_leList _ 8 hctr, UInt64.ofNat_toNat]
  rw [Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _
        (by rw [mk_toArray_bytesOf]; exact hseal)]
  rw [leVal_leList _ 4 hrcv, UInt32.ofNat_toNat]
  rfl

/-! ### Session indices (whitepaper §5.4.2/§5.4.3: sender/receiver) -/

/-- Allocate the next 32-bit session index from a running counter. -/
def alloc (ctr : Nat) : UInt32 × Nat := (UInt32.ofNat ctr, ctr + 1)

/-- **Index freshness.** Distinct allocations below the 2^32 horizon yield
distinct indices, so a peer never routes two live sessions through one
receiver index. -/
theorem wg_alloc_injective {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : (alloc a).1 = (alloc b).1) : a = b := by
  have := congrArg UInt32.toNat h
  simp only [alloc, UInt32.toNat_ofNat] at this
  omega

/-- Route an inbound message by its receiver index: the first session
whose local index matches. -/
def route {α : Type} (tbl : List (UInt32 × α)) (i : UInt32) : Option α :=
  (tbl.find? fun e => e.1 == i).map (·.2)

@[simp] theorem route_nil {α : Type} (i : UInt32) :
    route ([] : List (UInt32 × α)) i = none := rfl

/-- A registered session is found under its index. -/
theorem wg_route_hit {α : Type} (i : UInt32) (s : α)
    (tbl : List (UInt32 × α)) : route ((i, s) :: tbl) i = some s := by
  simp [route, List.find?]

/-- A foreign index falls through to the rest of the table. -/
theorem wg_route_skip {α : Type} {i j : UInt32} (s : α)
    (tbl : List (UInt32 × α)) (h : j ≠ i) :
    route ((j, s) :: tbl) i = route tbl i := by
  simp [route, List.find?_cons_of_neg, h]

/-- An unknown index routes nowhere: the message is dropped, matching the
whitepaper's silent-drop rule for unroutable transport messages. -/
theorem wg_route_unknown {α : Type} (tbl : List (UInt32 × α)) (i : UInt32)
    (h : ∀ e ∈ tbl, e.1 ≠ i) : route tbl i = none := by
  induction tbl with
  | nil => rfl
  | cons e rest ih =>
    rw [show e = (e.1, e.2) from rfl, wg_route_skip _ _ (h e (by simp))]
    exact ih fun x hx => h x (by simp [hx])

/-! ### mac2 and the cookie reply (message type 3, whitepaper §5.4.7)

Under load a responder answers an initiation lacking a valid `mac2` with a
cookie reply: 64 bytes — `type ‖ receiver ‖ nonce₂₄ ‖ XAEAD(HASH(LABEL-COOKIE
‖ S_pub), nonce, cookie, msg.mac1)`. The initiator opens it (bound to the
`mac1` of the message it sent), keeps the cookie, and stamps its retry's
`mac2 = MAC(cookie, msgβ)` where `msgβ` is the whole message up to (and
excluding) the mac2 field. The cookie value itself is `MAC(R, addr)` under
the responder's rotating secret — proving the sender owns its source
address. XChaCha20-Poly1305 is realized above (`XChaCha`), so this closes
the previously-named cookie/mac2 wire boundary. -/

/-- `msgβ` of an initiation: everything mac2 covers — `α ‖ mac1`. -/
def InitiationMsg.beta (m : InitiationMsg) : Bytes := m.alpha ++ bytesOf m.mac1

/-- `msgβ` of a response. -/
def ResponseMsg.beta (m : ResponseMsg) : Bytes := m.alpha ++ bytesOf m.mac1

/-- `mac2 := MAC(cookie, msgβ)` — keyed BLAKE2s-128 under the cookie. -/
def mac2Of (cookie : ByteArray) (beta : Bytes) : ByteArray :=
  Blake2s.mac cookie ⟨beta.toArray⟩

/-- mac2 verification for an initiation. -/
def checkMac2Init (cookie : ByteArray) (m : InitiationMsg) : Bool :=
  bytesOf m.mac2 == bytesOf (mac2Of cookie m.beta)

/-- Stamp a cookie into an initiation's mac2 (the §5.4.4 retry). Only the
mac2 field changes; `α` and mac1 are untouched. -/
def withMac2 (m : InitiationMsg) (cookie : ByteArray) : InitiationMsg :=
  { m with mac2 := mac2Of cookie m.beta }

/-- **mac2 is required, exactly**: the check passes iff the field equals the
keyed BLAKE2s of the message's own β bytes under the cookie. -/
theorem wg_mac2_exact (cookie : ByteArray) (m : InitiationMsg) :
    checkMac2Init cookie m = true ↔
      bytesOf m.mac2 = bytesOf (mac2Of cookie m.beta) := by
  simp [checkMac2Init]

/-- Stamping mac2 leaves `α` (and hence mac1 coverage) untouched — a
cookie-stamped retry still authenticates under mac1. -/
theorem wg_withMac2_alpha (m : InitiationMsg) (c : ByteArray) :
    (withMac2 m c).alpha = m.alpha ∧ (withMac2 m c).mac1 = m.mac1 :=
  ⟨rfl, rfl⟩

/-- A message stamped with the right cookie passes the mac2 check. -/
theorem wg_withMac2_valid (cookie : ByteArray) (m : InitiationMsg) :
    checkMac2Init cookie (withMac2 m cookie) = true := by
  simp [checkMac2Init, withMac2, InitiationMsg.beta, InitiationMsg.alpha]

/-- The cookie-encryption key: `HASH(LABEL-COOKIE ‖ S_pub)` of the
*replier's* static public key (which the initiator already holds). -/
def cookieKey (spub : ByteArray) : ByteArray := Blake2s.hash (labelCookie ++ spub)

/-- The cookie value `τ = MAC(R, addr)`: keyed BLAKE2s of the sender's
source address under the responder's rotating secret (§5.4.7). -/
def cookieOf (secret addr : ByteArray) : ByteArray := Blake2s.mac secret addr

/-- The cookie reply (message type 3; 64 bytes on the wire). -/
structure CookieMsg where
  receiver  : UInt32
  nonce     : ByteArray  -- 24
  encCookie : ByteArray  -- 32: XAEAD(cookieKey, nonce, cookie, mac1)

/-- Serialize message 3 (64 bytes). -/
def serializeCookie (m : CookieMsg) : Bytes :=
  [3, 0, 0, 0] ++ leList m.receiver.toNat 4 ++ bytesOf m.nonce ++
    bytesOf m.encCookie

def parseCookie (l : Bytes) : Option CookieMsg := do
  let (ty, l) ← readN 4 l
  let (rcv, l) ← readN 4 l
  let (nn, l) ← readN 24 l
  let (ec, l) ← readN 32 l
  if ty = [3, 0, 0, 0] ∧ l = [] then
    some { receiver := UInt32.ofNat (leVal rcv), nonce := ⟨nn.toArray⟩,
           encCookie := ⟨ec.toArray⟩ }
  else none

@[simp] theorem serializeCookie_length (m : CookieMsg)
    (hn : m.nonce.size = 24) (he : m.encCookie.size = 32) :
    (serializeCookie m).length = 64 := by
  simp [serializeCookie, hn, he]

/-- Roundtrip for the cookie reply. -/
theorem parse_serialize_cookie (m : CookieMsg)
    (hn : m.nonce.size = 24) (he : m.encCookie.size = 32) :
    parseCookie (serializeCookie m) = some m := by
  obtain ⟨rcv, nn, ec⟩ := m
  simp only at hn he
  have hv : UInt32.ofNat (leVal (leList rcv.toNat 4)) = rcv := by
    rw [leVal_leList rcv.toNat 4
      (by have : rcv.toNat < 2 ^ 32 := rcv.toBitVec.isLt
          have h4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
          omega)]
    exact UInt32.ofNat_toNat
  simp only [serializeCookie, List.append_assoc, parseCookie]
  rw [readN_bind 4 [3,0,0,0] _ (by rfl)]; dsimp only
  rw [readN_bind 4 (leList rcv.toNat 4) _ (by simp)]; dsimp only
  rw [readN_bind 24 (bytesOf nn) _ (by simp [hn])]; dsimp only
  rw [show (bytesOf ec : Bytes) = bytesOf ec ++ [] by simp,
      readN_bind 32 (bytesOf ec) _ (by simp [he])]; dsimp only
  simp [hv]

/-- Responder builds the cookie reply: seal the cookie under the
XChaCha key derived from our own public key, bound (as associated data) to
the mac1 of the initiation being refused. -/
def mkCookieReply (spub mac1 cookie nonce : ByteArray) (receiver : UInt32) :
    Option CookieMsg :=
  (XChaCha.xseal (cookieKey spub) nonce mac1 cookie).map fun ct =>
    { receiver, nonce, encCookie := ct }

/-- Initiator consumes the cookie reply: open under the key derived from
the *responder's* public key, bound to the mac1 of the initiation *we*
sent. Yields the cookie for the mac2 of the retry. -/
def consumeCookieReply (spub lastMac1 : ByteArray) (m : CookieMsg) :
    Option ByteArray :=
  XChaCha.xopen (cookieKey spub) m.nonce lastMac1 m.encCookie

/-- **The cookie reply round-trips.** What an honest responder seals for a
given mac1, the initiator holding that mac1 opens — recovering exactly the
cookie. Both derive the same XChaCha subkey from the responder's public
key, so this is the XChaCha (hence ChaCha20-Poly1305 seam) roundtrip. -/
theorem wg_cookie_reply_refines (spub mac1 cookie nonce : ByteArray)
    (receiver : UInt32) {m : CookieMsg}
    (h : mkCookieReply spub mac1 cookie nonce receiver = some m) :
    consumeCookieReply spub mac1 m = some cookie := by
  unfold mkCookieReply at h
  cases hseal : XChaCha.xseal (cookieKey spub) nonce mac1 cookie with
  | none => rw [hseal] at h; exact absurd h (by simp)
  | some ct =>
    rw [hseal] at h
    simp only [Option.map, Option.some.injEq] at h
    subst h
    exact XChaCha.wg_xchacha_roundtrip _ _ _ _ _ hseal

end Wire

/-! ## Rekey timers (whitepaper §6.1)

A session is bounded in both messages and time. WireGuard rekeys — starts
a fresh handshake — well before it is ever forced to drop the session, so
a live tunnel never stalls. These are the stock constants and the ordering
guarantee between the soft (rekey) and hard (reject) thresholds. -/

namespace Rekey

/-- Send-count rekey trigger: `2^60` messages. -/
def REKEY_AFTER_MESSAGES : Nat := 2 ^ 60
/-- Send-count hard limit: `2^64 − 2^13 − 1` messages (nonce exhaustion). -/
def REJECT_AFTER_MESSAGES : Nat := 2 ^ 64 - 2 ^ 13 - 1
/-- Time rekey trigger: 120 seconds. -/
def REKEY_AFTER_TIME : Nat := 120
/-- Time hard limit: 180 seconds. -/
def REJECT_AFTER_TIME : Nat := 180
/-- Handshake retransmit interval: 5 seconds. -/
def REKEY_TIMEOUT : Nat := 5

/-- A live session's usage: transport messages sent under the current keys,
and seconds since the handshake that established them. -/
structure Session where
  msgs : Nat
  age  : Nat
deriving Repr

/-- A new handshake should be started: either enough messages have been
sent or enough time has passed. -/
def needsRekey (s : Session) : Bool :=
  decide (REKEY_AFTER_MESSAGES ≤ s.msgs) || decide (REKEY_AFTER_TIME ≤ s.age)

/-- The session must be torn down (no more transport data): a hard limit
was hit. -/
def mustReject (s : Session) : Bool :=
  decide (REJECT_AFTER_MESSAGES ≤ s.msgs) || decide (REJECT_AFTER_TIME ≤ s.age)

/-- Sending a transport message advances the counter. -/
def onSend (s : Session) : Session := { s with msgs := s.msgs + 1 }
/-- Time passes. -/
def onTick (s : Session) (dt : Nat) : Session := { s with age := s.age + dt }

/-- The soft thresholds sit strictly below the hard ones. -/
theorem rekey_thresholds_ordered :
    REKEY_AFTER_MESSAGES ≤ REJECT_AFTER_MESSAGES ∧
    REKEY_AFTER_TIME ≤ REJECT_AFTER_TIME := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Rekey precedes reject.** Any session that has reached a hard reject
threshold has already crossed the rekey threshold — a correct peer always
initiates a new handshake before it is ever forced to drop the session, so
a live tunnel never dies mid-flight for lack of a fresh key. -/
theorem wg_rekey_before_reject (s : Session) (h : mustReject s = true) :
    needsRekey s = true := by
  obtain ⟨hm, ht⟩ := rekey_thresholds_ordered
  simp only [needsRekey, mustReject, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with hh | hh
  · exact Or.inl (Nat.le_trans hm hh)
  · exact Or.inr (Nat.le_trans ht hh)

/-- The send counter never decreases across a send. -/
theorem onSend_msgs_ge (s : Session) : s.msgs ≤ (onSend s).msgs := by
  simp [onSend]

end Rekey

/-! ## Cookie-reply DoS mitigation (whitepaper §5.3 / §5.4.7)

Under CPU load the responder must not spend an X25519/AEAD handshake on an
unverified sender. Each initiation carries MAC1 (proves the sender knows
the responder's public key) and, when demanded, MAC2 (proves the sender
recently received a cookie tied to its source address). Under load a valid
MAC2 is required; without it the responder answers with a cheap cookie
reply and does *no* handshake work. The cookie's own authenticity (a keyed
MAC over the source address under a rotating secret) is the crypto
boundary; the admission logic below is what mitigates the flood. -/

namespace Cookie

/-- The responder's response to an inbound initiation under the §5.3
admission rule. -/
inductive Reply where
  /-- MAC1 invalid: not even addressed to this responder; dropped in silence. -/
  | drop
  /-- Under load without a valid cookie MAC2: a cheap cookie reply, and no
  handshake computation. -/
  | cookieReply
  /-- Admitted: run the (expensive) Noise handshake response. -/
  | handshake
deriving Repr, DecidableEq

/-- The admission decision. MAC1 is always required. Under load, a valid
MAC2 is additionally required; without it the only response is a cookie
reply — crucially, no Diffie–Hellman or AEAD work is performed. Off load,
MAC1 alone admits the handshake. -/
def admit (mac1Valid mac2Valid underLoad : Bool) : Reply :=
  if mac1Valid = false then .drop
  else if underLoad = true ∧ mac2Valid = false then .cookieReply
  else .handshake

/-- **Cookie mitigation.** Under load, an initiation without a valid cookie
MAC2 is never admitted to the handshake — the responder spends only a
cheap cookie reply (or a drop), never an X25519/AEAD handshake. This is the
DoS guarantee: an off-path flood cannot force handshake work. -/
theorem wg_cookie_mitigates (mac1Valid : Bool) :
    admit mac1Valid false true ≠ Reply.handshake := by
  cases mac1Valid <;> decide

/-- Under load, an invalid cookie yields exactly a cookie reply (given a
valid MAC1). -/
theorem wg_cookie_reply_under_load :
    admit true false true = Reply.cookieReply := by decide

/-- A valid MAC1+MAC2 is admitted, load or not. -/
theorem wg_cookie_admits_valid (underLoad : Bool) :
    admit true true underLoad = Reply.handshake := by
  cases underLoad <;> decide

/-- A bad MAC1 is always dropped — before any cookie or handshake work. -/
theorem wg_cookie_bad_mac1_dropped (mac2 underLoad : Bool) :
    admit false mac2 underLoad = Reply.drop := rfl

/-! ### The admission rule on the real keyed MACs

`admit` above is the abstract §5.3 decision; with mac1, mac2, the cookie
value and the cookie reply all realized on the wire (`Wire`, `XChaCha`),
the admission can now be stated on actual message bytes. -/

/-- Wire-level admission: mac1 always required; under load, mac2 under the
`MAC(R, addr)` cookie of the sender's source address. -/
def admitWire (spubR secret addr : ByteArray) (underLoad : Bool)
    (m : Wire.InitiationMsg) : Reply :=
  admit (Wire.checkMac1Init spubR m)
    (Wire.checkMac2Init (Wire.cookieOf secret addr) m) underLoad

/-- **The cookie flow admits.** An initiator whose (mac1-valid) initiation
was refused under load, and who stamps the consumed cookie into its retry's
mac2, is admitted to the handshake — completing the §5.3 loop: refuse,
cookie-reply, retry-with-mac2, admit. -/
theorem wg_cookie_flow_admits (spubR secret addr : ByteArray)
    (m : Wire.InitiationMsg) (h1 : Wire.checkMac1Init spubR m = true) :
    admitWire spubR secret addr true
      (Wire.withMac2 m (Wire.cookieOf secret addr)) = Reply.handshake := by
  have h1' : Wire.checkMac1Init spubR
      (Wire.withMac2 m (Wire.cookieOf secret addr)) = true := h1
  have h2 := Wire.wg_withMac2_valid (Wire.cookieOf secret addr) m
  simp [admitWire, admit, h1', h2]

/-- Under load, a mac2-less (or wrong-cookie) initiation gets exactly the
cheap cookie reply, never the handshake — on the real MACs. -/
theorem wg_admit_wire_refuses (spubR secret addr : ByteArray)
    (m : Wire.InitiationMsg) (h1 : Wire.checkMac1Init spubR m = true)
    (h2 : Wire.checkMac2Init (Wire.cookieOf secret addr) m = false) :
    admitWire spubR secret addr true m = Reply.cookieReply := by
  simp [admitWire, admit, h1, h2]

end Cookie

/-! ## The composed peer engine (multi-peer, byte level)

Everything above is per-message: codecs, the handshake construction, the
window filter, the FSM. This section composes them into one executable
engine holding the *cross-packet* state of a WireGuard interface — the
session-index table, each session's anti-replay window and send counter,
the per-peer greatest-timestamp ratchet, the roaming endpoint, in-flight
initiations with their retransmission clocks — over multiple configured
peers, in both roles, consuming and producing raw wire bytes:

* **cryptokey routing** (whitepaper §2): a configured peer is a static key
  plus a set of allowed IPs; outbound packets route to the peer with the
  longest matching allowed-IPs prefix of the inner destination, inbound
  decrypted packets are dropped unless their inner source is inside the
  bound peer's allowed IPs;
* **roaming** (§2.1): the peer's wire endpoint is updated on every
  authenticated inbound packet;
* **sessions**: each completed handshake installs a fresh session keyed by
  the local index; new sessions are preferred for sending while old ones
  keep receiving until they expire (`REJECT_AFTER_TIME`) — the §6.1
  new-replaces-old grace;
* **timers** (§6.1/§6.5): `expire` tears down hard-expired sessions,
  `retransmits` lists initiations past `REKEY_TIMEOUT`, `rekeyDue` the
  sessions past the soft thresholds.

The theorems tie the per-message proofs to the composed engine: replay and
too-old rejection at the byte level across packets, allowed-IPs enforcement
on every delivery, the roaming update, the initiation-replay ratchet, the
longest-prefix property of the routing lookup, and the timer laws. -/

namespace Peer

/-! ### Allowed IPs (cryptokey routing) -/

/-- An allowed-IPs entry: an address (4 bytes for IPv4, 16 for IPv6) and a
prefix length in bits. -/
structure Cidr where
  addr : Bytes
  plen : Nat
deriving Repr, DecidableEq

/-- Bit `i` of an address, MSB-first (bit 0 = top bit of byte 0). -/
def bitAt (a : Bytes) (i : Nat) : Bool :=
  match a[i / 8]? with
  | some b => decide ((b.toNat >>> (7 - i % 8)) % 2 = 1)
  | none => false

/-- Prefix match: same address family (length) and the first `plen` bits
agree. -/
def Cidr.matches (c : Cidr) (ip : Bytes) : Bool :=
  ip.length == c.addr.length &&
    (List.range c.plen).all fun i => bitAt ip i == bitAt c.addr i

/-- The longest matching prefix length among a set of allowed IPs
(`none` ⇒ no entry matches). -/
def bestPlen : List Cidr → Bytes → Option Nat
  | [], _ => none
  | c :: rest, ip =>
    if c.matches ip then
      match bestPlen rest ip with
      | some m => some (max c.plen m)
      | none => some c.plen
    else bestPlen rest ip

theorem bestPlen_mem (cs : List Cidr) (ip : Bytes) (n : Nat)
    (h : bestPlen cs ip = some n) :
    ∃ c ∈ cs, c.matches ip = true ∧ c.plen = n := by
  induction cs generalizing n with
  | nil => simp [bestPlen] at h
  | cons c rest ih =>
    simp only [bestPlen] at h
    by_cases hm : c.matches ip
    · rw [if_pos hm] at h
      cases hr : bestPlen rest ip with
      | none => simp only [hr] at h
                injection h with h
                exact ⟨c, by simp, hm, h⟩
      | some m =>
        simp only [hr] at h
        injection h with h
        rcases Nat.le_total m c.plen with hle | hle
        · exact ⟨c, by simp, hm, by omega⟩
        · rcases ih m hr with ⟨c', hc', hm', hp'⟩
          exact ⟨c', by simp [hc'], hm', by omega⟩
    · rw [if_neg hm] at h
      rcases ih n h with ⟨c', hc', hm', hp'⟩
      exact ⟨c', by simp [hc'], hm', hp'⟩

/-- No matching entry ⇒ no route. -/
theorem bestPlen_none (cs : List Cidr) (ip : Bytes)
    (h : bestPlen cs ip = none) : ∀ c ∈ cs, c.matches ip = false := by
  induction cs with
  | nil => intro c hc; simp at hc
  | cons c0 rest ih =>
    intro c hc
    simp only [bestPlen] at h
    by_cases hm0 : c0.matches ip
    · rw [if_pos hm0] at h
      cases hr : bestPlen rest ip <;> simp [hr] at h
    · rw [if_neg hm0] at h
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · simpa using hm0
      · exact ih h c hc

theorem bestPlen_ub (cs : List Cidr) (ip : Bytes) (n : Nat)
    (h : bestPlen cs ip = some n) :
    ∀ c ∈ cs, c.matches ip = true → c.plen ≤ n := by
  induction cs generalizing n with
  | nil => intro c hc; simp at hc
  | cons c0 rest ih =>
    intro c hc hm
    simp only [List.mem_cons] at hc
    simp only [bestPlen] at h
    by_cases hm0 : c0.matches ip
    · rw [if_pos hm0] at h
      cases hr : bestPlen rest ip with
      | none =>
        simp only [hr] at h
        injection h with h
        rcases hc with rfl | hc
        · omega
        · exact absurd (bestPlen_none rest ip hr c hc) (by simp [hm])
      | some m =>
        simp only [hr] at h
        injection h with h
        rcases hc with rfl | hc
        · omega
        · have := ih m hr c hc hm; omega
    · rw [if_neg hm0] at h
      rcases hc with rfl | hc
      · exact absurd hm (by simp [hm0])
      · exact ih n h c hc hm

/-! ### Configured peers and the routing lookup -/

/-- A configured remote peer: static key, preshared key, allowed IPs. -/
structure PeerCfg where
  spub    : ByteArray
  psk     : ByteArray
  allowed : List Cidr

/-- Cryptokey routing: the configured peer with the longest matching
allowed-IPs prefix for an inner destination address. -/
def lookupPeer : List PeerCfg → Bytes → Option (PeerCfg × Nat)
  | [], _ => none
  | p :: rest, ip =>
    match bestPlen p.allowed ip with
    | none => lookupPeer rest ip
    | some n =>
      match lookupPeer rest ip with
      | none => some (p, n)
      | some (q, m) => if m < n then some (p, n) else some (q, m)

/-- A failed lookup means no configured peer has a matching entry — the
packet is unroutable and dropped (the cryptokey-routing drop rule). -/
theorem wg_lookup_none (ps : List PeerCfg) (ip : Bytes)
    (h : lookupPeer ps ip = none) :
    ∀ q ∈ ps, ∀ c ∈ q.allowed, c.matches ip = false := by
  induction ps with
  | nil => intro q hq; simp at hq
  | cons p0 rest ih =>
    intro q hq c hc
    simp only [lookupPeer] at h
    cases hbp : bestPlen p0.allowed ip with
    | none =>
      simp only [hbp] at h
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact bestPlen_none _ _ hbp c hc
      · exact ih h q hq c hc
    | some n0 =>
      simp only [hbp] at h
      cases hr : lookupPeer rest ip with
      | none => simp [hr] at h
      | some qm =>
        obtain ⟨q0, m0⟩ := qm
        simp only [hr] at h
        by_cases hlt : m0 < n0 <;> simp [hlt] at h

/-- **The lookup is sound and longest-prefix.** A routed peer has an
allowed-IPs entry matching the address with the returned prefix length,
and no configured peer has a *longer* matching entry. -/
theorem wg_lookup_longest_prefix (ps : List PeerCfg) (ip : Bytes)
    (p : PeerCfg) (n : Nat) (h : lookupPeer ps ip = some (p, n)) :
    (∃ c ∈ p.allowed, c.matches ip = true ∧ c.plen = n) ∧
    ∀ q ∈ ps, ∀ c ∈ q.allowed, c.matches ip = true → c.plen ≤ n := by
  induction ps generalizing p n with
  | nil => simp [lookupPeer] at h
  | cons p0 rest ih =>
    simp only [lookupPeer] at h
    cases hbp : bestPlen p0.allowed ip with
    | none =>
      simp only [hbp] at h
      rcases ih p n h with ⟨hex, hub⟩
      refine ⟨hex, ?_⟩
      intro q hq c hc hm
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact absurd (bestPlen_none _ _ hbp c hc) (by simp [hm])
      · exact hub q hq c hc hm
    | some n0 =>
      simp only [hbp] at h
      cases hr : lookupPeer rest ip with
      | none =>
        simp only [hr] at h
        injection h with h
        injection h with h1 h2
        subst h1; subst h2
        refine ⟨bestPlen_mem _ _ _ hbp, ?_⟩
        intro q hq c hc hm
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact bestPlen_ub _ _ _ hbp c hc hm
        · exact absurd hm (by simp [wg_lookup_none rest ip hr q hq c hc])
      | some qm =>
        obtain ⟨q0, m0⟩ := qm
        simp only [hr] at h
        by_cases hlt : m0 < n0
        · rw [if_pos hlt] at h
          injection h with h
          injection h with h1 h2
          subst h1; subst h2
          refine ⟨bestPlen_mem _ _ _ hbp, ?_⟩
          intro q hq c hc hm
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact bestPlen_ub _ _ _ hbp c hc hm
          · have := (ih q0 m0 hr).2 q hq c hc hm; omega
        · rw [if_neg hlt] at h
          injection h with h
          injection h with h1 h2
          subst h1; subst h2
          refine ⟨(ih q0 m0 hr).1, ?_⟩
          intro q hq c hc hm
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · have := bestPlen_ub _ _ _ hbp c hc hm; omega
          · exact (ih q0 m0 hr).2 q hq c hc hm

/-! ### Sessions and the engine state -/

/-- One live transport session (a "keypair set" in whitepaper terms):
local/remote indices, the peer it is bound to, both directional keys, the
outbound counter, the anti-replay window, and its creation time. -/
structure Session where
  localIdx  : UInt32
  remoteIdx : UInt32
  /-- The remote peer's static public key this session authenticated. -/
  peer    : ByteArray
  tSend   : ByteArray
  tRecv   : ByteArray
  sendCtr : Nat
  win     : Window
  born    : Nat

/-- An in-flight initiation awaiting its response (initiator side),
carrying what `consumeResponseCore` needs plus the serialized message for
`REKEY_TIMEOUT` retransmission. -/
structure Pending where
  localIdx : UInt32
  /-- The responder's static public key. -/
  peer   : ByteArray
  psk    : ByteArray
  /-- Our ephemeral private scalar for this handshake. -/
  ei     : ByteArray
  /-- The serialized initiation, byte-exact, for retransmission. -/
  msg    : Bytes
  sentAt : Nat
  hs     : Wire.HsState

/-- A wire endpoint. Updated on every authenticated inbound packet —
roaming (§2.1). -/
structure Endpoint where
  host : Bytes
  port : Nat
deriving Repr, DecidableEq

/-- The engine's dynamic state: the session table (newest first, keyed by
local index), pending initiations, the per-peer greatest-timestamp
ratchet, the per-peer roaming endpoint, and the index allocator. -/
structure St where
  sessions  : List (UInt32 × Session)
  pendings  : List (UInt32 × Pending)
  lastTs    : List (Bytes × Nat)
  endpoints : List (Bytes × Endpoint)
  idxCtr    : Nat

def St.empty : St := ⟨[], [], [], [], 1⟩

/-- Static configuration: our static keypair and the configured peers. -/
structure Cfg where
  s     : ByteArray
  spub  : ByteArray
  peers : List PeerCfg

/-- Per-step environment freshness (sans-IO: randomness and time are
inputs): a fresh ephemeral keypair and the clock. -/
structure Fresh where
  e    : ByteArray
  epub : ByteArray
  now  : Nat

/-! ### Association-list helpers -/

def getA {α : Type} (l : List (Bytes × α)) (k : Bytes) : Option α :=
  (l.find? (·.1 == k)).map (·.2)

def setA {α : Type} (l : List (Bytes × α)) (k : Bytes) (v : α) :
    List (Bytes × α) :=
  (k, v) :: l.filter (fun e => !(e.1 == k))

@[simp] theorem getA_setA {α : Type} (l : List (Bytes × α)) (k : Bytes)
    (v : α) : getA (setA l k v) k = some v := by
  simp [getA, setA, List.find?]

/-- The greatest timestamp accepted from a peer (0 before the first). -/
def tsOf (st : St) (k : Bytes) : Nat := (getA st.lastTs k).getD 0

/-- Replace the session stored under a local index. -/
def setSession (l : List (UInt32 × Session)) (i : UInt32) (s : Session) :
    List (UInt32 × Session) :=
  l.map fun e => if e.1 == i then (i, s) else e

theorem mem_setSession {l : List (UInt32 × Session)} {i : UInt32}
    {s' : Session} {e : UInt32 × Session} (hm : e ∈ setSession l i s') :
    e = (i, s') ∨ e ∈ l := by
  unfold setSession at hm
  rcases List.mem_map.mp hm with ⟨e0, he0, heq⟩
  by_cases hc : e0.1 == i
  · rw [if_pos hc] at heq; exact Or.inl heq.symm
  · rw [if_neg hc] at heq; exact Or.inr (heq ▸ he0)

/-- The configured peer for a static key. -/
def findCfg (peers : List PeerCfg) (spub : ByteArray) : Option PeerCfg :=
  peers.find? fun p => Wire.bytesOf p.spub == Wire.bytesOf spub

/-- The newest live session bound to a peer (the send session — new
sessions are prepended, so this is the §6.1 new-replaces-old rule). -/
def sessionFor (l : List (UInt32 × Session)) (spub : Bytes) :
    Option (UInt32 × Session) :=
  l.find? fun e => Wire.bytesOf e.2.peer == spub

theorem route_mem {α : Type} {l : List (UInt32 × α)} {i : UInt32} {a : α}
    (h : Wire.route l i = some a) : ∃ j, (j, a) ∈ l := by
  unfold Wire.route at h
  cases hf : l.find? (fun e => e.1 == i) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map, Option.some.injEq] at h
    exact ⟨e.1, by rw [show (e.1, a) = e by rw [← h]]
                   exact List.mem_of_find?_eq_some hf⟩

/-! ### Inner-packet addresses (cryptokey routing) -/

/-- The inner IPv4 source address of a decrypted transport payload. -/
def innerSrc (pt : ByteArray) : Bytes := ((Wire.bytesOf pt).drop 12).take 4

/-- The inner IPv4 destination address. -/
def innerDst (pt : ByteArray) : Bytes := ((Wire.bytesOf pt).drop 16).take 4

/-- Inbound cryptokey routing: a keepalive (empty payload) is always
admissible; a data packet's inner source must be inside the bound peer's
allowed IPs. -/
def srcAllowed (p : PeerCfg) (pt : ByteArray) : Bool :=
  pt.size == 0 || (bestPlen p.allowed (innerSrc pt)).isSome

/-! ### The four packet handlers -/

/-- Responder: consume a handshake initiation at the byte level. Drops
silently unless: the message parses, mac1 verifies, the AEAD chain opens
(`Wire.consumeInitiation`), the recovered static key is a *configured*
peer, and the timestamp beats the per-peer ratchet. On success: installs a
fresh session (responder key orientation), ratchets the timestamp, records
the roaming endpoint, and emits the serialized response. -/
def handleInitiation (cfg : Cfg) (f : Fresh) (src : Endpoint) (st : St)
    (l : Bytes) : St × Option Bytes :=
  match Wire.consumeInitiation cfg.s cfg.spub l with
  | none => (st, none)
  | some (m, spubI, ts, hs) =>
    match findCfg cfg.peers spubI with
    | none => (st, none)
    | some p =>
      if Wire.tsFresh (tsOf st (Wire.bytesOf spubI)) (Wire.bytesOf ts) then
        match Wire.mkResponse f.e f.epub m.ephemeral spubI p.psk
                (UInt32.ofNat st.idxCtr) m.sender hs with
        | none => (st, none)
        | some (r, hsF) =>
          let ks := Wire.sessionKeys hsF
          let s : Session :=
            ⟨UInt32.ofNat st.idxCtr, m.sender, spubI, ks.2, ks.1, 0,
             Window.fresh, f.now⟩
          ({ sessions := (UInt32.ofNat st.idxCtr, s) :: st.sessions,
             pendings := st.pendings,
             lastTs := setA st.lastTs (Wire.bytesOf spubI)
                        (Wire.tsVal (Wire.bytesOf ts)),
             endpoints := setA st.endpoints (Wire.bytesOf spubI) src,
             idxCtr := st.idxCtr + 1 },
           some (Wire.serializeResponse r))
      else (st, none)

/-- Initiator: start a handshake toward a configured peer, recording the
pending initiation for retransmission. -/
def startHandshake (cfg : Cfg) (f : Fresh) (spubR ts : ByteArray)
    (st : St) : St × Option Bytes :=
  match findCfg cfg.peers spubR with
  | none => (st, none)
  | some p =>
    match Wire.mkInitiation cfg.s cfg.spub f.e f.epub spubR ts
            (UInt32.ofNat st.idxCtr) with
    | none => (st, none)
    | some (m, hs) =>
      let bytes := Wire.serializeInitiation m
      ({ st with
         pendings := (UInt32.ofNat st.idxCtr,
           ⟨UInt32.ofNat st.idxCtr, spubR, p.psk, f.e, bytes, f.now, hs⟩)
           :: st.pendings,
         idxCtr := st.idxCtr + 1 },
       some bytes)

/-- Initiator: consume a handshake response at the byte level — route to
the pending initiation by receiver index, run `consumeResponseCore`, and
on success install the session (initiator key orientation), drop the
pending, and record the endpoint. Returns the new session's local index. -/
def handleResponse (cfg : Cfg) (now : Nat) (src : Endpoint) (st : St)
    (l : Bytes) : St × Option UInt32 :=
  match Wire.parseResponse l with
  | none => (st, none)
  | some m =>
    match Wire.route st.pendings m.receiver with
    | none => (st, none)
    | some pd =>
      match Wire.consumeResponseCore cfg.s pd.ei cfg.spub pd.psk m pd.hs with
      | none => (st, none)
      | some hsF =>
        let ks := Wire.sessionKeys hsF
        let s : Session :=
          ⟨pd.localIdx, m.sender, pd.peer, ks.1, ks.2, 0, Window.fresh, now⟩
        ({ st with
           sessions := (pd.localIdx, s) :: st.sessions,
           pendings := st.pendings.filter (fun e => !(e.1 == m.receiver)),
           endpoints := setA st.endpoints (Wire.bytesOf pd.peer) src },
         some pd.localIdx)

/-- Header peek of a type-4 packet: receiver index and clear counter. -/
def peekTransport (l : Bytes) : Option (UInt32 × Nat) :=
  match Wire.readN 4 l with
  | none => none
  | some (ty, l) =>
    if ty = [4, 0, 0, 0] then
      match Wire.readN 4 l with
      | none => none
      | some (rcv, l) =>
        match Wire.readN 8 l with
        | none => none
        | some (ctr, _) => some (UInt32.ofNat (Wire.leVal rcv), Wire.leVal ctr)
    else none

/-- Data plane: consume a transport packet at the byte level — route by
receiver index, consult the session's anti-replay window on the clear
counter, AEAD-open, enforce inbound cryptokey routing on the inner source
address, and only then mark the window, update the roaming endpoint, and
deliver the plaintext. Every failure is a silent drop with the state
untouched. -/
def handleTransport (cfg : Cfg) (src : Endpoint) (st : St)
    (l : Bytes) : St × Option ByteArray :=
  match peekTransport l with
  | none => (st, none)
  | some (idx, ctr) =>
    match Wire.route st.sessions idx with
    | none => (st, none)
    | some s =>
      if s.win.willAccept ctr then
        match Wire.openPacket s.tRecv l with
        | none => (st, none)
        | some (_, _, pt) =>
          match findCfg cfg.peers s.peer with
          | none => (st, none)
          | some p =>
            if srcAllowed p pt then
              ({ st with
                 sessions := setSession st.sessions idx
                              { s with win := s.win.mark ctr },
                 endpoints := setA st.endpoints (Wire.bytesOf s.peer) src },
               some pt)
            else (st, none)
      else (st, none)

/-- Application send: cryptokey-route the inner destination to a peer,
take its newest session and roamed endpoint, seal at the current send
counter, and advance the counter. -/
def sendApp (cfg : Cfg) (st : St) (pt : ByteArray) :
    St × Option (Bytes × Endpoint) :=
  match lookupPeer cfg.peers (innerDst pt) with
  | none => (st, none)
  | some (p, _) =>
    match sessionFor st.sessions (Wire.bytesOf p.spub) with
    | none => (st, none)
    | some (i, s) =>
      match getA st.endpoints (Wire.bytesOf p.spub) with
      | none => (st, none)
      | some ep =>
        match Wire.sealPacket s.tSend s.remoteIdx (UInt64.ofNat s.sendCtr) pt with
        | none => (st, none)
        | some out =>
          ({ st with sessions := setSession st.sessions i
                       { s with sendCtr := s.sendCtr + 1 } },
           some (out, ep))

/-! ### Timers (§6.1/§6.5) -/

/-- Tear down sessions past the hard `REJECT_AFTER_TIME` limit. -/
def expire (now : Nat) (st : St) : St :=
  { st with sessions := st.sessions.filter fun e =>
      decide (now < e.2.born + Rekey.REJECT_AFTER_TIME) }

/-- Initiations due for retransmission: `REKEY_TIMEOUT` elapsed. -/
def retransmits (now : Nat) (st : St) : List Bytes :=
  (st.pendings.filter fun e =>
    decide (e.2.sentAt + Rekey.REKEY_TIMEOUT ≤ now)).map (·.2.msg)

/-- Refresh the send time of just-retransmitted pendings. -/
def touchPendings (now : Nat) (st : St) : St :=
  { st with pendings := st.pendings.map fun e =>
      if decide (e.2.sentAt + Rekey.REKEY_TIMEOUT ≤ now)
      then (e.1, { e.2 with sentAt := now }) else e }

/-- Sessions past a soft rekey threshold (message count or age): a fresh
handshake should be initiated for their peers. -/
def rekeyDue (now : Nat) (st : St) : List Session :=
  (st.sessions.filter fun e =>
    Rekey.needsRekey ⟨e.2.sendCtr, now - e.2.born⟩).map (·.2)

/-! ### The window invariant, engine-wide -/

/-- Every installed session's window satisfies the anti-replay invariant. -/
def Inv (st : St) : Prop :=
  ∀ e : UInt32 × Session, e ∈ st.sessions → Window.Inv e.2.win

theorem inv_empty : Inv St.empty := by
  intro e he; simp [St.empty] at he

theorem inv_handleInitiation (cfg : Cfg) (f : Fresh) (src : Endpoint)
    (st : St) (l : Bytes) (h : Inv st) :
    Inv (handleInitiation cfg f src st l).1 := by
  unfold handleInitiation
  split
  · exact h
  · split
    · exact h
    · split
      · split
        · exact h
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact Window.inv_fresh
          · exact h e he
      · exact h

theorem inv_startHandshake (cfg : Cfg) (f : Fresh) (spubR ts : ByteArray)
    (st : St) (h : Inv st) : Inv (startHandshake cfg f spubR ts st).1 := by
  unfold startHandshake
  split
  · exact h
  · split
    · exact h
    · intro e he; exact h e he

theorem inv_handleResponse (cfg : Cfg) (now : Nat) (src : Endpoint)
    (st : St) (l : Bytes) (h : Inv st) :
    Inv (handleResponse cfg now src st l).1 := by
  unfold handleResponse
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact Window.inv_fresh
        · exact h e he

theorem inv_handleTransport (cfg : Cfg) (src : Endpoint) (st : St)
    (l : Bytes) (h : Inv st) : Inv (handleTransport cfg src st l).1 := by
  unfold handleTransport
  split
  · exact h
  · split
    · exact h
    · rename_i part idx ctr heq s hroute
      split
      · split
        · exact h
        · split
          · exact h
          · split
            · intro e he
              simp only at he
              rcases mem_setSession he with rfl | he
              · have hs : Window.Inv s.win := by
                  rcases route_mem hroute with ⟨j, hj⟩
                  exact h (j, s) hj
                exact Window.inv_mark _ _ hs
              · exact h e he
            · exact h
      · exact h

theorem sessionFor_mem {l : List (UInt32 × Session)} {spub : Bytes}
    {i : UInt32} {s : Session} (h : sessionFor l spub = some (i, s)) :
    (i, s) ∈ l :=
  List.mem_of_find?_eq_some h

theorem inv_sendApp (cfg : Cfg) (st : St) (pt : ByteArray) (h : Inv st) :
    Inv (sendApp cfg st pt).1 := by
  unfold sendApp
  split
  · exact h
  · split
    · exact h
    · rename_i pn p n i s hsess
      split
      · exact h
      · split
        · exact h
        · intro e he
          simp only at he
          rcases mem_setSession he with rfl | he
          · exact h (i, s) (sessionFor_mem hsess)
          · exact h e he

theorem inv_expire (now : Nat) (st : St) (h : Inv st) :
    Inv (expire now st) := by
  intro e he
  unfold expire at he
  simp only at he
  exact h e (List.mem_filter.mp he).1

theorem inv_touchPendings (now : Nat) (st : St) (h : Inv st) :
    Inv (touchPendings now st) := by
  intro e he
  exact h e he

/-- States reachable through the engine's operations from the empty
state. -/
inductive Reach (cfg : Cfg) : St → Prop where
  | empty : Reach cfg St.empty
  | init  {st} (h : Reach cfg st) (f : Fresh) (src : Endpoint) (l : Bytes) :
      Reach cfg (handleInitiation cfg f src st l).1
  | start {st} (h : Reach cfg st) (f : Fresh) (spubR ts : ByteArray) :
      Reach cfg (startHandshake cfg f spubR ts st).1
  | resp  {st} (h : Reach cfg st) (now : Nat) (src : Endpoint) (l : Bytes) :
      Reach cfg (handleResponse cfg now src st l).1
  | trans {st} (h : Reach cfg st) (src : Endpoint) (l : Bytes) :
      Reach cfg (handleTransport cfg src st l).1
  | send  {st} (h : Reach cfg st) (pt : ByteArray) :
      Reach cfg (sendApp cfg st pt).1
  | exp   {st} (h : Reach cfg st) (now : Nat) : Reach cfg (expire now st)
  | touch {st} (h : Reach cfg st) (now : Nat) :
      Reach cfg (touchPendings now st)

/-- Every reachable engine state satisfies the window invariant. -/
theorem wg_reach_inv (cfg : Cfg) {st : St} (h : Reach cfg st) : Inv st := by
  induction h with
  | empty => exact inv_empty
  | init _ f src l ih => exact inv_handleInitiation cfg f src _ l ih
  | start _ f spubR ts ih => exact inv_startHandshake cfg f spubR ts _ ih
  | resp _ now src l ih => exact inv_handleResponse cfg now src _ l ih
  | trans _ src l ih => exact inv_handleTransport cfg src _ l ih
  | send _ pt ih => exact inv_sendApp cfg _ pt ih
  | exp _ now ih => exact inv_expire now _ ih
  | touch _ now ih => exact inv_touchPendings now _ ih

/-! ### The composed data-plane guarantees -/

/-- **Replay rejected across packets, at the byte level.** In every
reachable engine state, a transport packet whose clear counter was already
accepted on its session delivers nothing and leaves the state exactly
unchanged. This is the FSM's `wg_replay_rejected` composed with the wire
codec, the index routing, and the session table. -/
theorem wg_peer_replay_rejected (cfg : Cfg) (src : Endpoint) {st : St}
    (hreach : Reach cfg st) {l : Bytes} {idx : UInt32} {ctr : Nat}
    (hp : peekTransport l = some (idx, ctr)) {s : Session}
    (hr : Wire.route st.sessions idx = some s)
    (hseen : s.win.seen.contains ctr = true) :
    handleTransport cfg src st l = (st, none) := by
  have hwin : Window.Inv s.win := by
    rcases route_mem hr with ⟨j, hj⟩
    exact wg_reach_inv cfg hreach (j, s) hj
  have hrej : s.win.willAccept ctr = false :=
    Window.replay_rejected _ _ hwin hseen
  unfold handleTransport
  simp [hp, hr, hrej]

/-- **Too-old rejected, composed** — a counter fallen off the back of the
window is dropped, no history needed. -/
theorem wg_peer_too_old_rejected (cfg : Cfg) (src : Endpoint) (st : St)
    {l : Bytes} {idx : UInt32} {ctr : Nat}
    (hp : peekTransport l = some (idx, ctr)) {s : Session}
    (hr : Wire.route st.sessions idx = some s)
    (hold : ctr + windowSize < s.win.next) :
    handleTransport cfg src st l = (st, none) := by
  have hrej : s.win.willAccept ctr = false :=
    Window.too_old_rejected _ _ hold
  unfold handleTransport
  simp [hp, hr, hrej]

/-- **Unknown receiver index: silent drop** (the whitepaper's unroutable
rule at the session table). -/
theorem wg_peer_unknown_index_dropped (cfg : Cfg) (src : Endpoint) (st : St)
    {l : Bytes} {idx : UInt32} {ctr : Nat}
    (hp : peekTransport l = some (idx, ctr))
    (hr : Wire.route st.sessions idx = none) :
    handleTransport cfg src st l = (st, none) := by
  unfold handleTransport
  simp [hp, hr]

/-- **Delivery inversion.** Anything the engine delivers passed the whole
gauntlet: a well-formed type-4 header routed to a live session, a window
acceptance, an AEAD open, a configured peer, and the inbound cryptokey
routing check — and the state advanced by exactly the window mark and the
roaming endpoint update. -/
theorem wg_transport_delivery_inverted (cfg : Cfg) (src : Endpoint)
    (st : St) (l : Bytes) {st' : St} {pt : ByteArray}
    (h : handleTransport cfg src st l = (st', some pt)) :
    ∃ idx ctr s p,
      peekTransport l = some (idx, ctr) ∧
      Wire.route st.sessions idx = some s ∧
      s.win.willAccept ctr = true ∧
      findCfg cfg.peers s.peer = some p ∧
      srcAllowed p pt = true ∧
      st'.sessions = setSession st.sessions idx
        { s with win := s.win.mark ctr } ∧
      getA st'.endpoints (Wire.bytesOf s.peer) = some src := by
  unfold handleTransport at h
  split at h
  · simp at h
  · rename_i part idx ctr hpeek
    split at h
    · simp at h
    · rename_i s hroute
      split at h
      · rename_i hacc
        split at h
        · simp at h
        · rename_i trip a b pt0 hopen
          split at h
          · simp at h
          · rename_i p hfind
            split at h
            · rename_i hallow
              injection h with h1 h2
              injection h2 with h2
              subst h2
              subst h1
              exact ⟨idx, ctr, s, p, hpeek, hroute, hacc, hfind, hallow,
                     rfl, getA_setA _ _ _⟩
            · simp at h
      · simp at h

/-- **Inbound cryptokey routing enforced.** A delivered (non-keepalive)
payload's inner source address lies inside the bound peer's allowed IPs:
there is a configured CIDR entry that matches it. -/
theorem wg_allowed_ips_enforced (cfg : Cfg) (src : Endpoint) (st : St)
    (l : Bytes) {st' : St} {pt : ByteArray}
    (h : handleTransport cfg src st l = (st', some pt))
    (hne : pt.size ≠ 0) :
    ∃ idx ctr s p c,
      peekTransport l = some (idx, ctr) ∧
      Wire.route st.sessions idx = some s ∧
      findCfg cfg.peers s.peer = some p ∧
      c ∈ p.allowed ∧ c.matches (innerSrc pt) = true := by
  rcases wg_transport_delivery_inverted cfg src st l h with
    ⟨idx, ctr, s, p, hpeek, hroute, _, hfind, hallow, _, _⟩
  have hz : (pt.size == 0) = false := by
    simp [hne]
  rw [srcAllowed, hz, Bool.false_or] at hallow
  cases hbp : bestPlen p.allowed (innerSrc pt) with
  | none => rw [hbp] at hallow; cases hallow
  | some n =>
    rcases bestPlen_mem _ _ _ hbp with ⟨c, hc, hm, _⟩
    exact ⟨idx, ctr, s, p, c, hpeek, hroute, hfind, hc, hm⟩

/-- **Roaming.** Every delivery re-points the peer's endpoint at the
packet's source — the §2.1 update-on-authenticated-receipt rule. -/
theorem wg_roaming_updates_endpoint (cfg : Cfg) (src : Endpoint) (st : St)
    (l : Bytes) {st' : St} {pt : ByteArray}
    (h : handleTransport cfg src st l = (st', some pt)) :
    ∃ idx ctr s, peekTransport l = some (idx, ctr) ∧
      Wire.route st.sessions idx = some s ∧
      getA st'.endpoints (Wire.bytesOf s.peer) = some src := by
  rcases wg_transport_delivery_inverted cfg src st l h with
    ⟨idx, ctr, s, _, hpeek, hroute, _, _, _, _, hep⟩
  exact ⟨idx, ctr, s, hpeek, hroute, hep⟩

/-! ### The composed handshake guarantees -/

/-- **Unconfigured static keys are refused.** An initiation that
authenticates cryptographically but whose recovered static key is not a
configured peer is dropped without any state change — cryptokey identity,
not just cryptographic validity. -/
theorem wg_unknown_static_dropped (cfg : Cfg) (f : Fresh) (src : Endpoint)
    (st : St) {l : Bytes} {m : Wire.InitiationMsg}
    {spubI ts : ByteArray} {hs : Wire.HsState}
    (hc : Wire.consumeInitiation cfg.s cfg.spub l = some (m, spubI, ts, hs))
    (hu : findCfg cfg.peers spubI = none) :
    handleInitiation cfg f src st l = (st, none) := by
  unfold handleInitiation
  simp [hc, hu]

/-- **A stale timestamp is refused** — the per-peer greatest-timestamp
ratchet at the engine level. -/
theorem wg_stale_initiation_dropped (cfg : Cfg) (f : Fresh) (src : Endpoint)
    (st : St) {l : Bytes} {m : Wire.InitiationMsg}
    {spubI ts : ByteArray} {hs : Wire.HsState}
    (hc : Wire.consumeInitiation cfg.s cfg.spub l = some (m, spubI, ts, hs))
    (hstale : Wire.tsFresh (tsOf st (Wire.bytesOf spubI))
                (Wire.bytesOf ts) = false) :
    handleInitiation cfg f src st l = (st, none) := by
  unfold handleInitiation
  cases hf : findCfg cfg.peers spubI with
  | none => simp [hc, hf]
  | some p => simp [hc, hf, hstale]

/-- **Initiation replay is inert end-to-end.** Feeding the engine the
exact bytes of an initiation it just accepted is a silent drop: acceptance
ratcheted the peer's timestamp to the message's own, and
`tsFresh (tsVal t) t = false`. The whitepaper's §5.1 replay story,
composed through the byte codec, the AEAD chain, and the state. -/
theorem wg_peer_initiation_replay_inert (cfg : Cfg) (f f' : Fresh)
    (src src' : Endpoint) (st : St) {st' : St} {out : Bytes} {l : Bytes}
    (h : handleInitiation cfg f src st l = (st', some out)) :
    handleInitiation cfg f' src' st' l = (st', none) := by
  unfold handleInitiation at h
  split at h
  · simp at h
  · rename_i quad m spubI ts hs hc
    split at h
    · simp at h
    · rename_i p hf
      split at h
      · split at h
        · simp at h
        · rename_i pair r hsF hmk
          injection h with h1 h2
          apply wg_stale_initiation_dropped cfg f' src' st' hc
          rw [← h1]
          simp [tsOf, Wire.wg_initiation_replay_rejected]
      · simp at h

/-- **An honest configured initiation is accepted by the engine.** The
byte-level handshake refinement (`wg_initiation_refines`) composed with
the codec roundtrip and the engine: honest initiation bytes from a
configured peer with a fresh timestamp produce exactly the serialized
response (the size hypotheses are the wire widths, emitted by
construction). -/
theorem wg_peer_accepts_honest_initiation
    (cfg : Cfg) (f : Fresh) (src : Endpoint) (st : St)
    {si ei spubI epubI ts : ByteArray} {sender : UInt32}
    (hSI : Crypto.x25519Base si = some spubI)
    (hEI : Crypto.x25519Base ei = some epubI)
    (hSR : Crypto.x25519Base cfg.s = some cfg.spub)
    {m : Wire.InitiationMsg} {hs : Wire.HsState}
    (hmk : Wire.mkInitiation si spubI ei epubI cfg.spub ts sender
            = some (m, hs))
    (he : m.ephemeral.size = 32) (hsz : m.encStatic.size = 48)
    (ht : m.encTs.size = 28) (h1 : m.mac1.size = 16) (h2 : m.mac2.size = 16)
    {p : PeerCfg} (hp : findCfg cfg.peers spubI = some p)
    (hfresh : Wire.tsFresh (tsOf st (Wire.bytesOf spubI))
                (Wire.bytesOf ts) = true)
    {r : Wire.ResponseMsg} {hsF : Wire.HsState}
    (hresp : Wire.mkResponse f.e f.epub m.ephemeral spubI p.psk
              (UInt32.ofNat st.idxCtr) m.sender hs = some (r, hsF)) :
    (handleInitiation cfg f src st (Wire.serializeInitiation m)).2
      = some (Wire.serializeResponse r) := by
  have hcore : Wire.consumeInitiationCore cfg.s cfg.spub m
      = some (spubI, ts, hs) :=
    Wire.wg_initiation_refines hSI hEI hSR hmk
  have hparse : Wire.parseInitiation (Wire.serializeInitiation m) = some m :=
    Wire.parse_serialize_initiation m he hsz ht h1 h2
  have hci : Wire.consumeInitiation cfg.s cfg.spub
      (Wire.serializeInitiation m) = some (m, spubI, ts, hs) := by
    unfold Wire.consumeInitiation
    rw [hparse]
    simp [hcore]
  unfold handleInitiation
  simp [hci, hp, hfresh, hresp]

/-! ### The send path and the timers -/

/-- **Unroutable outbound packets are dropped** — no configured peer's
allowed IPs cover the inner destination, nothing is sent (cryptokey
routing, outbound side). -/
theorem wg_unroutable_dropped (cfg : Cfg) (st : St) (pt : ByteArray)
    (h : lookupPeer cfg.peers (innerDst pt) = none) :
    sendApp cfg st pt = (st, none) := by
  unfold sendApp
  simp [h]

/-- **Each send burns a fresh counter.** A successful send sealed at the
session's current counter and stored the session back with the counter
advanced — combined with `wg_transport_nonce_injective`, no AEAD nonce
ever repeats under a transport key. -/
theorem wg_send_counter_advances (cfg : Cfg) (st : St) (pt : ByteArray)
    {st' : St} {out : Bytes} {ep : Endpoint}
    (h : sendApp cfg st pt = (st', some (out, ep))) :
    ∃ pn i s, lookupPeer cfg.peers (innerDst pt) = some pn ∧
      sessionFor st.sessions (Wire.bytesOf pn.1.spub) = some (i, s) ∧
      Wire.sealPacket s.tSend s.remoteIdx (UInt64.ofNat s.sendCtr) pt
        = some out ∧
      st'.sessions = setSession st.sessions i
        { s with sendCtr := s.sendCtr + 1 } := by
  unfold sendApp at h
  split at h
  · simp at h
  · rename_i pn p n hlook
    split at h
    · simp at h
    · rename_i pr i s hsess
      split at h
      · simp at h
      · rename_i ep0 hep
        split at h
        · simp at h
        · rename_i out0 hseal
          injection h with h1 h2
          injection h2 with h2
          injection h2 with h2a h2b
          subst h1
          subst h2a
          exact ⟨(p, n), i, s, hlook, hsess, hseal, rfl⟩

/-- **Expiry is sound and complete**: after `expire now`, exactly the
sessions strictly inside `REJECT_AFTER_TIME` remain. -/
theorem wg_expire_iff (now : Nat) (st : St) (e : UInt32 × Session) :
    e ∈ (expire now st).sessions ↔
      e ∈ st.sessions ∧ now < e.2.born + Rekey.REJECT_AFTER_TIME := by
  unfold expire
  simp [List.mem_filter]

/-- **Retransmission fires exactly on timeout**: the retransmit list is
precisely the pending initiations whose `REKEY_TIMEOUT` has elapsed. -/
theorem wg_retransmit_iff (now : Nat) (st : St) (b : Bytes) :
    b ∈ retransmits now st ↔
      ∃ e ∈ st.pendings, e.2.msg = b ∧
        e.2.sentAt + Rekey.REKEY_TIMEOUT ≤ now := by
  unfold retransmits
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨e, he, rfl⟩
    have hf := List.mem_filter.mp he
    exact ⟨e, hf.1, rfl, by simpa using hf.2⟩
  · rintro ⟨e, he, rfl, hd⟩
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simpa using hd⟩, rfl⟩

/-- **Touching quiesces the retransmit clock**: right after refreshing the
send times, nothing is due (REKEY_TIMEOUT is positive). -/
theorem wg_touch_quiesces (now : Nat) (st : St) :
    retransmits now (touchPendings now st) = [] := by
  cases hr : retransmits now (touchPendings now st) with
  | nil => rfl
  | cons b rest =>
    exfalso
    have hb : b ∈ retransmits now (touchPendings now st) := by
      rw [hr]; exact List.mem_cons_self ..
    rcases (wg_retransmit_iff now (touchPendings now st) b).mp hb with
      ⟨e, he, _, hd⟩
    unfold touchPendings at he
    simp only at he
    rcases List.mem_map.mp he with ⟨e0, _, heq⟩
    by_cases h0 : e0.2.sentAt + Rekey.REKEY_TIMEOUT ≤ now
    · rw [if_pos (by simpa using h0)] at heq
      subst heq
      simp only [Rekey.REKEY_TIMEOUT] at hd
      omega
    · rw [if_neg (by simpa using h0)] at heq
      subst heq
      exact h0 hd

end Peer

end Wireguard
