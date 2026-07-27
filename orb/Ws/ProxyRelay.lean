import Ws.Frame

/-!
# WebSocket proxy relay (RFC 6455 §5, §7) — bidirectional frame relay

A WebSocket proxy sits between a client and an upstream server and relays
decoded frames (`Ws.Frame`: FIN, opcode, unmasked payload) in both directions:
client→upstream and upstream→client. This module fixes the relay as a pure
per-direction transform and proves the three properties a transparent relay must
satisfy:

* **Faithful** (`ws_relay_faithful`) — the frames a direction emits are a verbatim
  prefix of the frames it received: identical frames, identical order, nothing
  rewritten. Both directions independently.
* **Close-propagating and halting** (`ws_relay_close`) — a Close control frame is
  forwarded to the peer, and the relay in that direction stops: every frame that
  arrived after the Close is dropped (§7.1.1 — no traffic after Close).
* **No injection** (`ws_relay_no_inject`) — every frame the relay emits arrived on
  the corresponding input stream; the relay originates no frames of its own.

The relay is byte-transparent at the frame layer: a forwarded frame is the same
`Frame` record, so its payload bytes are identical. Deliberately out of scope:
the close *handshake* state machine (that is `Ws.Close`); this module is the
data-plane relay that carries frames between the two `Ws.Close` endpoints.
-/

namespace Ws
namespace ProxyRelay

/-- Relay one direction of the connection: forward each frame verbatim until a
Close control frame, which is forwarded and then terminates the direction (no
frame after the Close is relayed — §7.1.1). -/
def relayDir : List Frame → List Frame
  | [] => []
  | f :: rest =>
    if f.opcode = Opcode.close then [f]
    else f :: relayDir rest

/-- The two half-connections a proxy bridges: `c2u` is the client→upstream frame
stream, `u2c` the upstream→client stream. -/
structure Duplex where
  c2u : List Frame
  u2c : List Frame
deriving Repr, DecidableEq

/-- What the relay forwards on each half. -/
structure Relayed where
  toUpstream : List Frame
  toClient : List Frame
deriving Repr, DecidableEq

/-- The bidirectional relay: each direction is relayed independently. -/
def relay (d : Duplex) : Relayed :=
  { toUpstream := relayDir d.c2u, toClient := relayDir d.u2c }

/-! ## Per-direction core lemmas -/

/-- The relayed stream is a **verbatim prefix** of the input stream: the emitted
frames are exactly the input frames, in order, up to the truncation point —
nothing is rewritten or reordered. -/
theorem relayDir_prefix (xs : List Frame) : relayDir xs <+: xs := by
  induction xs with
  | nil => exact List.nil_prefix
  | cons f rest ih =>
    simp only [relayDir]
    by_cases h : f.opcode = Opcode.close
    · rw [if_pos h]; exact ⟨rest, rfl⟩
    · rw [if_neg h]
      obtain ⟨t, ht⟩ := ih
      exact ⟨t, by rw [List.cons_append, ht]⟩

/-- With no Close frame present, the relay is the **identity**: every frame is
forwarded verbatim, the full stream passes through. -/
theorem relayDir_no_close (xs : List Frame)
    (h : ∀ f ∈ xs, f.opcode ≠ Opcode.close) : relayDir xs = xs := by
  induction xs with
  | nil => rfl
  | cons f rest ih =>
    have hf : f.opcode ≠ Opcode.close := h f (List.mem_cons_self)
    simp only [relayDir, if_neg hf]
    rw [ih (fun g hg => h g (List.mem_cons_of_mem f hg))]

/-- Every relayed frame arrived on the input stream: the relay **originates no
frame of its own**. -/
theorem relayDir_subset (xs : List Frame) {f : Frame}
    (hf : f ∈ relayDir xs) : f ∈ xs := by
  obtain ⟨t, ht⟩ := relayDir_prefix xs
  rw [← ht]
  exact List.mem_append.mpr (Or.inl hf)

/-- The relay never lengthens a stream: it emits at most the frames it received. -/
theorem relayDir_length_le (xs : List Frame) :
    (relayDir xs).length ≤ xs.length := by
  obtain ⟨t, ht⟩ := relayDir_prefix xs
  calc (relayDir xs).length
      ≤ (relayDir xs).length + t.length := Nat.le_add_right _ _
    _ = (relayDir xs ++ t).length := by rw [List.length_append]
    _ = xs.length := by rw [ht]

/-- **Close propagation + halt (per direction).** If a stream is `pre ++ f ::
post` where `pre` carries no Close and `f` is a Close frame, the relay forwards
exactly `pre ++ [f]`: the Close `f` is propagated to the peer, and every frame in
`post` (everything after the Close) is dropped. -/
theorem relayDir_close (pre : List Frame) (f : Frame) (post : List Frame)
    (hpre : ∀ g ∈ pre, g.opcode ≠ Opcode.close)
    (hf : f.opcode = Opcode.close) :
    relayDir (pre ++ f :: post) = pre ++ [f] := by
  induction pre with
  | nil => simp only [List.nil_append, relayDir, if_pos hf]
  | cons g gs ih =>
    have hg : g.opcode ≠ Opcode.close := hpre g (List.mem_cons_self)
    simp only [List.cons_append, relayDir, if_neg hg]
    rw [ih (fun x hx => hpre x (List.mem_cons_of_mem g hx))]

/-! ## Headline theorems — the bidirectional relay contract -/

/-- **`ws_relay_faithful`.** In *both* directions the proxy relays frames
verbatim: the frames delivered to the upstream are a prefix of the frames the
client sent, and the frames delivered to the client are a prefix of the frames
the upstream sent — identical frames, identical order, no rewriting. -/
theorem ws_relay_faithful (d : Duplex) :
    (relay d).toUpstream <+: d.c2u ∧ (relay d).toClient <+: d.u2c :=
  ⟨relayDir_prefix d.c2u, relayDir_prefix d.u2c⟩

/-- Sharpened faithfulness: on a Close-free connection the relay is the exact
identity in both directions — every frame passes through untouched. -/
theorem ws_relay_faithful_exact (d : Duplex)
    (hc2u : ∀ f ∈ d.c2u, f.opcode ≠ Opcode.close)
    (hu2c : ∀ f ∈ d.u2c, f.opcode ≠ Opcode.close) :
    (relay d).toUpstream = d.c2u ∧ (relay d).toClient = d.u2c :=
  ⟨relayDir_no_close d.c2u hc2u, relayDir_no_close d.u2c hu2c⟩

/-- **`ws_relay_close`.** A Close frame is propagated to the peer and the relay
halts. If the client sends `pre ++ close :: post` (with `pre` Close-free), the
proxy forwards exactly `pre ++ [close]` to the upstream: the Close crosses, and
every frame after it (`post`) is dropped. The upstream→client direction is the
symmetric statement `ws_relay_close_clientward`. -/
theorem ws_relay_close (d : Duplex) (pre post : List Frame) (f : Frame)
    (hc2u : d.c2u = pre ++ f :: post)
    (hpre : ∀ g ∈ pre, g.opcode ≠ Opcode.close)
    (hf : f.opcode = Opcode.close) :
    (relay d).toUpstream = pre ++ [f] := by
  simp only [relay, hc2u]
  exact relayDir_close pre f post hpre hf

/-- The symmetric direction: a Close from the upstream is propagated to the
client and the client-ward relay halts, dropping every following frame. -/
theorem ws_relay_close_clientward (d : Duplex) (pre post : List Frame) (f : Frame)
    (hu2c : d.u2c = pre ++ f :: post)
    (hpre : ∀ g ∈ pre, g.opcode ≠ Opcode.close)
    (hf : f.opcode = Opcode.close) :
    (relay d).toClient = pre ++ [f] := by
  simp only [relay, hu2c]
  exact relayDir_close pre f post hpre hf

/-- **`ws_relay_no_inject`.** The relay adds no frames of its own: every frame
delivered to the upstream arrived from the client, and every frame delivered to
the client arrived from the upstream. -/
theorem ws_relay_no_inject (d : Duplex) {f : Frame} :
    (f ∈ (relay d).toUpstream → f ∈ d.c2u) ∧
    (f ∈ (relay d).toClient → f ∈ d.u2c) :=
  ⟨fun h => relayDir_subset d.c2u h, fun h => relayDir_subset d.u2c h⟩

/-! ## Non-vacuity witnesses

Concrete instances that pin the relay down: the theorems are not vacuously true
of the empty stream, and a relay that dropped a Close, rewrote a payload, or
injected a keepalive would fail them. -/

/-- A data frame with a given payload. -/
private def dataFrame (b : Bytes) : Frame :=
  { fin := true, opcode := .binary, payload := b }

/-- A Close frame (empty body — a bare Close). -/
private def closeFrame : Frame :=
  { fin := true, opcode := .close, payload := [] }

/-- Witness: two data frames then a Close then a trailing (post-Close) data frame.
The relay forwards the first two data frames and the Close verbatim, and drops the
trailing frame — Close propagated, relay halted, nothing rewritten, nothing
injected. -/
example :
    relayDir [dataFrame [1], dataFrame [2], closeFrame, dataFrame [3]]
      = [dataFrame [1], dataFrame [2], closeFrame] := by decide

/-- Witness: with no Close, all frames pass through in order — a genuinely
non-empty faithful relay. -/
example :
    relayDir [dataFrame [7], dataFrame [8], dataFrame [9]]
      = [dataFrame [7], dataFrame [8], dataFrame [9]] := by decide

/-- Witness: the trailing post-Close frame is genuinely absent from the output —
`ws_relay_no_inject`/`ws_relay_close` are not vacuous. -/
example : dataFrame [3] ∉ relayDir [closeFrame, dataFrame [3]] := by decide

end ProxyRelay
end Ws
