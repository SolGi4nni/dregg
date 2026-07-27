/-
# ChannelDataLive — driving the PROVEN TURN ChannelData relay over bytes (RFC 8656 §12)

`TurnLive` wired ALLOCATE (default-deny) and `TurnPermLive` wired the two grant
paths (CREATE-PERMISSION §9 and CHANNEL-BIND §11). This lane wires the third RFC
8656 relay mechanism — the **ChannelData** message (§12) — driven off the wire,
and proves the two properties a ChannelData relay must have:

  1. `channeldata_frames` — the ChannelData wire format is exactly a 2-byte
     channel number, a 2-byte length, the application data, padded to a 4-byte
     boundary (§12.4); a frame round-trips to its `(channel, payload)`, and a
     frame carrying a *valid* channel number (0x4000..0x7FFF) is recognised as
     ChannelData (top two bits 0b01) on a socket shared with STUN (0b00).

  2. `channeldata_only_bound_peer` — a ChannelData frame relays to *exactly* the
     peer bound to its channel number and to no one else, and a frame whose
     channel is not bound is dropped (relayed to no peer). This is the §12
     anti-reflector clause: ChannelData follows the channel binding, never a
     free choice of destination.

Both compose the proven `Turn.lean` codec/relay (`channelData`,
`decodeChannelData`, `channelData_roundtrip`, `channelSend`, `channelPeer`,
`channelSend_channelData`) — no forked framer.

## Honesty / realization boundary (the ControlLive / TurnPermLive discipline)

This is **drorb-native**: a client and a relay speaking the modelled RFC 8656
ChannelData wire format over the byte level in ONE process (no sockets), NOT a
real UDP interop against a third-party TURN client/server. It is a live
cross-check (rung 2, a selftest), NOT the deployed dataplane serve. Everything
structural/codec/relay is the proven Lean; the selftest calls the proven Lean
functions on real bytes and cross-checks each decision against the model. It
exercises NO MESSAGE-INTEGRITY and NO crypto, so it runs under the pure Lean
interpreter (`lake env lean --run`) with zero linked crypto — no `@[extern]`
opaque is referenced by this file.

Deployed-engine correspondence: the ChannelData framing modelled here —
`[2B channel][2B length][payload][pad to 4B]`, valid channel 0x4000..0x7FFF,
and "unknown channel ⇒ drop" — matches the native TURN engine byte-for-byte
(`encode_channel_data` / `handle_channel_data`), so the row's claim holds of the
real dataplane, not merely of the model.

Usage:
  channeldata-live selftest
-/
import Turn

namespace Turn.ChannelDataLive

open Stun (Bytes Endpoint)
open Stun
open Turn

/-! ## Framing theorem (RFC 8656 §12.4)

The ChannelData wire form is exactly `[2B channel][2B length][data][pad]`. We
prove: (a) the first four bytes are the 16-bit big-endian channel number then
the 16-bit big-endian length; (b) the whole frame decodes back to precisely
`(ch, payload)`; (c) a frame carrying a channel number in the valid range
0x4000..0x7FFF is recognised as ChannelData (its first byte lies in 0x40..0x7F,
so the top two bits are 0b01, distinguishing it from a STUN message whose first
two bits are 0b00 on the shared socket).

Not a `P → P`: the hypotheses are the satisfiable size bounds (channel and
length each < 2^16); the conclusions are concrete byte-level equalities and a
`Bool` recognition fact that is FALSE for out-of-range channels (a real
implication, not a tautology). -/
theorem channeldata_frames
    (ch : Nat) (payload : Bytes) (hch : ch < 65536) (hlen : payload.length < 65536) :
    -- (a) the header is the 16-bit BE channel number then the 16-bit BE length
    (channelData ch payload).take 4
      = [UInt8.ofNat (ch / 256), UInt8.ofNat (ch % 256),
         UInt8.ofNat (payload.length / 256), UInt8.ofNat (payload.length % 256)]
    -- (b) the frame decodes back to exactly (ch, payload)
    ∧ decodeChannelData (channelData ch payload) = some (ch, payload)
    -- (c) a VALID channel number (0x4000..0x7FFF) is recognised as ChannelData
    ∧ (channelNumberValid ch = true → isChannelData (channelData ch payload) = true) := by
  -- The frame in cons form (mirrors `channelData_roundtrip`'s reshape).
  have hshape : channelData ch payload =
      UInt8.ofNat (ch / 256) :: UInt8.ofNat (ch % 256) ::
      UInt8.ofNat (payload.length / 256) :: UInt8.ofNat (payload.length % 256) ::
      (payload ++ zeros (padLen payload.length)) := by
    simp [channelData, enc16, List.append_assoc]
  refine ⟨?_, channelData_roundtrip ch payload hch hlen, ?_⟩
  · rw [hshape]; rfl
  · intro hvalid
    rw [hshape]
    simp only [isChannelData, decide_eq_true_eq]
    -- first byte value: (ch / 256) % 256 = ch / 256 since ch < 65536
    have hdiv : ch / 256 < 256 := by omega
    have htoNat : (UInt8.ofNat (ch / 256)).toNat = ch / 256 :=
      -- `UInt8.toNat_ofNat` states the `OfNat.ofNat` form and reduces mod 2^8;
      -- the `_of_lt` variant discharges the modulus from `hdiv` directly.
      UInt8.toNat_ofNat_of_lt (by omega)
    rw [htoNat]
    -- channelNumberValid ch = true ⇒ 0x4000 ≤ ch ≤ 0x7FFF ⇒ 0x40 ≤ ch/256 ≤ 0x7F
    simp only [channelNumberValid, decide_eq_true_eq] at hvalid
    omega

#print axioms Turn.ChannelDataLive.channeldata_frames

/-! ## "Only the bound peer" theorem (RFC 8656 §12)

A ChannelData frame is relayed to exactly the peer bound to its channel number.
Given a live allocation `a` for `ft` whose channel `ch` is bound to `peer`:

* the frame `channelData ch payload` routes to `some (peer, payload)` — the
  verbatim payload to exactly the bound peer;
* any destination it could route to IS that peer (`dst = peer`) — no other peer
  ever receives it;
* and a frame on ANY channel `ch'` that is *not* bound (`channelPeer a ch' =
  none`) is dropped (`= none`): ChannelData follows the binding, so an unbound
  channel reflects to no one.

Not a `P → P`: the hypotheses are a live allocation, a real channel binding, and
satisfiable size bounds; the conclusions are a positive route, a uniqueness
clause, and a universally-quantified negative that forbids relay on every
unbound channel. It composes `channelSend_channelData`, `channelData_roundtrip`,
and the `channelSend`/`channelPeer` definitions. -/
theorem channeldata_only_bound_peer
    (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (ch : Nat) (peer : Endpoint) (payload : Bytes) (now : Nat)
    (hch : ch < 65536) (hlen : payload.length < 65536)
    (hlook : s.lookup ft = some a) (hlive : now < a.expiry)
    (hbound : channelPeer a ch = some peer) :
    -- the frame on the bound channel routes to exactly the bound peer
    channelSend s ft (channelData ch payload) now = some (peer, payload)
    -- and it reaches no other peer: any destination it routes to is that peer
    ∧ (∀ dst pl, channelSend s ft (channelData ch payload) now = some (dst, pl) →
        dst = peer ∧ pl = payload)
    -- and a frame on any UNBOUND channel is dropped (relayed to no one)
    ∧ (∀ (ch' : Nat), ch' < 65536 → channelPeer a ch' = none →
        channelSend s ft (channelData ch' payload) now = none) := by
  have hroute : channelSend s ft (channelData ch payload) now = some (peer, payload) :=
    channelSend_channelData s ft a ch peer payload now hlook hlive hbound hch hlen
  refine ⟨hroute, ?_, ?_⟩
  · intro dst pl hsome
    rw [hroute] at hsome
    simp only [Option.some.injEq, Prod.mk.injEq] at hsome
    exact ⟨hsome.1.symm, hsome.2.symm⟩
  · intro ch' hch' hunbound
    -- `channelData ch' payload` decodes to (ch', payload); the live allocation
    -- has no peer bound to ch', so `channelSend` returns none.
    simp [channelSend, channelData_roundtrip ch' payload hch' hlen, hlook,
      hlive, hunbound]

#print axioms Turn.ChannelDataLive.channeldata_only_bound_peer

/-! ## Byte helpers (mirror TurnPermLive/TurnLive) -/

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def ipStr (b : Bytes) : String := ".".intercalate (b.map (fun x => toString x.toNat))

/-! ## The selftest — client + relay over the byte level, one process -/

def selftest : IO UInt32 := do
  IO.println "== channeldata-live selftest : RFC 8656 §12 ChannelData relay, byte-level =="

  -- The client 5-tuple, the relayed address, and two peers (drorb-native topology).
  let epClient : Endpoint := { family := 1, port := 51000, addr := [10, 0, 0, 1] }
  let epServer : Endpoint := { family := 1, port := 3478, addr := [10, 0, 0, 254] }
  let epRelay  : Endpoint := { family := 1, port := 49152, addr := [203, 0, 113, 7] }
  let epPeerA  : Endpoint := { family := 1, port := 6000, addr := [198, 51, 100, 20] }
  let epPeerB  : Endpoint := { family := 1, port := 7000, addr := [198, 51, 100, 99] }
  let ft : FiveTuple := { client := epClient, server := epServer, proto := protoUDP }
  let payload : Bytes := [0xC0, 0xFF, 0xEE, 0x42, 0x99]  -- 5 bytes ⇒ pads to 8

  -- ── setup: allocate, then channel-bind A to 0x4001 and B to 0x4002 ──
  let s0 := allocate TurnState.empty ft epRelay 0 600
  let chA : Nat := 0x4001
  let chB : Nat := 0x4002
  let s1 := channelBind s0 ft chA epPeerA
  let s2 := channelBind s1 ft chB epPeerB
  let some a2 := s2.lookup ft
    | do IO.eprintln "server: allocation missing after channel binds"; return 1
  IO.println s!"\n-- setup: allocated relay={ipStr epRelay.addr}:{epRelay.port}, channels bound = {a2.channels.length}: A=0x{Nat.toDigits 16 chA |>.asString} B=0x{Nat.toDigits 16 chB |>.asString} --"

  -- ── 1. FRAMING: build a ChannelData frame; inspect its bytes ──
  let frameA := channelData chA payload
  let hdr := frameA.take 4
  let hdrOk := hdr == [UInt8.ofNat (chA / 256), UInt8.ofNat (chA % 256),
                       UInt8.ofNat (payload.length / 256), UInt8.ofNat (payload.length % 256)]
  let padded4 := frameA.length % 4 == 0
  let recognised := isChannelData frameA
  let validCh := channelNumberValid chA
  IO.println s!"\n-- framing (RFC 8656 §12.4: [2B channel][2B length][data][pad]) --"
  IO.println s!"ChannelData ch=0x{Nat.toDigits 16 chA |>.asString} payload={toHex payload} ({payload.length}B)"
  IO.println s!"  frame ({frameA.length}B) = {toHex frameA}"
  IO.println s!"  header[0..4] = {toHex hdr}  (BE channel ++ BE length) : {hdrOk}"
  IO.println s!"  padded to 4-byte boundary : {padded4}"
  IO.println s!"  channel 0x{Nat.toDigits 16 chA |>.asString} valid (0x4000..0x7FFF) : {validCh}"
  IO.println s!"  recognised as ChannelData (top bits 0b01, not STUN) : {recognised}"

  -- round-trip: the frame decodes back to exactly (ch, payload)
  let rtOk := decodeChannelData frameA == some (chA, payload)
  IO.println s!"  decode(frame) == (ch, payload) : {rtOk}"

  -- ── 2. RELAY: ChannelData routes to EXACTLY the bound peer ──
  let outA := channelSend s2 ft frameA 5
  let frameB := channelData chB payload
  let outB := channelSend s2 ft frameB 5
  IO.println s!"\n-- relay (ChannelData follows the channel binding, §12) --"
  match outA with
  | some (dst, pl) =>
    IO.println s!"frame on 0x{Nat.toDigits 16 chA |>.asString} -> peer {ipStr dst.addr}:{dst.port}, payload={toHex pl} (== A / verbatim : {dst == epPeerA && pl == payload})"
  | none => IO.println "frame on 0x4001 -> DROP (UNEXPECTED)"
  match outB with
  | some (dst, pl) =>
    IO.println s!"frame on 0x{Nat.toDigits 16 chB |>.asString} -> peer {ipStr dst.addr}:{dst.port}, payload={toHex pl} (== B / verbatim : {dst == epPeerB && pl == payload})"
  | none => IO.println "frame on 0x4002 -> DROP (UNEXPECTED)"
  let routeAok := outA == some (epPeerA, payload)
  let routeBok := outB == some (epPeerB, payload)
  -- cross-channel: A's frame never reaches B and vice-versa
  let noCross := (outA != some (epPeerB, payload)) && (outB != some (epPeerA, payload))

  -- ── 3. UNBOUND channel is dropped (no reflection) ──
  let chU : Nat := 0x4009  -- valid range but never bound
  let frameU := channelData chU payload
  let outU := channelSend s2 ft frameU 5
  IO.println s!"\n-- unbound channel (anti-reflector) --"
  match outU with
  | some (dst, _) => IO.println s!"frame on 0x{Nat.toDigits 16 chU |>.asString} (unbound) -> {ipStr dst.addr} (REFLECT — UNEXPECTED)"
  | none => IO.println s!"frame on 0x{Nat.toDigits 16 chU |>.asString} (unbound) -> DROP (relayed to no one)"
  let unboundDrop := outU == none

  -- ── 4. faithfulness cross-check (realizes the two theorems) ──
  IO.println "\n-- cross-check (realizes channeldata_frames + channeldata_only_bound_peer) --"
  IO.println s!"header = BE channel ++ BE length                  : {hdrOk}"
  IO.println s!"frame padded to 4-byte boundary                   : {padded4}"
  IO.println s!"valid channel recognised as ChannelData           : {validCh && recognised}"
  IO.println s!"frame round-trips to (ch, payload)                : {rtOk}"
  IO.println s!"0x4001 routes to exactly A (verbatim payload)      : {routeAok}"
  IO.println s!"0x4002 routes to exactly B (verbatim payload)      : {routeBok}"
  IO.println s!"no cross-talk (A's frame never reaches B, vv)     : {noCross}"
  IO.println s!"unbound channel dropped (relayed to no one)       : {unboundDrop}"

  if hdrOk && padded4 && validCh && recognised && rtOk && routeAok && routeBok
      && noCross && unboundDrop then do
    IO.println "\nPASS — ChannelData framing [2B ch][2B len][data][pad] round-trips;"
    IO.println "       each frame routes to EXACTLY its bound peer; unbound ⇒ drop."
    IO.println "TURN CHANNELDATA RELAY COMPLETE (drorb-native, byte-level, no reflection)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the ChannelData relay did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do IO.eprintln "usage: channeldata-live selftest"; return 1

end Turn.ChannelDataLive

def main (args : List String) : IO UInt32 := Turn.ChannelDataLive.main args
