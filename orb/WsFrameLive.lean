/-
# WsFrameLive — driving the PROVEN WebSocket frame engine over the byte level

RFC 6455 gives WebSocket a small, sharp byte-level codec. The `Ws` library
models it as sans-IO, proven Lean, layered in inert pieces:

  * `Ws.Length` — the payload-length ladder (7-bit inline / 16-bit / 64-bit
    extended), with `decodeLenField_encodeLenField` (decode inverts encode) and
    `encodeLenField_canonical` (the §5.2 shortest-encoding rule);
  * `Ws.Mask` — the rotating 4-byte XOR mask (§5.3), with `applyMask_involution`
    (unmask ∘ mask = id) and `applyMask_length` (masking preserves length) —
    this is XOR, not cryptography;
  * `Ws.Frame` — the decoded logical frame (FIN, classified opcode, unmasked
    payload) and its control-frame well-formedness (§5.5);
  * `Ws.Reassembly` — the fragmentation FSM (§5.4), with `assemble_join_message`
    (a delivered message is the in-order concatenation of its fragments).

Those pieces are proven but inert beyond the frames the deployed WebSocket path
already handles. This executable is the wiring: a self-delimiting **wire frame**
codec assembled directly on top of the proven length ladder and the proven mask
(`encodeFrame` / `decodeFrame`), and a `selftest` that drives the WHOLE chain —
encode a masked frame, decode it back, mask/unmask a payload, reassemble a
fragmented message — over the byte level in one process, with **no crypto
whatsoever** (the mask is a per-octet XOR), so it runs under `lake env lean
--run`.

## Honesty / realization boundary (the NetmapLive / DiscoLive discipline)

This is **drorb-native** and **pure**: `encodeFrame` and `decodeFrame` are our
own spec-conformant peers speaking the RFC 6455 frame layout, built from the
proven ladder + mask; the reassembler is the proven `Ws.Reassembly.step`. No
socket, no FFI call — the reused C objects are linked only to satisfy the shared
executable link line, never invoked (masking is XOR, not cryptography, so the
selftest runs entirely in the pure Lean interpreter). Everything
structural/codec here is the proven Lean; the gap the selftest discharges by
construction (not by proof) is that this exe faithfully CALLS the proven Lean
functions on real bytes. The faithfulness of the encode→decode→unmask chain and
the reassembly fold is proven below as `ws_frame_faithful` (frame round-trip +
mask involution + reassembly-equals-the-message). Deliberately out of scope: the
opening HTTP handshake (§4) and permessage-deflate (RFC 7692) — the named
residual.

Usage:
  ws-frame-live selftest
-/
import Ws.Length
import Ws.Mask
import Ws.Frame
import Ws.Reassembly

namespace WsFrameLive

open Ws
open Ws.Reassembly

/-! ## §1  The frame layout on the wire (RFC 6455 §5.2), over the proven pieces

A frame is `[b0, b1] ++ ext ++ (maskKey?) ++ payload?`:

  * `b0` = FIN bit (0x80) ‖ opcode nibble (RSV modeled zero);
  * `b1` = MASK bit (0x80) ‖ the 7-bit length marker from the proven ladder;
  * `ext` = the extended length bytes the proven ladder appends (0 / 2 / 8);
  * when masked: a 4-byte masking key, then the payload transformed by the
    proven `applyMask` (a rotating XOR — no cryptography).

The decoder reads the marker, uses the *same proven `decodeLenField`* to recover
the length, splits off the key, and applies the proven `applyMask` again to
recover the plaintext (unmask = mask, by `applyMask_involution`). -/

/-- The low-nibble opcode value (RFC 6455 §5.2). Inverse of `Opcode.ofNat` on the
six defined opcodes. -/
def opcodeNibble : Opcode → Nat
  | .continuation => 0x0
  | .text         => 0x1
  | .binary       => 0x2
  | .close        => 0x8
  | .ping         => 0x9
  | .pong         => 0xA
  | .reserved n   => n

/-- The number of extended-length bytes a 7-bit marker introduces: none inline,
two for `126`, eight for `127`. Mirrors the proven `lenExt` length. -/
def extBytesLen (marker : Nat) : Nat :=
  if marker ≤ 125 then 0 else if marker = 126 then 2 else 8

/-- Encode a logical `Frame` to the RFC 6455 wire layout. `masked` selects the
client-to-server masking direction; `key` is the 4-byte masking key (used only
when `masked`). Built from the proven length ladder (`encodeLenField`) and the
proven mask (`applyMask`). -/
def encodeFrame (key : Bytes) (masked : Bool) (f : Frame) : Bytes :=
  let b0 := UInt8.ofNat (f.fin.toNat * 128 + opcodeNibble f.opcode)
  let b1 := UInt8.ofNat (masked.toNat * 128 + lenMarker f.payload.length)
  let body := if masked then key ++ applyMask key f.payload else f.payload
  b0 :: b1 :: (lenExt f.payload.length ++ body)

/-- Decode one RFC 6455 wire frame, returning the logical `Frame` (payload
already unmasked) and the trailing bytes. Uses the proven `decodeLenField` to
read the length and the proven `applyMask` to unmask. -/
def decodeFrame : Bytes → Option (Frame × Bytes)
  | b0 :: b1 :: rest =>
    let fin    := decide (128 ≤ b0.toNat)
    let op     := Opcode.ofNat (b0.toNat % 16)
    let masked := decide (128 ≤ b1.toNat)
    let marker := b1.toNat % 128
    let el     := extBytesLen marker
    let ext    := rest.take el
    let rest1  := rest.drop el
    let plen   := decodeLenField marker ext
    let key    := if masked then rest1.take 4 else []
    let rest2  := if masked then rest1.drop 4 else rest1
    let raw    := rest2.take plen
    let after  := rest2.drop plen
    let payload := if masked then applyMask key raw else raw
    some ({ fin := fin, opcode := op, payload := payload }, after)
  | _ => none

/-! ## §2  Supporting arithmetic on the header bytes -/

/-- The 7-bit length marker never overflows the low seven bits. -/
theorem lenMarker_le (n : Nat) : lenMarker n ≤ 127 := by
  unfold lenMarker
  by_cases h1 : n < 126
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : n < 2 ^ 16
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

/-- The decoder's extended-length count matches exactly the bytes the proven
encoder appends: `extBytesLen (lenMarker n) = (lenExt n).length`. -/
theorem extBytesLen_lenMarker (n : Nat) :
    extBytesLen (lenMarker n) = (lenExt n).length := by
  by_cases h1 : n < 126
  · have hm : lenMarker n = n := by unfold lenMarker; rw [if_pos h1]
    have he : lenExt n = [] := by unfold lenExt; rw [if_pos h1]
    rw [hm, he]
    show extBytesLen n = 0
    unfold extBytesLen
    rw [if_pos (show n ≤ 125 by omega)]
  · by_cases h2 : n < 2 ^ 16
    · have hm : lenMarker n = 126 := by unfold lenMarker; rw [if_neg h1, if_pos h2]
      have he : lenExt n = toBE16 n := by unfold lenExt; rw [if_neg h1, if_pos h2]
      rw [hm, he, toBE16_length]; decide
    · have hm : lenMarker n = 127 := by unfold lenMarker; rw [if_neg h1, if_neg h2]
      have he : lenExt n = toBE64 n := by unfold lenExt; rw [if_neg h1, if_neg h2]
      rw [hm, he, toBE64_length]; decide

/-! ## §3  The frame round-trip over the byte level (mask included)

The workhorse: for any masking key of length 4, any frame whose payload fits
`2⁶⁴` and whose opcode is one of the six defined ones, encoding to the wire then
decoding recovers the frame verbatim and leaves the trailing bytes untouched.
The two opcode hypotheses (`opcodeNibble f.opcode < 16` and the `Opcode.ofNat`
round-trip) hold for every defined opcode — the selftest witnesses them on
`text`/`binary`/`ping`/… — so this is not vacuous. -/
theorem decodeFrame_encodeFrame (key : Bytes) (f : Frame) (t : Bytes)
    (hk : key.length = 4)
    (hlen : f.payload.length < 2 ^ 64)
    (hnib : opcodeNibble f.opcode < 16)
    (hop : Opcode.ofNat (opcodeNibble f.opcode) = f.opcode) :
    decodeFrame (encodeFrame key true f ++ t) = some (f, t) := by
  -- byte 0 arithmetic (FIN bit ‖ opcode nibble)
  have hb0nat : (UInt8.ofNat (f.fin.toNat * 128 + opcodeNibble f.opcode)).toNat
      = f.fin.toNat * 128 + opcodeNibble f.opcode := by
    -- `UInt8.toNat_ofNat` is stated for the `OfNat.ofNat` form and leaves a `% 2^8`;
    -- `_of_lt` takes the in-range side condition directly.
    have hlt : f.fin.toNat * 128 + opcodeNibble f.opcode < 256 := by
      cases f.fin <;> simp <;> omega
    exact UInt8.toNat_ofNat_of_lt hlt
  have hfin : decide (128 ≤ (UInt8.ofNat (f.fin.toNat * 128 + opcodeNibble f.opcode)).toNat)
      = f.fin := by
    rw [hb0nat]; cases f.fin <;> simp <;> omega
  have hopdec : Opcode.ofNat
      ((UInt8.ofNat (f.fin.toNat * 128 + opcodeNibble f.opcode)).toNat % 16) = f.opcode := by
    rw [hb0nat]
    have hm : (f.fin.toNat * 128 + opcodeNibble f.opcode) % 16 = opcodeNibble f.opcode := by
      cases f.fin <;> simp <;> omega
    rw [hm]; exact hop
  -- byte 1 arithmetic (MASK bit ‖ 7-bit length marker)
  have hmle : lenMarker f.payload.length ≤ 127 := lenMarker_le f.payload.length
  have hb1nat : (UInt8.ofNat (128 + lenMarker f.payload.length)).toNat
      = 128 + lenMarker f.payload.length := by
    have hlt : 128 + lenMarker f.payload.length < 256 := by omega
    exact UInt8.toNat_ofNat_of_lt hlt
  have hmask : decide (128 ≤ (UInt8.ofNat (128 + lenMarker f.payload.length)).toNat) = true := by
    rw [hb1nat]; simp only [decide_eq_true_eq]; omega
  have hmarkerdec : (UInt8.ofNat (128 + lenMarker f.payload.length)).toNat % 128
      = lenMarker f.payload.length := by
    rw [hb1nat]; omega
  -- the tail after the two header bytes, fully left-associated
  have happ : encodeFrame key true f ++ t
      = (UInt8.ofNat (f.fin.toNat * 128 + opcodeNibble f.opcode))
        :: (UInt8.ofNat (128 + lenMarker f.payload.length))
        :: (lenExt f.payload.length ++ key ++ applyMask key f.payload ++ t) := by
    simp [encodeFrame, List.append_assoc]
  rw [happ]
  simp only [decodeFrame, hfin, hopdec, hmask, hmarkerdec]
  -- split the extended bytes
  have hel : extBytesLen (lenMarker f.payload.length) = (lenExt f.payload.length).length :=
    extBytesLen_lenMarker f.payload.length
  rw [hel]
  have htakeext : (lenExt f.payload.length ++ key ++ applyMask key f.payload ++ t).take
      (lenExt f.payload.length).length = lenExt f.payload.length := by
    rw [List.append_assoc, List.append_assoc, List.take_left]
  have hdropext : (lenExt f.payload.length ++ key ++ applyMask key f.payload ++ t).drop
      (lenExt f.payload.length).length = key ++ applyMask key f.payload ++ t := by
    rw [List.append_assoc, List.append_assoc, List.drop_left, ← List.append_assoc]
  rw [htakeext, hdropext]
  -- the length decodes back via the proven ladder
  have hplen : decodeLenField (lenMarker f.payload.length) (lenExt f.payload.length)
      = f.payload.length := decodeLenField_encodeLenField f.payload.length hlen
  rw [hplen]
  -- split the masking key (length 4)
  have htakekey : (key ++ applyMask key f.payload ++ t).take 4 = key := by
    rw [← hk, List.append_assoc, List.take_left]
  have hdropkey : (key ++ applyMask key f.payload ++ t).drop 4
      = applyMask key f.payload ++ t := by
    rw [← hk, List.append_assoc, List.drop_left]
  simp only [if_true, htakekey, hdropkey]
  -- split the masked payload (length preserved by applyMask)
  have hmasklen : (applyMask key f.payload).length = f.payload.length :=
    applyMask_length key f.payload
  have htakepay : (applyMask key f.payload ++ t).take f.payload.length
      = applyMask key f.payload := by
    rw [← hmasklen, List.take_left]
  have hdroppay : (applyMask key f.payload ++ t).drop f.payload.length = t := by
    rw [← hmasklen, List.drop_left]
  rw [htakepay, hdroppay, applyMask_involution]

/-! ## §4  The faithfulness theorem

`ws_frame_faithful` bundles the three realized guarantees, each discharged by a
proven law:

  1. **frame round-trip** over the byte level — the RFC 6455 wire codec built on
     the proven length ladder + mask recovers every defined-opcode frame
     (`decodeFrame_encodeFrame`);
  2. **mask involution** — unmasking is exactly masking again with the same key
     (`Ws.applyMask_involution`), the XOR self-inverse the receiver runs;
  3. **reassembly = the message** — feeding a fragmented sequence through the
     proven `Ws.Reassembly.step` delivers exactly the in-order concatenation of
     every fragment payload (`Ws.Reassembly.assemble_join_message`).

None of the three conjuncts is a `P → P`: each is a real equation over its
universally quantified inputs (arbitrary keys, frames, payloads, trailing bytes,
opcodes, fragment runs), and the selftest below witnesses each on concrete
bytes. -/
theorem ws_frame_faithful :
    -- (1) frame round-trip over the byte level
    (∀ (key : Bytes) (f : Frame) (t : Bytes),
        key.length = 4 → f.payload.length < 2 ^ 64 →
        opcodeNibble f.opcode < 16 → Opcode.ofNat (opcodeNibble f.opcode) = f.opcode →
        decodeFrame (encodeFrame key true f ++ t) = some (f, t))
    ∧ -- (2) mask involution (unmask ∘ mask = id)
    (∀ (key p : Bytes), applyMask key (applyMask key p) = p)
    ∧ -- (3) reassembly delivers the in-order concatenation of the fragments
    (∀ (op : Opcode) (initial : Bytes) (mids : List Bytes) (final : Bytes),
        Reassembly.step
            (.assembling (Reassembly.runAbsorb { opcode := op, acc := initial } mids))
            { fin := true, opcode := .continuation, payload := final }
          = (.idle, .message op (initial ++ mids.flatten ++ final))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro key f t hk hlen hnib hop
    exact decodeFrame_encodeFrame key f t hk hlen hnib hop
  · intro key p
    exact applyMask_involution key p
  · intro op initial mids final
    exact assemble_join_message op initial mids final

/-! ## §5  Byte helpers (pure) -/

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-- Render a byte list that is valid UTF-8 as text, else hex. -/
def textOrHex (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD (toHex b)

/-- Drive a list of frames through the proven reassembler, collecting delivered
messages (data messages and control frames), starting from `idle`. -/
def runReassembly (frames : List Frame) : List Output :=
  let rec go (st : State) : List Frame → List Output
    | [] => []
    | f :: fs =>
      let (st', out) := Reassembly.step st f
      match out with
      | .absorbed => go st' fs
      | o => o :: go st' fs
  go .idle frames

/-! ## §6  The selftest — the WS frame engine over the byte level, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== ws-frame-live selftest : WebSocket frame engine, byte-level, NO crypto (XOR mask) =="

  -- ── (1) frame round-trip: a masked client-to-server text frame ──
  let key : Bytes := [0xDE, 0xAD, 0xBE, 0xEF]
  let msg : Bytes := "hello, websocket".toUTF8.toList
  let f : Frame := { fin := true, opcode := .text, payload := msg }
  let wire := encodeFrame key true f
  IO.println s!"\n-- (1) masked text frame encode/decode --"
  IO.println s!"payload                : {textOrHex f.payload} ({f.payload.length}B)"
  IO.println s!"wire bytes             : {wire.length}B  {toHex (wire.take 12)}…"
  IO.println s!"masked payload on wire : {toHex (wire.drop 6)}  (XOR-masked, not plaintext)"
  let some (decoded, rest) := decodeFrame wire
    | do IO.eprintln "decodeFrame FAILED"; return 1
  let rtOk := (decoded == f) && rest.isEmpty
  IO.println s!"decodeFrame∘encodeFrame == frame (wire round-trip realized) : {rtOk}"
  IO.println s!"decoded payload        : {textOrHex decoded.payload}"
  if !rtOk then do IO.eprintln "frame did NOT round-trip"; return 1

  -- also drive a masked binary frame with a longer payload (exercises the 16-bit
  -- length rung of the proven ladder) and an unmasked control (ping) frame
  let bigPayload : Bytes := List.replicate 300 0x41
  let bf : Frame := { fin := true, opcode := .binary, payload := bigPayload }
  let some (dbf, _) := decodeFrame (encodeFrame key true bf)
    | do IO.eprintln "decodeFrame FAILED (binary/16-bit rung)"; return 1
  let bigOk := dbf == bf
  let pf : Frame := { fin := true, opcode := .ping, payload := [0x70, 0x69] }
  let some (dpf, _) := decodeFrame (encodeFrame [] false pf)
    | do IO.eprintln "decodeFrame FAILED (unmasked ping)"; return 1
  let pingOk := dpf == pf
  IO.println s!"binary/300B (16-bit length rung) round-trips : {bigOk}"
  IO.println s!"unmasked ping control frame round-trips      : {pingOk}"

  -- ── (2) mask involution: unmask ∘ mask = id, on concrete bytes ──
  let masked := applyMask key msg
  let unmasked := applyMask key masked
  let maskInv := unmasked == msg
  let maskChanged := masked != msg
  IO.println s!"\n-- (2) mask (rotating XOR) involution --"
  IO.println s!"applyMask changed the bytes           : {maskChanged}"
  IO.println s!"applyMask∘applyMask == id (unmask=mask): {maskInv}"
  if !(maskInv && maskChanged) then do IO.eprintln "mask involution FAILED"; return 1

  -- ── (3) fragmented-message reassembly = in-order concatenation ──
  -- a text message split as: text(fin=0) ‖ continuation(fin=0) ‖ continuation(fin=1),
  -- with a ping control frame interleaved (must not disturb reassembly, §5.4).
  let frag0 : Bytes := "Hel".toUTF8.toList
  let frag1 : Bytes := "lo, wor".toUTF8.toList
  let frag2 : Bytes := "ld!".toUTF8.toList
  let frames : List Frame :=
    [ { fin := false, opcode := .text,         payload := frag0 },
      { fin := true,  opcode := .ping,         payload := [0x01] },   -- interleaved control
      { fin := false, opcode := .continuation, payload := frag1 },
      { fin := true,  opcode := .continuation, payload := frag2 } ]
  let outs := runReassembly frames
  let expected : Bytes := frag0 ++ frag1 ++ frag2
  -- find the delivered data message
  let delivered := outs.filterMap (fun o => match o with
    | .message _ p => some p
    | _ => none)
  let reassembleOk := delivered == [expected]
  -- the control frame was delivered as-is, out of band
  let controlSeen := outs.any (fun o => match o with | .control _ => true | _ => false)
  -- cross-check against the model fold `assemble_join_message`:
  --   runAbsorb {text, frag0} [frag1] then a final frag2 == message (frag0++frag1++frag2)
  let modelMid := Reassembly.step
      (.assembling (Reassembly.runAbsorb { opcode := .text, acc := frag0 } [frag1]))
      { fin := true, opcode := .continuation, payload := frag2 }
  let modelOk := modelMid == (.idle, .message .text expected)
  IO.println s!"\n-- (3) fragmentation reassembly (§5.4) --"
  IO.println s!"fragments              : {frames.map (fun fr => textOrHex fr.payload)}"
  IO.println s!"delivered message      : {delivered.map textOrHex}"
  IO.println s!"expected concatenation : [{textOrHex expected}]"
  IO.println s!"reassembly == in-order concat (realizes assemble_join_message) : {reassembleOk}"
  IO.println s!"interleaved control frame delivered out-of-band               : {controlSeen}"
  IO.println s!"model fold (assemble_join_message) agrees                     : {modelOk}"

  if rtOk && bigOk && pingOk && maskInv && maskChanged && reassembleOk && controlSeen && modelOk then do
    IO.println "\nPASS — frame encoded/decoded over the byte level; mask is a self-inverse XOR;"
    IO.println "       a fragmented message reassembles to the in-order concatenation of its parts."
    IO.println "WS FRAME ENGINE LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+mask+reassembly)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the WS frame pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: ws-frame-live selftest"
    return 1

end WsFrameLive

def main (args : List String) : IO UInt32 := WsFrameLive.main args
