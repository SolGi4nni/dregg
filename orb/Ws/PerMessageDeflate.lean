import Ws.Frame
import Deflate

/-!
# WebSocket permessage-deflate (RFC 7692) — the compression extension

RFC 6455 frames carry a reserved bit `RSV1` that carries no meaning without a
negotiated extension. The permessage-deflate extension (RFC 7692) gives it one:
on the **first** frame of a message, `RSV1 = 1` marks the message payload as
DEFLATE-compressed (RFC 1951). This module models the receive side — the
dangerous, decompressing direction a server runs on inbound frames — on top of
the bounded `Deflate` inflate model, and proves the two properties that make the
extension correct and safe:

  * **Round-trip (RFC 7692 §7.2).** The wire transform is: compress with DEFLATE
    ending in an empty stored block (the `Z_SYNC_FLUSH` marker), then **remove the
    trailing four octets `00 00 FF FF`** (§7.2.1); the receiver **appends those
    four octets back** and inflates (§7.2.2). `ws_pmd_roundtrip` proves a frame
    carrying `RSV1 = 1` and a payload so produced decompresses to the original
    message — the trailing-octet handling is load-bearing (without the appended
    tail the reconstructed stream is truncated), and the receiver's branch on
    `RSV1` is load-bearing (an `RSV1 = 0` frame is passed through uncompressed).

  * **Context takeover (RFC 7692 §7.1.1.1).** With `no_context_takeover`
    negotiated, the LZ77 sliding window (the compression *context*) is **reset per
    message**: message *N* decompresses independently of every prior message.
    `ws_pmd_context_takeover` proves this as window-independence — the decode of a
    compressed message is the original message *regardless of the prior window*,
    because the reset discards it. The companion `pmd_ctxTakeover_uses_window`
    shows the contrast: with context takeover the prior window is *not* discarded,
    so the two modes are genuinely different (the reset is observable).

The compressed messages here are DEFLATE **stored** blocks (RFC 1951 §3.2.4): the
sync-flush framing, the `RSV1` flag, and the trailing-octet transform are the
permessage-deflate-specific machinery, and they compose with the independently
proven `Deflate` inflate. The receive driver `pmdInflateAux` terminates on a
final block, on input exhaustion after a complete block (the streaming/sync-flush
semantics — inflate consumes exactly the message), or on a typed error; it is a
`def` on explicit fuel, hence total.
-/

namespace Ws
namespace Pmd

open Deflate (Bits Cfg Err bytesToBits byteBits u16le align takeBitsLE takeBytes
  inflateStored pushBounded decodeBody buildDynamic fixedLitTree fixedDistTree)

/-! ## The wire transform (RFC 7692 §7.2.1) -/

/-- A non-final DEFLATE **stored** block (RFC 1951 §3.2.4) carrying `x`: the header
octet `0x00` (`BFINAL = 0`, `BTYPE = 00`, 5 pad bits), then `LEN`, `NLEN = ~LEN`,
then the literal bytes. (`Deflate.deflateStored` uses `0x01` — `BFINAL = 1`; a
permessage-deflate message body is non-final, its end marked by the sync flush.) -/
def storedBody (x : Bytes) : Bytes :=
  0x00 :: (u16le x.length ++ u16le (65535 - x.length) ++ x)

/-- The empty non-final stored block a `Z_SYNC_FLUSH` emits: bytes `00 00 00 FF FF`
(`storedBody []`). Its trailing four octets `00 00 FF FF` are exactly what §7.2.1
strips on the wire and §7.2.2 restores. -/
theorem storedBody_nil : storedBody [] = [0x00, 0x00, 0x00, 0xFF, 0xFF] := by decide

/-- The four octets the sync flush leaves and §7.2.2 re-appends before inflating. -/
def syncTail : Bytes := [0x00, 0x00, 0xFF, 0xFF]

/-- **Compress (RFC 7692 §7.2.1).** Emit `x` as one non-final stored block, append
the sync-flush empty stored block, then remove the trailing four octets
`00 00 FF FF`. Equivalently: the message body followed by the single retained
header octet of the empty block. -/
def compress (x : Bytes) : Bytes := storedBody x ++ [0x00]

/-- **Decompress (RFC 7692 §7.2.2).** Re-append `00 00 FF FF`, then inflate the
reconstructed DEFLATE stream from the given window. -/
def deflateInput (payload : Bytes) : Bytes := payload ++ syncTail

/-- The wire transform is a clean inverse of the framing: appending the sync tail
to a compressed message reconstructs the message body followed by the empty
stored block. -/
theorem deflateInput_compress (x : Bytes) :
    deflateInput (compress x) = storedBody x ++ storedBody [] := by
  simp only [deflateInput, compress, syncTail, storedBody_nil, List.append_assoc,
    List.cons_append, List.nil_append]

/-! ## The receive driver -/

/-- Decompress DEFLATE blocks until a final block, a typed error, or input
exhaustion after a complete block — the streaming (sync-flush) end-of-message
signal (RFC 7692 §7.2.2: the appended empty stored block flushes and the input is
consumed). `fuel` bounds the block count; total by construction. -/
def pmdInflateAux (cfg : Cfg) : Nat → Array UInt8 → Bits → Array UInt8 × Option Err
  | 0, out, _ => (out, some .truncated)
  | fuel + 1, out, bits =>
    match takeBitsLE 1 bits with
    | none => (out, none)                       -- byte-aligned pad exhausted: message complete
    | some (bfinal, b1) =>
      match takeBitsLE 2 b1 with
      | none => (out, some .truncated)
      | some (btype, b2) =>
        if btype == 0 then
          match inflateStored cfg out b2 with
          | (o, _, some e) => (o, some e)
          | (o, b3, none) =>
            if bfinal == 1 then (o, none)
            else if b3.isEmpty then (o, none)   -- sync-flush terminator consumed
            else pmdInflateAux cfg fuel o b3
        else if btype == 1 then
          match decodeBody cfg fixedLitTree fixedDistTree (b2.length + 1) out b2 with
          | (o, _, some e) => (o, some e)
          | (o, b3, none) =>
            if bfinal == 1 then (o, none)
            else if b3.isEmpty then (o, none)
            else pmdInflateAux cfg fuel o b3
        else if btype == 2 then
          match buildDynamic b2 with
          | none => (out, some .badHuffman)
          | some (lit, dist, b3) =>
            match decodeBody cfg lit dist (b3.length + 1) out b3 with
            | (o, _, some e) => (o, some e)
            | (o, b4, none) =>
              if bfinal == 1 then (o, none)
              else if b4.isEmpty then (o, none)
              else pmdInflateAux cfg fuel o b4
        else (out, some .badBlockType)

/-- Inflate a reconstructed permessage-deflate stream from an initial output
window (the LZ77 context). Total (a `def` on explicit fuel). -/
def pmdInflate (cfg : Cfg) (window : Array UInt8) (input : Bytes) : Array UInt8 × Option Err :=
  let bits := bytesToBits input
  pmdInflateAux cfg (bits.length + 1) window bits

/-! ## Stored-block inflate with a suffix (generalizes `Deflate.inflateStored_deflate`)

`Deflate.inflateStored_deflate` proves the stored-block reader inverts the writer
from an empty output and with no trailing bits. The permessage-deflate driver
needs the same fact with (a) a nonempty starting window and (b) trailing bits (the
next block), so it is reproved here from the `Deflate` round-trip lemmas — all of
which are exported and reused, not reimplemented.
-/

/-- `inflateStored` on a stored block's post-header bits (`[false×5]` pad, then the
`LEN`/`NLEN`/literal encoding) followed by any whole-byte suffix `s`: it recovers
the literal bytes, appends them to the window, and returns `s` untouched. -/
theorem inflateStored_suffix (cfg : Cfg) (out : Array UInt8) (x : Bytes) (s : Bits)
    (hlen : x.length < 65536) (hcap : out.size + x.length ≤ cfg.maxOut)
    (hs : s.length % 8 = 0) :
    ∃ o : Array UInt8,
      inflateStored cfg out
        ([false, false, false, false, false] ++
          (bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x) ++ s))
        = (o, s, none) ∧ o.toList = out.toList ++ x := by
  have hnlen : (65535 - x.length) < 65536 := by omega
  -- alignment: the 5 pad bits sit atop a whole-byte body+suffix, so `align` drops exactly them.
  have hbodylen :
      (bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x)).length = 8 * (4 + x.length) := by
    rw [Deflate.bytesToBits_length]
    simp only [List.length_append, Deflate.u16le, List.length_cons, List.length_nil]
  have hlen8 :
      ([false, false, false, false, false] ++
        (bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x) ++ s)).length % 8 = 5 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hbodylen]
    omega
  have halign :
      align ([false, false, false, false, false] ++
        (bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x) ++ s))
        = bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x) ++ s := by
    simp only [align, hlen8]
    rw [show (5 : Nat) = ([false, false, false, false, false] : List Bool).length from rfl]
    exact List.drop_left
  unfold inflateStored
  rw [halign]
  simp only [Deflate.bytesToBits_append, List.append_assoc]
  rw [Deflate.u16le_read x.length _ hlen]
  simp only
  rw [Deflate.u16le_read (65535 - x.length) _ hnlen]
  simp only
  have hsum : x.length + (65535 - x.length) = 65535 := by omega
  simp only [hsum, bne_self_eq_false, if_false]
  rw [Deflate.takeBytes_bytesToBits x s]
  simp only
  have hpb := Deflate.pushBounded_all cfg.maxOut x out (by omega)
  cases hp : pushBounded cfg.maxOut out x with
  | none => rw [hp] at hpb; simp at hpb
  | some o2 =>
    rw [hp] at hpb
    exact ⟨o2, rfl, by simpa using hpb⟩

/-! ## The driver over a single stored block -/

/-- One stored-block step of the driver: from a byte-aligned `BFINAL = 0`,
`BTYPE = 00` header (`byteBits 0x00 = [false×8]`) over a stored block carrying `x`
then a suffix `T`, the driver appends `x` to the window and either finishes (if the
suffix is empty — the sync-flush terminator was the whole rest) or recurses on `T`. -/
theorem pmdInflateAux_storedStep (cfg : Cfg) (fuel : Nat) (out : Array UInt8)
    (x : Bytes) (T : Bits)
    (hlen : x.length < 65536) (hcap : out.size + x.length ≤ cfg.maxOut)
    (hT : T.length % 8 = 0) :
    ∃ o : Array UInt8, o.toList = out.toList ++ x ∧
      pmdInflateAux cfg (fuel + 1) out
        (bytesToBits (storedBody x) ++ T)
        = (if T.isEmpty then (o, none) else pmdInflateAux cfg fuel o T) := by
  obtain ⟨o, hst, hox⟩ := inflateStored_suffix cfg out x T hlen hcap hT
  refine ⟨o, hox, ?_⟩
  have hbits : bytesToBits (storedBody x) ++ T
      = false :: false :: false ::
          ([false, false, false, false, false] ++
            (bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x) ++ T)) := by
    show (byteBits 0x00 ++
      bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x)) ++ T = _
    rw [show byteBits 0x00
        = [false, false, false, false, false, false, false, false] from by decide]
    rfl
  rw [hbits]
  simp only [pmdInflateAux, takeBitsLE, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.add_zero, Bool.false_eq_true, if_false, Nat.reduceBEq, reduceIte]
  rw [hst]

/-! ## The round-trip theorem (RFC 7692 §7.2) -/

/-- **Decompress recovers the message.** Inflating the reconstructed stream of a
compressed message `x` — the message body's stored block followed by the appended
sync-flush empty block — returns exactly `x`, from any window whose size fits under
the ceiling. This is the DEFLATE-level heart of the extension round-trip; both the
data block and the terminator block are discharged through `pmdInflateAux_storedStep`. -/
theorem pmdInflate_two_stored (cfg : Cfg) (window : Array UInt8) (x : Bytes) (m : Nat)
    (hlen : x.length < 65536) (hcap : window.size + x.length ≤ cfg.maxOut) :
    pmdInflateAux cfg (m + 1 + 1) window
      (bytesToBits (storedBody x) ++ bytesToBits (storedBody []))
      = (window ++ x.toArray, none) := by
  have hTdata : (bytesToBits (storedBody [])).length % 8 = 0 := by
    rw [Deflate.bytesToBits_length]; omega
  have hTnil : ([] : Bits).length % 8 = 0 := by simp
  -- step 1: the data block; the empty-block suffix is nonempty, so the driver recurses
  obtain ⟨o1, ho1, hstep1⟩ :=
    pmdInflateAux_storedStep cfg (m + 1) window x (bytesToBits (storedBody [])) hlen hcap hTdata
  rw [hstep1, if_neg (by decide : ¬ (bytesToBits (storedBody [])).isEmpty = true)]
  -- o1's size, from its byte list
  have ho1s : o1.size = window.size + x.length := by
    have h := congrArg List.length ho1
    rw [Array.length_toList, List.length_append, Array.length_toList] at h
    exact h
  -- step 2: the empty terminator block; the suffix is now empty, so the driver finishes
  have hcap2 : o1.size + ([] : Bytes).length ≤ cfg.maxOut := by
    simp only [List.length_nil, Nat.add_zero]; omega
  obtain ⟨o2, ho2, hstep2⟩ :=
    pmdInflateAux_storedStep cfg m o1 [] ([] : Bits) (by simp) hcap2 hTnil
  have happ : bytesToBits (storedBody ([] : Bytes)) ++ ([] : Bits) = bytesToBits (storedBody []) := by
    simp
  rw [happ] at hstep2
  rw [hstep2, if_pos (by decide : ([] : Bits).isEmpty = true)]
  -- o2.toList = window.toList ++ x  ⇒  o2 = window ++ x.toArray
  have hlist : o2.toList = (window ++ x.toArray).toList := by
    rw [ho2, ho1]
    simp [Array.toList_append, List.toList_toArray, List.append_nil]
  rw [Array.toList_inj.mp hlist]

/-- **Decompress recovers the message.** Inflating the reconstructed stream of a
compressed message `x` — the message body's stored block followed by the appended
sync-flush empty block — returns exactly `x`, from any window whose size fits under
the ceiling. This is the DEFLATE-level heart of the extension round-trip; both the
data block and the terminator block are discharged through `pmdInflateAux_storedStep`. -/
theorem pmdInflate_roundtrip (cfg : Cfg) (window : Array UInt8) (x : Bytes)
    (hlen : x.length < 65536) (hcap : window.size + x.length ≤ cfg.maxOut) :
    pmdInflate cfg window (deflateInput (compress x)) = (window ++ x.toArray, none) := by
  rw [deflateInput_compress]
  unfold pmdInflate
  simp only [Deflate.bytesToBits_append]
  rw [show (bytesToBits (storedBody x) ++ bytesToBits (storedBody [])).length + 1
      = ((bytesToBits (storedBody x) ++ bytesToBits (storedBody [])).length - 1) + 1 + 1 from by
        have h1 : 1 ≤ (bytesToBits (storedBody x) ++ bytesToBits (storedBody [])).length := by
          simp only [List.length_append, Deflate.bytesToBits_length, storedBody, List.length_cons]
          omega
        omega]
  exact pmdInflate_two_stored cfg window x _ hlen hcap

/-! ## The permessage-deflate frame (RFC 7692 §6) -/

/-- A permessage-deflate frame: the RFC 6455 fields plus the `RSV1` compression
flag the extension defines (RFC 7692 §6). (`Ws.Frame` deliberately drops the RSV
bits; the extension gives `RSV1` meaning, so it is retained here.) -/
structure Frame where
  fin : Bool
  /-- `RSV1` — set on the first frame of a compressed message (RFC 7692 §6). -/
  rsv1 : Bool
  opcode : Opcode
  payload : Bytes
deriving Repr, DecidableEq

/-- **Send side.** Compress `x` and emit a data frame with `RSV1 = 1`. -/
def compressFrame (op : Opcode) (x : Bytes) : Frame :=
  { fin := true, rsv1 := true, opcode := op, payload := compress x }

/-- **Receive side.** If `RSV1 = 1`, re-append the sync tail and inflate from the
window; otherwise (RFC 7692 §6: no extension bit) pass the payload through
uncompressed. The branch on `RSV1` is the extension's dispatch. -/
def recvFrame (cfg : Cfg) (window : Array UInt8) (f : Frame) : Array UInt8 × Option Err :=
  if f.rsv1 then pmdInflate cfg window (deflateInput f.payload)
  else (f.payload.toArray, none)

/-- **`ws_pmd_roundtrip` — RFC 7692 §7.2.** A permessage-deflate frame produced by
`compressFrame` carries `RSV1 = 1`, and the receiver — which branches on that
`RSV1` bit and re-appends the trailing `00 00 FF FF` before inflating — recovers
exactly the original message. Both the `RSV1` dispatch and the trailing-octet
handling are load-bearing: the send frame is uncompressed-flagged nowhere, and
`deflateInput` is the §7.2.2 append. -/
theorem ws_pmd_roundtrip (cfg : Cfg) (op : Opcode) (x : Bytes)
    (hlen : x.length < 65536) (hcap : x.length ≤ cfg.maxOut) :
    (compressFrame op x).rsv1 = true ∧
      recvFrame cfg #[] (compressFrame op x) = (x.toArray, none) := by
  refine ⟨rfl, ?_⟩
  simp only [recvFrame, compressFrame, if_pos]
  rw [pmdInflate_roundtrip cfg #[] x hlen (by simpa using hcap)]
  simp

/-! ## Context takeover (RFC 7692 §7.1.1.1) -/

/-- A receive endpoint with the `no_context_takeover` bit: when set, the LZ77
window is reset (dropped) before each message; when clear, the running window is
carried into the next message (RFC 7692 §7.1.1.1). -/
structure RecvState where
  /-- `no_context_takeover` negotiated for this direction. -/
  noContextTakeover : Bool
  /-- The carried window (the running decompressed context). -/
  window : Array UInt8

/-- Decompress one message under the endpoint's context-takeover policy: reset the
window to empty when `no_context_takeover` is set, else start from the carried
window. -/
def recvMessage (cfg : Cfg) (st : RecvState) (payload : Bytes) : Array UInt8 × Option Err :=
  let w := if st.noContextTakeover then #[] else st.window
  pmdInflate cfg w (deflateInput payload)

/-- **`ws_pmd_context_takeover` — RFC 7692 §7.1.1.1.** Under `no_context_takeover`,
the LZ77 window is reset per message: decompressing a compressed message yields
exactly the original message **regardless of the carried window** `st.window`. The
prior context cannot leak into — or corrupt — the current message, because the
reset discards it. (Contrast `pmd_ctxTakeover_uses_window`: with context takeover
the window is *not* discarded.) -/
theorem ws_pmd_context_takeover (cfg : Cfg) (st : RecvState) (x : Bytes)
    (hnct : st.noContextTakeover = true)
    (hlen : x.length < 65536) (hcap : x.length ≤ cfg.maxOut) :
    recvMessage cfg st (compress x) = (x.toArray, none) := by
  simp only [recvMessage, hnct, if_pos]
  rw [pmdInflate_roundtrip cfg #[] x hlen (by simpa using hcap)]
  simp

/-- **The reset is observable (the contrast).** With context takeover *off* in the
model (`noContextTakeover = false`), the carried window `st.window` is fed as the
initial output, so a nonempty prior context is prepended to the decoded message:
`recvMessage` on a compressed `x` returns `st.window ++ x`, not `x`. This is why
the §7.1.1.1 reset above is a real property and not a vacuous restatement — the two
modes give different outputs whenever the window is nonempty. -/
theorem pmd_ctxTakeover_uses_window (cfg : Cfg) (st : RecvState) (x : Bytes)
    (hct : st.noContextTakeover = false)
    (hlen : x.length < 65536) (hcap : st.window.size + x.length ≤ cfg.maxOut) :
    recvMessage cfg st (compress x) = (st.window ++ x.toArray, none) := by
  simp only [recvMessage, hct, Bool.false_eq_true, if_false]
  exact pmdInflate_roundtrip cfg st.window x hlen hcap

end Pmd
end Ws
