import Ws.Basic
import Ws.Length
import Ws.Frame

/-!
# The streaming frame-header verdict (RFC 6455 §5.1/§5.2/§5.5) — in the core

The open-connection WebSocket engine is host code: a bounded streaming codec
whose header decoder reads FIN/RSV/opcode/mask/length out of at most 14 wire
octets and enforces the §5 structural rules the moment the deciding bytes are
in hand. That decoder *is the frame-parse verdict* — whether bytes are a frame
header, where its payload starts, how long it is, and whether the connection
must instead be failed with 1002 — and until now it lived only in the host,
ungoverned by the proven core (the same green-proof/wrong-wire gap the raw
request framer `Body.FrameRaw` closed for HTTP/1.1).

This module lifts the verdict into the core. `decodeHeader` is a **total**
function (no recursion at all — the header grammar is fixed-shape, so totality
is by construction) from an accumulated wire prefix to one of:

* `needMore` — the prefix does not yet contain the deciding bytes;
* `bad 1002` — a structural violation (§5.2 RSV ≠ 0, a reserved opcode, a
  client frame without a mask, a fragmented or over-long control frame (§5.5),
  a 64-bit extended length with its top bit set);
* `done h used` — a complete, structurally valid header: FIN, the classified
  opcode, the payload length resolved by the **proven** `Ws.Length` ladder,
  and the 4-octet masking key; `used` is the exact header size in octets.

The theorems:

* `decode_encode` — **decode inverts encode**: a header assembled from any
  in-range fields (defined opcode, 4-octet key, length < 2⁶³, §5.5-shaped if
  control) is decoded back to exactly those fields, with the length riding the
  proven canonical ladder (`decodeLenField_encodeLenField`).
* `done_inv` / `done_valid` — an admitted header *cannot* carry set RSV bits,
  a reserved opcode, or an unmasked payload, and an admitted control header is
  unfragmented with payload ≤ 125 — the §5.5 half of `Ws.Frame.Wf`.
* `done_frame_wf` — the bridge to the logical layer: a frame assembled from an
  admitted header (plus the §5.5.1 close-length rule the close machinery
  enforces) is well-formed (`Ws.Frame.Wf`).
* `decodeHeader_extend` — **verdict stability**: a decided verdict (done or
  bad) never changes when more bytes arrive. This is the theorem that makes
  the verdict *streaming-safe*: the host may retry on any accumulation
  schedule and always lands on the same answer.
* `needMore_lt_14` / `no_needMore_of_14` — **progress**: 14 octets always
  decide (the longest §5.2 header is 2 + 8 + 4), so the host's fixed 14-byte
  accumulator can never stall.
* `done_used_bounds` — **no overread**: `used` never exceeds the supplied
  prefix (nor 14), and the returned key is exactly the 4 wire octets after the
  extended length.
* Concrete reject/accept vectors (kernel-checked): the RSV, reserved-opcode,
  unmasked, fragmented-ping, oversize-ping, and MSB-set-length violations are
  refused; the §1.3 masked `"Hello"` header and a non-canonical 64-bit-rung
  length (which §5.2 tolerates on receive) are admitted.

`closeCodeOk` is the §7.4 close-code registry decision (1000–1003, 1007–1014,
3000–4999 may appear on the wire; 1004–1006, 1015 and everything else must
not), with the reserved codes pinned refused and `closeNoStatus` (1005) proven
never-on-wire.

`drorb_ws_header` (`@[export]`) is the C-ABI seam: accumulated header prefix
in, encoded verdict out (`0` = needMore; `1 hi lo` = bad, code big-endian;
`2 fin op used mask₄ len₈` = done, length little-endian). `drorb_ws_close_ok`
exports the registry decision. The host's header decoder keeps only the byte
accumulation; every verdict it reports is this module's.
-/

namespace Ws
namespace Decode

/-! ## The decoded header and the verdict -/

/-- A structurally valid frame header: FIN, the classified opcode, the payload
length (already resolved through the extended-length ladder), and the 4-octet
client masking key (§5.3) the payload must be unmasked with. -/
structure Header where
  fin : Bool
  opcode : Opcode
  len : Nat
  mask : Bytes
deriving Repr, DecidableEq

/-- The streaming verdict on an accumulated wire prefix. -/
inductive Verdict where
  /-- The prefix does not yet contain the octets that decide. -/
  | needMore
  /-- A structural violation; fail the connection with this close code. -/
  | bad (code : Nat)
  /-- A complete, valid header occupying exactly `used` octets of the prefix. -/
  | done (h : Header) (used : Nat)
deriving Repr, DecidableEq

/-- The number of extended-length octets a 7-bit length field introduces:
none inline, two on the 16-bit rung (`126`), eight on the 64-bit rung
(`127`) — RFC 6455 §5.2. -/
def extCount (l7 : Nat) : Nat := if l7 = 126 then 2 else if l7 = 127 then 8 else 0

theorem extCount_le (l7 : Nat) : extCount l7 ≤ 8 := by
  unfold extCount
  split
  · omega
  · split <;> omega

/-- **The frame-header verdict** (RFC 6455 §5.1/§5.2/§5.5), as one total
function of the accumulated wire prefix. Checked in the order the octets
arrive — everything the two fixed octets decide is decided before more input
is demanded:

1. RSV1–3 must be zero (§5.2: no extension is negotiated);
2. the opcode must be one of the six defined values (§5.2);
3. a client-to-server frame must be masked (§5.1);
4. a control frame must be unfragmented with payload ≤ 125 (§5.5);
5. only then may the extended length + key octets be awaited;
6. a 64-bit extended length must have its top bit zero (§5.2).

On success: FIN is bit 7 of octet 0, the opcode its low nibble, the length is
the proven ladder's `decodeLenField`, and the mask is the 4 octets after the
extended length. `used = 2 + extCount + 4` is the exact header size. -/
def decodeHeader : Bytes → Verdict
  | b0 :: b1 :: rest =>
    if b0.toNat / 16 % 8 ≠ 0 then .bad closeProtocolError
    else if isDefinedOpcode (b0.toNat % 16) = false then .bad closeProtocolError
    else if b1.toNat < 128 then .bad closeProtocolError
    else if (Opcode.ofNat (b0.toNat % 16)).isControl = true
            ∧ (b0.toNat < 128 ∨ 125 < b1.toNat % 128) then .bad closeProtocolError
    else if rest.length < extCount (b1.toNat % 128) + 4 then .needMore
    else if 2 ^ 63 ≤ decodeLenField (b1.toNat % 128)
                       (rest.take (extCount (b1.toNat % 128))) then
      .bad closeProtocolError
    else
      .done
        { fin := decide (128 ≤ b0.toNat)
          opcode := Opcode.ofNat (b0.toNat % 16)
          len := decodeLenField (b1.toNat % 128) (rest.take (extCount (b1.toNat % 128)))
          mask := (rest.drop (extCount (b1.toNat % 128))).take 4 }
        (2 + extCount (b1.toNat % 128) + 4)
  | _ => .needMore

/-! ## Inversion: everything a `done` verdict certifies -/

/-- **Inversion.** A `done` verdict pins every gate it passed and every field
it returned: RSV1–3 were zero, the opcode nibble is defined, the mask bit was
set, the §5.5 control shape held, the prefix really contains the whole header,
the length is the proven ladder's reading of the extended field (below 2⁶³),
and the key is exactly the 4 wire octets after it. -/
theorem done_inv (b0 b1 : UInt8) (rest : Bytes) (h : Header) (u : Nat)
    (hd : decodeHeader (b0 :: b1 :: rest) = .done h u) :
    b0.toNat / 16 % 8 = 0
    ∧ isDefinedOpcode (b0.toNat % 16) = true
    ∧ 128 ≤ b1.toNat
    ∧ ¬((Opcode.ofNat (b0.toNat % 16)).isControl = true
        ∧ (b0.toNat < 128 ∨ 125 < b1.toNat % 128))
    ∧ extCount (b1.toNat % 128) + 4 ≤ rest.length
    ∧ h = { fin := decide (128 ≤ b0.toNat)
            opcode := Opcode.ofNat (b0.toNat % 16)
            len := decodeLenField (b1.toNat % 128) (rest.take (extCount (b1.toNat % 128)))
            mask := (rest.drop (extCount (b1.toNat % 128))).take 4 }
    ∧ h.len < 2 ^ 63
    ∧ u = 2 + extCount (b1.toNat % 128) + 4 := by
  simp only [decodeHeader] at hd
  by_cases g1 : b0.toNat / 16 % 8 ≠ 0
  · rw [if_pos g1] at hd; exact Verdict.noConfusion hd
  rw [if_neg g1] at hd
  by_cases g2 : isDefinedOpcode (b0.toNat % 16) = false
  · rw [if_pos g2] at hd; exact Verdict.noConfusion hd
  rw [if_neg g2] at hd
  by_cases g3 : b1.toNat < 128
  · rw [if_pos g3] at hd; exact Verdict.noConfusion hd
  rw [if_neg g3] at hd
  by_cases g4 : (Opcode.ofNat (b0.toNat % 16)).isControl = true
      ∧ (b0.toNat < 128 ∨ 125 < b1.toNat % 128)
  · rw [if_pos g4] at hd; exact Verdict.noConfusion hd
  rw [if_neg g4] at hd
  by_cases g5 : rest.length < extCount (b1.toNat % 128) + 4
  · rw [if_pos g5] at hd; exact Verdict.noConfusion hd
  rw [if_neg g5] at hd
  by_cases g6 : 2 ^ 63 ≤ decodeLenField (b1.toNat % 128)
      (rest.take (extCount (b1.toNat % 128)))
  · rw [if_pos g6] at hd; exact Verdict.noConfusion hd
  rw [if_neg g6] at hd
  injection hd with hh hu
  refine ⟨by omega, ?_, by omega, g4, by omega, hh.symm, ?_, hu.symm⟩
  · cases hop : isDefinedOpcode (b0.toNat % 16)
    · exact absurd hop g2
    · rfl
  · rw [hh.symm]
    show decodeLenField (b1.toNat % 128) (rest.take (extCount (b1.toNat % 128))) < 2 ^ 63
    omega

/-! ## Progress: 14 octets always decide -/

/-- A `needMore` verdict happens only below 14 octets — the longest header
§5.2 permits (2 fixed + 8 extended-length + 4 key). -/
theorem needMore_lt_14 : ∀ (bs : Bytes), decodeHeader bs = .needMore → bs.length < 14
  | [], _ => by simp
  | [_], _ => by simp
  | b0 :: b1 :: rest, h => by
    have hec := extCount_le (b1.toNat % 128)
    simp only [decodeHeader] at h
    by_cases g1 : b0.toNat / 16 % 8 ≠ 0
    · rw [if_pos g1] at h; exact Verdict.noConfusion h
    rw [if_neg g1] at h
    by_cases g2 : isDefinedOpcode (b0.toNat % 16) = false
    · rw [if_pos g2] at h; exact Verdict.noConfusion h
    rw [if_neg g2] at h
    by_cases g3 : b1.toNat < 128
    · rw [if_pos g3] at h; exact Verdict.noConfusion h
    rw [if_neg g3] at h
    by_cases g4 : (Opcode.ofNat (b0.toNat % 16)).isControl = true
        ∧ (b0.toNat < 128 ∨ 125 < b1.toNat % 128)
    · rw [if_pos g4] at h; exact Verdict.noConfusion h
    rw [if_neg g4] at h
    by_cases g5 : rest.length < extCount (b1.toNat % 128) + 4
    · simp only [List.length_cons]; omega
    rw [if_neg g5] at h
    by_cases g6 : 2 ^ 63 ≤ decodeLenField (b1.toNat % 128)
        (rest.take (extCount (b1.toNat % 128)))
    · rw [if_pos g6] at h; exact Verdict.noConfusion h
    · rw [if_neg g6] at h; exact Verdict.noConfusion h

/-- **Progress.** A 14-octet prefix is always decided: the host's fixed
14-byte accumulator can never stall waiting for a verdict. -/
theorem no_needMore_of_14 (bs : Bytes) (h : 14 ≤ bs.length) :
    decodeHeader bs ≠ .needMore := by
  intro hnm
  have := needMore_lt_14 bs hnm
  omega

/-! ## No overread: the header the verdict claims fits the prefix -/

/-- **Bounds.** A `done` verdict's `used` is the true header size: at least 6,
at most 14, never past the supplied prefix; and the returned key is exactly 4
octets. -/
theorem done_used_bounds : ∀ (bs : Bytes) (h : Header) (u : Nat),
    decodeHeader bs = .done h u →
    6 ≤ u ∧ u ≤ 14 ∧ u ≤ bs.length ∧ h.mask.length = 4
  | [], _, _, hd => absurd hd (by simp [decodeHeader])
  | [_], _, _, hd => absurd hd (by simp [decodeHeader])
  | b0 :: b1 :: rest, h, u, hd => by
    have hec := extCount_le (b1.toNat % 128)
    obtain ⟨-, -, -, -, hlen, hh, -, hu⟩ := done_inv b0 b1 rest h u hd
    subst hh hu
    refine ⟨by omega, by omega, by simp only [List.length_cons]; omega, ?_⟩
    simp only [List.length_take, List.length_drop]
    omega

/-! ## Verdict stability: more input never changes a decided verdict -/

/-- **Streaming safety.** Once the verdict is decided (`done` or `bad`),
feeding more octets cannot change it: the host may accumulate and retry on any
schedule — byte-by-byte or in bulk — and always lands on the same answer. -/
theorem decodeHeader_extend : ∀ (bs tl : Bytes), decodeHeader bs ≠ .needMore →
    decodeHeader (bs ++ tl) = decodeHeader bs
  | [], _, h => absurd rfl h
  | [_], _, h => absurd rfl h
  | b0 :: b1 :: rest, tl, h => by
    show decodeHeader (b0 :: b1 :: (rest ++ tl)) = decodeHeader (b0 :: b1 :: rest)
    simp only [decodeHeader]
    by_cases g1 : b0.toNat / 16 % 8 ≠ 0
    · rw [if_pos g1, if_pos g1]
    rw [if_neg g1, if_neg g1]
    by_cases g2 : isDefinedOpcode (b0.toNat % 16) = false
    · rw [if_pos g2, if_pos g2]
    rw [if_neg g2, if_neg g2]
    by_cases g3 : b1.toNat < 128
    · rw [if_pos g3, if_pos g3]
    rw [if_neg g3, if_neg g3]
    by_cases g4 : (Opcode.ofNat (b0.toNat % 16)).isControl = true
        ∧ (b0.toNat < 128 ∨ 125 < b1.toNat % 128)
    · rw [if_pos g4, if_pos g4]
    rw [if_neg g4, if_neg g4]
    by_cases g5 : rest.length < extCount (b1.toNat % 128) + 4
    · exfalso
      apply h
      simp only [decodeHeader]
      rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_pos g5]
    have hlen : ¬ ((rest ++ tl).length < extCount (b1.toNat % 128) + 4) := by
      rw [List.length_append]; omega
    have htake : (rest ++ tl).take (extCount (b1.toNat % 128))
        = rest.take (extCount (b1.toNat % 128)) :=
      List.take_append_of_le_length (by omega)
    have hdrop : (rest ++ tl).drop (extCount (b1.toNat % 128))
        = rest.drop (extCount (b1.toNat % 128)) ++ tl :=
      List.drop_append_of_le_length (by omega)
    have hdt : (rest.drop (extCount (b1.toNat % 128)) ++ tl).take 4
        = (rest.drop (extCount (b1.toNat % 128))).take 4 :=
      List.take_append_of_le_length (by rw [List.length_drop]; omega)
    rw [if_neg hlen, if_neg g5, htake, hdrop, hdt]

/-! ## Validation: what an admitted header can never be -/

/-- **Admitted headers are valid.** A `done` verdict certifies: RSV1–3 were
zero, the opcode is a defined (non-reserved) one, the frame was masked, an
admitted control header is unfragmented (`fin = true`) with payload ≤ 125
(§5.5), and the length is below 2⁶³ (§5.2). -/
theorem done_valid (b0 b1 : UInt8) (rest : Bytes) (h : Header) (u : Nat)
    (hd : decodeHeader (b0 :: b1 :: rest) = .done h u) :
    b0.toNat / 16 % 8 = 0
    ∧ isDefinedOpcode (b0.toNat % 16) = true
    ∧ 128 ≤ b1.toNat
    ∧ (h.opcode.isControl = true → h.fin = true ∧ h.len ≤ 125)
    ∧ h.len < 2 ^ 63 := by
  obtain ⟨hrsv, hop, hmask, g4, hlen, hh, hlt, -⟩ := done_inv b0 b1 rest h u hd
  refine ⟨hrsv, hop, hmask, ?_, hlt⟩
  intro hctl
  have hctl' : (Opcode.ofNat (b0.toNat % 16)).isControl = true := by
    rw [hh] at hctl
    exact hctl
  have hnb : ¬(b0.toNat < 128 ∨ 125 < b1.toNat % 128) := fun hb => g4 ⟨hctl', hb⟩
  constructor
  · rw [hh]
    show decide (128 ≤ b0.toNat) = true
    simp only [decide_eq_true_eq]
    omega
  · rw [hh]
    show decodeLenField (b1.toNat % 128) (rest.take (extCount (b1.toNat % 128))) ≤ 125
    have hl7' : b1.toNat % 128 ≤ 125 := by omega
    simp only [decodeLenField, if_pos hl7']
    exact hl7'

/-- **The bridge to the logical frame layer.** A frame assembled from an
admitted header — its payload of exactly the admitted length — is well-formed
(`Ws.Frame.Wf`), given the §5.5.1 close-length rule (`length ≠ 1`) that the
close machinery enforces on the close payload itself. So the header verdict
plus the close-code step reconstruct exactly the well-formedness predicate the
reassembly and close machines are proven over. -/
theorem done_frame_wf : ∀ (bs : Bytes) (h : Header) (u : Nat),
    decodeHeader bs = .done h u →
    ∀ (payload : Bytes), payload.length = h.len →
    (h.opcode = Opcode.close → payload.length ≠ 1) →
    Frame.Wf { fin := h.fin, opcode := h.opcode, payload := payload }
  | [], _, _, hd, _, _, _ => absurd hd (by simp [decodeHeader])
  | [_], _, _, hd, _, _, _ => absurd hd (by simp [decodeHeader])
  | b0 :: b1 :: rest, h, u, hd, payload, hlen, hclose => by
    obtain ⟨-, -, -, hctl, -⟩ := done_valid b0 b1 rest h u hd
    show (h.opcode.isControl = true → h.fin = true ∧ payload.length ≤ 125)
        ∧ (h.opcode = Opcode.close → payload.length ≠ 1)
    refine ⟨fun hc => ?_, fun hc => hclose hc⟩
    obtain ⟨hfin, hle⟩ := hctl hc
    exact ⟨hfin, by omega⟩

/-! ## Decode inverts encode — the ladder-canonical round trip -/

/-- Encode a frame header from its fields, written from the §5.2 wire layout:
octet 0 is FIN·2⁷ + opcode, octet 1 is MASK·2⁷ + the ladder marker, then the
canonical extended-length octets (`Ws.lenExt`), then the 4-octet key. -/
def encodeHeader (fin : Bool) (op : Nat) (mask : Bytes) (n : Nat) : Bytes :=
  UInt8.ofNat ((if fin then 128 else 0) + op)
    :: UInt8.ofNat (128 + lenMarker n)
    :: (lenExt n ++ mask)

/-- The defined opcode nibbles are below 16. -/
theorem isDefinedOpcode_lt {n : Nat} (h : isDefinedOpcode n = true) : n < 16 := by
  unfold isDefinedOpcode at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h <;> omega

/-- The ladder marker fits the 7-bit field. -/
theorem lenMarker_lt (n : Nat) : lenMarker n < 128 := by
  unfold lenMarker
  split
  · omega
  · split <;> omega

/-- The canonical extended octets are exactly as many as the marker announces. -/
theorem lenExt_length (n : Nat) : (lenExt n).length = extCount (lenMarker n) := by
  unfold lenExt lenMarker extCount
  by_cases h1 : n < 126
  · rw [if_pos h1, if_pos h1, if_neg (by omega), if_neg (by omega)]
    rfl
  · by_cases h2 : n < 2 ^ 16
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, if_pos rfl]
      rfl
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, if_neg (by omega), if_pos rfl]
      rfl

/-- **Decode inverts encode.** A header assembled from any in-range fields — a
defined opcode, a 4-octet key, a length below 2⁶³, and (if control) the §5.5
shape — decodes to exactly those fields, regardless of what payload octets
follow. The length rides the proven canonical ladder
(`Ws.decodeLenField_encodeLenField`), so this is the §5.2 wire grammar and the
ladder canonicity in one round trip. -/
theorem decode_encode (fin : Bool) (op : Nat) (mask : Bytes) (n : Nat) (tail : Bytes)
    (hop : isDefinedOpcode op = true) (hmask : mask.length = 4) (hn : n < 2 ^ 63)
    (hctl : (Opcode.ofNat op).isControl = true → fin = true ∧ n ≤ 125) :
    decodeHeader (encodeHeader fin op mask n ++ tail) =
      .done
        { fin := fin, opcode := Opcode.ofNat op, len := n, mask := mask }
        (2 + extCount (lenMarker n) + 4) := by
  have hoplt : op < 16 := isDefinedOpcode_lt hop
  have hmlt : lenMarker n < 128 := lenMarker_lt n
  have hextlen : (lenExt n).length = extCount (lenMarker n) := lenExt_length n
  have hb0 : (UInt8.ofNat ((if fin then 128 else 0) + op)).toNat
      = (if fin then 128 else 0) + op := by
    rw [toNat_ofNat]
    cases fin <;> simp <;> omega
  have hb1 : (UInt8.ofNat (128 + lenMarker n)).toNat = 128 + lenMarker n := by
    rw [toNat_ofNat]; omega
  simp only [encodeHeader, List.cons_append]
  simp only [decodeHeader]
  rw [hb0, hb1]
  have hl7 : (128 + lenMarker n) % 128 = lenMarker n := by omega
  rw [hl7]
  have hfl : ((if fin then 128 else 0) + op) % 16 = op := by
    cases fin <;> simp <;> omega
  rw [hfl]
  have hrsv : ¬(((if fin then 128 else 0) + op) / 16 % 8 ≠ 0) := by
    cases fin <;> simp <;> omega
  rw [if_neg hrsv,
      if_neg (by simp [hop] : ¬(isDefinedOpcode op = false)),
      if_neg (by omega : ¬(128 + lenMarker n < 128))]
  have g4 : ¬((Opcode.ofNat op).isControl = true
      ∧ ((if fin then 128 else 0) + op < 128 ∨ 125 < lenMarker n)) := by
    rintro ⟨hc, hbad⟩
    obtain ⟨hfin', hle⟩ := hctl hc
    subst hfin'
    have hm : lenMarker n = n := by
      unfold lenMarker
      rw [if_pos (by omega : n < 126)]
    rw [hm] at hbad
    simp only [eq_self_iff_true, if_true] at hbad
    omega
  rw [if_neg g4]
  have hlen5 : ¬((lenExt n ++ mask ++ tail).length < extCount (lenMarker n) + 4) := by
    rw [List.length_append, List.length_append, hextlen, hmask]
    omega
  rw [if_neg hlen5]
  have htake : (lenExt n ++ mask ++ tail).take (extCount (lenMarker n)) = lenExt n := by
    rw [← hextlen, List.append_assoc, List.take_left]
  rw [htake, decodeLenField_encodeLenField n (by omega)]
  rw [if_neg (by omega : ¬(2 ^ 63 ≤ n))]
  have hdrop4 : ((lenExt n ++ mask ++ tail).drop (extCount (lenMarker n))).take 4
      = mask := by
    rw [← hextlen, List.append_assoc, List.drop_left, ← hmask, List.take_left]
  rw [hdrop4]
  have hfin : decide (128 ≤ (if fin then 128 else 0) + op) = fin := by
    cases fin <;> simp <;> omega
  rw [hfin]

/-! ## Kernel-checked wire vectors (non-vacuity) -/

/-- §5.2: a set RSV bit is refused (RSV1 here). -/
theorem vec_rsv_refused : decodeHeader [0xC1, 0x80] = .bad closeProtocolError := by decide

/-- §5.2: a reserved opcode (0x3) is refused. -/
theorem vec_reserved_opcode_refused :
    decodeHeader [0x83, 0x80] = .bad closeProtocolError := by decide

/-- §5.1: an unmasked client frame is refused. -/
theorem vec_unmasked_refused : decodeHeader [0x81, 0x05] = .bad closeProtocolError := by decide

/-- §5.5: a fragmented ping (FIN = 0, control opcode) is refused. -/
theorem vec_fragmented_ping_refused :
    decodeHeader [0x09, 0x80] = .bad closeProtocolError := by decide

/-- §5.5: a ping announcing a 126-octet payload is refused. -/
theorem vec_oversize_ping_refused :
    decodeHeader [0x89, 0xFE] = .bad closeProtocolError := by decide

/-- §5.2: a 64-bit extended length with the top bit set is refused. -/
theorem vec_msb_len_refused :
    decodeHeader [0x82, 0xFF, 0x80, 0, 0, 0, 0, 0, 0, 1, 0xa5, 0x5a, 0x00, 0xff]
      = .bad closeProtocolError := by decide

/-- One octet decides nothing yet. -/
theorem vec_one_octet_needMore : decodeHeader [0x81] = .needMore := by decide

/-- A masked text header awaiting its key still needs more. -/
theorem vec_await_key_needMore : decodeHeader [0x81, 0x85, 0x37] = .needMore := by decide

/-- The RFC 6455 §1.3 masked `"Hello"` example: FIN text, length 5, key
`37 fa 21 3d` — admitted with `used = 6`, whatever payload follows. -/
theorem vec_hello_admitted :
    decodeHeader [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58]
      = .done
          { fin := true, opcode := .text, len := 5, mask := [0x37, 0xfa, 0x21, 0x3d] }
          6 := by decide

/-- §5.2 requires *senders* to use the minimal rung but receivers tolerate a
longer one: a 64-bit-rung length of 5 is admitted (the host's retired decoder
did the same, so the verdicts stay wire-identical). -/
theorem vec_noncanonical_admitted :
    decodeHeader [0x82, 0xFF, 0, 0, 0, 0, 0, 0, 0, 5, 0xa5, 0x5a, 0x00, 0xff]
      = .done
          { fin := true, opcode := .binary, len := 5, mask := [0xa5, 0x5a, 0x00, 0xff] }
          14 := by decide

/-! ## The §7.4 close-code registry -/

/-- May `code` appear on the wire in a Close frame (RFC 6455 §7.4)? 0–999 are
unused; 1004–1006 and 1015 are reserved and MUST NOT be sent; 1016–2999 are
reserved for future protocol revisions; 1012–1014 are registered post-6455;
3000–4999 are registered/private use. -/
def closeCodeOk (code : Nat) : Bool :=
  (1000 ≤ code && code ≤ 1003) || (1007 ≤ code && code ≤ 1014)
    || (3000 ≤ code && code ≤ 4999)

/-- The registry decision, characterized. -/
theorem closeCodeOk_iff (code : Nat) :
    closeCodeOk code = true ↔
      (1000 ≤ code ∧ code ≤ 1003) ∨ (1007 ≤ code ∧ code ≤ 1014)
        ∨ (3000 ≤ code ∧ code ≤ 4999) := by
  simp [closeCodeOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc]

/-- The reserved codes (§7.4.1: 1004, 1005, 1006, 1015) are never admitted on
the wire — in particular `closeNoStatus` (1005), the code that *means* "no
code was present". -/
theorem reserved_codes_refused :
    closeCodeOk 1004 = false ∧ closeCodeOk closeNoStatus = false
      ∧ closeCodeOk 1006 = false ∧ closeCodeOk 1015 = false := by decide

/-- Registry vectors: the boundary codes on both sides. -/
theorem registry_vectors :
    (closeCodeOk closeNormal ∧ closeCodeOk closeProtocolError ∧ closeCodeOk 1003
      ∧ closeCodeOk 1007 ∧ closeCodeOk closeTooBig ∧ closeCodeOk 1014
      ∧ closeCodeOk 3000 ∧ closeCodeOk 4999)
    ∧ (¬ closeCodeOk 0 ∧ ¬ closeCodeOk 999 ∧ ¬ closeCodeOk 1016
      ∧ ¬ closeCodeOk 2999 ∧ ¬ closeCodeOk 5000) := by decide

/-! ## The host-facing C-ABI seam -/

/-- Little-endian 8-octet encoding of a length (the host reads it back). -/
def le64 (n : Nat) : Bytes :=
  (List.range 8).map (fun i => UInt8.ofNat (n / 256 ^ i % 256))

/-- The wire nibble of a defined opcode (`reserved` keeps its low nibble; a
`done` verdict never carries one — `done_valid`). -/
def opcodeNibble : Opcode → UInt8
  | .continuation => 0x0
  | .text => 0x1
  | .binary => 0x2
  | .close => 0x8
  | .ping => 0x9
  | .pong => 0xA
  | .reserved n => UInt8.ofNat (n % 16)

/-- Encode a verdict for the host: `[0]` = needMore; `[1, hi, lo]` = bad (the
close code, big-endian); `[2, fin, opcode, used] ++ mask₄ ++ len₈` = done (the
length little-endian) — 16 octets exactly. -/
def encodeVerdict : Verdict → Bytes
  | .needMore => [0]
  | .bad code => [1, UInt8.ofNat (code / 256), UInt8.ofNat (code % 256)]
  | .done h used =>
    2 :: (if h.fin then 1 else 0) :: opcodeNibble h.opcode :: UInt8.ofNat used
      :: (h.mask ++ le64 h.len)

/-- A `done` verdict encodes to exactly 16 octets (given the 4-octet key a
`done` always carries — `done_used_bounds`). -/
theorem encode_done_length (h : Header) (u : Nat) (hm : h.mask.length = 4) :
    (encodeVerdict (.done h u)).length = 16 := by
  simp [encodeVerdict, le64, hm]

/-- **ABI vector.** The §1.3 `"Hello"` header's encoded verdict, octet by
octet: tag 2, FIN 1, opcode text, used 6, the key, then 5 little-endian. -/
theorem vec_hello_abi :
    encodeVerdict (decodeHeader [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d])
      = [2, 1, 1, 6, 0x37, 0xfa, 0x21, 0x3d, 5, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- **ABI vector.** A protocol violation encodes as `[1, 3, 234]`
(1002 big-endian). -/
theorem vec_bad_abi :
    encodeVerdict (decodeHeader [0xC1, 0x80]) = [1, 3, 234] := by decide

/-- **`drorb_ws_header`.** The seam the host's frame codec crosses instead of
deciding the header itself: the accumulated header prefix in, the encoded
verdict out. Total `ByteArray → ByteArray`. -/
@[export drorb_ws_header]
def headerExport (input : ByteArray) : ByteArray :=
  ByteArray.mk (encodeVerdict (decodeHeader input.toList)).toArray

/-- **`drorb_ws_close_ok`.** The §7.4 registry decision for the host's close
machinery: 1 iff the code may appear on the wire. -/
@[export drorb_ws_close_ok]
def closeCodeOkExport (code : UInt32) : UInt8 :=
  if closeCodeOk code.toNat then 1 else 0

end Decode
end Ws
