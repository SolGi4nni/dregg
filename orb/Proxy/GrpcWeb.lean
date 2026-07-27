import Reactor.Proxy.Grpc

/-!
# Proxy.GrpcWeb — gRPC-Web text mode (base64) and the gRPC-Web ⇄ gRPC bridge

`Reactor.Proxy.Grpc` proves the gRPC message framing (length-prefixed message),
the `grpc-status` trailer, and the binary gRPC-Web framing translation (the
trailer frame with the `0x80` flag). It leaves one capability named as residual:

* **gRPC-Web text mode** (`application/grpc-web-text`): the *whole* response/request
  body is base64-encoded so browsers that cannot handle binary can carry it. The
  framing translation itself is mode-independent; text mode is a standard
  base64 encoding layer wrapped around the already-framed body.

This module closes that residual with a **verified** base64 codec and lifts it
to the bridge:

* `encB64` / `decB64` — a from-scratch base64 codec over byte lists with `=`
  padding, proven a faithful inverse for every byte string
  (`decB64_encB64` — decoding an encoded body recovers it exactly).
* `grpcweb_text_roundtrip` — a text-mode gRPC-Web body (one length-prefixed data
  frame followed by the trailer frame) base64-decodes to the *same* gRPC message
  and the *same* trailer frame: text mode is transparent over the framing.
* `parseTrailerFrame` / `splitWeb` — the gRPC-Web → gRPC translation: split the
  leading data frame from the trailing `0x80` trailer frame.
* `grpcweb_to_grpc` — the translation preserves the length-prefixed message and
  the trailer block (which carries `grpc-status`) byte-for-byte.

## Base64 (RFC 4648 §4)

Three input bytes (24 bits) map to four base64 characters (four 6-bit *sextets*);
a 1- or 2-byte tail is padded to a full quantum with `=`. The alphabet is the
standard `A–Z a–z 0–9 + /`. The core lemma is the sextet inverse
`unSextet (sextet s) = s` for every `s < 64`; the byte roundtrip is then pure
`omega` bit-arithmetic per quantum, threaded over the list.
-/

namespace Proxy.GrpcWeb

open Reactor.Proxy.Grpc

/-! ## The base64 alphabet (RFC 4648 §4 Table 1) -/

/-- Map a 6-bit sextet (`0 … 63`) to its base64 ASCII code:
`A–Z` = `0–25` → `65–90`, `a–z` = `26–51` → `97–122`, `0–9` = `52–61` → `48–57`,
`+` = `62` → `43`, `/` = `63` → `47`. (Out-of-range inputs fold to `/`.) -/
def sextet (s : Nat) : Nat :=
  if s < 26 then s + 65
  else if s < 52 then s - 26 + 97
  else if s < 62 then s - 52 + 48
  else if s = 62 then 43
  else 47

/-- The padding character `=` (ASCII `61`). The data alphabet never emits it. -/
def pad : Nat := 61

/-- Inverse of `sextet`: map a base64 ASCII code back to its 6-bit value. -/
def unSextet (c : Nat) : Nat :=
  if c = 43 then 62
  else if c = 47 then 63
  else if 48 ≤ c ∧ c ≤ 57 then c - 48 + 52
  else if 65 ≤ c ∧ c ≤ 90 then c - 65
  else if 97 ≤ c ∧ c ≤ 122 then c - 97 + 26
  else 0

/-- **The alphabet is injective / round-trips**: decoding an encoded sextet
recovers it, for every 6-bit value. -/
theorem unSextet_sextet (s : Nat) (h : s < 64) : unSextet (sextet s) = s := by
  unfold sextet
  repeat' split
  all_goals unfold unSextet
  all_goals repeat' split
  all_goals omega

/-- The data alphabet never produces the padding byte, so `=` unambiguously marks
padding in an encoded stream. -/
theorem sextet_ne_pad (s : Nat) : sextet s ≠ pad := by
  unfold sextet pad
  repeat' split
  all_goals omega

/-! ## The byte codec -/

/-- Encode a byte list to base64 ASCII, three bytes → four characters, with `=`
padding for a 1- or 2-byte tail (RFC 4648 §4). -/
def encB64 : List Nat → List Nat
  | [] => []
  | [b0] =>
      let s0 := b0 / 4
      let s1 := (b0 % 4) * 16
      [sextet s0, sextet s1, pad, pad]
  | [b0, b1] =>
      let s0 := b0 / 4
      let s1 := (b0 % 4) * 16 + b1 / 16
      let s2 := (b1 % 16) * 4
      [sextet s0, sextet s1, sextet s2, pad]
  | b0 :: b1 :: b2 :: rest =>
      let s0 := b0 / 4
      let s1 := (b0 % 4) * 16 + b1 / 16
      let s2 := (b1 % 16) * 4 + b2 / 64
      let s3 := b2 % 64
      sextet s0 :: sextet s1 :: sextet s2 :: sextet s3 :: encB64 rest

/-- Decode base64 ASCII back to bytes: four characters → three bytes; a trailing
`==` quantum yields one byte, a trailing `=` yields two (RFC 4648 §4). -/
def decB64 : List Nat → List Nat
  | c0 :: c1 :: c2 :: c3 :: rest =>
      if c2 = pad then
        -- "xx==" : one data byte.
        [unSextet c0 * 4 + unSextet c1 / 16]
      else if c3 = pad then
        -- "xxx=" : two data bytes.
        let s0 := unSextet c0
        let s1 := unSextet c1
        let s2 := unSextet c2
        [s0 * 4 + s1 / 16, (s1 % 16) * 16 + s2 / 4]
      else
        let s0 := unSextet c0
        let s1 := unSextet c1
        let s2 := unSextet c2
        let s3 := unSextet c3
        (s0 * 4 + s1 / 16) :: ((s1 % 16) * 16 + s2 / 4) :: ((s2 % 4) * 64 + s3)
          :: decB64 rest
  | _ => []

/-- **The base64 codec is a faithful inverse.** For every byte string (each
element a real byte `< 256`), decoding its encoding recovers it exactly — text
mode loses nothing. -/
theorem decB64_encB64 : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) →
    decB64 (encB64 bs) = bs := by
  intro bs
  induction bs using encB64.induct with
  | case1 => intro _; rfl
  | case2 b0 =>
      intro h
      have hb0 : b0 < 256 := h b0 (by simp)
      simp only [encB64, decB64]
      rw [if_true, unSextet_sextet _ (by omega), unSextet_sextet _ (by omega)]
      congr 1
      omega
  | case3 b0 b1 =>
      intro h
      have hb0 : b0 < 256 := h b0 (by simp)
      have hb1 : b1 < 256 := h b1 (by simp)
      simp only [encB64, decB64]
      rw [if_neg (sextet_ne_pad _), if_true]
      rw [unSextet_sextet _ (by omega), unSextet_sextet _ (by omega),
        unSextet_sextet _ (by omega)]
      simp only [List.cons.injEq, and_true]
      refine ⟨by omega, by omega⟩
  | case4 b0 b1 b2 rest ih =>
      intro h
      have hb0 : b0 < 256 := h b0 (by simp)
      have hb1 : b1 < 256 := h b1 (by simp)
      have hb2 : b2 < 256 := h b2 (by simp)
      have hrest : ∀ b ∈ rest, b < 256 := fun b hb => h b (by simp [hb])
      simp only [encB64, decB64]
      rw [if_neg (sextet_ne_pad _), if_neg (sextet_ne_pad _)]
      rw [unSextet_sextet _ (by omega), unSextet_sextet _ (by omega),
        unSextet_sextet _ (by omega), unSextet_sextet _ (by omega)]
      have hih := ih hrest
      rw [hih]
      simp only [List.cons.injEq, and_true]
      refine ⟨by omega, by omega, by omega⟩

/-! ### Non-vacuity: real base64 test vectors (RFC 4648) -/

/-- `"Man"` (`77 97 110`) encodes to `"TWFu"` (`84 87 70 117`) — the canonical
3-byte quantum, no padding. -/
example : encB64 [77, 97, 110] = [84, 87, 70, 117] := by decide

/-- `"M"` (`77`) encodes to `"TQ=="` (`84 81 61 61`) — one byte, two pad chars. -/
example : encB64 [77] = [84, 81, 61, 61] := by decide

/-- `"Ma"` (`77 97`) encodes to `"TWE="` (`84 87 69 61`) — two bytes, one pad. -/
example : encB64 [77, 97] = [84, 87, 69, 61] := by decide

/-- Roundtrip on a concrete non-trivial byte string (spanning all three tail
lengths across the quanta). -/
example : decB64 (encB64 [0, 255, 16, 128, 7]) = [0, 255, 16, 128, 7] := by decide

/-- **Mutant**: corrupting a single encoded character changes the decoded bytes —
the codec is not the constant/identity function (a vacuous roundtrip would still
pass `decB64_encB64` but fail here). -/
example : decB64 [84, 87, 70, 117] ≠ decB64 [84, 87, 70, 118] := by decide

/-! ## gRPC-Web trailer-frame parse (the ⇄ gRPC seam) -/

/-- Parse a gRPC-Web trailer frame (`0x80 :: be32 len ++ block`), recovering the
trailer block; `none` if the flag is not the trailer flag, the header is short,
or the declared length exceeds the body. The dual of `encodeTrailerFrame`. -/
def parseTrailerFrame : List Nat → Option (List Nat)
  | flag :: b0 :: b1 :: b2 :: b3 :: body =>
      if flag = trailerFlag then
        let len := rd32 [b0, b1, b2, b3]
        if len ≤ body.length then some (body.take len) else none
      else none
  | _ => none

/-- **Faithful trailer-frame decode.** Parsing an encoded trailer block recovers
it exactly. -/
theorem parseTrailerFrame_encode (block : List Nat) (h : block.length < 4294967296) :
    parseTrailerFrame (encodeTrailerFrame block) = some block := by
  have hrd : rd32 (be32 block.length) = block.length := rd32_be32 h
  simp only [encodeTrailerFrame, be32, List.cons_append, List.nil_append,
    parseTrailerFrame] at hrd ⊢
  rw [hrd]
  simp [List.take_length]

/-- A trailer frame is never mistaken for a data frame: parsing a *data* frame
(flag `0`/`1`) as a trailer frame fails. -/
theorem parseTrailerFrame_data (f : Frame) (rest : List Nat) :
    parseTrailerFrame (encodeFrame f ++ rest) = none := by
  simp only [encodeFrame, be32, flagByte, List.cons_append, List.nil_append,
    List.append_assoc, parseTrailerFrame]
  cases f.compressed <;> simp [trailerFlag]

/-- Build a gRPC-Web response body: one length-prefixed data frame followed by
the `0x80` trailer frame carrying the trailer block (`grpc-status`, `grpc-message`).
Byte-identical to `Reactor.Proxy.Grpc.buildGrpcWebResponse (encodeFrame f) block`. -/
def webResponse (f : Frame) (block : List Nat) : List Nat :=
  encodeFrame f ++ encodeTrailerFrame block

/-- Translate a gRPC-Web response body back to gRPC: recover the leading data
frame (the length-prefixed message) and the trailer block.

Written with `Option.bind`/`Option.map` rather than a nested `match`: the compiled
nested matcher, reduced by the *kernel* on a `some (…)` discriminant carrying an
`encodeTrailerFrame` argument, overflows the kernel's recursion guard when the
round-trip lemma is checked (the `Derp.derp_frame_bounds` failure class). `bind`/`map`
reduce through their `Option` recursors instead, so the kernel never normalizes the
whole nested-match term. Definitionally the same function (see the `decide` mutant
below). -/
def splitWeb (body : List Nat) : Option (Frame × List Nat) :=
  (decodeFrame body).bind fun p =>
    (parseTrailerFrame p.2).map fun block => (p.1, block)

/-- **gRPC-Web → gRPC preserves the message and the status trailer.** Translating
a gRPC-Web response recovers the exact length-prefixed message `f` and the exact
trailer block `block` (which carries `grpc-status`) — byte-for-byte. -/
theorem grpcweb_to_grpc (f : Frame) (block : List Nat)
    (hf : f.payload.length < 4294967296) (hb : block.length < 4294967296) :
    splitWeb (webResponse f block) = some (f, block) := by
  unfold splitWeb webResponse
  rw [decodeFrame_encodeFrame f (encodeTrailerFrame block) hf,
      Option.bind_some, parseTrailerFrame_encode block hb, Option.map_some]

/-- The status trailer block `grpc-status: <code>\r\n` as ASCII bytes, for a
single-digit code (`0 … 9`) — the shape a health/unary reply carries. -/
def statusTrailer (s : GrpcStatus) : List Nat :=
  -- "grpc-status: " = [103,114,112,99,45,115,116,97,116,117,115,58,32]
  [103, 114, 112, 99, 45, 115, 116, 97, 116, 117, 115, 58, 32]
    ++ [48 + s.code, 13, 10]  -- <digit> CR LF

/-- The status trailer block is a fixed 16 bytes (13-byte prefix + digit + CRLF). -/
theorem statusTrailer_length (s : GrpcStatus) : (statusTrailer s).length = 16 := rfl

/-- **grpc-status survives the bridge.** For a status trailer, gRPC-Web → gRPC
recovers the *same* status block byte-for-byte, so `grpc-status` is preserved. -/
theorem grpcweb_to_grpc_status (f : Frame) (s : GrpcStatus)
    (hf : f.payload.length < 4294967296) :
    splitWeb (webResponse f (statusTrailer s)) = some (f, statusTrailer s) := by
  refine grpcweb_to_grpc f (statusTrailer s) hf ?_
  rw [statusTrailer_length]; omega

/-! ## The headline: text mode is transparent over the framing -/

/-- Text-mode encode: base64 of the whole gRPC-Web body. -/
def encodeTextBody (body : List Nat) : List Nat := encB64 body

/-- Text-mode decode: base64-decode the whole body back to binary. -/
def decodeTextBody (text : List Nat) : List Nat := decB64 text

/-- Every byte of a well-formed gRPC-Web response body is a real byte (`< 256`):
the flag byte, the 4 big-endian length bytes, the trailer flag `0x80`, and — given
the payload and trailer block are byte lists — the message payload and trailer
block. -/
theorem be32_bytes_lt (n : Nat) : ∀ x ∈ be32 n, x < 256 := by
  intro x hx
  simp only [be32, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h <;> omega

theorem webResponse_bytes_lt (f : Frame) (block : List Nat)
    (hpay : ∀ b ∈ f.payload, b < 256) (hblk : ∀ b ∈ block, b < 256) :
    ∀ b ∈ webResponse f block, b < 256 := by
  intro b hb
  simp only [webResponse, encodeFrame, encodeTrailerFrame, flagByte, trailerFlag,
    List.mem_append, List.mem_cons] at hb
  rcases hb with ((h | h) | h) | ((h | h) | h)
  · subst h; split <;> omega
  · exact be32_bytes_lt _ b h
  · exact hpay b h
  · omega
  · exact be32_bytes_lt _ b h
  · exact hblk b h

/-- **gRPC-Web text mode is transparent.** A text-mode (base64) gRPC-Web response
body — one length-prefixed data frame `f` followed by the trailer frame for
`block` — base64-decodes to the binary body, which decodes to the *same* gRPC
message `f`, leaving the *same* trailer frame as the tail. Text mode changes the
transport encoding, never the framing. -/
theorem grpcweb_text_roundtrip (f : Frame) (block : List Nat)
    (hf : f.payload.length < 4294967296)
    (hpay : ∀ b ∈ f.payload, b < 256) (hblk : ∀ b ∈ block, b < 256) :
    decodeFrame (decodeTextBody (encodeTextBody (webResponse f block)))
      = some (f, encodeTrailerFrame block) := by
  have hbytes := webResponse_bytes_lt f block hpay hblk
  unfold decodeTextBody encodeTextBody
  rw [decB64_encB64 (webResponse f block) hbytes]
  unfold webResponse
  exact decodeFrame_encodeFrame f (encodeTrailerFrame block) hf

/-! ### Non-vacuity: a real text-mode "hello" reply with grpc-status: 0 -/

/-- The concrete uncompressed `"hello"` data frame. -/
def helloFrame : Frame := { compressed := false, payload := [104, 101, 108, 108, 111] }

/-- End-to-end: the text-mode `"hello"` + `grpc-status: 0` body base64-decodes and
frame-decodes back to exactly the `"hello"` message, tail = the trailer frame. -/
example :
    decodeFrame (decodeTextBody (encodeTextBody (webResponse helloFrame (statusTrailer .ok))))
      = some (helloFrame, encodeTrailerFrame (statusTrailer .ok)) := by
  apply grpcweb_text_roundtrip helloFrame (statusTrailer .ok)
  · decide
  · decide
  · decide

/-- **Mutant**: a body whose "trailer" position is a second *data* frame (flag
`0`, not `0x80`) is rejected by the bridge — `splitWeb` requires the trailer
frame, so a stream missing it does not silently translate. -/
example :
    splitWeb (encodeFrame helloFrame ++ encodeFrame helloFrame) = none := by
  decide

end Proxy.GrpcWeb
