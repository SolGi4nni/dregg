import H2.Conn

/-!
# HPACK header-block **encoding** (RFC 7541) — the dual of the deployed decoder

`H2/Hpack.lean` decodes an HPACK block into the arena store and `H2/Conn.lean`
decodes one field representation (`decodeFieldV`, with the real dynamic-table
address space) into plain name/value bytes. This module is the **encoder**: it
lays a header list back onto the wire as HPACK, and round-trips against the
*deployed* field decoder — `decodeHeadersV (encodeHeaders hs) = hs` — so a drorb
H2 client and a drorb H2 server agree on every HPACK octet.

The encoder is the simple, always-correct one RFC 7541 §6.2.2 sanctions: every
field is a **literal without indexing, literal name** representation — a `0x00`
representation byte, then the name as a raw string literal (§5.2), then the value
as a raw string literal — no dynamic-table insertion, no Huffman. This is exactly
what a conservative client may always send; the decoder (which *does* carry the
full static + dynamic tables) recovers each field verbatim.

Names/values must fit the single-octet 7-bit length prefix (`< 127` octets),
which every real request pseudo-header and ordinary header satisfies.

* `encStr` / `encField` / `encodeHeaders` — the string-literal, field, and block
  encoders.
* `hpack_decode_encode` — the headline round-trip: decoding the encoding of any
  small-field header list, through the deployed field decoder, returns the list.
* `decodeFieldV_encField` — the single-field core (reused by the client engine).

Grounded on `:method GET`, `:scheme https`, `:path /`, `host …` (`#guard`), so
the round-trip is not vacuous.
-/

namespace H2
namespace HpackEncode

open H2 H2.Conn

/-! ## The encoders (RFC 7541 §5.2, §6.2.2) -/

/-- Encode a byte string as an HPACK string literal (RFC 7541 §5.2): a 7-bit
length prefix (Huffman flag clear) then the raw octets. Requires `< 127` octets
so the length rides the prefix byte alone. -/
def encStr (s : Bytes) : Bytes := UInt8.ofNat s.length :: s

/-- Encode one header field as a literal-without-indexing, literal-name
representation (RFC 7541 §6.2.2): the `0x00` representation byte, the literal
name, then the literal value. -/
def encField (n v : Bytes) : Bytes := (0x00 : UInt8) :: (encStr n ++ encStr v)

/-- Encode a header list into an HPACK block. -/
def encodeHeaders : List (Bytes × Bytes) → Bytes
  | [] => []
  | (n, v) :: rest => encField n v ++ encodeHeaders rest

/-- Each field encodes to at least one octet, so a header list is never longer
than its encoding — the fuel bound the block loops need. -/
theorem length_le_encodeHeaders (hs : List (Bytes × Bytes)) :
    hs.length ≤ (encodeHeaders hs).length := by
  induction hs with
  | nil => simp only [encodeHeaders, List.length_nil, Nat.le_refl]
  | cons p rest ih =>
    obtain ⟨n, v⟩ := p
    simp only [encodeHeaders, encField, encStr, List.length_cons, List.length_append] at ih ⊢
    omega

/-! ## A list-valued decoder, looping the deployed field decoder

`decodeFieldV` (RFC 7541 §6, with the static + dynamic tables) decodes one field
representation. `decodeHeadersV` loops it, collecting `(name, value)` pairs in
wire order — the plain-list image of the connection engine's `decodeBlockV`
(which additionally routes pseudo-headers into a `Head`). The dynamic table is
fixed (`tbl`): the encoder never inserts, so no table state changes across the
block. -/
def decodeHeadersV (hd : Hpack.HuffmanDecoder) (tbl : List DynEntry) :
    Nat → Bytes → List (Bytes × Bytes) → Except Hpack.Err (List (Bytes × Bytes))
  | 0, _, _ => .error .truncated
  | fuel + 1, bs, acc =>
    match bs with
    | [] => .ok acc.reverse
    | b :: rest =>
      match decodeFieldV hd tbl (b :: rest) with
      | .error e => .error e
      | .ok (.fld n v _, k) =>
        decodeHeadersV hd tbl fuel ((b :: rest).drop (max k 1)) ((n, v) :: acc)
      | .ok (.sizeUpdate _, k) =>
        decodeHeadersV hd tbl fuel ((b :: rest).drop (max k 1)) acc

/-! ## String-literal round-trip -/

/-- `decStr` (with a 7-bit length prefix) inverts `encStr`: for any string under
the 7-bit length bound, the length prefix reads back exactly and no Huffman flag
is set. -/
theorem decStr_encStr (hd : Hpack.HuffmanDecoder) (s more : Bytes) (hs : s.length < 127) :
    Hpack.decStr hd 7 (UInt8.ofNat s.length) (s ++ more) = .ok (s, s.length) := by
  have hb : (UInt8.ofNat s.length : UInt8).toNat = s.length := by
    rw [UInt8.toNat_ofNat']; omega
  have hmod : (UInt8.ofNat s.length : UInt8).toNat % 2 ^ 7 = s.length := by rw [hb]; omega
  have hpre : Hpack.decPrefixInt 7 (UInt8.ofNat s.length) (s ++ more) = some (s.length, 0) := by
    unfold Hpack.decPrefixInt
    rw [if_pos (by rw [hmod]; omega), hmod]
  have htake : (s ++ more).take s.length = s := List.take_left ..
  unfold Hpack.decStr
  rw [hpre]
  simp only [List.drop_zero, htake, hb]
  rw [if_neg (by omega), if_neg (by omega), Nat.zero_add]

/-- `readStr` (the deployed HPACK string-literal decoder) inverts `encStr` for
any string under the 7-bit length bound, leaving the tail untouched. -/
theorem readStr_encStr (hd : Hpack.HuffmanDecoder) (s more : Bytes) (hs : s.length < 127) :
    Hpack.readStr hd (encStr s ++ more) = .ok (s, 1 + s.length) := by
  unfold encStr
  rw [List.cons_append]
  simp only [Hpack.readStr, decStr_encStr hd s more hs]

/-! ## Single-field round-trip (the client-engine core) -/

/-- **One literal field round-trips through the deployed decoder.** For a
`0x00`-representation literal field with small name and value, `decodeFieldV`
recovers exactly the name and value (no dynamic-table insert), consuming exactly
the field's octets, ahead of any following bytes. -/
theorem decodeFieldV_encField (hd : Hpack.HuffmanDecoder) (tbl : List DynEntry)
    (n v more : Bytes) (hn : n.length < 127) (hv : v.length < 127) :
    decodeFieldV hd tbl (encField n v ++ more)
      = .ok (.fld n v false, (encField n v).length) := by
  have hlen : (encField n v).length = 1 + (1 + n.length) + (1 + v.length) := by
    simp only [encField, encStr, List.length_cons, List.length_append]; omega
  have hb0 : ((0x00 : UInt8)).toNat = 0 := rfl
  have hassoc : encStr n ++ encStr v ++ more = encStr n ++ (encStr v ++ more) :=
    List.append_assoc _ _ _
  have hdrop : (encStr n ++ (encStr v ++ more)).drop (1 + n.length) = encStr v ++ more := by
    have hn' : (encStr n).length = 1 + n.length := by simp only [encStr, List.length_cons]; omega
    rw [← hn', List.drop_left]
  have hpi : Hpack.decPrefixInt 4 (0x00 : UInt8) (encStr n ++ encStr v ++ more)
      = some (0, 0) := by
    unfold Hpack.decPrefixInt
    rw [if_pos (by simp only [hb0]; omega)]
    simp only [hb0]
  have hcons : encField n v ++ more = (0x00 : UInt8) :: (encStr n ++ encStr v ++ more) := by
    simp only [encField, List.cons_append]
  rw [hcons]
  unfold decodeFieldV
  simp only [hb0]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hpi]
  dsimp only
  unfold litField
  rw [if_pos rfl, List.drop_zero, hassoc, readStr_encStr hd n (encStr v ++ more) hn]
  dsimp only
  rw [hdrop, readStr_encStr hd v more hv]
  refine congrArg Except.ok (Prod.ext rfl ?_)
  rw [hlen]

/-! ## The block round-trip -/

/-- The fold: decoding an encoded block accumulates exactly the encoded fields in
order (onto the reversed accumulator). -/
theorem decodeHeadersV_encodeHeaders (hd : Hpack.HuffmanDecoder) (tbl : List DynEntry)
    (hs : List (Bytes × Bytes))
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    ∀ (fuel : Nat) (acc : List (Bytes × Bytes)), hs.length < fuel →
      decodeHeadersV hd tbl fuel (encodeHeaders hs) acc = .ok (acc.reverse ++ hs) := by
  induction hs with
  | nil =>
    intro fuel acc hfuel
    cases fuel with
    | zero => omega
    | succ f => simp only [encodeHeaders, decodeHeadersV, List.append_nil]
  | cons p rest ih =>
    intro fuel acc hfuel
    obtain ⟨n, v⟩ := p
    have hp := hsmall (n, v) (List.mem_cons_self)
    have hrest : ∀ q ∈ rest, q.1.length < 127 ∧ q.2.length < 127 :=
      fun q hq => hsmall q (List.mem_cons_of_mem _ hq)
    cases fuel with
    | zero => simp only [List.length_cons] at hfuel; omega
    | succ f =>
      have hk : (encField n v).length = 1 + (1 + n.length) + (1 + v.length) := by
        simp only [encField, encStr, List.length_cons, List.length_append]; omega
      have hpos : 1 ≤ (encField n v).length := by omega
      have hfield := decodeFieldV_encField hd tbl n v (encodeHeaders rest) hp.1 hp.2
      have hne : encField n v ++ encodeHeaders rest = (0x00 : UInt8) :: (encStr n ++ encStr v ++ encodeHeaders rest) := by
        simp only [encField, List.cons_append, List.append_assoc]
      show decodeHeadersV hd tbl (f + 1) (encField n v ++ encodeHeaders rest) acc = _
      rw [hne]
      unfold decodeHeadersV
      dsimp only
      rw [← hne, hfield]
      dsimp only
      have hmax : max (encField n v).length 1 = (encField n v).length := by omega
      have hdrop : (encField n v ++ encodeHeaders rest).drop (encField n v).length
          = encodeHeaders rest := List.drop_left ..
      rw [hmax, hdrop]
      rw [ih hrest f ((n, v) :: acc) (by simp only [List.length_cons] at hfuel ⊢; omega)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- **The headline HPACK round-trip** (RFC 7541): decoding the encoding of any
header list whose names and values fit the 7-bit length prefix, through the
deployed field decoder, returns exactly the list — the HPACK analogue of the
frame `decode ∘ encode = id`. -/
theorem hpack_decode_encode (hd : Hpack.HuffmanDecoder) (tbl : List DynEntry)
    (hs : List (Bytes × Bytes)) (fuel : Nat)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127)
    (hfuel : hs.length < fuel) :
    decodeHeadersV hd tbl fuel (encodeHeaders hs) [] = .ok hs := by
  have := decodeHeadersV_encodeHeaders hd tbl hs hsmall fuel [] hfuel
  simpa using this

/-! ## A `decodeBlockV` step (reused to prove client↔server request agreement)

The connection engine's `decodeBlockV` walks the same field decoder into a
routed `Head`. A `0x00`-literal field advances it by exactly one field with no
dynamic-table change — the lemma the client-agreement proof steps with. -/
theorem decodeBlockV_encField (hd : Hpack.HuffmanDecoder) (fuel : Nat) (ctx : HpackCtx)
    (n v more : Bytes) (acc : Head) (sawReg seenField : Bool)
    (hn : n.length < 127) (hv : v.length < 127) :
    decodeBlockV hd (fuel + 1) ctx (encField n v ++ more) acc sawReg seenField
      = decodeBlockV hd fuel ctx more (acc.addField sawReg n v)
          (sawReg || !(n.head? = some 0x3a)) true := by
  have hpos : 1 ≤ (encField n v).length := by simp only [encField, List.length_cons]; omega
  have hfield := decodeFieldV_encField hd ctx.tbl n v more hn hv
  have hdrop : (encField n v ++ more).drop (encField n v).length = more := List.drop_left ..
  have hmax : max (encField n v).length 1 = (encField n v).length := by omega
  -- One definitional step of `decodeBlockV` on a `succ` fuel and a cons buffer,
  -- keeping the field decode symbolic (the `::`/`++` match reduces up to defeq).
  have step : decodeBlockV hd (fuel + 1) ctx (encField n v ++ more) acc sawReg seenField
      = (match decodeFieldV hd ctx.tbl (encField n v ++ more) with
         | .error e => .error e
         | .ok (fs, k) =>
           match fs with
           | .sizeUpdate w =>
             if seenField then .error .dynamicUnsupported
             else if ourHeaderTableSize < w then .error .dynamicUnsupported
             else decodeBlockV hd fuel { tbl := trimTable (ctx.tbl.length + 1) w ctx.tbl, cap := w }
               ((encField n v ++ more).drop (max k 1)) acc sawReg seenField
           | .fld name value ins =>
             decodeBlockV hd fuel
               (if ins then { ctx with tbl := insertEntry ctx.cap ctx.tbl (name, value) } else ctx)
               ((encField n v ++ more).drop (max k 1)) (acc.addField sawReg name value)
               (sawReg || !(name.head? = some 0x3a)) true) := rfl
  rw [step, hfield]
  dsimp only
  rw [hmax, hdrop, if_neg (show ¬ (false = true) by decide)]

/-- The routing-fold: applying the engine's `Head.addField` to each field in wire
order (tracking the §8.3 pseudo-after-regular flag), reversing the ordinary
fields at the end (as `decodeBlockV`'s `[]` case does). -/
def stepHead : Head → Bool → List (Bytes × Bytes) → Head
  | acc, _, [] => { acc with fields := acc.fields.reverse }
  | acc, sawReg, (n, v) :: rest =>
    stepHead (acc.addField sawReg n v) (sawReg || !(n.head? = some 0x3a)) rest

/-- **The connection engine decodes the encoded block faithfully** (RFC 7541 +
RFC 9113 §8.3): the server's own `decodeBlockV` on a client-encoded block yields
exactly the routing-fold of the header list into a `Head` — no dynamic-table
change (the encoder never inserts). This is the request head the server hands its
handler, tied to the exact bytes the client sent. -/
theorem decodeBlockV_encodeHeaders (hd : Hpack.HuffmanDecoder)
    (hs : List (Bytes × Bytes))
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    ∀ (fuel : Nat) (ctx : HpackCtx) (acc : Head) (sawReg seenField : Bool), hs.length < fuel →
      decodeBlockV hd fuel ctx (encodeHeaders hs) acc sawReg seenField
        = .ok (stepHead acc sawReg hs, ctx) := by
  induction hs with
  | nil =>
    intro fuel ctx acc sawReg seenField hfuel
    cases fuel with
    | zero => omega
    | succ f => simp only [encodeHeaders, decodeBlockV, stepHead]
  | cons p rest ih =>
    intro fuel ctx acc sawReg seenField hfuel
    obtain ⟨n, v⟩ := p
    have hp := hsmall (n, v) (List.mem_cons_self)
    have hrest : ∀ q ∈ rest, q.1.length < 127 ∧ q.2.length < 127 :=
      fun q hq => hsmall q (List.mem_cons_of_mem _ hq)
    cases fuel with
    | zero => simp only [List.length_cons] at hfuel; omega
    | succ f =>
      show decodeBlockV hd (f + 1) ctx (encField n v ++ encodeHeaders rest) acc sawReg seenField = _
      rw [decodeBlockV_encField hd f ctx n v (encodeHeaders rest) acc sawReg seenField hp.1 hp.2,
        ih hrest f ctx (acc.addField sawReg n v) (sawReg || !(n.head? = some 0x3a)) true
          (by simp only [List.length_cons] at hfuel; omega)]
      rfl

/-! ## Wire vectors, checker-verified (the round-trips are not vacuous)

Grounded on a realistic request — `:method GET`, `:scheme https`, `:path /`,
`host a` — spelled as explicit octets so the round-trip discharges concretely. -/

/-- A realistic request header list (explicit ASCII octets). -/
private def reqHeaders : List (Bytes × Bytes) :=
  [([0x3a, 0x6d, 0x65, 0x74, 0x68, 0x6f, 0x64], [0x47, 0x45, 0x54]),  -- ":method" "GET"
   ([0x3a, 0x73, 0x63, 0x68, 0x65, 0x6d, 0x65], [0x68, 0x74, 0x74, 0x70, 0x73]),  -- ":scheme" "https"
   ([0x3a, 0x70, 0x61, 0x74, 0x68], [0x2f]),  -- ":path" "/"
   ([0x68, 0x6f, 0x73, 0x74], [0x61])]  -- "host" "a"

private def rejectAll : Hpack.HuffmanDecoder := ⟨fun _ => none⟩

/-- The concrete request block round-trips through the deployed field decoder:
`decode ∘ encode = id` on a real request header list. -/
example : decodeHeadersV rejectAll [] 32 (encodeHeaders reqHeaders) [] = .ok reqHeaders :=
  hpack_decode_encode rejectAll [] reqHeaders 32 (by decide) (by decide)

/-- One literal `:path /` field decodes to exactly its name/value, no table
change — the single-field core, discharged concretely. -/
example : decodeFieldV rejectAll [] (encField [0x3a, 0x70, 0x61, 0x74, 0x68] [0x2f] ++ [])
    = .ok (.fld [0x3a, 0x70, 0x61, 0x74, 0x68] [0x2f] false,
        (encField [0x3a, 0x70, 0x61, 0x74, 0x68] [0x2f]).length) :=
  decodeFieldV_encField rejectAll [] [0x3a, 0x70, 0x61, 0x74, 0x68] [0x2f] [] (by decide) (by decide)

end HpackEncode
end H2
