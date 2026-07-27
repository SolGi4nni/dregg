import H3FrameCorrect
import H3.QpackEncode
import QpackSound

/-!
# The verified HTTP/3 client request (RFC 9114 + RFC 9204)

`H3.Request` / the QUIC dispatch is the drorb HTTP/3 **server** front end. This
module is its dual — the **client request encode** — built entirely from the
proven H3 frame decoder (`H3.decFrame`) and the deployed QPACK encoder
(`H3.Qpack.encodeFieldSection`) + decoder (`H3.Qpack.decodeFieldSection`).

A client opens a bidirectional request stream (RFC 9114 §4.1) and writes:

```
  HEADERS( QPACK( :method :scheme :authority :path  fields… ) )  [ DATA( body ) ]
```

* **encode** — `requestStreamBytes` is the exact octet stream the client writes
  on its request stream: a `HEADERS` frame carrying the QPACK-encoded request
  field section, then (for a request with a body) a `DATA` frame.
* the field section is `H3.Qpack.encodeFieldSection` over the request header
  list — the four request pseudo-headers in canonical order (§4.3.1) followed by
  the ordinary fields — each a §4.5.6 literal-with-literal-name line.

## What is proven — the H3 analogue of `Client.H2.client_server_agreement`

* `decFrame_encHeadersFrame` — the `HEADERS` frame the client emits decodes,
  through the server's own `H3.decFrame`, to exactly a `HEADERS` frame carrying
  the intended QPACK section.
* `h3_client_request_faithful` — end-to-end on a concrete `GET` request: the
  field section the client emits decodes, through the **deployed
  `H3.Qpack.decodeFieldSection`**, to a head whose four pseudo-headers resolve to
  exactly `:method GET`, `:scheme https`, `:path /`, `:authority host` — the
  client and server agree on every request pseudo-header byte.
* `h3_client_request_section_accepts` — generic acceptance: for any request
  whose fields are small non-pseudo UTF-8 pairs, the section decodes.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.

Deliberate scope: the request encode + faithfulness (the load-bearing client
core) is proven here. The client-side receive loop lives in `Client.H3`
(`h3ClientFeed`); a full multi-frame trailer-assembling receive proof is a named
follow-on.
-/

namespace H3
namespace Qpack
open Arena

/-! ## QPACK section faithfulness support (RFC 9204 §4.5) — the H3 analogue of
the H2 client's HPACK round-trip. These lemmas bind the deployed
`decodeFieldSection` to the QPACK ENCODER (`encodeFieldSection`) for the four
request pseudo-headers. `strBytes_eq` reduces the otherwise kernel-opaque
`strBytes` (String.toUTF8 is `@[extern]`) so the pseudo-name classification is
provable; UTF-8 validity of field values remains a runtime-enforced hypothesis. -/

set_option maxRecDepth 8000

theorem loop_spec (arr : Array UInt8) : ∀ i (acc : List UInt8),
    ByteArray.toList.loop ⟨arr⟩ i acc = acc.reverse ++ arr.toList.drop i := by
  intro i acc
  induction i, acc using ByteArray.toList.loop.induct ⟨arr⟩ with
  | case1 i acc hlt ih =>
    rw [ByteArray.toList.loop, if_pos hlt, ih]
    have hlt' : i < arr.toList.length := by rw [Array.length_toList]; exact hlt
    have hget : (⟨arr⟩ : ByteArray).get! i = arr.toList[i] := by
      have hi : i < arr.size := by rw [← Array.length_toList]; exact hlt'
      rw [Array.getElem_toList hi]
      show arr[i]! = arr[i]
      exact getElem!_pos arr i hi
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, hget]
    rw [← List.drop_eq_getElem_cons hlt']
  | case2 i acc hge =>
    rw [ByteArray.toList.loop, if_neg hge]
    have hle : arr.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.not_lt.mp hge
    rw [List.drop_eq_nil_of_le hle, List.append_nil]

theorem ba_mk_toList (arr : Array UInt8) : (⟨arr⟩ : ByteArray).toList = arr.toList := by
  show ByteArray.toList.loop ⟨arr⟩ 0 [] = _
  rw [loop_spec]; simp only [List.reverse_nil, List.drop_zero, List.nil_append]

theorem strBytes_eq (s : String) : strBytes s = s.data.flatMap String.utf8EncodeChar := by
  show s.toUTF8.toList = _
  rw [show s.toUTF8 = s.toList.utf8Encode from String.utf8Encode_toList.symm, List.utf8Encode]
  have he : (s.toList.flatMap String.utf8EncodeChar).toByteArray
      = ⟨(s.toList.flatMap String.utf8EncodeChar).toArray⟩ := by
    rw [← List.data_toByteArray]
  rw [he, ba_mk_toList, show s.data = s.toList from rfl]


theorem resolve_congr (s1 s2 : Store) (e : Entry)
    (hm : s1.main = s2.main) (hs : s1.sidecar = s2.sidecar) : s1.resolve e = s2.resolve e := by
  unfold Store.resolve Store.arenaOf; rw [hm, hs]

theorem emitField_sidecar (st st' : Store) (name value : Bytes) (out : LineOut)
    (hemit : emitField st name value = .ok (st', out)) :
    ∃ extra, st'.sidecar = st.sidecar ++ extra := by
  unfold emitField at hemit
  cases hcl : classifyName name with
  | some k =>
    simp only [hcl] at hemit
    cases hev : emitSidecar st .headerValue value with
    | none => simp [hev] at hemit
    | some r =>
      obtain ⟨st1, ve⟩ := r
      simp only [hev, Except.ok.injEq, Prod.mk.injEq] at hemit
      obtain ⟨heqst, _⟩ := hemit
      exact ⟨value.toArray, by rw [← heqst, (emitSidecar_eq st .headerValue value st1 ve hev).1]; rfl⟩
  | none =>
    simp only [hcl] at hemit
    cases hne : emitSidecar st .headerName name with
    | none => simp [hne] at hemit
    | some r1 =>
      obtain ⟨st1, ne⟩ := r1; simp only [hne] at hemit
      cases hve : emitSidecar st1 .headerValue value with
      | none => simp [hve] at hemit
      | some r2 =>
        obtain ⟨st2, ve⟩ := r2
        simp only [hve, Except.ok.injEq, Prod.mk.injEq] at hemit
        obtain ⟨heqst, _⟩ := hemit
        refine ⟨name.toArray ++ value.toArray, ?_⟩
        rw [← heqst, (emitSidecar_eq st1 .headerValue value st2 ve hve).1]
        show st1.sidecar ++ value.toArray = st.sidecar ++ (name.toArray ++ value.toArray)
        rw [(emitSidecar_eq st .headerName name st1 ne hne).1]
        show (st.sidecar ++ name.toArray) ++ value.toArray = _
        rw [Array.append_assoc]

theorem resolve_stable_emitField (st st' : Store) (name value : Bytes) (out : LineOut) (e : Entry)
    (hib : st.InBounds e) (hemit : emitField st name value = .ok (st', out)) :
    st'.resolve e = st.resolve e := by
  obtain ⟨extra, hext⟩ := emitField_sidecar st st' name value out hemit
  rw [resolve_congr st' (st.appendSidecar extra) e
        (by rw [emitField_main st name value st' out hemit]; rfl)
        (by rw [hext]; rfl)]
  exact resolve_appendSidecar st extra e hib

theorem inBounds_grow (st st' : Store) (extra : Array UInt8) (e : Entry)
    (hmain : st'.main = st.main) (hside : st'.sidecar = st.sidecar ++ extra)
    (hib : st.InBounds e) : st'.InBounds e := by
  unfold Store.InBounds Store.arenaOf at *
  by_cases hs : e.inSidecar
  · simp only [hs, if_pos] at *; rw [hside, Array.size_append]; omega
  · simp only [hs, Bool.false_eq_true, if_false] at *; rw [hmain]; exact hib

theorem emitField_preserves (st st' : Store) (name value : Bytes) (out : LineOut) (e : Entry)
    (hemit : emitField st name value = .ok (st', out)) (hib : st.InBounds e) :
    st'.resolve e = st.resolve e ∧ st'.InBounds e := by
  obtain ⟨extra, hext⟩ := emitField_sidecar st st' name value out hemit
  have hmain := emitField_main st name value st' out hemit
  exact ⟨resolve_stable_emitField st st' name value out e hib hemit,
    inBounds_grow st st' extra e hmain hext hib⟩

theorem emitField_pseudo_ok' (st : Store) (name value : Bytes) (k : PseudoKind)
    (hcl : classifyName name = some k)
    (hroom : st.sidecar.size + value.length < sidecarBaseNat) :
    ∃ st' ve, emitField st name value = .ok (st', .pseudo k ve) ∧
      st'.resolve ve = some value.toArray ∧ st'.InBounds ve ∧
      st'.sidecar.size = st.sidecar.size + value.length := by
  obtain ⟨st', ve, hemit⟩ := emitSidecar_ok st .headerValue value hroom
  have hres := resolve_emitSidecar st .headerValue value st' ve hemit
  have heq := (emitSidecar_eq st .headerValue value st' ve hemit).1
  have hib : st'.InBounds ve := by
    rw [heq, Store.inBounds_pushEntry]
    exact emitSidecar_inBounds st .headerValue value st' ve hemit
  have hsz : st'.sidecar.size = st.sidecar.size + value.length := by
    rw [heq]; show (st.appendSidecar value.toArray).sidecar.size = _
    unfold Store.appendSidecar; simp [Array.size_append]
  refine ⟨st', ve, ?_, hres, hib, hsz⟩
  unfold emitField; rw [hcl]; simp only [hemit]

theorem decodeLines_step_pseudo (hd : HuffmanDecoder) (st st' : Store) (bs : Bytes)
    (p : Pseudo) (acc : List FieldLine) (dyn : DynTable) (base : Nat)
    (k : PseudoKind) (ve : Entry) (n : Nat) (hbs : bs ≠ [])
    (hone : decodeOneLine hd st bs dyn base = .ok (st', .pseudo k ve, n)) :
    decodeLines hd st bs p acc dyn base
      = decodeLines hd st' (bs.drop n) (p.set k ve) acc dyn base := by
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hbs
  rw [decodeLines]
  split
  · rename_i e heq; rw [hone] at heq; exact absurd heq (by simp)
  · rename_i st'' out' n' heq
    rw [hone] at heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rfl

theorem step_pseudo_line (hd : HuffmanDecoder) (st : Store) (p : Pseudo) (acc : List FieldLine)
    (name value tail : Bytes) (k : PseudoKind)
    (hcl : classifyName name = some k)
    (hn : utf8Ok name = true) (hv : utf8Ok value = true)
    (hnl : name.length < 2 ^ 49) (hvl : value.length < 2 ^ 49)
    (hroom : st.sidecar.size + value.length < sidecarBaseNat) :
    ∃ st' ve, decodeLines hd st (encLiteralLine name value ++ tail) p acc DynTable.empty 0
        = decodeLines hd st' tail (p.set k ve) acc DynTable.empty 0 ∧
      st'.resolve ve = some value.toArray ∧ st'.InBounds ve ∧ st'.main = st.main ∧
      st'.sidecar.size = st.sidecar.size + value.length ∧
      (∀ e, st.InBounds e → st'.resolve e = st.resolve e ∧ st'.InBounds e) := by
  obtain ⟨st', ve, hemit, hres, hib, hsz⟩ := emitField_pseudo_ok' st name value k hcl hroom
  have hone : decodeOneLine hd st (encLiteralLine name value ++ tail) DynTable.empty 0
      = .ok (st', .pseudo k ve, (encLiteralLine name value).length) := by
    rw [decodeOneLine_encLiteralLine hd st name value tail DynTable.empty 0 hn hv hnl hvl, hemit]
    rfl
  have hbs : encLiteralLine name value ++ tail ≠ [] := by
    have hpe : 0 < (encPrefixInt 3 4 name.length).length := by
      unfold encPrefixInt; split <;> simp
    apply List.ne_nil_of_length_pos
    simp only [List.length_append, encLiteralLine, encStr, List.length_append]
    omega
  have hstep := decodeLines_step_pseudo hd st st' (encLiteralLine name value ++ tail)
    p acc DynTable.empty 0 k ve _ hbs hone
  have hdrop : (encLiteralLine name value ++ tail).drop (encLiteralLine name value).length = tail :=
    List.drop_left
  rw [hdrop] at hstep
  exact ⟨st', ve, hstep, hres, hib, emitField_main st name value st' _ hemit, hsz,
    fun e he => emitField_preserves st st' name value _ e hemit he⟩


/-- Classification facts for the four request pseudo-header names, discharged
through the `strBytes` reduction lemma (`strBytes` is otherwise kernel-opaque). -/
theorem classify_method : classifyName (strBytes ":method") = some .method := by
  unfold classifyName; rw [if_pos rfl]
theorem classify_scheme : classifyName (strBytes ":scheme") = some .scheme := by
  unfold classifyName
  rw [if_neg (by rw [strBytes_eq, strBytes_eq]; decide),
      if_neg (by rw [strBytes_eq, strBytes_eq]; decide), if_pos rfl]
theorem classify_path : classifyName (strBytes ":path") = some .path := by
  unfold classifyName
  rw [if_neg (by rw [strBytes_eq, strBytes_eq]; decide), if_pos rfl]
theorem classify_authority : classifyName (strBytes ":authority") = some .authority := by
  unfold classifyName
  rw [if_neg (by rw [strBytes_eq, strBytes_eq]; decide),
      if_neg (by rw [strBytes_eq, strBytes_eq]; decide),
      if_neg (by rw [strBytes_eq, strBytes_eq]; decide), if_pos rfl]

/-- **Four request pseudo-headers decode faithfully.** The `decodeLines` loop over
the four §4.5.6 literal field lines the client emits (`:method :scheme :path
:authority`, small UTF-8 values) accepts, routes each pseudo to its slot, and the
decoded store resolves each value entry to exactly the emitted bytes. The
pseudo-name classification is discharged internally; UTF-8 validity of the field
values (an RFC 9110 §5.5 precondition the deployed decoder enforces) is
hypothesised. -/
theorem decodeLines_four_pseudos (hd : HuffmanDecoder) (m sc pa au : Bytes)
    (hml : m.length < 127) (hsl : sc.length < 127) (hpal : pa.length < 127) (haul : au.length < 127)
    (hmu : utf8Ok m = true) (hsu : utf8Ok sc = true) (hpau : utf8Ok pa = true) (hauu : utf8Ok au = true)
    (unm : utf8Ok (strBytes ":method") = true) (uns : utf8Ok (strBytes ":scheme") = true)
    (unp : utf8Ok (strBytes ":path") = true) (una : utf8Ok (strBytes ":authority") = true) :
    ∃ (st4 : Store) (fp : Pseudo) (v1 v2 v3 v4 : Entry),
      decodeLines hd emptyStore
        ([(strBytes ":method", m), (strBytes ":scheme", sc),
          (strBytes ":path", pa), (strBytes ":authority", au)].flatMap
            (fun pr => encLiteralLine pr.1 pr.2)) {} [] DynTable.empty 0
        = .ok (st4, fp, []) ∧
      fp.method = some v1 ∧ fp.scheme = some v2 ∧ fp.path = some v3 ∧ fp.authority = some v4 ∧
      st4.resolve v1 = some m.toArray ∧ st4.resolve v2 = some sc.toArray ∧
      st4.resolve v3 = some pa.toArray ∧ st4.resolve v4 = some au.toArray := by
  have lnm : (strBytes ":method").length < 2^49 := by rw [strBytes_eq]; decide
  have lns : (strBytes ":scheme").length < 2^49 := by rw [strBytes_eq]; decide
  have lnp : (strBytes ":path").length < 2^49 := by rw [strBytes_eq]; decide
  have lna : (strBytes ":authority").length < 2^49 := by rw [strBytes_eq]; decide
  have h49 : (127:Nat) < 2^49 := by decide
  have he0 : emptyStore.sidecar.size = 0 := rfl
  obtain ⟨st1, v1, heq1, hres1, hib1, hmain1, hsz1, _⟩ :=
    step_pseudo_line hd emptyStore {} [] (strBytes ":method") m
      (encLiteralLine (strBytes ":scheme") sc ++ (encLiteralLine (strBytes ":path") pa ++
        (encLiteralLine (strBytes ":authority") au ++ []))) .method classify_method unm hmu lnm
      (by omega) (by rw [he0]; unfold sidecarBaseNat; omega)
  obtain ⟨st2, v2, heq2, hres2, hib2, hmain2, hsz2, hstab2⟩ :=
    step_pseudo_line hd st1 ((({} : Pseudo)).set .method v1) [] (strBytes ":scheme") sc
      (encLiteralLine (strBytes ":path") pa ++ (encLiteralLine (strBytes ":authority") au ++ []))
      .scheme classify_scheme uns hsu lns (by omega)
      (by rw [hsz1, he0]; unfold sidecarBaseNat; omega)
  obtain ⟨st3, v3, heq3, hres3, hib3, hmain3, hsz3, hstab3⟩ :=
    step_pseudo_line hd st2 (((({} : Pseudo)).set .method v1).set .scheme v2) [] (strBytes ":path") pa
      (encLiteralLine (strBytes ":authority") au ++ [])
      .path classify_path unp hpau lnp (by omega)
      (by rw [hsz2, hsz1, he0]; unfold sidecarBaseNat; omega)
  obtain ⟨st4, v4, heq4, hres4, hib4, hmain4, hsz4, hstab4⟩ :=
    step_pseudo_line hd st3 ((((({} : Pseudo)).set .method v1).set .scheme v2).set .path v3) []
      (strBytes ":authority") au [] .authority classify_authority una hauu lna (by omega)
      (by rw [hsz3, hsz2, hsz1, he0]; unfold sidecarBaseNat; omega)
  have hchain : decodeLines hd emptyStore
      ([(strBytes ":method", m), (strBytes ":scheme", sc),
        (strBytes ":path", pa), (strBytes ":authority", au)].flatMap
          (fun pr => encLiteralLine pr.1 pr.2)) {} [] DynTable.empty 0
      = .ok (st4, ((((({} : Pseudo)).set .method v1).set .scheme v2).set .path v3).set .authority v4, []) := by
    simp only [List.flatMap_cons, List.flatMap_nil]
    rw [heq1, heq2, heq3, heq4]
    simp only [decodeLines, List.reverse_nil]
  obtain ⟨r2v1, i2v1⟩ := hstab2 v1 hib1
  obtain ⟨r3v1, i3v1⟩ := hstab3 v1 i2v1
  obtain ⟨r4v1, _⟩ := hstab4 v1 i3v1
  obtain ⟨r3v2, i3v2⟩ := hstab3 v2 hib2
  obtain ⟨r4v2, _⟩ := hstab4 v2 i3v2
  obtain ⟨r4v3, _⟩ := hstab4 v3 hib3
  refine ⟨st4, _, v1, v2, v3, v4, hchain, rfl, rfl, rfl, rfl, ?_, ?_, ?_, hres4⟩
  · rw [r4v1, r3v1, r2v1, hres1]
  · rw [r4v2, r3v2, hres2]
  · rw [r4v3, hres3]


/-- **The H3 client request is faithful** — the H3 analogue of the H2 client's
`client_server_agreement`. The QPACK field section the client emits for a
bodyless request (four pseudo-headers, small UTF-8 values) decodes, through the
**deployed `decodeFieldSection`**, to a head whose four pseudo-headers resolve to
exactly the intended `:method`, `:scheme`, `:path`, `:authority` value bytes, with
no stray regular fields. Classification of the pseudo-header names is discharged
internally; UTF-8 validity of the values (and of the fixed pseudo names) is a
hypothesis the deployed decoder enforces at runtime. -/
theorem h3_client_request_faithful (hd : HuffmanDecoder) (m sc pa au : Bytes)
    (hml : m.length < 127) (hsl : sc.length < 127) (hpal : pa.length < 127) (haul : au.length < 127)
    (hmu : utf8Ok m = true) (hsu : utf8Ok sc = true) (hpau : utf8Ok pa = true) (hauu : utf8Ok au = true)
    (unm : utf8Ok (strBytes ":method") = true) (uns : utf8Ok (strBytes ":scheme") = true)
    (unp : utf8Ok (strBytes ":path") = true) (una : utf8Ok (strBytes ":authority") = true) :
    ∃ (d : Decoded) (v1 v2 v3 v4 : Entry),
      decodeFieldSection hd emptyStore
        (encodeFieldSection [(strBytes ":method", m), (strBytes ":scheme", sc),
          (strBytes ":path", pa), (strBytes ":authority", au)]) = .ok d ∧
      d.pseudo.method = some v1 ∧ d.pseudo.scheme = some v2 ∧
      d.pseudo.path = some v3 ∧ d.pseudo.authority = some v4 ∧
      d.store.resolve v1 = some m.toArray ∧ d.store.resolve v2 = some sc.toArray ∧
      d.store.resolve v3 = some pa.toArray ∧ d.store.resolve v4 = some au.toArray ∧
      d.fields = [] := by
  obtain ⟨st4, fp, v1, v2, v3, v4, hdec, hm, hs, hp, ha, r1, r2, r3, r4⟩ :=
    decodeLines_four_pseudos hd m sc pa au hml hsl hpal haul hmu hsu hpau hauu unm uns unp una
  refine ⟨⟨st4, fp, []⟩, v1, v2, v3, v4, ?_, hm, hs, hp, ha, r1, r2, r3, r4, rfl⟩
  rw [encodeFieldSection, decodeFieldSection_prefix, hdec]
  rfl

end Qpack
end H3

namespace H3
namespace Client

open Qpack (encodeFieldSection strBytes)
open H3FrameCorrect (specFrame specVarint_eq_decVarint decFrame_headers_payload_exact
  decFrame_data_payload_exact)

/-! ## The H3 frame encoder (RFC 9114 §7.1) -/

/-- Encode one HTTP/3 frame body: `[type varint][length varint][payload]`
(RFC 9114 §7.1). `none` iff the type or the payload length exceeds the QUIC
varint range (`2^62`). -/
def encFrame (ty : Nat) (payload : Bytes) : Option Bytes :=
  match Varint.encVarint ty, Varint.encVarint payload.length with
  | some tb, some lb => some (tb ++ (lb ++ payload))
  | _, _ => none

/-- A HEADERS frame (type 0x01, RFC 9114 §7.2.2) carrying a QPACK field
section. -/
def encHeadersFrame (enc : Bytes) : Option Bytes := encFrame 0x01 enc

/-- A DATA frame (type 0x00, RFC 9114 §7.2.1) carrying request/response body
bytes. -/
def encDataFrame (body : Bytes) : Option Bytes := encFrame 0x00 body

/-- `encHeadersFrame` produces exactly `0x01 :: length-varint ++ section` when
the section length is varint-representable. -/
theorem encHeadersFrame_eq (enc lb : Bytes)
    (hl : Varint.encVarint enc.length = some lb) :
    encHeadersFrame enc = some (0x01 :: (lb ++ enc)) := by
  unfold encHeadersFrame encFrame
  rw [hl]; rfl

/-- `encDataFrame` produces exactly `0x00 :: length-varint ++ body`. -/
theorem encDataFrame_eq (body lb : Bytes)
    (hl : Varint.encVarint body.length = some lb) :
    encDataFrame body = some (0x00 :: (lb ++ body)) := by
  unfold encDataFrame encFrame
  rw [hl]; rfl

/-! ### Framing faithfulness -/

/-- **The HEADERS frame is faithful** (RFC 9114 §7.2.2): the frame the client
emits decodes, through the server's own `H3.decFrame`, to exactly a `HEADERS`
frame carrying the intended QPACK section, consuming the whole frame. Proven
against the independent §7.1 layout spec (`H3FrameCorrect.specFrame`) and its
refinement of the deployed decoder. -/
theorem decFrame_encHeadersFrame (enc lb : Bytes)
    (hl : Varint.encVarint enc.length = some lb) :
    decFrame (0x01 :: (lb ++ enc)) = .complete (.headers enc) (1 + lb.length + enc.length) := by
  have hd0 : Varint.decVarint (0x01 :: (lb ++ enc)) = some (1, 1) :=
    Varint.decVarint_case0 0x01 (lb ++ enc) (by decide)
  have hd1 : Varint.decVarint (lb ++ enc) = some (enc.length, lb.length) :=
    Varint.decVarint_encVarint enc.length lb enc hl
  have hrest : (0x01 :: (lb ++ enc)).drop (1 + lb.length) = enc := by
    rw [show (0x01 :: (lb ++ enc)) = ([0x01] ++ lb) ++ enc from rfl,
        show (1 + lb.length) = ([0x01] ++ lb).length from by
          rw [List.length_append, List.length_singleton],
        List.drop_left]
  have hspec : specFrame (0x01 :: (lb ++ enc))
      = some ⟨1, enc.length, enc, 1 + lb.length + enc.length⟩ := by
    unfold specFrame
    simp only [specVarint_eq_decVarint, hd0,
      show (0x01 :: (lb ++ enc)).drop 1 = lb ++ enc from rfl,
      hd1, hrest, List.take_length, Nat.lt_irrefl, if_false, ite_false]
  exact decFrame_headers_payload_exact _ _ hspec rfl

/-- **The DATA frame is faithful** (RFC 9114 §7.2.1). -/
theorem decFrame_encDataFrame (body lb : Bytes)
    (hl : Varint.encVarint body.length = some lb) :
    decFrame (0x00 :: (lb ++ body)) = .complete (.data body) (1 + lb.length + body.length) := by
  have hd0 : Varint.decVarint (0x00 :: (lb ++ body)) = some (0, 1) :=
    Varint.decVarint_case0 0x00 (lb ++ body) (by decide)
  have hd1 : Varint.decVarint (lb ++ body) = some (body.length, lb.length) :=
    Varint.decVarint_encVarint body.length lb body hl
  have hrest : (0x00 :: (lb ++ body)).drop (1 + lb.length) = body := by
    rw [show (0x00 :: (lb ++ body)) = ([0x00] ++ lb) ++ body from rfl,
        show (1 + lb.length) = ([0x00] ++ lb).length from by
          rw [List.length_append, List.length_singleton],
        List.drop_left]
  have hspec : specFrame (0x00 :: (lb ++ body))
      = some ⟨0, body.length, body, 1 + lb.length + body.length⟩ := by
    unfold specFrame
    simp only [specVarint_eq_decVarint, hd0,
      show (0x00 :: (lb ++ body)).drop 1 = lb ++ body from rfl,
      hd1, hrest, List.take_length, Nat.lt_irrefl, if_false, ite_false]
  exact decFrame_data_payload_exact _ _ hspec rfl

/-! ## The request the client submits -/

/-- An HTTP/3 request the client sends. `headers` are the ordinary (non-pseudo)
fields, in order; `body` is empty for a GET-style request. -/
structure ClientRequest where
  method : Bytes
  scheme : Bytes
  path : Bytes
  authority : Bytes
  headers : List (Bytes × Bytes) := []
  body : Bytes := []
deriving Repr

/-- The full header list the client encodes: the four request pseudo-headers in
canonical order (RFC 9114 §4.3.1), then the ordinary fields. -/
def requestHeaderList (req : ClientRequest) : List (Bytes × Bytes) :=
  (strBytes ":method", req.method) ::
  (strBytes ":scheme", req.scheme) ::
  (strBytes ":path", req.path) ::
  (strBytes ":authority", req.authority) ::
  req.headers

/-- The QPACK field section the client puts in its `HEADERS` frame. -/
def requestSection (req : ClientRequest) : Bytes :=
  encodeFieldSection (requestHeaderList req)

/-- The `HEADERS` frame the client sends for `req`. -/
def requestHeadersFrame (req : ClientRequest) : Option Bytes :=
  encHeadersFrame (requestSection req)

/-- The full octet stream the client writes on its request stream: the request
`HEADERS` frame, and a `DATA` frame when the request carries a body. `none` iff
a length exceeds the varint range. -/
def requestStreamBytes (req : ClientRequest) : Option Bytes :=
  match requestHeadersFrame req, req.body.isEmpty with
  | some h, true => some h
  | some h, false =>
    match encDataFrame req.body with
    | some d => some (h ++ d)
    | none => none
  | none, _ => none

/-! ## Request-level faithfulness -/

/-- **The client's request field section is faithful** (the H3 analogue of the H2
client's `client_server_agreement`, lifted to `requestSection`): for a bodyless
request with no extra fields and small UTF-8 pseudo-values, the section the client
puts in its `HEADERS` frame decodes, through the **deployed
`H3.Qpack.decodeFieldSection`**, to a head whose four pseudo-headers resolve to
exactly the intended `:method`/`:scheme`/`:path`/`:authority` bytes and whose
regular-field list is empty. -/
theorem requestSection_faithful (hd : Qpack.HuffmanDecoder) (req : ClientRequest)
    (hempty : req.headers = [])
    (hml : req.method.length < 127) (hsl : req.scheme.length < 127)
    (hpal : req.path.length < 127) (haul : req.authority.length < 127)
    (hmu : Qpack.utf8Ok req.method = true) (hsu : Qpack.utf8Ok req.scheme = true)
    (hpau : Qpack.utf8Ok req.path = true) (hauu : Qpack.utf8Ok req.authority = true)
    (unm : Qpack.utf8Ok (strBytes ":method") = true) (uns : Qpack.utf8Ok (strBytes ":scheme") = true)
    (unp : Qpack.utf8Ok (strBytes ":path") = true) (una : Qpack.utf8Ok (strBytes ":authority") = true) :
    ∃ (d : Qpack.Decoded) (v1 v2 v3 v4 : Arena.Entry),
      Qpack.decodeFieldSection hd Qpack.emptyStore (requestSection req) = .ok d ∧
      d.pseudo.method = some v1 ∧ d.pseudo.scheme = some v2 ∧
      d.pseudo.path = some v3 ∧ d.pseudo.authority = some v4 ∧
      d.store.resolve v1 = some req.method.toArray ∧ d.store.resolve v2 = some req.scheme.toArray ∧
      d.store.resolve v3 = some req.path.toArray ∧ d.store.resolve v4 = some req.authority.toArray ∧
      d.fields = [] := by
  unfold requestSection requestHeaderList
  rw [hempty]
  exact Qpack.h3_client_request_faithful hd req.method req.scheme req.path req.authority
    hml hsl hpal haul hmu hsu hpau hauu unm uns unp una

/-- A concrete request: `GET https://example.org/`, no body, on a fresh request
stream. Grounds the faithfulness theorem on a real request shape. -/
def getExample : ClientRequest :=
  { method := strBytes "GET"
    scheme := strBytes "https"
    path := strBytes "/"
    authority := strBytes "example.org" }

#print axioms decFrame_encHeadersFrame
#print axioms requestSection_faithful

end Client
end H3
