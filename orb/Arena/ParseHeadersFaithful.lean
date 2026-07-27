/-
Arena — the HEADER-LIST faithfulness lift.

`Arena/ParseFaithful.lean` lifts the request LINE (`parse_faithful`: the
resolved method/target/version ARE the wire slices, rejoining verbatim) and a
SINGLE header line (`parseHeaderLine_faithful`: name = pre-colon bytes, value =
OWS-trimmed field-value, plus injection rejection). What it left open is the
HEADER LIST: that *every* entry in the parsed `headers` list resolves to the
wire header block it came from, across the whole `parseHeaders` recursion,
including the sidecar/uppercase-name canonicalization offset.

This file discharges it. `parseHeaders_faithful` is a real induction over the
`parseHeaders` parse loop (mirroring `parse_faithful`'s request-line lift and
`parseHeaders_spec`'s bounds induction): for the whole header list, the resolved
name of every parsed header equals the **lowercased** wire field-name
(`(wire-name).map lowerByte` — the RFC 7230 §3.2 case-insensitive canonical
form; stored-name ≠ wire-name exactly when the wire name has an uppercase byte,
in which case the canonical bytes live in the sidecar arena at
`sidecarBase + (accumulated sidecar length)`), and the resolved value equals the
OWS-trimmed wire field-value. Every header is a faithful decode of its wire
CRLF-delimited segment — not one line, but the entire block.

The canonicalization is handled EXACTLY, not hand-waved: the stored canonical
name equals `(wire-name).map lowerByte` in BOTH cases — for an already-lowercase
name the main-arena bytes are the wire name and `map lowerByte` is the identity
on them; for a name with an uppercase byte the sidecar holds the lowered bytes,
and a prefix-monotonicity invariant on the sidecar accumulator
(`sidecar <+: sidecarF`) proves the FINAL sidecar still reads back exactly those
lowered bytes at the entry's offset.

Additive over the UNCHANGED `parse` / `parseHeaders` / `parse_complete_spec`;
the wire bytes are read through the same `Store.resolve` the deployed adapter
uses (`viewBytes` = `Reactor.Config.resolveBytes`).
-/
import Arena.Parse
import Arena.ParseTheorems
import Arena.ParseFaithful

namespace Arena
namespace Parse

/-! ## The per-span wire decode (the canonical name + OWS-trimmed value) -/

/-- The canonical (lowercased) field-name the header segment `sp` spells on the
wire: the bytes of the line **before the first colon**, lowercased byte-for-byte
(RFC 7230 §3.2 case-insensitive field-names). -/
def wireHeaderName (input : Bytes) (sp : Span) : Bytes :=
  ((sliceSpan input sp).take ((findByteIdx COLON (sliceSpan input sp)).getD 0)).map lowerByte

/-- The OWS-trimmed field-value the header segment `sp` spells on the wire: the
bytes **after the first colon**, with leading/trailing SP/HTAB stripped. -/
def wireHeaderValue (input : Bytes) (sp : Span) : Bytes :=
  owsTrim ((sliceSpan input sp).drop ((findByteIdx COLON (sliceSpan input sp)).getD 0 + 1))

/-! ## Small structural helpers -/

/-- If `p ++ q` is a prefix of `r`, then the `q`-length window of `r` at offset
`|p|` reads exactly `q` — the FINAL sidecar still holds the bytes an earlier
canonicalization appended, because the accumulator only grows at the end. -/
theorem prefix_slice {p q r : Bytes} (h : p ++ q <+: r) :
    (r.drop p.length).take q.length = q := by
  obtain ⟨t, rfl⟩ := h
  have hd : ((p ++ q) ++ t).drop p.length = q ++ t := by
    rw [List.append_assoc, List.drop_append_of_le_length (Nat.le_refl p.length),
        List.drop_length, List.nil_append]
  rw [hd, List.take_append_of_le_length (Nat.le_refl q.length), List.take_length]

/-- A name carrying no uppercase byte is its own lowercasing: `map lowerByte`
is the identity on already-lowercase bytes. -/
theorem map_lowerByte_of_not_hasUpper {l : Bytes} (h : hasUpper l = false) :
    l.map lowerByte = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    unfold hasUpper at h
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have ha : lowerByte a = a := by simp only [lowerByte, h.1, Bool.false_eq_true, if_false]
    have iht : t.map lowerByte = t := ih (by unfold hasUpper; exact h.2)
    simp only [List.map_cons, ha, iht]

/-- `canonNameEntry` only extends the sidecar accumulator (append or no-op), so
the input sidecar is always a prefix of the output sidecar. -/
theorem canonNameEntry_prefix {input sidecar : Bytes} {sp : Span}
    {sidecar' : Bytes} {e : Entry}
    (hce : canonNameEntry input sidecar sp = (sidecar', e)) :
    sidecar <+: sidecar' := by
  unfold canonNameEntry at hce
  simp only [] at hce
  split at hce
  · injection hce with h₁ _; subst h₁; exact ⟨_, rfl⟩
  · injection hce with h₁ _; subst h₁; exact List.prefix_refl _

/-! ## The sidecar resolve bridge (analogue of `viewBytes_main`) -/

/-- **The sidecar resolve/wire bridge.** A canonical-name entry
`mkEntry tag (sidecarBase + physOff) len` whose range fits the sidecar arena
resolves, through `Store.resolve`, to exactly the sidecar bytes
`(sidecar.drop physOff).take len` — the synthesized bytes its coordinates name.
The sidecar analogue of `viewBytes_main`. -/
theorem viewBytes_sidecar {main : Array UInt8} {sidecar : Bytes} {es : List Entry}
    {tag : NameTag} {physOff len : Nat}
    (hoff : physOff < sidecarBaseNat) (hlen : len < sidecarBaseNat)
    (hend : physOff + len ≤ sidecar.length) :
    viewBytes ⟨main, sidecar.toArray, es⟩ (mkEntry tag (sidecarBaseNat + physOff) len)
      = (sidecar.drop physOff).take len := by
  have hbase : sidecarBaseNat = 2147483648 := rfl
  have hsize : UInt32.size = 4294967296 := rfl
  have hoffN : (UInt32.ofNat (sidecarBaseNat + physOff)).toNat = sidecarBaseNat + physOff :=
    UInt32.toNat_ofNat_of_lt (by omega)
  have hlenN : (UInt32.ofNat len).toNat = len := UInt32.toNat_ofNat_of_lt (by omega)
  have hside : (mkEntry tag (sidecarBaseNat + physOff) len).inSidecar = true := by
    simp only [mkEntry, Entry.inSidecar, decide_eq_true_iff]
    unfold isSidecarAddr; rw [hoffN]; omega
  unfold viewBytes Store.resolve
  have harena : (Store.mk main sidecar.toArray es).arenaOf
      (mkEntry tag (sidecarBaseNat + physOff) len) = sidecar.toArray := by
    simp only [Store.arenaOf, hside, if_true]
  have hphys : (mkEntry tag (sidecarBaseNat + physOff) len).physOff = physOff := by
    unfold Entry.physOff; rw [hside]; simp only [mkEntry, hoffN, if_true]; omega
  simp only [harena, hphys]
  simp only [mkEntry, hlenN, List.size_toArray]
  rw [if_pos (by omega : physOff + len ≤ sidecar.length)]
  simp only [Option.getD]
  rw [toArray_extract_toList]
  congr 1; omega

/-! ## The header-list faithfulness induction -/

/-- **`parseHeaders_faithful` (the induction).** By induction over the
`parseHeaders` parse loop (mirroring `parse_faithful`'s request-line lift): for
ANY starting sidecar accumulator, the output sidecar extends it
(`sidecar <+: sidecarF`), and every parsed header's resolved `(name, value)` —
read through `Store.resolve` against the FINAL store — equals the per-segment
wire decode `(wireHeaderName, wireHeaderValue)`. The `sidecar <+: sidecarF`
prefix invariant is what lets a header canonicalized against an intermediate
sidecar resolve correctly against the final one: the accumulator only grows at
the end, so its earlier bytes are unchanged. -/
theorem parseHeaders_faithful (input : Bytes) (es : List Entry) :
    ∀ {spans : List Span} {sidecar sidecarF : Bytes} {headers : List ParsedHeader},
      input.length < sidecarBaseNat →
      (∀ sp ∈ spans, sp.off + sp.len ≤ input.length) →
      sidecar.length + spanSum spans < sidecarBaseNat →
      parseHeaders input spans sidecar = some (sidecarF, headers) →
      sidecar <+: sidecarF ∧
      headers.map (fun ph =>
          (viewBytes ⟨input.toArray, sidecarF.toArray, es⟩ ph.name,
           viewBytes ⟨input.toArray, sidecarF.toArray, es⟩ ph.value))
        = spans.map (fun sp => (wireHeaderName input sp, wireHeaderValue input sp))
  | [], sidecar, sidecarF, headers, _, _, _, h => by
    unfold parseHeaders at h
    injection h with h; injection h with h₁ h₂; subst h₁; subst h₂
    exact ⟨List.prefix_refl _, rfl⟩
  | sp :: rest, sidecar, sidecarF, headers, hin, hsp, hcap, h => by
    have hsc : spanSum (sp :: rest) = sp.len + spanSum rest := rfl
    unfold parseHeaders at h
    split at h
    · simp at h
    next hlen0 =>
    obtain ⟨raw, hraw, h⟩ := Option.bind_eq_some_iff.mp h
    rcases hce : canonNameEntry input sidecar raw.name with ⟨sidecar', nameEntry⟩
    rw [hce] at h
    obtain ⟨⟨sidecarF', parsed⟩, hrec, h⟩ := Option.bind_eq_some_iff.mp h
    injection h with h; injection h with h₁ h₂; subst h₁; subst h₂
    -- span/line facts
    have hspHere : sp.off + sp.len ≤ input.length := hsp sp (by simp)
    have hlineLen : (sliceSpan input sp).length = sp.len := by
      rw [sliceSpan_length]; omega
    obtain ⟨hnOff, hnLen, hnEnd, hvEnd⟩ := parseHeaderLine_spec hraw
    -- the faithful single-line decode
    obtain ⟨ci, hci, hcine0, hnameEq, hnameOff, hnameLen, hvalOff, hvalSlice,
        hnameClean, hvalClean⟩ := parseHeaderLine_faithful hraw
    -- ci is inside the line and hence ≤ sp.len
    have hciLt : ci < (sliceSpan input sp).length := findByteIdx_lt hci
    have hciLe : ci ≤ sp.len := by omega
    -- raw.name resolves to the wire name slice
    have hrawname : sliceSpan input raw.name = (sliceSpan input sp).take ci := by
      rw [hnameEq]; simp only [sliceSpan]; rw [List.take_take]; congr 1; omega
    have hrawnameLen : (sliceSpan input raw.name).length = ci := by
      rw [hrawname, List.length_take, hlineLen]; omega
    -- growth + prefix from the recursion (IH)
    have hgrow := canonNameEntry_length hce
    have hcap' : sidecar'.length + spanSum rest < sidecarBaseNat := by omega
    obtain ⟨ihPrefix, ihMap⟩ :=
      parseHeaders_faithful input es hin
        (fun q hq => hsp q (List.mem_cons_of_mem sp hq)) hcap' hrec
    have hpre : sidecar <+: sidecarF' := (canonNameEntry_prefix hce).trans ihPrefix
    -- === the VALUE decode ===
    have hvfit : raw.value.off + raw.value.len ≤ input.length := by omega
    have hval_main : viewBytes ⟨input.toArray, sidecarF'.toArray, es⟩
        (mkEntry .headerValue raw.value.off raw.value.len)
          = sliceSpan input raw.value := by
      rw [viewBytes_main (by omega) (by omega) hvfit]
    have hvb : (ci + 1 + (List.takeWhile isOws (List.drop (ci + 1) (sliceSpan input sp))).length)
        + raw.value.len ≤ sp.len := by
      have hh := hvEnd; rw [hvalOff] at hh; omega
    have hval_wire : sliceSpan input raw.value = wireHeaderValue input sp := by
      have hsub := sliceSpan_sub input sp.off sp.len
        (ci + 1 + (List.takeWhile isOws (List.drop (ci + 1) (sliceSpan input sp))).length)
        raw.value.len hvb
      have hoffeq : raw.value.off = sp.off +
          (ci + 1 + (List.takeWhile isOws (List.drop (ci + 1) (sliceSpan input sp))).length) := by
        rw [hvalOff]; omega
      unfold wireHeaderValue
      simp only [hci, Option.getD_some]
      calc sliceSpan input raw.value
          = sliceSpan input ⟨sp.off +
              (ci + 1 + (List.takeWhile isOws (List.drop (ci + 1) (sliceSpan input sp))).length),
              raw.value.len⟩ := by simp only [sliceSpan, hoffeq]
        _ = sliceSpan (sliceSpan input sp)
              ⟨ci + 1 + (List.takeWhile isOws (List.drop (ci + 1) (sliceSpan input sp))).length,
               raw.value.len⟩ := hsub
        _ = owsTrim ((sliceSpan input sp).drop (ci + 1)) := hvalSlice
    -- === the NAME decode ===  (both cases collapse to (wire-name).map lowerByte)
    have hname_lowered : viewBytes ⟨input.toArray, sidecarF'.toArray, es⟩ nameEntry
        = (sliceSpan input raw.name).map lowerByte := by
      unfold canonNameEntry at hce
      simp only [] at hce
      split at hce
      next hup =>
        injection hce with hseq hneq
        subst hneq
        have hsc' : sidecar' = sidecar ++ (sliceSpan input raw.name).map lowerByte := hseq.symm
        have hlenAppend : ((sliceSpan input raw.name).map lowerByte).length = raw.name.len := by
          rw [List.length_map, hrawnameLen]; omega
        have hpref2 : sidecar ++ (sliceSpan input raw.name).map lowerByte <+: sidecarF' := by
          rw [← hsc']; exact ihPrefix
        have hfitS : sidecar.length + raw.name.len ≤ sidecarF'.length := by
          have := hpref2.length_le
          rw [List.length_append, hlenAppend] at this; omega
        rw [viewBytes_sidecar (by omega) (by omega) hfitS]
        have hps := prefix_slice hpref2
        rw [hlenAppend] at hps
        exact hps
      next hup =>
        injection hce with hseq hneq
        subst hneq
        have hup' : hasUpper (sliceSpan input raw.name) = false := by simpa using hup
        rw [viewBytes_main (by omega : raw.name.off < sidecarBaseNat)
              (by omega : raw.name.len < sidecarBaseNat) (by omega)]
        rw [map_lowerByte_of_not_hasUpper hup']
    have hname_wire : (sliceSpan input raw.name).map lowerByte = wireHeaderName input sp := by
      unfold wireHeaderName
      simp only [hci, Option.getD_some, hrawname]
    -- assemble the head, prepend to the IH tail
    have hname : viewBytes ⟨input.toArray, sidecarF'.toArray, es⟩ nameEntry
        = wireHeaderName input sp := hname_lowered.trans hname_wire
    have hval : viewBytes ⟨input.toArray, sidecarF'.toArray, es⟩
        (mkEntry .headerValue raw.value.off raw.value.len) = wireHeaderValue input sp :=
      hval_main.trans hval_wire
    refine ⟨hpre, ?_⟩
    rw [List.map_cons, List.map_cons, ihMap]
    congr 1
    simp only [hname, hval]

/-! ## Lifting to `parse`: the whole header list is a faithful wire decode -/

/-- **`parse_headers_faithful` — every dispatched header IS its wire segment.**
On a `complete` parse, there is a header-segment list `spans` — precisely the
CRLF-delimited segments of the wire head after the request line — such that the
`Request.headers` list, resolved through `Store.resolve` exactly as the deployed
adapter reads it, equals the per-segment wire decode: each header's name is the
**lowercased** wire field-name and its value is the OWS-trimmed wire
field-value. The whole header block, not one line, is proven a faithful decode
of the wire bytes — the header half of the parse-faithfulness assumption the
serve previously carried. -/
theorem parse_headers_faithful {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) :
    ∃ (headEnd : Nat) (reqSpan : Span) (spans : List Span),
      findDoubleCrlf input = some headEnd ∧
      segments 0 headEnd (crlfPositions (input.take headEnd)) = reqSpan :: spans ∧
      (∀ sp ∈ spans, sp.off + sp.len ≤ input.length) ∧
      req.headers.map (fun ph =>
          (viewBytes req.store ph.name, viewBytes req.store ph.value))
        = spans.map (fun sp => (wireHeaderName input sp, wireHeaderValue input sp)) := by
  unfold parse at h
  split at h
  · simp at h
  next hin =>
  split at h
  · simp at h
  next headEnd hfd =>
  have hhead : headEnd + 4 ≤ input.length := findDoubleCrlf_add_four_le hfd
  have hin' : input.length < sidecarBaseNat := by omega
  simp only [] at h
  split at h
  · simp at h
  next reqSpan headerSpans hseg =>
  split at h
  · simp at h
  next rl hrl =>
  split at h
  · simp at h
  next sidecar headers hph =>
  split at h
  · simp at h
  next hcount =>
  split at h
  · simp at h
  injection h with h
  subst h
  dsimp only
  -- span-fit + spanSum bound (as in `parse_complete_spec`)
  have hlenHead : (input.take headEnd).length = headEnd := by simp; omega
  have hpos : ∀ p ∈ crlfPositions (input.take headEnd), p < headEnd := by
    intro p hp; have := crlfPositions_lt hp; omega
  have hends : ∀ sp ∈ reqSpan :: headerSpans, sp.off + sp.len ≤ headEnd + 1 := by
    rw [← hseg]; exact segments_end_le hpos (by omega)
  have hendsIn : ∀ sp ∈ reqSpan :: headerSpans, sp.off + sp.len ≤ input.length := by
    intro sp hsp; have := hends sp hsp; omega
  have hsum : spanSum (reqSpan :: headerSpans) ≤ headEnd + 1 := by
    have := segments_spanSum_le (start := 0) (hi := headEnd)
      (crlfPositions_pairwise (input.take headEnd)) hpos (fun p _ => by omega) (by omega)
    rw [hseg] at this; omega
  have hsc : spanSum (reqSpan :: headerSpans) = reqSpan.len + spanSum headerSpans := rfl
  have hcap : (([] : Bytes)).length + spanSum headerSpans < sidecarBaseNat := by
    show 0 + spanSum headerSpans < sidecarBaseNat; omega
  obtain ⟨_, hmap⟩ :=
    parseHeaders_faithful input
      (mkEntry .method rl.method.off rl.method.len ::
        mkEntry .target rl.target.off rl.target.len ::
        mkEntry .version rl.version.off rl.version.len ::
        headers.flatMap (fun hh => [hh.name, hh.value])).reverse
      hin' (fun q hq => hendsIn q (List.mem_cons_of_mem reqSpan hq)) hcap hph
  exact ⟨headEnd, reqSpan, headerSpans, hfd, hseg,
    fun sp hsp => hendsIn sp (List.mem_cons_of_mem reqSpan hsp), hmap⟩

/-! ## Non-vacuity: a concrete multi-header request, resolved exactly

The UTF-8 content check inside `parse` (`String.validateUTF8`, an `@[extern]`
primitive) does not reduce in the kernel, so a `decide`/`rfl` witness cannot be
driven through `parse` itself. The header-list decode `parseHeaders_faithful`
lifts, however, is entirely on the `parseHeaders` loop — which carries NO UTF-8
gate — so the witness is stated there: it reduces by `decide`, exercising both
canonicalization paths concretely. (`#eval (parse multiHeaderReq)` does return
`.complete` with `sidecar = [104,111,115,116]` and exactly these header entries;
the block is a kernel-reduction limitation of the extern UTF-8 check, not a gap
in the theorem.) -/

/-- A concrete request head `GET / HTTP/1.1` + `Host: x` + `k: v` (+ CRLFCRLF).
`Host` is an UPPERCASE-initial name (the sidecar canonicalization path); `k` is
already lowercase (the main-arena path). -/
def multiHeaderReq : Bytes :=
  [71,69,84,32,47,32,72,84,84,80,47,49,46,49,13,10,
   72,111,115,116,58,32,120,13,10,
   107,58,32,118,13,10,
   13,10]

/-- The two header-line segments of `multiHeaderReq`'s head: `Host: x` at
`⟨16,7⟩`, `k: v` at `⟨25,4⟩` — the CRLF-delimited segments after the request
line (`segments 0 29 (crlfPositions head)` past `⟨0,14⟩`). -/
def multiHeaderSpans : List Span := [⟨16, 7⟩, ⟨25, 4⟩]

/-- **The two-header block resolves to the EXACT wire `(name, value)`s.**
`parseHeaders` accepts the block, and the resolved header list — read through the
same `Store.resolve`/`viewBytes` the deployed adapter uses, against the final
store (sidecar included) — is `[("host","x"), ("k","v")]`: `Host` canonicalized
(lowercased) to `host` out of the SIDECAR arena, `k` from the MAIN arena, values
OWS-trimmed. Witnesses that `parseHeaders_faithful` is not vacuous, uppercase
name and both arena paths and all. -/
theorem multiHeaderReq_faithful :
    ∃ (sidecarF : Bytes) (headers : List ParsedHeader),
      parseHeaders multiHeaderReq multiHeaderSpans [] = some (sidecarF, headers) ∧
      headers.map (fun ph =>
        (viewBytes ⟨multiHeaderReq.toArray, sidecarF.toArray, []⟩ ph.name,
         viewBytes ⟨multiHeaderReq.toArray, sidecarF.toArray, []⟩ ph.value))
        = [([104,111,115,116], [120]), ([107], [118])] := by
  refine ⟨_, _, rfl, ?_⟩
  decide

end Parse
end Arena
