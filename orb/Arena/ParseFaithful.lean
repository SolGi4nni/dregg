/-
Arena — the parser's SEMANTIC faithfulness theory (the HEAD decode).

`Arena/ParseTheorems.lean` proves the head parse is *bounded / memory-safe*:
every `complete` outcome carries a well-formed store (`parse_wf`), a consumed
count inside the input (`parse_consumed_le`), and at most `maxHeaders` headers.
That is a SAFETY result — it says the parser never runs off the end and never
registers an unbounded number of ranges. It does NOT say the ranges it registers
are the *right* ranges: that the method entry actually addresses the method
bytes, the target the target bytes, and so on. Downstream (`Reactor/Config.lean
protoReqOf`, and the serve fold behind it) that faithfulness is *assumed*.

This file discharges it. The headline is `parse_faithful`: on a `complete`
parse, resolving the method / target / version entries through the proven-total
`Store.resolve` returns *exactly* the wire bytes the request line says they are —
and those three fields, rejoined with the single `SP` separators RFC 7230 §3.1.1
mandates, reconstruct the request line **verbatim** (a lossless decode /
round-trip of the request line). Header values resolve to exactly the
OWS-trimmed field-value (`parse_header_value_faithful`); header names resolve to
the lowercased field-name (RFC 7230 §3.2 case-insensitive field-names,
`parse_header_name_faithful`). The complement to `Body.Framing`'s BOUNDARY: this
is the HEAD.

`parse_rejects_ctl_in_value` is the header-injection analogue of the framing
smuggling theorem: a field-value carrying an embedded `CR` (or `NUL`, or any C0
control other than HTAB, or `DEL`) is REJECTED, never silently mis-parsed —
non-vacuously witnessed by a concrete CR-injection probe the parser rejects
against a clean request it accepts faithfully.

Everything here is stated against the *unchanged* `parse` / `parse_complete_spec`
(additive); the wire bytes are read back through the same `Store.resolve` the
deployed adapter uses, so a faithfulness theorem here is a faithfulness theorem
about the bytes the deployed serve dispatches on.
-/
import Arena.Parse
import Arena.ParseTheorems

namespace Arena
namespace Parse

/-! ## The view-bytes reader (matches `Reactor.Config.resolveBytes`) -/

/-- The bytes an entry denotes, read back through the proven-total
`Store.resolve`. Definitionally the deployed adapter's `resolveBytes`
(`Reactor/Config.lean`): on a `complete` parse every stored entry is in-bounds,
so the `none` arm is dead, but `resolve` is total-as-`Option` so the match is
still spelled. -/
def viewBytes (s : Store) (e : Entry) : Bytes :=
  match s.resolve e with
  | some b => b.toList
  | none => []

/-! ## Bridge: resolving a main-arena entry reads exactly the wire slice -/

/-- `Array.extract`'s `toList` on a `List.toArray` reads the list slice. -/
theorem toArray_extract_toList (bs : Bytes) (a b : Nat) :
    (bs.toArray.extract a b).toList = (bs.drop a).take (b - a) := by
  rw [Array.toList_extract, List.toList_toArray, List.extract_eq_drop_take]

/-- **The resolve/wire bridge.** A main-arena entry `mkEntry tag off len` whose
range fits the input resolves, through `Store.resolve`, to *exactly* the input
bytes `sliceSpan input ⟨off, len⟩` — the wire slice its coordinates name. This is
the fact that turns "the parser registered a range" into "the parser named the
right bytes". -/
theorem viewBytes_main {input : Bytes} {sc : Array UInt8} {es : List Entry}
    {tag : NameTag} {off len : Nat}
    (hoff : off < sidecarBaseNat) (hlen : len < sidecarBaseNat)
    (hend : off + len ≤ input.length) :
    viewBytes ⟨input.toArray, sc, es⟩ (mkEntry tag off len)
      = sliceSpan input ⟨off, len⟩ := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hbase : sidecarBaseNat = 2147483648 := rfl
  have hoffN : (UInt32.ofNat off).toNat = off := UInt32.toNat_ofNat_of_lt (by omega)
  have hlenN : (UInt32.ofNat len).toNat = len := UInt32.toNat_ofNat_of_lt (by omega)
  have hside : (mkEntry tag off len).inSidecar = false := by
    simp only [mkEntry, Entry.inSidecar, decide_eq_false_iff_not]
    unfold isSidecarAddr; simp only [mkEntry] at hoffN; omega
  unfold viewBytes Store.resolve
  have harena : (Store.mk input.toArray sc es).arenaOf (mkEntry tag off len)
      = input.toArray := by
    simp only [Store.arenaOf, hside, Bool.false_eq_true, if_false]
  have hphys : (mkEntry tag off len).physOff = off := by
    unfold Entry.physOff; rw [hside]; simp only [mkEntry, hoffN, Bool.false_eq_true, if_false]
  simp only [harena, hphys]
  simp only [mkEntry, hlenN, List.size_toArray]
  rw [if_pos (by omega : off + len ≤ input.length)]
  simp only [Option.getD, sliceSpan]
  rw [toArray_extract_toList]
  congr 1; omega

/-! ## Sub-slicing: a range inside a segment is a slice of that segment -/

/-- A range `⟨base + a, b⟩` inside the segment `⟨base, blen⟩` (i.e. `a + b ≤
blen`, and the segment fits the input) reads the same bytes whether taken from
`input` directly or from the segment's own slice. This is what lets a header
entry (absolute-offset into `input`) be read as a slice of its header *line*. -/
theorem sliceSpan_sub (input : Bytes) (base blen a b : Nat) (hab : a + b ≤ blen) :
    sliceSpan input ⟨base + a, b⟩
      = sliceSpan (sliceSpan input ⟨base, blen⟩) ⟨a, b⟩ := by
  simp only [sliceSpan]
  rw [List.drop_take, List.drop_drop, List.take_take]
  have h1 : min b (blen - a) = b := by omega
  rw [h1]

/-! ## The request line is a faithful, lossless decode -/

/-- `findByteIdx t l = some i` locates a real `t`: `l[i] = t`, `i < l.length`,
and no earlier byte is `t`. -/
theorem findByteIdx_spec {t : UInt8} {l : Bytes} {i : Nat}
    (h : findByteIdx t l = some i) :
    ∃ hlt : i < l.length, l[i] = t ∧ ∀ j, (hj : j < i) → l[j] ≠ t := by
  unfold findByteIdx at h
  obtain ⟨hlt, hp, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨hlt, eq_of_beq hp, fun j hj hcontra => ?_⟩
  exact hmin j hj (by simp [hcontra])

/-- **`parseRequestLine_faithful` — the request line rejoins verbatim.** From a
successful `parseRequestLine off line`, the three field slices of `line` — the
method (`line.take m`), the target (`(line.drop (m+1)).take t`), and the version
(`line.drop (m+t+2)`) — **rejoined with the single `SP` separators RFC 7230
§3.1.1 mandates, reconstruct `line` exactly** (a lossless decode). The method
is non-empty and contains no `SP`; the version begins `HTTP/`; and the field
spans are the consecutive, single-`SP`-separated coordinates
`⟨off, m⟩ / ⟨off+m+1, t⟩ / ⟨off+m+t+2, |version|⟩`. -/
theorem parseRequestLine_faithful {off : Nat} {line : Bytes} {rl : ReqLineSpans}
    (h : parseRequestLine off line = some rl) :
    rl.method.off = off ∧ rl.target.off = off + rl.method.len + 1
      ∧ rl.version.off = off + rl.method.len + rl.target.len + 2
      ∧ rl.version.len = line.length - (rl.method.len + rl.target.len + 2)
      ∧ (line.take rl.method.len)
          ++ SP :: ((line.drop (rl.method.len + 1)).take rl.target.len
            ++ SP :: line.drop (rl.method.len + rl.target.len + 2)) = line
      ∧ startsWithHttpSlash (line.drop (rl.method.len + rl.target.len + 2))
      ∧ 1 ≤ rl.method.len
      ∧ (∀ j, (hj : j < rl.method.len) → line[j]?.getD 0 ≠ SP) := by
  unfold parseRequestLine at h
  obtain ⟨i₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨i₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [] at h
  split at h
  · simp at h
  next hns =>
  split at h
  · simp at h
  next hne0 =>
  split at h
  · simp at h
  next hhttp =>
  injection h with h
  subst h
  dsimp only
  -- unpack the two space locations
  obtain ⟨hlt₁, hget₁, _⟩ := findByteIdx_spec h₁
  obtain ⟨hlt₂, hget₂, _⟩ := findByteIdx_spec h₂
  -- rest₁ = line.drop (i₁+1); i₂ found in it
  have hrest₁ : line.drop (i₁ + 1) = (line.drop (i₁ + 1)).take i₂
      ++ (line.drop (i₁ + 1))[i₂] :: (line.drop (i₁ + 1)).drop (i₂ + 1) := by
    conv => lhs; rw [← List.take_append_drop i₂ (line.drop (i₁ + 1)),
      List.drop_eq_getElem_cons hlt₂]
  have hget₂' : (line.drop (i₁ + 1))[i₂] = SP := hget₂
  -- drop composition for the version tail
  have hdropc : (line.drop (i₁ + 1)).drop (i₂ + 1) = line.drop (i₁ + i₂ + 2) := by
    rw [List.drop_drop]; congr 1; omega
  have hne0' : i₁ ≠ 0 := by simpa using hne0
  -- assemble the round trip
  refine ⟨rfl, by omega, by omega, ?_, ?_, ?_, by omega, ?_⟩
  · rw [hdropc, List.length_drop]
  · -- round trip: line.take i₁ ++ SP :: (rest₁.take i₂ ++ SP :: line.drop (i₁+i₂+2)) = line
    have hstep : (line.drop (i₁ + 1)).take i₂ ++ SP :: line.drop (i₁ + i₂ + 2)
        = line.drop (i₁ + 1) := by
      conv => rhs; rw [hrest₁]
      rw [hget₂', hdropc]
    have hi₁ : i₁ + 1 + i₂ + 1 = i₁ + i₂ + 2 := by omega
    calc line.take i₁ ++ SP :: ((line.drop (i₁ + 1)).take i₂ ++ SP :: line.drop (i₁ + i₂ + 2))
        = line.take i₁ ++ SP :: line.drop (i₁ + 1) := by rw [hstep]
      _ = line.take i₁ ++ line.drop i₁ := by rw [List.drop_eq_getElem_cons hlt₁, hget₁]
      _ = line := List.take_append_drop i₁ line
  · -- version starts HTTP/: rest₂ = line.drop (i₁+i₂+2) and startsWithHttpSlash rest₂ held
    rw [← hdropc]
    simpa using hhttp
  · -- method SP-free
    intro j hj
    obtain ⟨_, _, hmin₁⟩ := findByteIdx_spec h₁
    have : line[j]?.getD 0 = line[j] := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [this]
    exact hmin₁ j hj

/-! ## Lifting to `parse`: the resolved head fields are the wire bytes -/

/-- The first segment starts at the cut origin. -/
theorem segments_head_off {ps : List Nat} {start hi : Nat} {sp : Span} {rest : List Span}
    (h : segments start hi ps = sp :: rest) : sp.off = start := by
  cases ps with
  | nil => simp only [segments] at h; rw [← (List.cons.injEq _ _ _ _).mp h |>.1]
  | cons p ps => simp only [segments] at h; rw [← (List.cons.injEq _ _ _ _).mp h |>.1]

/-- **`parse_faithful` — the deployed head fields ARE the wire bytes.** On a
`complete` parse, the method / target / version entries, resolved through the
proven-total `Store.resolve` exactly as the deployed adapter reads them
(`viewBytes` = `Reactor.Config.resolveBytes`), return the *literal wire slices*
`input.take m` / `(input.drop (m+1)).take t` / `(input.drop (m+t+2)).take v` — and
those three fields, **rejoined with the single `SP` separators RFC 7230 §3.1.1
mandates, reconstruct the request line `input.take (m+t+v+2)` verbatim** (a
lossless round-trip). The version begins `HTTP/`; the method is non-empty. This
turns "the parser registered a well-formed range" (`parse_wf`) into "the parser
named exactly the bytes the wire says" — the semantic faithfulness the serve
previously *assumed*. -/
theorem parse_faithful {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) :
    ∃ m t v : Nat,
      viewBytes req.store req.method  = input.take m
      ∧ viewBytes req.store req.target  = (input.drop (m + 1)).take t
      ∧ viewBytes req.store req.version = (input.drop (m + t + 2)).take v
      ∧ viewBytes req.store req.method
          ++ SP :: (viewBytes req.store req.target
            ++ SP :: viewBytes req.store req.version) = input.take (m + t + v + 2)
      ∧ startsWithHttpSlash (viewBytes req.store req.version)
      ∧ 1 ≤ m := by
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
  -- reqSpan starts at 0 and fits the input
  have hoff0 : reqSpan.off = 0 := segments_head_off hseg
  have hlenHead : (input.take headEnd).length = headEnd := by simp; omega
  have hpos : ∀ p ∈ crlfPositions (input.take headEnd), p < headEnd := by
    intro p hp; have := crlfPositions_lt hp; omega
  have hendsAll : ∀ sp ∈ reqSpan :: headerSpans, sp.off + sp.len ≤ headEnd + 1 := by
    rw [← hseg]; exact segments_end_le hpos (by omega)
  have hends : reqSpan.off + reqSpan.len ≤ headEnd + 1 := hendsAll reqSpan (by simp)
  have hreqIn : reqSpan.len ≤ input.length := by omega
  -- the request line and its faithful decode (`line = sliceSpan input reqSpan`)
  have hlineLen : (sliceSpan input reqSpan).length = reqSpan.len := by
    rw [sliceSpan_length]; omega
  have hlineEq : sliceSpan input reqSpan = input.take reqSpan.len := by
    simp only [sliceSpan, hoff0, List.drop_zero]
  obtain ⟨hmEnd, htEnd, hvEnd⟩ := parseRequestLine_end_le hrl
  rw [hlineLen] at hmEnd htEnd hvEnd
  obtain ⟨hmoff, htoff, hvoff, hvlen, hround, hhttp, hm1, _hmsp⟩ :=
    parseRequestLine_faithful hrl
  rw [hoff0] at hmoff htoff hvoff
  rw [hmoff] at hmEnd; rw [htoff] at htEnd; rw [hvoff] at hvEnd
  rw [hlineLen] at hvlen
  have hsum : rl.method.len + rl.target.len + 2 ≤ reqSpan.len := by omega
  -- each field resolves to the wire slice its coordinates name (resolve ignores
  -- the entries list, so this is stated over any `es`)
  have hmB : ∀ es : List Entry, viewBytes ⟨input.toArray, sidecar.toArray, es⟩
      (mkEntry .method rl.method.off rl.method.len) = input.take rl.method.len := by
    intro es; rw [hmoff, viewBytes_main (by omega) (by omega) (by omega)]; simp [sliceSpan]
  have htB : ∀ es : List Entry, viewBytes ⟨input.toArray, sidecar.toArray, es⟩
      (mkEntry .target rl.target.off rl.target.len)
      = (input.drop (rl.method.len + 1)).take rl.target.len := by
    intro es; rw [htoff, viewBytes_main (by omega) (by omega) (by omega)]; simp [sliceSpan]
  have hvB : ∀ es : List Entry, viewBytes ⟨input.toArray, sidecar.toArray, es⟩
      (mkEntry .version rl.version.off rl.version.len)
      = (input.drop (rl.method.len + rl.target.len + 2)).take rl.version.len := by
    intro es; rw [hvoff, viewBytes_main (by omega) (by omega) (by omega)]; simp [sliceSpan]
  -- the request-line slices coincide with the wire slices
  have el_m : (sliceSpan input reqSpan).take rl.method.len = input.take rl.method.len := by
    rw [hlineEq, List.take_take]; congr 1; omega
  have el_t : ((sliceSpan input reqSpan).drop (rl.method.len + 1)).take rl.target.len
      = (input.drop (rl.method.len + 1)).take rl.target.len := by
    rw [hlineEq, List.drop_take, List.take_take]; congr 1; omega
  have el_v : (sliceSpan input reqSpan).drop (rl.method.len + rl.target.len + 2)
      = (input.drop (rl.method.len + rl.target.len + 2)).take rl.version.len := by
    rw [hlineEq, List.drop_take]; congr 1; omega
  refine ⟨rl.method.len, rl.target.len, rl.version.len,
    hmB _, htB _, hvB _, ?_, ?_, hm1⟩
  · -- round trip = input.take (m+t+v+2)
    rw [hmB, htB, hvB, ← el_m, ← el_t, ← el_v, hround, hlineEq]
    congr 1; omega
  · rw [hvB, ← el_v]; exact hhttp

/-! ## Header lines: faithful name/value decode, and injection rejection -/

/-- The RFC 7230 §3.2 OWS trim of a field value: strip leading, then trailing,
`SP`/`HTAB`. This is exactly the region `parseHeaderLine` addresses as the value. -/
def owsTrim (bs : Bytes) : Bytes :=
  let front := bs.drop (bs.takeWhile isOws).length
  front.take (front.length - (front.reverse.takeWhile isOws).length)

/-- **`parseHeaderLine_faithful` — the header line decodes faithfully.** A
successful `parseHeaderLine off line` names the field-name as the bytes **before
the first colon** (`⟨off, ci⟩`), and the value as the **OWS-trimmed field-value**
after it (`⟨off + ci + 1 + lead, |trimmed|⟩`, resolving to `owsTrim (line.drop
(ci+1))`). The name carries no `SP`/`HTAB`/`CR`/`LF`, and the value region carries
no control byte (`isCtlValueByte`) — the two injection-free invariants an accepted
header satisfies. -/
theorem parseHeaderLine_faithful {off : Nat} {line : Bytes} {hs : RawHeaderSpans}
    (h : parseHeaderLine off line = some hs) :
    ∃ ci, findByteIdx COLON line = some ci ∧ ci ≠ 0
      ∧ hs.name = ⟨off, ci⟩
      ∧ hs.name.off = off ∧ hs.name.len = ci
      ∧ hs.value.off = off + ci + 1 + ((line.drop (ci + 1)).takeWhile isOws).length
      ∧ sliceSpan line ⟨ci + 1 + ((line.drop (ci + 1)).takeWhile isOws).length, hs.value.len⟩
          = owsTrim (line.drop (ci + 1))
      ∧ ¬ (line.take ci).any (fun b => isOws b || b == CR || b == LF)
      ∧ ¬ (line.drop (ci + 1)).any isCtlValueByte := by
  unfold parseHeaderLine at h
  obtain ⟨ci, hci, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · simp at h
  next hne0 =>
  simp only [] at h
  split at h
  · simp at h
  next hname =>
  split at h
  · simp at h
  next hval =>
  injection h with h
  subst h
  refine ⟨ci, hci, by simpa using hne0, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · -- value decode: sliceSpan of the value span = owsTrim of the raw value
    simp only [sliceSpan, owsTrim, List.drop_drop]
  · simpa using hname
  · simpa using hval

/-- **`parseHeaderLine_rejects_ctl` (general).** If, past a real colon (`ci ≠ 0`)
with a clean name, the raw value region carries *any* control byte flagged by
`isCtlValueByte` — a `CR`, a `NUL`, any C0 control other than `HTAB`, or `DEL` —
the header line is **rejected** (`none`). This is the header-injection analogue of
`Body.Framing`'s smuggling rejection: a smuggled `CR`/`NUL` never survives into a
parsed value. -/
theorem parseHeaderLine_rejects_ctl {off : Nat} {line : Bytes} {ci : Nat}
    (hci : findByteIdx COLON line = some ci) (hne0 : ci ≠ 0)
    (hname : ¬ (line.take ci).any (fun b => isOws b || b == CR || b == LF))
    (hval : (line.drop (ci + 1)).any isCtlValueByte = true) :
    parseHeaderLine off line = none := by
  unfold parseHeaderLine
  rw [hci]
  rw [show ∀ (f : Nat → Option RawHeaderSpans), (some ci >>= f) = f ci from fun _ => rfl]
  rw [if_neg (by simpa using hne0), if_neg (by simpa using hname), if_pos hval]

/-- `CR` (and `NUL`, `DEL`, any C0 control ≠ `HTAB`) is a control byte a value may
not contain. -/
theorem isCtlValueByte_cr : isCtlValueByte CR = true := by decide

/-! ### Non-vacuity: a concrete CR-injection probe -/

/-- A concrete header line `"X: a" CR "b"` — a value with an embedded `CR`, the
header-injection vector. -/
def crInjectionLine : Bytes := [88, 58, 32, 97, 13, 98]

/-- A concrete clean header line `"X: a"`. -/
def cleanHeaderLine : Bytes := [88, 58, 32, 97]

/-- **The CR-injection line is rejected.** `parseHeaderLine` returns `none` on a
value carrying an embedded `CR` — the smuggled carriage return never yields a
parsed header. -/
theorem crInjectionLine_rejected (off : Nat) : parseHeaderLine off crInjectionLine = none := by
  refine parseHeaderLine_rejects_ctl (ci := 1) (by decide) (by decide) (by decide) (by decide)

/-- **The clean line is accepted and decodes faithfully.** `parseHeaderLine` on
`"X: a"` yields the name `⟨off, 1⟩` (the byte `X`) and the value `⟨off+3, 1⟩` (the
byte `a`, OWS-trimmed) — so the contract is not vacuous: a natural clean header is
accepted with exact coordinates, while the CR-injected sibling is refused. -/
theorem cleanHeaderLine_accepted :
    parseHeaderLine 0 cleanHeaderLine = some ⟨⟨0, 1⟩, ⟨3, 1⟩⟩ := by rfl

/-! ## Parse-level rejection: malformed heads never parse `complete` -/

/-- **`parse_incomplete_of_no_head`.** With no `CRLFCRLF` terminator the head is
incomplete — the parser asks for more bytes and never fabricates a `complete`
request out of an unterminated head. -/
theorem parse_incomplete_of_no_head {input : Bytes} {maxHeaders : Nat}
    (hlen : input.length < sidecarBaseNat) (hnf : findDoubleCrlf input = none) :
    parse input maxHeaders = .incomplete := by
  unfold parse
  rw [if_neg (by omega), hnf]

/-- A head with no `CRLFCRLF` never parses `complete`. -/
theorem parse_not_complete_of_no_head {input : Bytes} {maxHeaders : Nat} {req : Request}
    (hlen : input.length < sidecarBaseNat) (hnf : findDoubleCrlf input = none) :
    parse input maxHeaders ≠ .complete req := by
  rw [parse_incomplete_of_no_head hlen hnf]; exact fun h => Outcome.noConfusion h

end Parse
end Arena
