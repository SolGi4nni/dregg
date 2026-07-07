import Datapath.Span
import Arena.Parse
import Reactor.Config

/-!
# Datapath.Scan — the INDEX-NATIVE span scanner (materialization-free in the MODEL)

`Datapath.Refine`'s `spanParseRequest` reads the borrowed window into a
`List UInt8` (`s.read`) and hands that to the deployed cons-list parser. That is
materialization-free only *under the codegen obligation* — the model still names
`s.read`, a `List`.

This module goes further: it defines the dominant whole-payload scan **as an
index recursion that never names a list at all**. `spanFindDoubleCrlf` walks the
window by direct byte loads (`getByte i = buf[off+i]`) with a `Nat` cursor and
fuel, returning an *offset* (a `Nat`), and materializes **no** intermediate
`List UInt8`. It is then proven equal to the deployed parser's own framing scan
(`Arena.Parse.findDoubleCrlf`) on the window's denotation — so the dominant
`O(payload)` scan the whole request parse is gated on is materialization-free in
the model itself, not merely under codegen.

`spanCrlfPositions` is the same for the per-line `CRLF` sweep, and
`SpanBytes.sub` cuts an offset sub-window into the *same* buffer with no copy —
the `(off,len)` view a span-native request head is built out of.

The bridge to the abstract model stays `read_eq_denote`: every scan theorem is
stated against `s.read`, hence (on a well-formed span) against `s.denote`.
-/

namespace Datapath
namespace SpanBytes

open Arena.Parse (CR LF findDoubleCrlf crlfPositions)

/-- The `i`-th window byte agrees with `read`'s `i`-th element (both are the
direct load `buf[off+i]`). The bridge from index reads to the `read` list. -/
theorem getByte_eq_read_getElem (s : SpanBytes) (i : Nat) (h : i < s.read.length) :
    s.read[i] = s.getByte i := by
  simp only [read, List.getElem_ofFn]
  rfl

/-- A byte load clamped to the window: `0` past the end. Mirrors the deployed
scan's `List.getD … 0` so an out-of-window probe (e.g. the `i+1` of the last
index) reads `0`, NOT the next physical buffer byte. -/
def getByteOr0 (s : SpanBytes) (i : Nat) : UInt8 :=
  if i < s.len then s.getByte i else 0

theorem getByteOr0_eq_readGetD (s : SpanBytes) (i : Nat) :
    s.getByteOr0 i = s.read.getD i 0 := by
  unfold getByteOr0
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < s.len
  · rw [if_pos hi]
    have hi' : i < s.read.length := by rw [length_read]; exact hi
    rw [List.getElem?_eq_getElem hi', Option.getD_some, getByte_eq_read_getElem s i hi']
  · rw [if_neg hi]
    have hi' : s.read.length ≤ i := by rw [length_read]; omega
    rw [List.getElem?_eq_none hi', Option.getD_none]

/-- Unfold the deployed framing scan one step on a list with ≥ 4 bytes: the
first-four-byte test, else the shifted recursion on the tail. Lets the index scan
match it without reconstructing cons cells. -/
theorem findDoubleCrlf_step (l : List UInt8) (h : 4 ≤ l.length) :
    findDoubleCrlf l =
      (if l[0]'(by omega) == CR && l[1]'(by omega) == LF
          && l[2]'(by omega) == CR && l[3]'(by omega) == LF
       then some 0 else (findDoubleCrlf (l.drop 1)).map (· + 1)) := by
  match l, h with
  | a :: b :: c :: d :: t, _ =>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.drop_succ_cons, List.drop_zero]
    rw [findDoubleCrlf]

/-- The `k`-th byte of the suffix `read.drop i` is the direct window load
`getByte (i+k)`. -/
theorem dropRead_getElem (s : SpanBytes) (i k : Nat) (hk : i + k < s.len)
    (hb : k < (s.read.drop i).length) :
    (s.read.drop i)[k] = s.getByte (i + k) := by
  rw [List.getElem_drop]
  exact getByte_eq_read_getElem s (i + k) (by rw [length_read]; exact hk)

/-! ## The dominant scan: `CRLFCRLF`, by index -/

/-- Index-native `CRLFCRLF` search: walk the window with a `Nat` cursor `i` and
`fuel`, testing four direct byte loads at each step, returning the offset of the
first match. **Materializes no list** — the whole payload is scanned through
`getByte` alone. `fuel` bounds the recursion; `spanFindDoubleCrlf` supplies
`s.len`, which always suffices (`scanDCrlf_enough`). -/
def scanDCrlf (s : SpanBytes) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if i + 3 < s.len then
      if s.getByte i == CR && s.getByte (i+1) == LF
          && s.getByte (i+2) == CR && s.getByte (i+3) == LF then
        some i
      else scanDCrlf s (i+1) fuel
    else none

/-- **The dominant whole-payload scan, index-native.** Offset of the first
`CRLFCRLF` in the window, computed by direct byte loads with no materialized
list. -/
def spanFindDoubleCrlf (s : SpanBytes) : Option Nat := scanDCrlf s 0 s.len

/-- The invariant: from cursor `i`, with enough fuel to reach the window end, the
index scan equals the deployed list scan on the remaining suffix `read.drop i`,
shifted back by `i`. Proven by induction on `fuel`. -/
theorem scanDCrlf_eq (s : SpanBytes) (i fuel : Nat) (hfuel : s.len ≤ i + fuel) :
    scanDCrlf s i fuel = (findDoubleCrlf (s.read.drop i)).map (· + i) := by
  induction fuel generalizing i with
  | zero =>
    -- no fuel ⇒ i ≥ len ⇒ suffix is [] ⇒ both none
    have hi : s.len ≤ i := by omega
    have : s.read.drop i = [] := by
      apply List.drop_eq_nil_of_le; rw [length_read]; exact hi
    simp [scanDCrlf, this, findDoubleCrlf]
  | succ f ih =>
    unfold scanDCrlf
    by_cases hlt : i + 3 < s.len
    · -- four bytes remain: unfold the deployed scan one step and match by index
      rw [if_pos hlt]
      have hlen : 4 ≤ (s.read.drop i).length := by
        rw [List.length_drop, length_read]; omega
      rw [findDoubleCrlf_step (s.read.drop i) hlen]
      -- the four indexed byte tests are exactly the four window loads
      have b0 : (s.read.drop i)[0]'(by omega) = s.getByte i := by
        have := dropRead_getElem s i 0 (by omega) (by omega); simpa using this
      have b1 : (s.read.drop i)[1]'(by omega) = s.getByte (i+1) :=
        dropRead_getElem s i 1 (by omega) (by omega)
      have b2 : (s.read.drop i)[2]'(by omega) = s.getByte (i+2) :=
        dropRead_getElem s i 2 (by omega) (by omega)
      have b3 : (s.read.drop i)[3]'(by omega) = s.getByte (i+3) :=
        dropRead_getElem s i 3 (by omega) (by omega)
      rw [b0, b1, b2, b3]
      -- (read.drop i).drop 1 = read.drop (i+1)
      have hdrop : (s.read.drop i).drop 1 = s.read.drop (i+1) := by
        rw [List.drop_drop]
      rw [hdrop]
      by_cases hm : s.getByte i == CR && s.getByte (i+1) == LF
          && s.getByte (i+2) == CR && s.getByte (i+3) == LF
      · rw [if_pos hm, if_pos hm]; simp
      · rw [if_neg hm, if_neg hm]
        rw [ih (i+1) (by omega), Option.map_map]
        apply congrArg (Option.map · (findDoubleCrlf (s.read.drop (i+1))))
        funext x; simp [Function.comp]; omega
    · -- fewer than four bytes remain: deployed scan hits its `_ => none` arm
      rw [if_neg hlt]
      have hlen : (s.read.drop i).length < 4 := by
        rw [List.length_drop, length_read]; omega
      have : findDoubleCrlf (s.read.drop i) = none := by
        match hd : s.read.drop i with
        | [] => simp [findDoubleCrlf]
        | [a] => simp [findDoubleCrlf]
        | [a,b] => simp [findDoubleCrlf]
        | [a,b,c] => simp [findDoubleCrlf]
        | a :: b :: c :: d :: t =>
          rw [hd] at hlen; simp only [List.length_cons] at hlen; omega
      rw [this]; rfl

/-- **The scanner refinement (against `read`).** The index-native `CRLFCRLF`
scan equals the deployed parser's framing scan on the window's `read`. -/
theorem spanFindDoubleCrlf_eq_read (s : SpanBytes) :
    spanFindDoubleCrlf s = findDoubleCrlf s.read := by
  unfold spanFindDoubleCrlf
  rw [scanDCrlf_eq s 0 s.len (by omega)]
  simp

/-- **The scanner refinement (against `denote`) — the headline.** On a
well-formed span the index-native dominant scan equals the deployed parser's
framing scan on the window's *denotation*: the `O(payload)` scan the whole
request parse is gated on is materialization-free **in the model**, and computes
exactly the deployed result. -/
theorem spanFindDoubleCrlf_eq_denote (s : SpanBytes) (h : s.Wf) :
    spanFindDoubleCrlf s = findDoubleCrlf s.denote := by
  rw [spanFindDoubleCrlf_eq_read, read_eq_denote s h]

/-! ## The per-line sweep: `CRLF` positions, by index -/

/-- Index-native `CRLF`-position sweep over the window: the indices `i` where
`buf[off+i] = CR` and `buf[off+i+1] = LF`, with the past-the-end probe clamped to
`0` (`getByteOr0`) exactly as the deployed `getD … 0`. -/
def spanCrlfPositions (s : SpanBytes) : List Nat :=
  (List.range s.len).filter fun i => s.getByteOr0 i == CR && s.getByteOr0 (i+1) == LF

/-- **The `CRLF`-sweep refinement.** The index-native sweep equals the deployed
`crlfPositions` on `read` (hence, on a well-formed span, on `denote`). -/
theorem spanCrlfPositions_eq_read (s : SpanBytes) :
    spanCrlfPositions s = crlfPositions s.read := by
  unfold spanCrlfPositions crlfPositions
  rw [length_read]
  apply List.filter_congr
  intro i _
  rw [getByteOr0_eq_readGetD, getByteOr0_eq_readGetD]

theorem spanCrlfPositions_eq_denote (s : SpanBytes) (h : s.Wf) :
    spanCrlfPositions s = crlfPositions s.denote := by
  rw [spanCrlfPositions_eq_read, read_eq_denote s h]

/-! ## Offset sub-windows into the SAME buffer (no copy) -/

/-- Cut an `(off', len')` sub-window *relative to* `s` into the **same** buffer —
no bytes copied, just narrower offsets. This is the `⟨buf, off, len⟩` view a
span-native request head (method / target / version / header windows) is built
out of. -/
def sub (s : SpanBytes) (off' len' : Nat) : SpanBytes :=
  { buf := s.buf, off := s.off + off', len := len' }

@[simp] theorem sub_buf (s : SpanBytes) (o l : Nat) : (s.sub o l).buf = s.buf := rfl
@[simp] theorem sub_off (s : SpanBytes) (o l : Nat) : (s.sub o l).off = s.off + o := rfl
@[simp] theorem sub_len (s : SpanBytes) (o l : Nat) : (s.sub o l).len = l := rfl

/-- A sub-window stays well-formed while it lies inside the parent window. -/
theorem sub_wf (s : SpanBytes) (o l : Nat) (h : s.Wf) (hin : o + l ≤ s.len) :
    (s.sub o l).Wf := by
  unfold Wf sub at *; simp only; omega

/-- **The sub-window denotes to the offset slice of the parent** — `buf[off+o ..
+l]` is exactly the `(o,l)` slice of the parent's denotation. So naming a
sub-window copies nothing and its meaning is the corresponding slice of the
request bytes. -/
theorem denote_sub (s : SpanBytes) (o l : Nat) (h : s.Wf) (hin : o + l ≤ s.len) :
    (s.sub o l).denote = (s.denote.drop o).take l := by
  rw [← read_eq_denote _ (sub_wf s o l h hin), ← read_eq_denote s h]
  apply List.ext_getElem
  · rw [length_read, sub_len, List.length_take, List.length_drop, length_read]
    omega
  · intro i hi _
    rw [length_read, sub_len] at hi
    have hlt : o + i < s.read.length := by rw [length_read]; omega
    rw [getByte_eq_read_getElem _ i (by rw [length_read, sub_len]; exact hi)]
    rw [List.getElem_take, List.getElem_drop, getByte_eq_read_getElem s (o+i) hlt]
    show s.buf.get! (s.off + o + i) = s.buf.get! (s.off + (o + i))
    rw [Nat.add_assoc]

/-! ## Arena entries as offset windows into the SAME buffer

The deployed head parser (`Arena.Parse.parse`) already produces `(offset, len)`
view `Entry`s into its main arena — which, when the parser is driven by `s.read`,
IS the borrowed request buffer. `entryWindow` re-presents such an entry as a
`SpanBytes` window into `s.buf`, and `entryWindow_denote` proves that window
denotes to *exactly* the bytes the deployed adapter resolves for that entry
(`Reactor.Config.resolveBytes`). So the parse's fields are borrowed offset windows
into the recv buffer — no copy — with their meaning proven equal to the deployed
resolution. -/

/-- A main-arena view entry, re-presented as a borrowed `(off,len)` window into
`s.buf` (the recv buffer). No bytes copied. -/
def entryWindow (s : SpanBytes) (e : Arena.Entry) : SpanBytes :=
  s.sub e.physOff e.len.toNat

/-- **A main-arena parse entry is a borrowed buffer window with the resolved
bytes.** When the deployed parser is driven by `s.read` (so its main arena is the
borrowed buffer) and `e` is an in-bounds main-arena entry, the offset window
`entryWindow s e` denotes to exactly the bytes the deployed adapter resolves —
`Reactor.Config.resolveBytes`. The parse's method / target / version / value
fields are therefore zero-copy windows into the recv buffer. -/
theorem entryWindow_denote (s : SpanBytes) (store : Arena.Store) (e : Arena.Entry)
    (hmain : store.main = s.read.toArray)
    (hnot : e.inSidecar = false) (hwf : s.Wf) (hib : store.InBounds e) :
    (s.entryWindow e).denote = Reactor.Config.resolveBytes store e := by
  -- unfold the discriminant-dependent pieces on the main-arena side
  have harena : store.arenaOf e = store.main := by unfold Arena.Store.arenaOf; rw [hnot]; rfl
  have hphys : e.physOff = e.off.toNat := by unfold Arena.Entry.physOff; rw [hnot]; rfl
  -- InBounds gives  physOff + len ≤ main.size = read.length = len
  have hsize : store.main.size = s.len := by rw [hmain]; simp [length_read]
  have hbound : e.physOff + e.len.toNat ≤ s.len := by
    have := hib; unfold Arena.Store.InBounds at this
    rw [harena, hsize] at this; exact this
  -- LHS: the window denotes to the (physOff, len) slice of read
  have hlhs : (s.entryWindow e).denote = (s.read.drop e.physOff).take e.len.toNat := by
    unfold entryWindow
    rw [denote_sub s e.physOff e.len.toNat hwf hbound, read_eq_denote s hwf]
  -- RHS: resolveBytes reduces to the same slice
  have hresolve : store.resolve e = some (store.main.extract e.physOff (e.physOff + e.len.toNat)) := by
    unfold Arena.Store.resolve
    rw [harena, hphys]
    rw [if_pos (by rw [hsize, ← hphys]; exact hbound)]
  have hrhs : Reactor.Config.resolveBytes store e = (s.read.drop e.physOff).take e.len.toNat := by
    unfold Reactor.Config.resolveBytes
    rw [hresolve]
    show (store.main.extract e.physOff (e.physOff + e.len.toNat)).toList = _
    rw [hmain, Array.toList_extract, Array.toList_toArray, List.extract_eq_drop_take]
    congr 1; omega
  rw [hlhs, hrhs]

end SpanBytes
end Datapath
