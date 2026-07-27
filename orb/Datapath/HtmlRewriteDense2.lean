import Datapath.HtmlRewriteDense

/-!
# Datapath.HtmlRewriteDense2 — the FULLY-DENSE html-rewrite: no token `List` on the
compute path, proven byte-identical to the DEPLOYED `rewriteBytes`.

`Datapath.HtmlRewriteDense` made the html-rewrite body transform dense at the
INPUT (index-native `ByteArray.foldl`, no `input.toList`) and the OUTPUT
(`ByteArray.push` render). But it ran the DEPLOYED `feedF` state machine, whose
state `FState` is still `List`-typed: `curRev : List UInt8` (a per-byte `cons`,
the O(body) cost that caps the win) and `toks : List Token` with `Token` carrying
`List UInt8`. So the TOKENIZER INTERMEDIATE stayed a cons-list.

This module removes that last `List`. It defines:

* `FStateD` — the tokenizer state fully dense: the current run `cur : ByteArray`
  held in FORWARD order (so extending it is an O(1) `ByteArray.push`, not the
  reversed-`cons` `feedF` uses), and `toks : Array DToken` with each token's bytes
  a `ByteArray`. NO `List UInt8` anywhere in the state.
* `feedFD` — the same state-machine transitions as the deployed `feedF`, but
  accumulating the dense state (`ByteArray.push` per byte, `Array.push` per token).
  Proven `(feedFD s b).denote = feedF s.denote b` — one dense step simulates one
  deployed step under the denotation `FStateD.denote : FStateD → FState`.
* `rewriteStateD` / `rewriteBytesDense2` — the dense render + composition. NO
  `List UInt8` and NO `.toList` on the compute path (the token bytes are
  `ByteArray`, the token list is an `Array`).
* `rewriteBytesDense2_refines` — byte-identical to the DEPLOYED
  `Reactor.Stage.HtmlRewrite.rewriteBytes`. The `List` appears ONLY on the spec
  (RHS); the compute path materialises no token `List`.

★ This is ADDITIVE: the deployed `feedF`/`FState`/`rewriteBytes` are UNTOUCHED. The
dense state is grounded in the deployed one by `FStateD.denote` and a per-step
simulation, exactly as the ByteSeq stages ground their flat ops in the `List` spec.
The token-`List` is killable additively — 2.35× was NOT the additive ceiling.
-/

namespace Datapath.HtmlRewriteDense2

open HtmlRewrite (Token TState Mode FState feedF initF tokenizeFast flush lt gt FState.decode)
open Reactor.Stage.HtmlRewrite (renderTok rewriteState rewriteBytes)
open Datapath.HtmlRewriteDense (byteArray_foldl_toList empty_data_toList)

/-! ## `ByteArray` helper laws (append/size denotations, proof-side only) -/

/-- `ByteArray.append` denotes list concatenation (same technique as
`Datapath.ByteSeq.instByteSeqArray.append_denote`). Proof-side only. -/
theorem byteArray_append_toList (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList :=
  ByteArray.toList_data_append

/-- A `ByteArray` is empty (`size = 0`) iff its byte denotation is `[]`. The dense
`feedFD` closes a text run on `cur.size = 0` (O(1), dense); this bridges that
condition to the deployed `flush`'s `cur = []`. Proof-side only. -/
theorem ba_size_zero (a : ByteArray) : (a.size = 0) ↔ (a.data.toList = []) := by
  constructor
  · intro h
    apply List.eq_nil_of_length_eq_zero
    rw [Array.length_toList]; exact h
  · intro h
    have : a.data.toList.length = 0 := by rw [h]; rfl
    rw [Array.length_toList] at this; exact this

/-! ## The fully-dense token and tokenizer state -/

/-- A DENSE token: a text run or a `<…>` tag span, bytes held as a `ByteArray`
(never a `List UInt8`). -/
inductive DToken where
  | text (bytes : ByteArray)
  | tag (bytes : ByteArray)

/-- A dense token denotes the deployed `List`-byte `Token`. -/
def DToken.denote : DToken → Token
  | .text b => Token.text b.data.toList
  | .tag b  => Token.tag b.data.toList

/-- **The fully-dense tokenizer state.** `cur` is the in-progress run in FORWARD
(text) order — extended by an O(1) `ByteArray.push`, no reversed `cons`. `toks` is
the completed tokens in CHRONOLOGICAL order (oldest first), each token's bytes a
`ByteArray`. NO `List UInt8`. -/
structure FStateD where
  mode : Mode
  cur : ByteArray
  toks : Array DToken

/-- **The abstraction relation.** A dense state denotes the deployed `FState`: the
forward `cur` denotes to `feedF`'s reversed `curRev` (`cur.reverse`), and the
chronological dense `toks` denotes to `feedF`'s newest-first `toks` (`reverse` of
the denoted list). Proof-side only — never run on the datapath. -/
def FStateD.denote (s : FStateD) : FState :=
  { mode := s.mode
    curRev := s.cur.data.toList.reverse
    toks := (s.toks.toList.map DToken.denote).reverse }

/-- The initial dense state (denotes to `initF`). -/
def initFD : FStateD := { mode := .text, cur := ByteArray.empty, toks := #[] }

theorem initFD_denote : initFD.denote = initF := rfl

/-- `ByteArray.push` on the backing array (definitional). Proof-side simp helper. -/
theorem ba_push_data (a : ByteArray) (b : UInt8) : (a.push b).data = a.data.push b := rfl

/-- Extending a forward run (`push`) denotes to a `cons` on the reversed run. -/
theorem push_curRev (a : ByteArray) (b : UInt8) :
    (a.push b).data.toList.reverse = b :: a.data.toList.reverse := by
  rw [ba_push_data, Array.toList_push, List.reverse_append]; rfl

/-- Pushing a dense token denotes to a `cons` (newest first) on the reversed
denoted token list — the deployed `toks` accumulation. -/
theorem push_toks (arr : Array DToken) (t : DToken) :
    ((arr.push t).toList.map DToken.denote).reverse
      = t.denote :: (arr.toList.map DToken.denote).reverse := by
  rw [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append]; rfl

/-- **One dense step.** The DEPLOYED `feedF` transitions, accumulating the dense
state: extend the run with `cur.push b` (O(1), no `cons`); on `<` close the text
run into an `Array` token (dropping an empty run, as `flush` does) and start the
tag run at `#[<]`; on `>` close the tag run (bytes `< … >`) into a token. NO
`List UInt8`. -/
def feedFD (s : FStateD) (b : UInt8) : FStateD :=
  match s.mode with
  | .text =>
    if b = lt then
      { mode := .tag
        cur := ByteArray.empty.push lt
        toks := if s.cur.size = 0 then s.toks else s.toks.push (DToken.text s.cur) }
    else
      { s with cur := s.cur.push b }
  | .tag =>
    if b = gt then
      { mode := .text
        cur := ByteArray.empty
        toks := s.toks.push (DToken.tag (s.cur.push gt)) }
    else
      { s with cur := s.cur.push b }

/-- **The per-step simulation.** One dense step denotes to one deployed step: the
dense state machine computes the identical tokenizer state as the deployed
`feedF`, under `FStateD.denote`. This is the whole faithfulness argument — the
dense `push` accumulation mirrors the `cons` accumulation exactly. -/
theorem feedFD_denote (s : FStateD) (b : UInt8) :
    (feedFD s b).denote = feedF s.denote b := by
  cases hm : s.mode with
  | text =>
    by_cases hb : b = lt
    · by_cases hc : s.cur.size = 0
      · -- close an EMPTY text run: flush drops it
        have hnil : s.cur.data.toList = [] := (ba_size_zero s.cur).mp hc
        simp only [feedFD, feedF, FStateD.denote, flush, hm, hb, if_true, if_pos hc,
          push_curRev, empty_data_toList, List.reverse_nil, List.reverse_reverse, if_pos hnil]
      · -- close a NON-EMPTY text run: flush emits a text token
        have hnil : s.cur.data.toList ≠ [] := fun h => hc ((ba_size_zero s.cur).mpr h)
        simp only [feedFD, feedF, FStateD.denote, flush, hm, hb, if_true, if_neg hc,
          push_curRev, push_toks, DToken.denote, empty_data_toList, List.reverse_nil,
          List.reverse_reverse, if_neg hnil]
    · -- extend the text run
      simp only [feedFD, feedF, FStateD.denote, hm, if_neg hb, push_curRev]
  | tag =>
    by_cases hb : b = gt
    · -- close the tag run (bytes `< … >`)
      simp only [feedFD, feedF, FStateD.denote, hm, hb, if_true, DToken.denote,
        ba_push_data, Array.toList_push, empty_data_toList, List.map_append, List.map_cons,
        List.map_nil, List.reverse_append, List.reverse_nil, List.reverse_cons,
        List.reverse_reverse, List.nil_append, List.singleton_append]
    · -- extend the tag run
      simp only [feedFD, feedF, FStateD.denote, hm, if_neg hb, push_curRev]

/-- Fold the dense step over a byte list, then denote, equals denote-then-fold the
deployed step — lifts the per-step simulation to the whole fold. -/
theorem foldl_feedFD_denote (l : List UInt8) :
    ∀ s : FStateD, (l.foldl feedFD s).denote = l.foldl feedF s.denote := by
  induction l with
  | nil => intro s; rfl
  | cons b bs ih =>
    intro s
    simp only [List.foldl_cons]
    rw [ih (feedFD s b), feedFD_denote]

/-- **The dense tokenizer.** Fold `feedFD` over the `ByteArray` body BY INDEX
(`ByteArray.foldl` — the native bounded loop, no `input.toList`). The state is
FULLY dense; no token `List` is built. -/
def tokenizeFastD (bs : ByteArray) : FStateD := ByteArray.foldl feedFD initFD bs

/-- The dense tokenizer denotes to the deployed `feedF` fold over the byte
denotation — the fully-dense walk computes the identical `FState`. -/
theorem tokenizeFastD_denote (bs : ByteArray) :
    (tokenizeFastD bs).denote = bs.data.toList.foldl feedF initF := by
  unfold tokenizeFastD
  rw [byteArray_foldl_toList, foldl_feedFD_denote, initFD_denote]

/-! ## The dense render — tokens read from the dense state, output pushed -/

/-- Render one dense token: keep a text run's bytes, drop a tag span (a `ByteArray`,
no `List`). -/
def renderTokD : DToken → ByteArray
  | .text b => b
  | .tag _  => ByteArray.empty

theorem renderTokD_denote (t : DToken) :
    (renderTokD t).data.toList = renderTok t.denote := by
  cases t <;> rfl

/-- Render the completed dense tokens (chronological order) into a `ByteArray` by
appending each token's rendered bytes — no `flatMap`/`cons` spine. -/
def renderToksD (toks : Array DToken) : ByteArray :=
  toks.foldl (fun acc t => acc ++ renderTokD t) ByteArray.empty

theorem renderFoldD (l : List DToken) :
    ∀ acc : ByteArray,
      (l.foldl (fun acc t => acc ++ renderTokD t) acc).data.toList
        = acc.data.toList ++ (l.map DToken.denote).flatMap renderTok := by
  induction l with
  | nil => intro acc; simp
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, List.flatMap_cons]
    rw [ih (acc ++ renderTokD t), byteArray_append_toList, renderTokD_denote]
    simp [List.append_assoc]

theorem renderToksD_denote (toks : Array DToken) :
    (renderToksD toks).data.toList = (toks.toList.map DToken.denote).flatMap renderTok := by
  unfold renderToksD
  rw [← Array.foldl_toList, renderFoldD, empty_data_toList, List.nil_append]

/-- **The dense render of a dense state.** Render the tokens, then append the
trailing text run (kept in `Mode.text`, dropped in `Mode.tag`) — all `ByteArray`
ops, no `List UInt8`. -/
def rewriteStateD (s : FStateD) : ByteArray :=
  let base := renderToksD s.toks
  match s.mode with
  | Mode.text => base ++ s.cur
  | Mode.tag  => base

/-- The dense render denotes to `rewriteState` of the DECODED denoted state — i.e.
the deployed render on the tokenizer state the dense state stands for. -/
theorem rewriteStateD_toList (s : FStateD) :
    (rewriteStateD s).data.toList = rewriteState (FState.decode s.denote) := by
  unfold rewriteStateD rewriteState FState.decode FStateD.denote
  simp only [List.reverse_reverse]
  cases hm : s.mode with
  | text =>
    simp only [hm]
    rw [byteArray_append_toList, renderToksD_denote]
  | tag =>
    simp only [hm]
    rw [renderToksD_denote, List.append_nil]

/-! ## The fully-dense body transform — byte-identical to the DEPLOYED `rewriteBytes` -/

/-- **The fully-dense body transform.** Tokenize the body index-native into the
FULLY-DENSE state (no token `List`), then render into a `ByteArray`. NO `List UInt8`
and NO `.toList` on the compute path — grep `feedFD`, `rewriteStateD`,
`renderToksD`, `tokenizeFastD`: the current run, the token bytes, and the render
are all `ByteArray`/`Array`. -/
@[export drorb_rewrite_bytes_dense2]
def rewriteBytesDense2 (bs : ByteArray) : ByteArray := rewriteStateD (tokenizeFastD bs)

/-- **THE REFINEMENT.** The fully-dense transform is byte-identical to the DEPLOYED
`Reactor.Stage.HtmlRewrite.rewriteBytes` on the byte denotation. The `List UInt8`
appears ONLY on the spec (RHS); the compute path materialises NO token `List`. -/
theorem rewriteBytesDense2_refines (bs : ByteArray) :
    (rewriteBytesDense2 bs).data.toList = rewriteBytes bs.data.toList := by
  unfold rewriteBytesDense2 rewriteBytes
  rw [rewriteStateD_toList, tokenizeFastD_denote]
  rfl

/-! ## Non-vacuity — a concrete html body, fully-dense-rewritten -/

/-- `"<b>hi"` as a `ByteArray`. -/
def demoBodyBA2 : ByteArray := ⟨#[60, 98, 62, 104, 105]⟩

/-- The fully-dense rewrite equals the deployed rewrite on the concrete body. -/
example : (rewriteBytesDense2 demoBodyBA2).data.toList = rewriteBytes demoBodyBA2.data.toList :=
  rewriteBytesDense2_refines demoBodyBA2

/-- The fully-dense rewrite strips `<b>` to exactly `"hi"` (bytes `104, 105`). -/
theorem rewriteBytesDense2_demo_val :
    (rewriteBytesDense2 demoBodyBA2).data.toList = [104, 105] := by decide

/-- The fully-dense rewrite genuinely changes the body. -/
theorem rewriteBytesDense2_changes_demo :
    (rewriteBytesDense2 demoBodyBA2).data.toList ≠ demoBodyBA2.data.toList := by decide

-- Concrete non-vacuity: the demo body dense-rewrites to "hi".
#guard (rewriteBytesDense2 demoBodyBA2).data.toList == [104, 105]
-- Multi-tag body: "<a>x<b>y</b>" strips ALL tags, keeps "xy".
#guard (rewriteBytesDense2 ⟨"<a>x<b>y</b>".toUTF8.data⟩).data.toList
        == "xy".toUTF8.data.toList

/-! ## Axiom audit -/

#print axioms rewriteBytesDense2_refines

end Datapath.HtmlRewriteDense2
