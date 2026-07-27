import Reactor.Stage.HtmlRewrite
import HtmlRewrite.Basic

/-!
# Datapath.HtmlRewriteDense — the DENSE (index-native, `ByteArray`) body transform,
proven byte-identical to the DEPLOYED `Reactor.Stage.HtmlRewrite.rewriteBytes`.

The deployed html-rewrite stage runs `rewriteBytes = rewriteState (tokenizeFast bs)`
UNCONDITIONALLY on every response body — a stateful tokenizer FOLD over the body
bytes (`feedF` per byte) then a token render. On the deployed `List UInt8` body that
means the whole body is walked as a cons-list (requiring `input.toList` upstream) and
re-consed on output.

This module re-expresses that SAME transform over `ByteArray`, INDEX-NATIVE:

* `byteArray_foldl_toList` — the ONE generic stateful-fold combinator: folding any
  state machine `f` over a `ByteArray` by index (`ByteArray.foldl`, the native
  bounded loop, NO `toList`) equals `List.foldl f` over the byte denotation. Proven
  once, from the core loop, by induction on the fuel. This is the combinator the
  stateful body loop needs (the `foldCat_denote` analogue for a stateful fold).
* `tokenizeFastDense` — runs the deployed `feedF` state machine over the `ByteArray`
  by index; proven equal to `tokenizeFast bs.data.toList`.
* `rewriteStateDense` — renders the tokenizer state into a `ByteArray` by `push`
  (no `flatMap`/`++` cons-spine); proven `.data.toList = rewriteState s`.
* `rewriteBytesDense` — their composition; `rewriteBytesDense_refines` proves it is
  byte-identical to the deployed `rewriteBytes` (the `List` appears only on the SPEC
  side of the equality). The `ByteArray` compute path materialises NO body `List`.
-/

namespace Datapath.HtmlRewriteDense

open HtmlRewrite (Token TState Mode FState feedF initF tokenizeFast FState.decode)
open Reactor.Stage.HtmlRewrite (renderTok rewriteState rewriteBytes)

/-! ## The generic stateful-fold combinator — `ByteArray.foldl = List.foldl` -/

/-- The `ByteArray.foldlM` bounded loop equals the `Array.foldlM` loop on the backing
array, at equal `stop`. Induction on the fuel `i`; `bs[j] = bs.data[j]` definitionally,
so each step matches. -/
theorem foldlM_loop_eq {beta : Type u} (f : beta → UInt8 → beta) (bs : ByteArray) (stop : Nat)
    (h1 : stop ≤ bs.size) (h2 : stop ≤ bs.data.size) :
    ∀ (i j : Nat) (b : beta),
      ByteArray.foldlM.loop (m := Id) f bs stop h1 i j b
        = Array.foldlM.loop (m := Id) f bs.data stop h2 i j b := by
  intro i
  induction i with
  | zero => intro j b; unfold ByteArray.foldlM.loop Array.foldlM.loop; simp
  | succ i ih =>
    intro j b
    unfold ByteArray.foldlM.loop Array.foldlM.loop
    by_cases hlt : j < stop
    · simp only [hlt, dif_pos]
      show ByteArray.foldlM.loop (m := Id) f bs stop h1 i (j+1) (f b bs[j])
         = Array.foldlM.loop (m := Id) f bs.data stop h2 i (j+1) (f b bs.data[j])
      rw [ih]; rfl
    · simp only [hlt, dif_neg, not_false_iff]

/-- `ByteArray.foldl` (the native, index-native bounded loop — NO `toList`) equals
`Array.foldl` on the backing array. -/
theorem byteArray_foldl_data {beta : Type u} (f : beta → UInt8 → beta) (init : beta) (bs : ByteArray) :
    ByteArray.foldl f init bs = bs.data.foldl f init := by
  unfold ByteArray.foldl ByteArray.foldlM Array.foldl Array.foldlM Id.run
  rw [dif_pos (Nat.le_refl bs.size), dif_pos (Nat.le_refl bs.data.size)]
  simp only [Nat.sub_zero]
  exact foldlM_loop_eq f bs bs.size (Nat.le_refl _) (Nat.le_refl _) bs.size 0 init

/-- **THE generic stateful-fold combinator.** Folding a state machine `f` over a
`ByteArray` by index equals `List.foldl f` over the byte denotation — the `foldCat`
analogue for a stateful fold. Proven ONCE; the tokenizer reuses it with no
per-machine induction. The LHS reads the buffer by index (no `toList`); the `toList`
lives only on the spec RHS. -/
theorem byteArray_foldl_toList {beta : Type u} (f : beta → UInt8 → beta) (init : beta) (bs : ByteArray) :
    ByteArray.foldl f init bs = bs.data.toList.foldl f init := by
  rw [byteArray_foldl_data, Array.foldl_toList]

/-! ## The dense tokenizer — the deployed `feedF` machine, run over the buffer by index -/

/-- **Dense tokenizer.** Run the DEPLOYED `feedF` state machine over the `ByteArray`
by index (`ByteArray.foldl` — the native bounded loop, NO `input.toList`), then
`decode` once. Same machine, same state, buffer read index-native. -/
def tokenizeFastDense (bs : ByteArray) : TState :=
  (ByteArray.foldl feedF initF bs).decode

/-- `tokenizeFastDense bs` is exactly the deployed `tokenizeFast` on the byte
denotation — the index-native walk computes the identical tokenizer state. -/
theorem tokenizeFastDense_eq (bs : ByteArray) :
    tokenizeFastDense bs = tokenizeFast bs.data.toList := by
  unfold tokenizeFastDense tokenizeFast
  rw [byteArray_foldl_toList]

/-! ## The dense render — tokens written into a `ByteArray` by `push` (no cons-spine) -/

/-- Push every byte of a list onto a `ByteArray` accumulator (the flat concat of a
run into the uniquely-owned buffer). -/
def pushList (acc : ByteArray) (l : List UInt8) : ByteArray := l.foldl ByteArray.push acc

/-- `pushList` denotes appending the list — proven once, by induction. -/
theorem pushList_toList (l : List UInt8) :
    ∀ acc : ByteArray, (pushList acc l).data.toList = acc.data.toList ++ l := by
  induction l with
  | nil => intro acc; simp [pushList]
  | cons b l ih =>
    intro acc
    unfold pushList
    simp only [List.foldl_cons]
    rw [show (l.foldl ByteArray.push (acc.push b)) = pushList (acc.push b) l from rfl, ih]
    rw [show (acc.push b).data = acc.data.push b from rfl, Array.toList_push]
    simp

/-- **Dense render.** Render the completed tokens (chronological order) by pushing
each token bytes into a `ByteArray` (drop tag spans via `renderTok`), then append
the trailing text run — all by `push`, NO `flatMap`/`++` cons-spine. -/
def rewriteStateDense (s : TState) : ByteArray :=
  let base := s.toks.reverse.foldl (fun acc t => pushList acc (renderTok t)) ByteArray.empty
  match s.mode with
  | Mode.text => pushList base s.cur
  | Mode.tag  => base

/-- The token-render fold denotes the `flatMap renderTok` of the token list. -/
theorem renderFold_toList (toks : List Token) :
    ∀ acc : ByteArray,
      (toks.foldl (fun acc t => pushList acc (renderTok t)) acc).data.toList
        = acc.data.toList ++ toks.flatMap renderTok := by
  induction toks with
  | nil => intro acc; simp
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [ih (pushList acc (renderTok t)), pushList_toList]
    simp [List.append_assoc]

/-- `ByteArray.empty` denotes the empty byte list. -/
theorem empty_data_toList : (ByteArray.empty).data.toList = [] := rfl

/-- **Dense render is byte-identical to `rewriteState`.** -/
theorem rewriteStateDense_toList (s : TState) :
    (rewriteStateDense s).data.toList = rewriteState s := by
  unfold rewriteStateDense rewriteState
  cases hm : s.mode with
  | text =>
    simp only [hm]
    rw [pushList_toList, renderFold_toList, empty_data_toList, List.nil_append]
  | tag =>
    simp only [hm]
    rw [renderFold_toList, empty_data_toList, List.nil_append, List.append_nil]

/-! ## The dense body transform — byte-identical to the DEPLOYED `rewriteBytes` -/

/-- **The dense body transform.** Tokenize the `ByteArray` body index-native, render
the tokens back into a `ByteArray` by `push`. NO body `List` on the compute path. -/
def rewriteBytesDense (bs : ByteArray) : ByteArray :=
  rewriteStateDense (tokenizeFastDense bs)

/-- **THE REFINEMENT.** The dense `ByteArray` transform is byte-identical to the
DEPLOYED `Reactor.Stage.HtmlRewrite.rewriteBytes` run on the byte denotation. The
`List UInt8` appears ONLY on the spec (RHS); the compute path is pure `ByteArray`. -/
theorem rewriteBytesDense_refines (bs : ByteArray) :
    (rewriteBytesDense bs).data.toList = rewriteBytes bs.data.toList := by
  unfold rewriteBytesDense rewriteBytes
  rw [rewriteStateDense_toList, tokenizeFastDense_eq]

/-! ## Non-vacuity — a concrete html body, dense-rewritten, equals the deployed rewrite
    and genuinely changes the bytes. -/

/-- `"<b>hi"` as a `ByteArray`. -/
def demoBodyBA : ByteArray := ⟨#[60, 98, 62, 104, 105]⟩

/-- The dense rewrite strips `<b>` to `"hi"` — the SAME bytes the deployed rewrite
computes on the list body. -/
example : (rewriteBytesDense demoBodyBA).data.toList = rewriteBytes demoBodyBA.data.toList :=
  rewriteBytesDense_refines demoBodyBA

/-- The dense rewrite genuinely changes the body: `"<b>hi"` becomes `"hi"`. -/
theorem rewriteBytesDense_changes_demo :
    (rewriteBytesDense demoBodyBA).data.toList ≠ demoBodyBA.data.toList := by decide

/-- Concrete: the dense output is exactly `"hi"` (bytes `104, 105`). -/
theorem rewriteBytesDense_demo_val :
    (rewriteBytesDense demoBodyBA).data.toList = [104, 105] := by decide

end Datapath.HtmlRewriteDense
