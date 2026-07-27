import Datapath.Refinement

/-!
# Datapath.ByteSeq — a byte-sequence TYPECLASS and the once-proven op refinements

## Why this file exists (the de-risk question)

The fan-out flat path (`Datapath.FlatBody`, `Datapath.FlatStage`, the
`FlatStage_*` siblings) writes **two expressions per stage**: the deployed
`List UInt8`-typed stage *and* a hand-written flat (`ByteArray` / `Array UInt8`)
sibling, plus a bespoke `<stage>_refines` proof grounding one in the other. That
is the LOC baseline (`~40–140` per stage). `Datapath.RefinesData` collapses the
*framework* duplication (one `Denote` class, one functor law) but each **stage**
is still expressed twice.

This module tests the *polymorphic* alternative (ember's metaprogramming
direction): a class `ByteSeq T` of the byte-sequence ops a real stage needs, with
each op's **denotation law** proven ONCE per instance. A stage written ONCE over
an abstract `[ByteSeq T]` then instantiates at `List UInt8` (the spec) and
`ByteArray` (the fast path), and the question the prototype answers is whether the
**whole-stage refinement follows from the op laws** (a mechanical `simp` chain, no
per-stage induction) or still needs bespoke per-stage work (defeating the point).

`Datapath.ByteSeqProto` writes the ONE real stage and settles that question; this
file is the class, the two instances (with the op laws proven once), and the ONE
generic recursion lemma (`foldCat_denote`) that every fold-shaped stage reuses.

## The class

`ByteSeq T` carries the ops a serialize/body stage uses — `empty`, `append`,
`singleton`, `push`, `size`, `get?` — plus the **denotation** `toBytes : T → List
UInt8` (the abstraction relation, exactly `Datapath.Refinement.FlatRep.denote`)
and the LAWS relating each op to its `List UInt8` meaning. The laws are the
op-level refinements: `append_denote`, `singleton_denote`, `empty_denote`,
`push_denote`, `size_denote`, `get?_denote`. Proven once per instance; a stage's
whole refinement is discharged from them.

## The two instances

* `instByteSeqList : ByteSeq (List UInt8)` — the **spec**: `toBytes := id`, every
  op is the `List` op, every law is `rfl`/`simp`. A stage at this instance *is*
  the deployed `List`-typed stage.
* `instByteSeqArray : ByteSeq ByteArray` — the **fast, genuinely flat** path:
  `append := ByteArray.append` (a packed `Array` copy, NO cons-spine), `push :=
  ByteArray.push` (amortized `O(1)`), `size := ByteArray.size` (`O(1)`, no length
  walk), `toBytes := (·.data.toList)` — the denotation only, never run on the
  datapath. Each op law is proven once from the core `Array`/`ByteArray` lemmas.
-/

namespace Datapath.ByteSeq

/-- **The byte-sequence typeclass.** The ops a real serialize/body stage needs,
plus the denotation `toBytes` (the abstraction relation to the `List UInt8` spec)
and the LAWS relating each op to its spec meaning. Instances prove the laws ONCE;
a stage written over `[ByteSeq T]` gets its whole refinement from them. -/
class ByteSeq (T : Type) where
  /-- Empty sequence. -/
  empty : T
  /-- Concatenation. -/
  append : T → T → T
  /-- One-byte sequence. -/
  singleton : UInt8 → T
  /-- Push a byte onto the end (amortised on the flat instance). -/
  push : T → UInt8 → T
  /-- Length (`O(1)` on the flat instance). -/
  size : T → Nat
  /-- Indexed read. -/
  get? : T → Nat → Option UInt8
  /-- **The denotation** — the abstract `List UInt8` this value stands for. On the
  running (fast) datapath this is never computed; it is the spec relation. -/
  toBytes : T → List UInt8
  /-- Law: the empty sequence denotes the empty list. -/
  empty_denote : toBytes empty = []
  /-- Law: append denotes list concatenation (the ++ op refinement). -/
  append_denote : ∀ a b, toBytes (append a b) = toBytes a ++ toBytes b
  /-- Law: singleton denotes the one-element list. -/
  singleton_denote : ∀ b, toBytes (singleton b) = [b]
  /-- Law: push denotes appending the one-element list. -/
  push_denote : ∀ a b, toBytes (push a b) = toBytes a ++ [b]
  /-- Law: size denotes the list length. -/
  size_denote : ∀ a, size a = (toBytes a).length
  /-- Law: get? denotes the list index. -/
  get?_denote : ∀ a i, get? a i = (toBytes a)[i]?

attribute [simp] ByteSeq.empty_denote ByteSeq.append_denote ByteSeq.singleton_denote
  ByteSeq.push_denote ByteSeq.size_denote ByteSeq.get?_denote

/-! ## The spec instance — `List UInt8`, `toBytes := id` -/

/-- **The spec instance.** Every op is the `List` op; `toBytes` is the identity.
A stage instantiated here *is* the deployed `List UInt8`-typed stage — no separate
"spec expression" is written. Every law is `rfl` / `by simp`. -/
instance instByteSeqList : ByteSeq (List UInt8) where
  empty := []
  append := (· ++ ·)
  singleton := ([·])
  push := fun a b => a ++ [b]
  size := List.length
  get? := fun a i => a[i]?
  toBytes := id
  empty_denote := rfl
  append_denote := fun _ _ => rfl
  singleton_denote := fun _ => rfl
  push_denote := fun _ _ => rfl
  size_denote := fun _ => rfl
  get?_denote := fun _ _ => rfl

/-! ## The fast instance — `ByteArray`, genuinely flat -/

/-- **The fast instance — genuinely flat.** `append` is `ByteArray.append` (a
packed `Array UInt8` copy; NO cons-spine), `push` is `ByteArray.push` (amortised
`O(1)`), `size` is the `O(1)` `ByteArray.size` (no `List.length` walk). `toBytes`
is `(·.data.toList)` — the DENOTATION, used only on the spec side of a refinement,
never on the running datapath. Each law is proven once from core `Array` lemmas. -/
instance instByteSeqArray : ByteSeq ByteArray where
  empty := ByteArray.empty
  append := ByteArray.append
  singleton := fun b => ⟨#[b]⟩
  push := ByteArray.push
  size := ByteArray.size
  get? := fun a i => a.data[i]?
  toBytes := fun a => a.data.toList
  empty_denote := rfl
  append_denote := fun a b => by
    show (a ++ b).data.toList = a.data.toList ++ b.data.toList
    rw [ByteArray.toList_data_append]
  singleton_denote := fun b => rfl
  push_denote := fun a b => by
    show (a.push b).data.toList = a.data.toList ++ [b]
    rw [show (a.push b).data = a.data.push b from rfl, Array.toList_push]
  size_denote := fun a => by
    show a.size = a.data.toList.length
    rw [ByteArray.size, Array.length_toList]
  get?_denote := fun a i => Array.getElem?_toList.symm

/-! ## The ONE generic recursion lemma — reused by every fold-shaped stage

A stage that concatenates a *list* of fragments (the serializer head, chunked
bodies, multi-fragment assembly) folds `append` over that list. `foldCat` is that
combinator, and `foldCat_denote` proves its denotation ONCE, by induction, over an
ABSTRACT `[ByteSeq T]` — using only `append_denote` and `empty_denote`. Every
fold-shaped stage reuses it with NO further induction: this is the single place
induction is paid for the whole family. -/

/-- Fold `append` over a list of fragments into a flat accumulator — the flat
concat of a fragment list, polymorphic over the byte representation. -/
def foldCat {T : Type} [ByteSeq T] (frags : List T) : T :=
  frags.foldl ByteSeq.append ByteSeq.empty

/-- Accumulator form (needed for the induction): folding into `acc` denotes to
`acc`'s bytes followed by the flattened per-fragment denotations. Proven ONCE,
generic in `T`, from `append_denote` alone. -/
theorem foldl_append_denote {T : Type} [ByteSeq T] (frags : List T) :
    ∀ acc : T, ByteSeq.toBytes (frags.foldl ByteSeq.append acc)
      = ByteSeq.toBytes acc ++ (frags.map ByteSeq.toBytes).flatten := by
  induction frags with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons]
    rw [ih (ByteSeq.append acc x), ByteSeq.append_denote]
    simp [List.append_assoc]

/-- **THE generic recursion lemma.** `foldCat` denotes to the `flatten` of the
per-fragment denotations — a flat fold refines list concatenation, once and for
all, for EVERY `ByteSeq` instance. Every fold-shaped stage's refinement reuses
this; no stage re-does the induction. -/
@[simp] theorem foldCat_denote {T : Type} [ByteSeq T] (frags : List T) :
    ByteSeq.toBytes (foldCat frags) = (frags.map ByteSeq.toBytes).flatten := by
  rw [foldCat, foldl_append_denote frags ByteSeq.empty, ByteSeq.empty_denote]
  simp

/-- At the spec instance `toBytes = id`, so `foldCat` on a `List UInt8` fragment
list is exactly its `flatten` — the spec-side shape the grounding lemma uses. -/
@[simp] theorem foldCat_list (frags : List (List UInt8)) :
    foldCat frags = frags.flatten := by
  have h := foldCat_denote frags
  simpa [ByteSeq.toBytes, instByteSeqList] using h

end Datapath.ByteSeq
