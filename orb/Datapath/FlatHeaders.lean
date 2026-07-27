import Datapath.ByteRefine

/-!
# Datapath.FlatHeaders — the flat representation of the response HEADER BLOCK
(the cons-list-removal crux the scope named), and its refinement of the
`List (Bytes × Bytes)` header block.

The deployed response is `Reactor.Response`, whose header block is
`headers : List (Bytes × Bytes)` — an outer cons-spine of `(name, value)` pairs,
each pair itself a `List UInt8 × List UInt8`. Every header-transform stage
(`securityheaders`, `cors`, `headerRewrite`, the deploy header stage, …) grows
that spine with `List.++`/`addHeader` — an `O(n)` cons copy of the whole header
list PER STAGE — and the serializer walks the same spine once more
(`renderHeaders`). That outer cons-spine is the header-block half of the
cons-list cost.

This module introduces the flat concrete representation the stages should build
on instead: **`HdrBlock`**, the header list held in a contiguous
`Array (Bytes × Bytes)` (the header pairs; the *value* bytes stay `List UInt8`,
they are refined separately by `Datapath.ByteRefine`). A stage grows it with
`Array.push` — amortized `O(1)`, no per-stage spine copy — and the bridge back to
the model is `denote : HdrBlock → List (Bytes × Bytes)` (`Array.toList`), so the
`List`-typed spec header block, and every lane stated over it, is untouched.

## The refinement — a header-grain sibling of `Datapath.Refinement`

`Datapath.Refinement`'s `FlatRep`/`Refines`/`RefinesFn` calculus is fixed to the
byte grain (`denote : C → List UInt8`). The response header block lives at a
*different* grain — `List (Bytes × Bytes)` — so a header-transform stage's
naturality square is stated there. The functor law is generic (the proof is the
same one-liner), so this is the `List (Bytes × Bytes)` instance of the very same
pattern:

* `RefinesHdr a h := h.denote = a` — the concrete `HdrBlock` refines the abstract
  header list it denotes;
* `RefinesHdrFn fa fc := ∀ h, (fc h).denote = fa h.denote` — a refined
  header-combinator (the naturality square);
* `RefinesHdrFn.comp` — the functor law: a pipeline of refined header stages
  refines the composed `List` header pipeline **by construction** (so the
  remaining header-transform stages compose for free, exactly like the byte
  grain).

The crux lemma is `HdrBlock.denote_foldAddHeader`: folding a fixed header set onto
the flat block via `Array.push` denotes to the `List` append `denote h ++ xs` —
the flat-`push` sibling of `Reactor.Pipeline.build_addHeaders` (the `List` side).

The join back to the byte grain (so the whole thing is *byte-identical*) is
`flatRenderBlock` / `flatRenderBlock_refines`: the flat block renders to exactly
`Reactor.renderHeaders (denote h)`, reusing `Datapath.ByteRefine`'s existing
byte-grain `foldAppend` calculus (`renderHeaders_eq_flatten` +
`foldAppend_toArray_refines`). `RefinesHdrFn.compRender` is the grain-crossing
composition (header stage ⋙ renderer) that makes a header stage's flat output
byte-identical to the deployed stage's rendered header bytes.
-/

namespace Datapath.FlatHeaders

open Proto (Bytes)
open Datapath.Refinement

/-! ## The flat header block -/

/-- **The flat header-block representation.** The response header spine held in a
contiguous `Array (Bytes × Bytes)` instead of a per-header cons cell. A stage
grows it with `Array.push` (amortized `O(1)`, no per-stage spine copy); the value
bytes inside each pair stay `List UInt8` and are refined by `Datapath.ByteRefine`
separately. This is the header-block analogue of `Datapath.SpanBytes` for the
request window. -/
structure HdrBlock where
  /-- The header pairs, flat and contiguous. -/
  headers : Array (Bytes × Bytes)
deriving Repr

namespace HdrBlock

/-- **The abstraction relation.** The `List (Bytes × Bytes)` header block a flat
`HdrBlock` denotes — `Array.toList`, exactly mirroring `SpanBytes.denote` /
`ByteArray.toList` at the header grain. In the running datapath `denote` lowers to
zero work: the pairs are already contiguous. -/
def denote (h : HdrBlock) : List (Bytes × Bytes) := h.headers.toList

/-- Materialize a header list into a flat block — the leaf of a derivation (in the
running datapath the pairs are already flat and this is identity). -/
def ofList (hs : List (Bytes × Bytes)) : HdrBlock := ⟨hs.toArray⟩

/-- Push one header onto the flat block — an amortized-`O(1)` `Array.push`, the
flat sibling of `ResponseBuilder.addHeader`'s `List.++ [nv]`. -/
def addHeader (h : HdrBlock) (nv : Bytes × Bytes) : HdrBlock := ⟨h.headers.push nv⟩

/-- The empty flat block. -/
def empty : HdrBlock := ⟨#[]⟩

@[simp] theorem denote_empty : empty.denote = [] := rfl

@[simp] theorem denote_ofList (hs : List (Bytes × Bytes)) : (ofList hs).denote = hs := by
  show hs.toArray.toList = hs
  rw [List.toList_toArray]

/-- Pushing a header denotes to the `List` append — the single-step naturality of
`addHeader`. -/
@[simp] theorem denote_addHeader (h : HdrBlock) (nv : Bytes × Bytes) :
    (h.addHeader nv).denote = h.denote ++ [nv] := by
  show (h.headers.push nv).toList = h.headers.toList ++ [nv]
  rw [Array.toList_push]

/-- **THE HEADER FOLD COMBINATOR — the crux.** Folding a fixed header set `xs`
onto the flat block via `Array.push` denotes to the `List` append `denote h ++ xs`.
This is the flat-`push` sibling of `Reactor.Pipeline.build_addHeaders` (the `List`
side): where the deployed builder does `xs.foldl addHeader b |>.build = b.build ++ xs`
by copying the header spine per step, the flat block does the same push-fold with
no per-step spine copy, and this lemma proves the two agree on the denotation. It
is what every header-transform stage's refinement rides on. -/
theorem denote_foldAddHeader (xs : List (Bytes × Bytes)) :
    ∀ h : HdrBlock, (xs.foldl addHeader h).denote = h.denote ++ xs := by
  induction xs with
  | nil => intro h; simp
  | cons nv rest ih =>
    intro h
    rw [List.foldl_cons, ih (h.addHeader nv), denote_addHeader]
    simp [List.append_assoc]

end HdrBlock

/-! ## The header-grain refinement calculus (the `List (Bytes × Bytes)` sibling of
`Datapath.Refinement`) -/

/-- **The header-grain refinement relation.** A flat `HdrBlock` `h` refines the
abstract header list `a` exactly when it denotes back to `a` — the header-grain
`Datapath.Refinement.Refines`. -/
def RefinesHdr (a : List (Bytes × Bytes)) (h : HdrBlock) : Prop := h.denote = a

theorem RefinesHdr.denote_eq {a : List (Bytes × Bytes)} {h : HdrBlock}
    (r : RefinesHdr a h) : h.denote = a := r

@[simp] theorem RefinesHdr.refl (h : HdrBlock) : RefinesHdr h.denote h := rfl

/-- **A refined header combinator** — the naturality square at the header grain:
running the flat header op `fc` and denoting equals denoting and running the
abstract `List` header op `fa`. The single obligation per header-transform stage;
`RefinesHdrFn.comp` then lifts it to whole header pipelines. -/
def RefinesHdrFn (fa : List (Bytes × Bytes) → List (Bytes × Bytes))
    (fc : HdrBlock → HdrBlock) : Prop :=
  ∀ h : HdrBlock, (fc h).denote = fa h.denote

/-- **Point transfer.** A refined header combinator carries a refined input to a
refined output. -/
theorem RefinesHdrFn.apply {fa : List (Bytes × Bytes) → List (Bytes × Bytes)}
    {fc : HdrBlock → HdrBlock} (hf : RefinesHdrFn fa fc)
    {a : List (Bytes × Bytes)} {h : HdrBlock} (r : RefinesHdr a h) :
    RefinesHdr (fa a) (fc h) := by
  unfold RefinesHdr at r ⊢
  rw [hf h, r]

/-- **Compositionality — the functor law at the header grain.** The composite of
two refined header combinators refines the composite of the abstract header ops.
Consequence: a whole PIPELINE `gc ∘ fc` of refined header stages refines the
composed `List` header pipeline `ga ∘ fa` **by construction** — so the remaining
header-transform stages of `deployStagesFull2` compose for free, exactly as the
byte grain's `RefinesFn.comp` composes byte combinators. -/
theorem RefinesHdrFn.comp {fa ga : List (Bytes × Bytes) → List (Bytes × Bytes)}
    {fc gc : HdrBlock → HdrBlock} (hf : RefinesHdrFn fa fc) (hg : RefinesHdrFn ga gc) :
    RefinesHdrFn (ga ∘ fa) (gc ∘ fc) := by
  intro h
  simp only [Function.comp]
  rw [hg (fc h), hf h]

/-- The identity header stage is refined (the unit of the functor law). -/
theorem RefinesHdrFn.id : RefinesHdrFn id (id : HdrBlock → HdrBlock) := fun _ => rfl

/-- **`addHeader` is a refined header combinator.** Pushing a fixed header `nv`
onto the flat block refines the `List` append `· ++ [nv]`. -/
theorem refinesHdr_addHeader (nv : Bytes × Bytes) :
    RefinesHdrFn (fun hs => hs ++ [nv]) (fun h => h.addHeader nv) :=
  fun h => HdrBlock.denote_addHeader h nv

/-- **The header FOLD as a refined combinator.** Folding a fixed header set `xs`
onto the flat block refines the `List` append `· ++ xs`. This is the reusable
recipe every header-transform stage instantiates (with its own fixed `xs`). -/
theorem refinesHdr_foldAddHeader (xs : List (Bytes × Bytes)) :
    RefinesHdrFn (fun hs => hs ++ xs) (fun h => xs.foldl HdrBlock.addHeader h) :=
  fun h => HdrBlock.denote_foldAddHeader xs h

/-! ## The join back to the byte grain — flat rendering, byte-identical

The header stages refine at the `List (Bytes × Bytes)` grain; the serialized
output is `List UInt8`. `renderHeaders` is the grain-crossing morphism. This
section renders a flat `HdrBlock` to bytes *flat* by reusing
`Datapath.ByteRefine`'s existing byte-grain `foldAppend` calculus, and proves the
flat render is byte-identical to `Reactor.renderHeaders` on the denotation. That
is what makes a header stage's flat output byte-identical to the deployed stage's
rendered header bytes. -/

/-- **The flat header-block renderer.** Render the flat block to wire bytes by the
existing byte-grain fold: `foldAppend` over the header fragments (one flat
`Array.++` per fragment, no per-join cons-spine), reusing `ByteRefine`'s
`headerFragments`/`foldAppend`. The fragment list is computed from `denote h` (the
spec-side structure); the flatness is entirely the byte calculus's doing. -/
def flatRenderBlock (h : HdrBlock) : Array UInt8 :=
  foldAppend List.toArray #[] (headerFragments h.denote)

/-- **The flat render is byte-identical to `renderHeaders` — reused, not
re-proven.** `flatRenderBlock h` refines `Reactor.renderHeaders (denote h)`: the
FOLD combinator (`foldAppend_toArray_refines`) reads back the flatten of the
header fragments, and `renderHeaders_eq_flatten` collapses that to
`renderHeaders`. No new byte reasoning — the byte grain's existing calculus
supplies the flatness. -/
theorem flatRenderBlock_refines (h : HdrBlock) :
    Datapath.Refinement.Refines (Reactor.renderHeaders h.denote) (flatRenderBlock h) := by
  show (flatRenderBlock h).toList = Reactor.renderHeaders h.denote
  unfold flatRenderBlock
  have hfold := foldAppend_toArray_refines (headerFragments h.denote)
  rw [show (foldAppend List.toArray #[] (headerFragments h.denote)).toList
        = (headerFragments h.denote).flatten from hfold]
  rw [renderHeaders_eq_flatten]

/-- **The grain-crossing composition — a header stage rendered, byte-identical.**
Given a refined header stage `fc` (a `RefinesHdrFn`) and any flat block `h`
refining the abstract header list `a`, the flat block *rendered* after the stage
is byte-identical to `renderHeaders (fa a)` — the deployed `List` stage's rendered
header bytes. This is the functor law across the header→byte grain boundary: it
composes the header-grain stage refinement with the byte-grain `flatRenderBlock`
refinement in one step, so any header-transform stage's flat output is proven
equal to what the deployed stage + `renderHeaders` produce. -/
theorem RefinesHdrFn.compRender {fa : List (Bytes × Bytes) → List (Bytes × Bytes)}
    {fc : HdrBlock → HdrBlock} (hf : RefinesHdrFn fa fc)
    {a : List (Bytes × Bytes)} {h : HdrBlock} (r : RefinesHdr a h) :
    Datapath.Refinement.Refines (Reactor.renderHeaders (fa a)) (flatRenderBlock (fc h)) := by
  have hstage : RefinesHdr (fa a) (fc h) := hf.apply r
  have := flatRenderBlock_refines (fc h)
  rw [hstage.denote_eq] at this
  exact this

end Datapath.FlatHeaders
