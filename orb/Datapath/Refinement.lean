/-!
# Datapath.Refinement — a polymorphic data-refinement calculus (`List UInt8` → flat)

The deployed serve is typed on the abstract spec `Proto.Bytes = List UInt8`: a
per-byte cons-list. The datapath cost is dominated by that representation. The
elegant fix is **not** to retype `Bytes` (that would re-prove the 50 correctness
lanes + the serve cores); it is to keep `List UInt8` as the *abstract spec* and
**derive** a flat concrete representation by a *proven, compositional* data
refinement — so a flat serve is obtained *by construction* from the List spec,
with the spec and every lane untouched.

This module is the GENERAL, POLYMORPHIC core of that refinement: the relation and
the combinator calculus, stated once, for **any** flat representation `C`.

## The pattern (data refinement, general)

* an **abstract** type `List UInt8` (the spec);
* a **concrete** flat type `C` (e.g. `Array UInt8` / `ByteArray`, in
  `Datapath.ByteRefine`; `SpanBytes` for the borrowed-window request half);
* an **abstraction relation** `denote : C → List UInt8` (the `FlatRep` class) — the
  `List UInt8` a concrete value *stands for*, exactly `SpanBytes.denote` /
  `ByteArray.toList` generalized.

`Refines a c := denote c = a` says the concrete `c` refines the abstract bytes
`a`. A **refined combinator** (`RefinesFn fa fc`) is the naturality square
`denote (fc c) = fa (denote c)` — a single per-combinator obligation. The two
theorems that make the calculus *compositional* are:

* `RefinesFn.apply` — a refined combinator carries a refined input to a refined
  output (a proof about *representations* becomes a proof about a *running op*);
* `RefinesFn.comp` — the **functor law**: the composite of two refined combinators
  refines the composite of the abstract ops. Hence a whole PIPELINE of refined
  combinators refines the composed `List` pipeline, *by construction*.

`Datapath.ByteRefine` instantiates `C := Array UInt8` (bridged to the wire type
`ByteArray`), proves the combinator lemmas ONCE (`refine_empty`,
`refine_append`, `refine_map`, `refine_singleton`, `refine_ofList`, and the FOLD
combinator `foldAppend`), and DERIVES a flat response serializer *for free* from
them + compositionality — the framework does the work, no bespoke bridge.
-/

namespace Datapath.Refinement

universe u v w

/-- **The abstraction relation, as a class.** A flat concrete representation `C`
carries a `denote` reading back the abstract `List UInt8` it stands for. This is
the ONE relation the whole calculus is built on; every concrete representation
(`Array UInt8`, `ByteArray`, the borrowed `SpanBytes` window, an `OutBuf`) is a
`FlatRep` instance and the combinator calculus applies uniformly. -/
class FlatRep (C : Type u) where
  /-- The abstract byte list the concrete value denotes. -/
  denote : C → List UInt8

/-- **The refinement relation.** The concrete `c` refines the abstract byte list
`a` exactly when it denotes back to `a`. The flat concrete value carries the
abstract `List UInt8` without materializing it (in the running datapath `denote`
lowers to zero work: the bytes are already flat). -/
def Refines {C : Type u} [FlatRep C] (a : List UInt8) (c : C) : Prop :=
  FlatRep.denote c = a

theorem Refines.denote_eq {C : Type u} [FlatRep C] {a : List UInt8} {c : C}
    (h : Refines a c) : FlatRep.denote c = a := h

/-- Every concrete value refines its own denotation — the reflexive instance
(`refine_ofByteArray` / `Refines.rfl_full` generalized). -/
@[simp] theorem Refines.refl {C : Type u} [FlatRep C] (c : C) :
    Refines (FlatRep.denote c) c := rfl

/-- **A refined combinator** — the naturality square between denotations: running
the concrete op `fc` and denoting equals denoting and running the abstract op
`fa`. This is the SINGLE proof obligation per byte combinator; compositionality
(`comp`) then lifts it to whole pipelines with no further per-combinator work. -/
def RefinesFn {A : Type u} {B : Type v} [FlatRep A] [FlatRep B]
    (fa : List UInt8 → List UInt8) (fc : A → B) : Prop :=
  ∀ c : A, FlatRep.denote (fc c) = fa (FlatRep.denote c)

/-- **Point transfer.** A refined combinator carries a refinement of its input to
a refinement of its output. This is how the calculus turns a fact about
*representations* (`Refines a c`) into a fact about a *running computation*
(`Refines (fa a) (fc c)`). -/
theorem RefinesFn.apply {A : Type u} {B : Type v} [FlatRep A] [FlatRep B]
    {fa : List UInt8 → List UInt8} {fc : A → B} (hf : RefinesFn fa fc)
    {a : List UInt8} {c : A} (h : Refines a c) : Refines (fa a) (fc c) := by
  unfold Refines at h ⊢
  rw [hf c, h]

/-- **Compositionality — the functor law.** The composite of two refined
combinators refines the composite of the abstract ops. Consequence: a whole
PIPELINE `gc ∘ fc` of refined combinators refines the composed `List` pipeline
`ga ∘ fa` — the flat pipeline refines the spec pipeline **by construction**, from
the per-combinator lemmas alone. -/
theorem RefinesFn.comp {A : Type u} {B : Type v} {D : Type w}
    [FlatRep A] [FlatRep B] [FlatRep D]
    {fa ga : List UInt8 → List UInt8} {fc : A → B} {gc : B → D}
    (hf : RefinesFn fa fc) (hg : RefinesFn ga gc) :
    RefinesFn (ga ∘ fa) (gc ∘ fc) := by
  intro c
  simp only [Function.comp]
  rw [hg (fc c), hf c]

/-- The identity is a refined combinator (the unit of the functor law). -/
theorem RefinesFn.id {A : Type u} [FlatRep A] : RefinesFn (id) (id : A → A) :=
  fun _ => rfl

/-- A constant concrete value that refines a fixed abstract list is a refined
combinator into it — the leaf of a derivation (an already-flat literal). -/
theorem RefinesFn.const {A : Type u} {B : Type v} [FlatRep A] [FlatRep B]
    {b : List UInt8} {cb : B} (h : Refines b cb) :
    RefinesFn (fun _ => b) (fun _ : A => cb) :=
  fun _ => h

/-- **A refined BINARY combinator** — the naturality square for a two-argument op
(the shape `append` has). Needed because `List.++` is binary; `refine_append` in
`ByteRefine` is exactly a `RefinesFn2`. -/
def RefinesFn2 {A : Type u} {B : Type v} {D : Type w}
    [FlatRep A] [FlatRep B] [FlatRep D]
    (fa : List UInt8 → List UInt8 → List UInt8) (fc : A → B → D) : Prop :=
  ∀ (x : A) (y : B), FlatRep.denote (fc x y) = fa (FlatRep.denote x) (FlatRep.denote y)

/-- Point transfer for a binary combinator: refined inputs give a refined output. -/
theorem RefinesFn2.apply {A : Type u} {B : Type v} {D : Type w}
    [FlatRep A] [FlatRep B] [FlatRep D]
    {fa : List UInt8 → List UInt8 → List UInt8} {fc : A → B → D}
    (hf : RefinesFn2 fa fc)
    {ax ay : List UInt8} {x : A} {y : B} (hx : Refines ax x) (hy : Refines ay y) :
    Refines (fa ax ay) (fc x y) := by
  unfold Refines at hx hy ⊢
  rw [hf x y, hx, hy]

/-- **Right-operand specialization of a binary combinator — the shared-tail
trick.** Fixing an already-refined right operand `y` turns a binary refined
combinator into a UNARY refined combinator on the left operand. This is the
`SerializeFast` shared-right-operand pattern generalized: the flat *head* is built
by the calculus while the fixed *tail* (the response body) rides along as the
shared right operand of one append — appended once, never re-copied per join. -/
theorem RefinesFn2.right {A : Type u} {B : Type v} {D : Type w}
    [FlatRep A] [FlatRep B] [FlatRep D]
    {fa : List UInt8 → List UInt8 → List UInt8} {fc : A → B → D}
    (hf : RefinesFn2 fa fc) {ay : List UInt8} {y : B} (hy : Refines ay y) :
    RefinesFn (fun h => fa h ay) (fun x : A => fc x y) := by
  intro x
  rw [hf x y, hy.denote_eq]

end Datapath.Refinement
