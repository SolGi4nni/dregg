import Datapath.Refinement
import Datapath.FlatHeaders

/-!
# Datapath.RefinesData — a GENERIC, grain-polymorphic data-refinement framework

## The problem this generalizes

`Datapath.Refinement` gives a data-refinement calculus (`FlatRep`, `Refines`,
`RefinesFn`, and the functor law `RefinesFn.comp`) — but its abstraction relation
`FlatRep.denote : C → List UInt8` is **hardwired to the byte grain** (the abstract
type is fixed to `List UInt8`). The response header block lives at a *different*
grain — its abstract type is `List (Proto.Bytes × Proto.Bytes)` — so
`Datapath.FlatHeaders` had to **clone the entire calculus** (`RefinesHdr`,
`RefinesHdrFn`, `RefinesHdrFn.apply`, `RefinesHdrFn.comp`, `RefinesHdrFn.id`) with
byte-for-byte identical proofs, plus a *bespoke grain-crossing* composition
`RefinesHdrFn.compRender`. That duplication is the tax: **each new abstract grain
(cookies, trailers, chunk framing, query params, …) currently costs another
sibling calculus.**

## The generalization

This module makes the abstract type a **parameter too**: a class `Denote A D`
(the abstraction relation `denote : D → A`, polymorphic in *both* the abstract
spec type `A` and the dense concrete type `D`), and the whole calculus stated
**once** over it:

* `Refines a d` — the dense `d` refines the abstract `a` (`denote d = a`);
* `RefinesFn fa fd` — the naturality square, with **independent input and output
  grains** `(A₁,D₁) → (A₂,D₂)`. A same-grain refinement is the special case
  `A₁ = A₂`; a **grain-crossing** one (header → bytes, i.e. rendering) is the
  general case — so `compRender` is no longer bespoke;
* `RefinesFn.comp` — the functor law, proven **once, polymorphically**. It composes
  byte↔byte, header↔header, AND header↔byte in a single lemma. Every manual
  `.comp` (`Refinement.RefinesFn.comp`, `FlatHeaders.RefinesHdrFn.comp`) and the
  bespoke `RefinesHdrFn.compRender` are instances of THIS one.

## Subsumption (proven, not asserted — see `Datapath.RefinesDataDemo`)

* One bridge instance `[FlatRep C] → Denote (List UInt8) C` lifts **every** existing
  byte-grain `FlatRep` (`Array UInt8`, `ByteArray`, `SpanBytes`, `OutBuf`) into this
  framework for free — the byte grain is subsumed, `RefinesFn` here is
  *definitionally* `Refinement.RefinesFn` (`Iff.rfl`).
* One instance line `Denote (List (Bytes × Bytes)) HdrBlock` gives the header grain;
  `RefinesFn` here is *definitionally* `FlatHeaders.RefinesHdrFn` (`Iff.rfl`) — the
  ~40-LOC sibling calculus collapses to that single line.

The point: a NEW grain is **one instance**, not a new sibling calculus copy; and
composition across grains is **one functor law**, not a bespoke crossing lemma.
-/

namespace Datapath.RefinesData

open Proto (Bytes)

universe u₁ v₁ u₂ v₂ u₃ v₃

/-- **The abstraction relation, fully polymorphic.** A dense concrete type `D`
carries a `denote` reading back the abstract spec value of type `A` it stands for.
Unlike `Datapath.Refinement.FlatRep` (whose `denote` is fixed to `List UInt8`),
BOTH the abstract type `A` and the dense type `D` are parameters — so one class
covers the byte grain (`A := List UInt8`), the header grain
(`A := List (Bytes × Bytes)`), and any future grain, with no sibling calculus. -/
class Denote (A : outParam (Type u₁)) (D : Type v₁) where
  /-- The abstract spec value the dense value denotes. -/
  denote : D → A

/-- **The refinement relation.** The dense `d` refines the abstract `a` exactly
when it denotes back to `a`. In the running datapath `denote` lowers to zero work
(the value is already dense). Generalizes both `Refinement.Refines` (byte grain)
and `FlatHeaders.RefinesHdr` (header grain). -/
def Refines {A : Type u₁} {D : Type v₁} [Denote A D] (a : A) (d : D) : Prop :=
  Denote.denote d = a

theorem Refines.denote_eq {A : Type u₁} {D : Type v₁} [Denote A D] {a : A} {d : D}
    (h : Refines a d) : Denote.denote d = a := h

/-- Every dense value refines its own denotation — the reflexive leaf. -/
@[simp] theorem Refines.refl {A : Type u₁} {D : Type v₁} [Denote A D] (d : D) :
    Refines (Denote.denote d) d := rfl

/-- **A refined combinator — with independent input and output grains.** The
naturality square between denotations: running the dense op `fd` then denoting (at
the OUTPUT grain `(A₂, D₂)`) equals denoting (at the INPUT grain `(A₁, D₁)`) then
running the abstract op `fa`. Same-grain (`A₁ = A₂`) reproduces
`Refinement.RefinesFn` / `FlatHeaders.RefinesHdrFn`; a grain-CROSSING instance
(e.g. `A₁ = List (Bytes×Bytes)`, `A₂ = List UInt8`) is the *renderer* — so a
renderer is an ordinary refined combinator here, not a special case. -/
def RefinesFn {A₁ : Type u₁} {D₁ : Type v₁} {A₂ : Type u₂} {D₂ : Type v₂}
    [Denote A₁ D₁] [Denote A₂ D₂] (fa : A₁ → A₂) (fd : D₁ → D₂) : Prop :=
  ∀ d : D₁, Denote.denote (fd d) = fa (Denote.denote d)

/-- **Point transfer.** A refined combinator carries a refinement of its input to a
refinement of its output — turning a fact about *representations* into a fact about
a *running computation*, across any grain change. -/
theorem RefinesFn.apply {A₁ : Type u₁} {D₁ : Type v₁} {A₂ : Type u₂} {D₂ : Type v₂}
    [Denote A₁ D₁] [Denote A₂ D₂] {fa : A₁ → A₂} {fd : D₁ → D₂}
    (hf : RefinesFn fa fd) {a : A₁} {d : D₁} (h : Refines a d) :
    Refines (fa a) (fd d) := by
  unfold Refines at h ⊢
  rw [hf d, h]

/-- **Compositionality — the functor law, proven ONCE for all grains.** The
composite of two refined combinators refines the composite of the abstract ops.
The middle grain `(A₂, D₂)` is arbitrary, so this single lemma composes
byte↔byte, header↔header, AND header↔byte (renderer) chains. Every manual `.comp`
and the bespoke `RefinesHdrFn.compRender` are instances of this. -/
theorem RefinesFn.comp
    {A₁ : Type u₁} {D₁ : Type v₁} {A₂ : Type u₂} {D₂ : Type v₂} {A₃ : Type u₃} {D₃ : Type v₃}
    [Denote A₁ D₁] [Denote A₂ D₂] [Denote A₃ D₃]
    {fa : A₁ → A₂} {fd : D₁ → D₂} {ga : A₂ → A₃} {gd : D₂ → D₃}
    (hf : RefinesFn fa fd) (hg : RefinesFn ga gd) :
    RefinesFn (ga ∘ fa) (gd ∘ fd) := by
  intro d
  simp only [Function.comp]
  rw [hg (fd d), hf d]

/-- The identity is a refined combinator (the unit of the functor law). -/
theorem RefinesFn.id {A : Type u₁} {D : Type v₁} [Denote A D] :
    RefinesFn (id) (id : D → D) := fun _ => rfl

/-- A constant dense value refining a fixed abstract value is a refined combinator
into it — the leaf of a derivation (an already-dense literal). -/
theorem RefinesFn.const {A₁ : Type u₁} {D₁ : Type v₁} {A₂ : Type u₂} {D₂ : Type v₂}
    [Denote A₁ D₁] [Denote A₂ D₂] {b : A₂} {db : D₂} (h : Refines b db) :
    RefinesFn (fun _ => b) (fun _ : D₁ => db) := fun _ => h

/-- **A refined BINARY combinator** — the naturality square for a two-argument op
(the shape `append` has), with all three grains independent. -/
def RefinesFn2
    {A₁ : Type u₁} {D₁ : Type v₁} {A₂ : Type u₂} {D₂ : Type v₂} {A₃ : Type u₃} {D₃ : Type v₃}
    [Denote A₁ D₁] [Denote A₂ D₂] [Denote A₃ D₃]
    (fa : A₁ → A₂ → A₃) (fd : D₁ → D₂ → D₃) : Prop :=
  ∀ (x : D₁) (y : D₂), Denote.denote (fd x y) = fa (Denote.denote x) (Denote.denote y)

/-- Point transfer for a binary combinator: refined inputs give a refined output. -/
theorem RefinesFn2.apply
    {A₁ : Type u₁} {D₁ : Type v₁} {A₂ : Type u₂} {D₂ : Type v₂} {A₃ : Type u₃} {D₃ : Type v₃}
    [Denote A₁ D₁] [Denote A₂ D₂] [Denote A₃ D₃]
    {fa : A₁ → A₂ → A₃} {fd : D₁ → D₂ → D₃} (hf : RefinesFn2 fa fd)
    {ax : A₁} {ay : A₂} {x : D₁} {y : D₂} (hx : Refines ax x) (hy : Refines ay y) :
    Refines (fa ax ay) (fd x y) := by
  unfold Refines at hx hy ⊢
  rw [hf x y, hx, hy]

/-- **Right-operand specialization — the shared-tail trick, generic.** Fixing an
already-refined right operand turns a binary refined combinator into a unary one on
the left operand (the `SerializeFast` shared-right-operand pattern, at any grain). -/
theorem RefinesFn2.right
    {A₁ : Type u₁} {D₁ : Type v₁} {A₂ : Type u₂} {D₂ : Type v₂} {A₃ : Type u₃} {D₃ : Type v₃}
    [Denote A₁ D₁] [Denote A₂ D₂] [Denote A₃ D₃]
    {fa : A₁ → A₂ → A₃} {fd : D₁ → D₂ → D₃} (hf : RefinesFn2 fa fd)
    {ay : A₂} {y : D₂} (hy : Refines ay y) :
    RefinesFn (fun x => fa x ay) (fun x : D₁ => fd x y) := by
  intro x
  rw [hf x y, hy.denote_eq]

/-! ## The bridge instances — the existing grains become instances of THIS framework

Two instances subsume the two manual calculi. No sibling calculus, no re-proof. -/

/-- **The byte grain, subsumed wholesale.** EVERY existing byte-grain
`Datapath.Refinement.FlatRep` (`Array UInt8`, `ByteArray`, `SpanBytes`, `OutBuf`)
becomes a `Denote (List UInt8) ·` instance for free — its `denote` is the FlatRep
one. So the entire `Datapath.Refinement` / `Datapath.ByteRefine` byte calculus is
already an instance of this framework (`RefinesDataDemo` proves `RefinesFn` here is
*definitionally* `Refinement.RefinesFn`). -/
instance instDenoteOfFlatRep {C : Type u₁} [Datapath.Refinement.FlatRep C] :
    Denote (List UInt8) C where
  denote := Datapath.Refinement.FlatRep.denote

/-- **The header grain — ONE line replaces the ~40-LOC sibling calculus.** The flat
`HdrBlock` denotes to its `List (Bytes × Bytes)` header list. With this single
instance, `Refines` / `RefinesFn` / `RefinesFn.comp` here reproduce
`FlatHeaders.RefinesHdr` / `RefinesHdrFn` / `RefinesHdrFn.comp` *definitionally* —
that whole clone is unnecessary under this framework. -/
instance instDenoteHdrBlock : Denote (List (Bytes × Bytes)) Datapath.FlatHeaders.HdrBlock where
  denote := Datapath.FlatHeaders.HdrBlock.denote

end Datapath.RefinesData
