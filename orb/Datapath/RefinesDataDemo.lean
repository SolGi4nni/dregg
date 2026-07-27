import Datapath.RefinesData
import Datapath.FlatStage

/-!
# Datapath.RefinesDataDemo — the de-risk: re-derive a REAL densification via the
generic `Datapath.RefinesData` framework, and measure it against the manual per-grain
calculus.

This file proves the framework carries its weight, on the SAME `securityheaders`
stage `Datapath.FlatStage` did by hand (via the cloned `FlatHeaders` header calculus
and the bespoke `RefinesHdrFn.compRender`). Here EVERYTHING goes through the ONE
generic calculus in `Datapath.RefinesData`:

1. **Subsumption is definitional (`Iff.rfl`).** The generic `RefinesFn` at the byte
   grain IS `Refinement.RefinesFn`; at the header grain IS `FlatHeaders.RefinesHdrFn`
   — no new content, the manual calculi are special cases.
2. **The stage refinement, generic.** `flatSecurityStage` is a generic `RefinesFn`
   discharged from the reused fold fact `HdrBlock.denote_foldAddHeader` — the SAME
   one-liner as the manual `flatSecurityStage_refines`, but on the generic combinator.
3. **The renderer is an ordinary refined combinator** (a grain-CROSSING
   `RefinesFn`, header → bytes), from the reused `flatRenderBlock_refines`.
4. **The byte-identity via the ONE generic functor law.** `stage ⋙ render` composes
   by the polymorphic `RefinesFn.comp` — reproducing `RefinesHdrFn.compRender`
   with NO bespoke grain-crossing lemma — and `.apply` gives the byte-identity
   `flatSecurityStage_render_byte_identical` proved. Non-vacuous, axioms clean.

## What is REUSED vs what the framework SUPPLIES

Reused, legitimately (grain-specific *content*, not calculus): the fold fact
`HdrBlock.denote_foldAddHeader` and the renderer fact `flatRenderBlock_refines`
(both live in the un-modifiable cores; they are the actual `Array.push`/fold
computations). SUPPLIED by the framework, replacing the manual per-grain calculus:
the relation, `RefinesFn`, `.apply`, the functor law `.comp` (same-grain AND
grain-crossing), `.id`, `RefinesFn2` — proven once in `RefinesData`, instantiated
here by two one-line `Denote` instances.
-/

namespace Datapath.RefinesDataDemo

open Proto (Bytes)
open Datapath.RefinesData (Denote Refines RefinesFn)
open Datapath.FlatHeaders (HdrBlock flatRenderBlock RefinesHdr RefinesHdrFn)
open Datapath.FlatStage (flatSecurityStage)
open Reactor.Stage.SecurityHeaders (wireHeaders policy)

/-! ## 1. Subsumption — the two manual calculi are DEFINITIONAL special cases -/

/-- **The byte grain is subsumed definitionally.** The generic `RefinesFn` on any
two byte-grain `FlatRep`s is *literally* `Datapath.Refinement.RefinesFn` — the byte
calculus of `Datapath.Refinement` / `Datapath.ByteRefine` is this framework, no
re-proof. -/
theorem refinesFn_byte_is_manual {A B : Type} [Datapath.Refinement.FlatRep A]
    [Datapath.Refinement.FlatRep B]
    (fa : List UInt8 → List UInt8) (fc : A → B) :
    RefinesFn fa fc ↔ Datapath.Refinement.RefinesFn fa fc := Iff.rfl

/-- **The header grain is subsumed definitionally.** The generic `RefinesFn` on the
flat `HdrBlock` is *literally* `Datapath.FlatHeaders.RefinesHdrFn` — the entire
~40-LOC sibling header calculus (`RefinesHdr`, `RefinesHdrFn`, `.apply`, `.comp`,
`.id`) is unnecessary under this framework; one `Denote` instance suffices. -/
theorem refinesFn_hdr_is_manual
    (fa : List (Bytes × Bytes) → List (Bytes × Bytes)) (fc : HdrBlock → HdrBlock) :
    RefinesFn fa fc ↔ RefinesHdrFn fa fc := Iff.rfl

/-! ## 2. The header FOLD combinator, as a GENERIC `RefinesFn`

The one grain-specific fact — that folding a fixed header set onto the flat block
via `Array.push` denotes to the `List` append — is `HdrBlock.denote_foldAddHeader`
in the un-modifiable core. The framework turns it into a generic refined combinator
with no header-specific calculus. -/

/-- **The header fold as a generic refined combinator.** Folding a fixed header set
`xs` onto the flat block refines the `List` append `· ++ xs`, stated on the GENERIC
`RefinesData.RefinesFn`. Discharged directly from the reused core fold fact — the
generic framework, not the header sibling calculus, provides the combinator. -/
theorem refinesData_foldAddHeader (xs : List (Bytes × Bytes)) :
    RefinesFn (fun hs => hs ++ xs) (fun h => xs.foldl HdrBlock.addHeader h) :=
  fun h => HdrBlock.denote_foldAddHeader xs h

/-- **The `securityheaders` stage refines, via the generic framework.** Exactly the
statement of the manual `Datapath.FlatStage.flatSecurityStage_refines`, but on the
generic `RefinesFn` — a direct instance of the generic fold combinator. Non-vacuous:
`flatSecurityStage` genuinely `Array.push`-folds. -/
theorem flatSecurityStage_refines_generic :
    RefinesFn (fun hs => hs ++ wireHeaders policy) flatSecurityStage :=
  refinesData_foldAddHeader (wireHeaders policy)

/-! ## 3. The renderer as a grain-CROSSING refined combinator (header → bytes)

`flatRenderBlock : HdrBlock → Array UInt8` renders the flat header block to wire
bytes. Its refinement `flatRenderBlock_refines` (reused core fact) says exactly:
`flatRenderBlock` is a `RefinesFn` from the header grain to the byte grain, for the
abstract op `Reactor.renderHeaders`. In the manual world this grain change needed
the bespoke `RefinesHdrFn.compRender`; here it is an ordinary `RefinesFn`. -/

/-- **The flat renderer is a refined combinator across the grain boundary.** A
`RefinesFn` with input grain `(List (Bytes×Bytes), HdrBlock)` and output grain
`(List UInt8, Array UInt8)` — the renderer as a first-class arrow of the SAME
generic calculus, from the reused `flatRenderBlock_refines`. -/
theorem refinesData_flatRenderBlock :
    RefinesFn Reactor.renderHeaders flatRenderBlock :=
  fun h => Datapath.FlatHeaders.flatRenderBlock_refines h

/-! ## 4. The byte-identity via the ONE polymorphic functor law -/

/-- **Stage then render, composed by the generic functor law — no `compRender`.**
`flatSecurityStage` (header→header) composed with `flatRenderBlock` (header→bytes)
by the single polymorphic `RefinesFn.comp`. This is the exact job the bespoke
`Datapath.FlatHeaders.RefinesHdrFn.compRender` did, obtained here for free as an
instance of the generic functor law across a grain boundary. -/
theorem securityStage_render_comp :
    RefinesFn
      (Reactor.renderHeaders ∘ (fun hs => hs ++ wireHeaders policy))
      (flatRenderBlock ∘ flatSecurityStage) :=
  flatSecurityStage_refines_generic.comp refinesData_flatRenderBlock

/-- **THE BYTE-IDENTITY, re-derived via the framework.** For any flat block `h`
refining the abstract header list `a`, the flat security stage's output rendered
through the flat renderer is byte-identical to `Reactor.renderHeaders (a ++
wireHeaders policy)` — the deployed stage's rendered header bytes. This is the SAME
theorem as `Datapath.FlatStage.flatSecurityStage_render_byte_identical`, proved by
`generic .comp` then `generic .apply`, with the header sibling calculus and
`compRender` entirely bypassed. -/
theorem securityStage_render_byte_identical
    {a : List (Bytes × Bytes)} {h : HdrBlock} (r : RefinesHdr a h) :
    Datapath.Refinement.Refines
      (Reactor.renderHeaders (a ++ wireHeaders policy))
      (flatRenderBlock (flatSecurityStage h)) :=
  securityStage_render_comp.apply r

/-- Specialized to the deployed stage over a base header list — matching the manual
`flatSecurityStage_render_matches_deployed`, byte-for-byte the same statement. -/
theorem securityStage_render_matches_deployed (hs : List (Bytes × Bytes)) :
    Datapath.Refinement.Refines
      (Reactor.renderHeaders (hs ++ wireHeaders policy))
      (flatRenderBlock (flatSecurityStage (HdrBlock.ofList hs))) :=
  securityStage_render_byte_identical (h := HdrBlock.ofList hs)
    (by show (HdrBlock.ofList hs).denote = hs; simp [HdrBlock.denote_ofList])

/-! ## 5. Non-vacuity — the framework-derived op genuinely computes the SAME bytes -/

-- The framework-derived rendered header bytes equal `renderHeaders` of the deployed
-- header block — evaluated by the kernel, not just proven.
#guard (flatRenderBlock (flatSecurityStage (HdrBlock.ofList [("X-Test".toUTF8.toList, "1".toUTF8.toList)]))).toList
        == Reactor.renderHeaders ([("X-Test".toUTF8.toList, "1".toUTF8.toList)] ++ wireHeaders policy)

-- Genuine dependence on the input: different base headers give different rendered
-- bytes (the derived op is not a constant).
#guard (flatRenderBlock (flatSecurityStage (HdrBlock.ofList [("A".toUTF8.toList, "1".toUTF8.toList)]))).toList
        != (flatRenderBlock (flatSecurityStage (HdrBlock.ofList [("B".toUTF8.toList, "22".toUTF8.toList)]))).toList

/-! ## Axiom audit — the framework core + the re-derived refinement -/

-- Framework core
#print axioms Datapath.RefinesData.RefinesFn.comp
#print axioms Datapath.RefinesData.RefinesFn.apply
-- The re-derived prototype (fully qualified)
#print axioms Datapath.RefinesDataDemo.flatSecurityStage_refines_generic
#print axioms Datapath.RefinesDataDemo.securityStage_render_comp
#print axioms Datapath.RefinesDataDemo.securityStage_render_byte_identical
#print axioms Datapath.RefinesDataDemo.securityStage_render_matches_deployed
-- Subsumption
#print axioms Datapath.RefinesDataDemo.refinesFn_hdr_is_manual
#print axioms Datapath.RefinesDataDemo.refinesFn_byte_is_manual

end Datapath.RefinesDataDemo
