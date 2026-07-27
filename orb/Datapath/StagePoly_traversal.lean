import Datapath.FlatStage_traversal
import Reactor.Deploy
import Route.Path

/-!
# Datapath.StagePoly_traversal — the deployed `traversal` GATE stage, written ONCE
polymorphically over an abstract segment sequence `[SegSeq S]`, and the load-bearing
test: does its whole refinement FOLLOW from the op laws?

This is the GATE-grain sibling of `Datapath.HdrSeqProto` (header stages, refinement
= 1-line `simp` over `push`/`filter` laws) and `Datapath.ByteSeqProto` (body/serialize
stage, refinement = a `simp` chain over `append`/`singleton`/`foldCat` laws).

Where those two grains fold/rewrite a byte or header-pair sequence, the deployed
`traversalStage` (position 0 of `deployStagesFull2`) is a **gate**: it does NOT fold
headers, it DECIDES on the request-path **segment** sequence and, on a `..`-escape,
short-circuits with the fixed `traversalBlocked404` response.

## Why a NEW seq class (the honest re-scope, not a wall)

The gate's decision is `escapesSegs segs = (segs.map decodeSeg).contains ".."` — a
`map` over a sequence of `String` **segments**, then a `contains`. That is neither
the byte grain (`ByteSeq`, `List UInt8`) nor the header-pair grain (`HdrSeq`,
`List (Bytes × Bytes)`): it is the request-path **segment** grain (`List String`),
and its ops are `map` + `contains`, which neither existing class carries. So this
file introduces `SegSeq` — the segment-grain sibling, structurally identical to
`HdrSeq`/`ByteSeq` (denotation `toSegs`, the two ops, one law per op, proven ONCE
per instance), entirely in THIS file (no core edited). The instances are the same
spec + flat pair every grain uses: `List String` (spec, `toSegs := id`, laws `rfl`)
and the already-deployed flat `SegBlock` (a contiguous `Array String`, reused from
`Datapath.FlatStage_traversal`; `map := Array.map`, `contains := Array.contains`).

## What is proven (the same shape as `securityStagePoly`)

* `escapesPoly` — the gate decision, ONE polymorphic expression over `[SegSeq S]`.
* `escapesPoly_refines` — its whole refinement FOLLOWS from the op laws: a 1-line
  `simp` over `map_denote` + `contains_denote` (⇐ the two op laws), NO per-stage
  induction, NO re-expression of the gate. `escapesPoly s = escapesSegs (toSegs s)`.
* `escapesBlock_refines` — the fast `SegBlock` instance, a DIRECT instance.
* `traversalGatePoly` / `traversalGatePoly_eq_deployed` — the gate as ONE poly
  `StageStep`, grounded in the REAL deployed `traversalStage.onRequest` branch
  (read off `Deploy.lean`, not re-specified): a `..`-escape yields
  `.respond traversalBlocked404`, else `.continue c`.
* `traversalGatePoly_response_eq_guardOne` — the reject RESPONSE is byte-identical:
  when the poly gate fires, the deployed `guardOne` output is exactly
  `serialize traversalBlocked404` (the bytes `main` writes), grounded on the real
  `guardOne_blocks`. The reject response is a fixed, target-independent term, so it
  is byte-identical at BOTH instances by construction.
-/

namespace Datapath.StagePoly_traversal

open Proto (Bytes)
open Reactor.Pipeline (Ctx StageStep Stage)
open Datapath.FlatStage.Traversal (SegBlock)

/-! ## 1. `SegSeq` — the segment-grain sibling of `HdrSeq`/`ByteSeq` -/

/-- **The segment-sequence typeclass.** The two ops the traversal gate needs
(`map` a per-segment transform, `contains` a segment), plus the denotation `toSegs`
(the abstraction relation to the deployed `List String` segment spine) and the LAWS
relating each op to its `List String` meaning. Instances prove the laws ONCE; the
gate written over `[SegSeq S]` gets its whole refinement from them. -/
class SegSeq (S : Type) where
  /-- **The denotation** — the abstract `List String` segment spine this value
  stands for. Never computed on the running datapath; it is the spec relation. -/
  toSegs : S → List String
  /-- Map a per-segment transform over the sequence (the percent-decode step). -/
  map : S → (String → String) → S
  /-- Test membership of a segment (the `..`-escape check). -/
  contains : S → String → Bool
  /-- Law: `map` denotes `List.map` on the denotation. -/
  map_denote : ∀ s f, toSegs (map s f) = (toSegs s).map f
  /-- Law: `contains` denotes `List.contains` on the denotation. -/
  contains_denote : ∀ s x, contains s x = (toSegs s).contains x

attribute [simp] SegSeq.map_denote SegSeq.contains_denote

/-- **The spec instance** — `List String`, `toSegs := id`. Every op is the `List`
op; a gate instantiated here *is* the deployed `List String` gate. Laws are `rfl`. -/
instance instSegSeqList : SegSeq (List String) where
  toSegs := id
  map := fun s f => s.map f
  contains := fun s x => s.contains x
  map_denote := fun _ _ => rfl
  contains_denote := fun _ _ => rfl

/-- **The fast instance — genuinely flat.** Reuses the deployed
`Datapath.FlatStage.Traversal.SegBlock` (the path segments in a contiguous
`Array String`). `map := Array.map`, `contains := Array.contains` (both a packed
scan, NO cons-spine copy); `toSegs := SegBlock.denote` (`Array.toList`, the
denotation only, never run on the datapath). Each law is proven once from the core
`Array` lemmas. -/
instance instSegSeqBlock : SegSeq SegBlock where
  toSegs := SegBlock.denote
  map := fun b f => ⟨b.segs.map f⟩
  contains := fun b x => b.segs.contains x
  map_denote := fun b f => by
    show (b.segs.map f).toList = b.segs.toList.map f
    rw [Array.toList_map]
  contains_denote := fun b x => by
    show b.segs.contains x = b.segs.toList.contains x
    rw [← List.contains_toArray, Array.toArray_toList]

/-! ## 2. The gate decision, written ONCE over `[SegSeq S]` -/

/-- **The traversal gate decision, written ONCE over `[SegSeq S]`.** Percent-decode
every segment (`map Route.Path.decodeSeg`) then test for a decoded `..`
(`contains ".."`) — exactly the deployed `Reactor.Deploy.escapesSegs`
(`(decodeSegs ·).contains ".."`, `decodeSegs = map decodeSeg`), computed over an
abstract `[SegSeq S]` instead of a fixed `List String` spine. -/
def escapesPoly {S : Type} [SegSeq S] (s : S) : Bool :=
  SegSeq.contains (SegSeq.map s Route.Path.decodeSeg) ".."

/-- The gate at the **spec** instance is exactly `escapesSegs` — no separate spec
expression is written; this is `escapesPoly` at `S := List String`. -/
theorem escapesPoly_list (segs : List String) :
    escapesPoly (S := List String) segs = Reactor.Deploy.escapesSegs segs := by
  simp only [escapesPoly, SegSeq.contains, SegSeq.map, instSegSeqList,
    Reactor.Deploy.escapesSegs, Route.Path.decodeSegs, id_eq]

/-- **★ THE LOAD-BEARING THEOREM — the whole-gate refinement, proven ONCE.** The
gate's decision equals the REAL `escapesSegs` run at the spec instance on the
denoted segments. Proven polymorphically in `S`; discharged by ONE `simp` over the
op laws (`map_denote`, `contains_denote`, both `@[simp]`) — NO per-stage induction,
NO re-expression of the gate. The gate costs one expression + one `simp`, exactly
like `securityStagePoly`. -/
theorem escapesPoly_refines {S : Type} [SegSeq S] (s : S) :
    escapesPoly s = Reactor.Deploy.escapesSegs (SegSeq.toSegs s) := by
  simp only [escapesPoly, SegSeq.contains_denote, SegSeq.map_denote,
    Reactor.Deploy.escapesSegs, Route.Path.decodeSegs]

/-- The refinement at the fast `SegBlock` instance — a DIRECT instance of the
once-proven polymorphic theorem, no `SegBlock`-specific reasoning. -/
theorem escapesBlock_refines (b : SegBlock) :
    escapesPoly b = Reactor.Deploy.escapesSegs b.denote :=
  escapesPoly_refines b

/-! ## 3. Grounding on the REAL request-level gate -/

/-- **The gate decision equals the deployed request-level gate.** For a segment
value denoting the request's raw segments (`rawSegsOf`), `escapesPoly` equals the
REAL `Reactor.Deploy.targetEscapes` — the gate `traversalStage` decides on.
Grounded via `targetEscapes_eq_segs` (the deployed request→segment bridge). -/
theorem escapesPoly_eq_targetEscapes {S : Type} [SegSeq S] (s : S) (req : Proto.Request)
    (hs : SegSeq.toSegs s = Reactor.Deploy.rawSegsOf req) :
    escapesPoly s = Reactor.Deploy.targetEscapes req := by
  rw [escapesPoly_refines, hs, Reactor.Deploy.targetEscapes_eq_segs]

/-! ## 4. The whole gate as a poly `StageStep`, grounded in the REAL deployed stage -/

/-- **The traversal gate stage, written ONCE over `[SegSeq S]`.** On a `..`-escape
(`escapesPoly s`) short-circuit with the fixed serializer-built
`traversalBlocked404`; otherwise pass the context inward — exactly the shape of the
deployed `Reactor.Deploy.traversalStage.onRequest`, decided by the poly gate. -/
def traversalGatePoly {S : Type} [SegSeq S] (c : Ctx) (s : S) : StageStep :=
  match escapesPoly s with
  | true  => .respond Reactor.Deploy.traversalBlocked404
  | false => .continue c

/-- **Grounded in the REAL deployed stage (non-vacuous).** For a segment value
denoting the request's raw segments, the poly gate reproduces the deployed
`traversalStage.onRequest` branch EXACTLY: `.respond traversalBlocked404` on a
`..`-escape, `.continue c` otherwise. Read off the REAL `traversalStage`
(`onRequest = match targetEscapes …`), the gate value replaced by the poly one via
`escapesPoly_eq_targetEscapes`. Not re-specified: the stage's own branch. -/
theorem traversalGatePoly_eq_deployed {S : Type} [SegSeq S] (c : Ctx) (s : S)
    (hs : SegSeq.toSegs s = Reactor.Deploy.rawSegsOf c.req) :
    traversalGatePoly c s = Reactor.Deploy.traversalStage.onRequest c := by
  show (match escapesPoly s with
        | true  => StageStep.respond Reactor.Deploy.traversalBlocked404
        | false => StageStep.continue c) = _
  rw [escapesPoly_eq_targetEscapes s c.req hs]
  rfl

/-! ## 5. The reject RESPONSE is byte-identical (the fixed 404 form) -/

/-- **The reject response is byte-identical — grounded in the DEPLOYED byte effect.**
When the poly gate fires on a request whose raw segments the value denotes, the
deployed `Reactor.Deploy.guardOne` output is exactly `serialize traversalBlocked404`
— the fixed, target-independent bytes `main` writes on an escaping request
(`guardOne_blocks`, the deployed Safety branch). The reject response is a single
constant term, so it is byte-identical at BOTH instances by construction. -/
theorem traversalGatePoly_response_eq_guardOne {S : Type} [SegSeq S]
    (input : Bytes) (c : Ctx) (s : S)
    (hs : SegSeq.toSegs s = Reactor.Deploy.rawSegsOf c.req)
    (hfire : escapesPoly s = true) :
    Reactor.Deploy.guardOne input c.req = Reactor.serialize Reactor.Deploy.traversalBlocked404 := by
  have hesc : Reactor.Deploy.targetEscapes c.req = true := by
    rw [← escapesPoly_eq_targetEscapes s c.req hs]; exact hfire
  exact Reactor.Deploy.guardOne_blocks input c.req hesc

/-! ## Non-vacuity — the poly gate genuinely computes the REAL deployed effect
at BOTH instances (evaluated by the kernel, not just proven). -/

-- The poly gate computes exactly the REAL `escapesSegs` at BOTH the spec (`List
-- String`) and the flat (`SegBlock`) instance.
#guard escapesPoly (["..", "etc", "passwd"] : List String)
        == Reactor.Deploy.escapesSegs ["..", "etc", "passwd"]
#guard escapesPoly (SegBlock.ofList ["..", "etc", "passwd"])
        == Reactor.Deploy.escapesSegs ["..", "etc", "passwd"]

-- The gate FIRES on a `..`-escape and on the once-decoded `%2e%2e` …
#guard escapesPoly (SegBlock.ofList ["..", "etc", "passwd"]) == true
#guard escapesPoly (SegBlock.ofList ["%2e%2e", "etc", "passwd"]) == true
-- … stays QUIET on a legitimate target and on the double-encoded `%252e%252e`.
#guard escapesPoly (SegBlock.ofList ["health"]) == false
#guard escapesPoly (SegBlock.ofList ["%252e%252e", "etc"]) == false

-- The poly gate genuinely depends on the input (not a constant).
#guard escapesPoly (SegBlock.ofList ["..", "x"]) != escapesPoly (SegBlock.ofList ["health"])

-- Spec instance and flat instance agree on a concrete input (the refinement, run).
#guard escapesPoly (SegBlock.ofList ["..", "etc"]) == escapesPoly (["..", "etc"] : List String)

-- The whole poly gate STEP reproduces the deployed stage effect: a `..`-escape
-- lands `.respond` with the 404-status `traversalBlocked404`, a safe path continues.
/-- `.respond` with a 404 status — the fired-gate shape, for the `#guard`s. -/
def isRespond404 : StageStep → Bool
  | .respond r  => r.status == 404
  | .continue _ => false
/-- `.continue` — the passed-gate shape, for the `#guard`s. -/
def isContinue : StageStep → Bool
  | .respond _  => false
  | .continue _ => true
#guard isRespond404 (traversalGatePoly { input := [], req := {} } (SegBlock.ofList ["..", "x"]))
#guard isContinue (traversalGatePoly { input := [], req := {} } (SegBlock.ofList ["health"]))

-- Every SegSeq op is non-vacuous at the flat SegBlock instance.
#guard (SegSeq.toSegs (SegSeq.map (SegBlock.ofList ["%2e%2e"]) Route.Path.decodeSeg))
        == ([".."] : List String)
#guard (SegSeq.contains (SegBlock.ofList ["a", "b"]) "b") == true
#guard (SegSeq.contains (SegBlock.ofList ["a", "b"]) "c") == false

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms escapesPoly_refines
#print axioms escapesBlock_refines
#print axioms escapesPoly_eq_targetEscapes
#print axioms traversalGatePoly_eq_deployed
#print axioms traversalGatePoly_response_eq_guardOne

end Datapath.StagePoly_traversal
