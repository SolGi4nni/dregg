import Datapath.Refinement
import Datapath.Refine
import Reactor.Serialize

/-!
# Datapath.ByteRefine — the flat (`Array UInt8` / `ByteArray`) instance of the
polymorphic refinement calculus, and a serve fragment DERIVED flat from it

`Datapath.Refinement` gives the general calculus (the `FlatRep` abstraction
relation, `RefinesFn`, and the functor law `RefinesFn.comp`). This module makes it
concrete on the flat wire representation and USES it to derive a flat serializer
*mechanically*, with the `List`-typed spec (`Reactor.serialize`) and every lane
untouched.

## The flat representation and the combinator lemmas (proven ONCE)

The genuinely-flat, lemma-friendly carrier is `Array UInt8` (the `SerializeFast`
accumulator type); the wire type `ByteArray` is `{ data : Array UInt8 }`, reached
by the refinement-preserving bridge `ByteArray.mk`. On `Array UInt8` we prove,
each ONCE:

* `refine_empty`      — `#[]` refines `[]`;
* `refine_ofList`     — `l.toArray` refines `l` (the abstraction relation for a
                        materialized literal — the leaf of every derivation);
* `refine_singleton`  — `#[b]` refines `[b]`;
* `refine_append`     — array `++` refines `List.++` (a `RefinesFn2`), and its
                        shared-right-operand specialization `refine_append_shared`
                        (the body-stays-shared trick, `RefinesFn2.right`);
* `refine_map`        — `Array.map f` refines `List.map f`;
* `refine_fold`       — the FOLD combinator: a flat accumulator fold
                        (`foldAppend`) refines `List` concatenation
                        (`flatMap`/`flatten`) — the `parseHeadersAcc` /
                        `renderHeadersAcc` pattern generalized.

## The derived flat serializer (the framework does the work)

`flatSerialize : Response → ByteArray` is built from these combinators — a fold
over the head fragments (`refine_fold`) with the body as the shared right operand
(`refine_append_shared`) — and `flatSerialize_refines` proves it refines
`Reactor.serialize` **for free**, by chaining the combinator lemmas +
compositionality. The one serialize-specific fact is the framing decomposition
`serializeWire = (head fragments).flatten ++ body` (the spec side); the flatness
is entirely the calculus's doing. This is MECHANICAL: the same recipe (express the
`List`-`++`/`fold` structure of any serve stage in the combinators, discharge by
the lemmas) refines the whole serve.
-/

namespace Datapath.Refinement

open Proto (Bytes)

/-! ## The flat representation: `Array UInt8`, denoting to its byte list -/

/-- The flat concrete representation used by the derivation: a packed
`Array UInt8`, denoting to its underlying byte list (`Array.toList`). All the
combinator lemmas below are stated on this instance. -/
instance : FlatRep (Array UInt8) where
  denote a := a.toList

@[simp] theorem denote_array (a : Array UInt8) : FlatRep.denote a = a.toList := rfl

/-! ## The combinator lemmas — proven ONCE

Each byte combinator gets exactly one refinement lemma here; every derived flat
program reuses them through `RefinesFn.apply` / `RefinesFn2.apply` / `comp`. -/

/-- **`refine_empty`.** The empty flat array refines the empty byte list. -/
theorem refine_empty : Refines [] (#[] : Array UInt8) := rfl

/-- **`refine_ofList`.** Materializing a byte list into a flat array refines it —
the abstraction relation for a literal fragment (the leaf of a derivation; in the
running datapath the bytes are already flat and this is identity). -/
@[simp] theorem refine_ofList (l : List UInt8) : Refines l l.toArray := by
  show l.toArray.toList = l
  rw [List.toList_toArray]

/-- **`refine_singleton`.** A one-byte flat array refines the singleton list. -/
theorem refine_singleton (b : UInt8) : Refines [b] (#[b] : Array UInt8) := rfl

/-- **`refine_append`.** Flat-array append refines `List.++` — the naturality
square, as a binary refined combinator (`RefinesFn2`). This is the ++ combinator
of the calculus; every `List.++` in a spec maps to an array `++` here. -/
theorem refine_append :
    RefinesFn2 (· ++ ·) (fun x y : Array UInt8 => x ++ y) := by
  intro x y
  show (x ++ y).toList = x.toList ++ y.toList
  rw [Array.toList_append]

/-- **`refine_append_shared` — the shared-right-operand trick.** Appending a
FIXED already-refined tail `y` (e.g. the response body) is a UNARY refined
combinator on the head: the head is built flat by the calculus and the tail rides
as the shared right operand of one append, never re-copied per join. Directly the
`SerializeFast` body-optimality, obtained from `refine_append` by `RefinesFn2.right`. -/
theorem refine_append_shared {ay : List UInt8} {y : Array UInt8} (hy : Refines ay y) :
    RefinesFn (fun h => h ++ ay) (fun x : Array UInt8 => x ++ y) :=
  refine_append.right hy

/-- **`refine_map`.** `Array.map f` refines `List.map f` — the map combinator. -/
theorem refine_map (f : UInt8 → UInt8) :
    RefinesFn (List.map f) (fun a : Array UInt8 => a.map f) := by
  intro a
  show (a.map f).toList = a.toList.map f
  rw [Array.toList_map]

/-! ## The FOLD combinator — a flat accumulator fold refines `List` concatenation

`foldAppend f acc xs` folds one flat append per element into the uniquely-owned
accumulator (`acc ++ f x`, amortized-`O(1)` push, no per-join cons-spine) — the
`parseHeadersAcc` / `renderHeadersAcc` / `serializeHeadAcc` pattern, generalized
and stated once. `refine_fold` proves it reads back exactly the accumulator's
denotation followed by the `List.flatMap` of the per-element denotations, so with
an empty accumulator it refines `List.flatten` of the mapped fragments. -/

/-- Fold one flat append per element into the accumulator: the flat concat-map. -/
def foldAppend {α : Type u} (f : α → Array UInt8) (acc : Array UInt8) :
    List α → Array UInt8
  | [] => acc
  | x :: xs => foldAppend f (acc ++ f x) xs

/-- **`refine_fold` (accumulator form).** The flat accumulator fold reads back the
accumulator's bytes followed by the `List.flatMap` of the per-element flat
fragments — a flat fold refines `List` concatenation, once and for all. -/
theorem refine_fold {α : Type u} (f : α → Array UInt8) (xs : List α) :
    ∀ acc : Array UInt8,
      (foldAppend f acc xs).toList = acc.toList ++ xs.flatMap (fun x => (f x).toList) := by
  induction xs with
  | nil => intro acc; simp [foldAppend]
  | cons x xs ih =>
    intro acc
    show (foldAppend f (acc ++ f x) xs).toList = _
    rw [ih (acc ++ f x)]
    simp [Array.toList_append, List.append_assoc]

/-- **`refine_fold` (refinement form).** From an empty accumulator, the flat fold
refines the `List.flatMap` of the per-element denotations — the FOLD combinator as
a `Refines` fact ready to feed `RefinesFn.apply`/`comp`. -/
theorem foldAppend_refines {α : Type u} (f : α → Array UInt8) (xs : List α) :
    Refines (xs.flatMap (fun x => (f x).toList)) (foldAppend f #[] xs) := by
  show (foldAppend f #[] xs).toList = _
  rw [refine_fold f xs #[]]
  simp

/-- Specialized to fragment materialization (`f := List.toArray`): folding a list
of byte-fragments into a flat array refines their `flatten`. This is the exact
shape a serializer's head has (a fixed list of byte fragments). -/
theorem foldAppend_toArray_refines (frags : List (List UInt8)) :
    Refines frags.flatten (foldAppend List.toArray #[] frags) := by
  have h := foldAppend_refines (α := List UInt8) List.toArray frags
  simpa [List.toList_toArray, List.flatMap_id] using h

/-! ## The `ByteArray` wire bridge — `ByteArray.mk` preserves refinement

`Array UInt8` is where the clean lemmas live; the deployed wire type is
`ByteArray = { data : Array UInt8 }`. `ByteArray.mk` denotes to the wrapped array's
list, so it is a refinement-preserving bridge: a flat `Array` derivation lifts to
the `ByteArray` the host actually sends. -/

/-- The wire type `ByteArray`, denoting to its underlying byte list — the same
denotation the request-side `SpanBytes` uses (`buf.data.toList`). -/
instance : FlatRep ByteArray where
  denote b := b.data.toList

@[simp] theorem denote_byteArray (b : ByteArray) : FlatRep.denote b = b.data.toList := rfl

/-- **`refine_ofByteArray`.** A `ByteArray` refines its own byte list — the
reflexive abstraction relation for the wire type (generalizes
`Datapath.Refines.rfl_full`). -/
theorem refine_ofByteArray (b : ByteArray) : Refines b.data.toList b := rfl

/-- **The wire bridge.** `ByteArray.mk` carries an `Array`-level refinement to the
`ByteArray` wire type unchanged: what the flat array denotes, the wrapped
`ByteArray` denotes. -/
theorem refine_mk {a : List UInt8} {arr : Array UInt8} (h : Refines a arr) :
    Refines a (ByteArray.mk arr) := by
  show (ByteArray.mk arr).data.toList = a
  exact h

/-! ## THE DERIVED FLAT SERIALIZER — obtained from the combinators, not hand-written

`Reactor.serialize resp = serializeWire (build resp)` expands to a `List.++` chain
`statusLine ++ crlf ++ renderHeaders (allHeaders) ++ crlf ++ crlf ++ body`. We
express that chain's structure as (i) a fixed list of head fragments concatenated
by `flatten`, then (ii) the body appended as the shared right operand. The flat
version is then `foldAppend` over the head fragments (`refine_fold`) `++` the body
(`refine_append_shared`), and its refinement follows by chaining those two
combinator lemmas — the framework does the work. -/

/-- The header block as a flat list of byte fragments (`headerLine`s separated by
`crlf`), mirroring `Reactor.renderHeaders`' structure. `renderHeaders_eq_flatten`
proves its `flatten` is exactly `renderHeaders`. -/
def headerFragments : List (Bytes × Bytes) → List Bytes
  | []      => []
  | [h]     => [Reactor.headerLine h]
  | h :: t  => Reactor.headerLine h :: Reactor.crlf :: headerFragments t

/-- `renderHeaders` is the `flatten` of its fragment list — the spec's
right-recursive `++` chain re-presented as a flat fragment list (so the flat fold
can consume it). -/
theorem renderHeaders_eq_flatten :
    ∀ hs : List (Bytes × Bytes), Reactor.renderHeaders hs = (headerFragments hs).flatten
  | []          => rfl
  | [_]         => by simp [Reactor.renderHeaders, headerFragments]
  | _ :: _ :: t => by
      show Reactor.headerLine _ ++ Reactor.crlf ++ Reactor.renderHeaders (_ :: t) = _
      rw [renderHeaders_eq_flatten (_ :: t)]
      simp [headerFragments, List.append_assoc]

/-- The full HEAD fragment list of a wire record: status line, CRLF, the header
block fragments, and the blank-line separator (CRLF CRLF) — everything up to but
NOT including the body (which stays the shared right operand). -/
def wireHeadFragments (w : Reactor.Wire) : List Bytes :=
  [Reactor.statusLine w, Reactor.crlf] ++ headerFragments (Reactor.allHeaders w)
    ++ [Reactor.crlf, Reactor.crlf]

/-- **The framing decomposition (spec side).** `serializeWire w` is the `flatten`
of the head fragments followed by the body. This is the ONLY serialize-specific
lemma the derivation needs; everything flat is the calculus's doing. -/
theorem serializeWire_eq (w : Reactor.Wire) :
    Reactor.serializeWire w = (wireHeadFragments w).flatten ++ w.body := by
  unfold Reactor.serializeWire wireHeadFragments
  rw [renderHeaders_eq_flatten]
  simp [List.flatten_append, List.append_assoc]

/-- **The flat head builder** — `foldAppend` over the head fragments. This IS the
FOLD combinator applied; nothing serialize-specific, just the fragments. -/
def flatSerializeHead (w : Reactor.Wire) : Array UInt8 :=
  foldAppend List.toArray #[] (wireHeadFragments w)

/-- **The DERIVED flat response serializer.** The flat head (`foldAppend`) with the
body appended as the shared right operand, wrapped as the `ByteArray` wire type.
Built entirely from the calculus's combinators — no hand-written byte plumbing. -/
def flatSerialize (resp : Reactor.Response) : ByteArray :=
  let w := Reactor.build resp
  ByteArray.mk (flatSerializeHead w ++ w.body.toArray)

/-- **THE DERIVED-FRAGMENT REFINEMENT — proven FOR FREE from the combinators.**
The flat serializer refines the deployed `List`-typed `Reactor.serialize`. The
proof is a MECHANICAL chain: the head refines `(wireHeadFragments w).flatten` by
the FOLD combinator (`foldAppend_toArray_refines`); the body refines itself
(`refine_ofList`); the two combine by the shared-right-operand append
(`refine_append_shared`, i.e. `refine_append.right`); the wire bridge
(`refine_mk`) lifts to `ByteArray`; and the spec side collapses by the single
framing lemma `serializeWire_eq`. No reasoning about serialize's internals — the
calculus supplies the flatness. Non-vacuous: `flatSerialize` computes the bytes by
a genuine flat fold, not `serialize`. -/
theorem flatSerialize_refines (resp : Reactor.Response) :
    Refines (Reactor.serialize resp) (flatSerialize resp) := by
  -- head: the FOLD combinator
  have hhead : Refines (wireHeadFragments (Reactor.build resp)).flatten
      (flatSerializeHead (Reactor.build resp)) :=
    foldAppend_toArray_refines (wireHeadFragments (Reactor.build resp))
  -- body: the shared right operand refines itself
  have hbody : Refines (Reactor.build resp).body (Reactor.build resp).body.toArray :=
    refine_ofList (Reactor.build resp).body
  -- combine by append with the body as the shared right operand
  have happ : Refines ((wireHeadFragments (Reactor.build resp)).flatten ++ (Reactor.build resp).body)
      (flatSerializeHead (Reactor.build resp) ++ (Reactor.build resp).body.toArray) :=
    (refine_append_shared hbody).apply hhead
  -- lift to the ByteArray wire type
  have hmk := refine_mk happ
  -- collapse the spec side by the single framing lemma
  show (flatSerialize resp).data.toList = Reactor.serialize resp
  calc (flatSerialize resp).data.toList
      = (wireHeadFragments (Reactor.build resp)).flatten ++ (Reactor.build resp).body := hmk
    _ = Reactor.serialize resp := (serializeWire_eq (Reactor.build resp)).symm

/-! ## Non-vacuity — the derived flat op computes the SAME bytes on real inputs -/

/-- The flat serializer produces byte-identical output to the spec on a real
`200 OK` response — the derived op genuinely computes, and agrees. -/
example :
    (flatSerialize (Reactor.ok200 "hello".toUTF8.toList)).data.toList
      = Reactor.serialize (Reactor.ok200 "hello".toUTF8.toList) :=
  flatSerialize_refines _

-- A concrete `#guard`: the flat serialization of a real error response equals the
-- spec's, evaluated by the kernel (not just proven).
#guard (flatSerialize (Reactor.error4xx 404 "Not Found".toUTF8.toList "nope".toUTF8.toList)).data.toList
        == Reactor.serialize (Reactor.error4xx 404 "Not Found".toUTF8.toList "nope".toUTF8.toList)

-- Different responses serialize to different flat bytes (genuine dependence on
-- the input, not a constant).
#guard (flatSerialize (Reactor.ok200 "a".toUTF8.toList)).data.toList
        != (flatSerialize (Reactor.ok200 "bb".toUTF8.toList)).data.toList

/-! ## GENERALIZATION — the seed's request-side `SpanBytes` refinement and the
whole-serve `RefinesServe` are instances of THIS polymorphic calculus

The datapath seed (`Datapath.Refine`, `Datapath.Serve`) proved a *point-wise*
refinement `Datapath.Refines a s := s.denote = a` on the borrowed request window
`SpanBytes`, and a serve-level `RefinesServe serveA serveC`. Both are instances of
the general `FlatRep`/`Refines` here: `SpanBytes` and `OutBuf` are `FlatRep`s, the
seed's `Refines` is definitionally this module's `Refines`, and `RefinesServe` is
exactly the point-wise `Refines (serveA s.denote) (serveC s out)`. So this
calculus *generalizes* the seed's bespoke bridges into a reusable combinator
algebra. -/

/-- The borrowed request window is a `FlatRep` (its `denote` is the seed's). -/
instance : FlatRep Datapath.SpanBytes where
  denote s := s.denote

/-- **The seed's request-side refinement IS this calculus's `Refines`.** The
`SpanBytes` refinement relation from `Datapath.Refine` is definitionally the
general `Refines` — the seed was already a point instance of the framework. -/
theorem span_refines_iff (a : List UInt8) (s : Datapath.SpanBytes) :
    Datapath.Refines a s ↔ Refines a s := Iff.rfl

/-- The borrowed output buffer is a `FlatRep` (its live window is the denotation). -/
instance : FlatRep Datapath.OutBuf where
  denote o := o.bytes

/-- **`RefinesServe` is the point-wise instance of this calculus.** The seed's
serve-level obligation `RefinesServe serveA serveC` is exactly: for every
well-formed request span, the concrete serve's output `OutBuf` `Refines` the
abstract serve applied to the span's denotation. The whole-serve refinement the
compiler descent targets — a flat `serveC` proven to refine the `List`-spec
`serveA` — is this `Refines` at the serve grain; the combinator calculus above is
how that flat `serveC` is *built* (stage by stage: each stage's `List` structure
mapped to the flat combinators, refined by the lemmas + `comp`). -/
theorem refinesServe_iff_pointwise (serveA : Datapath.ServeA) (serveC : Datapath.ServeC) :
    Datapath.RefinesServe serveA serveC
      ↔ ∀ (s : Datapath.SpanBytes) (out : Datapath.OutBuf),
          s.Wf → Refines (serveA s.denote) (serveC s out) := Iff.rfl

/-! ## The whole-serve derivation + compiler composition (roadmap, stated precisely)

**How the fragment generalizes to the whole serve.** `flatSerialize` above is the
response *serialize* stage derived flat by the calculus. The deployed serve
`servePipelineFull2 = serialize ∘ runPipeline ∘ parse` is a composition of stages;
each stage is a `List`-typed byte transform whose `++`/`fold`/`map` structure maps
to the flat combinators here, and `RefinesFn.comp` (the functor law) composes the
per-stage refinements into a whole-serve refinement `RefinesFn serveA flatServe`
**by construction** — the same mechanical recipe applied stage by stage, the List
spec and all 50 lanes untouched. The remaining combinators to instantiate for full
coverage (named as the roadmap): the request-`parse` map (already proven point-wise
as `Datapath.spanParseRequest_refines` — a `RefinesFn` instance on `SpanBytes`),
and the per-stage transforms (`Reactor.runPipeline`), each a `map`/`fold`/`append`
composite the calculus already covers.

**How it composes with the compiler.** The flat `flatServe : … → ByteArray`
derived here is precisely the flat `serveC` the compiler descent (C-series) targets:
`List` spec → (this refinement) → flat Lean serve → (verified `leanc`-free lower) →
flat silicon. `flatSerialize_refines` closes the FIRST link (List spec ⇒ flat Lean)
for the serialize stage with the spec unchanged; the compiler closes the second
(flat Lean ⇒ machine code). The point-wise `RefinesServe` seam
(`refinesServe_iff_pointwise`) is where the two meet: the flat serve this calculus
builds is the object the compiler compiles, and its refinement of the `List` spec is
this module's `Refines`. -/

end Datapath.Refinement
