import Datapath.ByteSeq
import Datapath.ByteRefine
import Reactor.Stage.Compress

/-!
# Datapath.ByteSeqProto — the ONE real stage written polymorphically, and the
load-bearing test: does its refinement FOLLOW from the op laws?

## The stage

`servePoly` is the **compressed-response egress serializer**, written ONCE over an
abstract `[ByteSeq T]`:

    servePoly frags tag body := (foldCat frags) ++ ((singleton tag) ++ body)

It concatenates the response *head fragments* (`frags`, a fold — the `wireHeadFragments`
of the deployed serializer), prepends the compress **codec tag** to the body
(`singleton tag ++ body` = `codecTag enc :: body`, exactly
`Reactor.Stage.Compress.encode`), and appends the body. This is a REAL deployed
function: at the spec instance it is byte-for-byte `Reactor.serialize` of the
compress-encoded response (`servePolyList_eq_serialize`, proven against the actual
`Reactor.serialize` / `Reactor.serializeWire`, not a re-spec).

## The load-bearing test (the whole point of the prototype)

`servePoly_refines` proves, ONCE and polymorphically in `T`, that the stage's
denotation equals the stage run at the spec (`List UInt8`) instance on the denoted
inputs:

    toBytes (servePoly frags tag body)
      = servePoly (List UInt8) (frags.map toBytes) tag (toBytes body)

**Its proof is a `simp` chain over the op laws + the single generic fold lemma
`foldCat_denote` — NO per-stage induction, NO re-expression of the stage.** Lean
has no free-theorem generator, so this theorem is not *literally* free; but the
work is one `simp` line whose length is the number of distinct ops in the ONE
stage expression, discharged entirely by `append_denote` / `singleton_denote` /
`foldCat_denote`. The fan-out pays, per stage, a second hand-written flat
expression *plus* a bespoke `<stage>_refines`; here the refinement is a rewrite
that would be identical in shape for any straight-line/fold stage.

Instantiating `servePoly_refines` at `ByteArray` (`servePolyArray_refines`) and
chaining the spec grounding gives `servePolyArray_serialize`: the genuinely-flat
`ByteArray` computation is **byte-identical to the deployed `Reactor.serialize`**,
with the `List` body only on the spec side.

## Flatness (checked, not asserted)

The `ByteArray` instance's `append` is `ByteArray.append` (a `copySlice` packed
copy) and `singleton`/`push` are `Array`-backed — no cons-spine on the body. The
head *fragments* are materialized from the deployed `List`-fragment literals
(`fun l => ⟨l.toArray⟩`) — this is the SAME `O(#headers)` header-fragment residual
`Datapath.FlatBody`/`FlatWire` already carry (residual R1), NOT the body: the body
`fbody : ByteArray` is flat end to end.
-/

namespace Datapath.ByteSeqProto

open Datapath.ByteSeq
open Datapath.Refinement (wireHeadFragments serializeWire_eq)
open Reactor.Stage.Compress (Encoding encode codecTag)

/-! ## The polymorphic stage -/

/-- **The compressed-response egress serializer, written ONCE over `[ByteSeq T]`.**
Fold the head fragments, prepend the codec tag to the body, append the body. -/
def servePoly {T : Type} [ByteSeq T] (frags : List T) (tag : UInt8) (body : T) : T :=
  ByteSeq.append (foldCat frags) (ByteSeq.append (ByteSeq.singleton tag) body)

/-- The stage at the **spec** instance is exactly `frags.flatten ++ (tag :: body)`
— the `List UInt8` normal form. (`append@List = ++`, `singleton@List t = [t]`,
`foldCat@List = flatten`.) No separate spec expression is written; this is
`servePoly` itself at `T := List UInt8`. -/
theorem servePoly_list (frags : List (List UInt8)) (tag : UInt8) (body : List UInt8) :
    servePoly frags tag body = frags.flatten ++ (tag :: body) := by
  show foldCat frags ++ (ByteSeq.singleton tag ++ body) = _
  rw [foldCat_list]
  rfl

/-! ## ★ THE LOAD-BEARING THEOREM — the whole-stage refinement, proven ONCE

The proof is a `simp` chain over the op laws (`append_denote`, `singleton_denote`,
all `@[simp]`) plus the single generic fold lemma `foldCat_denote`. There is NO
per-stage induction and NO re-expression of the stage. -/

/-- **The whole-stage refinement — FOLLOWS from the op laws.** The dense stage's
denotation equals the stage run at the spec instance on the denoted inputs. Proven
polymorphically in `T`; instantiates at BOTH `List UInt8` (trivially, `toBytes =
id`) and `ByteArray` (the real content). Discharged by `simp` over the op-level
laws — the load-bearing evidence that a stage costs one expression + one rewrite,
not a bespoke per-stage proof. -/
theorem servePoly_refines {T : Type} [ByteSeq T] (frags : List T) (tag : UInt8) (body : T) :
    ByteSeq.toBytes (servePoly frags tag body)
      = servePoly (T := List UInt8) (frags.map ByteSeq.toBytes) tag (ByteSeq.toBytes body) := by
  rw [servePoly_list, servePoly]
  simp only [ByteSeq.append_denote, foldCat_denote, ByteSeq.singleton_denote, List.singleton_append]

/-- The refinement at the fast `ByteArray` instance: the flat computation's
denoted bytes equal the spec stage on the denoted inputs. A DIRECT instance of the
once-proven `servePoly_refines` — no `ByteArray`-specific reasoning. -/
theorem servePolyArray_refines (frags : List ByteArray) (tag : UInt8) (fbody : ByteArray) :
    (servePoly frags tag fbody).data.toList
      = servePoly (T := List UInt8) (frags.map (·.data.toList)) tag fbody.data.toList :=
  servePoly_refines frags tag fbody

/-! ## Grounding in the REAL deployed serializer (non-vacuity, not a re-spec) -/

/-- The compress-encoded response: the deployed `Reactor.Response` whose body is
`Reactor.Stage.Compress.encode enc resp.body` (the real compress container). -/
def encodedResp (resp : Reactor.Response) (enc : Encoding) : Reactor.Response :=
  { resp with body := encode enc resp.body }

/-- **The stage at the spec instance IS the deployed `Reactor.serialize`.** For the
head fragments of the compress-encoded response and the codec tag, `servePoly` at
`T := List UInt8` is byte-for-byte `Reactor.serialize (encodedResp resp enc)` —
grounded on the real `serializeWire_eq` (`serialize = head.flatten ++ body`) and
`encode enc b = codecTag enc :: b`, not on a re-specified stage. -/
theorem servePolyList_eq_serialize (resp : Reactor.Response) (enc : Encoding) :
    servePoly (T := List UInt8)
        (wireHeadFragments (Reactor.build (encodedResp resp enc)))
        (codecTag enc) resp.body
      = Reactor.serialize (encodedResp resp enc) := by
  rw [servePoly_list]
  show (wireHeadFragments (Reactor.build (encodedResp resp enc))).flatten ++ (codecTag enc :: resp.body)
      = Reactor.serialize (encodedResp resp enc)
  have hbody : (Reactor.build (encodedResp resp enc)).body = codecTag enc :: resp.body := by
    show encode enc resp.body = codecTag enc :: resp.body
    rfl
  rw [Reactor.serialize, serializeWire_eq, hbody]

/-- **THE FLAT BYTE-IDENTITY.** The genuinely-flat `ByteArray` computation of
`servePoly` (head fragments materialized from the deployed literals, body a real
`ByteArray`) is byte-identical to the deployed `Reactor.serialize` of the
compress-encoded response. The `List` body appears ONLY on the spec (RHS) side.
Chains the once-proven `servePolyArray_refines` with the spec grounding — NO extra
per-stage work. -/
theorem servePolyArray_serialize (resp : Reactor.Response) (enc : Encoding)
    (fbody : ByteArray) (hbody : fbody.data.toList = resp.body) :
    (servePoly ((wireHeadFragments (Reactor.build (encodedResp resp enc))).map (fun l => (⟨l.toArray⟩ : ByteArray)))
        (codecTag enc) fbody).data.toList
      = Reactor.serialize (encodedResp resp enc) := by
  have hfrags : ((wireHeadFragments (Reactor.build (encodedResp resp enc))).map
        (fun l => (⟨l.toArray⟩ : ByteArray))).map (·.data.toList)
      = wireHeadFragments (Reactor.build (encodedResp resp enc)) := by
    simp [List.map_map, Function.comp_def, List.toList_toArray]
  rw [servePolyArray_refines, hfrags, hbody, servePolyList_eq_serialize]

/-! ## Non-vacuity — the flat stage genuinely computes the deployed wire bytes -/

-- A concrete gzip-compressed `200 OK`: the flat `ByteArray` `servePoly` produces the
-- exact deployed `Reactor.serialize` bytes — evaluated by the kernel, not just proven.
#guard
  let resp : Reactor.Response :=
    { status := 200, reason := Reactor.reasonOK,
      headers := [("X-A".toUTF8.toList, "1".toUTF8.toList)], body := "hi".toUTF8.toList }
  let enc := Encoding.gzip
  let W := Reactor.build (encodedResp resp enc)
  (servePoly ((wireHeadFragments W).map (fun l => (⟨l.toArray⟩ : ByteArray)))
      (codecTag enc) "hi".toUTF8).data.toList
    == Reactor.serialize (encodedResp resp enc)

-- The flat stage genuinely depends on the body: different bodies ⇒ different flat bytes.
#guard
  (servePoly [("H".toUTF8 : ByteArray)] (0x1F : UInt8) "a".toUTF8).data.toList
    != (servePoly [("H".toUTF8 : ByteArray)] (0x1F : UInt8) "bb".toUTF8).data.toList

-- The stage at the spec instance and at the flat instance agree on a concrete input
-- (the refinement, evaluated).
#guard
  (servePoly [("H".toUTF8 : ByteArray)] (0x1F : UInt8) "body".toUTF8).data.toList
    == servePoly (T := List UInt8) ["H".toUTF8.toList] (0x1F : UInt8) "body".toUTF8.toList

-- Every ByteSeq op is non-vacuous at the ByteArray instance (size, get?, push, empty).
#guard (ByteSeq.size ("abc".toUTF8 : ByteArray)) == 3
#guard (ByteSeq.get? ("abc".toUTF8 : ByteArray) 1) == some (98 : UInt8)
#guard (ByteSeq.toBytes (ByteSeq.push ("ab".toUTF8 : ByteArray) 99)) == "abc".toUTF8.toList
#guard (ByteSeq.toBytes (ByteSeq.empty : ByteArray)) == ([] : List UInt8)

/-! ## Axiom audit — the op laws, the fold lemma, the polymorphic refinement, the
flat byte-identity. Expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms foldCat_denote
#print axioms servePoly_refines
#print axioms servePolyArray_refines
#print axioms servePolyList_eq_serialize
#print axioms servePolyArray_serialize

end Datapath.ByteSeqProto
