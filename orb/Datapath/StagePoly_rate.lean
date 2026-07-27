import Datapath.ByteSeq
import Datapath.ByteRefine
import Reactor.Stage.Rate

/-!
# Datapath.StagePoly_rate — the rate-limit GATE's `429` response, written ONCE
over `[ByteSeq T]`, and the load-bearing test: does its refinement FOLLOW from the
op laws?

This is the GATE-grain sibling of `Datapath.ByteSeqProto` / `Datapath.HdrSeqProto`.
Where `ByteSeqProto` wrote the compressed-egress serializer over `[ByteSeq T]` and
`HdrSeqProto` wrote three header-transform stages over `[HdrSeq H]`, this file takes
the ONE deployed *gate* stage — `Reactor.Stage.Rate.rateStage` — and writes the
byte effect it emits when it fires (`resp429`, a `429 Too Many Requests`) as a
single polymorphic serializer over `[ByteSeq T]`.

The rate gate's whole byte effect over the limit is `resp429` (read off the real
stage: `rateStage.onRequest c = .respond resp429` for an over-limit `c`, and the
built pipeline response IS `resp429` — `rateStage_onReq_respond` / `rateStage_gate_build`).
So the gate-grain poly target is the *wire serialization* of that rejection: the
head fragments (status line `HTTP/1.1 429 Too Many Requests`, the derived
`Content-Length`, the blank-line separator) concatenated with the body prose. The
body `tooManyBody` is the polymorphic `[ByteSeq T]` value; the head fragments are the
deployed literals.

`rateStagePoly` is ONE expression:

    rateStagePoly frags body := (foldCat frags) ++ body

Its `rateStagePoly_refines` is a ONE-line `simp` over the op laws (`append_denote`,
`foldCat_denote`) — NO per-stage induction, NO re-expression. It is then GROUNDED in
the REAL deployed stage: at the spec instance with the real head fragments and body
it is byte-for-byte `Reactor.serialize resp429` (`rateStagePoly_list_eq_serialize`,
against the actual `Reactor.serialize` / `serializeWire_eq`, not a re-spec), and
`rateStagePoly_grounds_gate` ties that to the real gate decision — when the bucket
is over the limit the deployed `rateStage` responds with exactly this `resp429`.
Instantiated at `List UInt8` (spec) and `ByteArray` (fast, genuinely flat).

## The gate-grain verdict

The gate is byte-grain-tractable with the SAME `ByteSeq` machinery as the egress
serializer: the refinement is one `simp` line, the body is genuinely flat end to
end on the `ByteArray` instance, and the head fragments are the same
`O(#headers)` deployed-literal residual (R1) `FlatBody`/`FlatWire`/`ByteSeqProto`
already carry — not the body. The gate's *decision* (`admits`, a `Bool`) is the
short-circuit CONDITION, not a byte transform, so it stays outside the `ByteSeq`
expression (exactly as `Ctx` stayed an external parameter for `corsStagePoly`);
the poly form computes the emitted `429` bytes, and the decision selects whether
those bytes fire. No bespoke per-stage work — a clean fit.
-/

namespace Datapath.StagePoly_rate

open Datapath.ByteSeq
open Datapath.Refinement (wireHeadFragments serializeWire_eq)
open Reactor.Stage.Rate (rateStage resp429 tooManyBody reason429 admits
  overCtx underCtx overCtx_over rateStage_onReq_respond)

/-! ## The polymorphic gate-response serializer -/

/-- **The rate gate's `429` response serializer, written ONCE over `[ByteSeq T]`.**
Fold the head fragments (status line, headers, blank-line separator), then append
the body. The head `frags` are the deployed wire-head literals; the `body` is the
polymorphic byte value. -/
def rateStagePoly {T : Type} [ByteSeq T] (frags : List T) (body : T) : T :=
  ByteSeq.append (foldCat frags) body

/-- The stage at the **spec** instance is exactly `frags.flatten ++ body` — the
`List UInt8` normal form. (`append@List = ++`, `foldCat@List = flatten`.) No
separate spec expression is written; this is `rateStagePoly` at `T := List UInt8`. -/
theorem rateStagePoly_list (frags : List (List UInt8)) (body : List UInt8) :
    rateStagePoly frags body = frags.flatten ++ body := by
  show foldCat frags ++ body = _
  rw [foldCat_list]

/-! ## ★ THE LOAD-BEARING THEOREM — the whole-stage refinement, proven ONCE

The proof is a `simp` chain over the op laws (`append_denote`, all `@[simp]`) plus
the single generic fold lemma `foldCat_denote`. NO per-stage induction, NO
re-expression of the stage. -/

/-- **The whole-stage refinement — FOLLOWS from the op laws.** The dense stage's
denotation equals the stage run at the spec instance on the denoted inputs. Proven
polymorphically in `T`; instantiates at BOTH `List UInt8` and `ByteArray`.
Discharged by `simp` over the op-level laws. -/
theorem rateStagePoly_refines {T : Type} [ByteSeq T] (frags : List T) (body : T) :
    ByteSeq.toBytes (rateStagePoly frags body)
      = rateStagePoly (T := List UInt8) (frags.map ByteSeq.toBytes) (ByteSeq.toBytes body) := by
  rw [rateStagePoly_list, rateStagePoly]
  simp only [ByteSeq.append_denote, foldCat_denote]

/-- The refinement at the fast `ByteArray` instance — a DIRECT instance of the
once-proven `rateStagePoly_refines`, no `ByteArray`-specific reasoning. -/
theorem rateStagePolyArray_refines (frags : List ByteArray) (fbody : ByteArray) :
    (rateStagePoly frags fbody).data.toList
      = rateStagePoly (T := List UInt8) (frags.map (·.data.toList)) fbody.data.toList :=
  rateStagePoly_refines frags fbody

/-! ## Grounding in the REAL deployed gate (non-vacuity, not a re-spec) -/

/-- **The stage at the spec instance IS the deployed `Reactor.serialize resp429`.**
For the real head fragments of the `429` rejection and its body `tooManyBody`,
`rateStagePoly` at `T := List UInt8` is byte-for-byte `Reactor.serialize resp429` —
grounded on the real `serializeWire_eq` (`serialize = head.flatten ++ body`) and
`(build resp429).body = tooManyBody`, not on a re-specified stage. -/
theorem rateStagePoly_list_eq_serialize :
    rateStagePoly (T := List UInt8)
        (wireHeadFragments (Reactor.build resp429)) tooManyBody
      = Reactor.serialize resp429 := by
  have hb : (Reactor.build resp429).body = tooManyBody := rfl
  rw [rateStagePoly_list, Reactor.serialize, serializeWire_eq, hb]

/-- **Grounded in the REAL deployed gate (non-vacuous).** When the bucket is over
the limit the deployed `rateStage` short-circuits with exactly `resp429`
(`rateStage_onReq_respond`), AND the poly serializer at the spec instance computes
that rejection's wire bytes byte-for-byte (`Reactor.serialize resp429`). So the poly
form is the serialization of the response the REAL gate emits — not a re-spec. -/
theorem rateStagePoly_grounds_gate (c : Reactor.Pipeline.Ctx) (hover : admits c = false) :
    rateStage.onRequest c = Reactor.Pipeline.StageStep.respond resp429
      ∧ rateStagePoly (T := List UInt8)
          (wireHeadFragments (Reactor.build resp429)) tooManyBody
          = Reactor.serialize resp429 :=
  ⟨rateStage_onReq_respond c hover, rateStagePoly_list_eq_serialize⟩

/-- **THE FLAT BYTE-IDENTITY.** The genuinely-flat `ByteArray` computation of
`rateStagePoly` (head fragments materialized from the deployed literals, body a real
`ByteArray`) is byte-identical to the deployed `Reactor.serialize resp429`. The
`List` body appears ONLY on the spec side. Chains the once-proven
`rateStagePolyArray_refines` with the spec grounding — NO extra per-stage work. -/
theorem rateStagePolyArray_serialize :
    (rateStagePoly
        ((wireHeadFragments (Reactor.build resp429)).map (fun l => (⟨l.toArray⟩ : ByteArray)))
        (⟨tooManyBody.toArray⟩ : ByteArray)).data.toList
      = Reactor.serialize resp429 := by
  have hfrags : ((wireHeadFragments (Reactor.build resp429)).map
        (fun l => (⟨l.toArray⟩ : ByteArray))).map (·.data.toList)
      = wireHeadFragments (Reactor.build resp429) := by
    simp [List.map_map, Function.comp_def, List.toList_toArray]
  rw [rateStagePolyArray_refines, hfrags]
  show rateStagePoly (T := List UInt8) _ (tooManyBody.toArray.toList) = _
  rw [List.toList_toArray, rateStagePoly_list_eq_serialize]

/-! ## Non-vacuity — the flat gate serializer genuinely computes the deployed `429` -/

-- The flat `ByteArray` `rateStagePoly` produces the exact deployed `Reactor.serialize
-- resp429` bytes — evaluated by the kernel, not just proven.
#guard
  (rateStagePoly
      ((wireHeadFragments (Reactor.build resp429)).map (fun l => (⟨l.toArray⟩ : ByteArray)))
      (⟨tooManyBody.toArray⟩ : ByteArray)).data.toList
    == Reactor.serialize resp429

-- The flat stage genuinely depends on the body: different bodies ⇒ different flat bytes.
#guard
  (rateStagePoly [("H".toUTF8 : ByteArray)] "a".toUTF8).data.toList
    != (rateStagePoly [("H".toUTF8 : ByteArray)] "bb".toUTF8).data.toList

-- The stage at the spec instance and at the flat instance agree on a concrete input
-- (the refinement, evaluated).
#guard
  (rateStagePoly [("H".toUTF8 : ByteArray)] "body".toUTF8).data.toList
    == rateStagePoly (T := List UInt8) ["H".toUTF8.toList] "body".toUTF8.toList

-- The deployed gate REALLY fires over the limit (the real bucket rejects `overCtx`):
-- `admits = false` is exactly the `.respond resp429` short-circuit branch of
-- `rateStage.onRequest`, so `rateStagePoly_grounds_gate` is non-vacuous — there is an
-- over-limit `c` for which the gate responds with the `resp429` this poly serializes.
#guard admits overCtx == false

-- The serialized `429` is the real rejection: nonempty and carries the `429` status.
#guard resp429.status == 429
#guard (rateStagePoly (T := List UInt8) (wireHeadFragments (Reactor.build resp429)) tooManyBody)
        == Reactor.serialize resp429

-- Every ByteSeq op is non-vacuous at the ByteArray instance (used in the body path).
#guard (ByteSeq.toBytes (ByteSeq.append ("ab".toUTF8 : ByteArray) "c".toUTF8)) == "abc".toUTF8.toList
#guard (ByteSeq.toBytes (foldCat [("a".toUTF8 : ByteArray), "b".toUTF8])) == "ab".toUTF8.toList

/-! ## Axiom audit — the polymorphic refinement, the spec grounding, the gate
grounding, the flat byte-identity. Expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms rateStagePoly_refines
#print axioms rateStagePolyArray_refines
#print axioms rateStagePoly_list_eq_serialize
#print axioms rateStagePoly_grounds_gate
#print axioms rateStagePolyArray_serialize

end Datapath.StagePoly_rate
