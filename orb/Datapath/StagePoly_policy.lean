import Datapath.ByteSeq
import Datapath.ByteRefine
import Reactor.Deploy

/-!
# Datapath.StagePoly_policy — the deployed `policy` GATE written ONCE over
`[ByteSeq T]`, and the load-bearing test: does its byte-identity FOLLOW from the
op laws?

This is the GATE-grain sibling of `Datapath.ByteSeqProto` (`servePoly`, a body
serializer) and `Datapath.HdrSeqProto` (the header stages). The grain here is a
**gate**: `Reactor.Deploy.policyStage`'s whole effect is in the REQUEST phase — an
ACL decision (`Reactor.Deploy.policyReserved`, the REAL `deployDecisionOf` /
`Policy.serveDecision`) that, when it fires, short-circuits the pipeline with the
fixed **denied response** `Reactor.Deploy.forbidden403` (`403`, body
`"policy: undeclared surface\n"`). The gate's `onResponse` is the identity on the
affine builder, so there is no header/body fold on the pass-through path.

What a fired gate contributes to the wire is exactly the SERIALIZATION of the
denied response. `policyStagePoly` writes that serialization ONCE over an abstract
`[ByteSeq T]`:

    policyStagePoly frags body := (foldCat frags) ++ body

It folds the response *head fragments* (`frags`, the `wireHeadFragments` of the
denied response) and appends the body — the gate has no codec tag (unlike
`servePoly`), just head ++ body. This is a REAL deployed function: at the spec
instance it is byte-for-byte `Reactor.serialize forbidden403`
(`policyStagePoly_eq_serialize`, grounded on the actual `Reactor.serialize` /
`serializeWire_eq`, not re-specified).

## The load-bearing test (the whole point)

`policyStagePoly_refines` proves, ONCE and polymorphically in `T`, that the
denied-response serialization's denotation equals the stage run at the spec
(`List UInt8`) instance on the denoted inputs. **Its proof is a 2-line `simp`
chain over the op laws (`append_denote`) + the single generic fold lemma
`foldCat_denote` — NO per-stage induction, NO re-expression of the gate.**
Instantiating at `ByteArray` (`policyStageArray_refines`) and chaining the spec
grounding gives `policyStageArray_serialize`: the genuinely-flat `ByteArray`
denied-response bytes are **byte-identical to the deployed `Reactor.serialize
forbidden403`** — the exact wire bytes the REAL gate's `.respond forbidden403`
short-circuit produces.

## Grounding the ACL decision → denied response (not a re-spec)

`policyStage_denies` reads the REAL gate: when `policyReserved c.req` holds, the
deployed `policyStage.onRequest c` IS `.respond forbidden403`. `policy_denied_bytes`
joins the two: the ACL decision fires the denied response AND the poly form of that
denied response is byte-identical to the deployed serialize.
-/

namespace Datapath.StagePoly_policy

open Datapath.ByteSeq
open Datapath.Refinement (wireHeadFragments serializeWire_eq)
open Reactor.Deploy (forbidden403 policyStage policyReserved)
open Reactor.Pipeline (Ctx)

/-! ## The polymorphic denied-response serializer (the gate's fired effect) -/

/-- **The `policy` gate's fired effect — the denied-response serialization, written
ONCE over `[ByteSeq T]`.** Fold the denied response's head fragments (`frags`) and
append the body. A gate has no codec tag; its wire contribution is head ++ body. -/
def policyStagePoly {T : Type} [ByteSeq T] (frags : List T) (body : T) : T :=
  ByteSeq.append (foldCat frags) body

/-- The stage at the **spec** instance is exactly `frags.flatten ++ body` — the
`List UInt8` normal form. (`append@List = ++`, `foldCat@List = flatten`.) No
separate spec expression is written; this is `policyStagePoly` at `T := List UInt8`. -/
theorem policyStagePoly_list (frags : List (List UInt8)) (body : List UInt8) :
    policyStagePoly frags body = frags.flatten ++ body := by
  show foldCat frags ++ body = _
  rw [foldCat_list]

/-! ## ★ THE LOAD-BEARING THEOREM — the whole-gate byte-identity, proven ONCE -/

/-- **The whole-gate refinement — FOLLOWS from the op laws.** The dense denied-
response serialization's denotation equals the stage run at the spec instance on
the denoted inputs. Proven polymorphically in `T`; discharged by `simp` over the
op-level laws (`append_denote`, all `@[simp]`) + the one generic fold lemma
`foldCat_denote` — NO per-stage induction, NO re-expression of the gate. -/
theorem policyStagePoly_refines {T : Type} [ByteSeq T] (frags : List T) (body : T) :
    ByteSeq.toBytes (policyStagePoly frags body)
      = policyStagePoly (T := List UInt8) (frags.map ByteSeq.toBytes) (ByteSeq.toBytes body) := by
  rw [policyStagePoly_list, policyStagePoly]
  simp only [ByteSeq.append_denote, foldCat_denote]

/-- The refinement at the fast `ByteArray` instance — a DIRECT instance of the
once-proven `policyStagePoly_refines`, no `ByteArray`-specific reasoning. -/
theorem policyStageArray_refines (frags : List ByteArray) (fbody : ByteArray) :
    (policyStagePoly frags fbody).data.toList
      = policyStagePoly (T := List UInt8) (frags.map (·.data.toList)) fbody.data.toList :=
  policyStagePoly_refines frags fbody

/-! ## Grounding in the REAL deployed gate + serializer (non-vacuity, not a re-spec) -/

/-- **The ACL decision → denied response, read off the REAL gate.** When the REAL
`policyReserved` holds on the request, the deployed `policyStage.onRequest` IS
`.respond forbidden403` — the denied response the poly form serializes. `rfl` up to
the `cond` branch; grounded on `policyStage`, not re-specified. -/
theorem policyStage_denies (c : Ctx) (hr : policyReserved c.req = true) :
    policyStage.onRequest c = .respond forbidden403 := by
  simp only [policyStage, hr, cond_true]

/-- **The gate at the spec instance IS `Reactor.serialize forbidden403`.** For the
head fragments and body of the denied response, `policyStagePoly` at
`T := List UInt8` is byte-for-byte `Reactor.serialize forbidden403` — grounded on
the real `serializeWire_eq` (`serializeWire = head.flatten ++ body`) and the fact
that `build` pins the body unchanged, not on a re-specified stage. -/
theorem policyStagePoly_eq_serialize :
    policyStagePoly (T := List UInt8)
        (wireHeadFragments (Reactor.build forbidden403)) forbidden403.body
      = Reactor.serialize forbidden403 := by
  rw [policyStagePoly_list, Reactor.serialize, serializeWire_eq]
  rfl

/-- **THE FLAT BYTE-IDENTITY.** The genuinely-flat `ByteArray` computation of the
denied-response bytes (head fragments materialized from the deployed literals, body
a real `ByteArray`) is byte-identical to the deployed `Reactor.serialize
forbidden403` — the exact wire bytes the REAL gate's `.respond forbidden403`
short-circuit produces. The `List` body appears ONLY on the spec (RHS) side. Chains
`policyStageArray_refines` with the spec grounding — NO extra per-stage work. -/
theorem policyStageArray_serialize (fbody : ByteArray)
    (hbody : fbody.data.toList = forbidden403.body) :
    (policyStagePoly
        ((wireHeadFragments (Reactor.build forbidden403)).map (fun l => (⟨l.toArray⟩ : ByteArray)))
        fbody).data.toList
      = Reactor.serialize forbidden403 := by
  have hfrags : ((wireHeadFragments (Reactor.build forbidden403)).map
        (fun l => (⟨l.toArray⟩ : ByteArray))).map (·.data.toList)
      = wireHeadFragments (Reactor.build forbidden403) := by
    simp [List.map_map, Function.comp_def, List.toList_toArray]
  rw [policyStageArray_refines, hfrags, hbody, policyStagePoly_eq_serialize]

/-- **THE GATE: ACL decision → denied response, poly byte-identical.** When the REAL
`policyReserved` fires, (a) the deployed `policyStage` responds with exactly
`forbidden403`, and (b) the poly form of that denied response is byte-identical to
`Reactor.serialize forbidden403`. Decision and denied bytes, both grounded in the
REAL `policyStage` / `Reactor.serialize`. -/
theorem policy_denied_bytes (c : Ctx) (hr : policyReserved c.req = true) :
    policyStage.onRequest c = .respond forbidden403
    ∧ policyStagePoly (T := List UInt8)
        (wireHeadFragments (Reactor.build forbidden403)) forbidden403.body
      = Reactor.serialize forbidden403 :=
  ⟨policyStage_denies c hr, policyStagePoly_eq_serialize⟩

/-! ## Non-vacuity — the flat gate genuinely computes the deployed denied-wire bytes -/

-- The flat `ByteArray` `policyStagePoly` (head fragments from the deployed literals,
-- the real denied body) produces the EXACT deployed `Reactor.serialize forbidden403`
-- bytes — evaluated by the kernel, not just proven.
#guard
  (policyStagePoly ((wireHeadFragments (Reactor.build forbidden403)).map (fun l => (⟨l.toArray⟩ : ByteArray)))
      (⟨forbidden403.body.toArray⟩ : ByteArray)).data.toList
    == Reactor.serialize forbidden403

-- The flat gate genuinely depends on the body: different bodies ⇒ different flat bytes.
#guard
  (policyStagePoly [("H".toUTF8 : ByteArray)] "a".toUTF8).data.toList
    != (policyStagePoly [("H".toUTF8 : ByteArray)] "bb".toUTF8).data.toList

-- Spec instance and flat instance agree on a concrete input (the refinement, run).
#guard
  (policyStagePoly [("H".toUTF8 : ByteArray)] "body".toUTF8).data.toList
    == policyStagePoly (T := List UInt8) ["H".toUTF8.toList] "body".toUTF8.toList

-- The ops genuinely compute at the flat ByteArray instance (fold, append, empty).
#guard (ByteSeq.toBytes (foldCat [("ab".toUTF8 : ByteArray), "c".toUTF8])) == "abc".toUTF8.toList
#guard (ByteSeq.toBytes (ByteSeq.append ("ab".toUTF8 : ByteArray) "c".toUTF8)) == "abc".toUTF8.toList
#guard (ByteSeq.toBytes (ByteSeq.empty : ByteArray)) == ([] : List UInt8)

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms policyStagePoly_refines
#print axioms policyStageArray_refines
#print axioms policyStage_denies
#print axioms policyStagePoly_eq_serialize
#print axioms policyStageArray_serialize
#print axioms policy_denied_bytes

end Datapath.StagePoly_policy
