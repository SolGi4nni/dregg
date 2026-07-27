import Datapath.ByteSeq
import Datapath.HdrSeq
import Reactor.Stage.IpFilter

/-!
# Datapath.StagePoly.IpFilter — the `ipfilter` GATE written ByteSeq/HdrSeq-POLYMORPHIC

This is the GATE-grain sibling of `Datapath.HdrSeqProto` / `Datapath.ByteSeqProto`.
Where those wrote header-transform / body stages over `[HdrSeq H]` / `[ByteSeq T]`,
`ipfilter` is a **gate**: it decides on the REQUEST (the deployed
`IpFilter.permits` admission over the CIDR ruleset, read off the real
`Reactor.Stage.IpFilter.ipfilterStage.onRequest`) and, on a rejected client,
short-circuits the whole pipeline with a FIXED `403 Forbidden` response — skipping
the handler and every later stage. So the poly obligation is not a header/body
*transform* but the byte-identical construction of that fixed refusal response,
across BOTH grains it spans:

* its **header block** (`forbidden403.headers`, empty) written over `[HdrSeq H]`
  with `foldPush` (denotation from `foldPush_denote`); and
* its **body** (`forbidden403.body`, the fixed `"forbidden: ip not admitted"`
  message) written over `[ByteSeq T]` as a `foldCat` of per-byte `singleton`s
  (a genuinely flat `Array.push` construction at `ByteArray`, no cons-spine),
  denotation from `foldCat_denote` + `singleton_denote`.

Each poly form is ONE expression over the abstract representation, its refinement a
1-line `rw`/`simp` over the op laws (NO per-stage induction — the single byte-list
`flatten_map_single` fact is paid once, generic in `T`), instantiated at both
`List` (spec) and `HdrBlock`/`ByteArray` (fast). The construction is GROUNDED in the
REAL deployed effect twice over:

* `polyForbidden403_eq_deployed` — the poly-built response (at the spec instances)
  is byte-identical to the deployed `forbidden403`; and
* `ipfilterPoly_gates_blocked` — the REAL deployed gate (`ipfilterStage.onRequest`)
  `.respond`s exactly this poly-built response on a blocked client, i.e. the
  construction is tied to the REAL `deployAdmits`/`IpFilter.permits` decision, not
  re-specified.

## The gate-grain honest note

Unlike the header/body transforms, the gate's byte contribution is a **constant**
(the fixed 403) — there is no data-dependent transform to carry through the ops. So
the poly form's non-vacuity comes from (a) computing that constant at BOTH reps
(spec `List` and flat `ByteArray`/`HdrBlock`, `#guard`-checked equal to the deployed
`forbidden403` bytes), and (b) the tie to the REAL request-phase decision
(`ipfilterPoly_gates_blocked`). The op *machinery* (`foldCat`/`foldPush`/`singleton`)
is exercised genuinely; the *data* it folds is the fixed refusal, not stage input.
-/

namespace Datapath.StagePoly.IpFilter

open Proto (Bytes)
open Datapath.ByteSeq
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Reactor (Response)
open Reactor.Stage.IpFilter
  (forbidden403 forbiddenReason forbiddenBody ipfilterStage blockedCtx
   ipfilterStage_gates_blocked)

/-! ## The per-byte list fact — paid ONCE, generic in `T` (no per-stage induction) -/

/-- Flattening a per-element singleton-list map is the identity — the one list fact
the body construction needs, proven once (the poly refinement below is a `rw`). -/
theorem flatten_map_single (bs : List UInt8) : (bs.map (fun b => [b])).flatten = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.map_cons, List.flatten_cons, ih]

/-! ## 1. The 403 header block — written ONCE over `[HdrSeq H]` -/

/-- **The gate's refusal header block, written ONCE over `[HdrSeq H]`.** Fold the
deployed `forbidden403.headers` onto the empty block with `push`. (The deployed 403
carries no headers, so this denotes `[]`; the construction stays grounded in the
REAL `forbidden403.headers` rather than a re-specified `[]`.) -/
def ipfilterHeadersPoly {H : Type} [HdrSeq H] : H :=
  foldPush forbidden403.headers HdrSeq.empty

/-- **Grounded in the REAL deployed refusal.** The header block at the spec instance
IS `forbidden403.headers` — the block the deployed gate emits. -/
theorem ipfilterHeadersPoly_list :
    ipfilterHeadersPoly (H := List (Bytes × Bytes)) = forbidden403.headers := by
  rw [ipfilterHeadersPoly, foldPush_list]
  show ([] : List (Bytes × Bytes)) ++ forbidden403.headers = forbidden403.headers
  rw [List.nil_append]

/-- **The header refinement — FOLLOWS from the op laws.** The dense block's
denotation equals the block built at the spec instance. One `simp` over
`foldPush_denote` (⇐ `push_denote`) + `empty_denote` — no per-stage induction. -/
theorem ipfilterHeadersPoly_refines {H : Type} [HdrSeq H] :
    HdrSeq.toHdrs (ipfilterHeadersPoly (H := H))
      = ipfilterHeadersPoly (H := List (Bytes × Bytes)) := by
  rw [ipfilterHeadersPoly_list]
  simp only [ipfilterHeadersPoly, foldPush_denote, HdrSeq.empty_denote, List.nil_append]

/-- The header refinement at the fast `HdrBlock` instance — a DIRECT instance. -/
theorem ipfilterHeadersBlock_refines :
    HdrBlock.denote (ipfilterHeadersPoly (H := HdrBlock))
      = ipfilterHeadersPoly (H := List (Bytes × Bytes)) :=
  ipfilterHeadersPoly_refines (H := HdrBlock)

/-! ## 2. The 403 body — written ONCE over `[ByteSeq T]` -/

/-- **The gate's refusal body, written ONCE over `[ByteSeq T]`.** Concatenate the
deployed `forbidden403.body` byte-by-byte as `singleton`s with `foldCat` — a
genuinely flat `Array.push` construction at `ByteArray` (no cons-spine); the
denotation is the fixed refusal message. -/
def ipfilterBodyPoly {T : Type} [ByteSeq T] : T :=
  foldCat (forbidden403.body.map ByteSeq.singleton)

/-- The body's denotation is the deployed `forbidden403.body`, for EVERY instance.
`foldCat_denote` (⇐ `append_denote`/`empty_denote`) + `singleton_denote` + the one
generic list fact — no per-stage induction. -/
theorem ipfilterBodyPoly_denote {T : Type} [ByteSeq T] :
    ByteSeq.toBytes (ipfilterBodyPoly (T := T)) = forbidden403.body := by
  rw [ipfilterBodyPoly, foldCat_denote, List.map_map]
  simp only [Function.comp_def, ByteSeq.singleton_denote]
  exact flatten_map_single forbidden403.body

/-- **Grounded in the REAL deployed refusal.** The body at the spec instance IS
`forbidden403.body` — the bytes the deployed gate emits. -/
theorem ipfilterBodyPoly_list :
    ipfilterBodyPoly (T := List UInt8) = forbidden403.body := by
  have h := ipfilterBodyPoly_denote (T := List UInt8)
  simpa [ByteSeq.toBytes, instByteSeqList] using h

/-- **The body refinement — FOLLOWS from the op laws.** The dense body's denotation
equals the body built at the spec instance. One `rw` chaining the two groundings —
no per-stage induction. -/
theorem ipfilterBodyPoly_refines {T : Type} [ByteSeq T] :
    ByteSeq.toBytes (ipfilterBodyPoly (T := T)) = ipfilterBodyPoly (T := List UInt8) := by
  rw [ipfilterBodyPoly_denote, ipfilterBodyPoly_list]

/-- The body refinement at the fast `ByteArray` instance — a DIRECT instance. -/
theorem ipfilterBodyArray_refines :
    (ipfilterBodyPoly (T := ByteArray)).data.toList = ipfilterBodyPoly (T := List UInt8) :=
  ipfilterBodyPoly_refines (T := ByteArray)

/-! ## 3. The crux — the poly-built refusal IS the REAL deployed gate response -/

/-- The poly-built `403` refusal at the spec instances: header block from
`ipfilterHeadersPoly`, body from `ipfilterBodyPoly`. -/
def polyForbidden403 : Response :=
  { status := 403, reason := forbiddenReason,
    headers := ipfilterHeadersPoly (H := List (Bytes × Bytes)),
    body := ipfilterBodyPoly (T := List UInt8) }

/-- **Grounded (non-vacuous), part 1.** The poly-built refusal is byte-identical to
the deployed `forbidden403` — the response the REAL gate serves. Both header and
body are the poly forms at the spec instances, discharged by the two groundings. -/
theorem polyForbidden403_eq_deployed : polyForbidden403 = forbidden403 := by
  rw [polyForbidden403, ipfilterHeadersPoly_list, ipfilterBodyPoly_list]
  rfl

/-- **Grounded (non-vacuous), part 2 — tied to the REAL decision.** The deployed
gate (`ipfilterStage.onRequest`, running the REAL `deployAdmits`/`IpFilter.permits`
admission) `.respond`s EXACTLY the poly-built refusal on a blocked client. The poly
construction is the response the real gate emits, on the real request-phase
decision — not a re-spec. -/
theorem ipfilterPoly_gates_blocked :
    ipfilterStage.onRequest blockedCtx = .respond polyForbidden403 := by
  rw [polyForbidden403_eq_deployed]; exact ipfilterStage_gates_blocked

/-! ## Non-vacuity — the flat ops genuinely compute the REAL deployed refusal bytes -/

-- The flat `ByteArray` body computes the deployed `forbidden403.body` — kernel-run.
#guard (ipfilterBodyPoly (T := ByteArray)).data.toList == forbidden403.body

-- ... which is the REAL refusal message (grounded on the literal, not a re-spec).
#guard (ipfilterBodyPoly (T := ByteArray)).data.toList == "forbidden: ip not admitted".toUTF8.toList

-- Spec instance and flat instance agree on the body (the refinement, evaluated).
#guard (ipfilterBodyPoly (T := ByteArray)).data.toList == ipfilterBodyPoly (T := List UInt8)

-- The body is genuinely non-empty content, not a vacuous empty fold.
#guard (ipfilterBodyPoly (T := ByteArray)).data.toList != ([] : List UInt8)
#guard (ipfilterBodyPoly (T := ByteArray)).size == forbidden403.body.length

-- The flat `HdrBlock` header block computes the deployed `forbidden403.headers`.
#guard (HdrSeq.toHdrs (ipfilterHeadersPoly (H := HdrBlock))) == forbidden403.headers

-- The spec header block IS the deployed refusal's header block (the refinement, run).
#guard (HdrSeq.toHdrs (ipfilterHeadersPoly (H := HdrBlock)))
        == ipfilterHeadersPoly (H := List (Bytes × Bytes))

-- Every op used is non-vacuous at the flat instances.
#guard (ByteSeq.toBytes (ByteSeq.singleton (70 : UInt8) : ByteArray)) == [(70 : UInt8)]
#guard (HdrSeq.toHdrs (HdrSeq.empty : HdrBlock)) == ([] : List (Bytes × Bytes))

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms ipfilterHeadersPoly_refines
#print axioms ipfilterHeadersPoly_list
#print axioms ipfilterBodyPoly_refines
#print axioms ipfilterBodyPoly_list
#print axioms polyForbidden403_eq_deployed
#print axioms ipfilterPoly_gates_blocked

end Datapath.StagePoly.IpFilter
