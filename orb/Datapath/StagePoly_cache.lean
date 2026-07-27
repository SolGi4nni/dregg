import Datapath.HdrSeq
import Datapath.ByteSeq
import Datapath.ByteRefine
import Reactor.Deploy

/-!
# Datapath.StagePoly_cache — the deployed `cache` GATE written ONCE over
`[HdrSeq H]` (headers) AND `[ByteSeq T]` (body), and the honest verdict on its
grain.

This is the cache-row sibling of `Datapath.HdrSeqProto` (header stages) and
`Datapath.ByteSeqProto` / `Datapath.StagePoly_policy` (byte/gate stages). The
deployed row is `Reactor.Deploy.cacheEmptyStage`
(`Reactor.Stage.Cache.mkStage emptyCacheCfg`): the REAL `Cache.Store.get?` /
`isFresh` gate over an **EMPTY** store.

## What the deployed stage ACTUALLY does (read off `Reactor.Deploy`)

Two phases, both grounded in the real functions:

* **request phase** — `cacheEmptyStage.onRequest c = cfg.onReq c`, and with the
  EMPTY store `cfg.st.store.get? _ = none` on every key, so the deployed
  reduction is `.continue c` (`cacheEmptyStage_miss`, the real
  `Reactor.Stage.Cache.onReq_miss`). Every request MISSES and passes through — no
  spurious hit shadows a handler response.
* **response phase** — `mkStage`'s `onResponse := fun _ b => b` is the **identity**
  on the affine `ResponseBuilder`. A gate contributes bytes by short-circuiting,
  not by transforming the tail; on the (always-taken) pass-through path there is
  NO header fold and NO body fold.

So the deployed `cacheEmptyStage`'s net effect on the response — at BOTH grains,
the header block (`HdrSeq`) and the body (`ByteSeq`) — is the **identity
passthrough**. `cacheStagePoly` (§1) is that passthrough written ONCE over
`[HdrSeq H] [ByteSeq T]`, and `cacheStagePoly_eq_deployed` grounds it in the REAL
`cacheEmptyStage.onResponse` (not re-specified).

### HONEST re-scope note

Because the response phase IS the identity, the whole-stage refinement is `rfl`,
NOT the 1–2-line op-law `simp` of `securityStagePoly` / `servePoly`: there is no
`push`/`append`/`filter`/`foldCat` op to discharge, because the deployed empty
cache row folds NOTHING onto the response. The passthrough is honestly *thinner*
than a fold stage — the byte/header machinery is exercised only to state that the
deployed effect is the identity at both grains, which is falsifiable (it would
break if `onResponse` ever appended a header or body byte).

## §2 — the reachable-but-INERT hit branch (warm store)

The cache *mechanism*'s only wire contribution is on a fresh HIT: the gate
short-circuits with `.respond (render e.body)` (the REAL
`Reactor.Stage.Cache.onReq_hit`), whose wire bytes are `Reactor.serialize` of the
rendered stored response — a real body+header serialization. `cacheHitPoly` writes
that serialization ONCE over `[ByteSeq T]` (policy-style: `foldCat frags ++ body`),
byte-identical to `Reactor.serialize (render bt)`
(`cacheHitPoly_eq_serialize`, grounded on the real `serializeWire_eq`). This branch
is REACHABLE (the warm `cacheStage` fires it) but **INERT under the deployed empty
store** — `cacheEmptyStage` never hits — so it is presented as the cache
mechanism's fold content, NOT as the deployed row's effect.
-/

namespace Datapath.StagePoly_cache

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.ByteSeq
open Datapath.FlatHeaders (HdrBlock)
open Datapath.Refinement (wireHeadFragments serializeWire_eq)
open Reactor (Response)
open Reactor.Pipeline (Ctx StageStep Stage ResponseBuilder)
open Reactor.Deploy (cacheEmptyStage emptyCacheCfg)

/-! ## §1. The deployed passthrough — identity over `[HdrSeq H]` AND `[ByteSeq T]` -/

/-- **The `cache` row's response effect, written ONCE over both grains.** The
deployed `cacheEmptyStage` response phase is the identity on the affine builder, so
its net effect on the `(header block, body)` pair is the passthrough. Polymorphic
over the header representation `[HdrSeq H]` and the body representation
`[ByteSeq T]`; instantiates at `List (Bytes × Bytes)` / `List UInt8` (spec) and
`HdrBlock` / `ByteArray` (fast, genuinely flat). -/
def cacheStagePoly {H T : Type} [HdrSeq H] [ByteSeq T] (h : H) (t : T) : H × T := (h, t)

/-- **The whole-stage refinement — the identity, at both grains.** The dense
stage's denotation (`toHdrs` of the header component, `toBytes` of the body
component) equals the stage run at the spec instances on the denoted inputs.
Proven polymorphically in `H` and `T`; `rfl`, because the deployed response phase
folds NOTHING — there is no op law to discharge (honestly thinner than a fold
stage's `simp`). -/
theorem cacheStagePoly_refines {H T : Type} [HdrSeq H] [ByteSeq T] (h : H) (t : T) :
    (HdrSeq.toHdrs (cacheStagePoly h t).1, ByteSeq.toBytes (cacheStagePoly h t).2)
      = ( (cacheStagePoly (H := List (Bytes × Bytes)) (T := List UInt8)
            (HdrSeq.toHdrs h) (ByteSeq.toBytes t)).1,
          (cacheStagePoly (H := List (Bytes × Bytes)) (T := List UInt8)
            (HdrSeq.toHdrs h) (ByteSeq.toBytes t)).2 ) := rfl

/-- The refinement at the fast `HdrBlock` / `ByteArray` instances — a DIRECT
instance of the once-proven polymorphic theorem, no representation-specific
reasoning. -/
theorem cacheStageFast_refines (h : HdrBlock) (t : ByteArray) :
    ( (cacheStagePoly h t).1.denote, (cacheStagePoly h t).2.data.toList )
      = ( (cacheStagePoly (H := List (Bytes × Bytes)) (T := List UInt8)
            h.denote t.data.toList).1,
          (cacheStagePoly (H := List (Bytes × Bytes)) (T := List UInt8)
            h.denote t.data.toList).2 ) :=
  cacheStagePoly_refines h t

/-! ### Grounding in the REAL deployed `cacheEmptyStage` (non-vacuity, not a re-spec) -/

/-- **The deployed response phase IS the identity.** Read off the real
`Reactor.Stage.Cache.mkStage` (`onResponse := fun _ b => b`): the deployed
`cacheEmptyStage.onResponse` leaves the affine builder untouched. `rfl`; grounded on
the actual stage, not re-specified. -/
theorem cacheEmptyStage_onResponse_id (c : Ctx) (b : ResponseBuilder) :
    cacheEmptyStage.onResponse c b = b := rfl

/-- **The deployed request phase MISSES.** The empty store yields `none` on every
key, so the real gate reduces to `.continue c` — every request passes through, no
spurious hit. `rfl`; grounded on the actual `emptyCacheCfg` (empty store). -/
theorem cacheEmptyStage_miss (c : Ctx) : cacheEmptyStage.onRequest c = .continue c := rfl

/-- **Grounded in the REAL deployed stage (non-vacuous).** The poly stage at the
spec instances computes exactly the deployed `cacheEmptyStage.onResponse`'s net
`(headers, body)` effect — which is the identity passthrough. Reads the effect off
the actual `onResponse` (`cacheEmptyStage_onResponse_id`); it would FAIL if the
deployed stage appended any header or body byte. -/
theorem cacheStagePoly_eq_deployed (c : Ctx) (b : ResponseBuilder) :
    cacheStagePoly (H := List (Bytes × Bytes)) (T := List UInt8)
        b.build.headers b.build.body
      = ( ((cacheEmptyStage.onResponse c b).build).headers,
          ((cacheEmptyStage.onResponse c b).build).body ) := by
  rw [cacheEmptyStage_onResponse_id]
  rfl

/-! ## §2. The reachable-but-INERT hit branch — the cache mechanism's fold content

Grounded in `Reactor.Stage.Cache`. REACHABLE (the warm `cacheStage` fires it) but
INERT under the deployed empty store (`cacheEmptyStage` never hits). -/

open Reactor.Stage.Cache (render mkStage onReq_hit Config)

/-- **The cache HIT's wire contribution, written ONCE over `[ByteSeq T]`.** On a
fresh hit the gate short-circuits with `.respond (render e.body)`, whose wire bytes
are the head fragments folded then the body appended (a gate has no codec tag;
head ++ body — exactly `Datapath.StagePoly_policy.policyStagePoly`'s shape). -/
def cacheHitPoly {T : Type} [ByteSeq T] (frags : List T) (body : T) : T :=
  ByteSeq.append (foldCat frags) body

/-- The hit stage at the **spec** instance is exactly `frags.flatten ++ body` — the
`List UInt8` normal form. No separate spec expression; this is `cacheHitPoly` at
`T := List UInt8`. -/
theorem cacheHitPoly_list (frags : List (List UInt8)) (body : List UInt8) :
    cacheHitPoly frags body = frags.flatten ++ body := by
  show foldCat frags ++ body = _
  rw [foldCat_list]

/-- **The hit-contribution refinement — FOLLOWS from the op laws.** Discharged by
`simp` over `append_denote` (`@[simp]`) + the one generic fold lemma
`foldCat_denote` — NO per-stage induction, NO re-expression. -/
theorem cacheHitPoly_refines {T : Type} [ByteSeq T] (frags : List T) (body : T) :
    ByteSeq.toBytes (cacheHitPoly frags body)
      = cacheHitPoly (T := List UInt8) (frags.map ByteSeq.toBytes) (ByteSeq.toBytes body) := by
  rw [cacheHitPoly_list, cacheHitPoly]
  simp only [ByteSeq.append_denote, foldCat_denote]

/-- The refinement at the fast `ByteArray` instance — a DIRECT instance. -/
theorem cacheHitArray_refines (frags : List ByteArray) (fbody : ByteArray) :
    (cacheHitPoly frags fbody).data.toList
      = cacheHitPoly (T := List UInt8) (frags.map (·.data.toList)) fbody.data.toList :=
  cacheHitPoly_refines frags fbody

/-- **The hit stage at the spec instance IS `Reactor.serialize (render bt)`.** For
the head fragments and body of the rendered stored response, `cacheHitPoly` at
`T := List UInt8` is byte-for-byte `Reactor.serialize (render bt)` — grounded on the
real `serializeWire_eq` and the REAL `Reactor.Stage.Cache.render`, not re-specified. -/
theorem cacheHitPoly_eq_serialize (bt : _root_.Cache.Body) :
    cacheHitPoly (T := List UInt8)
        (wireHeadFragments (Reactor.build (render bt))) (render bt).body
      = Reactor.serialize (render bt) := by
  rw [cacheHitPoly_list, Reactor.serialize, serializeWire_eq]
  rfl

/-- **THE FLAT BYTE-IDENTITY.** The genuinely-flat `ByteArray` computation of the
rendered-stored-response bytes (head fragments materialized from the deployed
literals, body a real `ByteArray`) is byte-identical to
`Reactor.serialize (render bt)` — the exact wire bytes a fresh cache hit produces.
The `List` body appears ONLY on the spec (RHS) side. -/
theorem cacheHitArray_serialize (bt : _root_.Cache.Body) (fbody : ByteArray)
    (hbody : fbody.data.toList = (render bt).body) :
    (cacheHitPoly
        ((wireHeadFragments (Reactor.build (render bt))).map (fun l => (⟨l.toArray⟩ : ByteArray)))
        fbody).data.toList
      = Reactor.serialize (render bt) := by
  have hfrags : ((wireHeadFragments (Reactor.build (render bt))).map
        (fun l => (⟨l.toArray⟩ : ByteArray))).map (·.data.toList)
      = wireHeadFragments (Reactor.build (render bt)) := by
    simp [List.map_map, Function.comp_def, List.toList_toArray]
  rw [cacheHitArray_refines, hfrags, hbody, cacheHitPoly_eq_serialize]

/-- **The hit fires the rendered response, poly byte-identical.** When a fresh entry
`e` is present under `c`'s key, (a) the deployed gate `(mkStage cfg).onRequest c` IS
`.respond (cfg.render e.body)` (the REAL `onReq_hit`), and (b) for the deployed
render, the poly form of that response is byte-identical to
`Reactor.serialize (render e.body)`. Both grounded in `Reactor.Stage.Cache`. -/
theorem cache_hit_bytes (cfg : Config) (c : Ctx) (e : _root_.Cache.Stored)
    (hget : cfg.st.store.get? (cfg.keyOf c) = some e)
    (hfresh : e.«meta».isFresh cfg.now = true) :
    (mkStage cfg).onRequest c = .respond (cfg.render e.body)
    ∧ cacheHitPoly (T := List UInt8)
        (wireHeadFragments (Reactor.build (render e.body))) (render e.body).body
      = Reactor.serialize (render e.body) :=
  ⟨onReq_hit cfg c e hget hfresh, cacheHitPoly_eq_serialize e.body⟩

/-! ## Non-vacuity — the poly forms genuinely compute the REAL deployed effects -/

/-- A fixed context (the response phase ignores it — `onResponse := fun _ b => b`). -/
def dummyCtx : Ctx := { input := [], req := { method := [], target := [] } }

-- §1: the flat `HdrBlock`/`ByteArray` passthrough computes the DEPLOYED
-- `cacheEmptyStage.onResponse` `(headers, body)` effect on a concrete builder —
-- evaluated by the kernel, routed through the REAL deployed stage.
#guard
  let r : Response :=
    { status := 200, reason := Reactor.reasonOK,
      headers := [("a".toUTF8.toList, "b".toUTF8.toList)], body := "hi".toUTF8.toList }
  let b := ResponseBuilder.ofResponse r
  let hb := HdrBlock.ofList r.headers
  let tb : ByteArray := ⟨r.body.toArray⟩
  ((cacheStagePoly hb tb).1.denote, (cacheStagePoly hb tb).2.data.toList)
    == ( ((cacheEmptyStage.onResponse dummyCtx b).build).headers,
         ((cacheEmptyStage.onResponse dummyCtx b).build).body )

-- §1: spec instance and flat instance agree on a concrete pair (the refinement, run).
#guard
  let hb := HdrBlock.ofList [("h".toUTF8.toList, "v".toUTF8.toList)]
  let tb : ByteArray := "body".toUTF8
  ((cacheStagePoly hb tb).1.denote, (cacheStagePoly hb tb).2.data.toList)
    == ((cacheStagePoly (H := List (Bytes × Bytes)) (T := List UInt8)
          hb.denote tb.data.toList).1,
        (cacheStagePoly (H := List (Bytes × Bytes)) (T := List UInt8)
          hb.denote tb.data.toList).2)

-- §2: the flat `ByteArray` hit contribution produces the EXACT
-- `Reactor.serialize (render bt)` bytes — the real rendered stored response.
#guard
  let bt : _root_.Cache.Body := { id := 7 }
  (cacheHitPoly ((wireHeadFragments (Reactor.build (render bt))).map (fun l => (⟨l.toArray⟩ : ByteArray)))
      (⟨(render bt).body.toArray⟩ : ByteArray)).data.toList
    == Reactor.serialize (render bt)

-- §2: the hit contribution genuinely depends on the body (different stored → different bytes).
#guard
  (cacheHitPoly [("H".toUTF8 : ByteArray)] "a".toUTF8).data.toList
    != (cacheHitPoly [("H".toUTF8 : ByteArray)] "bb".toUTF8).data.toList

-- Every op is non-vacuous at the flat instances (HdrBlock push/empty; ByteArray fold/append/empty).
#guard (HdrSeq.toHdrs (HdrSeq.push (HdrBlock.ofList []) ("a".toUTF8.toList, "b".toUTF8.toList)))
        == [("a".toUTF8.toList, "b".toUTF8.toList)]
#guard (HdrSeq.toHdrs (HdrSeq.empty : HdrBlock)) == ([] : List (Bytes × Bytes))
#guard (ByteSeq.toBytes (foldCat [("ab".toUTF8 : ByteArray), "c".toUTF8])) == "abc".toUTF8.toList
#guard (ByteSeq.toBytes (ByteSeq.append ("ab".toUTF8 : ByteArray) "c".toUTF8)) == "abc".toUTF8.toList
#guard (ByteSeq.toBytes (ByteSeq.empty : ByteArray)) == ([] : List UInt8)

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms cacheStagePoly_refines
#print axioms cacheStageFast_refines
#print axioms cacheEmptyStage_onResponse_id
#print axioms cacheEmptyStage_miss
#print axioms cacheStagePoly_eq_deployed
#print axioms cacheHitPoly_refines
#print axioms cacheHitArray_refines
#print axioms cacheHitPoly_eq_serialize
#print axioms cacheHitArray_serialize
#print axioms cache_hit_bytes

end Datapath.StagePoly_cache
