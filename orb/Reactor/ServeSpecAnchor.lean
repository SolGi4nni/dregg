import Reactor.Serialize
import Reactor.Stage.SecurityHeaders
import ServeSpec

/-!
# Reactor.ServeSpecAnchor — the dataplane side of the mirror-kill

The translator tree pins its serve constants against the SHARED `ServeSpec`
library (see the translator tree's serve-spec pin module). Until now the
DATAPLANE side of every such pin was a byte-for-byte RETYPED copy: the spec
constants were "the deployed bytes by inspection", anchored to nothing on this
side. This file closes that half — it `require`s the same `ServeSpec` (drorb's
FIRST external dependency) and proves, against the REAL deployed definitions:

* `serialize_eq` — the deployed `Reactor.serialize` IS the spec `ServeSpec.serialize`
  (across the trivial field-identity `Response` repack). A real cross-tree
  equation, by structural induction on the header render — not a transcription.
* `wireHeaders_is_spec` — the deployed security-header wire bytes
  (`wireHeaders policy`, driven off the real `SecurityHeaders.render` policy) ARE
  the spec's `SecurityHeadersDeployed.headers`. The retyped constant is dead: a
  fabricated byte would fail this equation.
* `securityheadersStage_anchored` — the deployed `securityheadersStage`'s built
  response transform equals the spec deployed stage's `onResp`, transported by the
  field-identity repack. The deployed stage's SEMANTICS is now the spec's.
* `ofSpec` + `securityheadersStageFromSpec_agrees` — the deployed stage COULD be
  DEFINED from the spec (`ofSpec ServeSpec.SecurityHeadersDeployed.stage`): the
  spec-derived stage is build-identical to the deployed one. This is the
  redefinition made safe — it does not touch the deployed stage's definition (so
  no deployed proof re-elaborates), yet exhibits the `deployed = ofSpec spec`
  closure.

This module is NOT in the deployed `Dataplane` closure (it is a standalone lib,
built on demand); it references the deployed definitions read-only and adds no
seam to the serving binary.
-/

namespace Reactor.ServeSpecAnchor

open Reactor.Pipeline
open Reactor.Stage.SecurityHeaders (securityheadersStage wireHeaders policy)
open Proto (Bytes)

/-! ## The response repack (field identity — both trees fix `Bytes := List UInt8`) -/

/-- Repack a deployed `Reactor.Response` as a spec `ServeSpec.Response`. Both trees
fix the same byte type, so this is a pure field identity. -/
def toSpecResp (r : Reactor.Response) : ServeSpec.Response :=
  { status := r.status, reason := r.reason, headers := r.headers, body := r.body }

/-- The inverse repack. -/
def toReactorResp (r : ServeSpec.Response) : Reactor.Response :=
  { status := r.status, reason := r.reason, headers := r.headers, body := r.body }

/-! ## 1. The serializer is the spec serializer -/

/-- The header render agrees across the trees, by induction on the header list
(both have the same three defining equations; `headerLine`/`crlf` are defeq). -/
theorem renderHeaders_eq (hs : List (Bytes × Bytes)) :
    Reactor.renderHeaders hs = ServeSpec.renderHeaders hs := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
    cases t with
    | nil => rfl
    | cons x xs =>
      show Reactor.headerLine h ++ Reactor.crlf ++ Reactor.renderHeaders (x :: xs)
         = ServeSpec.headerLine h ++ ServeSpec.crlf ++ ServeSpec.renderHeaders (x :: xs)
      rw [show ServeSpec.headerLine h = Reactor.headerLine h from rfl,
          show ServeSpec.crlf = Reactor.crlf from rfl, ih]

/-- **The deployed serializer IS the spec serializer.** Across the field-identity
`Response` repack, `Reactor.serialize` renders exactly `ServeSpec.serialize`. -/
theorem serialize_eq (r : Reactor.Response) :
    Reactor.serialize r = ServeSpec.serialize (toSpecResp r) := by
  show Reactor.serializeWire (Reactor.build r)
     = ServeSpec.serializeWire (ServeSpec.build (toSpecResp r))
  simp only [Reactor.serializeWire, ServeSpec.serializeWire,
             Reactor.statusLine, ServeSpec.statusLine,
             Reactor.allHeaders, ServeSpec.allHeaders,
             Reactor.build, ServeSpec.build, toSpecResp,
             Reactor.http11, ServeSpec.http11, Reactor.crlf, ServeSpec.crlf,
             Reactor.clName, ServeSpec.clName, Reactor.natToDec, ServeSpec.natToDec,
             renderHeaders_eq]

/-! ## 2. The deployed security-header bytes ARE the spec bytes -/

/-- **The retyped constant is dead.** The deployed security-header wire pairs —
computed off the REAL `SecurityHeaders.render policy` — are exactly the spec's
`SecurityHeadersDeployed.headers`. A fabricated byte fails this equation. -/
theorem wireHeaders_is_spec :
    wireHeaders policy = ServeSpec.SecurityHeadersDeployed.headers := by
  rfl

/-! ## 3. The deployed stage anchored to the spec stage -/

/-- **The deployed stage's semantics IS the spec stage's.** Building the deployed
`securityheadersStage`'s response transform, then repacking, equals the spec
deployed stage's `onResp` on the repacked base — for ANY context and builder. -/
theorem securityheadersStage_anchored (c : Ctx) (sctx : ServeSpec.Ctx) (b : ResponseBuilder) :
    toSpecResp ((securityheadersStage.onResponse c b).build)
      = ServeSpec.SecurityHeadersDeployed.stage.onResp sctx (toSpecResp b.build) := by
  show toSpecResp (((wireHeaders policy).foldl ResponseBuilder.addHeader b).build) = _
  rw [build_addHeaders]
  simp only [toSpecResp, wireHeaders_is_spec, ServeSpec.SecurityHeadersDeployed.stage]

/-! ## 4. The deployed stage COULD be defined FROM the spec (safe redefinition) -/

/-- Wrap a spec stage's functional `onResp` into a deployed `Stage` via the affine
builder's `mapResp`, transported across the field-identity repack. The request
phase passes (the deployed security stage never gates). -/
def ofSpec (s : ServeSpec.Stage) : Stage :=
  { name       := s.name
    onRequest  := fun c => .continue c
    onResponse := fun _ b => b.mapResp (fun r => toReactorResp (s.onResp {} (toSpecResp r))) }

/-- The spec-derived security stage. -/
def securityheadersStageFromSpec : Stage :=
  ofSpec ServeSpec.SecurityHeadersDeployed.stage

/-- **`deployed = ofSpec spec` at the build level.** The spec-derived stage's built
response transform is byte-identical to the deployed stage's — so the deployed
stage COULD be replaced by `ofSpec ServeSpec.SecurityHeadersDeployed.stage`
without changing a single served byte. The redefinition is sound; it is left
un-applied only to keep the deployed stage's existing proofs from re-elaborating. -/
theorem securityheadersStageFromSpec_agrees (c : Ctx) (b : ResponseBuilder) :
    (securityheadersStageFromSpec.onResponse c b).build
      = (securityheadersStage.onResponse c b).build := by
  show (b.mapResp (fun r => toReactorResp
          (ServeSpec.SecurityHeadersDeployed.stage.onResp {} (toSpecResp r)))).build
     = ((wireHeaders policy).foldl ResponseBuilder.addHeader b).build
  rw [build_mapResp, build_addHeaders]
  simp only [toReactorResp, toSpecResp, wireHeaders_is_spec,
             ServeSpec.SecurityHeadersDeployed.stage]

/-! ## 5. Non-vacuity + axiom audit -/

-- The deployed stage genuinely appends four headers (RHS not the identity).
#guard ServeSpec.SecurityHeadersDeployed.headers.length = 4

#print axioms serialize_eq
#print axioms wireHeaders_is_spec
#print axioms securityheadersStage_anchored
#print axioms securityheadersStageFromSpec_agrees

end Reactor.ServeSpecAnchor
