import Reactor.Deploy
import Reactor.BraidCalculus

/-!
# Reactor.BraidCalculusDemo — the WIN, demonstrated

Re-derives four of `Reactor.Deploy`'s BESPOKE braid-composition theorems as ONE-LINE
applications of the three general lemmas in `Reactor.BraidCalculus`, proving the
calculus genuinely subsumes them (and that the general lemmas are non-vacuous — the
concrete `Deploy` braid stages instantiate them). This file is additive: it imports
`Reactor.Deploy` and `Reactor.BraidCalculus` and edits neither.

| bespoke theorem (Deploy)          | general lemma          | bespoke proof-body lines | here |
|-----------------------------------|------------------------|--------------------------|------|
| `braided2_conn_denies_status`     | `braid_gate` (pref []) | ~10                      | 1    |
| `braided2_stick_denies_status`    | `braid_gate` (pref 1)  | ~11                      | ~4   |
| `braided2_errorpage_maps_404`     | `braid_transform`      | ~15                      | ~6   |
| `braided2_off_eq`                 | `braided_off_eq_extend`| ~14                      | ~4   |
-/

namespace Reactor.BraidCalculusDemo

open Proto (Bytes)
open Reactor.Deploy
open Reactor.BraidCalculus
open Reactor.Pipeline (Ctx Stage runPipeline)

/-! ## (1) `braid_gate` — the gate family, re-derived as one-liners -/

/-- `braided2_conn_denies_status` re-derived: pref `[]`, so `nil_transparent`. The whole
bespoke `have hst … / have hgs … / rw [show … , hgs] / rfl` collapses to one term. -/
theorem braided2_conn_denies_status' (c : Ctx) (nv : Bytes × Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == connMarker) = some nv) :
    ((runPipeline braidedChain2 appHandler c).build).status = 503 :=
  braid_gate [] connBraidStage _ appHandler c _ (nil_transparent c)
    (connBraidStage_denies c nv hfind)
    (fun t ht => braidedChain2_statusStable t (List.mem_cons_of_mem _ ht))

/-- `braided2_stick_denies_status` re-derived: pref `[connBraidStage]`. -/
theorem braided2_stick_denies_status' (c : Ctx) (nv : Bytes × Bytes)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == stickMarker) = some nv) :
    ((runPipeline braidedChain2 appHandler c).build).status = 429 :=
  braid_gate [connBraidStage] stickBraidStage _ appHandler c _
    (cons_transparent (connBraidStage_off c hconn) (nil_transparent c))
    (stickBraidStage_denies c nv hfind)
    (fun t ht => braidedChain2_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))

/-! ## (2) `braid_transform` — the transform family, re-derived -/

/-- `braided2_errorpage_maps_404` re-derived via `braid_transform`: the general lemma
peels the three gate-prefix stages and places the transform at its onion position in one
step; the tail-`prepend_pass` of the (still-transparent) compress stage and the stage's
own `errorPageBraidStage_on` + `applyPage` fact finish it. -/
theorem braided2_errorpage_maps_404' (c : Ctx) (nv : Bytes × Bytes)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = some nv)
    (hmatch : Reactor.Stage.ErrorPage.hasPage ((runPipeline braidedChain appHandler c).build).status = true) :
    ((runPipeline braidedChain2 appHandler c).build).body
      = Reactor.Stage.ErrorPage.renderPage (Reactor.Stage.ErrorPage.pathOf c) := by
  rw [show braidedChain2 = [connBraidStage, stickBraidStage, slowBraidStage]
        ++ errorPageBraidStage :: compressBraidStage :: braidedChain from rfl,
      braid_transform [connBraidStage, stickBraidStage, slowBraidStage] errorPageBraidStage
        (compressBraidStage :: braidedChain) appHandler c c
        (cons_transparent (connBraidStage_off c hconn)
          (cons_transparent (stickBraidStage_off c hstick)
            (cons_transparent (slowBraidStage_off c hslow) (nil_transparent c)))) rfl,
      errorPageBraidStage_on c _ nv hfind, Reactor.Pipeline.build_mapResp,
      prepend_pass compressBraidStage braidedChain appHandler c (compressBraidStage_off c hcomp)]
  simp only [Reactor.Stage.ErrorPage.applyPage, hmatch, if_true]

/-! ## (3) `braided_off_eq_extend` — the off-composition family, re-derived -/

/-- `braided2_off_eq` re-derived via `braided_off_eq_extend`: peel the five transparent
head stages, then defer to the smaller `braided_off_eq` (§8's proven off-equality). -/
theorem braided2_off_eq' (c : Ctx)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = none) :
    runPipeline braidedChain2 appHandler c = runPipeline deployStagesFull2 appHandler c :=
  braided_off_eq_extend
    [connBraidStage, stickBraidStage, slowBraidStage, errorPageBraidStage, compressBraidStage]
    braidedChain deployStagesFull2 appHandler c
    (cons_transparent (connBraidStage_off c hconn)
      (cons_transparent (stickBraidStage_off c hstick)
        (cons_transparent (slowBraidStage_off c hslow)
          (cons_transparent (errorPageBraidStage_off c herr)
            (cons_transparent (compressBraidStage_off c hcomp) (nil_transparent c))))))
    (braided_off_eq c hfa hrid)

/-! ## Axiom audit of the re-derivations (should match the bespoke: propext + Quot.sound) -/

#print axioms braided2_conn_denies_status'
#print axioms braided2_stick_denies_status'
#print axioms braided2_errorpage_maps_404'
#print axioms braided2_off_eq'

end Reactor.BraidCalculusDemo
