import Datapath.HdrSeq
import Reactor.Stage.Redirect

/-!
# Datapath.StagePoly_redirect — the deployed `redirect` GATE response written ONCE
over `[HdrSeq H]`, its refinement FROM the op laws, grounded in the REAL deployed
`Reactor.Stage.Redirect.redirectStage` (row `redirect`, position 5 of the deploy
chain in `Reactor.Deploy`).

The header-grain sibling of `Datapath.HdrSeqProto`'s `securityStagePoly` /
`corsStagePoly`, at the GATE shape. Unlike a header-transform stage (which folds a
header set onto the passing-through block), the `redirect` gate short-circuits with
a FRESH 3xx response whose header block is the single `Location` header the REAL
`Redirect.redirect` library renders (status 308 + `Location` template render, RFC
9110 §15.4/§15.4). So the polymorphic form is a single `push` onto `empty`:

* `redirectStagePoly` — the redirect gate's response header block, written ONCE over
  `[HdrSeq H]`: `push empty (Location, rendered-target)`.
* `redirectStagePoly_refines` — the whole-stage refinement, a `simp`/`rw` over the op
  laws (`push_denote`, `empty_denote`) — no per-stage induction, no re-spec.
* `redirectStagePoly_eq_deployed` — GROUNDED in the REAL deployed stage: the poly form
  at the spec instance is byte-identical to `(redirectFor req).headers`, the header
  block the deployed `redirectStage` emits (read off `redirectFor` / `toResponse`,
  NOT re-specified).

Instantiated at `List (Bytes × Bytes)` (spec) and `HdrBlock` (fast, genuinely flat —
`push = Array.push`, no cons cell).
-/

namespace Datapath.StagePoly_redirect

open Proto (Bytes Request)
open Reactor (Response)
open Datapath.HdrSeq (HdrSeq foldPush)
open Datapath.FlatHeaders (HdrBlock)
open Reactor.Stage.Redirect
  (redirectStage redirectFor toResponse ruleCode ruleTemplate ruleTarget
   locationName decodeTarget)

/-! ## The rendered `Location` header — read off the REAL `Redirect.redirect` -/

/-- The single `(Location, rendered-target)` header pair the deployed `redirect`
gate emits: the REAL `Redirect.redirect` (status + `Location` template render, RFC
9110 §15.4) run against the configured code/template and the request's own decoded
target, its rendered `location` as the header value. Read off the deployed
`redirectFor` / `toResponse`, not re-specified. -/
def locationHeader (req : Request) : Bytes × Bytes :=
  (locationName,
    (_root_.Redirect.redirect ruleCode ruleTemplate (decodeTarget req.target) "").location.toUTF8.toList)

/-! ## The redirect gate response header block, written ONCE over `[HdrSeq H]` -/

/-- **The `redirect` gate response, written ONCE over `[HdrSeq H]`.** The gate emits
a fresh 3xx response whose header block is the single `Location` header — polymorphic
form: `push` the `Location` pair onto the `empty` block. -/
def redirectStagePoly {H : Type} [HdrSeq H] (req : Request) : H :=
  HdrSeq.push HdrSeq.empty (locationHeader req)

/-- The stage at the spec instance is exactly the singleton `Location` header list —
the `List` normal form (`push@List = · ++ [·]`, `empty@List = []`). No separate spec
expression is written; this is `redirectStagePoly` at `H := List _`. -/
theorem redirectStagePoly_list (req : Request) :
    redirectStagePoly (H := List (Bytes × Bytes)) req = [locationHeader req] := rfl

/-- **The whole-stage refinement — FOLLOWS from the op laws.** The dense stage's
denotation equals the stage run at the spec instance on the denoted input. Proven
polymorphically in `H`; discharged by `simp` over `push_denote` + `empty_denote` (each
`@[simp]`) — one `simp`, no per-stage induction. -/
theorem redirectStagePoly_refines {H : Type} [HdrSeq H] (req : Request) :
    HdrSeq.toHdrs (redirectStagePoly (H := H) req)
      = redirectStagePoly (H := List (Bytes × Bytes)) req := by
  rw [redirectStagePoly, redirectStagePoly_list]
  simp only [HdrSeq.push_denote, HdrSeq.empty_denote, List.nil_append]

/-- The refinement at the fast `HdrBlock` instance — a DIRECT instance of the
once-proven polymorphic theorem, no `HdrBlock`-specific reasoning. -/
theorem redirectStageBlock_refines (req : Request) :
    HdrBlock.denote (redirectStagePoly (H := HdrBlock) req)
      = redirectStagePoly (H := List (Bytes × Bytes)) req :=
  redirectStagePoly_refines (H := HdrBlock) req

/-- **Grounded in the REAL deployed stage (non-vacuous).** The poly stage at the spec
instance computes exactly the header block the deployed `redirectStage` emits — the
single `Location` header `redirectFor` / `toResponse` build, run by the REAL
`Redirect.redirect`. Grounded on `redirectFor`, not re-specified. -/
theorem redirectStagePoly_eq_deployed (req : Request) :
    redirectStagePoly (H := List (Bytes × Bytes)) req = (redirectFor req).headers := by
  rw [redirectStagePoly_list]
  rfl

/-! ## Non-vacuity — the poly form genuinely computes the REAL deployed effect at
BOTH instances, witnessed on real inputs (kernel-evaluated). -/

-- Spec instance: the poly header block IS the deployed `redirectFor` header block.
#guard (redirectStagePoly (H := List (Bytes × Bytes)) { target := ruleTarget })
        == (redirectFor { target := ruleTarget }).headers

-- Fast `HdrBlock` instance: the flat (Array.push, no cons) block denotes to the same
-- deployed `redirectFor` header block.
#guard (redirectStagePoly (H := HdrBlock) { target := ruleTarget }).denote
        == (redirectFor { target := ruleTarget }).headers

-- Spec instance and flat instance agree on a concrete input (the refinement, run).
#guard (redirectStagePoly (H := HdrBlock) { target := ruleTarget }).denote
        == redirectStagePoly (H := List (Bytes × Bytes)) { target := ruleTarget }

-- The poly form carries exactly one header, and it is the `Location` header.
#guard (redirectStagePoly (H := List (Bytes × Bytes)) { target := ruleTarget }).map (·.1)
        == [locationName]

-- The poly op genuinely depends on the request target: different targets render
-- different `Location` bytes, hence different header blocks (not a constant).
#guard (redirectStagePoly (H := List (Bytes × Bytes)) { target := "/a".toUTF8.toList })
        != (redirectStagePoly (H := List (Bytes × Bytes)) { target := "/bb".toUTF8.toList })

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms redirectStagePoly_refines
#print axioms redirectStageBlock_refines
#print axioms redirectStagePoly_eq_deployed

end Datapath.StagePoly_redirect
