import Datapath.HdrSeq
import Reactor.Stage.BasicAuth

/-!
# Datapath.StagePoly_basicauth — the `basicauth` GATE stage's `401` response header
block written ONCE over `[HdrSeq H]`, and the load-bearing test: does its
refinement FOLLOW from the op laws?

This is the GATE-grain sibling of the header-transform stages in
`Datapath.HdrSeqProto` (`securityStagePoly` / `corsStagePoly` / `hrwStagePoly`).
Those stages run on the RESPONSE phase and transform an existing header block.
`Reactor.Stage.BasicAuth.basicStage` is different in KIND: it is a `/private`-scoped
REQUEST-phase gate that either passes (`.continue`) or SHORT-CIRCUITS the whole
pipeline with a canned `401 Unauthorized` carrying the RFC 7617
`WWW-Authenticate: Basic realm="…"` challenge (`.respond (basicUnauthorized www)`).

The byte grain the polymorphic representation touches here is that `401`'s
**header block** — a single `(WWW-Authenticate, www)` pair, where `www` is the
real challenge string the `BasicAuth.authenticate` machine produced. Written over
`[HdrSeq H]` it is one `foldPush` of that singleton set onto the empty block, so:

* `basicAuthPoly` — the `401` header block, ONE polymorphic expression over
  `[HdrSeq H]` (`foldPush [(wwwAuthName, strBytes www)] empty`).
* `basicAuthPoly_refines` — the whole-stage refinement, a 1-line `simp` over the
  op laws (`foldPush_denote` ⇐ `push_denote`, `empty_denote`). No induction, no
  re-expression of the stage.
* `basicAuthPoly_eq_deployed` — GROUNDED in the REAL deployed stage: at the spec
  instance the poly block IS `(basicUnauthorized www).headers`, the header list
  the deployed `basicStage`'s `.respond` short-circuit builds (read off the actual
  `basicUnauthorized`, not re-specified). Instantiates at `List` (spec) and
  `HdrBlock` (fast, genuinely flat).

## The residual (named, not hidden)

The `WWW-Authenticate` VALUE (`www`) is an external `String` parameter — the gate
computes it by running `BasicAuth.authenticate` (parse the `Basic` scheme,
**base64-decode** the credential, split on the colon, `verify`). The base64 decode
(`b64Decode` / `emitStep`) is a bit-buffer fold whose per-character `String`
boundary is opaque to the kernel on a general credential; it is NOT part of the
header-block algebra and does not go through `HdrSeq`. This file polys the RESPONSE
header block (byte-identical at both instances); the b64 loop stays where the
deployed stage runs it, as the byte-effect theorems in `Reactor.Stage.BasicAuth`
already establish (the credential-less `/private` witness `privateNoAuth_challenges`
grounds `www = challengeHeader stageConfig` by `rfl` through the real machine).
-/

namespace Datapath.StagePoly_basicauth

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Reactor (Response)
open Reactor.Stage.BasicAuth
  (basicUnauthorized wwwAuthName strBytes stageConfig)

/-! ## The polymorphic `401` header block -/

/-- **The `basicauth` gate's `401` response header block, written ONCE over
`[HdrSeq H]`.** Fold the singleton challenge-header set `(WWW-Authenticate, www)`
onto the empty block with `push`. `www` is the challenge string the real
`BasicAuth.authenticate` produced (an external parameter; see the b64 residual in
the module doc). -/
def basicAuthPoly {H : Type} [HdrSeq H] (www : String) : H :=
  foldPush [(wwwAuthName, strBytes www)] HdrSeq.empty

/-- The stage at the **spec** instance is exactly `[(wwwAuthName, strBytes www)]`
— the `List (Bytes × Bytes)` normal form (`foldPush@List xs [] = [] ++ xs`,
`empty@List = []`). No separate spec expression is written; this is `basicAuthPoly`
at `H := List _`. -/
theorem basicAuthPoly_list (www : String) :
    basicAuthPoly (H := List (Bytes × Bytes)) www = [(wwwAuthName, strBytes www)] := by
  show foldPush [(wwwAuthName, strBytes www)] ([] : List (Bytes × Bytes)) = _
  rw [foldPush_list, List.nil_append]

/-! ## ★ THE LOAD-BEARING THEOREM — the whole-stage refinement, proven ONCE -/

/-- **The whole-stage refinement — FOLLOWS from the op laws.** The dense `401`
header block's denotation equals the block built at the spec instance. Proven
polymorphically in `H`; discharged by `simp` over `foldPush_denote` (⇐ `push_denote`)
and `empty_denote` — one line, no per-stage induction, no re-expression. -/
theorem basicAuthPoly_refines {H : Type} [HdrSeq H] (www : String) :
    HdrSeq.toHdrs (basicAuthPoly (H := H) www)
      = basicAuthPoly (H := List (Bytes × Bytes)) www := by
  rw [basicAuthPoly_list, basicAuthPoly]
  simp only [foldPush_denote, HdrSeq.empty_denote, List.nil_append]

/-- The refinement at the fast `HdrBlock` instance — a DIRECT instance of the
once-proven polymorphic theorem, no `HdrBlock`-specific reasoning. -/
theorem basicAuthBlock_refines (www : String) :
    HdrBlock.denote (basicAuthPoly (H := HdrBlock) www)
      = basicAuthPoly (H := List (Bytes × Bytes)) www :=
  basicAuthPoly_refines (H := HdrBlock) www

/-! ## Grounding in the REAL deployed gate (non-vacuity, not a re-spec) -/

/-- **Grounded in the REAL deployed stage (non-vacuous).** The poly block at the
spec instance computes exactly the header list the deployed `basicStage`'s
`.respond` short-circuit builds — `(basicUnauthorized www).headers`, read off the
actual canned `401` (`[(wwwAuthName, strBytes www)]`), not re-specified. -/
theorem basicAuthPoly_eq_deployed (www : String) :
    basicAuthPoly (H := List (Bytes × Bytes)) www
      = (basicUnauthorized www).headers := by
  rw [basicAuthPoly_list]; rfl

/-! ## Non-vacuity — the flat block genuinely computes the deployed challenge header

The concrete challenge string is the one the REAL machine emits for a
credential-less `/private` request (`challengeHeader stageConfig`, the value
`privateNoAuth_challenges` grounds by `rfl` through `BasicAuth.authenticate`). -/

/-- The realm challenge string the deployed gate emits for the demonstration config
(`Basic realm="orb"`, via the real `BasicAuth.challengeHeader`). -/
def realWww : String := BasicAuth.challengeHeader stageConfig

-- The flat `HdrBlock` `401` block computes the deployed header list — kernel-evaluated.
#guard (basicAuthPoly (H := HdrBlock) realWww).denote == (basicUnauthorized realWww).headers

-- The spec instance also lands the deployed header list.
#guard basicAuthPoly (H := List (Bytes × Bytes)) realWww == (basicUnauthorized realWww).headers

-- Spec instance and flat instance agree on the concrete challenge (the refinement, run).
#guard (basicAuthPoly (H := HdrBlock) realWww).denote
        == basicAuthPoly (H := List (Bytes × Bytes)) realWww

-- The block genuinely carries the WWW-Authenticate name and the realm challenge value.
#guard (basicAuthPoly (H := HdrBlock) realWww).denote
        == [("WWW-Authenticate".toUTF8.toList, "Basic realm=\"orb\"".toUTF8.toList)]

-- The block genuinely depends on the challenge string: different realms ⇒ different bytes.
#guard (basicAuthPoly (H := HdrBlock) "Basic realm=\"a\"").denote
        != (basicAuthPoly (H := HdrBlock) "Basic realm=\"b\"").denote

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms basicAuthPoly_refines
#print axioms basicAuthBlock_refines
#print axioms basicAuthPoly_eq_deployed

end Datapath.StagePoly_basicauth
