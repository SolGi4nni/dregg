import Datapath.Refine
import Datapath.ByteRefine
import Reactor.Deploy

/-!
# Datapath.FlatStage_policy — the deployed `policy` GATE stage, flat and
byte-identical to its `List`-typed deployed form.

The representative header-transform stage is done in `Datapath.FlatStage`
(`securityheaders`). This module does one of the GATE stages of
`Reactor.Deploy.deployStages`: **`policyStage`** (the ACL admission gate). A gate
is structurally different from a header-transform stage — its whole effect is in
the REQUEST phase (`onResponse` is the identity on the affine builder), so there
is no header-block fold to flatten. What a gate contributes is:

* a **DECISION on the request** — `policyStage` short-circuits exactly when the
  REAL `Reactor.Deploy.policyReserved` holds (an undeclared surface that is also a
  reserved dotfile namespace), decided by the REAL `Policy.serveDecision` via
  `deployDecisionOf`; and
* a **fixed refusal RESPONSE** — the serializer-built `Reactor.Deploy.forbidden403`
  (`403`, body `"policy: undeclared surface\n"`), whose wire bytes replace the
  handler's.

Both are read off `Reactor/Deploy.lean` (grounded, NOT re-specified): the decision
is `Reactor.Deploy.policyStage.onRequest` (`policyStage_onRequest`), the response
is `Reactor.Deploy.forbidden403`.

## What is proven here (equality-transfer, NOT a re-spec)

* `policyStage_onRequest` — the DEPLOYED gate's request phase, read off the real
  `policyStage`: refuse (`.respond forbidden403`) iff the REAL `policyReserved`
  holds, else `.continue`. This is the function the flat gate must compute.
* `flatPolicyStep` / `flatPolicyStep_refines` — the flat gate reads the request out
  of the borrowed span BY INDEX (`Datapath.spanParseRequest`, zero-copy, no request
  cons-list) and runs the SAME `policyStage` decision. `flatPolicyStep_refines`
  proves it takes byte-for-byte the same `StageStep` as the deployed gate on the
  request the DEPLOYED cons-list parser (`h1ParseFn`) produces on the span's
  denotation. Non-vacuous: the flat side reads by index, the deployed side consumes
  `denote`; equal only via `SpanBytes.read_eq_denote` (inside
  `spanParseRequest_refines`).
* `flatPolicyStep_fires` / `flatPolicyStep_passes` — the flat gate genuinely
  branches: a parsed request the REAL `policyReserved` rejects short-circuits with
  exactly `forbidden403`; one it accepts passes through.
* `flatRefuse_serialize_refines` — the refusal bytes the flat gate emits
  (`flatSerialize forbidden403`, the DERIVED flat serializer) are byte-identical to
  `Reactor.serialize forbidden403` — the exact wire bytes the deployed gate's
  `.respond forbidden403` short-circuit produces. A direct instance of
  `Datapath.Refinement.flatSerialize_refines` at the deployed refusal response.
* `flatPolicy_refuses_byte_identical` — the two joined: a span parsing to a
  policy-refused request fires the flat gate to `forbidden403` AND the emitted 403
  bytes are byte-identical to the deployed serialize.

## What genuinely does NOT flatten here (honest residual)

The decision predicate `policyReserved` calls `deployDecisionOf`, whose route
extraction (`Reactor.App.targetSegments`) uses `String.splitOn`. `splitOn` does not
reduce in the kernel (it is the same boundary the deployed `Deploy.lean` #guards
avoid by working on explicit segment lists). So the FULL `flatPolicyStep = .respond
forbidden403` cannot be a kernel `#guard` on a concrete span — it is proven as a
theorem (`flatPolicyStep_fires`, hypothesis-driven exactly as `Deploy.lean`'s
`guardOne_refuses`). What IS kernel-evaluated below (non-vacuity): the refusal bytes
byte-identity, the reserved-namespace component (`isDotfileTarget`) of the real
decision, and that the flat gate recovers the request off the span by index. This
is the same split `Deploy.lean` itself uses (segment-level `#guard`, request-level
theorem).
-/

namespace Datapath.FlatStage_policy

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx StageStep)
open Reactor.Deploy (policyStage policyReserved forbidden403 isDotfileTarget)
open Datapath (SpanBytes spanParseRequest outcomeRequest? spanParseRequest_refines)
open Datapath.Refinement (flatSerialize flatSerialize_refines)

/-! ## 1. The deployed gate decision, read off the REAL stage -/

/-- **The deployed `policy` gate's request phase — grounded, not re-specified.**
For any context, `Reactor.Deploy.policyStage.onRequest` refuses with
`forbidden403` exactly when the REAL `policyReserved` holds (`deployDecisionOf`
undeclared AND a reserved dotfile namespace), else passes the context through. This
is the function the flat gate must compute. `rfl` — it IS the stage's definition. -/
theorem policyStage_onRequest (c : Ctx) :
    policyStage.onRequest c
      = cond (policyReserved c.req) (.respond forbidden403) (.continue c) := rfl

/-! ## 2. The flat gate and its decision refinement (request grain) -/

/-- The `Ctx` the gate decides over, built from a parsed request: the raw denoted
bytes as `input` (what the deployed `ctxOf` threads to the downstream response
transform) and the request the gate reads. The gate consumes only `.req`. -/
def ctxOfReq (s : SpanBytes) (req : Proto.Request) : Ctx :=
  { input := s.denote, req := req }

/-- **The flat `policy` gate.** Reads the request out of the borrowed span BY INDEX
(`spanParseRequest` — zero-copy, no per-byte request cons-list), then runs the REAL
deployed `policyStage` request-phase decision on it. A genuinely policy-refused
surface short-circuits with `forbidden403`; every other surface passes. -/
def flatPolicyStep (s : SpanBytes) : StageStep :=
  match spanParseRequest s with
  | some (_, req, _) => policyStage.onRequest (ctxOfReq s req)
  | none             => policyStage.onRequest (ctxOfReq s {})

/-- The deployed reference: the SAME `policyStage` decision, but on the request the
DEPLOYED cons-list parser (`h1ParseFn`) produces on the span's denotation. -/
def deployPolicyStep (s : SpanBytes) : StageStep :=
  match outcomeRequest? (Reactor.Config.h1ParseFn s.denote) with
  | some (_, req, _) => policyStage.onRequest (ctxOfReq s req)
  | none             => policyStage.onRequest (ctxOfReq s {})

/-- **The flat gate refines the deployed gate's decision.** On any well-formed span,
`flatPolicyStep` — reading the request by index off the borrowed window — takes the
byte-for-byte SAME `StageStep` as the deployed `policyStage` on the request the
deployed cons-list parser produces on the span's denotation. Proven by transferring
`spanParseRequest_refines` (the request-parse refinement) under the shared
`policyStage.onRequest` decision. Non-vacuous: the flat side reads by index, the
deployed side consumes `denote`; the two `StageStep`s agree only because
`spanParseRequest s = outcomeRequest? (h1ParseFn s.denote)`. -/
theorem flatPolicyStep_refines (s : SpanBytes) (h : s.Wf) :
    flatPolicyStep s = deployPolicyStep s := by
  unfold flatPolicyStep deployPolicyStep
  rw [spanParseRequest_refines s h]

/-- **The flat gate fires on a policy-refused request.** When the span parses to a
request the REAL `policyReserved` rejects, the flat gate short-circuits with exactly
the deployed `forbidden403` — the SAME `.respond` the deployed `policyStage` takes.
Hypothesis-driven exactly as `Deploy.lean`'s `guardOne_refuses` (the decision runs
through `deployDecisionOf`/`splitOn`, kernel-opaque; the branch fact is supplied). -/
theorem flatPolicyStep_fires (s : SpanBytes) (req : Proto.Request) (n : Nat) (ka : Bool)
    (hp : spanParseRequest s = some (n, req, ka)) (hr : policyReserved req = true) :
    flatPolicyStep s = .respond forbidden403 := by
  simp only [flatPolicyStep, hp, policyStage_onRequest, ctxOfReq, hr, cond_true]

/-- **The flat gate passes an admitted / merely-unknown-but-safe request.** When the
span parses to a request the REAL `policyReserved` accepts, the flat gate
`.continue`s unchanged — the handler and later stages still run. -/
theorem flatPolicyStep_passes (s : SpanBytes) (req : Proto.Request) (n : Nat) (ka : Bool)
    (hp : spanParseRequest s = some (n, req, ka)) (hr : policyReserved req = false) :
    flatPolicyStep s = .continue (ctxOfReq s req) := by
  simp only [flatPolicyStep, hp, policyStage_onRequest, ctxOfReq, hr, cond_false]

/-! ## 3. Byte-identical: the flat refusal response = the deployed refusal response -/

/-- The refusal bytes the flat gate emits: the DERIVED flat serialization
(`flatSerialize`, `foldAppend` fold, no per-join cons-spine) of the REAL deployed
refusal response `forbidden403`. -/
def flatRefuseBytes : ByteArray := flatSerialize forbidden403

/-- **Byte-identity of the refusal response.** The flat gate's emitted 403 bytes are
byte-identical to `Reactor.serialize forbidden403` — the exact wire bytes the
deployed `policyStage`'s `.respond forbidden403` short-circuit produces. A direct
instance of `flatSerialize_refines` at the deployed refusal response; the flat fold
genuinely computes the bytes, not `serialize`. -/
theorem flatRefuse_serialize_refines :
    Datapath.Refinement.Refines (Reactor.serialize forbidden403) flatRefuseBytes :=
  flatSerialize_refines forbidden403

/-- **THE GATE FIRES + THE BYTES ARE BYTE-IDENTICAL.** A borrowed span parsing to a
genuinely policy-refused request: (a) the flat gate short-circuits with exactly the
deployed `forbidden403` (`flatPolicyStep_fires`), and (b) the flat 403 bytes it
emits are byte-identical to `Reactor.serialize forbidden403` (the deployed refusal
wire bytes). Decision and response, both grounded in the REAL `policyStage`. -/
theorem flatPolicy_refuses_byte_identical (s : SpanBytes) (req : Proto.Request)
    (n : Nat) (ka : Bool)
    (hp : spanParseRequest s = some (n, req, ka)) (hr : policyReserved req = true) :
    flatPolicyStep s = .respond forbidden403
    ∧ Datapath.Refinement.Refines (Reactor.serialize forbidden403) flatRefuseBytes :=
  ⟨flatPolicyStep_fires s req n ka hp hr, flatRefuse_serialize_refines⟩

/-! ## Non-vacuity — kernel-evaluated on real inputs -/

/-- `"GET /.git/config HTTP/1.1\r\n\r\n"` — a reserved dotfile surface. -/
def gitBytes : ByteArray := "GET /.git/config HTTP/1.1\r\n\r\n".toUTF8
/-- The whole-buffer span over the dotfile request. -/
def gitSpan : SpanBytes := SpanBytes.full gitBytes

/-- `"GET /health HTTP/1.1\r\n\r\n"` — a declared, admitted surface. -/
def healthBytes : ByteArray := "GET /health HTTP/1.1\r\n\r\n".toUTF8
def healthSpan : SpanBytes := SpanBytes.full healthBytes

-- **The flat form computes the REAL deployed gate effect (the refusal bytes),
-- kernel-evaluated.** The flat serialization of the deployed `forbidden403` is
-- byte-identical to `Reactor.serialize forbidden403`.
#guard (flatSerialize forbidden403).data.toList == Reactor.serialize forbidden403

-- The reserved-namespace component of the REAL decision (`isDotfileTarget`, a
-- conjunct of `policyReserved`) genuinely depends on the target — fires on `/.git`,
-- quiet on `/health`.
#guard isDotfileTarget "/.git/config".toUTF8.toList == true
#guard isDotfileTarget "/health".toUTF8.toList == false

-- The flat gate reads the request off the borrowed span BY INDEX and recovers a
-- target the REAL reserved-namespace test flags (the dotfile span) — and does NOT
-- flag the health span. Genuine dependence of the gate input on the span bytes.
def spanTargetIsDotfile (s : SpanBytes) : Bool :=
  match spanParseRequest s with
  | some (_, req, _) => isDotfileTarget req.target
  | none => false

#guard spanTargetIsDotfile gitSpan == true
#guard spanTargetIsDotfile healthSpan == false

-- The span genuinely parses (the gate has a real request to decide on).
#guard (spanParseRequest gitSpan).isSome == true

/-! ## Axiom audit -/

#print axioms flatPolicyStep_refines
#print axioms flatPolicyStep_fires
#print axioms flatPolicyStep_passes
#print axioms flatRefuse_serialize_refines
#print axioms flatPolicy_refuses_byte_identical

end Datapath.FlatStage_policy
