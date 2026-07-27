import Datapath.HdrSeq
import Datapath.ByteSeq
import Reactor.Deploy

/-!
# Datapath.StagePoly_jwt — the deployed `jwt-admin` GATE's 401 response, written
POLYMORPHICALLY over BOTH `[HdrSeq H]` (header block) and `[ByteSeq T]` (body).

This is the GATE-grain sibling of `Datapath.HdrSeqProto` (header stages) and
`Datapath.ByteSeqProto` (body stage). A gate is not an `onResponse` transform: the
deployed `Reactor.Deploy.jwtAdminStage` runs the REAL `Jwt.authenticate` FSM on the
REQUEST phase and, on any rejection, SHORT-CIRCUITS with a canned `401` —
`Reactor.Stage.Jwt.unauthorized`. The data-heavy part of the gate is that `401`
RESPONSE CONSTRUCTION: its header block (`WWW-Authenticate: Bearer`) and its body
(`invalid or missing bearer token`). The HMAC/FSM DECISION itself (`Jwt.authenticate`,
whose crypto boundary is `verifyHmac`) is a NAMED RESIDUAL — this file polys the
RESPONSE the gate emits, and grounds it in the REAL deployed gate firing.

## The one polymorphic expression

`jwtGatePoly` builds the `401` as a `PolyResp H T` — a response record whose header
block is an abstract `[HdrSeq H]` and whose body is an abstract `[ByteSeq T]`:

* headers = `foldPush [(WWW-Authenticate, Bearer)] empty` — the ONE header pushed
  with the header-grain `push` op (reusing `HdrSeq.foldPush` / `foldPush_denote`).
* body = `foldCat (unauthorizedBody.map singleton)` — the fixed diagnostic bytes
  built flat from `ByteSeq.singleton` + `append` (reusing `ByteSeq.foldCat` /
  `foldCat_denote`, the single generic recursion lemma).

## The load-bearing test (same as the siblings)

`jwtGatePoly_refines` proves — ONCE, polymorphically in `H` and `T` — that the
denoted response equals the deployed `Reactor.Stage.Jwt.unauthorized`. Its proof is
a `simp` over the op laws (`foldPush_denote`, `bodyPoly_denote ⇐ foldCat_denote`) —
NO per-stage induction, NO re-spec of the `401`. Instantiated at `List` (spec) and
`HdrBlock`/`ByteArray` (fast, genuinely flat), the SAME theorem gives the flat 401.

`jwtGatePoly_eq_deployed` then grounds it in the REAL gate: on an `/admin` target
with a rejecting `Jwt.authenticate`, `Reactor.Deploy.jwtAdminStage.onRequest`
short-circuits with EXACTLY the poly-constructed `401` — not a re-spec, the deployed
`jwtAdminStage` firing off the genuine FSM.
-/

namespace Datapath.StagePoly_jwt

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.ByteSeq
open Datapath.FlatHeaders (HdrBlock)
open Reactor (Response)
open Reactor.Pipeline (Ctx StageStep)
open Reactor.Stage.Jwt
  (unauthorized unauthorizedReason unauthorizedBody wwwAuthName wwwAuthVal decision jwtStage
   jwtStage_gates_on_reject)

/-! ## A polymorphic response record — header block over `H`, body over `T` -/

/-- A response whose header block is an abstract `[HdrSeq H]` value and whose body
is an abstract `[ByteSeq T]` value. `denote` maps it to the deployed
`Reactor.Response` by denoting both. -/
structure PolyResp (H T : Type) where
  status  : Nat
  reason  : Bytes
  headers : H
  body    : T

/-- The abstraction relation to the deployed `Reactor.Response`: denote the header
block (`HdrSeq.toHdrs`) and the body (`ByteSeq.toBytes`). Never run on the datapath;
it is the spec side of the refinement. -/
def PolyResp.denote {H T : Type} [HdrSeq H] [ByteSeq T] (p : PolyResp H T) : Response :=
  { status  := p.status
    reason  := p.reason
    headers := HdrSeq.toHdrs p.headers
    body    := ByteSeq.toBytes p.body }

/-! ## The body helper — the fixed `401` body built flat, denoting to the real bytes -/

/-- Flattening a list of one-element lists is the identity — the single induction
the singleton-fold body construction needs. -/
private theorem flatten_map_singleton (l : List UInt8) :
    (l.map (fun b => [b])).flatten = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- **The body op-law bridge.** The fixed diagnostic body, built flat from
`ByteSeq.singleton` + `append` (a `foldCat` over the byte list), denotes to exactly
the deployed `unauthorizedBody`. Proven ONCE, generic in `T`, from `foldCat_denote`
(⇐ `append_denote`) + `singleton_denote` — no per-instance work. -/
theorem bodyPoly_denote {T : Type} [ByteSeq T] :
    ByteSeq.toBytes (foldCat (unauthorizedBody.map (ByteSeq.singleton (T := T)))) = unauthorizedBody := by
  rw [foldCat_denote, List.map_map]
  have hcomp : (ByteSeq.toBytes ∘ (ByteSeq.singleton (T := T))) = (fun b : UInt8 => [b]) := by
    funext b; exact ByteSeq.singleton_denote b
  rw [hcomp, flatten_map_singleton]

/-! ## The polymorphic gate response -/

/-- **The `jwt-admin` gate's `401`, written ONCE over `[HdrSeq H]` + `[ByteSeq T]`.**
Push the single `WWW-Authenticate: Bearer` challenge onto an empty header block, and
build the fixed diagnostic body flat from `singleton`/`append`. The DECISION
(`Jwt.authenticate`, the HMAC/FSM) is a named residual; this is the RESPONSE the
gate emits on rejection. -/
def jwtGatePoly (H T : Type) [HdrSeq H] [ByteSeq T] : PolyResp H T :=
  { status  := 401
    reason  := unauthorizedReason
    headers := foldPush [(wwwAuthName, wwwAuthVal)] HdrSeq.empty
    body    := foldCat (unauthorizedBody.map ByteSeq.singleton) }

/-! ## ★ THE LOAD-BEARING THEOREM — the whole-response refinement, proven ONCE -/

/-- **The whole-response refinement — FOLLOWS from the op laws.** For ANY
`[HdrSeq H]` + `[ByteSeq T]`, the denoted poly response equals the deployed
`Reactor.Stage.Jwt.unauthorized`. Discharged by `simp` over `foldPush_denote` (the
header op law) + `bodyPoly_denote` (⇐ `foldCat_denote`, the body op law) — NO
per-stage induction, NO re-spec of the `401`. Instantiating at `List`/`HdrBlock`/
`ByteArray` gives the spec and the two flat 401s from this ONE proof. -/
theorem jwtGatePoly_refines (H T : Type) [HdrSeq H] [ByteSeq T] :
    (jwtGatePoly H T).denote = unauthorized := by
  simp only [jwtGatePoly, PolyResp.denote, unauthorized, foldPush_denote,
    HdrSeq.empty_denote, List.nil_append, bodyPoly_denote]

/-- The refinement at the fast `HdrBlock`/`ByteArray` instance — a DIRECT instance
of the once-proven polymorphic theorem, no flat-specific reasoning: the genuinely
flat `401` (header spine in an `Array`, body in a `ByteArray`) denotes to the exact
deployed `unauthorized` bytes. -/
theorem jwtGateFlat_refines :
    (jwtGatePoly HdrBlock ByteArray).denote = unauthorized :=
  jwtGatePoly_refines HdrBlock ByteArray

/-! ## Grounding in the REAL deployed `jwtAdminStage` (non-vacuity, not a re-spec) -/

/-- **Grounded in the REAL deployed gate.** On an `/admin` target whose REAL
`Jwt.authenticate` decision rejects, the deployed `Reactor.Deploy.jwtAdminStage`
REQUEST phase short-circuits with EXACTLY the poly-constructed `401` (at the spec
instance). Read off the actual `jwtAdminStage` (`isAdminPath` branch →
`jwtStage.onRequest`), grounded on `jwtStage_gates_on_reject`, not re-specified. -/
theorem jwtGatePoly_eq_deployed (c : Ctx) (r : Jwt.Reason)
    (hadmin : Reactor.Deploy.isAdminPath c.req = true)
    (hrej : decision c = Jwt.Outcome.reject r) :
    Reactor.Deploy.jwtAdminStage.onRequest c
      = StageStep.respond ((jwtGatePoly (List (Bytes × Bytes)) (List UInt8)).denote) := by
  have hgate : Reactor.Deploy.jwtAdminStage.onRequest c = StageStep.respond unauthorized := by
    show (if Reactor.Deploy.isAdminPath c.req then jwtStage.onRequest c
          else StageStep.continue c) = _
    rw [if_pos hadmin]
    exact jwtStage_gates_on_reject c r hrej
  rw [hgate, ← jwtGatePoly_refines (List (Bytes × Bytes)) (List UInt8)]

/-- **The witnessed deployed gate.** For the concrete credential-less `GET /admin`
request (`Reactor.Deploy.adminNoAuthCtx`), the deployed `jwtAdminStage` short-circuits
with the poly-constructed `401` — the gate firing off the genuine FSM
(`adminNoAuth_rejects` computes `Jwt.authenticate` to `reject .noToken` by `rfl`). -/
theorem jwtGatePoly_witness :
    Reactor.Deploy.jwtAdminStage.onRequest Reactor.Deploy.adminNoAuthCtx
      = StageStep.respond ((jwtGatePoly (List (Bytes × Bytes)) (List UInt8)).denote) :=
  jwtGatePoly_eq_deployed Reactor.Deploy.adminNoAuthCtx Jwt.Reason.noToken
    Reactor.Deploy.adminNoAuth_isAdmin Reactor.Deploy.adminNoAuth_rejects

/-! ## Non-vacuity — the flat gate genuinely computes the deployed `401` -/

-- The flat (`HdrBlock`/`ByteArray`) 401 denotes to the deployed `unauthorized`,
-- field by field — evaluated by the kernel, not just proven.
#guard (jwtGatePoly HdrBlock ByteArray).denote.status == 401
#guard (jwtGatePoly HdrBlock ByteArray).denote.reason == unauthorized.reason
#guard (jwtGatePoly HdrBlock ByteArray).denote.headers == unauthorized.headers
#guard (jwtGatePoly HdrBlock ByteArray).denote.body == unauthorized.body

-- The flat body is GENUINELY the diagnostic bytes (non-empty, the real string) —
-- the ByteSeq singleton/append fold actually computed content.
#guard (jwtGatePoly HdrBlock ByteArray).denote.body == "invalid or missing bearer token".toUTF8.toList
#guard (jwtGatePoly HdrBlock ByteArray).denote.body.length == 31

-- The flat header block is the real `WWW-Authenticate: Bearer` challenge.
#guard (jwtGatePoly HdrBlock ByteArray).denote.headers
        == [("WWW-Authenticate".toUTF8.toList, "Bearer".toUTF8.toList)]

-- Spec instance and flat instance agree (the refinement, evaluated at both).
#guard (jwtGatePoly HdrBlock ByteArray).denote.headers
        == (jwtGatePoly (List (Bytes × Bytes)) (List UInt8)).denote.headers
#guard (jwtGatePoly HdrBlock ByteArray).denote.body
        == (jwtGatePoly (List (Bytes × Bytes)) (List UInt8)).denote.body

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms bodyPoly_denote
#print axioms jwtGatePoly_refines
#print axioms jwtGateFlat_refines
#print axioms jwtGatePoly_eq_deployed
#print axioms jwtGatePoly_witness

end Datapath.StagePoly_jwt
