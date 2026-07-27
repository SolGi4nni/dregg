import Reactor.Stage.FramingValidation

/-!
# Reactor.Stage.ClTeGuard — the Content-Length + Transfer-Encoding conflict gate

RFC 7230 §3.3.3(3): a request that carries BOTH `Content-Length` and
`Transfer-Encoding` is the classic request-smuggling shape — an intermediary
that frames the body by `Content-Length` while the origin frames it by
`Transfer-Encoding` (or vice versa) desynchronizes the connection, and the
"smuggled" tail bytes are parsed as a second request. §3.3.3 directs that
`Transfer-Encoding` overrides `Content-Length`, and that such a message "ought
to be handled as an error"; rejecting it outright with `400` before ANY body
handling is the defensive posture every hardened edge takes.

The deployed framing gate (`Reactor.Stage.FramingValidation`, run inside the
conformance wrapper) rejects a `Transfer-Encoding` whose FINAL coding is not
`chunked` (L1), but a request with `Transfer-Encoding: chunked` AND a
`Content-Length` passed it: both framings declared at once, the conflict
undetected. This gate closes exactly that hole — the ledger's h1.5 "CL/TE
conflict" residual.

* `clTeGuardStage` — request-phase gate: both `Content-Length` and
  `Transfer-Encoding` present (either direction, case-insensitive names) ⇒
  `.respond` the `400`; otherwise pass through unchanged. Response phase
  transparent.

## What is proven (headline, non-vacuous on concrete witnesses)

* `clte_denies` / `clte_allows` — the gate fires exactly on the conflict.
* `clte_denies_status` — the `400` survives ANY status-stable inner onion.
* `clte_denies_skips_handler` — the handler never runs on a refused request.
* `clte_gate_discriminates` — same handler, conflict forced to `400`,
  conflict-free request served — the gate genuinely drives the wire.

Every guard fact is `by decide` on explicit ASCII byte lists (no
`native_decide`, pure kernel).
-/

namespace Reactor.Stage.ClTeGuard

open Reactor.Pipeline
open Proto (Bytes Request)
open Reactor.Stage.RequestValidation (badRequestResp)
open Reactor.Stage.FramingValidation (lowerBytes teNameLower)

/-- `content-length` (lowercase, explicit ASCII). -/
def clNameLower : Bytes :=
  [99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110, 103, 116, 104]

/-- The request declares a `Content-Length` (case-insensitive name). -/
def hasCl (req : Request) : Bool :=
  req.headers.any (fun kv => lowerBytes kv.1 == clNameLower)

/-- The request declares a `Transfer-Encoding` (case-insensitive name). -/
def hasTe (req : Request) : Bool :=
  req.headers.any (fun kv => lowerBytes kv.1 == teNameLower)

/-- **The conflict decision.** Both body framings declared at once
(RFC 7230 §3.3.3(3) — the smuggling shape). -/
def clTeConflict (req : Request) : Bool := hasCl req && hasTe req

/-- **The CL/TE-conflict gate.** Request phase: the conflict ⇒ `400 Bad Request`
(reusing the deployed validation library's response); anything else passes
through unchanged. Response phase transparent. -/
def clTeGuardStage : Stage where
  name := "cl-te-guard"
  onRequest := fun c =>
    if clTeConflict c.req then .respond badRequestResp else .continue c
  onResponse := fun _ b => b

/-- The gate's response phase is the identity — safe inside any onion. -/
theorem clTeGuardStage_statusStable : Stage.statusStable clTeGuardStage :=
  fun _ _ => rfl

/-! ## Gate behaviour -/

/-- A conflicted request is refused with the `400`. -/
theorem clte_denies (c : Ctx) (h : clTeConflict c.req = true) :
    clTeGuardStage.onRequest c = .respond badRequestResp := by
  show (if clTeConflict c.req then StageStep.respond badRequestResp
        else StageStep.continue c) = _
  rw [h]
  rfl

/-- A conflict-free request passes through UNCHANGED. -/
theorem clte_allows (c : Ctx) (h : clTeConflict c.req = false) :
    clTeGuardStage.onRequest c = .continue c := by
  show (if clTeConflict c.req then StageStep.respond badRequestResp
        else StageStep.continue c) = _
  rw [h]
  rfl

/-- **The `400` through the onion.** A conflicted request's status is `400`
after ANY status-stable inner stage list — the refusal reaches the wire. -/
theorem clte_denies_status (c : Ctx) (rest : List Stage)
    (handler : Ctx → Response) (h : clTeConflict c.req = true)
    (hst : ∀ s ∈ rest, Stage.statusStable s) :
    ((runPipeline (clTeGuardStage :: rest) handler c).build).status = 400 := by
  rw [pipeline_gate_short_circuits clTeGuardStage rest handler c badRequestResp
        (clte_denies c h),
      runResp_build_status rest c _ hst]
  rfl

/-- The handler NEVER runs on a refused request: the pipeline output is
handler-independent. -/
theorem clte_denies_skips_handler (c : Ctx) (rest : List Stage)
    (handler handler' : Ctx → Response) (h : clTeConflict c.req = true) :
    runPipeline (clTeGuardStage :: rest) handler c
      = runPipeline (clTeGuardStage :: rest) handler' c := by
  rw [pipeline_gate_short_circuits clTeGuardStage rest handler c badRequestResp
        (clte_denies c h),
      pipeline_gate_short_circuits clTeGuardStage rest handler' c badRequestResp
        (clte_denies c h)]

/-! ## Concrete witnesses (non-vacuity) -/

/-- `POST / HTTP/1.1` with `Content-Length: 5` AND `Transfer-Encoding: chunked`
— the exact anti-smuggling probe shape. -/
def witnessCtx : Ctx :=
  { input := []
    req := { method := [80, 79, 83, 84], target := [47], version := []
             headers :=
               [ ([67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103,
                   116, 104], [53])
               , ([84, 114, 97, 110, 115, 102, 101, 114, 45, 69, 110, 99, 111,
                   100, 105, 110, 103],
                  [99, 104, 117, 110, 107, 101, 100]) ] }
    attrs := [] }

/-- The witness genuinely conflicts (kernel-decided on the explicit bytes). -/
theorem witness_conflict : clTeConflict witnessCtx.req = true := by decide

/-- The same request with ONLY a `Content-Length` — the allow contrast. -/
def okCtx : Ctx :=
  { input := []
    req := { method := [80, 79, 83, 84], target := [47], version := []
             headers :=
               [ ([67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103,
                   116, 104], [53]) ] }
    attrs := [] }

/-- The contrast is conflict-free (kernel-decided). -/
theorem ok_no_conflict : clTeConflict okCtx.req = false := by decide

/-- **The gate discriminates**: the conflicted witness is forced to the `400`,
the conflict-free contrast reaches the handler — same pipeline, same handler. -/
theorem clte_gate_discriminates (handler : Ctx → Response) :
    runPipeline [clTeGuardStage] handler witnessCtx
      = ResponseBuilder.ofResponse badRequestResp
  ∧ runPipeline [clTeGuardStage] handler okCtx
      = ResponseBuilder.ofResponse (handler okCtx) := by
  constructor
  · rw [pipeline_gate_short_circuits clTeGuardStage [] handler witnessCtx
        badRequestResp (clte_denies witnessCtx witness_conflict)]
    rfl
  · rw [pipeline_stage_effect clTeGuardStage [] handler okCtx okCtx
        (clte_allows okCtx ok_no_conflict)]
    rfl

end Reactor.Stage.ClTeGuard

#print axioms Reactor.Stage.ClTeGuard.clte_denies
#print axioms Reactor.Stage.ClTeGuard.clte_denies_status
#print axioms Reactor.Stage.ClTeGuard.witness_conflict
#print axioms Reactor.Stage.ClTeGuard.clte_gate_discriminates
