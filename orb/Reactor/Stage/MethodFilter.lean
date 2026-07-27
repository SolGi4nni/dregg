import Reactor.Pipeline

/-!
# Reactor.Stage.MethodFilter — the method allow-list gate (RFC 9110 §15.5.6 `405`)

A request whose method is NOT in the configured allow-list is refused
`405 Method Not Allowed`, carrying the RFC-9110 §10.2.1-required `Allow` header that
advertises the permitted methods; an allowed method passes to the handler untouched.
This is the nginx `limit_except` / Apache `<LimitExcept>` behaviour: a surface that
serves only `GET`/`POST`/`HEAD`/`OPTIONS` answers a `DELETE`/`TRACE`/`PATCH` with a
pristine `405` — the request never reaches the application.

## What is proven (headline)

* `method_denies` — a disallowed method makes the stage `.respond` the `405` (a genuine
  decision: the `Allow`-carrying `methodNotAllowed` whenever `isAllowed = false`), and
  `method_denies_status` carries that `405` through a status-stable inner onion.
* `method_allows` — an allowed method `.continue`s (pass-through).
* `method_denies_skips_handler` — the handler never runs on a refused request.
* `method_changes_bytes` — same handler: a disallowed method is forced to `405`, an
  allowed one runs the handler (`200`) — the gate genuinely drives the response.

Non-vacuity: `witnessCtx` (a `DELETE`) takes the deny branch (`witness_disallowed`),
`okCtx` (a `GET`) takes the allow branch; `method_changes_bytes` drives distinct status
bytes onto the wire.
-/

namespace Reactor.Stage.MethodFilter

open Reactor.Pipeline
open Proto (Bytes Request)

/-- ASCII byte-list of a string (kept as an explicit `List UInt8` so membership proofs
reduce in the kernel with `decide`). -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## The allow-list decision -/

/-- `GET` (ASCII). -/
def mGET  : Bytes := [71, 69, 84]
/-- `POST` (ASCII). -/
def mPOST : Bytes := [80, 79, 83, 84]
/-- `HEAD` (ASCII). -/
def mHEAD : Bytes := [72, 69, 65, 68]
/-- `OPTIONS` (ASCII). -/
def mOPTIONS : Bytes := [79, 80, 84, 73, 79, 78, 83]

/-- The permitted request methods. A surface serving these answers any other method a
`405`. -/
def allowedMethods : List Bytes := [mGET, mPOST, mHEAD, mOPTIONS]

/-- Whether a method is in the allow-list. -/
def isAllowed (m : Bytes) : Bool := allowedMethods.contains m

/-! ## The refusal response -/

/-- The `Allow` header name (RFC 9110 §10.2.1 — REQUIRED on a `405`). -/
def allowName : Bytes := strBytes "Allow"
/-- The `Allow` header value: the permitted methods, comma-joined. -/
def allowValue : Bytes := strBytes "GET, POST, HEAD, OPTIONS"

def notAllowedBody : Bytes := strBytes "method not allowed\n"

/-- The genuine `405` the gate answers with — status `405`, reason phrase, and the
RFC-required `Allow` header advertising the permitted methods (NOT a bare literal — it
carries the allow-list). -/
def methodNotAllowed : Response :=
  { status  := 405
    reason  := strBytes "Method Not Allowed"
    headers := [(allowName, allowValue)]
    body    := notAllowedBody }

/-- The refusal is a genuine `405`. -/
theorem methodNotAllowed_status : methodNotAllowed.status = 405 := rfl

/-- The refusal advertises the permitted methods (`Allow` header present) — a real
`405`, not a bare status. -/
theorem methodNotAllowed_advertises : (allowName, allowValue) ∈ methodNotAllowed.headers := by
  simp [methodNotAllowed]

/-! ## The stage -/

/-- **The method-filter gate stage.** Request phase: a method NOT in the allow-list is
refused `405` (short-circuit, handler skipped); an allowed method passes. Response phase
transparent. -/
def methodFilterStage : Stage where
  name := "method-filter"
  onRequest := fun c =>
    if isAllowed c.req.method then .continue c else .respond methodNotAllowed
  onResponse := fun _ b => b

theorem methodFilterStage_statusStable : Stage.statusStable methodFilterStage := fun _ _ => rfl

/-! ## Deny: a disallowed method is refused 405, handler skipped -/

/-- **`method_denies`.** A method not in the allow-list makes the stage `.respond` the
`405`. -/
theorem method_denies (c : Ctx) (h : isAllowed c.req.method = false) :
    methodFilterStage.onRequest c = .respond methodNotAllowed := by
  show (if isAllowed c.req.method then StageStep.continue c else StageStep.respond methodNotAllowed) = _
  rw [h]
  simp only [Bool.false_eq_true, if_false]

/-- **`method_allows`.** An allowed method passes (`.continue`). -/
theorem method_allows (c : Ctx) (h : isAllowed c.req.method = true) :
    methodFilterStage.onRequest c = .continue c := by
  show (if isAllowed c.req.method then StageStep.continue c else StageStep.respond methodNotAllowed) = _
  rw [h]; rfl

/-- **`method_denies_status`.** The refusal keeps its `405` through a status-stable inner
onion — a `405` stays a `405` on the wire. -/
theorem method_denies_status (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (h : isAllowed c.req.method = false) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (methodFilterStage :: rest) handler c).build).status = 405 := by
  have := pipeline_gate_status methodFilterStage rest handler c methodNotAllowed
    (method_denies c h) hst
  rw [this]; rfl

/-- **`method_denies_skips_handler`.** The request is NOT forwarded: swapping the handler
leaves the output unchanged — the handler never runs on a refused method. -/
theorem method_denies_skips_handler (c : Ctx) (rest : List Stage) (handler handler' : Ctx → Response)
    (h : isAllowed c.req.method = false) :
    runPipeline (methodFilterStage :: rest) handler c
      = runPipeline (methodFilterStage :: rest) handler' c :=
  pipeline_gate_ignores_handler methodFilterStage rest handler handler' c
    methodNotAllowed (method_denies c h)

/-! ## Concrete non-vacuity -/

/-- `DELETE` (ASCII, explicit bytes so `decide` reduces) — a method NOT in the
allow-list. -/
def mDELETE : Bytes := [68, 69, 76, 69, 84, 69]

/-- A `DELETE` request — a method NOT in the allow-list. -/
def witnessCtx : Ctx := { input := [], req := { method := mDELETE } }

/-- The witness method is genuinely disallowed. -/
theorem witness_disallowed : isAllowed witnessCtx.req.method = false := by decide

/-- **`witness_responds`.** On the `DELETE` witness the real stage `.respond`s the `405`
— the decision the braid gate delegates to. -/
theorem witness_responds : methodFilterStage.onRequest witnessCtx = .respond methodNotAllowed :=
  method_denies witnessCtx witness_disallowed

/-- A `GET` request — an allowed method. -/
def okCtx : Ctx := { input := [], req := { method := mGET } }

theorem okCtx_allowed : isAllowed okCtx.req.method = true := by decide

/-- **`method_changes_bytes`.** Same handler: a `DELETE` is forced to `405`, a `GET` runs
the handler (`200`). The gate genuinely drives the response. -/
theorem method_changes_bytes (body : Bytes) :
    ((runPipeline [methodFilterStage] (fun _ => Reactor.ok200 body) witnessCtx).build).status = 405
    ∧ ((runPipeline [methodFilterStage] (fun _ => Reactor.ok200 body) okCtx).build).status = 200 := by
  refine ⟨?_, ?_⟩
  · have := method_denies_status witnessCtx [] (fun _ => Reactor.ok200 body) witness_disallowed
      (by intro t ht; exact absurd ht (List.not_mem_nil))
    simpa using this
  · rw [pipeline_stage_effect methodFilterStage [] (fun _ => Reactor.ok200 body) okCtx okCtx
        (method_allows okCtx okCtx_allowed)]
    rfl

/-! ## Axiom audit -/

#print axioms method_denies
#print axioms method_allows
#print axioms method_denies_status
#print axioms method_denies_skips_handler
#print axioms witness_responds
#print axioms method_changes_bytes

end Reactor.Stage.MethodFilter
