import Reactor.Pipeline

/-!
# Reactor.Stage.HostAllowlist — the Host allow-list gate (RFC 9110 §15.5.20 `421`)

A request whose `Host` header names an authority NOT served by this endpoint is refused
`421 Misdirected Request`; a request for an allow-listed authority (or one with no `Host`)
passes. This is the coalesced-connection / SNI-vs-Host guard: a client that reuses a TLS
connection (or forges a `Host`) to reach an authority this server does not answer for is
told to open a fresh connection to the right origin, rather than being silently served
another vhost's content.

## What is proven (headline)

* `host_denies` — a non-allow-listed `Host` makes the stage `.respond` the `421`, and
  `host_denies_status` carries that `421` through a status-stable inner onion.
* `host_allows` — an allow-listed (or absent) `Host` `.continue`s.
* `host_denies_skips_handler` — the handler never runs on a misdirected request.
* `host_changes_bytes` — same handler: a misdirected request is forced to `421`, an
  allow-listed one runs the handler (`200`).

Non-vacuity: `witnessCtx` (`Host: evil.example`) takes the deny branch
(`witness_misdirected`), `okCtx` (`Host: localhost`) takes the allow branch.
-/

namespace Reactor.Stage.HostAllowlist

open Reactor.Pipeline
open Proto (Bytes Request)

def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## The Host allow-list decision -/

/-- `Host` header name (explicit ASCII bytes so the header match reduces in the kernel). -/
def hostName : Bytes := [72, 111, 115, 116]

/-- `localhost` (ASCII). -/
def hLocalhost : Bytes := [108, 111, 99, 97, 108, 104, 111, 115, 116]
/-- `orb.local` (ASCII). -/
def hOrbLocal : Bytes := [111, 114, 98, 46, 108, 111, 99, 97, 108]

/-- The authorities this endpoint answers for. A `Host` outside this list is misdirected. -/
def allowedHosts : List Bytes := [hLocalhost, hOrbLocal]

/-- **The misdirection decision.** `true` when the request carries a `Host` header whose
value is NOT in the allow-list; a listed host — or an absent `Host` — is `false` (not
misdirected). -/
def misdirected (req : Request) : Bool :=
  match req.headers.find? (fun nv => nv.1 == hostName) with
  | some nv => ! allowedHosts.contains nv.2
  | none    => false

/-! ## The refusal response -/

def misdirectedBody : Bytes := strBytes "misdirected request\n"

/-- The genuine `421` the gate answers with — status `421`, reason phrase, notice body. -/
def misdirectedResp : Response :=
  { status  := 421
    reason  := strBytes "Misdirected Request"
    headers := []
    body    := misdirectedBody }

theorem misdirectedResp_status : misdirectedResp.status = 421 := rfl

/-! ## The stage -/

/-- **The Host allow-list gate stage.** Request phase: a `Host` outside the allow-list is
refused `421` (short-circuit, handler skipped); a listed or absent `Host` passes. Response
phase transparent. -/
def hostAllowlistStage : Stage where
  name := "host-allowlist"
  onRequest := fun c =>
    if misdirected c.req then .respond misdirectedResp else .continue c
  onResponse := fun _ b => b

theorem hostAllowlistStage_statusStable : Stage.statusStable hostAllowlistStage := fun _ _ => rfl

/-! ## Deny: a misdirected Host is refused 421, handler skipped -/

/-- **`host_denies`.** A non-allow-listed `Host` makes the stage `.respond` the `421`. -/
theorem host_denies (c : Ctx) (h : misdirected c.req = true) :
    hostAllowlistStage.onRequest c = .respond misdirectedResp := by
  show (if misdirected c.req then StageStep.respond misdirectedResp else StageStep.continue c) = _
  rw [h]; rfl

/-- **`host_allows`.** An allow-listed (or absent) `Host` passes (`.continue`). -/
theorem host_allows (c : Ctx) (h : misdirected c.req = false) :
    hostAllowlistStage.onRequest c = .continue c := by
  show (if misdirected c.req then StageStep.respond misdirectedResp else StageStep.continue c) = _
  rw [h]
  simp only [Bool.false_eq_true, if_false]

/-- **`host_denies_status`.** The refusal keeps its `421` through a status-stable inner
onion — a `421` stays a `421` on the wire. -/
theorem host_denies_status (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (h : misdirected c.req = true) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (hostAllowlistStage :: rest) handler c).build).status = 421 := by
  have := pipeline_gate_status hostAllowlistStage rest handler c misdirectedResp
    (host_denies c h) hst
  rw [this]; rfl

/-- **`host_denies_skips_handler`.** The request is NOT forwarded on a misdirected Host. -/
theorem host_denies_skips_handler (c : Ctx) (rest : List Stage) (handler handler' : Ctx → Response)
    (h : misdirected c.req = true) :
    runPipeline (hostAllowlistStage :: rest) handler c
      = runPipeline (hostAllowlistStage :: rest) handler' c :=
  pipeline_gate_ignores_handler hostAllowlistStage rest handler handler' c
    misdirectedResp (host_denies c h)

/-! ## Concrete non-vacuity -/

/-- A request for `Host: evil.example` — an authority NOT in the allow-list. -/
def witnessCtx : Ctx :=
  { input := [], req := { headers := [(hostName, [101, 118, 105, 108, 46, 101, 120, 97, 109, 112, 108, 101])] } }

/-- The witness Host is genuinely misdirected. -/
theorem witness_misdirected : misdirected witnessCtx.req = true := by decide

/-- **`witness_responds`.** On the misdirected witness the real stage `.respond`s the
`421` — the decision the braid gate delegates to. -/
theorem witness_responds : hostAllowlistStage.onRequest witnessCtx = .respond misdirectedResp :=
  host_denies witnessCtx witness_misdirected

/-- A request for `Host: localhost` — an allow-listed authority. -/
def okCtx : Ctx :=
  { input := [], req := { headers := [(hostName, hLocalhost)] } }

theorem okCtx_allowed : misdirected okCtx.req = false := by decide

/-- **`host_changes_bytes`.** Same handler: a misdirected request is forced to `421`, an
allow-listed one runs the handler (`200`). The gate genuinely drives the response. -/
theorem host_changes_bytes (body : Bytes) :
    ((runPipeline [hostAllowlistStage] (fun _ => Reactor.ok200 body) witnessCtx).build).status = 421
    ∧ ((runPipeline [hostAllowlistStage] (fun _ => Reactor.ok200 body) okCtx).build).status = 200 := by
  refine ⟨?_, ?_⟩
  · have := host_denies_status witnessCtx [] (fun _ => Reactor.ok200 body) witness_misdirected
      (by intro t ht; exact absurd ht (List.not_mem_nil))
    simpa using this
  · rw [pipeline_stage_effect hostAllowlistStage [] (fun _ => Reactor.ok200 body) okCtx okCtx
        (host_allows okCtx okCtx_allowed)]
    rfl

/-! ## Axiom audit -/

#print axioms host_denies
#print axioms host_allows
#print axioms host_denies_status
#print axioms host_denies_skips_handler
#print axioms witness_responds
#print axioms host_changes_bytes

end Reactor.Stage.HostAllowlist
