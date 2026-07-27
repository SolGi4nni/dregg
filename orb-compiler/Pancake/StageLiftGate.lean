/-
  Pancake/StageLiftGate.lean — THE GATE LIFT: one general theorem for the
  gate SHAPE, then every gate-shaped deployed stage is a one-line instantiation.

  THE POINT. The previous stage files (StageMore / StageEvenMore) each hand-wrote a
  `StageProg` term plus a bespoke `denote`-pin proof, one stage at a time. That does
  not scale and it does not say anything general. The deployed serve's gate-shaped
  stages all have ONE shape:

      onRequest := fun c => if fire c then .respond refusal else .continue c
      onResponse := fun _ b => b                      -- transparent (a pure gate)

  so ONE theorem about that shape, quantified over the fire-predicate and the refusal
  response, covers ALL of them; a stage is then a one-line instantiation supplying its
  REAL refusal `Response` (transcribed from the deployed stage, field by field).

  THE HONEST CORRECTION TO THE ASSUMED SHAPE. The `gate` constructor carries a BARE
  `Nat` status, and `denote (.gate c code) ctx = { ctx.base with status := code }` —
  it keeps the base's reason/headers/body. But NOT ONE deployed gate refuses with a
  bare status: every single refusal is a FULL `Response` with its own reason phrase
  and its own body (`error4xx code reason body`, or an explicit record), and several
  carry headers too (`405` + `Allow`, `401` + `WWW-Authenticate`, `304` +
  `Last-Modified`). So a bare-`gate` full-response pin would be FALSE for every
  deployed gate. Two lemmas instead, and the split is the real one:

   * §3 `denote_gate_status_general` — the bare `.gate` constructor pins exactly the
     STATUS, for any fire-predicate and any (even context-dependent) refusal whose
     status is `code`. This is precisely the property the deployed side itself pins
     (`pipeline_gate_status`: the built response's status is the refusal's), so the
     bare gate is faithful at exactly the granularity the deployed gate theorems use
     — and no further.

   * §4 `denote_gateChain_exact` / `denote_gateChain` — the FULL-response lift. The
     payload-carrying gate is `condR fire (setStatus; replace body; addHeaders; gate)`
     — the trailing `gate` is what makes the short-circuit REAL (it sets `halted`, so
     `denoteStep_halted` absorbs everything after it: the DSL analogue of the deployed
     `pipeline_gate_ignores_handler`). Stated for a CHAIN of (fire, refusal) branches,
     because several deployed gates are nested if-chains with different statuses per
     branch (`400`/`501`/`505`; `400`/`400`/`417`). A single gate is the singleton
     chain (`denote_gateWith`).

  §5 instantiates the lift for every gate-shaped deployed stage: each `refusal` is the
  deployed refusal record transcribed field-for-field, and each instantiation is one
  application of the general lemma — no new proof per stage.

  RESIDUALS (named, not hidden):
   * The full-response lift's exact form is hypothesis-free
     (`denote_gateChain_exact`); equality with the deployed refusal ON THE NOSE needs
     `ctx.base.headers = []` (the DSL appends onto the seed's header list, whereas a
     deployed short-circuit REPLACES the builder with the refusal record). That is a
     real, stated side condition of the gate seed, not a fudge — `denote_gateChain`
     carries it explicitly.
   * The deployed gate's emitted response is modelled with a TRANSPARENT tail (the
     single-gate, empty-tail built response). The tail case — response transforms
     enriching a short-circuit while preserving its status — is the deployed side's
     own status-stability result and is not restated here.
   * Two gates are genuine MISFITS: their refusal is a FUNCTION of the request rather
     than a constant record (a redirect whose `Location` is built from the request's
     own target; a cache hit whose body is the stored entry). The DSL's `addHeader`
     carries constant `Bytes`, so those need a context-dependent header/body operand —
     listed in §6, NOT force-fitted.
-/
import Pancake.StageCompile

namespace Pancake.StageLiftGate

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageCompile

variable {σ : Type}

/-! ## 1. The generic deployed gate, transcribed

The deployed gate-shaped stage is

    Stage.mk name (fun c => if fire c then .respond refusal else .continue c)
                  (fun _ b => b)

and, run over a transparent tail with the handler seeding the base response, the
response it EMITS is: the refusal when `fire` holds, the handler's own response
otherwise (the handler and every later stage are skipped on the refusal path). That
emitted response is `gateEmit`. -/

/-- **The generic deployed gate's emitted response.** `fire ctx` ⇒ the refusal
record; otherwise the handler's base response, untouched. -/
def gateEmit (fire : ReqPred) (refusal : Response) (ctx : Ctx) : Response :=
  if fire ctx then refusal else ctx.base

/-- **The generic deployed if-CHAIN gate's emitted response.** The deployed
multi-branch gates test their conditions in order and answer with the first match's
refusal; a request clearing every branch passes to the handler. -/
def gateChainEmit : List (ReqPred × Response) → Ctx → Response
  | [],          ctx => ctx.base
  | (f, r) :: t, ctx => if f ctx then r else gateChainEmit t ctx

/-- A single gate is the singleton chain. -/
theorem gateChainEmit_singleton (fire : ReqPred) (r : Response) (ctx : Ctx) :
    gateChainEmit [(fire, r)] ctx = gateEmit fire r ctx := rfl

/-! ## 2. Building blocks in the DSL -/

/-- The no-op stage program: a body-identity rewrite. -/
def nop : StageProg := .rewriteBody .identity

/-- Append a whole header list, one `addHeader` per entry, in order. -/
def addHeaders : List (Bytes × Bytes) → StageProg
  | []          => nop
  | (n, v) :: t => .seq (.addHeader n v) (addHeaders t)

/-- **The refusal payload.** Overwrite the status line, replace the body, append the
refusal's headers, and then HALT (the trailing `gate` fires unconditionally, setting
the already-set status and flipping `halted`). The halt is the load-bearing part: it
is the DSL's short-circuit, and `denoteStep_halted` makes it absorb every later op. -/
def payload (r : Response) : StageProg :=
  .seq (.setStatus r.status r.reason)
    (.seq (.rewriteBody (.replace r.body))
      (.seq (addHeaders r.headers) (.gate (fun _ => true) r.status)))

/-- **The gate-shaped stage program, as an if-chain.** Test each branch's fire
predicate in order; the first that fires runs its refusal payload and halts; a
request clearing every branch falls through to the no-op (pass to the handler). -/
def gateChain : List (ReqPred × Response) → StageProg
  | []          => nop
  | (f, r) :: t => .condR f (payload r) (gateChain t)

/-- **The single gate-shaped stage program** — the singleton chain. -/
def gateWith (fire : ReqPred) (r : Response) : StageProg := gateChain [(fire, r)]

/-! ## 3. THE BARE-GATE LIFT (status granularity)

The `gate` constructor carries a bare `Nat`, so it pins the STATUS and nothing else.
That is not a weakness papered over: it is exactly the granularity of the deployed
gate's own wire theorem (the built response's status IS the refusal's status). -/

/-- **`denote_gate_status_general` — ONE theorem, every gate.** For ANY fire
predicate `fire`, ANY refusal-response family `refusal : Ctx → Response` (constant or
context-dependent), and ANY status `code` such that a firing request's refusal carries
`code`: the bare DSL gate's denotation has, at every context, EXACTLY the status the
generic deployed gate emits. Both branches are live — pass yields the handler's base
status, refusal yields `code` — so this is not a tautology, and it is quantified over
the predicate and the refusal, not sampled at one stage. -/
theorem denote_gate_status_general
    (fire : ReqPred) (refusal : Ctx → Response) (code : Nat)
    (hcode : ∀ c, fire c = true → (refusal c).status = code) (ctx : Ctx) :
    (denote (.gate fire code) ctx).status
      = (if fire ctx then refusal ctx else ctx.base).status := by
  cases hf : fire ctx with
  | true =>
    rw [denote, denoteStep_gate_fires ctx fire code _ rfl hf]
    simp only [if_true, hcode ctx hf]
  | false =>
    show (if (false : Bool) = true then _
          else if fire ctx then _ else ({ resp := ctx.base, halted := false } : DState)).resp.status = _
    simp only [hf, Bool.false_eq_true, if_false]

/-! ## 4. THE FULL-RESPONSE GATE LIFT

The real lift: a gate-shaped stage's whole refusal record — status, reason, headers,
body — plus the short-circuit itself. -/

/-- `addHeaders` appends its whole list to a live fold state (structural induction on
the header list). -/
theorem denoteStep_addHeaders (ctx : Ctx) :
    ∀ (hs : List (Bytes × Bytes)) (d : DState), d.halted = false →
      denoteStep ctx (addHeaders hs) d
        = { d with resp := { d.resp with headers := d.resp.headers ++ hs } } := by
  intro hs
  induction hs with
  | nil =>
    intro d h
    show denoteStep ctx nop d = _
    simp only [nop, denoteStep, h, Bool.false_eq_true, if_false, runBody, List.append_nil]
  | cons nv t ih =>
    intro d h
    obtain ⟨n, v⟩ := nv
    show denoteStep ctx (addHeaders t) (denoteStep ctx (.addHeader n v) d) = _
    have h1 : denoteStep ctx (.addHeader n v) d
        = { d with resp := { d.resp with headers := d.resp.headers ++ [(n, v)] } } := by
      simp only [denoteStep, h, Bool.false_eq_true, if_false]
    rw [h1, ih { d with resp := { d.resp with headers := d.resp.headers ++ [(n, v)] } } h]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- **The refusal payload's denotation.** From a live state, the payload lands the
refusal's status, reason and body, appends the refusal's headers to the seed's, and
HALTS. -/
theorem denoteStep_payload (ctx : Ctx) (r : Response) (d : DState) (h : d.halted = false) :
    denoteStep ctx (payload r) d
      = { resp := { r with headers := d.resp.headers ++ r.headers }, halted := true } := by
  obtain ⟨resp, halted⟩ := d
  obtain ⟨st, rs, hs, bd⟩ := resp
  subst h
  -- the `setStatus` and body-`replace` steps reduce (the fold state is live by
  -- construction), leaving the header append and the halting gate:
  show denoteStep ctx (.gate (fun _ => true) r.status)
        (denoteStep ctx (addHeaders r.headers)
          ({ resp := { status := r.status, reason := r.reason, headers := hs, body := r.body },
             halted := false } : DState)) = _
  rw [denoteStep_addHeaders ctx r.headers
        ({ resp := { status := r.status, reason := r.reason, headers := hs, body := r.body },
           halted := false } : DState) rfl]
  -- the halting gate then reduces: the state is live and the predicate is `true`.
  rfl

/-- **`denote_gateChain_exact` — THE LIFT, hypothesis-free.** For ANY list of
(fire-predicate, refusal-response) branches and ANY context, the chain's denotation is
the first firing branch's refusal record — status, reason and body exactly the
deployed refusal's, headers the seed's followed by the refusal's — or the seed's own
response when no branch fires. ONE structural induction on the branch list; every
gate-shaped stage is an instantiation. -/
theorem denote_gateChain_exact (ctx : Ctx) :
    ∀ (hs : List (ReqPred × Response)),
      denote (gateChain hs) ctx
        = (gateChainEmit (hs.map (fun fr =>
            (fr.1, { fr.2 with headers := ctx.base.headers ++ fr.2.headers }))) ctx) := by
  intro hs
  induction hs with
  | nil =>
    show (denoteStep ctx nop { resp := ctx.base, halted := false }).resp = _
    simp only [nop, denoteStep, Bool.false_eq_true, if_false, runBody]
    rfl
  | cons fr t ih =>
    obtain ⟨f, r⟩ := fr
    show (if f ctx then denoteStep ctx (payload r) { resp := ctx.base, halted := false }
          else denoteStep ctx (gateChain t) { resp := ctx.base, halted := false }).resp = _
    by_cases hf : f ctx = true
    · rw [if_pos hf, denoteStep_payload ctx r { resp := ctx.base, halted := false } rfl]
      simp only [List.map_cons, gateChainEmit, hf, if_true]
    · have hf' : f ctx = false := by simpa using hf
      rw [if_neg hf]
      show (denoteStep ctx (gateChain t) { resp := ctx.base, halted := false }).resp = _
      rw [show (denoteStep ctx (gateChain t) { resp := ctx.base, halted := false }).resp
            = denote (gateChain t) ctx from rfl, ih]
      simp only [List.map_cons, gateChainEmit, hf', Bool.false_eq_true, if_false]

/-- **`denote_gateChain` — the lift, pinned ON THE NOSE to the deployed gate.** With
the gate's seed carrying no headers (a gate short-circuits BEFORE the handler, so the
seed the refusal overwrites is a bare response), the chain's denotation IS the generic
deployed if-chain gate's emitted response, record for record. ONE theorem; every
gate-shaped deployed stage instantiates it. -/
theorem denote_gateChain (ctx : Ctx) (hbase : ctx.base.headers = [])
    (hs : List (ReqPred × Response)) :
    denote (gateChain hs) ctx = gateChainEmit hs ctx := by
  rw [denote_gateChain_exact ctx hs]
  induction hs with
  | nil => rfl
  | cons fr t ih =>
    obtain ⟨f, r⟩ := fr
    cases hf : f ctx with
    | true =>
      simp only [List.map_cons, gateChainEmit, hf, if_true, hbase, List.nil_append]
    | false =>
      simp only [List.map_cons, gateChainEmit, hf, Bool.false_eq_true, if_false]
      exact ih

/-- **`denote_gateWith` — the single-gate lift** (the singleton chain). For ANY fire
predicate and ANY refusal record, a bare-seeded gate's denotation is EXACTLY the
generic deployed gate's emitted response. This is the one-liner every gate-shaped
stage in §5 instantiates. -/
theorem denote_gateWith (fire : ReqPred) (r : Response) (ctx : Ctx)
    (hbase : ctx.base.headers = []) :
    denote (gateWith fire r) ctx = gateEmit fire r ctx :=
  denote_gateChain ctx hbase [(fire, r)]

/-! ### 4.1 The short-circuit is REAL

The DSL analogue of the deployed `pipeline_gate_ignores_handler`: a fired gate makes
everything sequenced after it — the handler's work and every later stage — vanish. -/

/-- **`gateChain_short_circuits`.** When a branch fires, ANY program `q` sequenced
after the chain contributes NOTHING: `seq (gateChain hs) q` denotes exactly as
`gateChain hs` does. Quantified over `q`, so the handler and every later stage are
genuinely skipped — the gate's short-circuit, not a claim about one sample. -/
theorem gateChain_short_circuits (ctx : Ctx) (f : ReqPred) (r : Response)
    (t : List (ReqPred × Response)) (hf : f ctx = true) (q : StageProg) :
    denote (.seq (gateChain ((f, r) :: t)) q) ctx = denote (gateChain ((f, r) :: t)) ctx := by
  have hfire : denoteStep ctx (gateChain ((f, r) :: t)) { resp := ctx.base, halted := false }
      = { resp := { r with headers := ctx.base.headers ++ r.headers }, halted := true } := by
    show (if f ctx = true then denoteStep ctx (payload r) { resp := ctx.base, halted := false }
          else denoteStep ctx (gateChain t) { resp := ctx.base, halted := false }) = _
    rw [if_pos hf, denoteStep_payload ctx r { resp := ctx.base, halted := false } rfl]
  show (denoteStep ctx q (denoteStep ctx (gateChain ((f, r) :: t))
          { resp := ctx.base, halted := false })).resp
      = (denoteStep ctx (gateChain ((f, r) :: t)) { resp := ctx.base, halted := false }).resp
  rw [hfire, denoteStep_halted ctx q _ rfl]

/-! ### 4.2 The lift meets the compiler keystone

`compile2_correct` is already `∀ p` — so the compiled control flow of EVERY gate-shaped
program below is covered with no new proof; this corollary just names that fact at the
lift's own terms. -/

/-- **`gateChain_compile2_correct` — the lift's terms compile.** For ANY branch list,
the genuine per-constructor compiler's emitted fragment lands the response skeleton of
`gateChain hs`'s reference fold. A direct instantiation of the induction keystone at
`p := gateChain hs`; no per-stage proof. -/
theorem gateChain_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx) (hd : Distinct aStat aCnt aBody aHalt)
    (hs : List (ReqPred × Response)) (d : DState) (st : PancakeState σ)
    (he : CoreEnc aStat aCnt aBody aHalt st d)
    (hn : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (gateChain hs)) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st' (denoteStep ctx (gateChain hs) d) ∧
      st'.locals = st.locals ∧
      (∀ x, st'.memaddrs x = st.memaddrs x) ∧
      st'.clock = st.clock :=
  compile2_correct o nm aStat aCnt aBody aHalt ctx hd (gateChain hs) d st he hn

/-! ## 5. The deployed gate-shaped stages — one line each

Each refusal below is the deployed stage's OWN refusal record, transcribed field for
field (status / reason phrase / headers / body) from the deployed stage source. The
`error4xx`-built refusals (`503`/`429`/`408`/`401`/`403`/`500`) carry an EMPTY header
list by that constructor's definition; the record-built ones carry the headers the
stage writes. -/

/-! ### 5.1 The refusal records -/

/-- `405` — method allow-list refusal: carries the RFC-9110-required `Allow`. -/
def methodNotAllowed : Response :=
  { status := 405, reason := str "Method Not Allowed",
    headers := [(str "Allow", str "GET, POST, HEAD, OPTIONS")],
    body := str "method not allowed\n" }

/-- `403` — CIDR admission refusal. -/
def forbidden403 : Response :=
  { status := 403, reason := str "Forbidden", headers := [],
    body := str "forbidden: ip not admitted" }

/-- `413` — body-size cap refusal. -/
def contentTooLarge : Response :=
  { status := 413, reason := str "Content Too Large", headers := [],
    body := str "content too large\n" }

/-- `503` — per-source connection-cap refusal (`error4xx`: no headers). -/
def resp503 : Response :=
  { status := 503, reason := str "Service Unavailable", headers := [],
    body := str "per-source connection limit reached\n" }

/-- `431` — request-head byte-cap refusal. -/
def requestHeaderFieldsTooLarge : Response :=
  { status := 431, reason := str "Request Header Fields Too Large", headers := [],
    body := str "request header fields too large\n" }

/-- `414` — request-target length refusal. -/
def uriTooLong : Response :=
  { status := 414, reason := str "URI Too Long", headers := [],
    body := str "uri too long\n" }

/-- `429` — aggregated stick-counter threshold refusal (`error4xx`: no headers). -/
def stickResp429 : Response :=
  { status := 429, reason := str "Too Many Requests", headers := [],
    body := str "aggregated request limit exceeded\n" }

/-- `429` — token-bucket rate refusal (`error4xx`: no headers). -/
def rateResp429 : Response :=
  { status := 429, reason := str "Too Many Requests", headers := [],
    body := str "rate limit exceeded\n" }

/-- `408` — header-dribble timeout refusal (`error4xx`: no headers). -/
def resp408 : Response :=
  { status := 408, reason := str "Request Timeout", headers := [],
    body := str "request header timeout\n" }

/-- `304` — conditional-request hit: carries the validator instant as
`Last-Modified`, and an empty body by definition of a `304`. -/
def notModified304 : Response :=
  { status := 304, reason := str "Not Modified",
    headers := [(str "Last-Modified", str "Mon, 01 Jan 2024 00:00:00 GMT")],
    body := [] }

/-- `400` — malformed-request refusal (shared by the framing and validation gates). -/
def badRequest400 : Response :=
  { status := 400, reason := str "Bad Request", headers := [],
    body := str "bad request\n" }

/-- `417` — unsatisfiable `Expect` refusal. -/
def expectationFailed417 : Response :=
  { status := 417, reason := str "Expectation Failed", headers := [],
    body := str "expectation failed\n" }

/-- `501` — unrecognized method refusal. -/
def notImplemented501 : Response :=
  { status := 501, reason := str "Not Implemented", headers := [],
    body := str "not implemented\n" }

/-- `505` — unsupported protocol version refusal. -/
def badVersion505 : Response :=
  { status := 505, reason := str "HTTP Version Not Supported", headers := [],
    body := str "http version not supported\n" }

/-- `421` — `Host` allow-list refusal. -/
def misdirected421 : Response :=
  { status := 421, reason := str "Misdirected Request", headers := [],
    body := str "misdirected request\n" }

/-- `401` — bearer-token refusal: carries the `WWW-Authenticate: Bearer` challenge. -/
def bearerUnauthorized : Response :=
  { status := 401, reason := str "Unauthorized",
    headers := [(str "WWW-Authenticate", str "Bearer")],
    body := str "invalid or missing bearer token" }

/-- `401` — credential refusal, carrying EXACTLY the challenge value the real
authenticator produced (a family over the challenge, one gate per value). -/
def basicUnauthorized (www : Bytes) : Response :=
  { status := 401, reason := str "Unauthorized",
    headers := [(str "WWW-Authenticate", www)],
    body := str "authentication required" }

/-- `401` — auth-subrequest deny (`error4xx`: no headers). -/
def authResp401 : Response :=
  { status := 401, reason := str "Unauthorized", headers := [],
    body := str "auth subrequest denied\n" }

/-- `403` — auth-subrequest deny (`error4xx`: no headers). -/
def authResp403 : Response :=
  { status := 403, reason := str "Forbidden", headers := [],
    body := str "auth subrequest denied\n" }

/-- `500` — auth-subrequest fail-closed (`error4xx`: no headers). -/
def authResp500 : Response :=
  { status := 500, reason := str "Internal Server Error", headers := [],
    body := str "auth subrequest failed\n" }

/-- `500` — forwarded-auth fail-closed (`error4xx`: no headers). -/
def forwardResp500 : Response :=
  { status := 500, reason := str "Internal Server Error", headers := [],
    body := str "auth subrequest failed\n" }

/-- The forwarded-auth deny refusal at a carried-through status; the reason phrase is
the deployed `reasonOf` table (`401` ⇒ `Unauthorized`, anything else ⇒ `Forbidden`). -/
def forwardReasonOf : Nat → Bytes
  | 401 => str "Unauthorized"
  | _   => str "Forbidden"

/-- `4xx` — forwarded-auth deny, a family over the carried status. -/
def forwardDenyResp (status : Nat) : Response :=
  { status := status, reason := forwardReasonOf status, headers := [],
    body := str "auth subrequest denied\n" }

/-! ### 5.2 The instantiations — every one is `denote_gateWith` / `denote_gateChain`

Each theorem below pins the DSL term's `denote` to the generic deployed gate's emitted
response at the stage's REAL refusal record. `fire` is left universally quantified: it
is whatever decision the deployed stage computes (a CIDR match, a token bucket, a
timeout, a signature check) — the lift is about the gate SHAPE, and the decisions
themselves are the deployed libraries' own proven cores. -/

/-- **Method allow-list gate (`405`).** -/
theorem lift_methodFilter (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire methodNotAllowed) ctx = gateEmit fire methodNotAllowed ctx :=
  denote_gateWith fire methodNotAllowed ctx hbase

/-- **CIDR admission gate (`403`).** -/
theorem lift_ipFilter (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire forbidden403) ctx = gateEmit fire forbidden403 ctx :=
  denote_gateWith fire forbidden403 ctx hbase

/-- **Body-size cap gate (`413`).** -/
theorem lift_bodyLimit (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire contentTooLarge) ctx = gateEmit fire contentTooLarge ctx :=
  denote_gateWith fire contentTooLarge ctx hbase

/-- **Per-source connection-cap gate (`503`).** -/
theorem lift_connLimit (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire resp503) ctx = gateEmit fire resp503 ctx :=
  denote_gateWith fire resp503 ctx hbase

/-- **Request-head byte-cap gate (`431`).** -/
theorem lift_requestHeadLimit (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire requestHeaderFieldsTooLarge) ctx
      = gateEmit fire requestHeaderFieldsTooLarge ctx :=
  denote_gateWith fire requestHeaderFieldsTooLarge ctx hbase

/-- **Request-target length gate (`414`).** -/
theorem lift_uriTooLong (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire uriTooLong) ctx = gateEmit fire uriTooLong ctx :=
  denote_gateWith fire uriTooLong ctx hbase

/-- **Aggregated stick-counter gate (`429`).** -/
theorem lift_stickTable (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire stickResp429) ctx = gateEmit fire stickResp429 ctx :=
  denote_gateWith fire stickResp429 ctx hbase

/-- **Token-bucket rate gate (`429`).** -/
theorem lift_rate (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire rateResp429) ctx = gateEmit fire rateResp429 ctx :=
  denote_gateWith fire rateResp429 ctx hbase

/-- **Header-dribble timeout gate (`408`).** -/
theorem lift_slowloris (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire resp408) ctx = gateEmit fire resp408 ctx :=
  denote_gateWith fire resp408 ctx hbase

/-- **Conditional-request gate (`304` + `Last-Modified`).** -/
theorem lift_modifiedSince (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire notModified304) ctx = gateEmit fire notModified304 ctx :=
  denote_gateWith fire notModified304 ctx hbase

/-- **`Host` allow-list gate (`421`).** -/
theorem lift_hostAllowlist (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire misdirected421) ctx = gateEmit fire misdirected421 ctx :=
  denote_gateWith fire misdirected421 ctx hbase

/-- **Bearer-token gate (`401` + `WWW-Authenticate: Bearer`).** -/
theorem lift_jwt (fire : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire bearerUnauthorized) ctx = gateEmit fire bearerUnauthorized ctx :=
  denote_gateWith fire bearerUnauthorized ctx hbase

/-- **Credential gate (`401` + the authenticator's own challenge).** A FAMILY: one gate
per challenge value the real authenticator produces. -/
theorem lift_basicAuth (fire : ReqPred) (www : Bytes) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateWith fire (basicUnauthorized www)) ctx = gateEmit fire (basicUnauthorized www) ctx :=
  denote_gateWith fire (basicUnauthorized www) ctx hbase

/-- **Auth-subrequest gate — the three-outcome if-chain (`401` / `403` / `500`).** -/
theorem lift_authRequest (f401 f403 f500 : ReqPred) (ctx : Ctx) (hbase : ctx.base.headers = []) :
    denote (gateChain [(f401, authResp401), (f403, authResp403), (f500, authResp500)]) ctx
      = gateChainEmit [(f401, authResp401), (f403, authResp403), (f500, authResp500)] ctx :=
  denote_gateChain ctx hbase _

/-- **Forwarded-auth gate — deny at a carried status, else fail-closed `500`.** A
FAMILY over the carried deny status. -/
theorem lift_forwardAuth (fdeny f500 : ReqPred) (status : Nat) (ctx : Ctx)
    (hbase : ctx.base.headers = []) :
    denote (gateChain [(fdeny, forwardDenyResp status), (f500, forwardResp500)]) ctx
      = gateChainEmit [(fdeny, forwardDenyResp status), (f500, forwardResp500)] ctx :=
  denote_gateChain ctx hbase _

/-- **Framing-validation gate — the ordered three-branch chain (`400` field-name,
`400` transfer-coding, `417` `Expect`).** -/
theorem lift_framingValidation (fname fte fexp : ReqPred) (ctx : Ctx)
    (hbase : ctx.base.headers = []) :
    denote (gateChain [(fname, badRequest400), (fte, badRequest400),
                       (fexp, expectationFailed417)]) ctx
      = gateChainEmit [(fname, badRequest400), (fte, badRequest400),
                       (fexp, expectationFailed417)] ctx :=
  denote_gateChain ctx hbase _

/-- **Request-validation gate — the ordered three-branch chain (`505` version, `501`
method, `400` host).** The deployed nesting tests version first, then method, then
host; the chain's branch order is that order. -/
theorem lift_requestValidation (fver fmeth fhost : ReqPred) (ctx : Ctx)
    (hbase : ctx.base.headers = []) :
    denote (gateChain [(fver, badVersion505), (fmeth, notImplemented501),
                       (fhost, badRequest400)]) ctx
      = gateChainEmit [(fver, badVersion505), (fmeth, notImplemented501),
                       (fhost, badRequest400)] ctx :=
  denote_gateChain ctx hbase _

/-! ### 5.3 The bare-gate status lift, instantiated

The bare `gate` constructor still says something true and useful about every one of
these: its status IS the refusal's status — the granularity the deployed gate's own
wire theorem pins. Shown at the whole refusal set at once. -/

/-- **`lift_status_all`.** For ANY fire predicate, the bare DSL gate at each deployed
refusal's status emits exactly the status the generic deployed gate does. One
application of the general status lift per refusal — no bespoke proofs. -/
theorem lift_status_all (fire : ReqPred) (ctx : Ctx) :
    (denote (.gate fire 405) ctx).status
        = (if fire ctx then methodNotAllowed else ctx.base).status
    ∧ (denote (.gate fire 403) ctx).status
        = (if fire ctx then forbidden403 else ctx.base).status
    ∧ (denote (.gate fire 413) ctx).status
        = (if fire ctx then contentTooLarge else ctx.base).status
    ∧ (denote (.gate fire 503) ctx).status
        = (if fire ctx then resp503 else ctx.base).status
    ∧ (denote (.gate fire 431) ctx).status
        = (if fire ctx then requestHeaderFieldsTooLarge else ctx.base).status
    ∧ (denote (.gate fire 414) ctx).status
        = (if fire ctx then uriTooLong else ctx.base).status
    ∧ (denote (.gate fire 429) ctx).status
        = (if fire ctx then rateResp429 else ctx.base).status
    ∧ (denote (.gate fire 408) ctx).status
        = (if fire ctx then resp408 else ctx.base).status
    ∧ (denote (.gate fire 304) ctx).status
        = (if fire ctx then notModified304 else ctx.base).status
    ∧ (denote (.gate fire 400) ctx).status
        = (if fire ctx then badRequest400 else ctx.base).status
    ∧ (denote (.gate fire 417) ctx).status
        = (if fire ctx then expectationFailed417 else ctx.base).status
    ∧ (denote (.gate fire 501) ctx).status
        = (if fire ctx then notImplemented501 else ctx.base).status
    ∧ (denote (.gate fire 505) ctx).status
        = (if fire ctx then badVersion505 else ctx.base).status
    ∧ (denote (.gate fire 421) ctx).status
        = (if fire ctx then misdirected421 else ctx.base).status
    ∧ (denote (.gate fire 401) ctx).status
        = (if fire ctx then bearerUnauthorized else ctx.base).status
    ∧ (denote (.gate fire 500) ctx).status
        = (if fire ctx then authResp500 else ctx.base).status :=
  ⟨denote_gate_status_general fire (fun _ => methodNotAllowed) 405 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => forbidden403) 403 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => contentTooLarge) 413 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => resp503) 503 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => requestHeaderFieldsTooLarge) 431 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => uriTooLong) 414 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => rateResp429) 429 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => resp408) 408 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => notModified304) 304 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => badRequest400) 400 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => expectationFailed417) 417 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => notImplemented501) 501 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => badVersion505) 505 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => misdirected421) 421 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => bearerUnauthorized) 401 (fun _ _ => rfl) ctx,
   denote_gate_status_general fire (fun _ => authResp500) 500 (fun _ _ => rfl) ctx⟩

/-- **The status lift covers the context-DEPENDENT refusal families too** — the bare
gate's status pin does not need a constant refusal, only a constant status. The
forwarded-auth deny family at a fixed carried status is exactly that. -/
theorem lift_status_forwardDeny (fire : ReqPred) (status : Nat) (ctx : Ctx) :
    (denote (.gate fire status) ctx).status
      = (if fire ctx then forwardDenyResp status else ctx.base).status :=
  denote_gate_status_general fire (fun _ => forwardDenyResp status) status (fun _ _ => rfl) ctx

/-! ## 6. Non-vacuity — the lift genuinely drives distinct wire bytes -/

/-- A `200 OK` seed with an empty header list — the bare seed a gate short-circuits
over (`ok200` builds exactly this: no headers). -/
def baseOk : Response := ok200 (str "hi")

/-- The seed carries no headers — the side condition of `denote_gateChain`, discharged
for the real seed. -/
theorem baseOk_headers : baseOk.headers = [] := rfl

/-- A firing context. -/
def ctxFire : Ctx := { req := { method := str "DELETE" }, base := baseOk }

/-- The always-firing / never-firing predicates (the two live branches). -/
def always : ReqPred := fun _ => true
def never  : ReqPred := fun _ => false

-- the lift lands the REAL refusal record on the firing path, and the seed on the pass
-- path — both branches live, so neither instantiation is vacuous:
#guard serialize (denote (gateWith always methodNotAllowed) ctxFire) = serialize methodNotAllowed
#guard serialize (denote (gateWith never methodNotAllowed) ctxFire) = serialize baseOk

-- ... and the refusal genuinely reaches the WIRE: distinct serialized bytes, and the
-- pass path is byte-identical to the seed.
#guard serialize (denote (gateWith always methodNotAllowed) ctxFire) ≠ serialize baseOk
#guard serialize (denote (gateWith never methodNotAllowed) ctxFire) = serialize baseOk
#guard serialize (denote (gateWith always forbidden403) ctxFire) ≠ serialize baseOk
#guard serialize (denote (gateWith always notModified304) ctxFire) ≠ serialize baseOk
#guard serialize (denote (gateWith always bearerUnauthorized) ctxFire) ≠ serialize baseOk

-- distinct gates produce distinct wire responses (the lift is not collapsing them):
#guard serialize (denote (gateWith always methodNotAllowed) ctxFire)
     ≠ serialize (denote (gateWith always forbidden403) ctxFire)
#guard serialize (denote (gateWith always rateResp429) ctxFire)
     ≠ serialize (denote (gateWith always stickResp429) ctxFire)

-- the if-CHAIN genuinely picks the FIRST firing branch, in order:
#guard serialize (denote (gateChain [(always, badVersion505), (always, notImplemented501),
                          (always, badRequest400)]) ctxFire) = serialize badVersion505
#guard serialize (denote (gateChain [(never, badVersion505), (always, notImplemented501),
                          (always, badRequest400)]) ctxFire) = serialize notImplemented501
#guard serialize (denote (gateChain [(never, badVersion505), (never, notImplemented501),
                          (never, badRequest400)]) ctxFire) = serialize baseOk

-- the payload gate genuinely HALTS (the short-circuit flag is really set):
#guard (denoteStep ctxFire (gateWith always forbidden403)
          { resp := baseOk, halted := false }).halted == true
#guard (denoteStep ctxFire (gateWith never forbidden403)
          { resp := baseOk, halted := false }).halted == false

/-! ## 7. MISFITS — gate-shaped stages the lift does NOT cover, and why

Named, not force-fitted. A forced pin here would be a FALSE pin.

 * **The redirect gate.** Its refusal is `.respond (redirectFor c.req)` — the response
   is a FUNCTION of the request: the `Location` header value is built from the
   request's own (decoded) target. The DSL's `addHeader` carries constant `Bytes`, so
   no `StageProg` term denotes to it for all requests. Covered only at the STATUS
   granularity (`denote_gate_status_general` at the configured redirect code, whose
   refusal family is `fun c => redirectFor c.req`). Closing it needs a
   context-dependent header-value operand in the DSL (`addHeaderF : (Ctx → Bytes) → …`)
   — a real constructor extension, not a proof.

 * **The cache-hit gate.** Its refusal is `.respond (cfg.render e.body)` — the body is
   the stored entry, read out of the lookup. Same reason, same fix.

 * Everything else in §5 has a CONSTANT refusal record (or a constant record per member
   of an explicit family: the challenge value, the carried deny status) and is lifted
   at full-response granularity.

COVERAGE. Gate-shaped deployed stages: 18. Lifted at FULL-response granularity: 16
(§5.2 — 12 single gates, 4 if-chains covering 10 distinct refusal records). Misfit at
full-response granularity: 2 (redirect, cache-hit), both covered at status granularity.
-/

/-! ## 8. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms denote_gate_status_general
#print axioms denoteStep_addHeaders
#print axioms denoteStep_payload
#print axioms denote_gateChain_exact
#print axioms denote_gateChain
#print axioms denote_gateWith
#print axioms gateChain_short_circuits
#print axioms gateChain_compile2_correct
#print axioms lift_methodFilter
#print axioms lift_ipFilter
#print axioms lift_bodyLimit
#print axioms lift_connLimit
#print axioms lift_requestHeadLimit
#print axioms lift_uriTooLong
#print axioms lift_stickTable
#print axioms lift_rate
#print axioms lift_slowloris
#print axioms lift_modifiedSince
#print axioms lift_hostAllowlist
#print axioms lift_jwt
#print axioms lift_basicAuth
#print axioms lift_authRequest
#print axioms lift_forwardAuth
#print axioms lift_framingValidation
#print axioms lift_requestValidation
#print axioms lift_status_all
#print axioms lift_status_forwardDeny

end Pancake.StageLiftGate
