import Reactor.Deploy

/-!
# Proto.Expect100Proven — the DEPLOYED HTTP/1.1 `Expect: 100-continue` behavior

PROVE-WHAT-RUNS for ledger row `h1.expect`. The row was recorded as
"`Expect: 100-continue` (deployed)", implying the deployed dataplane sends an
interim `100 (Continue)` before the final response per RFC 7231 §5.1.1. **That is
not what runs.**

## Ground truth (curl against the running orb, hbox, `--io blocking`, port 8347)

```
> POST / HTTP/1.1
> Host: 127.0.0.1:8347
> Expect: 100-continue
> Content-Length: 16
>
* Done waiting for 100-continue          ← curl timed out; NO interim 100 arrived
* upload completely sent off: 16 bytes
< HTTP/1.1 404 Not Found                  ← the server jumped straight to the final
< Connection: keep-alive
< Server: drorb
```

The deployed serve treats `Expect: 100-continue` as an ordinary request header:
it is parsed but never acted on. `crates/dataplane/src/http.rs`
(`is_complete`/`body_frame`) waits for the whole framed request — head **and**
body — before dispatching, and the serve emits exactly one response. There is no
code path anywhere in `crates/dataplane` that writes a `100 Continue` line
(`grep -rin '100 Continue\|Expect'` over `crates/dataplane/src` finds no Expect
handling and no interim-1xx emission).

This is RFC 7231 §5.1.1-*compliant* — a server MAY answer an
`Expect: 100-continue` with a final status directly instead of the interim `100`
— but the *interim-100* behavior the ledger row claimed is a **false-deployed
row** (the same class as `sse.1`/`dn.1`). This file proves the honest deployed
behavior: the deployed serve emits a **single final (non-1xx, ≥ 200) response**
for such a request — never an interim `100 Continue` — and that this is
independent of whether the request carried the `Expect` header.

The deployed function under proof is `Reactor.Deploy.serveFull` (bytes in → the
proven reactor over `deployConfig` → bytes out; the function `main` runs via
`deployStep`). Its dispatch-path response is `Reactor.Deploy.deployResp`, whose
status is the real application router's (`Reactor.App.handle Reactor.App.demoApp`)
— proven here to be a genuine final status for every route the deployed table can
select. No new axioms; nothing here edits a shared file.
-/

namespace Proto.Expect100Proven

open Proto (Bytes Request)
open Reactor (Response serialize sendsOf)
open Reactor.Deploy (deployResp deploySubs serveFull deployProg deployPlan)
open Reactor.App (demoApp handle responseOfReq responseOfHandler)

/-! ## The deployed router never emits an interim (1xx) status

`Reactor.App.handle Reactor.App.demoApp` is the real application layer the
deployed serve dispatches to (`demoResp`'s `.dispatch` arm). Its response is
`responseOfReq` of the route `Route.Match.bestMatch` chose over the effective
table `demoApp.table`. That table has exactly four entries — `/health`
(`static 200`), `/static` (`staticFile`), `/cgi-bin` (`cgi`), and the host/glob
default — and every one of them is a genuine final (non-1xx, ≥ 200) status. So no
request can drive the deployed router to a 1xx (in particular never a `100
Continue`). -/

/-- **`handle_demoApp_status_final`** — every response the deployed router
produces is a genuine final status (`≥ 200`), never a 1xx interim. The route
`Route.Match.bestMatch` selects is a member of `demoApp.table`
(`bestMatch_mem`); each of the four handlers is status-final
(`Nat.le_refl` for the literal `static 200`; `staticFile_status_final`,
`cgi_status_final`, `hostGlob_status_final` for the others). -/
theorem handle_demoApp_status_final (req : Request) :
    200 ≤ (handle demoApp req).status := by
  obtain ⟨r, hr, heq⟩ := Reactor.App.demoApp_routes_total req
  rw [heq]
  have hmem := Route.Match.bestMatch_mem hr
  simp only [Reactor.App.AppConfig.table, demoApp, List.cons_append, List.nil_append,
    List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact Nat.le_refl 200
  · exact Reactor.App.staticFile_status_final req
  · exact Reactor.App.cgi_status_final _
  · exact Reactor.App.hostGlob_status_final req _

/-! ## The deployed serve emits one final response — no interim 100 -/

/-- The deployed dispatch-path response status is exactly the application
router's, because the deployed header rewrite (`deployProg`) touches only headers
(`deploy_rewrite_status`). -/
theorem deployResp_status_eq (input : Bytes) (req : Request) (rest : List Reactor.RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    (deployResp input).status = (handle demoApp req).status := by
  unfold deployResp
  rw [Reactor.Deploy.deploy_rewrite_status, hsub]
  rfl

/-- The deployed serve emits exactly one response on the dispatch path: when the
FSM produced no response bytes of its own, `serveFull` serializes the single
`deployResp` — there is no informational (1xx) message prefixing it. -/
theorem deployed_serve_one (input : Bytes)
    (hsends : sendsOf (deploySubs input) = []) :
    serveFull input = serialize (deployResp input) := by
  unfold serveFull
  rw [hsends]

/-- **`expect_100_not_deployed`** — the honest replacement for the claimed
`expect_100`. For a request bearing `Expect: 100-continue` that the deployed
reactor dispatches (FSM emitting no bytes of its own), the deployed serve emits
**one** response — `serveFull input = serialize (deployResp input)`, no interim
message ahead of it — and that response's status is a genuine final status
(`≥ 200`), hence **never** the interim `100 Continue`. This is exactly the wire
the live curl showed: `* Done waiting for 100-continue` then a direct
`HTTP/1.1 404`. (The hypotheses are witnessed by that live dispatch: the running
orb answered the Expect-bearing `POST /` with a single `404`.) -/
theorem expect_100_not_deployed (input : Bytes) (req : Request) (rest : List Reactor.RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input = serialize (deployResp input)
    ∧ 200 ≤ (deployResp input).status
    ∧ (deployResp input).status ≠ 100 := by
  refine ⟨deployed_serve_one input hsends, ?_, ?_⟩
  · rw [deployResp_status_eq input req rest hsub]; exact handle_demoApp_status_final req
  · have h := deployResp_status_eq input req rest hsub
    rw [h]
    have hge := handle_demoApp_status_final req
    omega

/-- **`expect_no_100_without_header`** — the same request *without* an
`Expect: 100-continue` header gets the same deployed treatment: one final
(`≥ 200`) response, never an interim `100`. The `_hno` hypothesis records that
the request carries no `Expect` header; the proof does not consult it, which is
precisely the deployed truth — the header is *ignored*, so its presence or
absence makes no difference to whether a `100` is emitted (none is, either way).
Together with `expect_100_not_deployed` this shows the interim-100 behavior is
absent on both header variants. -/
theorem expect_no_100_without_header (input : Bytes) (req : Request)
    (rest : List Reactor.RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (_hno : req.headers.find?
      (fun h => h.1 == "expect".data.map (fun c => c.toNat.toUInt8)) = none) :
    serveFull input = serialize (deployResp input)
    ∧ (deployResp input).status ≠ 100 := by
  obtain ⟨hone, _, hne⟩ := expect_100_not_deployed input req rest hsends hsub
  exact ⟨hone, hne⟩

/-! ## Non-vacuity

`handle_demoApp_status_final` is unconditional (a universally-quantified real
inequality, not a tautology): the deployed router is final-status on *every*
request. The two deployed theorems are conditional on the request being
dispatched (`hsub`) with no FSM send (`hsends`); those hypotheses are inhabited —
the live orb dispatched the Expect-bearing `POST /` to a single `404` (see the
curl in the module header), so the conditional facts are not vacuous. The status
conclusions are strict: `100 < 200 ≤ (deployResp input).status`, so
`(deployResp input).status ≠ 100` genuinely rules out the interim `100 Continue`
the ledger row had claimed. -/

/-- A witness that the final-status bound strictly excludes the interim `100`:
no `Nat` is both `≥ 200` and `= 100`. -/
example (n : Nat) (h : 200 ≤ n) : n ≠ 100 := by omega

end Proto.Expect100Proven
