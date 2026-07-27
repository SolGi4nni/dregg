import Reactor.RespTransform

/-!
# EarlyHintsCorrect — RFC 8297 (HTTP 103 Early Hints) correctness by refinement

This upgrades the 103 Early-Hints lane from a SAFETY property (an ordering
invariant stated in the implementation's own vocabulary) to a CORRECTNESS
result: the DEPLOYED emission function refines an INDEPENDENT specification of
the wire behaviour RFC 8297 mandates, written over raw HTTP status codes with
no reference to the implementation's `State`/`Msg`/`step` model.

## The specification (independent, from the standard)

RFC 8297, "An HTTP Status Code for Indicating Hints", §2:

  > The 103 (Early Hints) informational status code indicates to the client
  > that the server is likely to send a final response with the header fields
  > included in the informational response. ... A server MAY send one or more
  > 103 (Early Hints) responses prior to sending a final response. ... The 103
  > (Early Hints) response is intended to be used ... to allow the user agent
  > to preload resources while the server is still preparing the final
  > response.

103 is a member of the 1xx (Informational) class. RFC 9110, "HTTP Semantics",
§15.2 (Informational 1xx) is the controlling text for how such interim
responses sit on the wire:

  > The 1xx (Informational) class of status code indicates an interim response
  > for communicating connection status or request progress prior to
  > completing the requested action and sending a final response. ... A client
  > MUST be able to parse one or more 1xx responses received prior to a final
  > response, even if the client does not expect one.

and §15 fixes the class boundaries: 1xx = 100..199 (interim), and every
response finishes with exactly one FINAL status code in 2xx..5xx (>= 200).

Distilled to the wire, a completed HTTP/1.1 response transaction is therefore a
(possibly empty) run of interim (1xx) status codes — among which a 103 may
appear — followed by EXACTLY ONE final (non-1xx) status code. Two consequences,
each of which the spec below makes a rejectable proposition:

  * a 103 is never the terminal response (the transaction always ends with the
    one final, non-1xx code), and
  * no interim (1xx) response — in particular no 103 — appears AFTER the final.

`EarlyHintsSpec` below states exactly this over `List Nat` (the wire sequence of
status codes) and mentions nothing from `EarlyHints`/`Reactor`.

## The refinement (against the deployed function)

`Reactor.RespTransform` is where the deployed serve emits early hints: a route
declaring preload `hints` runs the REAL `EarlyHints.run` from `building` over
`hintActions hints (deployedFinal input)` — one `emitInfo` per hint, then one
`emitFinal` carrying `deployedFinal input`, whose status/body ARE the deployed
response `serveFull`/`deployResp` serialize (`Arena.Orb.main`'s dispatch path).

`statusOf` projects each emitted `Msg` onto its wire status code (every `103`
informational becomes `103`; the final becomes its own status). The refinement
theorem `deployed_run_refines_spec` proves that projected code sequence is a
`CompletedTransaction` in the sense above — for ALL inputs and ALL hint lists.

The one property the `EarlyHints` model does NOT itself enforce — that the
final's status is genuinely non-1xx (>= 200), RFC 9110 §15.4 — was previously
carried as an explicit hypothesis on the deployed response's status. It is now
DISCHARGED: `deployedFinal_status_final` proves the deployed final's status is
non-1xx for every input (the header rewrite carries `demoResp`'s status through,
and every branch of `demoResp`/`App.handle` over the demo table is non-1xx), so
`deployed_run_refines_spec` holds UNCONDITIONALLY and a 1xx terminal is
impossible on the deployed path (`deployed_final_not_interim`,
`deployed_final_not_103`) — not merely a caller obligation. The generic model
lemma `run_refines_spec` still takes the non-1xx hypothesis because an arbitrary
`EarlyHints.Final` can hold any `status`; the deployed instantiation removes it
by proof.
-/

namespace EarlyHintsSpec

/-- RFC 9110 §15.2 / §15: the 1xx (Informational) class — an *interim* status
code (100..199). -/
def isInterim (code : Nat) : Prop := 100 ≤ code ∧ code ≤ 199

/-- RFC 9110 §15: a *final* status code is any non-1xx response (2xx..5xx),
i.e. `>= 200`. Exactly one such code terminates the transaction. -/
def isFinal (code : Nat) : Prop := 200 ≤ code

/-- RFC 8297 §2: the 103 (Early Hints) status code. -/
def is103 (code : Nat) : Prop := code = 103

instance : DecidablePred isInterim := fun c => inferInstanceAs (Decidable (100 ≤ c ∧ c ≤ 199))
instance : DecidablePred isFinal := fun c => inferInstanceAs (Decidable (200 ≤ c))

/-- RFC 8297 §2's 103 is a member of the 1xx interim class. -/
theorem is103_isInterim {code : Nat} (h : is103 code) : isInterim code := by
  subst h; exact ⟨by decide, by decide⟩

/-- No interim code is a final code (the classes 100..199 and >=200 are
disjoint). In particular a 103 is never a final status. -/
theorem isInterim_not_isFinal {code : Nat} (h : isInterim code) : ¬ isFinal code := by
  intro hf; exact absurd (Nat.le_trans hf h.2) (by decide)

/-- **The specification.** A completed HTTP response transaction (RFC 8297 §2 +
RFC 9110 §15.2): a run of interim (1xx) status codes — a 103 may appear among
them — followed by EXACTLY ONE final (non-1xx) status code. Because the sole
tail element is final (>=200) and every earlier element is interim (<=199), a
103 can be neither the terminal code nor placed after the final. -/
def CompletedTransaction (codes : List Nat) : Prop :=
  ∃ interim final,
    codes = interim ++ [final] ∧ (∀ c ∈ interim, isInterim c) ∧ isFinal final

/-! ### The spec genuinely discriminates (non-vacuity of the SPEC side) -/

/-- In any completed transaction, the sole final is the LAST wire code, so a
sequence whose terminal code is interim (`< 200`) — a 103 sitting where the
final must be, whether because 103 was made terminal or emitted after the
final — is rejected. -/
theorem not_completed_of_getLast_lt {codes : List Nat} {last : Nat}
    (hlast : codes.getLast? = some last) (hlt : last < 200) :
    ¬ CompletedTransaction codes := by
  rintro ⟨interim, final, heq, _, hfin⟩
  have hgl : codes.getLast? = some final := by rw [heq]; simp
  rw [hlast] at hgl
  have hlf : last = final := Option.some.inj hgl
  have hfin' : 200 ≤ final := hfin
  omega

/-- A lone 103 is NOT a completed transaction: a 103 may never be the terminal
response. (Forces the "103 made terminal" mutant to fail.) -/
theorem not_completed_lone_103 : ¬ CompletedTransaction [103] :=
  not_completed_of_getLast_lt (last := 103) (by decide) (by decide)

/-- A 103 placed AFTER the final is NOT a completed transaction: its terminal
code is a 103, where a non-1xx final is required. (Forces the "103 emitted after
the final" mutant to fail.) -/
theorem not_completed_103_after_final : ¬ CompletedTransaction [200, 103] :=
  not_completed_of_getLast_lt (last := 103) (by decide) (by decide)

/-- The unmutated 103-then-final wire sequence IS accepted (non-vacuity: the
spec is satisfiable by exactly the shape the deployed path produces). -/
theorem completed_103_then_200 : CompletedTransaction [103, 200] :=
  ⟨[103], 200, rfl, by intro c hc; simp at hc; subst hc; exact ⟨by decide, by decide⟩,
    by decide⟩

end EarlyHintsSpec

namespace EarlyHintsCorrect

open EarlyHintsSpec
open Reactor.RespTransform (hintActions deployedFinal run_hintActions toFinal_status)
open Reactor.Deploy (deployResp)

/-! ### The deployed final is provably non-1xx (RFC 9110 §15.4), DISCHARGED

The one property `EarlyHints` alone does not enforce — that the committed final
carries a genuine non-1xx status — is no longer carried as a hypothesis on the
deployed refinement. It is PROVED here: the deployed final's status IS the
deployed response's status (`deployResp`, via `toFinal_status`), which the header
rewrite carries through unchanged from the demo application response
(`demoResp`); and every branch `demoResp` can take is a non-1xx code — a `400` on
the malformed path, or `App.handle`'s routed response, whose status is
`responseOfHandler` of a route drawn from the demo table (`bestMatch_mem`): a
`200` (`/health`, `/static`), a `404` (default), or the `502` proxy placeholder.
So a 1xx terminal is not merely rejected by the spec — it is IMPOSSIBLE on the
deployed path. -/

/-- Every handler the demo route table can select answers with a non-1xx status,
**request-aware**. The demo table's handlers are `static 200`, the real
`staticFile` route (whose `StaticFile.toResponse` statuses are `200/206/304/416/404`),
a `cgi` route (whose script status the app layer clamps `< 200 → 502`), and the
`static 404` default. Each is `≥ 200` — proved per handler (the `staticFile`/`cgi`
payloads are opaque to the kernel, so this is not a `decide`). -/
theorem demoApp_table_status_final (req : Proto.Request) :
    ∀ r ∈ Reactor.demoAppConfig.table,
      isFinal (Reactor.App.responseOfReq req r.handler).status := by
  intro r hr
  show 200 ≤ _
  -- The effective table is the three author routes plus the folded default.
  have ht : Reactor.demoAppConfig.table =
      [ ⟨Route.Match.Pat.exact ["health"], Reactor.App.Handler.static 200 "ok".toUTF8.toList⟩,
        ⟨Route.Match.Pat.«prefix» ["static"], Reactor.App.Handler.staticFile⟩,
        ⟨Route.Match.Pat.«prefix» ["cgi-bin"], Reactor.App.Handler.cgi "conformance/cgi-bin/hello"⟩,
        ⟨Route.Match.Pat.default, Reactor.App.Handler.hostGlob Reactor.App.demoVhBlocks⟩ ] := rfl
  rw [ht] at hr
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (by decide : (200 : Nat) ≤ 200)                       -- /health  static 200
  · exact Reactor.App.staticFile_status_final req                -- /static  staticFile
  · exact Reactor.App.cgi_status_final _                         -- /cgi-bin cgi (clamped)
  · exact Reactor.App.hostGlob_status_final req _                -- default  host/glob (clamped)

/-- `App.handle` over the demo config answers with a non-1xx status: it returns the
request-aware `responseOfReq` of a route the REAL `Route.Match.bestMatch` drew from
the table (`bestMatch_mem`), and every such handler is non-1xx
(`demoApp_table_status_final`). -/
theorem handle_demoApp_status_final (req : Proto.Request) :
    isFinal (Reactor.App.handle Reactor.demoAppConfig req).status := by
  obtain ⟨r, hbest, hresp⟩ := Reactor.App.app_routes_total Reactor.demoAppConfig req
  rw [hresp]
  exact demoApp_table_status_final req r (Route.Match.bestMatch_mem hbest)

/-- The demo response for any submission list is non-1xx: the malformed path is a
`400`; a dispatch is `App.handle`'s routed (non-1xx) response; any other head is
stripped and the tail is answered the same way. -/
theorem demoResp_status_final (subs : List Reactor.RingSubmission) :
    isFinal (Reactor.demoResp subs).status := by
  induction subs with
  | nil => decide
  | cons a rest ih => cases a <;> first | exact ih | exact handle_demoApp_status_final _

/-- **The deployed response's status is a genuine final (non-1xx).** The header
rewrite carries the demo response's status through unchanged
(`deploy_rewrite_status`), and that status is non-1xx for every input. This
DISCHARGES the RFC 9110 §15.4 obligation the `EarlyHints` model delegates to its
caller — on the deployed path it is a theorem, not a hypothesis. -/
theorem deployResp_status_final (input : Proto.Bytes) :
    isFinal (deployResp input).status := by
  unfold Reactor.Deploy.deployResp
  rw [Reactor.Deploy.deploy_rewrite_status]
  exact demoResp_status_final _

/-- The deployed final's status is non-1xx (the `deployedFinal` view carries
`deployResp`'s status through, `toFinal_status`). -/
theorem deployedFinal_status_final (input : Proto.Bytes) :
    isFinal (deployedFinal input).status := by
  rw [show (deployedFinal input).status = (deployResp input).status from
    toFinal_status (deployResp input)]
  exact deployResp_status_final input

/-- Project an emitted message onto the HTTP status code it puts on the wire:
every `103` informational hint carries status `103`; the final response carries
its own status. This is the wire view the RFC specification is stated over. -/
def statusOf : EarlyHints.Msg → Nat
  | .info _ => 103
  | .final r => r.status

/-- **The deployed wire sequence.** Projecting the messages the deployed
emission actually produces — `EarlyHints.run` from `building` over the deployed
`hintActions hints f` — onto their status codes yields exactly: one `103` per
declared hint, in order, then the final's status. Derived from the REAL
`Reactor.RespTransform.run_hintActions`, not a re-statement. -/
theorem deployed_status_seq (hints : List EarlyHints.Info) (f : EarlyHints.Final) :
    ((EarlyHints.run .building (hintActions hints f)).2).map statusOf
      = hints.map (fun _ => (103 : Nat)) ++ [f.status] := by
  have h2 : (EarlyHints.run .building (hintActions hints f)).2
      = hints.map EarlyHints.Msg.info ++ [EarlyHints.Msg.final f] :=
    congrArg Prod.snd (run_hintActions hints f)
  rw [h2, List.map_append, List.map_map]
  rfl

/-- **Core refinement, generic over the final.** For any declared preload
`hints` and any final response `f` whose status is genuinely non-1xx, the
deployed emission's projected status sequence is a `CompletedTransaction` in the
independent RFC 8297 / RFC 9110 sense: the 103 hints, in order, strictly precede
EXACTLY ONE final status, and no interim response follows the final.

This binds the deployed `EarlyHints.run ∘ hintActions` — the function the serve
path invokes — not a proof-file re-model. The `hf` hypothesis is precisely the
RFC 9110 §15.4 well-formedness obligation; for the DEPLOYED final it is
discharged by `deployedFinal_status_final`, so `deployed_run_refines_spec` needs
no such hypothesis. It survives here only because this lemma is generic over an
arbitrary `EarlyHints.Final`. -/
theorem run_refines_spec (hints : List EarlyHints.Info) (f : EarlyHints.Final)
    (hf : isFinal f.status) :
    CompletedTransaction (((EarlyHints.run .building (hintActions hints f)).2).map statusOf) := by
  refine ⟨hints.map (fun _ => (103 : Nat)), f.status, deployed_status_seq hints f, ?_, hf⟩
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨_, _, rfl⟩ := hc
  exact ⟨by decide, by decide⟩

/-- **Exactly one final on the deployed wire.** Under the same non-1xx
obligation, the projected sequence contains PRECISELY ONE final (non-1xx) status
code — the 103 hints are all interim, the sole final is the tail. This is the
"exactly one final" half of RFC 8297 §2 made quantitative. -/
theorem deployed_exactly_one_final (hints : List EarlyHints.Info) (f : EarlyHints.Final)
    (hf : isFinal f.status) :
    (((EarlyHints.run .building (hintActions hints f)).2).map statusOf).countP
        (fun c => decide (isFinal c)) = 1 := by
  rw [deployed_status_seq hints f, List.countP_append]
  have hhints : (hints.map (fun _ => (103 : Nat))).countP (fun c => decide (isFinal c)) = 0 := by
    rw [List.countP_eq_zero]
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨_, _, rfl⟩ := hc
    simp [isFinal]
  have htail : ([f.status]).countP (fun c => decide (isFinal c)) = 1 := by
    simp [List.countP_cons, hf]
  rw [hhints, htail]

/-- **The deployed refinement, at the real deployed response — UNCONDITIONAL.**
Instantiates the core refinement at `deployedFinal input` — the `EarlyHints.Final`
whose status and body ARE `serveFull`/`deployResp`'s deployed response on
`Arena.Orb.main`'s dispatch path. For every request `input` and every declared
preload `hints`, the emitted 103-then-final wire sequence is an RFC 8297 completed
transaction. The former non-1xx hypothesis is now discharged internally by
`deployedFinal_status_final`, so the refinement binds the deployed function with
no carried obligation. -/
theorem deployed_run_refines_spec (input : Proto.Bytes) (hints : List EarlyHints.Info) :
    CompletedTransaction
      (((EarlyHints.run .building (hintActions hints (deployedFinal input))).2).map statusOf) :=
  run_refines_spec hints (deployedFinal input) (deployedFinal_status_final input)

/-- Companion: exactly one final at the real deployed response — UNCONDITIONAL. -/
theorem deployed_run_one_final (input : Proto.Bytes) (hints : List EarlyHints.Info) :
    (((EarlyHints.run .building (hintActions hints (deployedFinal input))).2).map statusOf).countP
        (fun c => decide (isFinal c)) = 1 :=
  deployed_exactly_one_final hints (deployedFinal input) (deployedFinal_status_final input)

/-! ## Non-vacuity, mechanically checked against the deployed function

The two mutants RFC 8297 forbids, evaluated on the REAL deployed `statusOf` ∘
`EarlyHints.run` ∘ `hintActions`, land OUTSIDE the spec — the refinement above
therefore has real content. Both use one declared hint and a well-formed final
`200`. -/

/-- A well-formed deployed run of one hint then a `200` final projects to the
accepted wire sequence `[103, 200]`. -/
theorem deployed_witness_ok :
    ((EarlyHints.run .building
        (hintActions [{ headers := [] }] { status := 200, headers := [], body := [] })).2).map
        statusOf = [103, 200] := by
  rw [deployed_status_seq]; rfl

/-- The "103 made terminal" mutant — the deployed run with the final's status
demoted to a 1xx `103` — projects to `[103]` (one hint-free final of status
103), whose terminal code is `103 < 200`; the spec REJECTS it. -/
theorem mutant_terminal_103_rejected :
    ¬ CompletedTransaction
        (((EarlyHints.run .building
            (hintActions [] { status := 103, headers := [], body := [] })).2).map statusOf) := by
  rw [deployed_status_seq]
  simp only [List.map_nil, List.nil_append]
  exact not_completed_of_getLast_lt (last := 103) (by decide) (by decide)

/-- The "103 emitted AFTER the final" mutant is caught at the spec level by
`EarlyHintsSpec.not_completed_103_after_final`: the wire `[200, 103]` is
rejected. The deployed `EarlyHints.run` structurally cannot even produce it —
`run_committed_nil` drops every action once committed — so this ordering
violation is unreachable on the deployed path, not merely rejected. -/
theorem after_final_mutant_note : ¬ CompletedTransaction [200, 103] :=
  not_completed_103_after_final

/-! ### The 1xx-final is impossible on the deployed path (not merely rejected)

The mutants above show the SPEC rejects a 1xx terminal. The DEPLOYED path goes
further: its final can never *be* a 1xx, because `deployedFinal_status_final`
proves its status non-1xx for all inputs. So the "103 made terminal" mutant is
not a reachable deployed run whose projection the spec then rejects — it is
unconstructible from the deployed final at all. -/

/-- The deployed final is never an interim (1xx) response — a would-be 1xx
terminal is impossible on the deployed path. -/
theorem deployed_final_not_interim (input : Proto.Bytes) :
    ¬ isInterim (deployedFinal input).status :=
  fun hi => isInterim_not_isFinal hi (deployedFinal_status_final input)

/-- In particular the deployed final is never a 103: the informational status can
never sit in the terminal position on the deployed path. -/
theorem deployed_final_not_103 (input : Proto.Bytes) :
    ¬ is103 (deployedFinal input).status :=
  fun h => deployed_final_not_interim input (is103_isInterim h)

end EarlyHintsCorrect
