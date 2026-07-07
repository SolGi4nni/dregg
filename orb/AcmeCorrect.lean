/-
AcmeCorrect — an independent RFC 8555 specification of the ACME order and
challenge state machines, and a refinement proof that the deployed `Acme` FSM
(`Acme.Challenge.step`, `Acme.Challenge.validateStep`, `Acme.orderStep`,
`Acme.orderRun`) obeys it.

## What is specified, and from where

The specification below is written *from RFC 8555* — the "Status Changes" state
machine (§7.1.6), the challenge-response protocol (§7.5), and the identifier
validation challenges (§8) — WITHOUT reference to the `Acme` step functions. It
is a labelled transition RELATION, one constructor per RFC-permitted move, so the
constructors read directly against the RFC prose:

  * **Challenge** (RFC 8555 §7.1.6 challenge object, §7.5.1, §8.2). A challenge
    object is created "pending". It moves to "processing" when the client
    responds (§7.5.1: the client POSTs the challenge URL to tell the server it
    is ready). The server then validates (§8): "If validation is successful, the
    challenge moves to the 'valid' state; if there is an error … the challenge
    moves to the 'invalid' state." `valid`/`invalid` are final.

  * **Authorization ↔ challenge bridge** (RFC 8555 §7.1.6, authorization object).
    "If one of the challenges listed in the authorization transitions to the
    'valid' state, then the authorization also changes to the 'valid' state."
    So an authorization is valid *exactly* when its challenge is validated — the
    order-level label `authzResult i ok` carries that challenge outcome.

  * **Order** (RFC 8555 §7.1.6 order object, §7.4). "Order objects are created
    in the 'pending' state. Once all of the authorizations … are in the 'valid'
    state, the order moves to the 'ready' state. The order moves to the
    'processing' state after the client submits a request to the order's
    'finalize' URL … Once the certificate is issued, the order enters the
    'valid' state. If an error occurs at any of these stages, the order moves to
    the 'invalid' state." §7.4 further: finalize is honoured only for a `ready`
    order (else `orderNotReady`).

The load-bearing normative facts, stated as spec constructors and their
consequences: an order reaches `ready` only with **all** authorizations valid;
`finalize` advances only a `ready` order (never a `pending` one); an order
reaches `valid` only from `processing`; a challenge reaches `valid` only by a
*successful* validation from `processing`.

## What is proven about the deployed functions

`chalStep_refines` / `orderStep_refines` show every transition the *deployed*
`Acme.Challenge.step` / `Acme.orderStep` makes is a transition the RFC relation
permits. `deployed_run_is_rfc_trace` lifts this to whole event sequences run by
`Acme.orderRun` from `Acme.Order.fresh` — the fold the deployed ACME issuance
executes. Composing with the spec-only meaningfulness lemma
`rfcSteps_valid_needs_allValid` re-derives, *through the independent spec*, that
no order the deployed FSM drives to `valid` skipped an authorization.

Non-vacuity is discharged three ways: the RFC relation refuses to finalize a
pending order (`rfc_no_finalize_from_pending`) and refuses a challenge into
`valid` without a successful validation (`rfc_chal_into_valid`), and the deployed
functions are shown to agree (`deployed_no_finalize_from_pending`,
`deployed_no_validate_before_respond`) — so the refinement is not against a
vacuously-total relation.

Everything discharges on the core axioms only.
-/

import Acme.Order
import Acme.Challenge

namespace AcmeCorrect

open Acme

/-! ## 1. Independent labels (RFC 8555 §7.5, §7.4, §8)

The RFC's client/server actions, named independently of the `Acme` event types.
`ofChalEvent` / `ofOrderEvent` map the deployed event alphabet onto these labels;
they are plain renamings, hiding no behaviour. -/

/-- Challenge protocol actions (RFC 8555 §7.5.1 respond; §8 validate). -/
inductive ChalLabel where
  /-- §7.5.1: the client POSTs the challenge URL, signalling it is ready. -/
  | clientResponds
  /-- §8: the server's validation of the challenge succeeded. -/
  | validationSucceeds
  /-- §8: the server's validation of the challenge failed. -/
  | validationFails
deriving DecidableEq, Repr

/-- Order protocol actions (RFC 8555 §7.1.6, §7.4). -/
inductive OrderLabel where
  /-- §7.1.6 authorization object: authorization `i`'s challenge was validated
  with result `ok` (the challenge→authorization bridge). -/
  | authzResolved (i : Nat) (ok : Bool)
  /-- §7.4: the client POSTs the order's finalize URL with a CSR. -/
  | finalizeOrder
  /-- §7.1.6: the CA issued the certificate. -/
  | certIssued
  /-- §7.1.6: certificate issuance failed. -/
  | certFailed
deriving DecidableEq, Repr

/-- Deployed challenge events → RFC challenge labels. -/
def ofChalEvent : ChalEvent → ChalLabel
  | .respond => .clientResponds
  | .validated true => .validationSucceeds
  | .validated false => .validationFails

/-- Deployed order events → RFC order labels. -/
def ofOrderEvent : OrderEvent → OrderLabel
  | .authzResult i ok => .authzResolved i ok
  | .finalize => .finalizeOrder
  | .issued => .certIssued
  | .issuanceFailed => .certFailed

/-! ## 2. The RFC challenge relation (RFC 8555 §7.1.6, §7.5.1, §8)

One constructor per RFC-permitted move. The only edges into `valid`/`invalid`
are the successful/failed validation of a `processing` challenge; terminal
states are absorbing; an action that does not apply to the current state is a
no-op (the client re-responding to a challenge already processing, or a
validation result arriving before the client has responded). -/

inductive RfcChalStep : ChalStatus → ChalLabel → ChalStatus → Prop where
  /-- §7.5.1: client responds ⇒ pending → processing. -/
  | respond : RfcChalStep .pending .clientResponds .processing
  /-- §8: successful validation ⇒ processing → valid. -/
  | succeed : RfcChalStep .processing .validationSucceeds .valid
  /-- §8: failed validation ⇒ processing → invalid. -/
  | fail : RfcChalStep .processing .validationFails .invalid
  /-- §7.1.6: a valid challenge is final (absorbing). -/
  | validAbsorb (l : ChalLabel) : RfcChalStep .valid l .valid
  /-- §7.1.6: an invalid challenge is final (absorbing). -/
  | invalidAbsorb (l : ChalLabel) : RfcChalStep .invalid l .invalid
  /-- A validation result before the client has responded is ignored. -/
  | ignoreEarlyValidation (b : Bool) :
      RfcChalStep .pending (if b then .validationSucceeds else .validationFails) .pending
  /-- The client re-responding to a challenge already processing is ignored. -/
  | ignoreLateRespond : RfcChalStep .processing .clientResponds .processing

/-- **No-bypass (spec side).** The RFC relation admits a step into `valid` only
from `valid` itself or by a *successful validation* of a `processing` challenge.
There is no other door — in particular none from `pending`. -/
theorem rfc_chal_into_valid {s : ChalStatus} {l : ChalLabel}
    (h : RfcChalStep s l .valid) :
    s = .valid ∨ (s = .processing ∧ l = .validationSucceeds) := by
  cases h with
  | succeed => exact Or.inr ⟨rfl, rfl⟩
  | validAbsorb => exact Or.inl rfl

/-- **Non-vacuity: validating without a responded challenge fails.** The RFC
relation has *no* edge sending a `pending` challenge to `valid`. -/
theorem rfc_no_validate_from_pending (l : ChalLabel) :
    ¬ RfcChalStep .pending l .valid := by
  intro h
  rcases rfc_chal_into_valid h with h | ⟨h, _⟩ <;> simp at h

/-! ## 3. Deployed challenge FSM refines the RFC challenge relation

`Acme.Challenge.step` and `Acme.Challenge.validateStep` are the functions the
issuance path runs; we bind them directly. -/

/-- **Refinement (challenge).** Every transition the deployed `Challenge.step`
takes is one the RFC relation permits, under the label renaming. -/
theorem chalStep_refines (c : Challenge) (e : ChalEvent) :
    RfcChalStep c.status (ofChalEvent e) (c.step e).status := by
  obtain ⟨ty, tok, dom, st⟩ := c
  cases st <;> cases e with
  | respond => first | exact .respond | exact .ignoreLateRespond
                     | exact .validAbsorb _ | exact .invalidAbsorb _
  | validated b =>
      cases b <;>
        first
          | exact .succeed | exact .fail
          | exact .ignoreEarlyValidation true | exact .ignoreEarlyValidation false
          | exact .validAbsorb _ | exact .invalidAbsorb _

/-- **Non-vacuity (deployed).** The deployed FSM refuses to validate a challenge
the client has not yet responded to: a `pending` challenge receiving any
validation result stays `pending`, never `valid`. -/
theorem deployed_no_validate_before_respond
    (ty : ChallengeType) (tok dom : Bytes) (ok : Bool) :
    ((⟨ty, tok, dom, .pending⟩ : Challenge).step (.validated ok)).status
      = .pending := by
  cases ok <;> rfl

/-- The deployed `validateStep` reaches `valid` only on a successful validator
result — bound to `Acme.Challenge.validateStep`, the seam that reads the CA's
http-01/dns-01 verdict (§8.3/§8.4). -/
theorem deployed_validate_needs_success {validate : Challenge → Bool}
    {c : Challenge} (hp : c.status = .processing)
    (hv : (c.validateStep validate).status = .valid) : validate c = true :=
  Acme.validateStep_valid_needs_success hp hv

/-! ## 4. The RFC order relation (RFC 8555 §7.1.6, §7.4)

The order state is its authorization statuses and its own status. Authorization
bookkeeping is constrained only to be **monotone** — a terminal (valid/invalid)
authorization is never rewritten (§7.1.6: those statuses are final) — leaving the
exact list mechanics to the implementation; the normative content is carried by
the status gates. -/

/-- Every terminal authorization is preserved exactly: the RFC's "valid/invalid
authorizations are final". Also length-preserving (no authorization appears or
vanishes mid-order). -/
def AuthzMonotone (as as' : List AuthzStatus) : Prop :=
  as.length = as'.length ∧
    ∀ (i : Nat) (s : AuthzStatus), as[i]? = some s → s ≠ .pending → as'[i]? = some s

/-- Which (status, label) pairs are productive RFC edges. Everything else is a
no-op (the `stutter` guard below). -/
def OrderApplicable : OrderStatus → OrderLabel → Bool
  | .pending, .authzResolved _ _ => true
  | .ready, .finalizeOrder => true
  | .processing, .certIssued => true
  | .processing, .certFailed => true
  | _, _ => false

/-- Order transitions permitted by RFC 8555. -/
inductive RfcOrderStep : Order → OrderLabel → Order → Prop where
  /-- §7.1.6: resolving an authorization while pending, not yet all valid and none
  failed ⇒ the order stays pending (authz list updated monotonically). -/
  | authzStay {as as' : List AuthzStatus} {i : Nat} {ok : Bool}
      (hmono : AuthzMonotone as as')
      (hnotAll : allValid as' = false)
      (hnotInv : anyInvalid as' = false) :
      RfcOrderStep ⟨as, .pending⟩ (.authzResolved i ok) ⟨as', .pending⟩
  /-- §7.1.6: "Once all of the authorizations … are 'valid', the order moves to
  'ready'." The gate: `allValid as'`. -/
  | authzReady {as as' : List AuthzStatus} {i : Nat} {ok : Bool}
      (hmono : AuthzMonotone as as')
      (hall : allValid as' = true) :
      RfcOrderStep ⟨as, .pending⟩ (.authzResolved i ok) ⟨as', .ready⟩
  /-- §7.1.6: an authorization failing sends the order to `invalid`. -/
  | authzInvalid {as as' : List AuthzStatus} {i : Nat} {ok : Bool}
      (hmono : AuthzMonotone as as')
      (hinv : anyInvalid as' = true) :
      RfcOrderStep ⟨as, .pending⟩ (.authzResolved i ok) ⟨as', .invalid⟩
  /-- §7.4: finalize advances **only a `ready` order** to `processing`; a `ready`
  order has all authorizations valid (§7.1.6). -/
  | finalize {as : List AuthzStatus} (hall : allValid as = true) :
      RfcOrderStep ⟨as, .ready⟩ .finalizeOrder ⟨as, .processing⟩
  /-- §7.1.6: certificate issued ⇒ processing → valid. -/
  | issued {as : List AuthzStatus} :
      RfcOrderStep ⟨as, .processing⟩ .certIssued ⟨as, .valid⟩
  /-- §7.1.6: issuance failed ⇒ processing → invalid. -/
  | issueFail {as : List AuthzStatus} :
      RfcOrderStep ⟨as, .processing⟩ .certFailed ⟨as, .invalid⟩
  /-- An action that does not apply to the current status is a no-op (finalize on
  a pending order → `orderNotReady`, §7.4; issuance results before finalize;
  further authz results after `ready`; and the absorbing terminal states). -/
  | stutter {o : Order} {l : OrderLabel} (h : OrderApplicable o.status l = false) :
      RfcOrderStep o l o

/-! ### Spec-side non-vacuity: the RFC relation is a proper subrelation -/

/-- **Non-vacuity: no finalize from a pending order.** The RFC relation has no
edge taking a `pending` order to `processing` under `finalizeOrder`; §7.4's
`orderNotReady` is a no-op, not an advance. -/
theorem rfc_no_finalize_from_pending (as : List AuthzStatus) :
    ¬ RfcOrderStep ⟨as, .pending⟩ .finalizeOrder ⟨as, .processing⟩ := by
  intro h
  cases h

/-! ## 5. The deployed order FSM refines the RFC order relation

We bind `Acme.orderStep` (the deployed step) directly. The one place the deployed
step relies on a global invariant rather than a local check is `finalize`: it
advances any `ready` order to `processing` without re-inspecting the authz list,
because a `ready` order is *already* all-valid. That invariant is `Acme.Order.wf`,
established for every reachable order by `Acme.Order.fresh_wf` + `Acme.orderStep_wf`;
we take it as the refinement hypothesis, exactly as the deployed reachability
guarantees it. -/

/-- `setAuthzAt` is monotone: it only ever overwrites a `pending` entry, so every
terminal authorization survives unchanged and the length is preserved. -/
theorem setAuthzAt_monotone (as : List AuthzStatus) (i : Nat) (ok : Bool) :
    AuthzMonotone as (setAuthzAt as i ok) := by
  rw [setAuthzAt]
  cases hi : as[i]? with
  | none => simp only [hi]; exact ⟨rfl, fun _ _ hj _ => hj⟩
  | some st =>
    cases st with
    | pending =>
        simp only [hi]
        refine ⟨(List.length_set ..).symm, ?_⟩
        intro j s hj hne
        by_cases hji : j = i
        · exfalso; subst hji; rw [hi] at hj; cases hj; exact hne rfl
        · rw [List.getElem?_set_ne (fun a => hji a.symm)]; exact hj
    | valid => simp only [hi]; exact ⟨rfl, fun _ _ hj _ => hj⟩
    | invalid => simp only [hi]; exact ⟨rfl, fun _ _ hj _ => hj⟩

/-- **Refinement (order).** Every transition the deployed `Acme.orderStep` takes
from a well-formed (reachable) order is one the RFC relation permits, under the
label renaming. The `wf` hypothesis discharges the `finalize` gate; every
reachable order satisfies it (`Acme.orderStep_wf`). -/
theorem orderStep_refines {o : Order} (hwf : o.wf) (e : OrderEvent) :
    RfcOrderStep o (ofOrderEvent e) (orderStep o e) := by
  obtain ⟨as, st⟩ := o
  cases st with
  | pending =>
    cases e with
    | authzResult i ok =>
        have hmono := setAuthzAt_monotone as i ok
        show RfcOrderStep ⟨as, .pending⟩ (.authzResolved i ok)
            (Order.recompute ⟨setAuthzAt as i ok, .pending⟩)
        unfold Order.recompute
        by_cases hv : allValid (setAuthzAt as i ok) = true
        · rw [if_pos hv]; exact RfcOrderStep.authzReady hmono hv
        · rw [if_neg hv]
          by_cases hbad : anyInvalid (setAuthzAt as i ok) = true
          · rw [if_pos hbad]; exact RfcOrderStep.authzInvalid hmono hbad
          · rw [if_neg hbad]
            exact RfcOrderStep.authzStay hmono (by simpa using hv) (by simpa using hbad)
    | finalize => exact RfcOrderStep.stutter rfl
    | issued => exact RfcOrderStep.stutter rfl
    | issuanceFailed => exact RfcOrderStep.stutter rfl
  | ready =>
    cases e with
    | authzResult i ok => exact RfcOrderStep.stutter rfl
    | finalize => exact RfcOrderStep.finalize (hwf (Or.inl rfl))
    | issued => exact RfcOrderStep.stutter rfl
    | issuanceFailed => exact RfcOrderStep.stutter rfl
  | processing =>
    cases e with
    | authzResult i ok => exact RfcOrderStep.stutter rfl
    | finalize => exact RfcOrderStep.stutter rfl
    | issued => exact RfcOrderStep.issued
    | issuanceFailed => exact RfcOrderStep.issueFail
  | valid => cases e <;> exact RfcOrderStep.stutter rfl
  | invalid => cases e <;> exact RfcOrderStep.stutter rfl

/-- **Non-vacuity (deployed).** The deployed FSM refuses to finalize a pending
order: `orderStep` on a `pending` order under `finalize` stays `pending`, never
`processing` — matching `rfc_no_finalize_from_pending`. -/
theorem deployed_no_finalize_from_pending (as : List AuthzStatus) :
    (orderStep ⟨as, .pending⟩ .finalize).status = .pending := rfl

/-! ## 6. Whole-run refinement, and the spec-only guarantee it carries

`Acme.orderRun` folds `orderStep` over an event list — the deployed issuance
loop. We show the whole trace it produces from `Acme.Order.fresh` is an RFC trace,
then that any RFC trace from a fresh order that reaches `valid` has all
authorizations valid — a fact proven *entirely inside the spec*, so composing the
two re-derives the deployed guarantee through the independent specification. -/

/-- Multi-step RFC trace relation (the spec's own run). -/
inductive RfcOrderSteps : Order → List OrderLabel → Order → Prop where
  | nil (o : Order) : RfcOrderSteps o [] o
  | cons {o o' o'' : Order} {l : OrderLabel} {ls : List OrderLabel}
      (h : RfcOrderStep o l o') (t : RfcOrderSteps o' ls o'') :
      RfcOrderSteps o (l :: ls) o''

/-- Spec-side well-formedness: a non-pending order has all authorizations valid.
(Identical in content to `Acme.Order.wf`, but re-proven inductive over the
*independent* `RfcOrderStep` relation — nothing here calls `orderStep`.) -/
def SpecWf (o : Order) : Prop :=
  o.status = .ready ∨ o.status = .processing ∨ o.status = .valid
    → allValid o.authzs = true

/-- `SpecWf` is inductive over a single RFC step. -/
theorem rfcOrderStep_specWf {o o' : Order} {l : OrderLabel}
    (h : RfcOrderStep o l o') (hw : SpecWf o) : SpecWf o' := by
  cases h with
  | authzStay _ hnotAll _ => intro hs; rcases hs with h | h | h <;> simp_all
  | authzReady _ hall => intro _; exact hall
  | authzInvalid _ hinv => intro hs; rcases hs with h | h | h <;> simp_all
  | finalize hall => intro _; exact hall
  | issued => intro _; exact hw (Or.inr (Or.inl rfl))
  | issueFail => intro hs; rcases hs with h | h | h <;> simp_all
  | stutter _ => exact hw

/-- `SpecWf` survives a whole RFC trace. -/
theorem rfcOrderSteps_specWf {o o' : Order} {ls : List OrderLabel}
    (h : RfcOrderSteps o ls o') (hw : SpecWf o) : SpecWf o' := by
  induction h with
  | nil => exact hw
  | cons hstep _ ih => exact ih (rfcOrderStep_specWf hstep hw)

/-- **Spec-only guarantee.** Any RFC trace from a fresh order that reaches `valid`
— the point of certificate issuance — has *every* authorization valid. Proven
without reference to the deployed functions. -/
theorem rfcSteps_valid_needs_allValid {ids : List Bytes} {ls : List OrderLabel}
    {o : Order} (h : RfcOrderSteps (Order.fresh ids) ls o)
    (hvalid : o.status = .valid) : allValid o.authzs = true := by
  have hw0 : SpecWf (Order.fresh ids) := by
    intro hs; simp [Order.fresh] at hs
  exact rfcOrderSteps_specWf h hw0 (Or.inr (Or.inr hvalid))

/-- **Whole-run refinement.** The deployed `Acme.orderRun` from any well-formed
order produces an RFC trace (under the label renaming). -/
theorem run_is_rfc_trace {o : Order} (hwf : o.wf) (es : List OrderEvent) :
    RfcOrderSteps o (es.map ofOrderEvent) (orderRun o es) := by
  induction es generalizing o with
  | nil => exact RfcOrderSteps.nil o
  | cons e es ih =>
      exact RfcOrderSteps.cons (orderStep_refines hwf e)
        (ih (Acme.orderStep_wf hwf))

/-- The deployed issuance loop from a fresh order is an RFC trace. -/
theorem deployed_run_is_rfc_trace (ids : List Bytes) (es : List OrderEvent) :
    RfcOrderSteps (Order.fresh ids) ((es.map ofOrderEvent)) (orderRun (Order.fresh ids) es) :=
  run_is_rfc_trace (Order.fresh_wf ids) es

/-- **Headline (deployed, through the spec).** Any order the deployed
`Acme.orderRun` drives to `valid` from a fresh order has all authorizations valid
— no certificate is issued past a pending or failed authorization. Obtained by
composing the whole-run refinement with the spec-only guarantee, so the
independent RFC specification is load-bearing. -/
theorem deployed_valid_needs_allValid (ids : List Bytes) (es : List OrderEvent)
    (hvalid : (orderRun (Order.fresh ids) es).status = .valid) :
    allValid (orderRun (Order.fresh ids) es).authzs = true :=
  rfcSteps_valid_needs_allValid (deployed_run_is_rfc_trace ids es) hvalid

/-! ## 7. Axiom audit -/

#print axioms chalStep_refines
#print axioms rfc_chal_into_valid
#print axioms deployed_no_validate_before_respond
#print axioms orderStep_refines
#print axioms rfc_no_finalize_from_pending
#print axioms deployed_no_finalize_from_pending
#print axioms deployed_valid_needs_allValid
#print axioms rfcSteps_valid_needs_allValid

end AcmeCorrect
