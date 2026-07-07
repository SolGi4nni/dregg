/-
RedirectCorrect — redirect-handler *correctness*: a refinement of the deployed
redirect response builder (`Redirect.redirect`) and followed-request-method
selector (`Redirect.followedMethod`) against an INDEPENDENT specification
transcribed from RFC 9110 §15.4 (Redirection 3xx).

`Redirect.lean` proves SAFETY-flavoured facts about what the handler emits: the
`Location` is a faithful substitution (`render_eq_join`), the status is one of a
hard-coded four-element list (`status_is_redirect`), 307/308 keep the method
(`method_preserved`), 301/302 downgrade (`method_safe_downgrade`). Each pins a
property of a *particular internal function*, but the list `[301,302,307,308]`,
the classification, and the method rule are all stated in the implementation's
own vocabulary — nothing checks them against the standard's enumeration and
method-rewriting rule, read off the RFC on its own terms.

This file closes that gap. It specifies, *without any reference to*
`Redirect.Code`, `Redirect.redirect`, `Redirect.followedMethod`,
`Redirect.Code.status`, `Redirect.Code.methodPreserving`, or
`Redirect.redirectStatuses`, the RFC 9110 §15.4 requirements as predicates keyed
only on the numeric HTTP status:

  * `IsRedirectStatus` — the response status is one of the redirection codes the
    RFC enumerates in §15.4: 301 (§15.4.2), 302 (§15.4.3), 303 (§15.4.4),
    307 (§15.4.7), 308 (§15.4.9).
  * `IsPermanent` / `IsTemporary` — the permanent (301, 308) vs temporary
    (302, 303, 307) split the RFC draws.
  * `hasLocation` — a redirection response carries a `Location` header field
    (RFC 9110 §15.4, §10.2.2): the field is present, modelled as `Option.isSome`.
  * `MethodAllowed` — the RFC §15.4 rule for the method a user agent uses on the
    followed request: 307/308 MUST reuse the original method (§15.4.7/§15.4.9);
    303 changes it to GET (§15.4.4); 301/302 MAY rewrite a request whose method
    is neither GET nor HEAD to GET (§15.4.2/§15.4.3, and the historical note),
    but MUST NOT alter a GET/HEAD.

  * `rfcExactStatus` — the RFC §15.4 EXACT status table keyed on the two axes
    the standard classifies a redirect on (permanence × method-semantics):
    permanent-preserving→308, permanent-may-change→301, temporary-preserving→307,
    temporary-may-change→302 (303 See Other is the off-grid fifth code).

The headline `redirect_status_exact` binds the DEPLOYED builder to PER-CODE
equality: for every configured `Code` the emitted status equals *exactly* the
`rfcExactStatus` cell for that code's permanence and method-semantics — not
merely membership in `{301,302,303,307,308}`. `redirect_refines_rfc` carries this
exact-status clause together with `IsWellFormedRedirect` (a `Location` is present
and the exact status is a §15.4 code, via `rfcExactStatus_isRedirect`) and the
`MethodAllowed` §15.4 followed-method rule on the deployed `followedMethod`.
`permanent_classification_correct` binds the deployed `Code.permanent` to the
RFC's permanent split.

NON-VACUITY (`nonvacuous_*`): the specification rejects a non-3xx status, a
missing `Location`, a 307 that downgrades a POST, a 303 that keeps a POST, and a
301 that rewrites a GET. Crucially `nonvacuous_exact_mismatch` shows the exact
table rejects a WELL-FORMED-but-wrong code — 302 where 308 is configured, which
the old membership clause could not catch — so per-code exactness is strictly
discriminating, not a renamed tautology.
-/
import Redirect

namespace RedirectSpec

open Redirect (Method)

/-! ## The RFC 9110 §15.4 requirements, as an independent specification.

Every definition below is keyed on the numeric HTTP status (`Nat`) and the
`Method` alphabet only. None mentions any implementation function; they are the
standard's clauses written on their own terms. -/

/-- The redirection status codes RFC 9110 §15.4 enumerates: 301 Moved
Permanently (§15.4.2), 302 Found (§15.4.3), 303 See Other (§15.4.4), 307
Temporary Redirect (§15.4.7), 308 Permanent Redirect (§15.4.9). -/
def redirectionCodes : List Nat := [301, 302, 303, 307, 308]

/-- The response status is one of the §15.4 redirection codes. -/
def IsRedirectStatus (n : Nat) : Prop := n ∈ redirectionCodes

/-- Permanent redirection: 301 (§15.4.2) and 308 (§15.4.9) — the client SHOULD
update stored references to the target. -/
def IsPermanent (n : Nat) : Prop := n = 301 ∨ n = 308

/-- Temporary redirection: 302 (§15.4.3), 303 (§15.4.4), 307 (§15.4.7) — the
client SHOULD NOT update stored references. -/
def IsTemporary (n : Nat) : Prop := n = 302 ∨ n = 303 ∨ n = 307

/-- **The RFC 9110 §15.4 exact status table**, keyed on the two orthogonal axes
the standard classifies a method-explicit redirect on — permanence and
method-semantics — and *nothing else*. This is the enumeration read off the RFC
on its own terms; it mentions no implementation function and, in particular,
never touches `Redirect.Code.status`:

  * permanent + method-preserving  = **308** Permanent Redirect (§15.4.9);
  * permanent + may-rewrite-method = **301** Moved Permanently  (§15.4.2);
  * temporary + method-preserving  = **307** Temporary Redirect (§15.4.7);
  * temporary + may-rewrite-method = **302** Found              (§15.4.3).

(303 See Other, §15.4.4, is the fifth §15.4 code; it is not on this two-axis
grid — it forces GET regardless of the original method rather than "may rewrite"
— and lives in `seeOtherStatus` below, outside the deployed handler's domain.) -/
def rfcExactStatus (permanent preserving : Bool) : Nat :=
  match permanent, preserving with
  | true,  true  => 308
  | true,  false => 301
  | false, true  => 307
  | false, false => 302

/-- 303 See Other (§15.4.4): the fifth §15.4 redirection code, off the
permanence × method-preserving grid. Recorded for completeness of the RFC
enumeration; the deployed handler's `Code` cannot configure it. -/
def seeOtherStatus : Nat := 303

/-- The exact table only ever names §15.4 redirection codes — every cell is an
`IsRedirectStatus`. Ties the fine-grained spec back to the coarse membership
one, so exactness *subsumes* the old membership clause. -/
theorem rfcExactStatus_isRedirect (permanent preserving : Bool) :
    IsRedirectStatus (rfcExactStatus permanent preserving) := by
  unfold IsRedirectStatus redirectionCodes
  cases permanent <;> cases preserving <;> decide

/-- A redirection response abstracted to the two fields §15.4 constrains: the
numeric status and the `Location` header field, present-or-absent. -/
structure Response where
  status : Nat
  location : Option String
deriving DecidableEq, Repr

/-- RFC 9110 §15.4 / §10.2.2: a redirection response carries a `Location`
header field — the field is present. -/
def hasLocation (r : Response) : Prop := r.location.isSome = true

/-- A well-formed §15.4 redirection response: the status is a redirection code
and a `Location` field is present. -/
def IsWellFormedRedirect (r : Response) : Prop :=
  IsRedirectStatus r.status ∧ hasLocation r

/-- The RFC 9110 §15.4 rule for the method a user agent uses on the followed
request, as a Boolean-backed decidable predicate on the emitted status.

  * 307 / 308: MUST reuse the original method (§15.4.7, §15.4.9).
  * 303: change to GET (§15.4.4).
  * 301 / 302: MUST NOT alter a GET or HEAD; MAY rewrite any other method to GET
    (§15.4.2, §15.4.3, and the note about historical practice). -/
def methodAllowedB (n : Nat) (orig result : Method) : Bool :=
  if n = 307 ∨ n = 308 then decide (result = orig)
  else if n = 303 then decide (result = Method.get)
  else decide (result = orig ∨
        (orig ≠ Method.get ∧ orig ≠ Method.head ∧ result = Method.get))

/-- The RFC §15.4 followed-method rule as a proposition. -/
def MethodAllowed (n : Nat) (orig result : Method) : Prop :=
  methodAllowedB n orig result = true

instance (n : Nat) (orig result : Method) : Decidable (MethodAllowed n orig result) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## The refinement: the deployed handler satisfies the specification.

The bridge `ofResp` embeds the deployed response into the specification's
`Response`; a `Location` header is always present because the deployed
`Redirect.Resp` structurally carries one. -/

/-- Embed a deployed `Redirect.Resp` into the specification `Response`: the
built `location` string is the (always present) `Location` header value. -/
def ofResp (r : Redirect.Resp) : Response :=
  { status := r.status, location := some r.location }

/-- **Exact status (per-code equality).** The DEPLOYED redirect builder emits,
for every configured `Code`, EXACTLY the status code the RFC 9110 §15.4 table
prescribes for that code's permanence and method-semantics — not merely *some*
member of `{301,302,303,307,308}`. The right-hand side is the independent
`rfcExactStatus` table; its arguments are the redirect's configured *semantics*
(the permanence and method-preserving axes), and the claim is that the emitted
*status* equals the RFC's assignment for those semantics.

Concretely this pins each configured code to its own number:
`.perm308 ↦ 308`, `.moved301 ↦ 301`, `.temp307 ↦ 307`, `.found302 ↦ 302`.
An implementation that emitted 302 where a permanent-preserving redirect is
configured would make the two sides `302 ≠ 308` and this theorem would FAIL —
see `nonvacuous_exact_mismatch`. -/
theorem redirect_status_exact
    (code : Redirect.Code) (template : List Redirect.Tok) (path query : String) :
    (Redirect.redirect code template path query).status
      = rfcExactStatus code.permanent code.methodPreserving := by
  cases code <;> rfl

/-- **Refinement.** For every configured redirect `Code`, `Location` template,
request path/query, and original request method, the DEPLOYED redirect handler
meets the RFC 9110 §15.4 specification:

  1. the emitted status is EXACTLY the §15.4 code its configured permanence /
     method-semantics prescribe (`rfcExactStatus`) — a per-code equality;
  2. the response carries a `Location` header, and that exact status is a §15.4
     redirection code (`IsWellFormedRedirect`);
  3. the DEPLOYED `followedMethod` obeys the §15.4 method rule (`MethodAllowed`)
     for that emitted status.

Clause 1 is strictly stronger than the earlier membership clause: it fixes the
one right code per configuration, and membership follows from it via
`rfcExactStatus_isRedirect`. This binds `Redirect.redirect` and
`Redirect.followedMethod` themselves, not a copy. -/
theorem redirect_refines_rfc
    (code : Redirect.Code) (template : List Redirect.Tok)
    (path query : String) (m : Method) :
    (Redirect.redirect code template path query).status
        = rfcExactStatus code.permanent code.methodPreserving
    ∧ IsWellFormedRedirect (ofResp (Redirect.redirect code template path query))
    ∧ MethodAllowed (Redirect.redirect code template path query).status
        m (Redirect.followedMethod code m) := by
  refine ⟨redirect_status_exact code template path query, ⟨?_, ?_⟩, ?_⟩
  · -- membership of the *exact* status: derived from clause 1, not re-proved
    rw [show (ofResp (Redirect.redirect code template path query)).status
          = rfcExactStatus code.permanent code.methodPreserving from
        redirect_status_exact code template path query]
    exact rfcExactStatus_isRedirect _ _
  · rfl
  · show MethodAllowed (Redirect.Code.status code) m (Redirect.followedMethod code m)
    cases code <;> cases m <;> decide

/-- **Permanent classification.** The DEPLOYED `Code.permanent` flag agrees, on
every code, with the RFC §15.4 permanent split (`IsPermanent` of the emitted
status). -/
theorem permanent_classification_correct (code : Redirect.Code) :
    Redirect.Code.permanent code = true ↔ IsPermanent (Redirect.Code.status code) := by
  cases code <;>
    simp [Redirect.Code.permanent, Redirect.Code.status, IsPermanent]

/-! ## Non-vacuity: the specification rejects malformed redirects.

Each witness is a response or method choice the standard forbids and the
deployed handler never emits; that the predicate is FALSE on them shows the
refinement above is discriminating, not a tautology. -/

/-- A non-3xx status is not a well-formed redirect: a 200 response fails. -/
theorem nonvacuous_bad_status :
    ¬ IsWellFormedRedirect { status := 200, location := some "https://x" } := by
  unfold IsWellFormedRedirect IsRedirectStatus hasLocation redirectionCodes
  decide

/-- A redirection status with no `Location` header fails. -/
theorem nonvacuous_missing_location :
    ¬ IsWellFormedRedirect { status := 301, location := none } := by
  unfold IsWellFormedRedirect IsRedirectStatus hasLocation redirectionCodes
  decide

/-- A 307 that downgrades a POST to GET violates the §15.4.7 MUST-reuse rule. -/
theorem nonvacuous_307_must_preserve :
    ¬ MethodAllowed 307 Method.post Method.get := by decide

/-- A 308 that rewrites a POST to GET violates the §15.4.9 MUST-reuse rule. -/
theorem nonvacuous_308_must_preserve :
    ¬ MethodAllowed 308 Method.post Method.get := by decide

/-- A 303 that keeps the original POST violates the §15.4.4 change-to-GET rule. -/
theorem nonvacuous_303_must_get :
    ¬ MethodAllowed 303 Method.post Method.post := by decide

/-- A 301 that rewrites a GET to POST violates the §15.4.2 MUST-NOT-alter-GET
rule. -/
theorem nonvacuous_301_keeps_get :
    ¬ MethodAllowed 301 Method.get Method.post := by decide

/-! ### Non-vacuity of the *exact* status table.

Exactness is discriminating precisely because the RFC assigns a DIFFERENT number
to each (permanence, method-semantics) cell: a status that is a perfectly good
member of `redirectionCodes` can still be the *wrong* code for the configuration,
and `redirect_status_exact` rules that out. -/

/-- The RFC's exact code for a permanent-preserving redirect is 308, and it is
NOT 302 — so an implementation emitting 302 there (a `redirectionCodes` member,
hence undetectable by the old membership clause) violates `redirect_status_exact`.
This is the failure the strengthened theorem forbids. -/
theorem nonvacuous_exact_mismatch :
    rfcExactStatus true true = 308 ∧ (302 : Nat) ≠ rfcExactStatus true true := by
  decide

/-- Every distinct cell of the exact table is a distinct code: the four
configurations map to four different numbers, so exactness genuinely
distinguishes the codes rather than collapsing them. -/
theorem exact_table_injective :
    rfcExactStatus true true = 308 ∧ rfcExactStatus true false = 301 ∧
    rfcExactStatus false true = 307 ∧ rfcExactStatus false false = 302 ∧
    (rfcExactStatus true true ≠ rfcExactStatus true false ∧
     rfcExactStatus true true ≠ rfcExactStatus false true ∧
     rfcExactStatus true true ≠ rfcExactStatus false false ∧
     rfcExactStatus true false ≠ rfcExactStatus false true ∧
     rfcExactStatus true false ≠ rfcExactStatus false false ∧
     rfcExactStatus false true ≠ rfcExactStatus false false) := by
  decide

/-- The DEPLOYED handler's exact-status assignment, spelled out per configured
`Code`: each constructor emits its own number, no other. Direct instances of
`redirect_status_exact`. -/
theorem deployed_status_table (template : List Redirect.Tok) (path query : String) :
    (Redirect.redirect .moved301 template path query).status = 301 ∧
    (Redirect.redirect .found302 template path query).status = 302 ∧
    (Redirect.redirect .temp307 template path query).status = 307 ∧
    (Redirect.redirect .perm308 template path query).status = 308 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- The deployed handler's `Code` domain cannot configure a 303: no constructor
emits `seeOtherStatus`. This is the honest boundary — 303 is a §15.4 code but off
the two-axis grid the deployed handler models. -/
theorem deployed_never_303
    (code : Redirect.Code) (template : List Redirect.Tok) (path query : String) :
    (Redirect.redirect code template path query).status ≠ seeOtherStatus := by
  rw [show (Redirect.redirect code template path query).status = code.status from rfl]
  cases code <;> decide

/-- The deployed handler on a 307 genuinely preserves a POST — the positive
companion to `nonvacuous_307_must_preserve`. -/
theorem deployed_307_preserves_post :
    MethodAllowed 307 Method.post (Redirect.followedMethod .temp307 .post) := by
  decide

/-- The deployed handler on a 302 genuinely downgrades a POST to GET, one of the
`MethodAllowed` 301/302 options. -/
theorem deployed_302_downgrades_post :
    MethodAllowed 302 Method.post (Redirect.followedMethod .found302 .post) := by
  decide

#print axioms redirect_status_exact
#print axioms redirect_refines_rfc
#print axioms permanent_classification_correct
#print axioms nonvacuous_exact_mismatch
#print axioms nonvacuous_307_must_preserve

end RedirectSpec
