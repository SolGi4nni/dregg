/-
BasicAuthCorrect — HTTP Basic authentication *correctness*: a refinement of the
deployed server-side admit decision (`BasicAuth.authenticate`, the REAL machine
run on the serve path by `Reactor.AuthDeploy`) against an INDEPENDENT
specification transcribed from RFC 7617.

`BasicAuth.lean` proves SAFETY-flavoured, one-directional facts: `authenticate_ok`
inverts a *given* `ok` outcome, `basic_rejects_bad_cred` says a `verify`-rejected
credential is never 200, `basic_no_creds_challenges` handles the empty header.
Each pins down one direction of one path. None of them, on its own, states the
whole decision: that on EVERY input the machine admits a user IFF that user's
credential is exactly the one RFC 7617 §2 says must be admitted — nothing more,
nothing less. A machine that admitted an extra input (a wrong password, a
malformed header) could still satisfy every safety lemma above while authorizing
a request the standard forbids.

This file closes that gap with a two-sided characterization.

Standard basis — RFC 7617 §2 ("The 'Basic' Authentication Scheme"):

  * The client sends `Authorization: Basic <token68>`; the scheme name is matched
    case-insensitively. Recovering the `token68` from the header value is the
    boundary `Config.parseBasic` (RFC 7617 §2).
  * The `token68` is the Base64 (RFC 4648 §4) encoding of `user-id ":" password`.
    "The user-id and password MUST NOT contain any control characters … Note
    that … the user-id … [is] everything up to the FIRST colon." Base64-decoding
    and splitting at the first colon into `(user-id, password)` is the boundary
    `Config.decodeUserPass` (RFC 7617 §2).
  * "the server … [checks] the … credentials against the server's authentication
    database": the recovered password is verified against the stored record. This
    is the boundary `Config.verify` — a constant-time password-hash comparison.
  * On any failure — no `Authorization` header, a non-`Basic` scheme, undecodable
    octets, or a rejected password — "the origin server … send[s] a 401
    (Unauthorized) … with a `WWW-Authenticate` header field … containing … the
    `Basic` … scheme". That is `BasicAuth.challenge`.

The specification (`Admits`) is written PURELY from that mandate. It is a flat
existential over the RFC's three boundary operations — parse the `Basic` scheme,
decode-and-first-colon-split, verify the password — and it NEVER mentions
`BasicAuth.authenticate`. The refinement theorem `authenticate_admits_iff` proves
the deployed machine admits a user IFF `Admits` holds; `authenticate_rejects`
proves the machine challenges whenever no user is admitted. Together they force
the machine to be exactly the RFC's decision, on all inputs.

Non-vacuity. Two classic bypasses are exhibited as concrete alternative machines
and shown to DISAGREE with the real one on a concrete input, so the iff is FALSE
for them and genuinely rules them out:

  * `admitIgnoringVerify` — a machine that admits any decodable credential
    WITHOUT checking the password (`verify` bypassed). It admits a user for whom
    `Admits` is false; `ignoreVerify_violates_spec`.
  * `admitMalformed` — a machine that admits even when the `Basic` scheme fails
    to parse (malformed / non-`Basic` header). It admits where the real machine
    challenges; `malformed_violates_spec`.

Boundary note (honest scope). The base64 decode, the FIRST-colon split, and the
password-hash compare are RFC operations captured as the named total boundaries
`decodeUserPass` / `verify`; `authenticate` is the policy *around* them and the
refinement proves that policy correct for every instantiation of the boundaries.
A boundary that split at the WRONG colon is a different `decodeUserPass` value,
not a defect in `authenticate`; the octet-level base64 and colon arithmetic are
out of scope for this policy-level lane (see the `## Boundary scope` section).
-/

import BasicAuth

namespace BasicAuthCorrect

open BasicAuth

/-! ## Independent specification (RFC 7617 §2)

Nothing in this section mentions `BasicAuth.authenticate`. `Admits` is the
ground-truth admit relation: there is a header carrying a `Basic` `token68` that
decodes and first-colon-splits to `(user, password)`, and the password verifies
against the stored record. It is a flat statement of the RFC's mandate, on the
opposite side of the decision from the implementation's nested match. -/

/-- **RFC 7617 §2 admit relation.** The request should be authenticated as
`user` exactly when it carries an `Authorization` value `v` whose `Basic`
`token68` is `tok` (`parseBasic`), that `token68` base64-decodes and splits at
the first colon into `(user, pass)` (`decodeUserPass`), and `pass` verifies
against the stored credential for `user` (`verify`). Written from the standard;
it never calls the machine. -/
def Admits (cfg : Config) (req : Request) (user : String) : Prop :=
  ∃ v tok pass,
    req.authorization = some v ∧
    cfg.parseBasic v = some tok ∧
    cfg.decodeUserPass tok = some (user, pass) ∧
    cfg.verify user pass = true

/-! ## Structural lemma: the machine only ever admits or issues the realm challenge -/

/-- Every run of the deployed machine is either an `ok` for some user, or exactly
the configured realm challenge `challenge cfg` — there is no third outcome and no
other challenge value. -/
theorem authenticate_form (cfg : Config) (req : Request) :
    (∃ u, authenticate cfg req = .ok u) ∨ authenticate cfg req = challenge cfg := by
  unfold authenticate
  split
  · exact Or.inr rfl
  · split
    · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · next user pass _ =>
        by_cases hb : cfg.verify user pass = true
        · exact Or.inl ⟨user, if_pos hb⟩
        · exact Or.inr (if_neg hb)

/-! ## Refinement: the deployed decision IS the RFC's admit decision -/

/-- **BasicAuth correctness — the admit direction.** For every configuration and
request, the deployed `BasicAuth.authenticate` admits `user` (returns `ok user`,
HTTP 200) IFF the RFC 7617 §2 `Admits` relation holds for that user. The forward
direction is inversion of the machine; the backward direction runs the machine
forward on a supplied RFC-conformant credential. Neither side is the other
renamed: `Admits` is a flat existential specification, `authenticate` is a nested
decision procedure — this equation is the whole refinement.

This binds the DEPLOYED function: `authenticate` is the same machine
`Reactor.AuthDeploy.serveBasicAuthGuarded` runs on the serve path. -/
theorem authenticate_admits_iff (cfg : Config) (req : Request) (user : String) :
    authenticate cfg req = .ok user ↔ Admits cfg req user := by
  constructor
  · intro h
    obtain ⟨v, tok, pass, h1, h2, h3, h4⟩ := authenticate_ok cfg req h
    exact ⟨v, tok, pass, h1, h2, h3, h4⟩
  · intro h
    obtain ⟨v, tok, pass, h1, h2, h3, h4⟩ := h
    simp only [authenticate, h1, h2, h3]
    exact if_pos h4

/-- **BasicAuth correctness — the reject direction (completeness of the
challenge).** If the RFC admits NO user for this request, the deployed machine
issues exactly the realm challenge (`challenge cfg`, HTTP 401). Combined with
`authenticate_admits_iff` this fixes the machine as the RFC decision on every
input: a request is 200-for-`user` iff `Admits cfg req user`, and 401 otherwise.
The no-credentials, non-`Basic`-scheme, undecodable, and wrong-password failure
modes (RFC 7617 §2) are all subsumed — each makes `Admits` false for every user. -/
theorem authenticate_rejects (cfg : Config) (req : Request)
    (h : ∀ user, ¬ Admits cfg req user) :
    authenticate cfg req = challenge cfg := by
  rcases authenticate_form cfg req with ⟨u, hu⟩ | hc
  · exact absurd ((authenticate_admits_iff cfg req u).1 hu) (h u)
  · exact hc

/-- The reject direction lands the RFC's status code: no admitted user ⇒ HTTP 401. -/
theorem authenticate_rejects_401 (cfg : Config) (req : Request)
    (h : ∀ user, ¬ Admits cfg req user) :
    (authenticate cfg req).status = 401 := by
  rw [authenticate_rejects cfg req h]; rfl

/-! ## Non-vacuity: RFC-violating machines FAIL the refinement

Each alternative below satisfies the *shape* of a Basic-auth gate but breaks one
RFC rule. On a concrete input it disagrees with the real machine, so
`authenticate_admits_iff` is FALSE for it — the theorem genuinely forbids it. -/

/-- A concrete configuration whose password check REJECTS everything, whose
`Basic` parse and decode always succeed with a fixed credential. -/
def rejectingCfg : Config :=
  { realm := "r"
    charset := none
    parseBasic := fun _ => some "tok"
    decodeUserPass := fun _ => some ("alice", "secret")
    verify := fun _ _ => false }

/-- A request that carries some `Authorization` value. -/
def someReq : Request := { authorization := some "Basic YWxpY2U6c2VjcmV0" }

/-- **Bypass 1 — password not checked.** Admits any credential that decodes,
skipping `verify` entirely. -/
def admitIgnoringVerify (cfg : Config) (req : Request) : Outcome :=
  match req.authorization with
  | none => challenge cfg
  | some v => match cfg.parseBasic v with
    | none => challenge cfg
    | some tok => match cfg.decodeUserPass tok with
      | none => challenge cfg
      | some (user, _) => .ok user

/-- The RFC admits NOBODY under `rejectingCfg`/`someReq`: `verify` is `false`, so
`Admits` fails for every user. -/
theorem rejecting_admits_none (user : String) : ¬ Admits rejectingCfg someReq user := by
  rintro ⟨v, tok, pass, _, _, hd, hv⟩
  simp [rejectingCfg] at hv

/-- The REAL deployed machine challenges here (no admitted user). -/
theorem real_rejects_here : authenticate rejectingCfg someReq = challenge rejectingCfg :=
  authenticate_rejects rejectingCfg someReq rejecting_admits_none

/-- The verify-skipping machine ADMITS `alice` — a user the RFC does not admit. -/
theorem ignoreVerify_admits_alice :
    admitIgnoringVerify rejectingCfg someReq = .ok "alice" := rfl

/-- **Non-vacuity 1.** The verify-skipping machine admits a user for whom `Admits`
is false, so it violates `authenticate_admits_iff`: the refinement is FALSE for a
machine that skips the password check. -/
theorem ignoreVerify_violates_spec :
    admitIgnoringVerify rejectingCfg someReq = .ok "alice" ∧
    ¬ Admits rejectingCfg someReq "alice" :=
  ⟨ignoreVerify_admits_alice, rejecting_admits_none "alice"⟩

/-- The verify-skipping machine and the real machine genuinely DISAGREE on this
input — one admits, one challenges. So `authenticate_admits_iff` is not vacuous:
it forces the password-check direction that the bypass drops. -/
theorem ignoreVerify_differs_from_real :
    admitIgnoringVerify rejectingCfg someReq ≠ authenticate rejectingCfg someReq := by
  rw [ignoreVerify_admits_alice, real_rejects_here]
  intro h; exact Outcome.noConfusion h

/-- A configuration whose `Basic` parse ALWAYS FAILS (non-`Basic` / malformed
header), but whose decode+verify would otherwise succeed. -/
def malformedCfg : Config :=
  { realm := "r"
    charset := none
    parseBasic := fun _ => none
    decodeUserPass := fun _ => some ("bob", "pw")
    verify := fun _ _ => true }

/-- **Bypass 2 — malformed header accepted.** Admits a fixed user even when the
`Basic` scheme fails to parse. -/
def admitMalformed (_cfg : Config) (_req : Request) : Outcome := .ok "bob"

/-- The RFC admits nobody when the `Basic` parse fails: `Admits` requires
`parseBasic v = some tok`, but here it is always `none`. -/
theorem malformed_admits_none (user : String) : ¬ Admits malformedCfg someReq user := by
  rintro ⟨v, tok, pass, _, hp, _, _⟩
  simp [malformedCfg] at hp

/-- The REAL machine challenges a malformed / non-`Basic` header. -/
theorem real_rejects_malformed : authenticate malformedCfg someReq = challenge malformedCfg :=
  authenticate_rejects malformedCfg someReq malformed_admits_none

/-- **Non-vacuity 2.** The malformed-accepting machine admits `bob` where `Admits`
is false, violating `authenticate_admits_iff`: the refinement is FALSE for a
machine that accepts a malformed header. -/
theorem malformed_violates_spec :
    admitMalformed malformedCfg someReq = .ok "bob" ∧
    ¬ Admits malformedCfg someReq "bob" :=
  ⟨rfl, malformed_admits_none "bob"⟩

/-- The malformed-accepting machine and the real machine DISAGREE — one admits,
one challenges — so the reject direction is genuinely forced. -/
theorem malformed_differs_from_real :
    admitMalformed malformedCfg someReq ≠ authenticate malformedCfg someReq := by
  show Outcome.ok "bob" ≠ authenticate malformedCfg someReq
  rw [real_rejects_malformed]
  intro h; exact Outcome.noConfusion h

/-! ## Boundary scope (honest)

`decodeUserPass` is the named boundary for base64-decode + FIRST-colon split
(RFC 7617 §2); `verify` is the named boundary for the password-hash compare. The
octet-level correctness of those two operations — that base64 is RFC 4648 §4 and
that the split lands at the first colon rather than the last — is a property of
the boundary *value*, not of `authenticate`, which quantifies over all such
boundaries. This lane proves the *policy* correct for every instantiation; the
octet-level decode is out of scope here (it would be a separate refinement of a
concrete `decodeUserPass`). No admit path avoids `verify`, and no missing check
was found in `authenticate`. -/

/-! ## Axiom audit -/

#print axioms authenticate_admits_iff
#print axioms authenticate_rejects
#print axioms ignoreVerify_violates_spec
#print axioms malformed_violates_spec
#print axioms ignoreVerify_differs_from_real

end BasicAuthCorrect
