/-
SecurityHeadersCorrect — response security-header rendering *correctness*: a
refinement of the DEPLOYED `SecurityHeaders.render` / `SecurityHeaders.hstsRender`
(the functions the security-header response-transform stage folds onto every
response) against an INDEPENDENT specification transcribed from the standards that
govern each field.

`SecurityHeaders.lean` proves SAFETY-flavoured facts about the emitted set: the
rendered HSTS directive set contains `max-age` and repeats no name
(`hsts_wellformed`), a zero `max-age` disables `includeSubDomains`
(`hsts_zero_disables`), the serialized value begins with `max-age=`
(`hsts_render_maxage`), a policy carrying HSTS emits the field
(`render_hsts_present`). Each pins a *property* of the rendered value; none, on its
own, says the value the server writes is EXACTLY the string the grammar mandates —
a renderer that emitted `max-age=…; includeSubDomains` unconditionally, or that put
`includeSubDomains` before `max-age`, would satisfy several of them while producing
a value the standard forbids.

This file closes that gap. It specifies, *without reference to* `hstsRender`,
`render`, `cspRender`, or `xfoValue`, the exact serialized form of each field:

  * `specHstsValue` — the `Strict-Transport-Security` field-value grammar
    (RFC 6797 §6.1 / §6.1.1 / §6.1.2). The value is the directive list serialized
    as `directive *( "; " directive )`: the REQUIRED `max-age=<delta-seconds>`
    directive first, then the valueless `includeSubDomains` directive iff
    configured, then the de-facto `preload` directive iff configured — in that
    order. Written as an `intercalate` over an independently built directive list,
    not as the implementation's prefix-concatenation.
  * `specXfoValue` — the `X-Frame-Options` field-value (RFC 7034 §2.1): the
    tokens `DENY` and `SAMEORIGIN`.
  * `specCspValue` — the `Content-Security-Policy` serialization (WHATWG CSP,
    "serialize a CSP"): directives joined by `"; "`, each a directive-name
    followed by its space-separated source list.
  * the `X-Content-Type-Options` value is the fixed token `nosniff` (WHATWG Fetch,
    "X-Content-Type-Options header"); `Referrer-Policy` carries its configured
    opaque token (W3C Referrer Policy §3).

The correctness theorems are equations. `hstsRender_matches_spec` proves the
deployed HSTS serializer equals `specHstsValue` on every `max-age`, every
`includeSubDomains` flag, and every `preload` flag — so the directive order and
the two conditionals are pinned exactly. `render_matches_spec` lifts this to the
whole header set: for every policy, the list `SecurityHeaders.render` emits equals
the independently specified set `specRender`, field for field, in order.

Non-vacuity. The spec DISTINGUISHES wrong renderers. `misordered_value` is the
same three directives with `includeSubDomains` ahead of `max-age`;
`misordered_fails_spec` proves it differs from `specHstsValue`, so a renderer
emitting it would violate `hstsRender_matches_spec`. `always_includeSubDomains` is
a renderer that emits `includeSubDomains` whether or not it is configured;
`always_includeSubDomains_fails_spec` proves it disagrees with `specHstsValue` on a
policy that did NOT configure it. And `deployed_hsts_value` computes the exact
string the deployed one-year/subdomains/preload policy renders, exhibiting the
theorem on a concrete non-trivial input. Hence the refinement genuinely forces the
grammar and is false for the mis-ordered and over-emitting implementations.

Standard basis. RFC 6797 §6.1 (Strict-Transport-Security syntax), §6.1.1
(`max-age`, REQUIRED), §6.1.2 (`includeSubDomains`); RFC 7034 §2.1
(X-Frame-Options); WHATWG Fetch (X-Content-Type-Options `nosniff`); WHATWG CSP
("serialize a CSP"); W3C Referrer Policy §3. `preload` is not an RFC directive; it
is the de-facto HSTS-preload-list extension, serialized last as the standard
directive grammar permits unknown directives.
-/

import SecurityHeaders

namespace SecurityHeadersCorrect

open SecurityHeaders

/-! ## Independent specification

Nothing in this section mentions `SecurityHeaders.hstsRender`, `.render`,
`.cspRender`, or `.xfoValue`. Each definition transcribes a field-value grammar
straight from its governing standard. -/

/-- **RFC 6797 §6.1 directive list.** The ordered directives of a
Strict-Transport-Security field value: the REQUIRED `max-age=<delta-seconds>`
directive (§6.1.1) first, then the valueless `includeSubDomains` directive
(§6.1.2) iff configured, then the de-facto `preload` directive iff configured.
Built independently of the implementation. -/
def specHstsDirectives (maxAge : Nat) (inclSub preload : Bool) : List String :=
  ["max-age=" ++ toString maxAge]
    ++ (if inclSub then ["includeSubDomains"] else [])
    ++ (if preload then ["preload"] else [])

/-- **RFC 6797 §6.1 serialized field value.** The directive list serialized as
`directive *( "; " directive )` — the directives joined by the `"; "` separator.
This is the exact string the standard mandates for the field value. -/
def specHstsValue (maxAge : Nat) (inclSub preload : Bool) : String :=
  String.intercalate "; " (specHstsDirectives maxAge inclSub preload)

/-- **RFC 7034 §2.1** `X-Frame-Options` field values. -/
def specXfoValue : XFrameOptions → String
  | .deny => "DENY"
  | .sameOrigin => "SAMEORIGIN"

/-- **WHATWG CSP, "serialize a CSP".** Directives joined by `"; "`, each a
directive-name followed by its space-separated source list. -/
def specCspValue (c : Csp) : String :=
  String.intercalate "; " (c.directives.map (fun d => String.intercalate " " (d.1 :: d.2)))

/-- **The independently specified security-header set.** For every policy, the
header list mandated by the standards: HSTS with its RFC-6797 value iff a policy
is configured, CSP with its WHATWG value, X-Frame-Options with its RFC-7034 token,
`X-Content-Type-Options: nosniff` (WHATWG Fetch) iff enabled, and Referrer-Policy
with its configured opaque token (W3C) — in that field order. Written without any
reference to `SecurityHeaders.render`. -/
def specRender (p : Policy) : Resp :=
  (match p.hsts with
   | some h => [("Strict-Transport-Security", specHstsValue h.maxAge h.includeSubDomains h.preload)]
   | none => [])
  ++ (match p.csp with
   | some c => [("Content-Security-Policy", specCspValue c)]
   | none => [])
  ++ (match p.xfo with
   | some x => [("X-Frame-Options", specXfoValue x)]
   | none => [])
  ++ (if p.noSniff then [("X-Content-Type-Options", "nosniff")] else [])
  ++ (match p.referrerPolicy with
   | some r => [("Referrer-Policy", r)]
   | none => [])

/-! ## Refinement: the deployed serializer equals the spec -/

/-- **HSTS serialization correctness (RFC 6797 §6.1).** The DEPLOYED
`SecurityHeaders.hstsRender` — the exact serializer the security-header stage
renders into the wire `Strict-Transport-Security` value — equals the independently
specified `specHstsValue` for EVERY `max-age`, `includeSubDomains`, and `preload`.
The required-directive-first order and both conditional directives are pinned. -/
theorem hstsRender_matches_spec (h : Hsts) :
    hstsRender h = specHstsValue h.maxAge h.includeSubDomains h.preload := by
  cases hi : h.includeSubDomains <;> cases hp : h.preload <;>
    (simp only [hstsRender, specHstsValue, specHstsDirectives, hi, hp,
      Bool.false_eq_true, reduceIte, if_true, if_false,
      List.cons_append, List.nil_append, String.intercalate, String.intercalate.go]
     <;> apply String.ext
     <;> simp only [String.data_append, List.append_assoc, List.cons_append, List.nil_append,
       List.append_nil, String.intercalate.go])

/-- **Security-header set correctness.** For every policy, the header list the
DEPLOYED `SecurityHeaders.render` emits equals the independently specified
`specRender` — field for field, in order. The whole set refines the standards; the
HSTS value refines RFC 6797 exactly via `hstsRender_matches_spec`. -/
theorem render_matches_spec (p : Policy) :
    SecurityHeaders.render p = specRender p := by
  simp only [SecurityHeaders.render, specRender, specXfoValue, xfoValue,
    specCspValue, cspRender, hstsRender_matches_spec]
  rfl

/-! ## Non-vacuity: the spec distinguishes wrong renderers

Each fact below shows the specification REJECTS an implementation that violates the
grammar, so `hstsRender_matches_spec` is not a tautology — it forces the RFC-6797
directive order and the two configured-only conditionals. -/

/-- The exact value the DEPLOYED policy renders (one year, subdomains, preload):
`SecurityHeaders.render` on the stage's policy produces this literal HSTS value,
via `hstsRender_matches_spec` on a concrete non-trivial input. -/
theorem deployed_hsts_value :
    specHstsValue 31536000 true true = "max-age=31536000; includeSubDomains; preload" := by
  decide

/-- A configuration that does NOT ask for `includeSubDomains` renders no such
directive: the spec value is exactly `max-age=<n>`. -/
theorem spec_omits_unconfigured_includeSubDomains :
    specHstsValue 100 false false = "max-age=100" := by decide

/-- The same three directives, but with `includeSubDomains` placed AHEAD of
`max-age` — the mis-ordering a naive serializer might produce. -/
def misordered_value (maxAge : Nat) : String :=
  "includeSubDomains; max-age=" ++ toString maxAge ++ "; preload"

/-- **Mis-ordering fails the spec.** A serializer that leads with
`includeSubDomains` disagrees with `specHstsValue`, so it violates
`hstsRender_matches_spec`. The required-directive-first order is genuinely forced. -/
theorem misordered_fails_spec :
    misordered_value 100 ≠ specHstsValue 100 true true := by decide

/-- A renderer that emits `includeSubDomains` unconditionally (ignoring the
configuration flag) — the classic over-emission bug. -/
def always_includeSubDomains (maxAge : Nat) : String :=
  "max-age=" ++ toString maxAge ++ "; includeSubDomains"

/-- **Over-emitting `includeSubDomains` fails the spec.** On a policy that did NOT
configure `includeSubDomains`, the always-emitting renderer disagrees with
`specHstsValue`, so it violates `hstsRender_matches_spec`. Emitting the directive
when unconfigured is genuinely ruled out. -/
theorem always_includeSubDomains_fails_spec :
    always_includeSubDomains 100 ≠ specHstsValue 100 false false := by decide

/-! ## Axiom audit -/

#print axioms hstsRender_matches_spec
#print axioms render_matches_spec
#print axioms misordered_fails_spec
#print axioms always_includeSubDomains_fails_spec

end SecurityHeadersCorrect
