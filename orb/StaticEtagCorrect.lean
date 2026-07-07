/-
# StaticEtagCorrect — conditional-request correctness for the static handler

An INDEPENDENT specification of the `If-None-Match` conditional-request
semantics of RFC 7232 (HTTP/1.1 Conditional Requests), and a REFINEMENT proof
that the deployed static-file handler `StaticFile.serveResolved` (the function
`StaticFile.serve`, and hence the reactor's static route, actually invokes)
selects exactly the response the RFC mandates.

## What the RFC mandates (cited verbatim from RFC 7232)

  * §3.2 (If-None-Match):
      "A recipient MUST use the weak comparison function when comparing
       entity-tags for If-None-Match (Section 2.3.2) …"
      "If the field-value is a list of entity-tags, the condition is false if
       one of the listed tags match the entity-tag of the selected
       representation."
      "An origin server MUST NOT perform the requested method if the condition
       evaluates to false; instead, the origin server MUST respond with either
       a) the 304 (Not Modified) status code if the request method is GET or
       HEAD …"

  * §2.3.2 (weak comparison): two entity-tags are equivalent under the weak
    comparison function iff their opaque tags are equal, regardless of whether
    either carries the weak flag `W/`.

  * §4.1 (304 Not Modified):
      "A 304 response cannot contain a message-body; it is always terminated by
       the first empty line after the header fields."
    i.e. a `304` carries an EMPTY body.

  * §6 (Precedence): the If-None-Match precondition is evaluated before the
    method is performed — before any `Range` processing — so a matching
    validator pre-empts the body/range path entirely (step 3 precedes step 5).
    When If-None-Match is NOT present, step 4 evaluates If-Modified-Since: a
    representation not modified since the client's date yields `304`. A
    present-but-non-matching If-None-Match skips step 4 and proceeds to step 5.

## The specification is independent of the handler

The precondition predicate `PreconditionFails` and the weak-comparison relation
`weakCompare` are defined here from the RFC prose alone: `weakCompare a b` is
`a.tag = b.tag` (opaque-tag equality), and `PreconditionFails` is the existence
of a listed tag equal to the current tag. Neither mentions
`StaticFile.serveResolved`, `StaticFile.ifNoneMatchHit`, or any handler
internal. `preconditionFails_iff_hit` then relates this independent predicate to
the handler's boolean, and the refinement theorems bind the DEPLOYED
`serveResolved`/`serve` — not a wrapper.

## Non-vacuity

`serveResolved_304_iff` is an `↔`: a `304` with empty body is produced *if and
only if* the independent precondition holds — either the `If-None-Match`
precondition fails (a listed tag matches), OR `If-None-Match` is absent and
`If-Modified-Since` shows the representation not modified since the client's
date (RFC 7232 §6 step 4). An implementation that served the body on a matching
validator would break the `←` direction (it would not reach status 304); one
that returned `304` on a full mismatch would break the `→` direction (status
304 would not imply either precondition held) and `serveResolved_full`. The
concrete witnesses at the end exercise the match (weak flag ignored), the
mismatch (distinct tag), and the `If-Modified-Since` not-modified cases against
the real handler.

## If-Modified-Since is honored on the deployed path (RFC 7232 §6 step 4)

RFC 7232 §6 step 4 requires that, when `If-None-Match` is absent and
`If-Modified-Since` is present, a not-modified representation yields `304`. The
deployed handler `serveResolved` (the one `StaticFile.serve` invokes) now
evaluates `Req.ifModifiedSince` via `StaticFile.ifModifiedSince304`, ordered
after the `If-None-Match` precondition (§6): a not-modified representation with
no `If-None-Match` receives `304` with an empty body, never the full `200`.
`serve_honors_ifModifiedSince` exhibits this on the real handler with a concrete
witness whose `If-Modified-Since` post-dates the representation's
`Last-Modified`; the old `200` behavior would fail the theorem.
-/

import StaticFile

namespace StaticEtagCorrect

open StaticFile (ETag Config Req Resp serveResolved serve ifNoneMatchHit)

/-! ## The independent RFC 7232 §2.3.2 weak comparison -/

/-- **Weak comparison (RFC 7232 §2.3.2).** Two entity-tags are equivalent under
the weak comparison function exactly when their opaque tags are equal — the weak
flag `W/` is disregarded on both sides. Stated as a `Prop` over the opaque tag,
with no reference to the handler. -/
def weakCompare (a b : ETag) : Prop := a.tag = b.tag

/-! ## The independent RFC 7232 §3.2 precondition -/

/-- **The If-None-Match precondition evaluates to false (RFC 7232 §3.2).** For a
list of entity-tags, "the condition is false if one of the listed tags match the
entity-tag of the selected representation" — under the weak comparison function
(§3.2 mandate). When the condition is false, RFC 7232 §6 step 3 requires the
server to respond `304` for a GET/HEAD. This existential is the RFC condition,
defined purely over the field-value list and the current tag. -/
def PreconditionFails (inm : List ETag) (cur : ETag) : Prop :=
  ∃ t ∈ inm, weakCompare t cur

/-- **Bridge: the independent precondition matches the handler's boolean.** The
RFC-level predicate `PreconditionFails` holds exactly when the handler's
`ifNoneMatchHit` evaluates true. This relates the specification to the
implementation's decision procedure; it is a theorem, not a definition, and the
proof is where a strong-vs-weak-comparison bug (or a wrong tag equality) would
surface. -/
theorem preconditionFails_iff_hit (inm : List ETag) (cur : ETag) :
    PreconditionFails inm cur ↔ ifNoneMatchHit inm cur = true := by
  unfold PreconditionFails weakCompare ifNoneMatchHit StaticFile.ETag.weakMatch
  induction inm with
  | nil => simp
  | cons t rest ih =>
    simp only [List.any_cons, Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ⟨x, hx | hx, hcmp⟩
      · subst hx; exact Or.inl (by rw [beq_iff_eq]; exact hcmp)
      · exact Or.inr (ih.mp ⟨x, hx, hcmp⟩)
    · rintro (h | h)
      · exact ⟨t, Or.inl rfl, by rw [beq_iff_eq] at h; exact h⟩
      · obtain ⟨x, hx, hcmp⟩ := ih.mpr h; exact ⟨x, Or.inr hx, hcmp⟩

/-! ## The refinement: the deployed handler matches the specification -/

/-- **`serveResolved_304_iff` — the refinement theorem.** For a request resolved
to an existing representation (`cfg.fs path = some body`), the DEPLOYED handler
`StaticFile.serveResolved` produces a `304 (Not Modified)` response carrying an
EMPTY body IF AND ONLY IF the RFC 7232 §6 precondition for a `304` holds:
  * the independent §3.2 `If-None-Match` precondition fails — a listed tag
    weak-matches the current entity-tag (§6 step 3); OR
  * `If-None-Match` is absent AND `If-Modified-Since` shows the representation
    not modified since the client's date (§6 step 4).

This binds the exact function `StaticFile.serve` dispatches to (`serve cfg req =
serveResolved cfg req (resolvePath cfg req)`, definitionally), not a wrapper. It
is an `↔`, so it is non-vacuous in both directions:
  * `→` a `304`+empty response is emitted only on a genuine validator match or a
    genuine not-modified `If-Modified-Since` with no `If-None-Match`;
  * `←` either precondition is answered with `304`+empty, never the body.

The §6 precedence is exact: a present-but-non-matching `If-None-Match` makes the
right disjunct's `req.ifNoneMatch = []` false, so it proceeds to the body/range
path (step 5), never to a date `304`. -/
theorem serveResolved_304_iff (cfg : Config) (req : Req) (path : List String)
    (body : StaticFile.Bytes) (hfile : cfg.fs path = some body) :
    ((serveResolved cfg req path).status = 304
      ∧ (serveResolved cfg req path).body = [])
    ↔ (PreconditionFails req.ifNoneMatch (cfg.etag path)
        ∨ (req.ifNoneMatch = []
            ∧ StaticFile.ifModifiedSince304 (cfg.lastModified path)
                req.ifModifiedSince = true)) := by
  rw [preconditionFails_iff_hit]
  by_cases hhit : ifNoneMatchHit req.ifNoneMatch (cfg.etag path) = true
  · -- §6 step 3: a matching `If-None-Match` yields `304`.
    have hserve : serveResolved cfg req path = .notModified (cfg.etag path) := by
      unfold serveResolved; rw [hfile]; simp only [hhit, if_true]
    rw [hserve]
    constructor
    · intro _; exact Or.inl hhit
    · intro _; exact ⟨rfl, rfl⟩
  · simp only [Bool.not_eq_true] at hhit
    by_cases hmid : (req.ifNoneMatch.isEmpty
        && StaticFile.ifModifiedSince304 (cfg.lastModified path) req.ifModifiedSince) = true
    · -- §6 step 4: `If-None-Match` absent and not modified since ⇒ `304`.
      have hserve : serveResolved cfg req path = .notModified (cfg.etag path) := by
        unfold serveResolved; rw [hfile]
        simp only [hhit, Bool.false_eq_true, if_false, hmid, if_true]
      rw [hserve]
      rw [Bool.and_eq_true] at hmid
      obtain ⟨hemp, hims⟩ := hmid
      have hnil : req.ifNoneMatch = [] := List.isEmpty_iff.mp hemp
      constructor
      · intro _; exact Or.inr ⟨hnil, hims⟩
      · intro _; exact ⟨rfl, rfl⟩
    · -- neither precondition holds ⇒ the body/range path, status ≠ 304.
      simp only [Bool.not_eq_true] at hmid
      have hne : (serveResolved cfg req path).status ≠ 304 := by
        unfold serveResolved
        rw [hfile]
        simp only [hhit, Bool.false_eq_true, if_false, hmid]
        split
        · simp only [StaticFile.Resp.status]; decide
        · split <;> (simp only [StaticFile.Resp.status]; decide)
      constructor
      · intro hst; exact absurd hst.1 hne
      · intro hrhs
        cases hrhs with
        | inl h => rw [h] at hhit; exact absurd hhit (by decide)
        | inr h =>
          obtain ⟨hnil, hims⟩ := h
          rw [hnil, hims] at hmid
          simp at hmid

/-- **`serve_304_iff` — the refinement on the deployed entry point.** The same
`↔` stated on `StaticFile.serve`, the function the reactor's static route
(`Reactor.StaticRouteDeploy.deployStaticServe`) invokes. `serve` reduces to
`serveResolved cfg req (resolvePath cfg req)` by definition, so the deployed
whole-request handler emits `304`+empty exactly when the RFC 7232 §6 precondition
for a `304` holds — the `If-None-Match` precondition fails, or `If-None-Match` is
absent and `If-Modified-Since` shows the representation not modified. -/
theorem serve_304_iff (cfg : Config) (req : Req)
    (body : StaticFile.Bytes) (hfile : cfg.fs (StaticFile.resolvePath cfg req) = some body) :
    ((serve cfg req).status = 304 ∧ (serve cfg req).body = [])
    ↔ (PreconditionFails req.ifNoneMatch (cfg.etag (StaticFile.resolvePath cfg req))
        ∨ (req.ifNoneMatch = []
            ∧ StaticFile.ifModifiedSince304 (cfg.lastModified (StaticFile.resolvePath cfg req))
                req.ifModifiedSince = true)) := by
  unfold serve
  exact serveResolved_304_iff cfg req (StaticFile.resolvePath cfg req) body hfile

/-- **`serveResolved_full_on_mismatch` — the non-matching branch.** When the
independent precondition does NOT fail (no listed tag weak-matches), the
`If-Modified-Since` precondition does NOT yield `304` (the representation is
modified since, or the header is absent), and there is no `Range`, the deployed
handler serves the full `200 (OK)` with the complete representation body — never
a `304`. This is the RFC 7232 §6 "continue to step 5" path and is the positive
half of non-vacuity: an implementation that returned `304` on a mismatch would
fail here. -/
theorem serveResolved_full_on_mismatch (cfg : Config) (req : Req) (path : List String)
    (body : StaticFile.Bytes) (hfile : cfg.fs path = some body)
    (hmiss : ¬ PreconditionFails req.ifNoneMatch (cfg.etag path))
    (hims : StaticFile.ifModifiedSince304 (cfg.lastModified path) req.ifModifiedSince = false)
    (hrange : req.range = none) :
    (serveResolved cfg req path).status = 200
    ∧ (serveResolved cfg req path).body = body := by
  rw [preconditionFails_iff_hit, Bool.not_eq_true] at hmiss
  have hserve : serveResolved cfg req path = .ok body (cfg.etag path) := by
    unfold serveResolved
    rw [hfile]
    simp only [hmiss, Bool.false_eq_true, if_false, hims, Bool.and_false, hrange]
  rw [hserve]; exact ⟨rfl, rfl⟩

/-- `serve_full_on_mismatch` — the mismatch branch on the deployed entry point. -/
theorem serve_full_on_mismatch (cfg : Config) (req : Req)
    (body : StaticFile.Bytes) (hfile : cfg.fs (StaticFile.resolvePath cfg req) = some body)
    (hmiss : ¬ PreconditionFails req.ifNoneMatch (cfg.etag (StaticFile.resolvePath cfg req)))
    (hims : StaticFile.ifModifiedSince304 (cfg.lastModified (StaticFile.resolvePath cfg req))
        req.ifModifiedSince = false)
    (hrange : req.range = none) :
    (serve cfg req).status = 200 ∧ (serve cfg req).body = body := by
  unfold serve
  exact serveResolved_full_on_mismatch cfg req (StaticFile.resolvePath cfg req) body hfile hmiss hims hrange

/-! ## If-Modified-Since is honored on the deployed path

RFC 7232 §6 step 4: "When the method is GET or HEAD, If-None-Match is not
present, and If-Modified-Since is present, evaluate the If-Modified-Since
precondition … if false, respond 304 (Not Modified)." The deployed handler
`serveResolved` (the one `serve` calls) evaluates `Req.ifModifiedSince` after
the `If-None-Match` precondition (§6): a not-modified representation with no
`If-None-Match` yields `304` with an empty body. The theorem exhibits a concrete
request whose `If-Modified-Since` is at or after the representation's
`Last-Modified` (so §6 step 4 mandates `304`) and confirms the real handler now
returns `304`, not `200`. -/

/-- A representation whose `Last-Modified` is epoch second 100. -/
def imsCfg : Config where
  docRoot := []
  fs := fun _ => some [(1 : UInt8)]
  isDir := fun _ => false
  readDir := fun _ => []
  etag := fun _ => ⟨false, "v1"⟩
  lastModified := fun _ => 100

/-- A GET with no `If-None-Match`, no `Range`, and `If-Modified-Since = 200`
(≥ the representation's `Last-Modified = 100`): RFC 7232 §6 step 4 mandates a
`304`. -/
def imsReq : Req :=
  { target := [], ifNoneMatch := [], range := none, ifModifiedSince := some 200 }

/-- **`serve_honors_ifModifiedSince` (WITNESS).** The deployed handler returns
`304` with an empty body for `imsReq` — no `If-None-Match`, and its
`If-Modified-Since` (200) is at or after the representation's `Last-Modified`
(100), which RFC 7232 §6 step 4 mandates as a `304`. `serveResolved`/`serve` now
evaluate the `If-Modified-Since` precondition on the deployed path, so the old
`200` behavior would fail this theorem's `.status = 304`. -/
theorem serve_honors_ifModifiedSince :
    (serve imsCfg imsReq).status = 304
    ∧ (serve imsCfg imsReq).body = []
    ∧ StaticFile.ifModifiedSince304 (imsCfg.lastModified []) imsReq.ifModifiedSince = true := by
  decide

/-! ## Concrete witnesses — the real handler on concrete conditional requests -/

/-- A configuration whose representation carries the strong entity-tag `"abc"`. -/
def wCfg : Config where
  docRoot := []
  fs := fun _ => some [(7 : UInt8), 8, 9]
  isDir := fun _ => false
  readDir := fun _ => []
  etag := fun _ => ⟨false, "abc"⟩
  lastModified := fun _ => 0

/-- **Match witness (weak flag ignored).** An `If-None-Match: W/"abc"` weak-tag
against the strong current tag `"abc"` matches under weak comparison
(RFC 7232 §2.3.2), so the real handler answers `304` with an empty body. -/
theorem witness_weak_match_304 :
    (serveResolved wCfg { target := [], ifNoneMatch := [⟨true, "abc"⟩] } []).status = 304
  ∧ (serveResolved wCfg { target := [], ifNoneMatch := [⟨true, "abc"⟩] } []).body = [] := by
  decide

/-- **Mismatch witness.** An `If-None-Match: "xyz"` that does not match the
current `"abc"` leaves the precondition true, so the real handler serves the full
`200` with the complete body — not a `304`. -/
theorem witness_mismatch_200 :
    (serveResolved wCfg { target := [], ifNoneMatch := [⟨false, "xyz"⟩] } []).status = 200
  ∧ (serveResolved wCfg { target := [], ifNoneMatch := [⟨false, "xyz"⟩] } []).body
        = [(7 : UInt8), 8, 9] := by
  decide

/-- **Absent-header witness.** With no `If-None-Match` the precondition cannot
fail; the real handler serves the full `200`. -/
theorem witness_absent_200 :
    (serveResolved wCfg { target := [] } []).status = 200 := by decide

/-- The independent precondition genuinely distinguishes match from mismatch:
`W/"abc"` fails the precondition against `"abc"`, `"xyz"` does not. -/
theorem spec_distinguishes :
    PreconditionFails [⟨true, "abc"⟩] ⟨false, "abc"⟩
  ∧ ¬ PreconditionFails [⟨false, "xyz"⟩] ⟨false, "abc"⟩ := by
  constructor
  · exact ⟨⟨true, "abc"⟩, List.mem_cons_self _ _, rfl⟩
  · rintro ⟨t, ht, hcmp⟩
    simp only [List.mem_singleton] at ht
    subst ht
    rw [weakCompare] at hcmp
    exact absurd hcmp (by decide)

#guard (serveResolved wCfg { target := [], ifNoneMatch := [⟨true, "abc"⟩] } []).status = 304
#guard (serveResolved wCfg { target := [], ifNoneMatch := [⟨false, "xyz"⟩] } []).status = 200
#guard (serve imsCfg imsReq).status = 304
#guard (serve imsCfg imsReq).body = []

end StaticEtagCorrect

#print axioms StaticEtagCorrect.serveResolved_304_iff
#print axioms StaticEtagCorrect.serve_304_iff
#print axioms StaticEtagCorrect.serveResolved_full_on_mismatch
#print axioms StaticEtagCorrect.preconditionFails_iff_hit
#print axioms StaticEtagCorrect.serve_honors_ifModifiedSince
