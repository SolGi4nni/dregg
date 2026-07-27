import Reactor.Serialize

/-!
# Cache.Conditional — verified conditional-request preconditions (RFC 7232)

The fresh-hit cache gate (`Reactor.Stage.Cache`) short-circuits on a *stored*
fresh entry. This module is the orthogonal half: **conditional requests** — a
client that already holds a representation asks the origin to transfer bytes
only if its copy is stale. RFC 7232 (*HTTP Conditional Requests*) defines four
request header fields — `If-Match`, `If-Unmodified-Since`, `If-None-Match`,
`If-Modified-Since` — and the precondition evaluation order (§6) that turns them
into a `304 (Not Modified)` (validated, no body re-transfer) or a
`412 (Precondition Failed)` (state changed under the client's assumption).

The model here is a total, pure evaluator

    evaluate : (safe : Bool) → Conds → Resource → Outcome

over an explicit, boundary-supplied notion of the resource's current validators
(its strong entity-tag and `Last-Modified` instant). `safe` is `true` for the
selection methods GET / HEAD, for which a matching `If-None-Match` /
not-modified `If-Modified-Since` yields `304`; for other methods a matching
`If-None-Match` is a `412` (§3.2). The uninterpreted boundary — exactly as in
`Cache.lean` (§5.2: HTTP-date parsing is out of model) — is the reduction of an
HTTP-date header to a `Nat` instant; the arithmetic and the precedence are
theorems.

## Entity-tag comparison (§2.3)

An `ETag` is a `weak` flag plus the `opaque` validator bytes.
* **Strong comparison** (`strongEq`, used by `If-Match`, §2.3.2): matches iff
  *neither* tag is weak and the opaque bytes are equal.
* **Weak comparison** (`weakEq`, used by `If-None-Match`, §2.3.2): matches iff
  the opaque bytes are equal, regardless of the weak flags.

## Precondition evaluation order (§6)

1. `If-Match`: if it does not pass (strong) → `412`.
2. else `If-Unmodified-Since`: if the resource *was* modified after the date
   (`lastModified > date`) → `412`.
3. `If-None-Match`: if it matches (weak) → `304` for a selection method, else
   `412`.
4. else `If-Modified-Since` (selection method): if *not* modified since the date
   (`lastModified ≤ date`) → `304`.
5. otherwise the normal `200` transfer proceeds.

## Headline theorems (each 0-`sorry`, non-vacuous, clean-axiom)

* `if_none_match_304` — an `If-None-Match` that matches the resource ETag (with
  `If-Match` / `If-Unmodified-Since` absent) produces a `304` whose body is
  **empty** and whose ETag validator header is **preserved**.
* `if_modified_since_304` — with the entity-tag conditionals absent, an
  `If-Modified-Since` whose date is at least the `Last-Modified` instant (the
  resource was *not* modified) produces a `304` with an empty body.
* `if_match_412` — an `If-Match` that fails the strong comparison produces a
  `412 (Precondition Failed)` with an empty body.

Discrimination (the spec is not vacuous — the conditions are load-bearing):
`if_none_match_mismatch_200` (a non-matching `If-None-Match` transfers the full
`200`), `if_match_pass_200` (a matching `If-Match` does *not* fail), and
`evaluate_honors_if_match` (a mutant that drops the `If-Match` step disagrees
with `evaluate` on a concrete request — so honoring `If-Match` changes bytes).
`demo_if_none_match_304` drives the whole path from a real `Proto.Request`'s
`If-None-Match` header bytes.
-/

namespace Cache.Conditional

open Reactor (Response reasonOK)
open Proto (Bytes Request)

/-! ## Entity tags and their §2.3 comparisons -/

/-- An HTTP entity-tag validator (§2.3): a `weak` flag and the opaque
validator bytes (the content *between* the quotes on the wire). -/
structure ETag where
  weak : Bool
  tag : Bytes
deriving Repr, DecidableEq

/-- §2.3.2 **strong comparison**: matches iff neither tag is weak and the
opaque validators are byte-equal. Used by `If-Match` / `If-Unmodified-Since`. -/
def ETag.strongEq (a b : ETag) : Bool :=
  !a.weak && !b.weak && decide (a.tag = b.tag)

/-- §2.3.2 **weak comparison**: matches iff the opaque validators are
byte-equal, regardless of the weak flags. Used by `If-None-Match` /
`If-Modified-Since`. -/
def ETag.weakEq (a b : ETag) : Bool :=
  decide (a.tag = b.tag)

/-- The wire rendering of an entity-tag: optional `W/` prefix, then the opaque
bytes in double quotes. -/
def ETag.render (e : ETag) : Bytes :=
  (if e.weak then [87, 47] else []) ++ [34] ++ e.tag ++ [34]

/-- The value of an `If-Match` / `If-None-Match` field (§3.1, §3.2): either the
wildcard `*` (any current representation) or a list of candidate entity-tags. -/
inductive IfList where
  | star
  | tags (ts : List ETag)
deriving Repr, DecidableEq

/-- §3.1 `If-Match` passes iff the field is `*` (resource exists) or some listed
tag matches the resource ETag under **strong** comparison. -/
def IfList.matchesStrong (l : IfList) (etag : ETag) : Bool :=
  match l with
  | .star => true
  | .tags ts => ts.any (fun t => t.strongEq etag)

/-- §3.2 `If-None-Match` matches iff the field is `*` (resource exists) or some
listed tag matches the resource ETag under **weak** comparison. -/
def IfList.matchesWeak (l : IfList) (etag : ETag) : Bool :=
  match l with
  | .star => true
  | .tags ts => ts.any (fun t => t.weakEq etag)

/-! ## The request conditionals and the resource validators -/

/-- The four RFC 7232 precondition header fields, already extracted. A date
conditional is a `Nat` instant (the HTTP-date → epoch reduction is the boundary,
cf. `Cache.lean` §5.2). -/
structure Conds where
  ifMatch : Option IfList := none
  ifUnmodifiedSince : Option Nat := none
  ifNoneMatch : Option IfList := none
  ifModifiedSince : Option Nat := none
deriving Repr

/-- The origin's current validators for the selected representation, plus the
bytes it would transfer on a full `200`. `lastModified` is the representation's
`Last-Modified` instant (seconds); `lastModifiedHeader` is its rendered value. -/
structure Resource where
  etag : ETag
  lastModified : Nat
  lastModifiedHeader : Bytes
  body : Bytes
deriving Repr

/-! ## The evaluator (§6 precedence) -/

/-- The precondition outcome. -/
inductive Outcome where
  /-- Proceed with the normal (`200`) transfer. -/
  | normal
  /-- `304 (Not Modified)` — the client's copy is still valid. -/
  | notModified
  /-- `412 (Precondition Failed)` — the state changed under the client's
  assumption. -/
  | preconditionFailed
deriving Repr, DecidableEq

/-- §6 steps 3–4: the `If-None-Match` / `If-Modified-Since` tail, reached only
after the `If-Match` / `If-Unmodified-Since` guards pass. -/
def evalNoneMatch (safe : Bool) (c : Conds) (r : Resource) : Outcome :=
  match c.ifNoneMatch with
  | some inm =>
    if inm.matchesWeak r.etag then
      -- §3.2: a match is 304 for a selection method, 412 otherwise.
      if safe then .notModified else .preconditionFailed
    else .normal
  | none =>
    match c.ifModifiedSince with
    | some d =>
      -- §3.3: not modified iff lastModified ≤ date (selection methods only).
      if safe && decide (r.lastModified ≤ d) then .notModified else .normal
    | none => .normal

/-- §6 full precondition evaluation, in the mandated order. -/
def evaluate (safe : Bool) (c : Conds) (r : Resource) : Outcome :=
  match c.ifMatch with
  | some im =>
    -- §3.1: If-Match present.
    if im.matchesStrong r.etag then evalNoneMatch safe c r else .preconditionFailed
  | none =>
    match c.ifUnmodifiedSince with
    | some d =>
      -- §3.4: If-Unmodified-Since — modified after the date ⇒ 412.
      if decide (r.lastModified ≤ d) then evalNoneMatch safe c r else .preconditionFailed
    | none => evalNoneMatch safe c r

/-! ## Rendering an outcome to a response (§4.1) -/

/-- `"Not Modified"`. -/
def reason304 : Bytes := "Not Modified".toUTF8.toList
/-- `"Precondition Failed"`. -/
def reason412 : Bytes := "Precondition Failed".toUTF8.toList
/-- Canonical lowercase `etag` header name. -/
def etagName : Bytes := "etag".toUTF8.toList
/-- Canonical lowercase `last-modified` header name. -/
def lastModifiedName : Bytes := "last-modified".toUTF8.toList

/-- The validator/metadata headers a `304` (§4.1) and a full `200` both carry:
the current `ETag` and `Last-Modified`. A `304` re-uses these so a cache can
update its stored headers; the client's held body is *not* re-transferred. -/
def metadataHeaders (r : Resource) : List (Bytes × Bytes) :=
  [(etagName, r.etag.render), (lastModifiedName, r.lastModifiedHeader)]

/-- §4.1 `304 (Not Modified)`: the validator headers are preserved and the body
is **empty** (the client keeps its cached representation). -/
def notModifiedResponse (r : Resource) : Response :=
  { status := 304, reason := reason304, headers := metadataHeaders r, body := [] }

/-- `412 (Precondition Failed)`: no representation is transferred. -/
def preconditionFailedResponse : Response :=
  { status := 412, reason := reason412, headers := [], body := [] }

/-- The full `200 (OK)` transfer with the resource's body and validators. -/
def fullResponse (r : Resource) : Response :=
  { status := 200, reason := reasonOK, headers := metadataHeaders r, body := r.body }

/-- Render a precondition outcome to the wire response it selects. -/
def respond (r : Resource) : Outcome → Response
  | .normal => fullResponse r
  | .notModified => notModifiedResponse r
  | .preconditionFailed => preconditionFailedResponse

/-! ## Headline theorems -/

/-- §6 step 3 reduction: with the earlier guards absent, a matching
`If-None-Match` for a selection method evaluates to `notModified`. -/
theorem eval_none_match_hit (c : Conds) (r : Resource) (inm : IfList)
    (hmatch : c.ifMatch = none) (hunmod : c.ifUnmodifiedSince = none)
    (hnm : c.ifNoneMatch = some inm) (hhit : inm.matchesWeak r.etag = true) :
    evaluate true c r = Outcome.notModified := by
  simp [evaluate, evalNoneMatch, hmatch, hunmod, hnm, hhit]

/-- **`If-None-Match` → 304.** A conditional GET whose `If-None-Match` matches
the resource's current ETag (weak comparison, §2.3.2), with no `If-Match` /
`If-Unmodified-Since` overriding it, is answered `304 (Not Modified)`: the
status is `304`, the **body is empty** (the client keeps its copy), and the
resource's `ETag` validator header is **preserved** on the response (§4.1). -/
theorem if_none_match_304 (c : Conds) (r : Resource) (inm : IfList)
    (hmatch : c.ifMatch = none) (hunmod : c.ifUnmodifiedSince = none)
    (hnm : c.ifNoneMatch = some inm) (hhit : inm.matchesWeak r.etag = true) :
    (respond r (evaluate true c r)).status = 304
    ∧ (respond r (evaluate true c r)).body = []
    ∧ (etagName, r.etag.render) ∈ (respond r (evaluate true c r)).headers := by
  rw [eval_none_match_hit c r inm hmatch hunmod hnm hhit]
  refine ⟨rfl, rfl, ?_⟩
  simp [respond, notModifiedResponse, metadataHeaders]

/-- §6 step 4 reduction: with the entity-tag conditionals absent, an
`If-Modified-Since` whose date is at least the `Last-Modified` instant evaluates
to `notModified`. -/
theorem eval_modified_since_not_modified (c : Conds) (r : Resource) (d : Nat)
    (hmatch : c.ifMatch = none) (hunmod : c.ifUnmodifiedSince = none)
    (hnm : c.ifNoneMatch = none) (hims : c.ifModifiedSince = some d)
    (hle : r.lastModified ≤ d) :
    evaluate true c r = Outcome.notModified := by
  simp [evaluate, evalNoneMatch, hmatch, hunmod, hnm, hims, hle]

/-- **`If-Modified-Since` → 304.** With no entity-tag conditionals, a conditional
GET whose `If-Modified-Since` date is at least the representation's
`Last-Modified` instant (so it was *not* modified, §3.3) is answered
`304 (Not Modified)` with an **empty body**. -/
theorem if_modified_since_304 (c : Conds) (r : Resource) (d : Nat)
    (hmatch : c.ifMatch = none) (hunmod : c.ifUnmodifiedSince = none)
    (hnm : c.ifNoneMatch = none) (hims : c.ifModifiedSince = some d)
    (hle : r.lastModified ≤ d) :
    (respond r (evaluate true c r)).status = 304
    ∧ (respond r (evaluate true c r)).body = [] := by
  rw [eval_modified_since_not_modified c r d hmatch hunmod hnm hims hle]
  exact ⟨rfl, rfl⟩

/-- §3.1 reduction: an `If-Match` that fails the strong comparison evaluates to
`preconditionFailed` regardless of the selection method. -/
theorem eval_if_match_fail (safe : Bool) (c : Conds) (r : Resource) (im : IfList)
    (hm : c.ifMatch = some im) (hfail : im.matchesStrong r.etag = false) :
    evaluate safe c r = Outcome.preconditionFailed := by
  simp [evaluate, hm, hfail]

/-- **`If-Match` fails → 412.** An `If-Match` whose listed tags none match the
resource ETag under strong comparison (§2.3.2) fails the precondition and is
answered `412 (Precondition Failed)` with an **empty body** — the origin does
*not* apply the client's assumed-state request. -/
theorem if_match_412 (c : Conds) (r : Resource) (im : IfList)
    (hm : c.ifMatch = some im) (hfail : im.matchesStrong r.etag = false) :
    (respond r (evaluate true c r)).status = 412
    ∧ (respond r (evaluate true c r)).body = [] := by
  rw [eval_if_match_fail true c r im hm hfail]
  exact ⟨rfl, rfl⟩

/-! ## Discrimination — the conditions are load-bearing (non-vacuity) -/

/-- A **non-matching** `If-None-Match` does *not* yield `304`: the full `200`
transfer proceeds (body present). Shows the `304` in `if_none_match_304` genuinely
depends on the match. -/
theorem if_none_match_mismatch_200 (c : Conds) (r : Resource) (inm : IfList)
    (hmatch : c.ifMatch = none) (hunmod : c.ifUnmodifiedSince = none)
    (hnm : c.ifNoneMatch = some inm) (hmiss : inm.matchesWeak r.etag = false) :
    evaluate true c r = Outcome.normal
    ∧ (respond r (evaluate true c r)).status = 200
    ∧ (respond r (evaluate true c r)).body = r.body := by
  have he : evaluate true c r = Outcome.normal := by
    simp [evaluate, evalNoneMatch, hmatch, hunmod, hnm, hmiss]
  rw [he]
  exact ⟨rfl, rfl, rfl⟩

/-- A **passing** `If-Match` does *not* fail: evaluation proceeds past step 1.
Shows the `412` in `if_match_412` genuinely depends on the mismatch. -/
theorem if_match_pass_200 (c : Conds) (r : Resource) (im : IfList)
    (hm : c.ifMatch = some im) (hpass : im.matchesStrong r.etag = true)
    (hunmod : c.ifNoneMatch = none) (hims : c.ifModifiedSince = none) :
    evaluate true c r = Outcome.normal := by
  simp [evaluate, evalNoneMatch, hm, hpass, hunmod, hims]

/-- A **mutant** evaluator that drops the `If-Match` guard entirely (a common
real-world bug — the reference server this parity row targets ignored `If-Match`
and returned `200` on a mismatch). -/
def evaluateNoIfMatch (safe : Bool) (c : Conds) (r : Resource) : Outcome :=
  evalNoneMatch safe c r

/-- **`If-Match` is load-bearing.** There is a concrete request on which the
faithful `evaluate` and the `If-Match`-dropping mutant `evaluateNoIfMatch`
disagree — so honoring `If-Match` changes the emitted status. This witnesses that
`if_match_412`'s hypothesis is satisfiable *and* that its conclusion is not what a
degenerate evaluator would produce (the reference bug the parity row fixes). -/
theorem evaluate_honors_if_match :
    ∃ (c : Conds) (r : Resource),
      evaluate true c r ≠ evaluateNoIfMatch true c r := by
  refine ⟨{ ifMatch := some (.tags [{ weak := false, tag := [1] }]) },
          { etag := { weak := false, tag := [2] },
            lastModified := 0, lastModifiedHeader := [], body := [9] }, ?_⟩
  decide

/-! ## End-to-end: a real request's `If-None-Match` header bytes drive the 304 -/

/-- `if-none-match` field name, explicit ASCII bytes (so the demo reduces in the
kernel without forcing a `String` decode). -/
def ifNoneMatchName : Bytes := [105, 102, 45, 110, 111, 110, 101, 45, 109, 97, 116, 99, 104]

/-- Parse the opaque bytes up to the closing `"` of a quoted-string. -/
def upToQuote : Bytes → Option Bytes
  | [] => none
  | 34 :: _ => some []
  | c :: rest => (upToQuote rest).map (fun t => c :: t)

/-- Parse a single wire entity-tag: optional `W/` prefix, then a quoted opaque. -/
def parseETag (b : Bytes) : Option ETag :=
  match b with
  | 87 :: 47 :: 34 :: rest => (upToQuote rest).map (ETag.mk true)
  | 34 :: rest => (upToQuote rest).map (ETag.mk false)
  | _ => none

/-- Parse an `If-Match` / `If-None-Match` field value: `*`, else one entity-tag. -/
def parseIfList (b : Bytes) : Option IfList :=
  match b with
  | [42] => some .star
  | _ => (parseETag b).map (fun e => .tags [e])

/-- Extract the entity-tag conditionals from a real request's headers (§3.1/§3.2).
Date conditionals are left to the boundary (HTTP-date parsing, §5.2). -/
def condsOf (req : Request) : Conds :=
  { ifNoneMatch := (req.headers.lookup ifNoneMatchName).bind parseIfList }

/-- `GET` / `HEAD` are the selection methods for which a validated conditional is
`304` (§3.2/§3.3). -/
def isSafe (m : Bytes) : Bool := m == [71, 69, 84] || m == [72, 69, 65, 68]

/-- The demo resource: a strong ETag with opaque bytes `[1,2,3]`. -/
def demoResource : Resource :=
  { etag := { weak := false, tag := [1, 2, 3] }
    lastModified := 1000
    lastModifiedHeader := []
    body := [104, 105] }

/-- A real `GET` request carrying `If-None-Match: "\x01\x02\x03"` (the demo
resource's rendered strong ETag), as explicit header bytes. -/
def demoReq : Request :=
  { method := [71, 69, 84]
    target := [47, 100, 111, 99]
    headers := [(ifNoneMatchName, demoResource.etag.render)] }

/-- The extracted `If-None-Match` is exactly the demo resource's tag. -/
theorem demo_conds : (condsOf demoReq).ifNoneMatch
    = some (.tags [{ weak := false, tag := [1, 2, 3] }]) := by decide

/-- **End-to-end 304.** Driving the whole path — extract the conditionals from the
real request bytes, evaluate, render — on the demo `GET` whose `If-None-Match`
matches yields a `304` with an empty body. Fully concrete: the parse, the weak
comparison, and the render all fire in the kernel. -/
theorem demo_if_none_match_304 :
    (respond demoResource
      (evaluate (isSafe demoReq.method) (condsOf demoReq) demoResource)).status = 304
    ∧ (respond demoResource
      (evaluate (isSafe demoReq.method) (condsOf demoReq) demoResource)).body = [] := by
  decide

/-- **End-to-end 412.** A concrete `If-Match` mismatch renders `412` with an empty
body (the boundary case the reference server got wrong). -/
theorem demo_if_match_412 :
    (respond demoResource
      (evaluate true { ifMatch := some (.tags [{ weak := false, tag := [9] }]) }
        demoResource)).status = 412 := by
  decide

/-- **End-to-end 304 via `If-Modified-Since`.** A concrete not-modified date
(`lastModified = 1000 ≤ 2000`) renders `304`. -/
theorem demo_if_modified_since_304 :
    (respond demoResource
      (evaluate true { ifModifiedSince := some 2000 } demoResource)).status = 304 := by
  decide

#print axioms if_none_match_304
#print axioms if_modified_since_304
#print axioms if_match_412
#print axioms evaluate_honors_if_match
#print axioms demo_if_none_match_304

end Cache.Conditional
