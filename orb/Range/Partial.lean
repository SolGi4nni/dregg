/-
# Range.Partial — single byte-range serving (RFC 9110 §14.1.2 / RFC 7233 §2.1, §4.1, §4.4)

A self-contained sans-IO model of the single `Range: bytes=a-b` decision for a
static representation held in memory as a list of octets. It closes the
`h1.range` parity row: a `Range` request selects `206 (Partial Content)` with
the exact byte sub-slice and a `Content-Range: bytes a-b/L` header; an
unsatisfiable first-byte-pos selects `416 (Range Not Satisfiable)` with a
`Content-Range: bytes */L` header; an absent or syntactically-invalid `Range`
falls back to a full `200 (OK)`.

This is a leaf: the representation octets enter as a plain `List UInt8`; there
is no filesystem, no I/O, and no dependency on any other module. The theorems
are about the response-selection value, and the `Content-Range` header is
rendered to its exact wire string.

Theorems:
  * `range_serves_slice`       — `bytes=a-b` with `a ≤ b < L` yields `206`,
                                 body `= slice body a b`, and the exact
                                 `Content-Range: bytes a-b/L` header string.
  * `range_unsatisfiable_416`  — first-byte-pos `a ≥ L` yields `416` with an
                                 empty body and `Content-Range: bytes */L`.
  * `range_full_200`           — an absent or invalid (`b < a`) `Range` yields
                                 `200` carrying the complete representation and
                                 no `Content-Range`.

Left as a boundary (UNCLOSED): the `bytes=a-` (open-ended) and `bytes=-k`
(suffix) forms, multi-range `multipart/byteranges`, and `If-Range` gating are
not modeled here — this leaf owns only the closed `bytes=a-b` single-range
surface. The `L-1` remainder clamp (`b ≥ L`) is handled by `serve` but the
named theorems characterize only the `b < L` and `a ≥ L` regions.
-/

namespace Range.Partial

/-- Raw representation octets, modeled as a list for ease of reasoning. -/
abbrev Bytes := List UInt8

/-- A single closed byte-range-spec `bytes=first-last` (RFC 7233 §2.1). -/
structure Spec where
  first : Nat
  last : Nat
deriving DecidableEq, Repr

/-- The exact inclusive byte sub-slice `body[s], …, body[e]` (length `e-s+1`
when well-formed) — the octet sequence a `206` response body carries
(RFC 9110 §14.1.2). -/
def slice (b : Bytes) (s e : Nat) : Bytes := (b.drop s).take (e - s + 1)

/-- The slice has the RFC 9110 §14.1.2 partial length `e - s + 1` whenever the
offsets are well-formed (`s ≤ e`) and in range (`e < length`). -/
theorem slice_length (b : Bytes) (s e : Nat) (hse : s ≤ e) (he : e < b.length) :
    (slice b s e).length = e - s + 1 := by
  unfold slice
  rw [List.length_take, List.length_drop]
  omega

/-- The `Content-Range` response-header value (RFC 9110 §14.4). `satisfied` is
the ordinary `bytes first-last/complete` form; a `416` carries the unsatisfied
`bytes */complete` form (the `first`/`last` fields are then irrelevant). -/
structure ContentRange where
  satisfied : Bool
  first : Nat
  last : Nat
  complete : Nat
deriving DecidableEq, Repr

/-- The exact wire rendering of the `Content-Range` header value
(RFC 9110 §14.4): `bytes a-b/L` when satisfied, `bytes */L` otherwise. -/
def ContentRange.render (cr : ContentRange) : String :=
  if cr.satisfied then s!"bytes {cr.first}-{cr.last}/{cr.complete}"
  else s!"bytes */{cr.complete}"

/-- The HTTP response the single-range handler selects. -/
inductive Resp where
  /-- `200 OK`: the complete representation. -/
  | ok (body : Bytes)
  /-- `206 Partial Content`: the sub-slice and its `Content-Range` value. -/
  | partialContent (body : Bytes) (cr : ContentRange)
  /-- `416 Range Not Satisfiable`: no body, an unsatisfied `Content-Range`. -/
  | notSatisfiable (cr : ContentRange)
deriving Repr

/-- The numeric status line. -/
def Resp.status : Resp → Nat
  | .ok _ => 200
  | .partialContent _ _ => 206
  | .notSatisfiable _ => 416

/-- The response body; a `416` carries none. -/
def Resp.body : Resp → Bytes
  | .ok b => b
  | .partialContent b _ => b
  | .notSatisfiable _ => []

/-- The `Content-Range` header value, present on `206`/`416`, absent on `200`. -/
def Resp.contentRange : Resp → Option ContentRange
  | .ok _ => none
  | .partialContent _ cr => some cr
  | .notSatisfiable cr => some cr

/-- **The single-range handler.** Given a representation `body` and an optional
`bytes=a-b` spec, select the response (RFC 9110 §14.1.2, RFC 7233 §4.1, §4.4):

  * no `Range`                → `200`, full body.
  * `b < a` (invalid spec)    → `200`, full body (RFC 7233 §3.1: an invalid
                                 `Range` is ignored, not `416`).
  * `a ≥ L` (unsatisfiable)   → `416`, `bytes */L`.
  * otherwise                 → `206`, slice `a … min(b, L-1)`, the last-pos
                                 clamped to the representation end. -/
def serve (body : Bytes) (range : Option Spec) : Resp :=
  let L := body.length
  match range with
  | none => .ok body
  | some ⟨a, b⟩ =>
      if b < a then .ok body
      else if a ≥ L then
        .notSatisfiable { satisfied := false, first := 0, last := 0, complete := L }
      else
        let e := min b (L - 1)
        .partialContent (slice body a e)
          { satisfied := true, first := a, last := e, complete := L }

/-! ## The named parity theorems -/

/-- **`range_serves_slice`** — a well-formed, satisfiable single range
`bytes=a-b` with `a ≤ b < L` yields `206 (Partial Content)` whose body is
exactly `slice body a b` and whose `Content-Range` renders to the exact wire
string `bytes a-b/L` (RFC 9110 §14.1.2, §14.4). -/
theorem range_serves_slice (body : Bytes) (a b : Nat)
    (hab : a ≤ b) (hbL : b < body.length) :
    (serve body (some ⟨a, b⟩)).status = 206 ∧
    (serve body (some ⟨a, b⟩)).body = slice body a b ∧
    (∃ cr, (serve body (some ⟨a, b⟩)).contentRange = some cr ∧
           cr.render = s!"bytes {a}-{b}/{body.length}") := by
  have hba : ¬ b < a := by omega
  have haL : ¬ a ≥ body.length := by omega
  have hmin : min b (body.length - 1) = b := by omega
  have hserve : serve body (some ⟨a, b⟩)
      = .partialContent (slice body a b)
          { satisfied := true, first := a, last := b, complete := body.length } := by
    simp only [serve, if_neg hba, if_neg haL, hmin]
  rw [hserve]
  refine ⟨rfl, rfl, ⟨_, rfl, ?_⟩⟩
  simp [ContentRange.render]

/-- **`range_unsatisfiable_416`** — a first-byte-pos at or beyond the
representation length (`a ≥ L`, with `a ≤ b`) yields `416 (Range Not
Satisfiable)` with an empty body and a `Content-Range: bytes */L` header
(RFC 9110 §15.5.17). -/
theorem range_unsatisfiable_416 (body : Bytes) (a b : Nat)
    (hab : a ≤ b) (haL : body.length ≤ a) :
    (serve body (some ⟨a, b⟩)).status = 416 ∧
    (serve body (some ⟨a, b⟩)).body = [] ∧
    (∃ cr, (serve body (some ⟨a, b⟩)).contentRange = some cr ∧
           cr.render = s!"bytes */{body.length}") := by
  have hba : ¬ b < a := by omega
  have haL' : a ≥ body.length := haL
  have hserve : serve body (some ⟨a, b⟩)
      = .notSatisfiable { satisfied := false, first := 0, last := 0, complete := body.length } := by
    simp only [serve, if_neg hba, if_pos haL']
  rw [hserve]
  refine ⟨rfl, rfl, ⟨_, rfl, ?_⟩⟩
  simp [ContentRange.render]

/-- **`range_full_200`** — an absent `Range`, or a syntactically invalid one
(`b < a`), yields `200 (OK)` carrying the complete representation and no
`Content-Range` header (RFC 7233 §3.1). -/
theorem range_full_200 (body : Bytes) (range : Option Spec)
    (h : range = none ∨ ∃ a b, range = some ⟨a, b⟩ ∧ b < a) :
    (serve body range).status = 200 ∧
    (serve body range).body = body ∧
    (serve body range).contentRange = none := by
  rcases h with hnone | ⟨a, b, hsome, hba⟩
  · subst hnone
    refine ⟨rfl, rfl, rfl⟩
  · subst hsome
    have hserve : serve body (some ⟨a, b⟩) = .ok body := by
      simp only [serve, if_pos hba]
    rw [hserve]
    refine ⟨rfl, rfl, rfl⟩

/-! ## Non-vacuity: a worked RFC 9110 §14.1.2 example on a real body

`bytes=1-3` over a 6-octet representation selects octets `[b,c,d]` at inclusive
offsets `1..3`, and the header renders to `bytes 1-3/6`. These are decided on a
concrete `List UInt8`, so the theorems above are not vacuously about an empty
representation. -/

/-- `serve` on a concrete body actually produces the `206` slice. -/
example : (serve [104, 101, 108, 108, 111, 33] (some ⟨1, 3⟩)).body
    = [101, 108, 108] := by decide

/-- The concrete `Content-Range` value is the satisfied `1-3/6`. -/
example : (serve [104, 101, 108, 108, 111, 33] (some ⟨1, 3⟩)).contentRange
    = some { satisfied := true, first := 1, last := 3, complete := 6 } := by decide

/-- …and that value renders to its exact wire string. -/
example : (ContentRange.mk true 1 3 6).render = "bytes 1-3/6" := by rfl

/-- `bytes=9-9` over the same 6-octet body is unsatisfiable (`a = 9 ≥ 6`). -/
example : (serve [104, 101, 108, 108, 111, 33] (some ⟨9, 9⟩)).contentRange
    = some { satisfied := false, first := 0, last := 0, complete := 6 } := by decide

/-- …and the unsatisfied value renders `bytes */6`. -/
example : (ContentRange.mk false 0 0 6).render = "bytes */6" := by rfl

/-- An invalid spec (`b < a`) is ignored and the full body is served. -/
example : (serve [104, 101, 108, 108, 111, 33] (some ⟨3, 1⟩)).status = 200 := by
  decide

end Range.Partial
