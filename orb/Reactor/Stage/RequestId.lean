import Reactor.Pipeline

/-!
# Reactor.Stage.RequestId — request-id generation / propagation, as a pipeline stage

A byte-driving `Stage` for the extensible serve fold. On every request it resolves a
request identifier — preserving a trusted incoming id when one is present, otherwise
generating a fresh, well-formed one — stashes it into the context (so an upstream
proxy pass carries it) and, on the response phase, stamps it as a header. This is the
trace/correlation id every request carries.

## The generated id is well-formed by construction

`genId seed` renders a deterministic id in the canonical UUID shape
`xxxxxxxx-xxxx-4xxx-8xxx-xxxxxxxxxxxx`: 32 lowercase hex characters laid out in the
`8-4-4-4-12` groups with hyphens, a version nibble `4`, and a variant nibble `8`.
`genId_length` proves it is EXACTLY 36 bytes for ANY seed (the base length invariant),
and `wellFormed` (checked on concrete seeds) confirms the hyphen and version/variant
positions — so a generated id is a genuine well-formed identifier, not a placeholder.
`genId_distinct` exhibits two seeds producing different ids (it genuinely varies).

## The resolve decision (trusted preservation vs generation)

`resolve trust incoming seed` is the reference policy, total: a *trusted* incoming id
is preserved verbatim; otherwise a fresh id is generated. Its truth table
(`resolve_trust_preserve`, `resolve_untrusted_generate`, `resolve_absent_generate`)
is proven directly.

## Propagation is a genuine byte effect

The stage stashes the resolved id under `ridAttrKey` in the request phase (upstream
propagation) and adds `(ridName, id)` on the response phase. `ridStage_propagates`
proves the header — carrying the exact resolved id — is present in the FINALIZED
response the serializer renders, for ANY tail and handler, on both the generate path
(`ridStage_generates_wellformed`) and the trusted-echo path (`ridStage_echoes`).
-/

namespace Reactor.Stage.RequestId

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Hex rendering -/

/-- Map a nibble (`0`–`15`) to its lowercase hex ASCII byte. -/
def hexDigit (n : Nat) : UInt8 :=
  let d := n % 16
  if d < 10 then (48 + d).toUInt8 else (87 + d).toUInt8

/-- A deterministic stream of 30 hex nibbles derived from `seed` — the entropy body
of the generated id. Length is exactly 30 by construction. -/
def nibblesOf (seed : Nat) : Bytes :=
  (List.range 30).map (fun i => hexDigit ((seed / (16 ^ i)) % 16))

/-- The nibble stream is always 30 bytes. -/
theorem nibblesOf_length (seed : Nat) : (nibblesOf seed).length = 30 := by
  simp [nibblesOf]

/-! ## The canonical layout -/

/-- ASCII `'-'`. -/
def hy : UInt8 := 45

/-- The version nibble `'4'` (UUID v4). -/
def verChar : UInt8 := 52

/-- The variant nibble `'8'` (RFC 4122 variant `10xx`). -/
def varChar : UInt8 := 56

/-- A fixed-length slice of the nibble stream: `len` bytes starting at index `i`. -/
def block (ns : Bytes) (i len : Nat) : Bytes := (ns.drop i).take len

/-- **The generated id.** The 30-nibble stream laid out in the canonical
`8-4-4-4-12` UUID shape with hyphens, a version nibble `4`, and a variant nibble
`8`. -/
def genId (seed : Nat) : Bytes :=
  let ns := nibblesOf seed
  block ns 0 8 ++ [hy] ++ block ns 8 4 ++ [hy] ++ [verChar] ++ block ns 12 3
    ++ [hy] ++ [varChar] ++ block ns 15 3 ++ [hy] ++ block ns 18 12

/-- **Well-formed by construction — length.** The generated id is EXACTLY 36 bytes
for ANY seed (the canonical hyphenated UUID length). -/
theorem genId_length (seed : Nat) : (genId seed).length = 36 := by
  have hn : (nibblesOf seed).length = 30 := nibblesOf_length seed
  simp only [genId, block, List.length_append, List.length_cons, List.length_nil,
    List.length_take, List.length_drop, hn]
  omega

/-! ## Structural well-formedness (concrete, non-vacuous) -/

/-- Whether an id has the canonical UUID structure: length 36, hyphens at the four
group boundaries, and the version/variant nibbles in place. -/
def wellFormed (id : Bytes) : Bool :=
  id.length == 36
    && id[8]?  == some hy  && id[13]? == some hy
    && id[18]? == some hy  && id[23]? == some hy
    && id[14]? == some verChar && id[19]? == some varChar

/-- `genId 0` is structurally well-formed — kernel-checked. -/
theorem genId0_wellFormed : wellFormed (genId 0) = true := by decide

/-- `genId 255` is structurally well-formed — a second concrete witness. -/
theorem genId255_wellFormed : wellFormed (genId 255) = true := by decide

/-- The generator genuinely varies: two different seeds yield different ids. -/
theorem genId_distinct : genId 0 ≠ genId 1 := by decide

/-! ## The resolve decision -/

/-- **The resolve policy.** A *trusted* incoming id is preserved verbatim; otherwise a
fresh id is generated from the seed. Total. -/
def resolve (trust : Bool) (incoming : Option Bytes) (seed : Nat) : Bytes :=
  match trust, incoming with
  | true, some id => id
  | _,    _       => genId seed

/-- A trusted incoming id is preserved. -/
theorem resolve_trust_preserve (id : Bytes) (seed : Nat) :
    resolve true (some id) seed = id := rfl

/-- An untrusted incoming id is ignored — a fresh id is generated. -/
theorem resolve_untrusted_generate (id : Bytes) (seed : Nat) :
    resolve false (some id) seed = genId seed := rfl

/-- No incoming id ⇒ a fresh id is generated (either trust setting). -/
theorem resolve_absent_generate (trust : Bool) (seed : Nat) :
    resolve trust none seed = genId seed := by cases trust <;> rfl

/-! ## Reading the incoming id off the request -/

/-- The header name the id is carried under (`x-request-id`, lowercase for matching).
Explicit ASCII bytes so header-name matching reduces in the kernel. -/
def ridNameLower : Bytes := [120, 45, 114, 101, 113, 117, 101, 115, 116, 45, 105, 100]

/-- The header name stamped on responses (`X-Request-Id`, canonical casing). -/
def ridName : Bytes := [88, 45, 82, 101, 113, 117, 101, 115, 116, 45, 73, 100]

/-- Lower one ASCII byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- The incoming request id, if the request carries an `x-request-id` header. -/
def incomingOf (req : Request) : Option Bytes :=
  (req.headers.find? (fun nv => lower nv.1 == ridNameLower)).map Prod.snd

/-- Whether trusted incoming ids are honored (deploy policy: trust). -/
def trustIncoming : Bool := true

/-- The per-request generation seed (derived from the raw input length — deterministic
in the model; a real deployment seeds from an entropy source). -/
def seedOf (c : Ctx) : Nat := c.input.length

/-- **The resolved id for this request.** The real resolve policy on the request's
incoming id and the per-request seed. -/
def ctxId (c : Ctx) : Bytes := resolve trustIncoming (incomingOf c.req) (seedOf c)

/-! ## The stage -/

/-- The attribute key the resolved id is stashed under for upstream propagation. -/
def ridAttrKey : String := "request.id"

/-- **The request-id stage.** Request phase: resolve the id and stash it under
`ridAttrKey` (so an upstream proxy pass carries it), then `.continue` the enriched
context. Response phase: read the stashed id back and stamp it as `(ridName, id)` via
one affine `addHeader`. A passing stage — it never gates. -/
def ridStage : Stage where
  name := "request-id"
  onRequest := fun c =>
    .continue { c with attrs := (ridAttrKey, ctxId c) :: c.attrs }
  onResponse := fun c b =>
    match c.attrs.find? (fun p => p.1 == ridAttrKey) with
    | some p => b.addHeader (ridName, p.2)
    | none   => b.addHeader (ridName, ctxId c)

/-! ## Propagation — the request phase stashes the id -/

/-- The request phase stashes the resolved id into the context attributes, keyed by
`ridAttrKey`, for upstream propagation. -/
theorem ridStage_stashes (c : Ctx) :
    ridStage.onRequest c = .continue { c with attrs := (ridAttrKey, ctxId c) :: c.attrs } := rfl

/-! ## Propagation — the response phase stamps the id -/

/-- The enriched context after the request phase. -/
def enriched (c : Ctx) : Ctx := { c with attrs := (ridAttrKey, ctxId c) :: c.attrs }

/-- On the enriched context, the response phase finds the stashed id and adds it. -/
theorem ridStage_onResp_enriched (c : Ctx) (b : ResponseBuilder) :
    ridStage.onResponse (enriched c) b = b.addHeader (ridName, ctxId c) := by
  show (match ((ridAttrKey, ctxId c) :: c.attrs).find? (fun p => p.1 == ridAttrKey) with
        | some p => b.addHeader (ridName, p.2)
        | none   => b.addHeader (ridName, ctxId c)) = _
  simp [List.find?]

/-- The stage factors through `pipeline_stage_effect`: it passes to the enriched
context and its response phase adds the resolved id. -/
theorem ridStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (ridStage :: rest) h c
      = (runPipeline rest h (enriched c)).addHeader (ridName, ctxId c) := by
  rw [pipeline_stage_effect ridStage rest h c (enriched c) (ridStage_stashes c)]
  exact ridStage_onResp_enriched c _

/-- **Propagation byte-effect.** The resolved request id is present as `(ridName,
ctxId c)` in the FINALIZED response the serializer renders — for ANY tail and
handler. The id genuinely reaches the wire. -/
theorem ridStage_propagates (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (ridName, ctxId c) ∈ ((runPipeline (ridStage :: rest) h c).build).headers := by
  rw [ridStage_effect, build_addHeader]
  simp

/-! ## Concrete non-vacuous contexts -/

/-- A request with no incoming id — the generate path (seed `0`, since input is `[]`). -/
def genCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- A request carrying a trusted incoming id — the echo path. -/
def echoId : Bytes := "trace-abc-123".toUTF8.toList
def echoCtx : Ctx :=
  { input := [], req := { headers := [(ridName, echoId)] }, attrs := [] }

/-- On the generate path, the resolved id is a fresh, well-formed id (`genId 0`). -/
theorem genCtx_id : ctxId genCtx = genId 0 := rfl

/-- **The generated id that reaches the wire is well-formed.** On the generate path
the propagated header carries `genId 0`, which is structurally well-formed. -/
theorem ridStage_generates_wellformed (rest : List Stage) (h : Ctx → Response) :
    (ridName, genId 0) ∈ ((runPipeline (ridStage :: rest) h genCtx).build).headers
    ∧ wellFormed (genId 0) = true := by
  refine ⟨?_, genId0_wellFormed⟩
  have := ridStage_propagates rest h genCtx
  rwa [genCtx_id] at this

/-- On the echo path, the resolved id is the trusted incoming one (verbatim). -/
theorem echoCtx_id : ctxId echoCtx = echoId := rfl

/-- **The trusted incoming id is echoed to the wire.** On the echo path the propagated
header carries the exact incoming id — trusted preservation reaches the response. -/
theorem ridStage_echoes (rest : List Stage) (h : Ctx → Response) :
    (ridName, echoId) ∈ ((runPipeline (ridStage :: rest) h echoCtx).build).headers := by
  have := ridStage_propagates rest h echoCtx
  rwa [echoCtx_id] at this

/-! ## Axiom audit -/

#print axioms genId_length
#print axioms genId0_wellFormed
#print axioms genId_distinct
#print axioms resolve_trust_preserve
#print axioms resolve_absent_generate
#print axioms ridStage_propagates
#print axioms ridStage_generates_wellformed
#print axioms ridStage_echoes

end Reactor.Stage.RequestId
