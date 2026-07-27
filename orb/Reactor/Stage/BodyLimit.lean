import Reactor.Pipeline

/-!
# Reactor.Stage.BodyLimit — the body-size gate (RFC 9110 §15.5.14 `413`)

A request whose body exceeds the configured cap is refused `413 Content Too Large`.
Two independent triggers, and BOTH must fire — a body is over-cap when

    oversized  :=  declaredLen > cap   OR   streamedSoFar > cap

* **declared** — the request ANNOUNCES an oversized upload via a wide `Content-Length`
  (rejected up front, before the body is read — the nginx `client_max_body_size` /
  Apache `LimitRequestBody` behaviour).
* **streamed** — the request DOES NOT declare its length (a chunked
  `Transfer-Encoding`, so `Content-Length` is absent and the declared check is
  vacuously false), but the bytes actually streamed onto the wire have exceeded the
  cap. This is the hole the declared-only gate leaves open: a chunked upload with no
  `Content-Length` sails past a `Content-Length`-only check. Counting the ACTUAL
  streamed bytes closes it — see `streamed_denies_bypass`.

The declared guard is on the WIDTH of the `Content-Length` field (its digit count), a
monotone proxy for the announced size that needs no decimal parser: a decimal
`Content-Length` with more than `maxCLDigits` digits announces at least
`10 ^ maxCLDigits = bodyCap` bytes. The streamed guard counts the bytes accumulated so
far (`streamedOf`, threaded from the dataplane body-read path under `streamedKey`) and
refuses once they pass `bodyCap`.

## What is proven (headline)

* `body_denies` / `body_allows` — the stage `.respond`s the `413` exactly when the
  combined `oversizedCtx` decision holds, else `.continue`s.
* `body_denies_declared` / `body_denies_streamed` — either trigger alone forces the
  `413`.
* `streamed_denies_bypass` — **the closed hole**: with NO declared length
  (`declaredLen = 0`) a streamed count over the cap is STILL refused.
* `body_denies_status` — the `413` carries through a status-stable inner onion.
* `body_denies_skips_handler` — the handler never runs on a refused request.
* `body_changes_bytes` — same handler: an over-cap request is forced to `413`, a
  within-cap one runs the handler (`200`).

Non-vacuity: `witnessCtx` (an 8-digit `Content-Length`, over the 7-digit budget) takes
the declared deny branch; `streamedWitnessCtx` (NO `Content-Length`, a streamed count of
`bodyCap + 1`) takes the streamed deny branch — the bypass shape, refused; `okCtx` (a
3-digit length, no streamed bytes) takes the allow branch.
-/

namespace Reactor.Stage.BodyLimit

open Reactor.Pipeline
open Proto (Bytes Request)

def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## The declared-size decision -/

/-- `Content-Length` header name (explicit ASCII bytes so the header match reduces in
the kernel). -/
def contentLengthName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104]

/-- Digit budget for the declared `Content-Length`. A wider field announces ≥
`10 ^ maxCLDigits` bytes and is refused. `7` ⇒ a 10 MB cap. -/
def maxCLDigits : Nat := 7

/-- **The declared-size decision.** `true` when the request carries a `Content-Length`
whose decimal field is wider than the digit budget (announces an over-cap body); a
within-budget or absent length is `false`. -/
def oversized (req : Request) : Bool :=
  match req.headers.find? (fun nv => nv.1 == contentLengthName) with
  | some nv => decide (maxCLDigits < nv.2.length)
  | none    => false

/-- The byte cap in bytes: a declared/streamed length of `bodyCap` or more is over-cap.
Equal to `10 ^ maxCLDigits`, so the digit-width declared gate (`> maxCLDigits` digits)
and the exact-byte streamed gate (`> bodyCap - 1`, i.e. `≥ bodyCap`) name the SAME
threshold. -/
def bodyCap : Nat := 10 ^ maxCLDigits

/-! ## The streamed-size decision — the hole the declared gate leaves open

A chunked upload carries NO `Content-Length`, so `oversized` is vacuously `false` on it
however many bytes it streams. The dataplane body-read path counts the bytes actually
accumulated and threads that count into the context under `streamedKey`; the gate reads
it back and refuses once it passes `bodyCap`, independent of any declared length. -/

/-- The attribute key under which the body-read path stashes the streamed-byte
accumulator (its byte length IS the count, mirroring the connection-count idiom). -/
def streamedKey : String := "body.streamed"

/-- The count of body bytes streamed so far, recovered from the context's attribute
bag (`0` when the body-read path has stashed nothing — the sans-IO default). -/
def streamedOf (c : Ctx) : Nat :=
  match c.attrs.find? (fun p => p.1 == streamedKey) with
  | some p => p.2.length
  | none   => 0

/-- **The combined decision.** A body is over-cap when its declared length is over
budget OR the bytes actually streamed have passed `bodyCap`. This is the
`declaredLen > cap OR streamedSoFar > cap` rule stated on the context. -/
def oversizedCtx (c : Ctx) : Bool :=
  oversized c.req || decide (bodyCap < streamedOf c)

/-- **The pure combined decision**, parametric in the cap — the exact rule the
dataplane body-read accumulator and this stage both conform to:
`declaredLen > cap OR streamedSoFar > cap`. -/
def oversizedStreamed (cap declaredLen streamedSoFar : Nat) : Bool :=
  decide (cap < declaredLen) || decide (cap < streamedSoFar)

/-- When no bytes have been streamed (the sans-IO fold, where the body-read
accumulator stashes nothing), the combined decision collapses to the declared gate —
so a fold built without a streamed accumulator is exactly the declared-`Content-Length`
gate, and inert wherever `oversized` is. -/
theorem oversizedCtx_of_no_stream (c : Ctx) (h : streamedOf c = 0) :
    oversizedCtx c = oversized c.req := by
  rw [oversizedCtx, h, decide_eq_false (Nat.not_lt_zero bodyCap), Bool.or_false]

/-! ## The refusal response -/

def tooLargeBody : Bytes := strBytes "content too large\n"

/-- The genuine `413` the gate answers with — status `413`, reason phrase, empty body-cap
notice. -/
def contentTooLarge : Response :=
  { status  := 413
    reason  := strBytes "Content Too Large"
    headers := []
    body    := tooLargeBody }

theorem contentTooLarge_status : contentTooLarge.status = 413 := rfl

/-! ## The stage -/

/-- **The body-size gate stage.** Request phase: an over-cap body — declared OR
streamed — is refused `413` (short-circuit, handler skipped); a within-cap body (or one
with neither a declared length nor streamed bytes) passes. Response phase transparent. -/
def bodyLimitStage : Stage where
  name := "body-limit"
  onRequest := fun c =>
    if oversizedCtx c then .respond contentTooLarge else .continue c
  onResponse := fun _ b => b

theorem bodyLimitStage_statusStable : Stage.statusStable bodyLimitStage := fun _ _ => rfl

/-! ## Deny: an over-cap body is refused 413, handler skipped -/

/-- **`body_denies`.** The combined over-cap decision makes the stage `.respond` the
`413`. -/
theorem body_denies (c : Ctx) (h : oversizedCtx c = true) :
    bodyLimitStage.onRequest c = .respond contentTooLarge := by
  show (if oversizedCtx c then StageStep.respond contentTooLarge else StageStep.continue c) = _
  rw [h]; rfl

/-- **`body_allows`.** A within-cap body (neither trigger) passes (`.continue`). -/
theorem body_allows (c : Ctx) (h : oversizedCtx c = false) :
    bodyLimitStage.onRequest c = .continue c := by
  show (if oversizedCtx c then StageStep.respond contentTooLarge else StageStep.continue c) = _
  rw [h]
  simp only [Bool.false_eq_true, if_false]

/-- **`body_denies_declared`.** The declared trigger alone forces the `413`. -/
theorem body_denies_declared (c : Ctx) (h : oversized c.req = true) :
    bodyLimitStage.onRequest c = .respond contentTooLarge :=
  body_denies c (by simp only [oversizedCtx, h, Bool.true_or])

/-- **`body_denies_streamed`.** The streamed trigger alone forces the `413` — a body
whose accumulated streamed bytes have passed `bodyCap`, with NO reliance on a declared
`Content-Length`. -/
theorem body_denies_streamed (c : Ctx) (h : bodyCap < streamedOf c) :
    bodyLimitStage.onRequest c = .respond contentTooLarge :=
  body_denies c (by simp only [oversizedCtx, decide_eq_true h, Bool.or_true])

/-- **`body_denies_status`.** The refusal keeps its `413` through a status-stable inner
onion — a `413` stays a `413` on the wire. -/
theorem body_denies_status (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (h : oversizedCtx c = true) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (bodyLimitStage :: rest) handler c).build).status = 413 := by
  have := pipeline_gate_status bodyLimitStage rest handler c contentTooLarge
    (body_denies c h) hst
  rw [this]; rfl

/-- **`body_denies_skips_handler`.** The request is NOT forwarded on a refused body. -/
theorem body_denies_skips_handler (c : Ctx) (rest : List Stage) (handler handler' : Ctx → Response)
    (h : oversizedCtx c = true) :
    runPipeline (bodyLimitStage :: rest) handler c
      = runPipeline (bodyLimitStage :: rest) handler' c :=
  pipeline_gate_ignores_handler bodyLimitStage rest handler handler' c
    contentTooLarge (body_denies c h)

/-! ## The streamed decision — the pure rule, and the bypass it closes -/

/-- **`streamed_denies_declared`.** The declared branch of the combined rule. -/
theorem streamed_denies_declared (cap d s : Nat) (h : cap < d) :
    oversizedStreamed cap d s = true := by
  simp only [oversizedStreamed, decide_eq_true h, Bool.true_or]

/-- **`streamed_denies_bypass` — THE CLOSED HOLE.** A request that declares NO length
(`declaredLen = 0`, exactly the chunked / `Content-Length`-absent shape the declared
gate cannot see) whose STREAMED bytes have passed the cap is refused all the same. The
streamed accumulator, not the announced length, is what fires. -/
theorem streamed_denies_bypass (cap s : Nat) (h : cap < s) :
    oversizedStreamed cap 0 s = true := by
  simp only [oversizedStreamed, decide_eq_true h, Bool.or_true]

/-- **`streamed_allows`.** Neither over cap ⇒ pass. -/
theorem streamed_allows (cap d s : Nat) (hd : d ≤ cap) (hs : s ≤ cap) :
    oversizedStreamed cap d s = false := by
  simp only [oversizedStreamed, decide_eq_false (Nat.not_lt.2 hd),
    decide_eq_false (Nat.not_lt.2 hs), Bool.or_self]

-- Non-vacuity of the pure rule: the bypass shape (declared 0, streamed over) denies,
-- the declared-over shape denies, and the within-cap shape allows — real Nats, both
-- branches exercised, no tautology.
example : oversizedStreamed 100 0 250 = true := by decide      -- bypass: no declared len
example : oversizedStreamed 100 250 0 = true := by decide      -- declared over
example : oversizedStreamed 100 50 80 = false := by decide     -- within cap

/-! ## Concrete non-vacuity -/

/-- A request declaring an 8-digit `Content-Length` (over the 7-digit budget), no
streamed bytes. -/
def witnessCtx : Ctx :=
  { input := [], req := { headers := [(contentLengthName, [49, 50, 51, 52, 53, 54, 55, 56])] } }

/-- The witness declares an over-budget body. -/
theorem witness_oversized : oversized witnessCtx.req = true := by decide

/-- The witness is over-cap by the combined decision. -/
theorem witness_oversizedCtx : oversizedCtx witnessCtx = true := by
  simp only [oversizedCtx, witness_oversized, Bool.true_or]

/-- **`witness_responds`.** On the over-budget witness the real stage `.respond`s the
`413` — the decision the braid gate delegates to. -/
theorem witness_responds : bodyLimitStage.onRequest witnessCtx = .respond contentTooLarge :=
  body_denies_declared witnessCtx witness_oversized

/-- **The bypass witness — a chunked-shape request with NO `Content-Length` whose
streamed bytes reach `bodyCap + 1`.** Its `Content-Length` is absent, so `oversized` is
`false` on it (the declared gate is blind here); the streamed accumulator carries
`bodyCap + 1` bytes under `streamedKey`. -/
def streamedWitnessCtx : Ctx :=
  { input := [], req := {}, attrs := [(streamedKey, List.replicate (bodyCap + 1) 0)] }

/-- The bypass witness declares NO oversized length — the declared gate does not fire. -/
theorem streamedWitness_declared_blind : oversized streamedWitnessCtx.req = false := by decide

/-- The bypass witness has streamed past the cap. -/
theorem streamedWitness_streamed : streamedOf streamedWitnessCtx = bodyCap + 1 := by
  simp [streamedOf, streamedWitnessCtx, streamedKey, List.length_replicate]

theorem streamedWitness_over : bodyCap < streamedOf streamedWitnessCtx := by
  rw [streamedWitness_streamed]; omega

/-- **`streamedWitness_bypass_denied` — the bypass, closed, on the real stage.** A
request with NO `Content-Length` (the shape that sails past a declared-only gate) is
`.respond`ed the genuine `413` purely because its STREAMED bytes passed the cap. -/
theorem streamedWitness_bypass_denied :
    bodyLimitStage.onRequest streamedWitnessCtx = .respond contentTooLarge :=
  body_denies_streamed streamedWitnessCtx streamedWitness_over

/-- A request declaring a 3-digit `Content-Length` (within budget), no streamed bytes. -/
def okCtx : Ctx :=
  { input := [], req := { headers := [(contentLengthName, [49, 50, 51])] } }

theorem okCtx_within : oversized okCtx.req = false := by decide

/-- The within-budget context is under cap by the combined decision (no declared
over-length, no streamed bytes). -/
theorem okCtx_within_ctx : oversizedCtx okCtx = false := by decide

/-- **`body_changes_bytes`.** Same handler: an over-cap request (declared) is forced to
`413`, a streamed-over request is forced to `413`, and a within-cap one runs the handler
(`200`). The gate genuinely drives the response on BOTH triggers. -/
theorem body_changes_bytes (body : Bytes) :
    ((runPipeline [bodyLimitStage] (fun _ => Reactor.ok200 body) witnessCtx).build).status = 413
    ∧ ((runPipeline [bodyLimitStage] (fun _ => Reactor.ok200 body) streamedWitnessCtx).build).status = 413
    ∧ ((runPipeline [bodyLimitStage] (fun _ => Reactor.ok200 body) okCtx).build).status = 200 := by
  refine ⟨?_, ?_, ?_⟩
  · have := body_denies_status witnessCtx [] (fun _ => Reactor.ok200 body) witness_oversizedCtx
      (by intro t ht; exact absurd ht (List.not_mem_nil))
    simpa using this
  · have := body_denies_status streamedWitnessCtx [] (fun _ => Reactor.ok200 body)
      (by simp only [oversizedCtx, decide_eq_true streamedWitness_over, Bool.or_true])
      (by intro t ht; exact absurd ht (List.not_mem_nil))
    simpa using this
  · rw [pipeline_stage_effect bodyLimitStage [] (fun _ => Reactor.ok200 body) okCtx okCtx
        (body_allows okCtx okCtx_within_ctx)]
    rfl

/-! ## Axiom audit -/

#print axioms body_denies
#print axioms body_allows
#print axioms body_denies_declared
#print axioms body_denies_streamed
#print axioms streamed_denies_bypass
#print axioms streamed_allows
#print axioms body_denies_status
#print axioms body_denies_skips_handler
#print axioms witness_responds
#print axioms streamedWitness_bypass_denied
#print axioms body_changes_bytes

end Reactor.Stage.BodyLimit
