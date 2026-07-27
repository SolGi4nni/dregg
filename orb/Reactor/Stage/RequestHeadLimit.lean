import Reactor.Stage.FramingValidation

/-!
# Reactor.Stage.RequestHeadLimit — the request-head length gate (Z1 DoS)

The wave-5 EXTENDED probe (`docs/engine/review/CONFORMANCE-EXT.md`, finding **Z1** —
the TOP finding of the whole conformance effort) showed a single unauthenticated
request whose **head** (request-line + header block) is ≳ 30 KiB aborts the entire
`dataplane` process with a stack overflow:

```
thread 'drorb-serve' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

Root class: a non-tail-recursive fold over the request head grows one stack frame
per input unit until the ~8 MiB thread stack is exhausted. Any shape of oversized
head triggers it — a long URI, one large header value, or ~900 small headers — and
they all inflate the same quantity: the **total head byte length**. A 28 KiB head
survives (`200`); 32 KiB crashes. Body size is safe.

**The fix (RFC 7230 §3.1.1 / §3.2.5, RFC 6585 §5).** Bound the head BEFORE the
recursive parse, and answer the RFC's status for the shape that broke the bound.
This file provides:

* `headGate` — **the definitive pre-parse gate**: reads the head GEOMETRY of the
  raw `ByteArray` with a fixed number of index probes (no scan at all on a
  message ≤ `maxHeadBytes`) and refuses `414 URI Too Long` when the
  request-LINE is over `maxRequestLine` (the RFC 7230 §3.1.1 MUST) or
  `431 Request Header Fields Too Large` when the header block is over
  `maxHeadBytes`, BEFORE `Proto.RequestSerialize.parse` is ever called. A large
  BODY behind a small head passes: the gate never confuses message size with
  head size.
* `headPrefix` — the head-only slice of the input, ≤ `maxHeadBytes + 4` bytes
  for EVERY input (`headPrefix_size_le`): what the wrapper feeds the request-head
  parser, so the parser's structural recursion is bounded by a CONSTANT by
  construction (a gate that runs AFTER the parse cannot un-overflow it).
* `headBytesTooLarge` — the older whole-message decision (`limit < size`), kept
  for the in-pipeline BACKSTOP `headLimitStage` (defense in depth) and as the
  compatibility reference: everything it admitted, `headGate` admits
  (`headGate_none_of_within`), so previously-served traffic is byte-identical.
* `requestHeaderFieldsTooLargeResp` / `uriTooLongResp` — the `431` and `414`.

## What is proven (non-vacuous on concrete witnesses)

* `scanFor_some` / `scanFor_none` — the constant-fuel index scans find exactly
  the in-window matches.
* `headGate_none_bound` — a gate-passed head ENDS within `maxHeadBytes`.
* `headPrefix_size_le` — the parser's input is ≤ `maxHeadBytes + 4`, always.
* `headGate_small` / `headGate_none_of_within` — pass-through compatibility.
* `headGate_statuses` — the only refusals are the `414` and the `431`.
* `headLimitStage_rejects` / `headLimitStage_passes` — the pipeline backstop.
* Executable witnesses: the 20 KB / 100 KB request-targets ⇒ `414`; a ~28 KB
  header block ⇒ `431`; a 20 KB BODY behind a 57-byte head ⇒ pass; an
  8000-octet request-line (the RFC SHOULD) ⇒ pass.
-/

namespace Reactor.Stage.RequestHeadLimit

open Reactor.Pipeline
open Proto (Bytes Request)
open Reactor.Stage.RequestValidation (strBytes)

/-- The maximum accepted request-head byte length. 16 KiB: comfortably above any
legitimate request-line + header block, comfortably below the 28–32 KiB stack-crash
band the Z1 bisection found. -/
def maxHeadBytes : Nat := 16384

/-- **The decision.** A head of `size` bytes is too large when it exceeds the limit.
Applied at the byte boundary to `input.size` (the definitive Z1 gate, pre-parse) and,
as a backstop, to `c.input.length` inside the pipeline — the SAME function both. -/
def headBytesTooLarge (size : Nat) : Bool := decide (maxHeadBytes < size)

/-- `431 Request Header Fields Too Large` — the oversized-head refusal (Z1). -/
def requestHeaderFieldsTooLargeResp : Response :=
  { status := 431, reason := strBytes "Request Header Fields Too Large", headers := []
    body := strBytes "request header fields too large\n" }

theorem requestHeaderFieldsTooLargeResp_status :
    requestHeaderFieldsTooLargeResp.status = 431 := rfl

/-! ## The stage (in-pipeline backstop over `c.input.length`) -/

/-- **The head-length gate.** Request phase: if the raw head is over `maxHeadBytes`,
short-circuit with the `431`; otherwise pass unchanged. Response phase transparent.
The DEFINITIVE gate is this same decision on `input.size` before parse (see the wire
fragment); this in-pipeline form is a backstop. -/
def headLimitStage : Stage where
  name := "request-head-limit"
  onRequest := fun c =>
    if headBytesTooLarge c.input.length then .respond requestHeaderFieldsTooLargeResp
    else .continue c
  onResponse := fun _ b => b

theorem headLimitStage_statusStable : Stage.statusStable headLimitStage := fun _ _ => rfl

/-- **Reject.** An oversized head ⇒ the gate answers `431`. -/
theorem headLimitStage_rejects (c : Ctx) (h : headBytesTooLarge c.input.length = true) :
    headLimitStage.onRequest c = .respond requestHeaderFieldsTooLargeResp := by
  show (if headBytesTooLarge c.input.length then _ else _) = _
  rw [h]; simp only [if_true]

/-- **Pass.** A within-limit head ⇒ `.continue` unchanged. -/
theorem headLimitStage_passes (c : Ctx) (h : headBytesTooLarge c.input.length = false) :
    headLimitStage.onRequest c = .continue c := by
  show (if headBytesTooLarge c.input.length then _ else StageStep.continue c) = _
  rw [h]; simp only [Bool.false_eq_true, if_false]

/-- The `431` survives a status-stable inner onion (gate composition). -/
theorem headLimitStage_status (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (h : headBytesTooLarge c.input.length = true)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (headLimitStage :: rest) handler c).build).status = 431 := by
  have := pipeline_gate_status headLimitStage rest handler c requestHeaderFieldsTooLargeResp
    (headLimitStage_rejects c h) hst
  rw [this]; rfl

/-- A rejected (oversized) request never reaches the handler. -/
theorem headLimitStage_skips_handler (c : Ctx) (rest : List Stage)
    (handler handler' : Ctx → Response) (h : headBytesTooLarge c.input.length = true) :
    runPipeline (headLimitStage :: rest) handler c
      = runPipeline (headLimitStage :: rest) handler' c :=
  pipeline_gate_ignores_handler headLimitStage rest handler handler' c
    requestHeaderFieldsTooLargeResp (headLimitStage_rejects c h)

/-! ## Concrete non-vacuity witnesses -/

/-- A request whose raw head is 40000 bytes (over the 16 KiB limit — a Z1-class
oversized head; `List.replicate` of a filler byte stands in for the real bytes). -/
def bigCtx : Ctx :=
  { input := List.replicate 40000 65, req := { } }

/-- A small, normal request head (100 bytes). -/
def smallCtx : Ctx :=
  { input := List.replicate 100 65, req := { } }

theorem bigCtx_too_large : headBytesTooLarge bigCtx.input.length = true := by
  simp only [bigCtx, List.length_replicate]; decide
theorem smallCtx_ok : headBytesTooLarge smallCtx.input.length = false := by
  simp only [smallCtx, List.length_replicate]; decide

/-- **Z1.** The oversized head ⇒ the gate answers `431`. -/
theorem bigCtx_rejected :
    headLimitStage.onRequest bigCtx = .respond requestHeaderFieldsTooLargeResp :=
  headLimitStage_rejects bigCtx bigCtx_too_large

/-- The small head passes through unchanged. -/
theorem smallCtx_passes : headLimitStage.onRequest smallCtx = .continue smallCtx :=
  headLimitStage_passes smallCtx smallCtx_ok

/-- **Non-vacuity contrast.** The gate rejects the oversized head with `431` but
passes the small one — it genuinely discriminates on size. -/
theorem gate_discriminates :
    (headLimitStage.onRequest bigCtx = .respond requestHeaderFieldsTooLargeResp)
    ∧ (headLimitStage.onRequest smallCtx = .continue smallCtx) :=
  ⟨bigCtx_rejected, smallCtx_passes⟩

/-! ### Executable sanity checks -/

def decideStatus : StageStep → Nat
  | .respond r => r.status
  | .continue _ => 200

#guard decideStatus (headLimitStage.onRequest bigCtx) == 431
#guard decideStatus (headLimitStage.onRequest smallCtx) == 200
#guard headBytesTooLarge 40000 == true
#guard headBytesTooLarge 100 == false
#guard headBytesTooLarge 16384 == false
#guard headBytesTooLarge 16385 == true

/-! ## The pre-parse HEAD gate — `414`/`431` by bounded index probes

The `input.size` byte gate above refuses on the TOTAL message length: head plus
body. That conflates two different quantities. The stack hazard is driven by the
HEAD length alone (the Z1 bisection: body size is safe), and RFC 7230 §3.1.1
separately demands `414 URI Too Long` — not `431` — when it is the request-LINE
that is over-long. Gating on `input.size`:

* refuses a legitimate request whose BODY pushes the message over 16 KiB with a
  bogus `431 Request Header Fields Too Large` (a body-cliff: no header was large);
* answers `431` where the RFC says `414` MUST be the answer for an over-long
  request-target.

`headGate` below reads the head GEOMETRY instead, with a fixed number of index
probes — `O(1)` on every message up to `maxHeadBytes` (one size test, no scan),
and at most `maxRequestLine + maxHeadBytes + 1` probes on a larger one — all
BEFORE any recursive parse:

* no `CRLF` within the first `maxRequestLine` bytes ⇒ the request-line (hence
  the request-target) is longer than the server parses ⇒ `414` (the RFC 7230
  §3.1.1 MUST; `maxRequestLine` = 8192 honors the SHOULD of ≥ 8000 octets);
* otherwise no `CRLFCRLF` within the first `maxHeadBytes + 1` positions ⇒ the
  header block is over the head bound ⇒ `431` (RFC 6585 §5);
* otherwise pass: `headGate_none_bound` proves the head then ENDS within
  `maxHeadBytes` — the constant that bounds every head-walking recursion — while
  the body behind it may be arbitrarily large.

The scanners are CONSTANT-fuel tail loops (`scanFor`): their recursion depth is
the fuel constant, never the input length, so the gate itself cannot be the
overflow it guards against. -/

/-- RFC 7230 §3.1.1: a server SHOULD support a request-line of at least 8000
octets, and MUST answer `414` when the request-target is longer than any URI it
is willing to parse. The accepted request-line bound: 8192. -/
def maxRequestLine : Nat := 8192

/-- `414 URI Too Long` — the over-long request-line refusal (RFC 7230 §3.1.1). -/
def uriTooLongResp : Response :=
  { status := 414, reason := strBytes "URI Too Long", headers := []
    body := strBytes "uri too long\n" }

theorem uriTooLongResp_status : uriTooLongResp.status = 414 := rfl

/-- Clamped byte load: byte `i`, `0` past the end — the index probe the gate
scans are built from (the deployed scanners' `List.getD … 0`, index-native). -/
def byteAt (input : ByteArray) (i : Nat) : UInt8 :=
  if h : i < input.size then input[i] else 0

/-- `CRLF` starting at `i` (two probes; `false` past the end since `0 ≠ CR`). -/
def crlfAt (input : ByteArray) (i : Nat) : Bool :=
  byteAt input i == 13 && byteAt input (i + 1) == 10

/-- `CRLFCRLF` — the head terminator — starting at `i`. -/
def crlf2At (input : ByteArray) (i : Nat) : Bool :=
  crlfAt input i && crlfAt input (i + 2)

/-- First index `j ∈ [i, i + fuel)` with `p j = true`. A TAIL-recursive cursor
loop structurally recursive on `fuel`; the gate instantiates `fuel` with a fixed
constant, so the scan's stack depth is bounded by that constant for EVERY input
— by construction, not by an argument about the input's shape. -/
def scanFor (p : Nat → Bool) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 => if p i then some i else scanFor p (i + 1) fuel

/-- `scanFor` finds only genuine, in-window matches. -/
theorem scanFor_some (p : Nat → Bool) :
    ∀ fuel i k, scanFor p i fuel = some k → p k = true ∧ i ≤ k ∧ k < i + fuel := by
  intro fuel
  induction fuel with
  | zero => intro i k h; exact absurd h (by simp [scanFor])
  | succ f ih =>
    intro i k h
    rw [scanFor] at h
    by_cases hp : p i = true
    · rw [if_pos hp] at h
      cases h
      exact ⟨hp, Nat.le_refl i, by omega⟩
    · rw [if_neg hp] at h
      obtain ⟨h1, h2, h3⟩ := ih (i + 1) k h
      exact ⟨h1, by omega, by omega⟩

/-- `scanFor` misses nothing in its window: `none` ⇒ no index in `[i, i + fuel)`
satisfies `p`. -/
theorem scanFor_none (p : Nat → Bool) :
    ∀ fuel i, scanFor p i fuel = none →
      ∀ j, i ≤ j → j < i + fuel → p j = false := by
  intro fuel
  induction fuel with
  | zero => intro i _ j h1 h2; omega
  | succ f ih =>
    intro i h j h1 h2
    rw [scanFor] at h
    by_cases hp : p i = true
    · rw [if_pos hp] at h; exact absurd h (by simp)
    · rw [if_neg hp] at h
      by_cases hj : j = i
      · subst hj; exact Bool.eq_false_iff.mpr hp
      · exact ih (i + 1) h j (by omega) (by omega)

/-- **The pre-parse request-head gate.** `none` = proceed to the parse;
`some r` = answer `r` (`414` or `431`) without parsing. See the section
comment for the three cases. -/
def headGate (input : ByteArray) : Option Response :=
  if input.size ≤ maxHeadBytes then none
  else if (scanFor (crlfAt input) 0 maxRequestLine).isNone then
    some uriTooLongResp
  else if (scanFor (crlf2At input) 0 (maxHeadBytes + 1)).isNone then
    some requestHeaderFieldsTooLargeResp
  else none

/-- A message within the head bound is never refused — `O(1)`, no scan. -/
theorem headGate_small (input : ByteArray) (h : input.size ≤ maxHeadBytes) :
    headGate input = none := by
  unfold headGate; rw [if_pos h]

/-- Old-gate compatibility: every input the `input.size` byte gate ADMITTED, the
head gate admits — so on that whole class the wrapped serve is byte-identical to
what it was. (The gates differ only on `> maxHeadBytes` messages: the old gate
refused them all with `431`; the head gate refuses only oversized HEADS, and
distinguishes `414`.) -/
theorem headGate_none_of_within (input : ByteArray)
    (h : headBytesTooLarge input.size = false) : headGate input = none := by
  apply headGate_small
  have := of_decide_eq_false h
  omega

/-- The gate's only refusals are the `414` and the `431`. -/
theorem headGate_statuses (input : ByteArray) (r : Response)
    (h : headGate input = some r) : r.status = 414 ∨ r.status = 431 := by
  unfold headGate at h
  by_cases h1 : input.size ≤ maxHeadBytes
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : (scanFor (crlfAt input) 0 maxRequestLine).isNone = true
    · rw [if_pos h2] at h; cases h; exact Or.inl rfl
    · rw [if_neg h2] at h
      by_cases h3 : (scanFor (crlf2At input) 0 (maxHeadBytes + 1)).isNone = true
      · rw [if_pos h3] at h; cases h; exact Or.inr rfl
      · rw [if_neg h3] at h; exact absurd h (by simp)

/-- **The head bound.** When the gate passes, the head ENDS within the constant:
either the whole message is ≤ `maxHeadBytes`, or a `CRLFCRLF` sits at some
`k ≤ maxHeadBytes`. This is the fact that bounds every head-walking recursion
behind the gate (`ServeConformant.headGate_none_parse_bound` carries it to the
deployed framing scan). -/
theorem headGate_none_bound (input : ByteArray) (h : headGate input = none) :
    input.size ≤ maxHeadBytes ∨ ∃ k, k ≤ maxHeadBytes ∧ crlf2At input k = true := by
  unfold headGate at h
  by_cases h1 : input.size ≤ maxHeadBytes
  · exact Or.inl h1
  · rw [if_neg h1] at h
    by_cases h2 : (scanFor (crlfAt input) 0 maxRequestLine).isNone = true
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · rw [if_neg h2] at h
      by_cases h3 : (scanFor (crlf2At input) 0 (maxHeadBytes + 1)).isNone = true
      · rw [if_pos h3] at h; exact absurd h (by simp)
      · rcases hk : scanFor (crlf2At input) 0 (maxHeadBytes + 1) with _ | k
        · rw [hk] at h3; exact absurd rfl h3
        · obtain ⟨hp, _, hlt⟩ := scanFor_some (crlf2At input) _ 0 k hk
          exact Or.inr ⟨k, by omega, hp⟩

/-! ## The head prefix — everything a request-head parse may read -/

/-- The HEAD PREFIX of the input: the whole input when it is small; otherwise
the bytes through the first `CRLFCRLF` (inclusive). An input the gate refuses is
cut at the bound (defensive — the wrapper answers the gate's `414`/`431` and
never parses it), so the prefix is ≤ `maxHeadBytes + 4` for EVERY input
(`headPrefix_size_le`): feeding the request-head parser `headPrefix input`
instead of `input` bounds its structural recursion by a CONSTANT, by
construction. The body — however large — is never in the parser's input. -/
def headPrefix (input : ByteArray) : ByteArray :=
  if input.size ≤ maxHeadBytes then input
  else
    match scanFor (crlf2At input) 0 (maxHeadBytes + 1) with
    | some k => ByteArray.mk (input.data.extract 0 (k + 4))
    | none => ByteArray.mk (input.data.extract 0 (maxHeadBytes + 4))

/-- On every message within the head bound the prefix IS the input — the parse
sees byte-identical bytes (all previously-admitted traffic is unchanged). -/
theorem headPrefix_small (input : ByteArray) (h : input.size ≤ maxHeadBytes) :
    headPrefix input = input := by
  unfold headPrefix; rw [if_pos h]

/-- **The parse-input bound, unconditional.** For EVERY input — gated or not —
the head prefix is at most `maxHeadBytes + 4` bytes. Every scan the request-head
parser runs is structural recursion on (a suffix of) this list, so its recursion
depth is bounded by this constant regardless of what arrives on the wire. -/
theorem headPrefix_size_le (input : ByteArray) :
    (headPrefix input).size ≤ maxHeadBytes + 4 := by
  unfold headPrefix
  by_cases h1 : input.size ≤ maxHeadBytes
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    rcases hk : scanFor (crlf2At input) 0 (maxHeadBytes + 1) with _ | k
    · show (ByteArray.mk (input.data.extract 0 (maxHeadBytes + 4))).size ≤ maxHeadBytes + 4
      show (input.data.extract 0 (maxHeadBytes + 4)).size ≤ maxHeadBytes + 4
      rw [Array.size_extract]
      omega
    · obtain ⟨_, _, hlt⟩ := scanFor_some (crlf2At input) _ 0 k hk
      show (input.data.extract 0 (k + 4)).size ≤ maxHeadBytes + 4
      rw [Array.size_extract]
      omega

/-! ### Executable witnesses — the gate discriminates the three refusal shapes

Real wire bytes (evaluator-checked): the 20 KB and 100 KB request-targets that
crashed the serve are `414`s; an oversized header BLOCK (short request-line) is
a `431`; a large BODY behind a small head — refused `431` by the `input.size`
gate — passes; a normal request and an 8000-octet request-line (the RFC SHOULD)
pass. -/

private def gateStatus (input : ByteArray) : Nat :=
  match headGate input with
  | some r => r.status
  | none => 0

private def longTargetInput (n : Nat) : ByteArray :=
  ("GET /" ++ String.mk (List.replicate n 'a') ++ " HTTP/1.1\r\nHost: x\r\n\r\n").toUTF8

private def bigHeaderInput : ByteArray :=
  ("GET / HTTP/1.1\r\nHost: x\r\n"
    ++ String.join (List.replicate 900 "x-filler: aaaaaaaaaaaaaaaaaaaa\r\n")
    ++ "\r\n").toUTF8

private def bigBodyInput : ByteArray :=
  ("POST /health HTTP/1.1\r\nHost: x\r\nContent-Length: 20000\r\n\r\n"
    ++ String.mk (List.replicate 20000 'x')).toUTF8

private def line8000BigBody : ByteArray :=
  ("GET /" ++ String.mk (List.replicate 7994 'a')
    ++ " HTTP/1.1\r\nHost: x\r\nContent-Length: 20000\r\n\r\n"
    ++ String.mk (List.replicate 20000 'x')).toUTF8

#guard gateStatus (longTargetInput 20000) == 414   -- crash #1's request, by hand
#guard gateStatus (longTargetInput 100000) == 414
#guard gateStatus bigHeaderInput == 431            -- ~28 KB of headers, short line
#guard gateStatus bigBodyInput == 0                -- the body-cliff: 20 KB body passes
#guard gateStatus ("GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8) == 0
#guard gateStatus line8000BigBody == 0             -- RFC SHOULD: 8000-octet line passes
#guard (headPrefix (longTargetInput 100000)).size ≤ maxHeadBytes + 4
#guard (headPrefix bigBodyInput).size ≤ maxHeadBytes + 4
-- the prefix cut keeps the whole head: it still ends in CRLFCRLF
#guard ((headPrefix bigBodyInput).size == 57
        && crlf2At (headPrefix bigBodyInput) 53) == true

/-! ## Axiom audit -/

#print axioms headLimitStage_rejects
#print axioms headLimitStage_passes
#print axioms headLimitStage_status
#print axioms headLimitStage_skips_handler
#print axioms bigCtx_rejected
#print axioms smallCtx_passes
#print axioms gate_discriminates

/-! ### Axiom audit — the pre-parse head gate -/

#print axioms scanFor_some
#print axioms scanFor_none
#print axioms headGate_small
#print axioms headGate_none_of_within
#print axioms headGate_statuses
#print axioms headGate_none_bound
#print axioms headPrefix_small
#print axioms headPrefix_size_le

end Reactor.Stage.RequestHeadLimit
