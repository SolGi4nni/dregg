import Ws.CloseHandshake

/-!
# Incremental UTF-8 validation (RFC 3629) — the streaming automaton

`Ws.CloseHandshake.validUtf8Aux` fixes what "this byte string is UTF-8"
*means* — the RFC 3629 leading/continuation grammar with the overlong,
surrogate, and beyond-`U+10FFFF` exclusions — as a whole-string check. The
open-connection message engine needs the same decision **incrementally**: a
text message's payload arrives in fragments and recv-sized chunks, one
character may straddle any of those boundaries (§5.6), and a definite
violation must fail the connection at once (§8.1 fail fast) — while a
merely-incomplete trailing character must not.

This module is that incremental form: an 8-state automaton whose state
between chunks is exactly "how far into one character the stream stopped"
(`State`, `step`); `run` folds it over a chunk, with `none` the definite
violation. The theorems:

* `validReason_iff_run` — **the automaton is the spec**: a byte string
  satisfies the whole-string validator iff running the automaton from `ready`
  lands back on `ready`.
* `run_append` — **chunking-schedule independence**: running chunk-by-chunk
  composes, so the verdict cannot depend on where recv or fragment boundaries
  fell.
* `error_definite` — **fail-fast soundness**: once `run` answers `none`, *no*
  continuation of the input satisfies the spec — rejecting mid-message refuses
  only streams every completion of which is invalid.
* `partial_completable` — **fail-fast completeness**: every live state is at
  most 3 octets from acceptance (`completion`), so an alive scan never
  condemns a stream that could still become valid.
* Kernel-checked vectors: the classic boundary cases (overlong `C0`/`E0 80`,
  surrogate `ED A0`, beyond-`U+10FFFF` `F4 90`, a character straddling a
  chunk boundary `E2 98 | 83`) land where RFC 3629 says.

`drorb_ws_utf8` (`@[export]`) is the C-ABI seam: (state, chunk) in, next
state out (`0xFF` = definite violation; states are `0–7`, `0` = character
boundary). The host keeps only the `u32` watermark state; every fail-fast and
end-of-message boundary decision it reports is this module's.
-/

namespace Ws
namespace Utf8

open CloseHandshake (isCont inRange validUtf8Aux validReason)

/-! ## The automaton -/

/-- Where within one UTF-8 character the stream stopped. -/
inductive State where
  /-- At a character boundary: expecting a leading octet. -/
  | ready
  /-- One unconstrained continuation octet (`0x80–0xBF`) remains. -/
  | one
  /-- Two unconstrained continuation octets remain. -/
  | two
  /-- Three unconstrained continuation octets remain. -/
  | three
  /-- After an `0xE0` lead: the next octet must be `0xA0–0xBF` (the overlong
  exclusion), then one more continuation. -/
  | e0
  /-- After an `0xED` lead: the next octet must be `0x80–0x9F` (the surrogate
  exclusion, `U+D800–U+DFFF`), then one more continuation. -/
  | ed
  /-- After an `0xF0` lead: the next octet must be `0x90–0xBF` (the overlong
  exclusion), then two more continuations. -/
  | f0
  /-- After an `0xF4` lead: the next octet must be `0x80–0x8F` (the
  beyond-`U+10FFFF` exclusion), then two more continuations. -/
  | f4
deriving Repr, DecidableEq

/-- One octet of the RFC 3629 grammar; `none` is a definite violation. The
`ready` dispatch mirrors the spec validator's leading-byte ranges exactly;
the constrained second octets (`e0`/`ed`/`f0`/`f4`) carry its overlong,
surrogate, and beyond-`U+10FFFF` exclusions. -/
def step : State → UInt8 → Option State
  | .ready, b =>
    if b.toNat ≤ 0x7F then some .ready
    else if inRange b 0xC2 0xDF then some .one
    else if b.toNat = 0xE0 then some .e0
    else if b.toNat = 0xED then some .ed
    else if inRange b 0xE0 0xEF then some .two
    else if b.toNat = 0xF0 then some .f0
    else if b.toNat = 0xF4 then some .f4
    else if inRange b 0xF0 0xF4 then some .three
    else none
  | .one, b => if isCont b then some .ready else none
  | .two, b => if isCont b then some .one else none
  | .three, b => if isCont b then some .two else none
  | .e0, b => if inRange b 0xA0 0xBF then some .one else none
  | .ed, b => if inRange b 0x80 0x9F then some .one else none
  | .f0, b => if inRange b 0x90 0xBF then some .two else none
  | .f4, b => if inRange b 0x80 0x8F then some .two else none

/-- Run the automaton over one chunk. Total (structural recursion on the
chunk); a violation (`none`) is absorbing. -/
def run (s : State) : Bytes → Option State
  | [] => some s
  | b :: bs =>
    match step s b with
    | some s' => run s' bs
    | none => none

private theorem bind_some {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

private theorem bind_none {α β : Type _} (f : α → Option β) :
    (none : Option α).bind f = none := rfl

/-- `run` on a cons is one `step`, then the rest — `none` absorbing. -/
theorem run_cons (s : State) (b : UInt8) (bs : Bytes) :
    run s (b :: bs) = (step s b).bind (fun s' => run s' bs) := by
  cases h : step s b <;> simp [run, h]

/-! ## Chunking-schedule independence -/

/-- **Chunking-schedule independence.** Scanning `xs ++ ys` is scanning `xs`,
then scanning `ys` from where it left off: the verdict cannot depend on where
the recv or fragment boundaries fell. -/
theorem run_append (s : State) (xs ys : Bytes) :
    run s (xs ++ ys) = (run s xs).bind (fun s' => run s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    rw [List.cons_append, run_cons, run_cons]
    cases step s b with
    | none => rfl
    | some s' => exact ih s'

/-! ## `step` computed on the leading-byte ranges -/

private theorem inR {b : UInt8} {lo hi : Nat} (h : inRange b lo hi = true) :
    lo ≤ b.toNat ∧ b.toNat ≤ hi := by
  simpa [inRange] using h

private theorem step_ready_ascii {b : UInt8} (h : b.toNat ≤ 0x7F) :
    step .ready b = some .ready := by
  simp [step, h]

private theorem step_ready_pair {b : UInt8} (h : inRange b 0xC2 0xDF = true) :
    step .ready b = some .one := by
  have hr := inR h
  simp only [step]
  rw [if_neg (by omega), if_pos h]

private theorem step_ready_e0 {b : UInt8} (h : b.toNat = 0xE0) :
    step .ready b = some .e0 := by
  simp only [step]
  rw [if_neg (by omega), if_neg (by simp [inRange]; omega), if_pos h]

private theorem step_ready_ed {b : UInt8} (h : b.toNat = 0xED) :
    step .ready b = some .ed := by
  simp only [step]
  rw [if_neg (by omega), if_neg (by simp [inRange]; omega),
      if_neg (by omega), if_pos h]

private theorem step_ready_triple {b : UInt8} (h : inRange b 0xE0 0xEF = true)
    (h0 : ¬ b.toNat = 0xE0) (hd : ¬ b.toNat = 0xED) :
    step .ready b = some .two := by
  have hr := inR h
  simp only [step]
  rw [if_neg (by omega), if_neg (by simp [inRange]; omega), if_neg h0,
      if_neg hd, if_pos h]

private theorem step_ready_f0 {b : UInt8} (h : b.toNat = 0xF0) :
    step .ready b = some .f0 := by
  simp only [step]
  rw [if_neg (by omega), if_neg (by simp [inRange]; omega),
      if_neg (by omega), if_neg (by omega),
      if_neg (by simp [inRange]; omega), if_pos h]

private theorem step_ready_f4 {b : UInt8} (h : b.toNat = 0xF4) :
    step .ready b = some .f4 := by
  simp only [step]
  rw [if_neg (by omega), if_neg (by simp [inRange]; omega),
      if_neg (by omega), if_neg (by omega),
      if_neg (by simp [inRange]; omega), if_neg (by omega), if_pos h]

private theorem step_ready_quad {b : UInt8} (h : inRange b 0xF0 0xF4 = true)
    (h0 : ¬ b.toNat = 0xF0) (h4 : ¬ b.toNat = 0xF4) :
    step .ready b = some .three := by
  have hr := inR h
  simp only [step]
  rw [if_neg (by omega), if_neg (by simp [inRange]; omega),
      if_neg (by omega), if_neg (by omega),
      if_neg (by simp [inRange]; omega), if_neg h0, if_neg h4, if_pos h]

private theorem step_ready_none {b : UInt8} (h7 : ¬ b.toNat ≤ 0x7F)
    (h2 : ¬ inRange b 0xC2 0xDF = true) (h3 : ¬ inRange b 0xE0 0xEF = true)
    (h4 : ¬ inRange b 0xF0 0xF4 = true) : step .ready b = none := by
  simp only [inRange, decide_eq_true_eq] at h2 h3 h4
  simp only [step]
  rw [if_neg h7, if_neg (by simp [inRange]; omega),
      if_neg (by omega), if_neg (by omega),
      if_neg (by simp [inRange]; omega),
      if_neg (by omega), if_neg (by omega),
      if_neg (by simp [inRange]; omega)]

private theorem step_one {b : UInt8} :
    step .one b = if isCont b then some .ready else none := rfl
private theorem step_two {b : UInt8} :
    step .two b = if isCont b then some .one else none := rfl
private theorem step_three {b : UInt8} :
    step .three b = if isCont b then some .two else none := rfl
private theorem step_e0 {b : UInt8} :
    step .e0 b = if inRange b 0xA0 0xBF then some .one else none := rfl
private theorem step_ed {b : UInt8} :
    step .ed b = if inRange b 0x80 0x9F then some .one else none := rfl
private theorem step_f0 {b : UInt8} :
    step .f0 b = if inRange b 0x90 0xBF then some .two else none := rfl
private theorem step_f4 {b : UInt8} :
    step .f4 b = if inRange b 0x80 0x8F then some .two else none := rfl

/-! ## The automaton is the spec -/

/-- **The automaton is the spec** (fuel form). For any sufficient fuel, the
whole-string validator accepts exactly the strings on which the automaton
runs from `ready` back to `ready`. -/
theorem valid_iff_run : ∀ (fuel : Nat) (bs : Bytes), bs.length ≤ fuel →
    (validUtf8Aux fuel bs = true ↔ run .ready bs = some .ready)
  | fuel, [], _ => by cases fuel <;> simp [validUtf8Aux, run]
  | 0, _ :: _, h => by simp only [List.length_cons] at h; omega
  | fuel + 1, b0 :: rest, h => by
    have hlen : rest.length ≤ fuel := by
      simp only [List.length_cons] at h; omega
    simp only [validUtf8Aux]
    by_cases h7 : b0.toNat ≤ 0x7F
    · rw [if_pos h7, run_cons, step_ready_ascii h7, bind_some]
      exact valid_iff_run fuel rest hlen
    rw [if_neg h7]
    by_cases h2 : inRange b0 0xC2 0xDF = true
    · -- Two-octet character: one unconstrained continuation.
      rw [if_pos h2, run_cons, step_ready_pair h2, bind_some]
      cases rest with
      | nil => simp [run]
      | cons b1 rest2 =>
        have hlen2 : rest2.length ≤ fuel := by
          simp only [List.length_cons] at hlen; omega
        rw [run_cons, step_one]
        by_cases hc : isCont b1 = true
        · rw [if_pos hc, bind_some]
          simp only [hc, Bool.true_and]
          exact valid_iff_run fuel rest2 hlen2
        · rw [if_neg hc, bind_none]
          simp [Bool.and_eq_true, hc]
    rw [if_neg h2]
    by_cases h3 : inRange b0 0xE0 0xEF = true
    · -- Three-octet character: one constrained octet, one continuation.
      rw [if_pos h3]
      by_cases he0 : b0.toNat = 0xE0
      · rw [run_cons, step_ready_e0 he0, bind_some]
        cases rest with
        | nil => simp [run]
        | cons b1 rest1 =>
          rw [run_cons, step_e0]
          cases rest1 with
          | nil =>
            by_cases hr : inRange b1 0xA0 0xBF = true
            · rw [if_pos hr, bind_some]; simp [run]
            · rw [if_neg hr, bind_none]; simp
          | cons b2 rest2 =>
            have hlen2 : rest2.length ≤ fuel := by
              simp only [List.length_cons] at hlen; omega
            rw [if_pos he0, if_neg (show ¬ b0.toNat = 0xED by omega)]
            by_cases hr : inRange b1 0xA0 0xBF = true
            · rw [if_pos hr, bind_some, run_cons, step_one]
              by_cases hc : isCont b2 = true
              · rw [if_pos hc, bind_some]
                simp only [hr, hc, Bool.true_and]
                exact valid_iff_run fuel rest2 hlen2
              · rw [if_neg hc, bind_none]
                simp [Bool.and_eq_true, hc]
            · rw [if_neg hr, bind_none]
              simp [Bool.and_eq_true, hr]
      by_cases hed : b0.toNat = 0xED
      · rw [run_cons, step_ready_ed hed, bind_some]
        cases rest with
        | nil => simp [run]
        | cons b1 rest1 =>
          rw [run_cons, step_ed]
          cases rest1 with
          | nil =>
            by_cases hr : inRange b1 0x80 0x9F = true
            · rw [if_pos hr, bind_some]; simp [run]
            · rw [if_neg hr, bind_none]; simp
          | cons b2 rest2 =>
            have hlen2 : rest2.length ≤ fuel := by
              simp only [List.length_cons] at hlen; omega
            rw [if_neg (show ¬ b0.toNat = 0xE0 by omega), if_pos hed]
            by_cases hr : inRange b1 0x80 0x9F = true
            · rw [if_pos hr, bind_some, run_cons, step_one]
              by_cases hc : isCont b2 = true
              · rw [if_pos hc, bind_some]
                simp only [hr, hc, Bool.true_and]
                exact valid_iff_run fuel rest2 hlen2
              · rw [if_neg hc, bind_none]
                simp [Bool.and_eq_true, hc]
            · rw [if_neg hr, bind_none]
              simp [Bool.and_eq_true, hr]
      · -- Generic three-octet lead (E1–EC, EE–EF): both unconstrained.
        rw [run_cons, step_ready_triple h3 he0 hed, bind_some]
        cases rest with
        | nil => simp [run]
        | cons b1 rest1 =>
          rw [run_cons, step_two]
          cases rest1 with
          | nil =>
            by_cases hc : isCont b1 = true
            · rw [if_pos hc, bind_some]; simp [run]
            · rw [if_neg hc, bind_none]; simp
          | cons b2 rest2 =>
            have hlen2 : rest2.length ≤ fuel := by
              simp only [List.length_cons] at hlen; omega
            rw [if_neg he0, if_neg hed]
            have hcont : inRange b1 0x80 0xBF = isCont b1 := rfl
            by_cases hc1 : isCont b1 = true
            · rw [if_pos hc1, bind_some, run_cons, step_one]
              by_cases hc2 : isCont b2 = true
              · rw [if_pos hc2, bind_some]
                simp only [hcont, hc1, hc2, Bool.true_and]
                exact valid_iff_run fuel rest2 hlen2
              · rw [if_neg hc2, bind_none]
                simp [Bool.and_eq_true, hc2]
            · rw [if_neg hc1, bind_none]
              simp [Bool.and_eq_true, hcont, hc1]
    rw [if_neg h3]
    by_cases h4 : inRange b0 0xF0 0xF4 = true
    · -- Four-octet character: one constrained octet, two continuations.
      rw [if_pos h4]
      by_cases hf0 : b0.toNat = 0xF0
      · rw [run_cons, step_ready_f0 hf0, bind_some]
        cases rest with
        | nil => simp [run]
        | cons b1 rest1 =>
          rw [run_cons, step_f0]
          cases rest1 with
          | nil =>
            by_cases hr : inRange b1 0x90 0xBF = true
            · rw [if_pos hr, bind_some]; simp [run]
            · rw [if_neg hr, bind_none]; simp
          | cons b2 rest1' =>
            cases rest1' with
            | nil =>
              by_cases hr : inRange b1 0x90 0xBF = true
              · rw [if_pos hr, bind_some, run_cons, step_two]
                by_cases hc : isCont b2 = true
                · rw [if_pos hc, bind_some]; simp [run]
                · rw [if_neg hc, bind_none]; simp
              · rw [if_neg hr, bind_none]; simp
            | cons b3 rest2 =>
              have hlen2 : rest2.length ≤ fuel := by
                simp only [List.length_cons] at hlen; omega
              rw [if_pos hf0, if_neg (show ¬ b0.toNat = 0xF4 by omega)]
              by_cases hr : inRange b1 0x90 0xBF = true
              · rw [if_pos hr, bind_some, run_cons, step_two]
                by_cases hc2 : isCont b2 = true
                · rw [if_pos hc2, bind_some, run_cons, step_one]
                  by_cases hc3 : isCont b3 = true
                  · rw [if_pos hc3, bind_some]
                    simp only [hr, hc2, hc3, Bool.true_and]
                    exact valid_iff_run fuel rest2 hlen2
                  · rw [if_neg hc3, bind_none]
                    simp [Bool.and_eq_true, hc3]
                · rw [if_neg hc2, bind_none]
                  simp [Bool.and_eq_true, hc2]
              · rw [if_neg hr, bind_none]
                simp [Bool.and_eq_true, hr]
      by_cases hf4 : b0.toNat = 0xF4
      · rw [run_cons, step_ready_f4 hf4, bind_some]
        cases rest with
        | nil => simp [run]
        | cons b1 rest1 =>
          rw [run_cons, step_f4]
          cases rest1 with
          | nil =>
            by_cases hr : inRange b1 0x80 0x8F = true
            · rw [if_pos hr, bind_some]; simp [run]
            · rw [if_neg hr, bind_none]; simp
          | cons b2 rest1' =>
            cases rest1' with
            | nil =>
              by_cases hr : inRange b1 0x80 0x8F = true
              · rw [if_pos hr, bind_some, run_cons, step_two]
                by_cases hc : isCont b2 = true
                · rw [if_pos hc, bind_some]; simp [run]
                · rw [if_neg hc, bind_none]; simp
              · rw [if_neg hr, bind_none]; simp
            | cons b3 rest2 =>
              have hlen2 : rest2.length ≤ fuel := by
                simp only [List.length_cons] at hlen; omega
              rw [if_neg (show ¬ b0.toNat = 0xF0 by omega), if_pos hf4]
              by_cases hr : inRange b1 0x80 0x8F = true
              · rw [if_pos hr, bind_some, run_cons, step_two]
                by_cases hc2 : isCont b2 = true
                · rw [if_pos hc2, bind_some, run_cons, step_one]
                  by_cases hc3 : isCont b3 = true
                  · rw [if_pos hc3, bind_some]
                    simp only [hr, hc2, hc3, Bool.true_and]
                    exact valid_iff_run fuel rest2 hlen2
                  · rw [if_neg hc3, bind_none]
                    simp [Bool.and_eq_true, hc3]
                · rw [if_neg hc2, bind_none]
                  simp [Bool.and_eq_true, hc2]
              · rw [if_neg hr, bind_none]
                simp [Bool.and_eq_true, hr]
      · -- Generic four-octet lead (F1–F3): all three unconstrained.
        rw [run_cons, step_ready_quad h4 hf0 hf4, bind_some]
        cases rest with
        | nil => simp [run]
        | cons b1 rest1 =>
          rw [run_cons, step_three]
          cases rest1 with
          | nil =>
            by_cases hc : isCont b1 = true
            · rw [if_pos hc, bind_some]; simp [run]
            · rw [if_neg hc, bind_none]; simp
          | cons b2 rest1' =>
            cases rest1' with
            | nil =>
              by_cases hc1 : isCont b1 = true
              · rw [if_pos hc1, bind_some, run_cons, step_two]
                by_cases hc2 : isCont b2 = true
                · rw [if_pos hc2, bind_some]; simp [run]
                · rw [if_neg hc2, bind_none]; simp
              · rw [if_neg hc1, bind_none]; simp
            | cons b3 rest2 =>
              have hlen2 : rest2.length ≤ fuel := by
                simp only [List.length_cons] at hlen; omega
              rw [if_neg hf0, if_neg hf4]
              have hcont : inRange b1 0x80 0xBF = isCont b1 := rfl
              by_cases hc1 : isCont b1 = true
              · rw [if_pos hc1, bind_some, run_cons, step_two]
                by_cases hc2 : isCont b2 = true
                · rw [if_pos hc2, bind_some, run_cons, step_one]
                  by_cases hc3 : isCont b3 = true
                  · rw [if_pos hc3, bind_some]
                    simp only [hcont, hc1, hc2, hc3, Bool.true_and]
                    exact valid_iff_run fuel rest2 hlen2
                  · rw [if_neg hc3, bind_none]
                    simp [Bool.and_eq_true, hc3]
                · rw [if_neg hc2, bind_none]
                  simp [Bool.and_eq_true, hc2]
              · rw [if_neg hc1, bind_none]
                simp [Bool.and_eq_true, hcont, hc1]
    · -- No admissible lead octet: both sides refuse.
      rw [if_neg h4, run_cons, step_ready_none h7 h2 h3 h4, bind_none]
      simp

/-- **The automaton is the spec.** `validReason` (the RFC 3629 whole-string
validator the close-reason well-formedness is stated over) accepts exactly
the strings the automaton scans from `ready` back to `ready`. -/
theorem validReason_iff_run (bs : Bytes) :
    validReason bs = true ↔ run .ready bs = some .ready := by
  unfold CloseHandshake.validReason
  exact valid_iff_run (bs.length + 1) bs (by omega)

/-! ## Fail-fast: errors are definite, live states are completable -/

/-- **Fail-fast soundness.** Once the automaton answers `none`, no
continuation of the input can satisfy the spec: rejecting mid-message refuses
only streams every completion of which is invalid. -/
theorem error_definite {bs : Bytes} (h : run .ready bs = none) (tail : Bytes) :
    validReason (bs ++ tail) = false := by
  have hrun : run .ready (bs ++ tail) = none := by
    rw [run_append, h, bind_none]
  cases hv : validReason (bs ++ tail) with
  | false => rfl
  | true =>
    have := (validReason_iff_run (bs ++ tail)).mp hv
    rw [hrun] at this
    exact Option.noConfusion this

/-- The canonical completion of each live state: the cheapest octets that
finish the in-flight character (at most 3). -/
def completion : State → Bytes
  | .ready => []
  | .one => [0x80]
  | .two => [0x80, 0x80]
  | .three => [0x80, 0x80, 0x80]
  | .e0 => [0xA0, 0x80]
  | .ed => [0x80, 0x80]
  | .f0 => [0x90, 0x80, 0x80]
  | .f4 => [0x80, 0x80, 0x80]

theorem completion_length (s : State) : (completion s).length ≤ 3 := by
  cases s <;> simp [completion]

theorem run_completion (s : State) : run s (completion s) = some .ready := by
  cases s <;> decide

/-- **Fail-fast completeness.** Every live (non-error) state is at most 3
octets from acceptance, so an alive scan never condemns a stream that could
still become valid — the automaton rejects exactly as late as the spec
permits. -/
theorem partial_completable {bs : Bytes} {s : State}
    (h : run .ready bs = some s) :
    validReason (bs ++ completion s) = true ∧ (completion s).length ≤ 3 := by
  refine ⟨(validReason_iff_run _).mpr ?_, completion_length s⟩
  rw [run_append, h, bind_some]
  exact run_completion s

/-! ## Kernel-checked vectors (non-vacuity) -/

/-- A plain ASCII-and-snowman text is accepted whole. -/
theorem vec_snowman :
    run .ready [0x68, 0x69, 0x20, 0xE2, 0x98, 0x83] = some .ready := by decide

/-- A chunk ending mid-character parks on the in-flight state — not an error —
and the continuation completes it (§5.6: a character may straddle chunks). -/
theorem vec_straddle :
    run .ready [0xE2, 0x98] = some .one ∧ run .one [0x83] = some .ready := by
  decide

/-- `0xFF` can begin no UTF-8 sequence: a definite violation. -/
theorem vec_ff_refused : run .ready [0xFF] = none := by decide

/-- The overlong lead `C0` (two-octet form of `U+0000–U+007F`) is refused. -/
theorem vec_overlong_refused : run .ready [0xC0] = none := by decide

/-- The overlong three-octet form `E0 80` is refused at its second octet. -/
theorem vec_overlong_e0_refused : run .ready [0xE0, 0x80] = none := by decide

/-- The surrogate range (`ED A0` starts `U+D800`) is refused at its second
octet. -/
theorem vec_surrogate_refused : run .ready [0xED, 0xA0] = none := by decide

/-- `F4 90` (the first sequence beyond `U+10FFFF`) is refused. -/
theorem vec_beyond_max_refused : run .ready [0xF4, 0x90] = none := by decide

/-- A bare continuation octet at a character boundary is refused. -/
theorem vec_bare_cont_refused : run .ready [0x80] = none := by decide

/-! ## The host-facing C-ABI seam -/

/-- The wire code of each state (`0–7`; `0` = character boundary). -/
def State.code : State → UInt32
  | .ready => 0
  | .one => 1
  | .two => 2
  | .three => 3
  | .e0 => 4
  | .ed => 5
  | .f0 => 6
  | .f4 => 7

/-- Decode a wire state code. -/
def ofCode (c : UInt32) : Option State :=
  if c = 0 then some .ready
  else if c = 1 then some .one
  else if c = 2 then some .two
  else if c = 3 then some .three
  else if c = 4 then some .e0
  else if c = 5 then some .ed
  else if c = 6 then some .f0
  else if c = 7 then some .f4
  else none

/-- The state encoding round-trips. -/
theorem ofCode_code (s : State) : ofCode s.code = some s := by
  cases s <;> rfl

/-- The definite-violation sentinel (disjoint from every state code). -/
def errCode : UInt32 := 0xFF

/-- No state code collides with the violation sentinel. -/
theorem code_ne_errCode (s : State) : s.code ≠ errCode := by
  cases s <;> decide

/-- `0` is exactly the `ready` (character-boundary) state. -/
theorem code_eq_zero_iff (s : State) : s.code = 0 ↔ s = .ready := by
  cases s <;> decide

/-- **`drorb_ws_utf8`.** The incremental-validation seam the host's message
engine crosses instead of validating UTF-8 itself: the watermark state and
the newly arrived (already unmasked) payload octets in, the next watermark
state out — `0xFF` = definite violation (fail the connection, 1007), `0` = at
a character boundary (a message may END here), `1–7` = a character is in
flight. An out-of-range input state (which the host never sends — it only
ever echoes this function's own output back) answers the violation sentinel. -/
@[export drorb_ws_utf8]
def scanExport (state : UInt32) (chunk : ByteArray) : UInt32 :=
  match ofCode state with
  | none => errCode
  | some s =>
    match run s chunk.toList with
    | some s' => s'.code
    | none => errCode

/-- The export computes `run`, in the round-tripping encoding. -/
theorem scanExport_spec (state : UInt32) (chunk : ByteArray) (s : State)
    (hs : ofCode state = some s) :
    scanExport state chunk
      = (match run s chunk.toList with
         | some s' => s'.code
         | none => errCode) := by
  simp [scanExport, hs]

/-- The zero-in/zero-out crossing is exactly whole-chunk spec validity: the
host's "message ends at a character boundary" check is `validReason`. -/
theorem scanExport_zero_iff (chunk : ByteArray) :
    scanExport 0 chunk = 0 ↔ validReason chunk.toList = true := by
  rw [validReason_iff_run]
  have h0 : ofCode 0 = some .ready := rfl
  rw [scanExport_spec 0 chunk .ready h0]
  cases h : run .ready chunk.toList with
  | none => simp [errCode]
  | some s' =>
    simp only [Option.some.injEq]
    cases s' <;> simp [State.code, errCode]

end Utf8
end Ws
