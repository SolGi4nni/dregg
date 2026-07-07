/-
C15 probe — the THIRD primitive: an HTTP RESPONSE STATUS CLASSIFIER, a real
serve fragment, as a self-contained Lean 4 model (core only, no Mathlib).

Where C0/C1's `boundScan` is a REGION primitive (bounds decision + scan loop)
and C2's `step` is a MACHINE primitive (a stateful transition), this is a
DECISION/MAPPER primitive: a pure classification `code -> classDigit`.

  Input  : an HTTP response status code (0..599 in practice; the model needs
           only `code < 1000`, well inside the signed 63-bit range).
  Rule   : map the code to its RFC 9110 class digit —
             1xx informational -> 1,  2xx success -> 2,  3xx redirect -> 3,
             4xx client error  -> 4,  5xx (and above) server error -> 5.

`statusClass` is the SPEC. The Pancake program `statusclass.pnk` is the
IMPLEMENTATION (the same else-if cascade). It is deliberately STRUCTURALLY
DIFFERENT from both prior primitives:
  * a LINEAR else-if CASCADE (4 guards, 5 leaves) — deeper than `step`'s
    2-guard/3-leaf nest, and unlike `boundScan` there is NO loop at all;
  * ONE input word read (vs `step`'s two) — so the wrapper's read section is a
    genuinely different length (N=1), exercising the read-fold generalization;
  * all-CONSTANT leaves (no data-dependent `c+1` arithmetic).

This is the fresh loop-free primitive C15 descends AUTOMATICALLY via the
`panLinkA_branch` tactic + the wrapper/LinkB generator.
-/

namespace C15

/-- Map an HTTP response status code to its class digit (RFC 9110 §15). A pure,
total, loop-free classifier — the smallest honest core of response routing. -/
@[inline] def statusClass (code : Nat) : Nat :=
  if code < 200 then 1        -- 1xx informational
  else if code < 300 then 2   -- 2xx success
  else if code < 400 then 3   -- 3xx redirection
  else if code < 500 then 4   -- 4xx client error
  else 5                      -- 5xx (and beyond) server error

/-! ### The MEANING the classifier guarantees -/

/-- The classifier always returns a valid class digit in 1..5. -/
theorem statusClass_range (code : Nat) : 1 ≤ statusClass code ∧ statusClass code ≤ 5 := by
  unfold statusClass
  split <;> [omega; split] <;> [omega; split] <;> [omega; split] <;> omega

/-- Reference vectors exercising every arm (boundary codes included). -/
def vectors : List (String × Nat) :=
  [ ("100-continue",        100),   -- 1
    ("199-boundary",        199),   -- 1
    ("200-ok",              200),   -- 2
    ("204-no-content",      204),   -- 2
    ("301-moved",           301),   -- 3
    ("404-not-found",       404),   -- 4
    ("418-teapot",          418),   -- 4
    ("500-internal",        500),   -- 5
    ("599-boundary",        599) ]  -- 5

def main : IO Unit := do
  for (name, code) in vectors do
    IO.println s!"statusClass {name} ({code})  =>  {statusClass code}"

end C15
