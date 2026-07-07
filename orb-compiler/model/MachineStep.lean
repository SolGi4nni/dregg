/-
C2 probe — the MACHINE primitive: one step of a saturating event counter FSM,
as a self-contained Lean 4 model (core only, no Mathlib).

Where C0/C1's `boundScan` is a REGION primitive (a bounds decision over a byte
view), this is a MACHINE primitive: a total transition `State -> Input -> State`.

  State  : a counter `c` (a UInt32, invariant `c <= CAP`).
  Input  : one byte `b`.
  Rule   : classify the byte, then update the counter.
             * a "low" byte (`b < 128`)  HOLDS the counter;
             * a "high" byte (`b >= 128`) is an EVENT: advance the counter,
               SATURATING at `CAP` (never overflow).

`step` is the transition. The whole machine `run` folds `step` over an input
stream from `c = 0`. This is the smallest honest core of a streaming FSM: a
data-dependent classify (`If`), a data-dependent saturating update (a second
`If`), and a state carried across the fold.

`step` is the SPEC. The Pancake program `pnk/machinestep.pnk` is the
IMPLEMENTATION (the same classify+saturate, folded by a `while`). The
preservation obligation (C2-MACHINE-REPORT §4, Link A) is that the machine
code cake emits for the `.pnk` refines this transition. The HOL4 theory
`hol-c2/machineStepLinkAScript.sml` discharges Link A for the SINGLE step.
-/

namespace C2

/-- The saturation cap. The counter never exceeds this. -/
@[inline] def CAP : UInt32 := 255

/-- One transition of the machine. Total by construction (no recursion, no
`partial`). Classifies the byte then updates the counter, saturating at `CAP`.
All arithmetic in `UInt32`; the only `+1` fires when `c < CAP <= 255`, so the
sum is `<= 255` and the `UInt32` wrap never triggers — the model computes over
the mathematical integers within range, exactly as the Pancake `c + 1` does. -/
@[inline] def step (c : UInt32) (b : UInt8) : UInt32 :=
  if b.toUInt32 < 128 then c            -- low byte: hold
  else if c < CAP then c + 1 else CAP   -- high byte: saturating increment

/-- The whole machine: fold the transition over an input stream from `c = 0`. -/
def run (input : Array UInt8) : UInt32 :=
  input.foldl step 0

/-! ### The MEANING the transition guarantees (constrains behaviour, not bounds)

These are the properties an FSM refinement must actually preserve, and they are
what the HOL4 Link A theorem re-establishes on the machine side (the state
relation is an *invariant* preserved by the emitted step). -/

/-- Saturation invariant: the transition never lets the counter exceed `CAP`.
This is the load-bearing safety property (a counter that overflowed would wrap
to 0 and undercount). Proven, so it is a fact and not a hope. -/
theorem step_le_cap (c : UInt32) (b : UInt8) (h : c ≤ CAP) : step c b ≤ CAP := by
  unfold step CAP
  split
  · exact h                                   -- hold: c ≤ 255 by hypothesis
  · split
    · -- high byte, c < 255: the increment stays in range, c + 1 ≤ 255
      rename_i hlt
      have h1 : c.toNat < 255 := by exact_mod_cast hlt
      have e1 : (1 : UInt32).toNat = 1 := by decide
      have e255 : (255 : UInt32).toNat = 255 := by decide
      have h2 : (c + 1).toNat = c.toNat + 1 := by rw [UInt32.toNat_add, e1]; omega
      refine UInt32.le_iff_toNat_le.mpr ?_
      rw [h2, e255]; omega
    · exact Nat.le.refl                        -- saturated: CAP ≤ CAP

/-- The classify law: a low byte holds the state exactly. -/
theorem step_low (c : UInt32) (b : UInt8) (h : b.toUInt32 < 128) : step c b = c := by
  unfold step; simp [h]

/-! ### Reference vectors

Input streams chosen adversarially to exercise every arm of the transition:
holds only, single events, the run-up to saturation, and past saturation. The
`0x80 = 128` byte is the boundary event byte (>= 128 fires); `0x7f = 127` is the
boundary hold byte (< 128 holds). These are the vectors run in all three kernels
(Lean here, and the compiled Pancake binary; HOL4 checks the single step). -/

/-- Named input vectors: `(name, bytes)`. -/
def vectors : List (String × Array UInt8) :=
  [ ("empty",        #[]),
    ("all-low",      #[0x00,0x7f,0x10,0x7f,0x00]),          -- 0 events -> 0
    ("three-events", #[0x80,0xff,0x81,0x7f,0x00]),          -- 3 events -> 3
    ("boundary-127", #[0x7f,0x7f,0x7f]),                    -- 127 holds -> 0
    ("boundary-128", #[0x80,0x80,0x80]),                    -- 128 events -> 3
    ("mixed",        #[0x80,0x00,0x90,0x7f,0xa0,0x40,0xff]) -- 4 events -> 4
  ]

/-- A stream of `n` event bytes (0xFF), to drive saturation past CAP. -/
def eventBurst (n : Nat) : Array UInt8 := Array.replicate n 0xFF

def main : IO Unit := do
  IO.println s!"CAP = {CAP}"
  for (name, bytes) in vectors do
    IO.println s!"run {name} (len={bytes.size})  =>  {run bytes}"
  -- saturation: 300 events must saturate at CAP=255, not wrap
  IO.println s!"run event-burst-300 (len=300)  =>  {run (eventBurst 300)}  (must be 255)"
  IO.println s!"run event-burst-255 (len=255)  =>  {run (eventBurst 255)}  (must be 255)"
  IO.println s!"run event-burst-254 (len=254)  =>  {run (eventBurst 254)}  (must be 254)"

end C2
