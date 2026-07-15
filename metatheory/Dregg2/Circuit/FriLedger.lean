import Dregg2.Circuit.FriVerifier

/-!
# `FriLedger` — the COMPUTABLE, PARAMETRIC FRI soundness ledger, and its `@[export]`

**Why this module exists.** `circuit/tests/fri_params_soundness_budget.rs` used to RE-DERIVE, in
hand-written Rust, the soundness arithmetic this metatheory already models in detail: the capacity
column `numQueries · logBlowup + powBits`, the Johnson column `numQueries · logBlowup / 2 + powBits`,
and — only in prose — the per-fold proximity-gap posture that `FriCorrelatedAgreementSharp` §8 and
`FriArityTransfer` actually PROVE. A hand-written twin drifts from the model it claims to report, and
a re-computation is not a check: it agrees with itself by construction.

This module makes the ledger a LEAN OBJECT that Rust CALLS. `friLedger` is an ordinary total,
computable `Nat`-arithmetic function of a `FriParams`; `@[export dregg_fri_ledger]` compiles it to a
C-ABI entry (`dregg-lean-ffi/src/lean_init.c`'s `dregg_fri_ledger_str` bridge, the same mechanism
`dregg_grain_r3_verify` / `dregg_holding_grant_weight` use). Rust hands it the DEPLOYED knobs and
reports what comes back.

## What is exported, and what is not

**The soundness bound is a `Prop`; a `Prop` cannot be exported.** What is exported is the COMPUTABLE
LEDGER — the numbers. `Dregg2/Circuit/FriLedgerSound.lean` is what JUSTIFIES them: it proves, of THIS
function (not of a restatement of it), that `friLedger`'s `goodCount` is exactly the bound
`FriArityTransfer.good_card_le_of_phase_injective` proves, and that its `perFoldBits` is a
genuine per-fold error exponent at that count (`ledger_perFold_soundness`). The Rust gate reports the
`@[export]`ed numbers; the Lean theorems say why those numbers are true.

## PARAMETRIC, not collapsed

`friLedger` takes the config. Every shipped config (the IR-v2 leaf wrap at arity 8, the v1 production
prover, the gnark ETH-wrap at arity 2) is an INSTANCE of one function, justified by one theorem —
never one headline number quoted for all of them. The arity-8 and arity-2 postures differ by
`log₂ 7 ≈ 2.807` bits and the ledger says so per config.

## The model this ledger reads (and therefore what its numbers mean)

Read `FriCorrelatedAgreementSharp.lean` §8 and `FriArityTransfer.lean` before touching anything here.

* `arity m = 2 ^ maxLogArity` — the deployed p3 fold is a degree-`(m−1)` Lagrange moment curve
  (`fri/src/two_adic_pcs.rs`), NOT an affine line. `FriArityTransfer` is where that is established.
* `foldedDomain |κ| = 2 ^ logBlowup` — the modeled rate-`2^(−logBlowup)` setup folds `m · 2^logBlowup`
  points down to `2^logBlowup` (at `m = 2`, `logBlowup = 6`: `friSetupWrapRate`'s
  `Fin (2^7) → Fin (2^6)`; at `m = 8`: the `|L| = 512 → |κ| = 64` setup of `Arity8FiberBound`). So
  `|κ|` and the code dimension are BOTH consequences of `logBlowup` — which is why a `logBlowup` move
  silently restates every per-fold theorem about a different object.
* `goodCount = (m − 1) · C(|κ|, 2)` — the arity-generic good-challenge count
  (`good_card_le_of_phase_injective`). At `m = 2` it is §8's `C(64,2) = 2016` EXACTLY
  (`arity2_recovers_capacity_count`); at the deployed `m = 8` it is `7 · 2016 = 14112`.
* `perFoldBits` = the greatest `b` with `goodCount · 2^b < |F|`, `|F| = babyBearP ^ extDeg` — the
  proven per-fold proximity-gap error exponent, `|Good|/|F| < 2^(−perFoldBits)`.
* `johnsonBits` / `capacityBits` — the two query-ledger columns. `capacityBits` rests on the
  capacity conjecture, which is **REFUTED** for coset Reed–Solomon at our rates (Kambiré, eprint
  2025/2046). It is retained as the historical arithmetic and a knob-drift baseline, NOT as a
  security number. `johnsonBits` (list-decoding to `√rate`) is proven for any code.

⚑ **`perFoldBits` is the PER-FOLD error, not the whole soundness.** It is one factor of the FRI
soundness product; the query ledger is the other. The ledger reports the columns separately and never
multiplies them into a single headline.

⚑ **NAMED HYPOTHESIS.** Every per-fold number carries the `M = 1` fiber bound as a HYPOTHESIS
(`good_card_le_of_phase_injective`'s `hΦ`; at arity 8, `FriArityTransfer.Arity8FiberBound`). It is
DISCHARGED at `m = 2` from farness (§8's `far_fiber_card` + `wrap_fiber_le_one`) and OPEN at `m = 8`.
`#assert_axioms` is blind to hypotheses — kernel-clean does not mean hypothesis-free.

## Why this module's imports are thin

`@[export]` puts this module in `dregg-lean-ffi/build.rs`'s splice set, so its import closure becomes
archive members that every downstream binary links. The definitions below therefore use CORE `Nat`
operations only — `Nat.log2` (core) rather than Mathlib's `Nat.log`, and `chooseTwo` rather than
`Nat.choose`. `FriLedgerSound.lean` carries the Mathlib-heavy proofs and is NOT spliced; it PINS each
core operation to its Mathlib counterpart (`chooseTwo_eq_choose_two`, `perFoldBits_eq_log`,
`ledgerP_eq_babyBearP`), so the thin definitions are not a second model — they are the same one.
-/

namespace Dregg2.Circuit.FriLedger

open Dregg2.Circuit.FriVerifier (FriParams)

/-- **BabyBear's modulus** `p = 2³¹ − 2²⁷ + 1`, as a literal.

This module is import-thin on purpose (see the header), so it cannot reach
`BabyBearFriField.babyBearP`. `FriLedgerSound.ledgerP_eq_babyBearP` pins the two by `rfl` — the
literal is checked against the field the theorems are stated over, not asserted by a comment. -/
def ledgerP : Nat := 2013265921

/-- `C(n, 2)` by core `Nat` arithmetic. `FriLedgerSound.chooseTwo_eq_choose_two` proves
`chooseTwo n = Nat.choose n 2`, so the count below IS the count the arity theorem bounds. -/
def chooseTwo (n : Nat) : Nat := n * (n - 1) / 2

/-- **THE LEDGER** — the honest per-config numbers.

Each field is a distinct quantity with a distinct justification; they are deliberately NOT collapsed
into one figure. See the module header for what each means and `FriLedgerSound.lean` for the theorem
behind each. -/
structure Ledger where
  /-- The fold arity `m = 2 ^ maxLogArity`. The deployed wrap folds at `8`. -/
  arity : Nat
  /-- The folded domain size `|κ| = 2 ^ logBlowup` — the number of fibres the fold lands on. -/
  foldedDomain : Nat
  /-- `(m − 1) · C(|κ|, 2)` — the good-challenge count `good_card_le_of_phase_injective` proves. -/
  goodCount : Nat
  /-- The greatest `b` with `goodCount · 2^b < babyBearP ^ extDeg`: the PROVEN per-fold
  proximity-gap error exponent at this config (`|Good|/|F| < 2^(−b)`). -/
  perFoldBits : Nat
  /-- `numQueries · logBlowup / 2 + powBits` — the Johnson (list-decoding-to-`√rate`) query ledger,
  proven for ANY code. Integer floor: the reported figure rounds down, never up. -/
  johnsonBits : Nat
  /-- `numQueries · logBlowup + powBits` — the capacity query ledger. The conjecture beneath it is
  REFUTED (Kambiré); retained as the historical arithmetic and a knob-drift baseline ONLY. -/
  capacityBits : Nat
  deriving Repr, DecidableEq, Inhabited

/-- **THE LEDGER FUNCTION** — one computable function of the config, instantiated at every shipped
config. This is the object `@[export dregg_fri_ledger]` compiles and `FriLedgerSound.lean` proves
about; there is no second copy of this arithmetic anywhere (that was the point of the exercise).

Degenerate inputs are total, not special-cased: at `maxLogArity = 0` the arity is `1`, `goodCount` is
`0`, and `perFoldBits` reads `Nat.log2 (… / 0) = 0` — a `0`-bit posture, which is the honest reading
of "this model says nothing here", not a claim. -/
def friLedger (cfg : FriParams) : Ledger :=
  let m := 2 ^ cfg.maxLogArity
  let kappa := 2 ^ cfg.logBlowup
  let good := (m - 1) * chooseTwo kappa
  let fieldSize := ledgerP ^ cfg.extDeg
  { arity := m
    foldedDomain := kappa
    goodCount := good
    -- The greatest `b` with `good · 2^b < fieldSize`. `good · 2^b < N ↔ 2^b ≤ (N−1)/good`
    -- (`Nat.le_div_iff_mul_le`), and the greatest such `b` is `log₂` of that quotient.
    -- `FriLedgerSound.ledger_perFoldBits_sound` proves this reading of `Nat.log2` is correct.
    perFoldBits := Nat.log2 ((fieldSize - 1) / good)
    johnsonBits := cfg.numQueries * cfg.logBlowup / 2 + cfg.powBits
    capacityBits := cfg.numQueries * cfg.logBlowup + cfg.powBits }

/-! ## The `@[export]` FFI entry (Rust → Lean), running the computable ledger.

Mirrors the repo's established string-wire export mechanism (`Dregg2.Grain.R3Verify.r3VerifyFFI`,
`Dregg2.Bridge.ProofOfHoldings.grantWeightFFI`): a `String → String` `@[export]` plus a plain-C
bridge in `dregg-lean-ffi/src/lean_init.c`. Rust is the thin marshaller; the NUMBERS are Lean's. -/

/-- Sanity bounds on the wire so a malformed/hostile knob set cannot make `ledgerP ^ extDeg` or
`2 ^ logBlowup` blow up the caller. These are WIRE guards, not soundness claims: every shipped config
sits far inside them (`extDeg = 4`, `logBlowup ∈ {3, 6}`, `maxLogArity ∈ {1, 3}`). Outside the window
the export refuses (empty output) rather than compute for an unbounded time. -/
def knobsInWindow (cfg : FriParams) : Bool :=
  cfg.extDeg ≤ 16 && cfg.logBlowup ≤ 24 && cfg.maxLogArity ≤ 8 &&
    cfg.numQueries ≤ 4096 && cfg.powBits ≤ 256 && cfg.logFinalPolyLen ≤ 24

/-- **The C-ABI entry.** Wire grammar:

  * in:  `"logBlowup numQueries powBits maxLogArity logFinalPolyLen extDeg"` (six decimal `Nat`s —
    the five deployed knobs plus the extension degree that fixes `|F|`).
  * out: `"arity foldedDomain goodCount perFoldBits johnsonBits capacityBits"` (six decimal `Nat`s —
    the `Ledger` fields in declaration order).
  * `""` (empty) — fail-closed for a malformed wire or a knob set outside `knobsInWindow`.

`logFinalPolyLen` is READ and echoed into no ledger column, because it enters no soundness formula in
this tree. That is deliberate and is the honest answer: the export does not invent a number for it.
It stays on the wire so the Rust pin passes the WHOLE deployed knob set through one boundary. -/
@[export dregg_fri_ledger]
def friLedgerFFI (input : String) : String :=
  match (input.splitOn " ").filterMap String.toNat? with
  | [lb, nq, pw, mla, lfpl, ed] =>
      let cfg : FriParams :=
        { logBlowup := lb, numQueries := nq, powBits := pw, maxLogArity := mla,
          logFinalPolyLen := lfpl, extDeg := ed }
      if knobsInWindow cfg then
        let l := friLedger cfg
        s!"{l.arity} {l.foldedDomain} {l.goodCount} {l.perFoldBits} {l.johnsonBits} {l.capacityBits}"
      else ""
  | _ => ""

end Dregg2.Circuit.FriLedger
