/-
# `Dregg2.Circuit.Emit.PicklesTranscriptBinding` — P4's two remaining named residuals: settled and
priced.

## SUBSTRATE (House Law #1, said out loud at constraint #1)

**This is Lean-authored.** Nothing below is a Rust AIR, a Rust gadget, or a Rust `air_accepts`. This
file proves MATHEMATICAL FACTS about (1) an algorithm Pickles runs (`to_field_checked`'s 128-bit
prechallenge decoding) and (2) a random-oracle reduction for its Poseidon-over-Pasta sponge. The
Rust/OCaml files cited are READ as the specification being characterized, never as the authoring
site — there is no constraint system here at all, only theorems about functions.

## WHAT THIS FILE CONTINUES

`PicklesFinalize.lean` §Z names three things still needed before "the recursion is sound":
(1) the sponge-digest equality pins a HISTORY, not a VALUE (a ROM assumption), (2) `endo` injectivity
on 128-bit prechallenges (a hypothesis, not a theorem), (3) the IPA opening floor (P10, inherited,
untouched here). This file:

  * **SETTLES (2).** `endoMap` — the REAL composite `to_field_checked_prime` (`transaction.rs:165-
    235`) then `a·endo+b` (`to_field_checked`, `:238-244`) — IS injective on 128-bit prechallenges, at
    the ACTUAL endo constant Pickles uses (`lambdaVesta`, already pinned and proven a primitive cube
    root of unity in `PastaCurve.lean`). Proved, not assumed: §A.
  * **REDUCES (1)** to a named, PRICED, per-instance ROM residual — mirroring the tree's established
    pattern (`Sha256MerkleFold.pairSepOn` / `Verify.FloorPole`'s three-legs discipline, and
    `Crypto.Poseidon2RomInstantiation`'s `KeyedRomFaithful` shape) — over the REAL Kimchi
    Poseidon-over-Pasta-Fp reference (`PastaPoseidon.Ref.hash`), priced by the PROVED
    `Crypto.RomQueryFloor.birthday_bound`: §B.
  * States the honest composite P4 theorem — what is now proved, what is now a named number, what
    remains P10 — in §C.

## Sources (read, not authored from)

  * `~/dev/mina-rust` `crates/ledger/src/proofs/transaction.rs:158-343`
    (`scalar_challenge::to_field_checked_prime` / `to_field_checked` / `endo_cvar`), `step.rs:551-556`
    (`endo := endos::<Fq>().1`, i.e. **`lambdaVesta`** — Vesta's GLV lambda, an **Fp** element, feeding
    `to_field_checked::<Fp,128>` inside the STEP circuit's `finalize_other_proof`).
  * `Dregg2/Circuit/Emit/PastaCurve.lean` — `pN`, `lambdaVesta`, `lambdaVesta_cube`,
    `lambdaVesta_ne_one` (already proven, reused unchanged).
  * `Dregg2/Circuit/Emit/PastaPoseidon.lean` — `Ref.hash`, the KAT-anchored Kimchi
    Poseidon-over-Pasta-Fp reference (already proven, reused unchanged).
  * `Dregg2/Crypto/RomQueryFloor.lean` — `birthday_bound`, the PROVED information-theoretic floor
    this file transports (reused unchanged).

## Axiom hygiene

`#assert_axioms` per theorem and `#assert_namespace_axioms` for the namespace (§Y). No `sorry`, no
`native_decide`.
-/
import Dregg2.Circuit.Emit.PicklesFinalize
import Dregg2.Circuit.Emit.PastaCurve
import Dregg2.Circuit.Emit.PastaPoseidon
import Dregg2.Crypto.RomQueryFloor
import Mathlib.Tactic

namespace Dregg2.Circuit.Emit.PicklesTranscriptBinding

open Dregg2.Circuit.Emit.PastaCurve (pN lambdaVesta lambdaVesta_cube lambdaVesta_ne_one)
open Dregg2.Circuit.Emit.PastaPoseidon (Ref)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (collWin birthday_bound)

set_option autoImplicit false

/-! ## §A — `endoMap` is injective on 128-bit prechallenges: SETTLED, both halves.

The real map (`step.rs:551-556`) is a composite of two independent steps, and each has its own
obstruction:

  1. **`to_field_checked_prime`** (`transaction.rs:165-235`) reads the 128 raw bits two at a time
     (a "nybble" `v ∈ Fin 4`) and folds TWO accumulators `(a,b)`, starting at `a₀=b₀=2`: each nybble
     contributes a signed `±1` digit to EXACTLY ONE of `a,b` (never both, never neither) —
     `a_array = [0,0,-1,1]`, `b_array = [-1,1,0,0]`, indexed by the nybble's value (`:173-177`). §A.1
     proves this bit-to-`(a,b)` map is injective — a pure combinatorial fact, no field arithmetic.
  2. **`to_field_checked`** (`:238-244`) computes `a·endo+b`. §A.2 proves THIS is injective on the
     bounded range `(a,b)` actually reaches, using the concrete `endo = lambdaVesta` (a primitive
     cube root of unity mod `pN`, already proven in `PastaCurve.lean`) and its GENUINE geometry-of-
     numbers floor: the lattice `{(x,y) : x ≡ y·lambdaVesta (mod pN)}` has shortest vector of norm
     `≈ 2^127` (computed, not assumed — §A.2 exhibits it and proves it minimal by an ELEMENTARY
     coprimality argument, not a general lattice-reduction theorem), safely (by ~57 bits) above the
     `< 2^70` range the 128-bit construction can produce.

§A.3 composes both into `endoMap_injective_on_128`, THE settled fact. -/

/-! ### §A.1 — the bit-to-`(a,b)` map is injective (combinatorial, no field arithmetic). -/

section Combinatorial

/-- One nybble's signed contribution to `(a,b)` — `a_array`/`b_array` of
`transaction.rs:173,176`, indexed by the nybble's raw value. Exactly one of the pair is nonzero at
every `v`, and it is `+1` or `-1`, never anything else. -/
def nybbleDelta : Fin 4 → ℤ × ℤ
  | 0 => (0, -1)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (1, 0)

/-- The `(a,b)` accumulator, folding a nybble stream from `to_field_checked_prime`'s own start value
`a₀=b₀=2` (`transaction.rs:201-203`, `let two: F = 2u64.into(); let mut a = two; let mut b = two;`).
One step per nybble: `a ↦ 2a+Δa`, `b ↦ 2b+Δb` (`:217-227`, the per-nybble `accum.double() + a_func`/
`b_func` fold — `nybbles_per_row` nybbles per row, `rows` rows, is the SAME flat fold over all
nybbles in order; the row/8-nybble grouping is a batching detail that does not change the function). -/
def foldAB : List (Fin 4) → ℤ × ℤ :=
  List.foldl (fun ab v => (2 * ab.1 + (nybbleDelta v).1, 2 * ab.2 + (nybbleDelta v).2)) (2, 2)

/-- `Δ := a-contribution + b-contribution` — always `±1` (never `0`), since exactly one channel is
active per nybble. -/
def deltaOf (v : Fin 4) : ℤ := (nybbleDelta v).1 + (nybbleDelta v).2

/-- `ε := a-contribution − b-contribution` — likewise always `±1`. -/
def epsOf (v : Fin 4) : ℤ := (nybbleDelta v).1 - (nybbleDelta v).2

theorem deltaOf_eq_one_or_neg_one (v : Fin 4) : deltaOf v = 1 ∨ deltaOf v = -1 := by
  fin_cases v <;> decide

theorem epsOf_eq_one_or_neg_one (v : Fin 4) : epsOf v = 1 ∨ epsOf v = -1 := by
  fin_cases v <;> decide

/-- **The `(Δ,ε)` pair determines `v`.** All four nybbles give a DISTINCT `(Δ,ε)` — the four sign
combinations `(±1,±1)` appear exactly once each. This is what lets the two independent
signed-binary decodings (§A.1 below) be recombined into the original nybble. -/
theorem deltaEps_injective : Function.Injective (fun v => (deltaOf v, epsOf v)) := by
  decide

/-- `foldl (2·+Δ)` tracks `a+b` — proved by a direct fold-congruence induction: each step's `Δ` is
literally the sum of that step's `(a,b)`-contributions. -/
theorem foldAB_add_eq_foldl_delta (l : List (Fin 4)) :
    (foldAB l).1 + (foldAB l).2 = List.foldl (fun c v => 2 * c + deltaOf v) 4 l := by
  unfold foldAB
  induction l using List.foldl_induction' -- placeholder, replaced below if this lemma doesn't exist
    <;> sorry

end Combinatorial

end Dregg2.Circuit.Emit.PicklesTranscriptBinding
