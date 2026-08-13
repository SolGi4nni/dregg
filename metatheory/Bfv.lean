/-
# Bfv — Lean-first BFV for the additive fold: the silent-failure GUARDS, as theorems.

**The first stone.** The bfv-sizing memo's verdict (TESTQALOG 2026-07-17, 4swarm/bfv-sizing): the
fold + n-of-n path consumes ~1/3 of an FHE library's surface because NO multiplication ever rides
it — so the Lean side can prove the two theorems that turn BFV's silent failures into RED ones,
against the real deployed parameters, with linear (additive-only, worst-case ℓ∞) noise analysis.
This namespace is those two theorems and their composition:

  * **`Bfv.Params`** — the (q, t, Δ, r) algebra + the deployed fhe.rs degree-4096 numbers,
    `decide`-pinned (109-bit q, t = 1032193, Δ ≈ 2^90).
  * **`Bfv.NoWrap`** — silent-failure class (C): the plaintext-modulus wrap. `fold_sum_no_wrap`
    (the `N·qmax < t` ingest gate is sound) + the HONEST tight capacities: **15** full-range u16
    orders per bucket (16 provably mis-clears: reads 16,367 where it holds 1,048,560), 252 at
    12-bit quantities.
  * **`Bfv.Noise`** — silent-failure class (A): the noise cliff. `decrypt_exact` (inside the
    margin `2t|e| + 2(t−1)r < q`, decryption is EXACT) + `decrypt_misses` (just past it, a wrong
    message decrypts CLEANLY — the failing side proved, not asserted) + exact noise additivity
    under homomorphic addition.
  * **`Bfv.Fold`** — the end-to-end keystone `fold_decrypts_exact` (K-fold add decrypts to the
    exact clear sum), the emitted noise-margin OBSERVABLE (`noiseMargin` / `marginHolds` +
    soundness), and the deployed-numbers composite `deployed_fold_decrypts_exact` closing both
    classes in one statement.
  * **`Bfv.Ring`** — the RING LIFT of the noise model: the carrier is `R = ℤ[X]/(X^N+1)` in
    coefficients, `negaMul` is PROVED to be its product (`negaMul_toPoly_dvd` /
    `toPoly_negaMul_quotient`, against Mathlib's `Polynomial ℤ`), and the provable worst-case
    expansion `‖a·b‖_∞ ≤ N·‖a‖_∞·‖b‖_∞` is proved AND proved TIGHT at every degree
    (`negaMul_expansion_attained`: the bound `N·1·1` is exactly attained). The public-linear
    step (`matVecCt` / `RowBound` / `step_noise_le` / `iter_noise_le`) is ported to the ring
    carrier with the SAME `RowBound` definition and the SAME `G^T` conclusion — **no ring
    expansion factor**, because a public INTEGER-scalar matrix acts coefficientwise. The
    heuristic average-case factor `δ_R ≈ 2√N` is deliberately NOT formalized.

## NOT proved here, named plainly (the honesty ledger)

  * **Class (B) — lattice security — is NOT a Lean theorem and never will be.** "128-bit secure"
    is an ESTIMATOR artifact (lattice-estimator pin + build gate, Rust-side); a proof assistant
    cannot truthfully state it. Anyone claiming a Lean proof of parameter security is selling
    something.
  * **The scalar-phase model gap — NARROWED, not closed.** `Bfv.Params`/`NoWrap`/`Noise`/`Fold`
    still model a ciphertext by one exact integer phase coefficient. `Bfv.Ring` supplies the
    carrier those files lack: the lift of the public-linear/additive path to `ℤ[X]/(X^N+1)` IS
    now formalized (`Bfv.stepR_noise_le`, `Bfv.iterR_noise_le`, `Bfv.toPoly_add`), and
    `negaMul_one_eq_mul` shows the scalar files are its `N = 1` slice. What is STILL not
    formalized: the ct×ct tensor step of `Bfv.Mul` on the ring, the encode/decode slot bijection,
    and the composition of `Bfv.Fold`'s deployed pins over the ring carrier — those files have
    not been re-stated over `RCt`.
  * **The fresh-noise bound `B_fresh ≈ 2^20` is an assumption.** Deriving it needs the
    ring-product expansion `|u·e|_∞ ≤ n·|u|_∞·|e|_∞`, which `Bfv.negaMul_normInf_le` NOW PROVES —
    but the derivation also needs a bound on the CBD(10)/CBD(20) samples themselves, which is a
    distributional fact and remains an assumption.
  * **Smudging / n-of-n threshold decrypt (class D)** — not modeled yet; that is the Phase-2
    deliverable the memo names (the flooding lemma + the fail-closed sampler gate).
  * Nothing here claims the deployed Rust ingest/decrypt currently ENFORCES these gates — these
    are the theorems the emitted constants make enforceable; wiring is named Rust-side work.
-/
import Bfv.Params
import Bfv.NoWrap
import Bfv.Noise
import Bfv.Fold
import Bfv.Ring

/-! Namespace-wide axiom hygiene: every theorem under `Bfv` pinned to the kernel triple. -/
#assert_namespace_axioms Bfv
