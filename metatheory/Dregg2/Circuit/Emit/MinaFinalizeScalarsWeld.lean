/-
# `Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld` — ⚑ the finalize-scalars program on Mina devnet
block 539508's OWN wire, against upstream's OWN answers.

## What is measured here, and against what

`MinaFinalizeScalars.finalizeProg` is a 301-op straight-line rendering of `ftEval0R` + `cipR` +
`permScalarR`. This file runs its DENOTATION (`progEval` — the same function the forcing story is
about, not the emit driver's memoized renderer) on the real block's environment and pins:

  * **cip** — the program's ξ-fold equals `MinaRealBlockGate.CIP`, the `combined_inner_product`
    `proof.oracles(…)` computed for the block (`real_cip` proved that number IS `cipR` of the
    47-entry es lists; this file proves the PROGRAM reaches the same number through its own 301
    ops, ft_eval0 recomputed in the middle);
  * **perm** — the program's permutation scalar equals `MinaWrapGroupGate.PERM_SCALAR`, o1-labs'
    own `perm_scalars` output for the block (the scalar the `f_comm` MSM consumes);
  * **the reference tie at the fixture point** — `cipRef`/`permRef` (the thin composition of the
    shipped bodies stated in the AIR file's §5) equal the same two numbers, so program and
    reference are tied AT THIS POINT through the block rather than through each other.
    ⚠ The GENERIC `progEval = reference` theorem (every ring, every environment) is the named
    residual `MinaFinalizeScalars` §5 stands for; until it lands, this weld is a differential —
    one point, real data, both sides upstream-derived — not a proof about all inputs.
  * **the constants** — `OMEGA_Q` is `MinaRealBlockGate.OMEGA` AND `rootOfUnity qN 14` (derived,
    not carried); the three `zkPolyR` roots are its powers; the seven shifts are the
    `MinaMultiBlockConformance` Wrap fixture's own list; the witnessed inverse inverts.
  * **the discriminations** — one bumped eval moves the cip; a bumped `LCT` moves it too (the
    port's affine reach, the same fact the Rust `lct-shift` exhibit proves ACCEPTS); a bumped σ
    eval moves the perm. Without these the equalities above could be theorems of a constant
    function.

## Axiom hygiene

Kernel `decide` throughout — no `native_decide`, no `#guard`, `#assert_axioms` per theorem.
NEW file; not imported by the `Dregg2` root, per house practice for gates.
Import line: `import Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld`
-/
import Dregg2.Circuit.Emit.MinaFinalizeScalars
import Dregg2.Circuit.Emit.MinaRealBlockGate
import Dregg2.Circuit.Emit.MinaWrapGroupGate
import Dregg2.Bridge.MinaMultiBlockConformance

namespace Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld

open Dregg2.Circuit.Emit.MinaFinalizeScalars
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Bridge.MinaWrapFtEval0 (invCand invOk rootOfUnity powFast)

abbrev Fq := ZMod qN

set_option autoImplicit false
set_option maxRecDepth 1000000

open Dregg2.Circuit.Emit.MinaRealBlockGate in
/-- ⚑ **THE REAL BLOCK'S ENVIRONMENT**, index for index the AIR file's §1 value table. The eval
columns are `EVZ`/`EVZW`'s slices (their indices 4… are the wire's 43 columns; 0..3 the prefix),
the challenges are the block's raw/mapped scalars, the two claims are upstream's own outputs, and
`DINV` is produced HERE by Fermat's ladder — `the_witnessed_inverse_inverts` is what makes that a
witness rather than a trust. -/
def env0Real : Nat → Fq := fun v =>
  if v < 43 then EVZ.getD (4 + v) 0
  else if v < 86 then EVZW.getD (4 + (v - 43)) 0
  else if v = vFT1 then EVZW.getD 3 0
  else if v = vPUBZ then EVZ.getD 2 0
  else if v = vPUBW then EVZW.getD 2 0
  else if v = vBETA then BETA
  else if v = vGAMMA then GAMMA
  else if v = vALPHA then ALPHA
  else if v = vZETA then ZETA
  else if v = vXI then VV
  else if v = vRSQ then UU
  else if v = vBP0Z then EVZ.getD 0 0
  else if v = vBP1Z then EVZ.getD 1 0
  else if v = vBP0W then EVZW.getD 0 0
  else if v = vBP1W then EVZW.getD 1 0
  else if v = vCIPCL then CIP
  else if v = vPERMCL then ((Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR : Nat) : Fq)
  else if v = vDINV then invCand ((ZETA - ((OM3_C : Nat) : Fq)) * (ZETA - 1))
  else if v = vLCT then LCT
  else if v = vONE then 1
  else if v = vZERO then 0
  else if v = vOM3 then ((OM3_C : Nat) : Fq)
  else if v = vOM2 then ((OM2_C : Nat) : Fq)
  else if v = vOM1 then ((OM1_C : Nat) : Fq)
  else if 108 ≤ v ∧ v < 115 then ((SHIFTS_Q.getD (v - 108) 0 : Nat) : Fq)
  else 0

/-- The computed-value index the final cip equality reads (the LAST op is that eq), and the one
the perm equality reads — extracted from the program, not hand-numbered. -/
def cipResultV : Nat := (finalizeProg.getD (finalizeProg.length - 1) ⟨.eq, 0, 0⟩).y
def permResultV : Nat :=
  ((finalizeProg.filter (fun o => o.k == FKind.eq && o.x == vPERMCL)).headD ⟨.eq, 0, 0⟩).y

/-- A one-index perturbation. -/
def bump (env0 : Nat → Fq) (v : Nat) (d : Fq) : Nat → Fq :=
  fun u => if u = v then env0 v + d else env0 u

/-! ## §1 — the constants are the deployed Wrap domain's, from two sources each. -/

set_option maxHeartbeats 1000000000 in
/-- ⚑ `OMEGA_Q` is simultaneously the fixture's generator (`MinaRealBlockGate.OMEGA`) and the
DERIVED `2^14`-th root of unity — carried nowhere, checked both ways. -/
theorem the_domain_generator_is_derived_and_the_fixtures :
    ((OMEGA_Q : Nat) : Fq) = Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA
    ∧ ((OMEGA_Q : Nat) : Fq) = rootOfUnity qN LOG2N := by
  refine ⟨by decide, by decide⟩

set_option maxHeartbeats 1000000000 in
/-- The three `zkPolyR` roots are the generator's `n−3`, `n−2`, `n−1` powers. -/
theorem the_zk_roots_are_the_generators_powers :
    ((OM3_C : Nat) : Fq) = powFast ((OMEGA_Q : Nat) : Fq) (DOMN - 3)
    ∧ ((OM2_C : Nat) : Fq) = powFast ((OMEGA_Q : Nat) : Fq) (DOMN - 2)
    ∧ ((OM1_C : Nat) : Fq) = powFast ((OMEGA_Q : Nat) : Fq) (DOMN - 1) := by
  refine ⟨by decide, by decide, by decide⟩

set_option maxHeartbeats 1000000000 in
/-- The seven shifts are the Wrap fixture's own list — for EVERY wrap block the conformance
fixture carries (shifts are per-index constants), and the fixture list is non-empty, so the
`all` is not vacuous. -/
theorem the_shifts_are_the_wrap_fixtures :
    (Dregg2.Bridge.MinaMultiBlockConformance.WRAP_BLOCKS.map (fun b => b.shift)).all
        (fun s => s == SHIFTS_Q) = true
    ∧ Dregg2.Bridge.MinaMultiBlockConformance.WRAP_BLOCKS.isEmpty = false := by
  refine ⟨by decide, by decide⟩

set_option maxHeartbeats 1000000000 in
/-- The witnessed inverse inverts the block's own C5 denominator — the check the AIR performs
in-trace (`den·DINV = 1`), performed here on the fixture. -/
theorem the_witnessed_inverse_inverts :
    ((Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA - ((OM3_C : Nat) : Fq))
        * (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA - 1)) * env0Real vDINV = 1 := by
  decide

/-! ## §2 — ⚑⚑ THE DIFFERENTIAL: the program reproduces upstream's two numbers. -/

set_option maxHeartbeats 1000000000 in
/-- ⚑⚑ **THE PROGRAM'S ξ-FOLD IS THE BLOCK'S `combined_inner_product`** — 301 ops, ft_eval0
recomputed in the middle from the same wire, landing on `proof.oracles(…)`'s own number. -/
theorem the_program_reproduces_the_blocks_cip :
    progEval env0Real cipResultV = Dregg2.Circuit.Emit.MinaRealBlockGate.CIP := by
  decide

set_option maxHeartbeats 1000000000 in
/-- ⚑⚑ **THE PROGRAM'S PERMUTATION SCALAR IS o1-labs' OWN `perm_scalars` VALUE** — conjunct 4's
number, reached through the shared σ-factor chain. -/
theorem the_program_reproduces_perm_scalars :
    progEval env0Real permResultV
      = ((Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR : Nat) : Fq) := by
  decide

set_option maxHeartbeats 1000000000 in
/-- The reference composition (the AIR file's §5 `cipRef`/`permRef`) meets the same two numbers
at the same point — program and reference tied through the block. -/
theorem the_reference_meets_the_same_numbers :
    cipRef env0Real ((OMEGA_Q : Nat) : Fq) = Dregg2.Circuit.Emit.MinaRealBlockGate.CIP
    ∧ permRef env0Real ((OMEGA_Q : Nat) : Fq)
        = ((Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR : Nat) : Fq) := by
  refine ⟨by decide, by decide⟩

/-! ## §3 — the discriminations: each equality above can go red. -/

set_option maxHeartbeats 1000000000 in
/-- One bumped eval column moves the cip — the ξ-fold genuinely reads the wire. -/
theorem a_bumped_eval_moves_the_cip :
    progEval (bump env0Real (vEZ 5) 1) cipResultV
      ≠ Dregg2.Circuit.Emit.MinaRealBlockGate.CIP := by
  decide

set_option maxHeartbeats 1000000000 in
/-- ⚑ A bumped `LCT` moves the cip — the port's affine reach, the Lean half of the Rust
`lct-shift` exhibit: the SAME family that ACCEPTS when the claim moves with it. -/
theorem a_bumped_lct_moves_the_cip :
    progEval (bump env0Real vLCT 1) cipResultV
      ≠ Dregg2.Circuit.Emit.MinaRealBlockGate.CIP := by
  decide

set_option maxHeartbeats 1000000000 in
/-- A bumped σ eval moves the perm — conjunct 4 genuinely reads the permutation columns. -/
theorem a_bumped_sigma_moves_the_perm :
    progEval (bump env0Real (sCol 2) 1) permResultV
      ≠ ((Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR : Nat) : Fq) := by
  decide

#assert_axioms the_domain_generator_is_derived_and_the_fixtures
#assert_axioms the_zk_roots_are_the_generators_powers
#assert_axioms the_shifts_are_the_wrap_fixtures
#assert_axioms the_witnessed_inverse_inverts
#assert_axioms the_program_reproduces_the_blocks_cip
#assert_axioms the_program_reproduces_perm_scalars
#assert_axioms the_reference_meets_the_same_numbers
#assert_axioms a_bumped_eval_moves_the_cip
#assert_axioms a_bumped_lct_moves_the_cip
#assert_axioms a_bumped_sigma_moves_the_perm

end Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld
