import Hygiene

/-!
# Hygiene.SelfTest — the assertions demonstrably CATCHING violations

`#print axioms` cannot fail a build, so the whole point of `Hygiene` is that its
assertions *do*. That claim needs evidence, and the evidence has to survive CI:
each negative case below is wrapped in `#guard_msgs`, which captures the
elaboration error and compares it against the pinned text. So this file is GREEN
exactly when every assertion still throws on the violation it is meant to catch —
if someone weakens `#assert_axioms` into a no-op, THIS FILE GOES RED.

Positive cases (assertions that must pass) are stated bare.
-/

namespace Drorb.Hygiene.SelfTest

/-! ## Fixtures -/

/-- Depends on `Classical.choice` (through `Classical.choose_spec`). -/
theorem usesChoice (p : Nat → Prop) (h : ∃ n, p n) : p (Classical.choose h) :=
  Classical.choose_spec h

/-- Depends on nothing: a definitional-unfolding fact. -/
theorem pureRfl (n : Nat) : n + 0 = n := rfl

/-- Content-free: `a = a`. -/
theorem vacuousEq (n : Nat) : n + 0 = n + 0 := rfl

/-- Content-free: function-hood restated. -/
theorem vacuousExists (n : Nat) : ∃ m, n + 0 = m := ⟨_, rfl⟩

/-- Content-free: `a ↔ a`. -/
theorem vacuousIff (n : Nat) : n = 0 ↔ n = 0 := Iff.rfl

/-- Closed by RUNNING COMPILED CODE. In Lean 4.30 this mints a per-declaration
axiom `…._native.native_decide.ax_1_1`, so the Lean compiler, the C toolchain and
the evaluator are in this theorem's trusted base — not the kernel alone. -/
theorem usesNativeDecide : (List.range 40).length = 40 := by native_decide

/-! ## Positive cases — these must PASS -/

#assert_axioms pureRfl ⊆ []
#assert_axioms usesChoice ⊆ [stdAxioms]
#assert_axioms_exact usesChoice = [Classical.choice]
#assert_axioms usesNativeDecide ⊆ [nativeDecide]
#assert_nonvacuous pureRfl

/-! ## Negative cases — these must FAIL, and the failure IS the test

A group name expands literally, so `⊆ []` is a genuine empty allowance: a proof
that touches `Classical.choice` cannot hide behind it. -/

/--
error: axiom-footprint violation: 'Drorb.Hygiene.SelfTest.usesChoice' depends on [Classical.choice], which the declared set does not allow.
  declared: []
  actual:   [Classical.choice]
-/
#guard_msgs (whitespace := lax) in
#assert_axioms usesChoice ⊆ []

/-! The `_exact` form additionally rejects an over-broad advertisement: claiming
the classical three when the proof is in fact axiom-free. -/

/--
error: axiom-footprint over-declaration: 'Drorb.Hygiene.SelfTest.pureRfl' does NOT depend on [propext, Classical.choice, Quot.sound], but the exact set claims it does.
  actual: []
-/
#guard_msgs (whitespace := lax) in
#assert_axioms_exact pureRfl = [stdAxioms]

/-! And a `native_decide` proof cannot pass itself off as kernel-checked: the
minted axiom is outside `stdAxioms`, so the assertion catches it. -/

/--
error: axiom-footprint violation: 'Drorb.Hygiene.SelfTest.usesNativeDecide' depends on [Drorb.Hygiene.SelfTest.usesNativeDecide._native.native_decide.ax_1_1], which the declared set does not allow.
  declared: [propext, Classical.choice, Quot.sound]
  actual:   [Drorb.Hygiene.SelfTest.usesNativeDecide._native.native_decide.ax_1_1]
-/
#guard_msgs (whitespace := lax) in
#assert_axioms usesNativeDecide ⊆ [stdAxioms]

/-! Vacuity: the three content-free shapes, each rejected by name. -/

/--
error: vacuous statement: 'Drorb.Hygiene.SelfTest.vacuousEq' - conclusion is `a = a` (reflexivity - holds for every function). A theorem of this shape holds for EVERY definition of the same arity, so the name advertises a property the statement does not carry. Prove the real property or delete it.
-/
#guard_msgs (whitespace := lax) in
#assert_nonvacuous vacuousEq

/--
error: vacuous statement: 'Drorb.Hygiene.SelfTest.vacuousExists' - conclusion is `exists y, f .. = y` (function-hood restated - holds for every function). A theorem of this shape holds for EVERY definition of the same arity, so the name advertises a property the statement does not carry. Prove the real property or delete it.
-/
#guard_msgs (whitespace := lax) in
#assert_nonvacuous vacuousExists

/--
error: vacuous statement: 'Drorb.Hygiene.SelfTest.vacuousIff' - conclusion is `a <-> a`. A theorem of this shape holds for EVERY definition of the same arity, so the name advertises a property the statement does not carry. Prove the real property or delete it.
-/
#guard_msgs (whitespace := lax) in
#assert_nonvacuous vacuousIff

end Drorb.Hygiene.SelfTest
