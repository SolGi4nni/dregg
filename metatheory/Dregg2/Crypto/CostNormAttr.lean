/-
# `Dregg2.Crypto.CostNormAttr` — the `cost_norm` simp-set declaration.

A `register_simp_attr` set cannot be USED in the file that declares it (Lean restriction),
so the `cost_norm` attribute lives here on its own and is consumed by
`Dregg2.Crypto.CostTactics` (the `cost_simp` normal-form tactic) one import away.

`cost_norm` collects the lemmas that REDUCE `cost sz prog` / `stepCost sz prog` /
`(cost sz prog).intr` / `.qry` / `.total` to a concrete arithmetic expression, driven by the
`FreeOracle` program syntax. It is a SEPARATE set from the global `@[simp]` set: adding a lemma
here does not perturb ordinary `simp`, and `cost_simp` runs `simp only [cost_norm, …]`, so the
normal form is a reduction of the program, never an assertion. Future cost lemmas join the set by
being tagged `@[cost_norm]`, which is what makes the replication cheap.
-/
import Lean

/-- The cost normal-form simp set consumed by `cost_simp` — reduces `cost`/`stepCost`/`.intr`/
`.qry`/`.total` over the `FreeOracle` program syntax to a concrete arithmetic expression. -/
register_simp_attr cost_norm
