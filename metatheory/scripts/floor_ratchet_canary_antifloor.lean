/-
# floor_ratchet_canary_antifloor.lean — THE B1/B2 TOOTH, CAUGHT IN THE ACT OF BITING.

`#floor_ratchet` exempts ANTI-floor content, because the campaign wants refutations WRITTEN and a
gate that made writing one a build error would be working against it. The shipped exemption tested
the CONCLUSION'S SHAPE: `¬ Floor …`, or `False`. That is not a refutation test, and both
adversarial probes walked through it carrying `Poseidon2SpongeCR` — a hypothesis this tree PROVES
FALSE at deployed BabyBear parameters. Measured on a HEAD-pinned green tree before the fix: EXIT=0,
`1600 grandfathered carriers`, unchanged.

  * **B1** — assume a refuted floor, conclude a negation of some OTHER floor. The conclusion is
    anti-floor content; the declaration is not.
  * **B2** — assume a refuted floor, conclude `False`. `False` is the most permissive conclusion in
    the language, so exempting on it exempts on nothing. 113 declarations in the tree were riding
    it, and they are not refutations: they are contrapositive SOUNDNESS claims
    (`consensus_safe_under_floor`, `lightclient_no_fork`, `downgrade_resistant_under_floor`, every
    `*_rejects_*`/`*_unsat` in the emit tree), each saying "the deployed system cannot be broken"
    under an assumption the tree refutes.

The rule now is: **refutes floor content and assumes none.** Conclusion `¬ F …` with no
floor-carrying hypothesis, or — uncurried, since `Γ → F → False` IS `Γ → ¬ F` — conclusion `False`
with the floor as the INNERMOST binder.

    cd metatheory && lake env lean scripts/floor_ratchet_canary_antifloor.lean

**EXPECTED: EXIT=1**, naming BOTH `b1_via_negation_exemption` and `b2_via_false_exemption`.
A ZERO exit means the exemption has gone back to being a conclusion-shape test.

⚑ The OTHER direction — an exemption that degenerates to gating everything, which would make the
campaign's own anti-floor work a build error — cannot be caught by a canary at all, because it
looks like a healthy red. `FloorRatchet.specimenVerdicts` catches it: five declaration TYPES with
fixed expected verdicts, two of them EXEMPT, asserted on every root build.

⚑ Nothing here touches a tracked file, so this is swarm-safe to run at any time, concurrently.
-/
import Dregg2

open Dregg2.Circuit.Poseidon2Binding

/-- **B1.** A refuted floor in HYPOTHESIS position, on a declaration that merely happens to
CONCLUDE a negation. The hypothesis is never used — it does not need to be; the point is that the
conclusion's shape bought the exemption. -/
theorem b1_via_negation_exemption {sponge : List ℤ → ℤ} (_hCR : Poseidon2SpongeCR sponge) :
    ¬ Poseidon2SpongeCR (fun _ : List ℤ => (0 : ℤ)) := by
  intro hbad
  exact List.cons_ne_nil (0 : ℤ) [] (hbad [] [0] rfl).symm

/-- **B2.** Conclusion `False`, with the refuted floor NOT the innermost binder — so what the
statement actually asserts is `¬ (0 = 1 ∧ …)`, i.e. a claim about the middle hypothesis, proved
under a hypothesis the tree refutes. This is the shape of `closure_rejects_overdebit_avail` and of
every other contrapositive soundness claim the old exemption laundered. -/
theorem b2_via_false_exemption {sponge : List ℤ → ℤ}
    (hCR : Poseidon2SpongeCR sponge) (hLive : sponge [1] = sponge [2]) : False :=
  absurd (hCR [1] [2] hLive) (by simp)

#floor_ratchet
