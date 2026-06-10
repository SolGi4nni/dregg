/-
# Dregg2.Exec.CoordinatedCaveat — promoting `DriftTier.coordinated` from fail-closed to a real discharge.

`Confluence.DriftStable` classifies a state-reading caveat by its drift-stability `DriftTier`. The
non-coordinated tiers carry a REAL drift-stability witness, so the executor can skip coordination:
`tieredCaveat_driftStable` (`DriftStable.lean:257`) fires for any `tier ≠ .coordinated`, consuming the
carried `IConfluent`/`IConfluentUnder` proof. The `.coordinated` tier (`DriftStable.lean:226`) is the
non-monotone, no-rep case: its `DriftWitness` is `PUnit` (`DriftStable.lean:240`) — *no*
drift-stability proof exists, "the executor MUST take the equalizer." Until now that instruction had
no executable target: `FullForestAuth.GatedCaveat.holds` simply returns `false` on `.coordinated`
(`FullForestAuth.lean:235`), an intra-cell *fail-closed* gate — correct as far as it goes (a caveat
that reads another cell cannot be discharged within a single-cell node) but a dead branch
with no positive discharge path.

This module supplies the missing target. The equalizer the `.coordinated` tier is told to take is
ALREADY PROVED: it is `Exec.CrossCaveat.jointApplyCaveated` + `crossCaveat_sound` (`CrossCaveat.lean:98`)
+ `caveated_check_eq_use` (the no-TOCTOU lemma, `:77`) + `crossCaveat_rejects` (the teeth, `:120`).
A coordinated caveat reads BOTH cells `(A, B)` — its very type (`KernelState → KernelState → Bool`)
forces the turn to be the bilateral (joint) turn over `{A, B}` (the type-level factoring, `CrossCaveat.lean:27`).
So the coordinated discharge is the atomic-snapshot equalizer per use: the cross-cell caveat is read
on the SAME atomic snapshot the bilateral turn commits against — time-of-check and time-of-use are one
indivisible observation, no window for a concurrent turn to invalidate `φ`.

What is proved here (the wiring + the bridge):
  * `coordinated_discharge_sound`   — the promotion is SOUND (CG-5 conservation ∧ CG-2 single-id ∧ `φ`),
                                       reusing `crossCaveat_sound`.
  * `coordinated_no_toctou`         — check-state = use-state = the identical atomic snapshot `(A, B)`,
                                       reusing `caveated_check_eq_use`. The property the `.coordinated`
                                       tier was promised (`DriftStable.lean:10`) but never wired.
  * `coordinated_refines_failclosed`— the promotion is a CONSERVATIVE refinement: whenever the covenant
                                       is violated the discharge STILL fail-closes (it never opened a
                                       hole), reusing `crossCaveat_rejects`. The old `false` behavior is
                                       exactly the `φ = false` case.
  * `coordinated_tier_discharges_via_equalizer` — THE BRIDGE (the new content): the coordinated tier,
                                       which carries NO drift-stability witness (`DriftWitness .coordinated
                                       = PUnit`), is instead made sound by the atomic equalizer. Connects
                                       `DriftStable`'s classification (`tieredCaveat_driftStable` REQUIRES
                                       `tier ≠ .coordinated`) to `CrossCaveat`'s executable discharge
                                       (what to DO when `tier = .coordinated`).

TEETH (proved as a theorem, not just `#eval`): `overbroad_discharge_rejected` — an over-broad coordinated
discharge whose `φ` is violated by `B`'s state is rejected EVEN THOUGH the raw bilateral turn would
commit, reusing the proved `CrossCaveat.covenant_rejects_high` (`CrossCaveat.lean:150`).

The §8 posture is inherited unchanged from `CrossCaveat`/`JointCell`: no crypto is faked, no
drift-stability is faked. The `.coordinated` tier carries `PUnit` (no proof); soundness comes
NOT from a fabricated drift-stability fact but from the atomic-snapshot equalizer — exactly the
single-machine principle (`CrossCaveat.lean:43`): forming the joint turn over `{A, B}` is free on one
machine, so the equalizer is cheap AND sound; the distributed partition-blocking variant is an
explicitly-flagged OPEN (Q-C2), NOT built here.

Pure executable Lean, `#eval`-able; builds only on `Exec.CrossCaveat` and `Confluence.DriftStable`
(no new primitives) — every keystone is a 1–2 line reuse of an already-green, `#assert_axioms`-pinned
`CrossCaveat` lemma; the new content is the wiring and the bridge.
-/
import Dregg2.Tactics
import Dregg2.Exec.CrossCaveat
import Dregg2.Confluence.DriftStable

namespace Dregg2.Exec.CoordinatedCaveat

-- The headline structure shares its name with this namespace (the established repo idiom for a
-- self-named carrier, cf. `Intent/Core.lean:36`). Silence the cosmetic dup-namespace lint.
set_option linter.dupNamespace false

open Dregg2.Exec Dregg2.Exec.JointCell Dregg2.Exec.CrossCaveat Dregg2.Confluence.DriftStable

/-! ## §1. The coordinated caveat — a cross-cell `φ` whose tier is FORCED `.coordinated`.

A coordinated caveat carries a `CrossCaveat` `φ` (reads BOTH cells, `CrossCaveat.lean:62`) and pins its
`DriftTier` to `.coordinated` — the tier whose `DriftWitness` is `PUnit` (`DriftStable.lean:240`), i.e.
the non-monotone, no-rep case for which NO drift-stability proof exists. The `tier` field is
carried as DATA so the executor's verify-not-find dispatch (`DriftStable.lean:213`) can read the tag and
route to the equalizer, exactly as the non-coordinated tiers route to `tieredCaveat_driftStable`. -/

/-- A **coordinated caveat** — the cross-cell `φ` the `.coordinated` tier is told to discharge via the
atomic equalizer. `φ` reads BOTH cells `(A, B)`, so its type alone forces the turn to be the bilateral
(joint) turn over `{A, B}` (the type-level factoring, `CrossCaveat.lean:27`). The `tier` is carried (and
asserted `.coordinated` by `tier_is_coordinated`) for the executor's dispatch. -/
structure CoordinatedCaveat where
  /-- The cross-cell caveat — a predicate on the JOINT pre-state `(A, B)` (`CrossCaveat.lean:62`). -/
  φ    : CrossCaveat
  /-- The drift tier, carried as data for verify-not-find dispatch. Forced `.coordinated` (see
  `tier_is_coordinated`): this is precisely the tier whose `DriftWitness` is `PUnit`. -/
  tier : DriftTier := .coordinated
  /-- The tier is `.coordinated` — this caveat is the no-drift-stability-witness case that MUST take
  the equalizer (`DriftStable.lean:226`/`:240`). Carried so the structure cannot be mis-tagged. -/
  tier_is_coordinated : tier = .coordinated := by rfl

/-- **The PROMOTED discharge.** Instead of fail-closing (`FullForestAuth.lean:235` returns `false` on
`.coordinated`), route the coordinated caveat onto the proved atomic-snapshot equalizer
`jointApplyCaveated` (`CrossCaveat.lean:68`). This is the executor's "take the equalizer per use"
(`DriftStable.lean:226`) made concrete: fail-closed UNLESS the cross-cell `φ` holds on the SAME atomic
pre-state `(A, B)` from which the bilateral turn commits. -/
def dischargeCoordinated (c : CoordinatedCaveat) (A B : KernelState) (bt : BiTurn) :
    Option (KernelState × KernelState) :=
  jointApplyCaveated c.φ A B bt        -- REUSE the proved atomic-snapshot gate

/-! ## §2. The keystones — each a 1–2 line reuse of a proved `CrossCaveat` lemma.

The mathematical content is already green and `#assert_axioms`-pinned in `CrossCaveat.lean`; the new
content of this module is the WIRING (showing the dead `.coordinated` tier is exactly the domain of the
proved equalizer) and the BRIDGE theorem (§3). -/

/-- **KEYSTONE 1 — `coordinated_discharge_sound`: the promotion is SOUND with no TOCTOU.**
GIVEN the CG-2 shared-id binding (carried as a HYPOTHESIS, never derived — exactly as
`crossCaveat_sound`/`joint_sound_of_binding` require), a discharged coordinated caveat held on EXACTLY
the atomic commit snapshot, AND conserves the joint total (CG-5), AND is bound to one shared id (CG-2).
The `.coordinated` tier is live (`FullForestAuth.lean:235`): it discharges
through the proved equalizer, soundly. Direct reuse of `crossCaveat_sound`. -/
theorem coordinated_discharge_sound (c : CoordinatedCaveat) {A B A' B' : KernelState} {bt : BiTurn}
    (bind : SharedBinding bt)
    (h : dischargeCoordinated c A B bt = some (A', B')) :
    jointTotal A' B' = jointTotal A B ∧ bind.sidOfA = bind.sidOfB ∧ c.φ A B = true :=
  crossCaveat_sound bind h

/-- **KEYSTONE 2 — `coordinated_no_toctou`: NO TOCTOU, stated for the coordinated tier.**
The cross-cell caveat held on EXACTLY the pre-state `(A, B)` from which the underlying atomic
`jointApply` committed — the time-of-check state and the time-of-use state are the IDENTICAL atomic
snapshot, indivisibly. This is the property the `DriftStable` docstring (`:10`) promised the
`.coordinated` tier ("the commit-instant (TOCTOU) window is already handled by the equalizer") but
never wired to the tier. Direct reuse of `caveated_check_eq_use`. -/
theorem coordinated_no_toctou (c : CoordinatedCaveat) {A B A' B' : KernelState} {bt : BiTurn}
    (h : dischargeCoordinated c A B bt = some (A', B')) :
    c.φ A B = true ∧ jointApply A B bt = some (A', B') :=
  caveated_check_eq_use h

/-- **KEYSTONE 2′ — `coordinated_no_toctou_atomic`: the check and BOTH half-commits are one step
.** Sharper form of no-TOCTOU exposing the per-half atomicity (Q-C3, free — one more reuse): a
discharged coordinated caveat held on `(A, B)` AND both half-edges committed in their own ledgers from
that same `(A, B)`. So the caveat-check and the two-sided commit are atomic over one snapshot — the
executable face of "no concurrent turn can invalidate `φ` between check and use." Direct reuse of
`crossCaveat_atomic`. -/
theorem coordinated_no_toctou_atomic (c : CoordinatedCaveat) {A B A' B' : KernelState} {bt : BiTurn}
    (h : dischargeCoordinated c A B bt = some (A', B')) :
    c.φ A B = true ∧ applyHalfOut A bt = some A' ∧ applyHalfIn B bt = some B' :=
  crossCaveat_atomic h

/-- **KEYSTONE 3 — `coordinated_refines_failclosed`: the promotion is a CONSERVATIVE refinement
.** Whenever the cross-cell covenant is violated (`φ = false`), the discharge STILL fail-closes
— it never opened a hole. So the OLD behavior (`FullForestAuth.lean:235` rejecting every `.coordinated`
caveat) is recovered exactly as the `φ = false` case: the promotion can only ADD admissions where `φ`
holds on the atomic snapshot, never remove the fail-closed guarantee. Direct reuse of
`crossCaveat_rejects`. -/
theorem coordinated_refines_failclosed (c : CoordinatedCaveat) {A B : KernelState} {bt : BiTurn}
    (hφ : c.φ A B = false) : dischargeCoordinated c A B bt = none :=
  crossCaveat_rejects hφ

/-! ## §3. THE BRIDGE — connecting the dead `.coordinated` tier to the executable equalizer.

This is the new content. `tieredCaveat_driftStable` (`DriftStable.lean:257`) discharges every
tier EXCEPT `.coordinated` (it requires `hne : tc.tier ≠ .coordinated`, and the `coordinated` branch is
`absurd htier hne`). The reason is `DriftWitness .coordinated = PUnit` (`DriftStable.lean:240`): there is
no drift-stability proof to consume. THIS module supplies what to do WHEN `tier = .coordinated` — not a
fabricated drift-stability fact, but the atomic equalizer. The bridge makes the connection explicit and
checked: the coordinated caveat's tier IS `.coordinated`, its `DriftWitness` IS the empty `PUnit`, and
yet a discharge is sound — because soundness rides on the equalizer, not on drift-stability. -/

/-- **KEYSTONE 4 (THE BRIDGE) — `coordinated_tier_discharges_via_equalizer`.** A coordinated
caveat is precisely a caveat whose tier is `.coordinated` and whose `DriftWitness` is therefore the
empty `PUnit` (no drift-stability proof) — yet a committed discharge is sound: `φ` held on the committed
atomic snapshot AND the joint total is conserved (CG-5). This is the missing complement to
`tieredCaveat_driftStable` (`DriftStable.lean:257`), which can ONLY fire for `tier ≠ .coordinated`. The
conjunction's first two components witness the bridge premise (the tier really is the
no-drift-witness one); the last two are the equalizer's soundness. So: where the drift-stability
classifier hands off (`tier = .coordinated`, `DriftWitness = PUnit`), the equalizer takes over — the
`.coordinated` tier is live. Reuses `coordinated_discharge_sound`/`caveated_check_eq_use`. -/
theorem coordinated_tier_discharges_via_equalizer (c : CoordinatedCaveat)
    {A B A' B' : KernelState} {bt : BiTurn} (bind : SharedBinding bt)
    (h : dischargeCoordinated c A B bt = some (A', B')) :
    -- the bridge premise (this IS the no-drift-witness tier) …
    (c.tier = .coordinated ∧ DriftWitness (S := VersionCell) lockEnv lockEnv .coordinated = PUnit) ∧
    -- … and yet it is made sound by the atomic equalizer:
    (c.φ A B = true ∧ jointTotal A' B' = jointTotal A B) := by
  refine ⟨⟨c.tier_is_coordinated, rfl⟩, ?_⟩
  obtain ⟨hcg5, _, hφ⟩ := coordinated_discharge_sound c bind h
  exact ⟨hφ, hcg5⟩

/-! ## §4. TEETH — the coordinated discharge REJECTS an over-broad case.

Non-vacuity: the discharge is not a `fun _ _ => True` overlay. We reuse the proved `CrossCaveat` demo
verbatim. The covenant *"cell 0 in ledger `A` must hold at least cell 7's balance in ledger `B`"* (which
READS `B`) is violated when `B` holds more (`sBhigh`: cell 7 = 200 > A's cell 0 = 100); the coordinated
discharge rejects EVEN THOUGH the raw bilateral turn `jointApply sA sBhigh goodBi` would commit. This is
the literal "over-broad discharge rejected" tooth: an attempt to discharge a coordinated caveat against a
state that violates it is fail-closed, not silently passed. -/

/-- The over-broad coordinated caveat: the `CrossCaveat.covenant` (`CrossCaveat.lean:134`) wrapped as a
`.coordinated` tiered caveat. It reads `B` and gates on it — it cannot be evaluated on `A` alone. -/
def covenantCoord : CoordinatedCaveat := { φ := covenant }

/-- **`overbroad_discharge_rejected` — THE TEETH.** When `B`'s state violates the covenant
(`sBhigh`: cell 7 = 200 > cell 0 = 100), the coordinated discharge is rejected — a theorem, not just an
`#eval`. The over-broad coordinated caveat does NOT pass: the cross-cell read gates, and the
discharge fail-closes exactly where the equalizer's `φ` is false. Reuses the proved
`CrossCaveat.covenant_rejects_high` (`CrossCaveat.lean:150`). -/
theorem overbroad_discharge_rejected :
    dischargeCoordinated covenantCoord sA sBhigh goodBi = none :=
  covenant_rejects_high

/-! ### §4a. `#eval` non-vacuity demos — the coordinated discharge is load-bearing, not a no-op.

Mirrors `CrossCaveat.lean:140-145`: the SAME coordinated caveat admits when the covenant holds and
rejects when `B` violates it, while the RAW bilateral turn commits regardless — proving the coordinated
discharge (not the underlying turn) is what gates. -/

#guard decide ((covenantCoord.tier) = DriftTier.coordinated)  --  DriftTier.coordinated (the promoted tier)
#guard (decide (covenantCoord.tier = DriftTier.coordinated))  --  true  (it IS the no-drift-witness tier)
#guard ((dischargeCoordinated covenantCoord sA sB goodBi).isSome)  --  true  (covenant holds ⇒ ADMITS via equalizer)
#guard ((dischargeCoordinated covenantCoord sA sBhigh goodBi).isSome) == false  --  false (covenant violated by B ⇒ REJECT)
#guard ((jointApply sA sBhigh goodBi).isSome)  --  true  (RAW turn fine; only the coordinated caveat rejects)
#guard ((dischargeCoordinated covenantCoord sA sB goodBi).map (fun p => jointTotal p.1 p.2)) == some 125  --  some 125 (CG-5 conserved on the admitted discharge)

/-! ## §5. Axiom-hygiene tripwires — pin each coordinated-discharge keystone kernel-clean.

Each pin elaborates to an error if the keystone depends on any axiom outside
`{propext, Classical.choice, Quot.sound}` (notably `sorryAx`). The reuse posture means these inherit
`CrossCaveat`'s already-pinned hygiene. -/

#assert_axioms coordinated_discharge_sound
#assert_axioms coordinated_no_toctou
#assert_axioms coordinated_no_toctou_atomic
#assert_axioms coordinated_refines_failclosed
#assert_axioms coordinated_tier_discharges_via_equalizer
#assert_axioms overbroad_discharge_rejected

end Dregg2.Exec.CoordinatedCaveat
