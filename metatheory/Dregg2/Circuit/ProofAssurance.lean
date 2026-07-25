/-
# `Dregg2.Circuit.ProofAssurance` — aggregator root for the premise-vacuity work.

This module exists so the proof-assurance subtree is reachable from `Dregg2.lean` through a **single**
import line. `Dregg2.lean` is a hot shared file with many concurrent lanes; every one of these modules
was rooted individually at some point and every one of those lines was **dropped by a contending
commit**, leaving the whole subtree outside the default `lake build` target — i.e. outside CI, free to
rot, and not covered by any "full build green" claim. One line has a far smaller conflict surface than
seven, and this is the second time the lesson has been paid for (see
`Dregg2/Circuit/CorrelatedAgreement.lean`).

## What this subtree is for

A proof can be kernel-clean, `sorry`-free, and non-vacuous *in its own terms* and still say **nothing**,
because its **premise is empty**. `#assert_axioms` is **structurally blind** to that: it checks what a
proof *rests on*, and cannot see that nothing satisfies its hypotheses. The apex vacuity found here was
kernel-clean, sorry-free, and true.

* `PremiseInhabitability` — **the instrument**. `Empties P acc := P → RejectsAll acc`, `Extracts` (the
  accepts-implies-exists shape every soundness class has), `empties_of_refuted`,
  `empties_proves_anything`, `not_of_empties_of_acceptsSome`, `empties_mono`. Turns an audit note into a
  theorem.
* `PremiseInhabitabilitySweep` — the instrument **run** across the tree's accepts-implies-exists surface
  (R1–R18). Enumeration was mechanical, not impressionistic: a structural scan returned 39 candidates
  and a second grep on `extractable : Prop` found 13 more the filter missed.
* `PremiseInhabitabilitySweepSettled` — the sweep's `UNKNOWN` rows worked down, and a **THIRD vacuity
  mode** found: the first two live on the ANTECEDENT, this one on the **CONCLUSION**. A total conclusion
  makes a gated theorem free with carrier *and* acceptance deleted, while `CarrierLive` reports green,
  axioms are clean and no `sorry` exists (`carrierLive_does_not_exclude_mode3`). Concretely
  `nonmembership_verify_sound` is a **tautology at every instantiation** — its conclusion
  `∃ leaves, NonMember leaves stmt.elem` is discharged by `leaves := []` and never mentions
  `stmt.root`, so no deployment can repair it. And the polarity INVERTS on the reference Merkle kernel:
  the *forge* kernel's collapsing hash gives a conclusion that bites while the *reference* one does not
  — the instance cited as the family's reassurance is the one saying nothing.
* `FriLdtExtractDeployed` — where the wound was proved:
  `friLdtExtractV3_makes_verifyBatch_reject_everything`. The landed extraction bundle, at the deployed
  args, forces `verifyBatch` to reject **every** input.
* `ApexOodLaneRepair`, `OodSingletonRepair`, `FriFsDecodedOodRepair`, `StarkSoundFriLdtCorrected` — the
  corrected cons-shape bundles and the non-vacuous apex.
* `ExtChallengeOodSites`, `ExtChallengeLogUpSite` — the remaining base-field-challenge sites retyped to
  the quartic extension. Same asymmetry proved each time (base lifts, extension does not descend, and
  the base equation *cannot express* the deployed value) with the same payoff shape: the extension-typed
  hypothesis still forces the identical base-field conclusion — weaker-but-achievable, same conclusion.
  Two sharpenings worth knowing: `OodSoundnessGame`'s BabyBear instance prices a **different object**, so
  citing it for the deployed ε would be laundering — though it is *conservative*, never too small; and
  the LogUp wound is not `F`'s type (already generic) but the **read** — one ℤ from one public column
  cannot produce four lanes, and `atMostOne_basis_mem_range` makes that obstruction basis-independent.
* `Crypto.CarrierContent` — the repair of the sweep's R11 finding: the `CarrierAudit` tooth (a record
  no `True` carrier can inhabit, because it demands a REFUTATION of the same carrier shape at a
  broken sibling oracle) plus nine audits, one per reference kernel of the carrier-gated family.
  Their carriers are now PROVED theorems over their own oracles instead of `extractable := True`.
  This closes the *self-witnessing* hole, NOT the deployment question: R11 stays UNKNOWN.
  (It was briefly de-rooted while it did not compile: the `accepts` witnesses were written `by decide`,
  which cannot synthesize `Decidable (ofBool …)` because `ofBool` is an opaque `def` — the goal is
  `f i = true` only up to unfolding. `rfl`, which is what `PremiseInhabitabilitySweep`'s own
  `referenceMerkleKernel_accepts_a_run` uses for the identical goal shape, discharges it.)

## The repair obligation (why these modules carry so many `_adds_no_strength` theorems)

A corrected bundle can be **exactly as empty** as the broken one, and it *looks* fixed — which is worse.
So every repair here discharges one of:

* the **bar**: the corrected conjuncts are *implied by acceptance*, hence add exactly zero strength
  (`friLdtExtractCons_iff_noOodShape`); or
* **sharper**: the conclusion follows from a premise *mentioning no OOD conjunct at all*
  (`algoStarkSound_memFree_apply_noOodShape`) — a premise cannot be emptied by a conjunct it does not
  contain.

Each repair also leaves a **receipt** that what it replaced forced `verifyBatch = reject` on every
triple, and retains the broken shape as a vacuity tooth's subject so it cannot be reintroduced silently.

## Honest ceiling for the whole subtree

**Nothing here proves any bundle *satisfiable* at the deployed `cfg*` args — and nothing can**, because
those are `opaque`. Every `UNKNOWN` in the sweep is an unsettled entry, **not** a pass. The corrected
bundles retain `topen ∈ proof.tableOpenings`, which is refutable at the only exhibited accepting pole
(`tableOpenings = []`), so the cutover traded a premise empty *everywhere* for one whose emptiness is
*conditional and undecided* — an improvement, not a closure. And that pole is `Nat`-typed while the
premises are `ℤ`-typed: what is refuted is the **schema**, not the deployed instance.
-/
import Dregg2.Circuit.PremiseInhabitability
import Dregg2.Circuit.PremiseInhabitabilitySweep
import Dregg2.Circuit.PremiseInhabitabilitySweepSettled
import Dregg2.Circuit.PremiseInhabitabilityConclusionAxis
import Dregg2.Circuit.FriLdtExtractDeployed
import Dregg2.Circuit.ApexOodLaneRepair
import Dregg2.Circuit.OodSingletonRepair
import Dregg2.Circuit.FriFsDecodedOodRepair
import Dregg2.Circuit.StarkSoundFriLdtCorrected
import Dregg2.Circuit.ExtChallengeOodSites
import Dregg2.Circuit.ExtChallengeLogUpSite
import Dregg2.Circuit.ExtOpeningRecordWidth
import Dregg2.Crypto.CarrierContent
