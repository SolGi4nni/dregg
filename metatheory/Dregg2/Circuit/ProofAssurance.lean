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
* `FriLdtExtractDeployed` — where the wound was proved:
  `friLdtExtractV3_makes_verifyBatch_reject_everything`. The landed extraction bundle, at the deployed
  args, forces `verifyBatch` to reject **every** input.
* `ApexOodLaneRepair`, `OodSingletonRepair`, `FriFsDecodedOodRepair`, `StarkSoundFriLdtCorrected` — the
  corrected cons-shape bundles and the non-vacuous apex.

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
import Dregg2.Circuit.FriLdtExtractDeployed
import Dregg2.Circuit.ApexOodLaneRepair
import Dregg2.Circuit.OodSingletonRepair
import Dregg2.Circuit.FriFsDecodedOodRepair
import Dregg2.Circuit.StarkSoundFriLdtCorrected
