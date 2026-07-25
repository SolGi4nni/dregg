<!-- ⚑ This repo runs MULTIPLE concurrent /goal sessions — see GOALS-INDEX.md.
     This file is the **proof-assurance** lane trail. Edit only this one. -->

> ⚑ **Multiple goals are live — see [`GOALS-INDEX.md`](GOALS-INDEX.md).** This is the
> **proof-assurance** lane. Adjacent by design: `honest-verification` (carrier debt) and
> `greens-that-mean-something` (vacuous theorems). Coordinate, don't collide.

# GOAL — PROOF ASSURANCE: make the arguments SENSIBLE, not just green

**Standing goal:** grind down proof engineering / assurance / argument-sensibility / refactor /
replacement. Set 2026-07-25, run to 11am.

## The thesis
A proof can be kernel-clean, `sorry`-free, non-vacuous *in its own terms*, and still say nothing —
because its **premise is empty**, its **antecedent is the wrong object**, its **reach doesn't cover
the regime it's quoted for**, or its **types model a different system than the deployed one**. This
lane hunts and heals that class.

Governing rule: *a carrier vacuous at deployed parameters is a **sin**, not a hypothesis to carry.*
Cutovers, not parallel towers.

## The wound classes (calibrated from real finds, not theory)
1. **Empty premises.** PROVED: the landed extraction bundle forces `verifyBatch` to reject *every*
   input, so the apex quantified over an empty accepting set and was vacuously true.
   `#assert_axioms` is **structurally blind** to this — the vacuous apex was kernel-clean and true.
2. **Wrong-object antecedents.** `FriLdtExtractV3` was assumed over a verifier the tree *itself*
   proves is foolable, while the deployed apex uses a stronger one.
3. **Vacuous named residuals.** `TranscriptWordCommitment` is literally `Classical.em` pointwise.
4. **Field-typing infidelity.** Deployed quartic-extension challenges modelled as base felts —
   *not* a restriction (lane-0 projection isn't multiplicative), a **different equation**.
5. **Reach ≠ truth.** Theorems true, clean, non-vacuous — and not covering the regime cited.
6. **Out-of-CI proof.** A seven-file subtree outside the build target; committed imports pointing
   at untracked files (has broken a fresh checkout **three times** today).

## The instrument
`Dregg2/Circuit/PremiseInhabitability.lean` — `Empties P acc := P → RejectsAll acc`, `Extracts`,
`empties_of_refuted`, `empties_proves_anything`, `not_of_empties_of_acceptsSome`. Turns "audit note"
into "theorem". **Repair obligation:** every fix must prove the corrected conjuncts are *implied by
acceptance* (hence add zero strength) — a repair that swaps one vacuity for another is worse than
none, because it looks fixed.

## In flight (background agents)
- `cut:memfree-fanout` — migrate ~25 `hfri : FriLdtExtract` consumers to the cons-shape assembler
- `cut:memory-and-kernel` — memory fanout + kernel/config, **and the true census** (35 is an estimate)
- `instrument-sweep` — `PremiseInhabitability` across every accepts-implies-exists class; `UNKNOWN`
  is a first-class verdict, not a pass

## Next moves (my pick)
0. ~~Cut over the bare-premise consumers~~ **DONE** — zero soundness consumers remain on it.
1. **De-honest the fold chain** — every survival theorem instantiates `Strategy := honestStrategy`,
   so the tree's deepest probabilistic object bounds the *honest* prover. Generalize to `∀ S` under
   a path-local fold-consistency predicate. Highest value on the adversary axis.
2. **Give `TranscriptWordCommitment` content.**
3. **Kill the duplication debt** — `hitWin`/`hit_cond`/`hit_bound` exist twice.
4. Then: the ~11 remaining base-field-challenge typing sites.

## Done log
- L0–L6 correlated-agreement ladder landed; crux `polishchuk_spielman` PROVEN (Cramér–Nardi-fixed).
  No Mathlib gap blocked it — the `resultant` API carried it, refuting the plan's own fragility §.
- `DecimLift` discharged from the landed tower; `RlcDistributes` discharged at deployed params.
- Apex premise vacuity **PROVED**; repair pattern + `PremiseInhabitability` instrument built.
- `docs/WOUND-apex-premise-vacuity-2026-07-24.md` — wound proved, replacement path built.
- **CENSUS corrected**: 392 occurrences / 35 files, not the doc's "~35 consumers" (prose conflated with
  code). By binder position: bare `FriLdtExtract` 8 — *all vacuity-subjects*; `Cons` 47 migrated;
  `V3` 14 with 8 genuine consumers still empty; `V3Cons/Faithful` 7 migrated.
- **Bare-premise cutover COMPLETE** (`756efedb01`, `fb741c815f`) — zero soundness consumers left on it,
  verified by grepping binder positions myself. Found + migrated an **orphan fan-out**
  (`AlgoStarkSoundFanoutSetField`) the campaign inventory never listed.
- **The subtle find**: `decodedLdtLink_of_friLdtExtract` was the ONLY entry into `DecodedLdtLink`, and
  composing `_imp_cons` downstream would NOT have repaired it — *composing after an empty premise leaves
  the entry empty*. Deleted; cons-shaped entry written. This is why a cutover ≠ adding a variant beside.
- **Non-emptiness went past the bar**: `..._noOodShape` derives the conclusion from a premise mentioning
  no OOD conjunct *at all* — a premise cannot be emptied by a conjunct it does not contain.
- **Caveat promoted to theorem, not inherited quietly**: an accepting run with `tableOpenings = []`
  refutes the corrected premise. So the cutover trades a premise empty *everywhere* for one whose
  emptiness is *conditional and undecided* at the opaque `cfg*` args — an improvement, **not a closure**.
  And the exhibited pole is `Nat`-typed while the premises are `ℤ`-typed: what is refuted is the
  **schema**, not the deployed instance.
