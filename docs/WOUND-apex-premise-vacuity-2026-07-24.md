# The apex premise was empty — a proved vacuity, its repair, and the instrument

**Date:** 2026-07-24. **Status:** wound PROVED; correct replacement path built; **apex NOT closed**.

## The finding, stated plainly

`Dregg2/Circuit/FriLdtExtractDeployed.friLdtExtractV3_makes_verifyBatch_reject_everything`

> The **landed** extraction bundle `FriLdtExtractV3`, at the deployed `cfg*` args, forces
> `CircuitSoundness.verifyBatch` to **reject every input**.

So `StarkSoundFriLdt.starkSound_of_friLdtExtract_transferV3` — and every apex theorem conditioned on
that bundle — quantified over an **empty accepting set** and was **vacuously true**. This is
machine-checked, not an audit note.

### The mechanism: the field-typing wound in terminal form

The bundle concluded `oodPoint = [ood]` — a **singleton** list holding one `BabyBear` felt — while the
deployed acceptance predicate forces **four lanes**:

- `ExtFieldChallenge.lean:753-768` — `verifyAlgoUnifiedFaithfulExt` carries `decide (params.extDeg = 4)`
- `FriChallengerUnified.lean:122` — `unifiedTranscriptChecks` opens with `decide (proof.oodPoint = d.ζ)`
- `FriVerifier.lean:139-146,581` — `d.ζ := Challenger.sampleExt … params.extDeg`, and `sampleN_length`
  gives `d.ζ.length = extDeg = 4`

Accept ⟹ length 4. Bundle ⟹ length 1. Contradiction.

**A single base felt standing in for a 4-lane `Challenge` does not merely model the deployed system
unfaithfully — at the apex it silently empties the premise.** That is the strongest reason yet to finish
the extension retyping: this is not a fidelity nicety, it is a soundness-statement killer.

## Why our existing gates could not see it

`#assert_axioms` is **structurally blind** to this class. The vacuous apex was kernel-clean, sorry-free,
and *true*. Axiom hygiene checks what a proof **rests on**; it cannot see that a premise is **empty**.
Nor can a `sorry` grep, a build, or CI. This wound class needs its own instrument.

## The instrument — `Dregg2/Circuit/PremiseInhabitability.lean`

The pattern that caught the apex, made reusable so it is applied by default rather than by luck:

```lean
def RejectsAll (acc : Acc ι) : Prop := ∀ i, ¬ acc i
def AcceptsSome (acc : Acc ι) : Prop := ∃ i, acc i
def Empties (P : Prop) (acc : Acc ι) : Prop := P → RejectsAll acc
def Extracts (acc : Acc ι) (C : ∀ i, W i → Prop) : Prop := …  -- the accepts-implies-exists shape
```

with `empties_of_refuted` (the general tooth), `empties_proves_anything` (the vacuity consequence),
`not_of_empties_of_acceptsSome` (the refutation direction), and `empties_mono`. Any bundle can now be
**tested** against an acceptance predicate, and the outcome is a **theorem**, not a note.

## The repair pattern (and the obligation any repair must discharge)

1. Do **not** edit a landed definition in place if modules consume it — add a corrected variant and
   prove the relation.
2. **Prove the vacuity** where found, and **retain the broken shape** as that theorem's subject so it
   cannot be reintroduced silently (`FriLdtExtractV3FaithfulSingleton` exists for this).
3. The corrected shape is `ood :: oodRest` — what `batchTablesCheck` actually matches
   (`FriVerifier.lean:803-808`); it never required a singleton.
4. **⚑ Prove the repair introduces no NEW vacuity.** The gold standard is the
   `_iff_noOodShape` form: the corrected bundle is *equivalent to the bundle with those conjuncts
   deleted*, because **acceptance supplies them** — so the repair adds exactly **zero** strength and can
   never itself empty a premise. A repair without this is worthless: it may have swapped one vacuity for
   another, and it *looks* fixed, which is worse.

## Sites healed

| repair module | sites |
|---|---|
| `ApexOodLaneRepair` | `AlgoStarkSoundGeneral:147`, `DeployedRefinesProof:103`, `FriVerifierBridge:185` |
| `OodSingletonRepair` | `OodColumnLayout:229`, `OodExtChallengeLayout:617` |
| `FriFsDecodedOodRepair` | `FriVerifierFS:112`, `FriDecodedTraceWitness:464` |
| `StarkSoundFriLdtCorrected` | a non-vacuous apex to migrate to |

**Headline from the FRI/decoded lane:** `DecodedLdtLink` — the DEEP-ALI residual the entire L5/R4b
ladder terminates at — was **inert against the deployed verifier** for the same reason. Re-deriving
`positiveRadiusTraceDecode_decoded_cons` / `_transferV3_cons` shows the singleton was **load-bearing
nowhere**, so correcting it cost nothing.

## ⚑ Honest limits — the apex is NOT closed

Recorded because they were nearly lost when a concurrent commit swept the files in without this message.

1. **Nothing was migrated.** Roughly **35** `hfri : FriLdtExtract` hypotheses across
   `AlgoStarkSoundFanoutMemFree`, `AlgoStarkSoundFanoutMemory` and the kernel/config modules still ride
   the premise proved empty. `algoStarkSound_of_memoryLegs_cons` exists but **nothing calls it**. The
   honest status is *"wound proved and a correct replacement path built"*, **not** *"wound repaired"*.
2. **The corrected bundles have no exhibited model anywhere.** An adversarial verifier wrote its own
   falsifier and showed that a conjunct the repair **retains** — `topen ∈ proof.tableOpenings` — is
   *refutable at the very accepting pole used as the witness run*, because that pole has
   `tableOpenings = []`. So the residual is not merely unwitnessed but **refutable at the toy pole**:
   the same disease, one conjunct over.
3. **Toy-parameter results wearing "deployed" labels.** Several were name overreach and are called out
   as such in the modules.
4. What the repairs buy, exactly: **the premise no longer *forces* universal rejection.** Satisfiability
   at the opaque `cfg*` args remains unproven and is labelled, not claimed.

## Next

- Migrate the ~35 consumers to the corrected assembler; until then the deployed apex chain is
  byte-for-byte as vacuous as before.
- Run the instrument over the remaining soundness classes (`StarkComplete`, `AccumulatorSound`, …).
- The named next falsifier: **does the deployed predicate accept a run with `tableOpenings = []`?**
  Unprovable at opaque `cfg*`, but the ∀-instantiation form of every bundle in this family is already
  refuted at the pole.
