# The apex premise was empty — a proved vacuity, its repair, and the instrument

**Date:** 2026-07-24 (status updated 2026-07-25). **Status:** wound PROVED; bare-premise cutover
COMPLETE; the `FriLdtExtractV3` block and the apex itself **still open**. Read the Status update before
relying on any figure in the original text — its census was wrong.

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

1. ~~**Nothing was migrated.**~~ **SUPERSEDED 2026-07-25 — see the Status update below.** As written on
   07-24 this was true and is left visible rather than deleted, because the *reasoning* still applies to
   the block that remains. What changed: the **bare-premise cutover is complete** (zero soundness
   consumers left on `FriLdtExtract`; `algoStarkSound_of_memoryLegs_cons` now has callers), and the
   census figure quoted here — "roughly 35" — was itself wrong, conflating prose with code. What has
   *not* changed: **8 consumers still ride the sibling proven-empty `FriLdtExtractV3`**, including the
   named apex, so for that bundle the honest status remains *"wound proved and a correct replacement
   path built"*, not *"wound repaired"*.
2. **The corrected bundles have no exhibited model anywhere.** An adversarial verifier wrote its own
   falsifier and showed that a conjunct the repair **retains** — `topen ∈ proof.tableOpenings` — is
   *refutable at the very accepting pole used as the witness run*, because that pole has
   `tableOpenings = []`. So the residual is not merely unwitnessed but **refutable at the toy pole**:
   the same disease, one conjunct over.
3. **Toy-parameter results wearing "deployed" labels.** Several were name overreach and are called out
   as such in the modules.
4. What the repairs buy, exactly: **the premise no longer *forces* universal rejection.** Satisfiability
   at the opaque `cfg*` args remains unproven and is labelled, not claimed.

## Status update (2026-07-25)

**The census in this doc was wrong and is corrected.** "~35 consumers" conflated prose with code. The
real figure: **392 occurrences across 35 files**; by *binder position*, bare `FriLdtExtract` 8 — **all
vacuity-subjects**, not consumers — `Cons` 47, `V3` 14 (8 genuine consumers), `V3Cons/Faithful` 7.

- **The bare-premise cutover is COMPLETE** (`756efedb01`, `fb741c815f`): zero soundness consumers remain
  on it, verified by grepping binder positions. It also turned up an **orphan fan-out**
  (`AlgoStarkSoundFanoutSetField`) this doc never listed.
- **The subtle find, worth generalizing:** `decodedLdtLink_of_friLdtExtract` was the *only* entry into
  `DecodedLdtLink`, and composing the corrected implication downstream would **not** have repaired it —
  *composing after an empty premise leaves the entry empty*. That is precisely why a cutover is not the
  same as adding a corrected variant beside the old one.
- **Non-emptiness reached a form sharper than this doc's bar**: `..._noOodShape` derives the conclusion
  from a premise **mentioning no OOD conjunct at all**. A premise cannot be emptied by a conjunct it does
  not contain.
- **The instrument has been RUN** — `Dregg2/Circuit/PremiseInhabitabilitySweep.lean`, 37 theorems,
  R1–R18, enumeration *mechanical* (39 structural candidates + 13 more found by grepping
  `extractable : Prop`). This discharges the old "run the instrument over the remaining classes" item.
  Settled: `StarkComplete` **collapses** with the landed bundle; `GroundedApex.BindingExtract` is
  **free** (zero information); `AccumulatorSound` is **negative at deployment** — correcting an earlier
  pass that had read it as an abstract class, because *a verdict about an abstract class is not a
  verdict about its instantiation*.
- **The `tableOpenings` falsifier is answered at the pole**:
  `at_the_only_exhibited_pole_the_repair_is_half_realized` reads **both halves off the same run**, so the
  repair's outstanding debt is exactly **one conjunct**, not diffuse.

### ⚑ A wound class this doc did not know about — R11

Thirteen soundness classes gate extraction on a **self-chosen `extractable : Prop`**, and **all eight**
in-tree reference instances set it to `True`. The family's own non-vacuity witnesses pass the carrier
half *by writing `True`*. Two **independent** vacuity modes are proved:

- a legal kernel that **accepts every triple** with `extractable := False` — the gated soundness shape
  then holds for *arbitrary* conclusion, i.e. true and unappliable. **`PremiseInhabitability`
  structurally cannot see this mode**, because it is not about acceptance at all;
- a true carrier over a verifier that rejects everything (the mode the instrument *does* see).

Checking either alone is not a check; the criterion is `CarrierLive`. `PortalFloor` is this same tree
doing it correctly — carrier proved at a reference instance, refuted at a forge instance — so this is a
**default that spread**, not an unavoidable design.

## Next

- The **8 `FriLdtExtractV3` consumers**, including the named apex `starkSound_of_friLdtExtract_transferV3`.
  Corrected targets are on disk and `StarkSoundFriLdtCorrected` still has no callers. *(dispatched)*
- **R11**: replace `extractable := True` with real carriers, following `PortalFloor`. *(dispatched)*
- **~28 declarations remain `UNKNOWN` at deployment**, concentrated in the abstract-verifier families —
  for the structural reason that the tree never instantiates them at a deployed verifier. Every
  `UNKNOWN` is an unsettled entry, **not** a pass.
- Standing ceiling: **nothing proves any bundle satisfiable at the opaque `cfg*` args, and nothing can.**
