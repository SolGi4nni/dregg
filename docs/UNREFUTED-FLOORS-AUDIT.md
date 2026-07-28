# The 8 unrefuted floors, read adversarially

**2026-07-27.** Against `docs/artifacts/floor-census-v2-2026-07-26/floor-census-v2.tsv`
(`#floor_census` at `e0160d116`: 35 candidate floors, 27 refuted, **8 unrefuted**, 1925
carriers). Two sibling lanes are deleting `CollisionResistant` and `Poseidon2SpongeCR`; this
audit stayed off both.

The question is not "are these refuted yet". It is `feedback-prove-the-floor-false`'s three-way
test: a floor must be **SATISFIABLE** (else every consumer is vacuously true), **REFUTABLE**
(else it asserts nothing), and **NOT PROVABLE** (else it is a tautology wearing an assumption's
clothes). "Unrefuted" answers one third of that, and only in the weak sense of "nobody wrote the
theorem yet".

---

## THE HEADLINE

**Of the 8, exactly ONE is a cryptographic hardness assumption.**

| | count | |
|---|---|---|
| already refuted before this audit began | 1 | `Hash4NoCollision` — census stale by ~21h |
| **refuted by this audit** | **1** | `Hash4Injective` — tooth landed, `34854bf62` |
| **provable, therefore not a floor at all** | **1** | `SplitUniqueAt` — it is a theorem in its own file |
| survive as honest hypotheses | **5** | |
| …of which are **cryptographic** | **1** | `WideBindingCR` |
| …structural program invariants | 2 | `StrandForkFree`, `Lace.Canonical` |
| …an encoding lemma, dischargeable | 1 | `Injective3` |
| …a cross-scheme binding obligation | 1 | `CrossSchemeSameOpening` |

So the honest reading of "what the tree rests on after the cleanup" is not eight assumptions.
It is **one hash assumption, two data-structure invariants, one serialization fact, one named
crypto obligation, and three things that were never floors.** That is better news than eight
would have been — a smaller assumption base — and worse news about the instrument, which
could not distinguish any of those five categories from one another.

---

## ⚑ THE INSTRUMENT FINDINGS, FIRST

These matter more than any individual verdict, because they say the 27/8 split is softer than
it reads.

### 1. The census does not measure the carrier exposure of an unrefuted floor. At all.

`FloorCensus.lean:452` — `let floors : NameSet := refutedBy.fold …`. Pass 1 classifies carriers
**only for floors that are already refuted**. Every one of the 8 therefore reads **`carriers=0`**
in the TSV, and that zero means "not measured", not "nothing depends on it".

Measured by hand for this audit (hypothesis-position binders):

| floor | carriers | modules | census says |
|---|---|---|---|
| `Blocklace.Lace.Canonical` | **8** | 5 | 0 |
| `StrandIntegrity.StrandForkFree` | 4 | 1 | 0 |
| `ShieldedWideValueLinkDescriptor.WideBindingCR` | 3 | 1 | 0 |
| `AttestedFactsRootModel.Hash4Injective` | 2 → **0** (ported) | 1 | 0 |
| `XmVrfRefinement.Injective3` | 2 | 1 | 0 |
| `ShieldedWideJoinPin.CrossSchemeSameOpening` | 1 | 1 | 0 |
| `Segmentation.SplitUniqueAt` | 0 | — | 0 |

`Lace.Canonical` is the widest-reaching floor in the whole unrefuted set — consensus safety,
CRDT convergence, checkpoint recovery and catchup all take it — and it has never been counted.

### 2. There is no PROVABLE arm. A theorem and an assumption report identically.

Pass 0b asks one question: does the environment hold a `¬ F` theorem. It never asks whether the
tree holds an `F` theorem. `SplitUniqueAt` is **proved four lines below its own definition**
(`Segmentation.lean:94`) and is reported as "UNREFUTED" — the same word the census gives
`WideBindingCR`. The doctrine's three-way test cannot be run by the instrument that is supposed
to police it.

Cheap fix, offered not landed: a Pass 0c that looks for a theorem whose conclusion IS `F …` with
no `F` in any binder, and emits `FLOOR name PROVABLE witness`. It is the mirror image of Pass 0b
and reuses its telescope walk.

### 3. Pass 0b only matches a top-level `¬`. A conjoined refutation is invisible.

`StrandIntegrity.lean:333` proves

```lean
theorem forked_strand_not_forkFree :
    forkedLace = insertOverwrite k0b [k0a] ∧ ¬ StrandForkFree forkedLace 9
```

That is an in-tree refutation at a chosen instance — the same standard by which
`MacaroonDischarge.BindingHashCR` is recorded `refuted … instance`. Pass 0b runs `notArg? body`
on the telescope body, which here is an `And`, so it sees nothing. **`StrandForkFree` is
refuted in the tree and the census calls it unrefuted.** One conjunct of laundering, entirely
accidental, and it means the 27/8 boundary is a lower bound on refutedness.

### 4. The ratchet PUNISHES writing the refutability pole of an honest floor.

`#floor_ratchet` derives its refuted set from `¬ F`-conclusion theorems. So for a floor that is
honest — satisfiable, refutable, not provable — writing down the refutability half of the
doctrine's own test reclassifies it as refuted and gates **every consumer** as a vacuous carrier.
The author's reward for completing the required check is a red root and a baseline entry.

This is a plausible mechanical explanation for why 5 of the 8 had no refutability witness. It
also shaped this audit: the `CrossSchemeSameOpening` refutability pole was landed as a statement
about a concrete weak pair of schemes rather than as `¬ CrossSchemeSameOpening …`, deliberately
(`ae37dd523`).

The instrument needs a way to say **refutable-in-principle** distinctly from **false at deployed
parameters**. Today it has one word for both, and the word triggers a gate.

### 5. The load-bearing assumption can be an ANONYMOUS hypothesis, and nothing counts those.

Pass 0 discovers candidates by δ-matching **`Prop`-valued `def`s**. An injectivity hypothesis
written inline in a binder, with no name, is not a candidate — and if it is not spelled
`Function.Injective` it is not in the 527 `SHAPE` sites or the 628 ungated inline sites either.
It is in **no count in the tree**.

The specimen is `LaceMerge.sameView_of_canonical_eq_ids:213`:

```lean
    (hagree : ∀ b₁ ∈ B₁, ∀ b₂ ∈ B₂, b₁.id = b₂.id → b₁ = b₂)
```

This is CROSS-lace canonicity — two blocks from *different replicas* sharing a content-address
must be equal — and it is strictly stronger than, and independent of, the two named
`Lace.Canonical` hypotheses beside it (those constrain each list internally and say nothing
about B₁ vs B₂). It is exactly the point where a hash collision breaks CRDT convergence. It has
no name, no model, no refutation, no census record, and it is threaded into
`merge_convergence_to_state`, the end-to-end convergence theorem.

**The named floor beside it is the weak one; the load-bearing one is anonymous.** Naming
`hagree` — as, say, `Lace.CrossCanonical` — would cost one `def` and would put the real
assumption on the instrument's radar.

### 6. Found in passing: `merge_convergence_tauOrder` is `P → P`.

`LaceMerge.lean:279`. Hypothesis `hOrder : tauOrder B₁ participants wavelength = tauOrder B₂ …`;
conclusion, verbatim, the same equation; proof `exact hOrder`. The `Canonical` hypotheses feed a
`have _hview` that is discarded at an underscore. It is a tautology with four decorative
hypotheses, sitting in the convergence section under the name "consensus-side convergence". The
file's own §6 prose is honest that `hOrder` is an unrediscovered residual — but the theorem is
not the residual being *named*, it is the residual being *restated as its own conclusion*.
`merge_convergence_to_state` immediately below is real; this one is not.

---

## THE EIGHT, ONE BY ONE

### 1. `Emit.AttestedFactsRootModel.Hash4Injective` — **FALSE. Tooth landed.**

`AttestedFactsRootModel.lean:53`. Four field elements in, one out, and the result must determine
all four:

```lean
def Hash4Injective {F : Type} (hash4 : F → F → F → F → F) : Prop :=
  ∀ a b c d a' b' c' d' : F, hash4 a b c d = hash4 a' b' c' d' →
    a = a' ∧ b = b' ∧ c = c' ∧ d = d'
```

Fix the last two arguments and the floor hands you an injection `F × F ↪ F`, forcing
`|F|² ≤ |F|`, forcing `|F| ≤ 1`. False at **every** finite carrier with more than one element,
the deployed BabyBear field included. Its docstring called it "the honest collision-resistance
floor the whole system already stands on". Both consumers were vacuous at deployed parameters.

The tell was on the page the whole time: the non-vacuity witness `hash4Injective_is_satisfiable`
inhabited the floor at `FTree`, a **free inductive type** — infinite. A satisfiability witness
that has to leave the deployed parameter regime to find a model is reporting the refutation.

**Landed** (`34854bf62`): `hash4Injective_false_of_finite` (parametric in the carrier),
`hash4Injective_false_babyBear` (at `Fin 2013265921`, so the deployed claim is literal),
`hash4Injective_false_bool` (pinning that `1 < |F|` is the entire hypothesis). Ported to the
per-instance residual `Coll4` — a collision at the exact two quadruples the two-level peel
compares — with both poles proved and `coll4_breaks_hash4Injective` recording that the deleted
floor implied every residual, so the port is a visible weakening. Added
`attested_member_is_committed_or_collides`: bind, or exhibit the collision, floor-free.
`hash4Injective_is_satisfiable` deleted in favour of the floor-free `ftreeNode_injective`.

Carriers after the port: **0.** `metatheory/scripts/ratchet_probe_attested.lean` calls the gate's own
`FloorRatchet.antiFloor` and confirms the tooth adds zero gated carriers.

⚠ **Needs one line in `metatheory/Dregg2.lean`** (not edited here — the main loop roots it),
next to line 1481:

```lean
import Dregg2.Circuit.Emit.AttestedFactsRootRegrounded -- the tooth: Hash4Injective is 4-to-1 compression asked to be injective, refuted at every finite carrier.
```

Until that line exists the tooth arms the gate against nobody.

### 2. `Emit.AutomataflRevealRefine.Hash4NoCollision` — **ALREADY REFUTED. Census is stale.**

Refuted at `c6b6c8393` (2026-07-27 23:04), ~21 hours after the census ran, by
`hash4NoCollision_false_babyBear`, and its consumers ported to `RevealColl`. Not touched here.
Recorded because it means **the "8 unrefuted" figure was already 7 before this audit started**,
and any planning doc quoting 8 is quoting a superseded measurement.

### 3. `Crypto.Segmentation.SplitUniqueAt` — **PROVABLE. Not a floor.**

`Segmentation.lean:90`, and four lines later:

```lean
theorem split_unique_generic_packaged (c : α) : SplitUniqueAt c := split_unique_generic c
```

It is a theorem, for every `α` and every `c`. Zero assumption content; a consumer that took it
as a hypothesis would gain nothing. The file is entirely honest about this — it says the `def`
exists so "the instance identity reads as one equation", i.e. it is a named *shape*, not an
assumption — and the two Handlebars uniqueness lemmas derive from `split_unique_generic`
directly, so nothing takes it in hypothesis position anyway.

**Nothing breaks and nothing frees**, because nothing assumed it. The finding is entirely about
the instrument: a `Prop` `def` that matches an injectivity shape is reported as a candidate
floor whether or not the tree proves it, and the census has no arm that would notice. It should
be reclassified out of the candidate set, not refuted.

### 4. `Distributed.StrandIntegrity.StrandForkFree` — **HONEST, and not a crypto floor.**

`StrandIntegrity.lean:128` — "`p`'s feed holds at most one block per sequence". A structural
invariant on a data structure, not a hardness assumption. All three arms are already **on disk**:

* SATISFIABLE — `honest_strand_forkFree:312`, on a concrete clean lace.
* REFUTABLE — `forked_strand_not_forkFree:333`, on the concretely forked one (invisible to the
  census, see instrument finding 3).
* NOT PROVABLE — immediately, from the refutation.

And the part that actually matters for an invariant, which the census does not ask about:
**is it discharged on reachable states?** Yes — `insert_preserves_forkFree:256` proves the fixed
write path preserves it, and `forkFree_of_honestChain:219` derives it from the honest-chain
discipline. This is the healthiest object of the eight.

**It is the wrong kind of thing for the census to be scoring.** For a crypto floor, "refutable"
is a wound. For an invariant, "refutable" is the whole point — it is what distinguishes a good
state from a forked one — and the real audit is the discharge, which no instrument here runs.

Exposure: 4 carriers, all in one file, all fine.

### 5. `Authority.Blocklace.Lace.Canonical` — **HONEST, and the highest-exposure unrefuted floor.**

`Blocklace.lean:84` — `∀ a ∈ B, ∀ b ∈ B, a.id = b.id → a = b`. Same class as `StrandForkFree`: a
structural distinctness invariant, honest by all three arms (satisfiable — discharged at
`Blocklace.lean:270` for `cdtToLace`; refutable — two distinct blocks at one id; not provable).
The docstring is careful and correct that it is "an explicit structural hypothesis (NOT a crypto
axiom)".

**8 carriers across 5 modules**, none measured:
`Blocklace.lookup_of_mem:90` · `StrandIntegrity.forkFree_of_honestChain:218` ·
`LaceMerge:214, :282, :299` · `CheckpointPrune:370` · `CatchupConverges:173, :195`.
It reaches consensus safety, CRDT convergence, checkpoint recovery and catchup.

Two residuals, both above: the anonymous `hagree` (finding 5) is the assumption actually doing
the cryptographic work at the convergence site, and `merge_convergence_tauOrder` (finding 6) is
`P → P`. Neither is a defect in `Lace.Canonical` itself, which survives the attack.

### 6. `Emit.ShieldedWideValueLinkDescriptor.WideBindingCR` — **HONEST. The one real crypto floor.**

`ShieldedWideValueLinkDescriptor.lean:317`. Injectivity of the 8-lane squeeze **restricted to
canonical openings**: eight 16-bit limbs plus a canonical BabyBear randomness, ~2^159 domain
against a ~2^248 range. This is the only member of the eight that was designed against the
attack that kills the others, and it survives it:

* Not pigeonhole-refutable — the counting goes the right way, and the file says so with the
  numbers.
* **Model on disk** — `wideBindingCR_satisfiable:732` exhibits `packPerm` at width 8. The
  witness lives at deployed shape, not at an escape hatch like `FTree`.
* Refutable — `permOut := fun _ => []` breaks it immediately; hence not provable.
* The 1-felt counterpart is *unconditionally refuted* right beside it
  (`narrow_binding_collision_exists`), which is what makes the widening a real gain rather than
  a restatement.

**Standard assumption it corresponds to:** wide-output collision resistance of Poseidon2
restricted to the honest encoding domain. On the honest ladder it sits at rung 2 —
`HashCRHardQuant F Eff`-shaped, with the adversary class still informal. Rung 3
(`RomQueryFloor.birthday_bound`, PROVED) is what turns it into a number: 8 lanes reads
~2^123.5, against ~2^15.5 for the one-felt version. That climb is the remaining work, and it is
a re-grounding, not a repair.

Exposure: 3 carriers, one file. Verdict: **keep it, and make it the template.** It is the only
place in the tree where both required moves — restrict the domain to the canonical encoding
*and* widen the codomain — are worked end to end.

### 7. `Crypto.XmVrfRefinement.Injective3` — **HONEST in shape, but an ENCODING lemma.**

`XmVrfRefinement.lean:84`. Generic 3-ary injectivity, used only at
`X.frameLeaf : Epoch → Output → Rand → Pre` — a length-framed **serialization into a pre-image
type**, not a compression into a digest. So no pigeonhole: the codomain is a byte string, and
`0x01 ‖ t ‖ y ‖ r` with fixed-width fields really is injective.

Not provable *generically* (take `D := Unit`), so it passes the three-way test as a shape. But
that is the wrong frame: **it is not a hardness assumption, it is a fact about a concrete
encoder**, and it is provable the moment `frameLeaf` is concrete —
`goodX_frameLeaf_inj:349` proves exactly that for the toy. What is undischarged is the *deployed*
encoder's instance, and that is engineering, not cryptography.

Mitigating, and worth noting: both carriers (`leaf_collision_breaks_hashcr:183`,
`distinct_outputs_break_hashcr:252`) conclude `¬ HashCR X.cr`. They are **reductions**, not
soundness claims. If `Injective3` were somehow false the damage would be a vacuous *tooth*, not
a laundered guarantee — the least dangerous possible position for an undischarged hypothesis.

Recommendation: discharge it at the deployed framing rather than carry it. No tooth is warranted.

### 8. `Circuit.ShieldedWideJoinPin.CrossSchemeSameOpening` — **HONEST. Model was missing; landed.**

`ShieldedWideJoinPin.lean:234`. "Agreement on both scheme commitments forces one opening" — the
named obligation for keeping Ristretto-Pedersen and Poseidon `node8` as two schemes. `Wide` is
`Opening → ℤ` with `Opening` an unbounded `(value, asset)` record, so no counting argument
applies; the file's §7 is right that discharging it "is a real argument … NOT free".

**The gap was vacuity.** It had a consumer (`cross_scheme_join_needs_argument:246`) and *no
exhibited model anywhere in the tree*. An obligation nobody has inhabited is indistinguishable
from a vacuity bomb.

**Landed** (`ae37dd523`) — both poles:

* `crossScheme_satisfiable` — value-projection on the ring side, asset-projection on the wide
  side. Deliberately a **jointly** binding pair: neither scheme is injective alone (each discards
  a whole field) yet agreement on both pins the opening. That is the two-scheme story the
  obligation is about, so the witness demonstrates the claim rather than dodging it with an
  injective stand-in.
* `crossScheme_fails_on_weak_schemes` — the demo squeeze on both sides accepts a value-distinct
  pair, so the obligation genuinely constrains the schemes.

Satisfiable and refutable ⟹ not provable. **It survives, and it is now checkable.** It remains an
honest crypto obligation and not a hardness assumption in the standard-model sense: it is
discharged by a sigma protocol / equality-of-committed-value proof, or dissolved by Fix A
(one shared witness) or Fix B (one faithful binding).

---

## WHAT I DID NOT DO

* **`lake build Dregg2` — the real gate — could not adjudicate any of this.** It was run and
  failed on **11 targets, none of them mine**: `FriLdtExtractDeployed`, `OodColumnLayout`,
  `DslBackingAttack`, five `*BindingFromFold` modules, `Emit.MinaStateQuery`,
  `Games.DungeonCompleteness`. The cause is the sibling `Poseidon2SpongeCR` deletion mid-flight
  (`Unknown constant OodCommitmentBinding.commitmentOpening_binds_of_poseidon2CR`,
  `Unknown identifier merkleRecomputeZ`). So `#floor_ratchet` never ran. Every module touched
  here elaborates green individually (`lake env lean`, EXIT=0, all `#assert_axioms` passing),
  and `metatheory/scripts/ratchet_probe_attested.lean` puts the gating question to the gate's own
  `antiFloor` predicate — but that is a strictly weaker claim than a green root and is not a
  substitute for one.
* **No tooth for `StrandForkFree`.** It is already refuted in-tree; restating the refutation
  with a bare `¬` conclusion so the census could see it would flip a healthy invariant into the
  ratchet's refuted set and gate its four honest carriers. That is a degradation, not a repair.
  The right fix is instrument-side (Pass 0b should look inside conjunctions, and the census
  should distinguish invariants from hardness assumptions), not tree-side.
* **`hagree` not named.** Turning it into `Lace.CrossCanonical` touches
  `sameView_of_canonical_eq_ids`, `merge_convergence_tauOrder` and `merge_convergence_to_state`,
  and belongs with the `merge_convergence_tauOrder` repair rather than bolted onto a floor audit.
  It is the single highest-value follow-up here.

## FOLLOW-UPS, IN PRIORITY ORDER

1. **Root the tooth** — the one-line import above. Without it, `34854bf62` arms nothing.
2. **Name `hagree`** and delete or repair `merge_convergence_tauOrder`. The tree's CRDT
   convergence currently rests on an anonymous collision-resistance hypothesis, and its
   consensus-side headline is a tautology.
3. **Census Pass 0c (PROVABLE arm)** and **Pass 0b through conjunctions**. Both are small, both
   are mirror images of code that already exists, and together they would have found two of
   this audit's eight verdicts mechanically.
4. **Split the census's floor kinds** — hardness assumption vs structural invariant vs encoding
   lemma. Three of the eight are not hash floors and scoring them on the same axis produced
   three misleading "UNREFUTED" rows.
5. **Climb `WideBindingCR` to rung 3.** It is the only member ready for it, and the payoff is a
   number (~2^123.5) instead of an assumption.

## CORRECTION TO A SIBLING DOCUMENT

`docs/INJECTIVITY-FLOOR-CLASS.md` §1.2 tabulates "the 8 UNREFUTED candidates" but the table is
not the census's 8. It adds `Market.Fxc4ConsequenceBinding.Node8CROnFxc4`,
`Market.WideCarrierSameOpening.SpongeCROnCarrier` and `Crypto.HomomorphicDigest.SumInjective`
(none of which is among the census's unrefuted 8) and lumps four of the real members into a
single row. `SumInjective` in particular is listed "legitimately unrefuted"; the census records
it **refuted**, by `HomomorphicDigestPositioned.demo_zeroVals_not_sumInjective:181`. Its
substantive claims about the members it shares with this audit hold up — `Hash4Injective` FALSE,
`WideBindingCR` the model member — and its §1 replacement-ladder analysis is the reason this
audit did not reach for `CollisionResistant` as a repair.
