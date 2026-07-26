# VACUITY SWEEP — every named hypothesis carrier, five tests (2026-07-16)

Three named "honest residuals" in a row turned out vacuous or false, and **each one's header advertised
rigor**. That is a base-rate problem, not bad luck. This is the sweep.

**Verdict up front: the base rate is bad, but not uniformly bad, and it is bad in a *specific place*.**
The `∃`-shaped carriers came back nearly clean — the tree's existential carriers overwhelmingly pin their
witnesses, and several carry proved refutable poles. The rot is concentrated in **floors**: the `Prop`s that
stand for a cryptographic assumption. There, two *systemic* defects are proved below, and the second one is
worse than any of the three precedents, because it is not one carrier — it is a **family of five**, and its
consumers are the "re-grounded" keystones that were themselves the fix for an earlier vacuity.

Every verdict here is **proved in Lean**. Assertions do not count; that is why this sweep exists.

## New Lean, all `sorry`-free, `#assert_axioms`-clean, root `lake build Dregg2` green (9702 jobs)

| file | contents |
|---|---|
| `metatheory/Dregg2/Crypto/HardQuantVacuity.lean` | 11 teeth — the `*HardQuant` family finding |
| `metatheory/Dregg2/Circuit/VacuitySweepTeeth.lean` | 6 teeth — the injective-floor class + `MembersAt8` depth |

Both registered in the root `Dregg2.lean` import list with full annotations.

---

## ⚑⚑⚑ FINDING 1 — the `*HardQuant` floor family carries NO problem content (URGENT-adjacent; see scope)

**Carriers** (all in `metatheory/Dregg2/Crypto/ProbCrypto.lean`):

| carrier | file:line |
|---|---|
| `MSISHardQuant` | `ProbCrypto.lean:140` |
| `MLWEHardQuant` | `ProbCrypto.lean:143` |
| `DLHardQuant` | `ProbCrypto.lean:146` |
| `HashCRHardQuant` | `ProbCrypto.lean:149` |
| `DecisionMLWEHardQuant` | `ProbCrypto.lean:528` |

**Verdict: DOCSTRING-CONSTRAINT + FALSIFIER-CONFUSION.** All five are the same definition:

```lean
def MSISHardQuant {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)
```

Nothing in any of them mentions a lattice, a curve, a hash, `IsMSISSolution`, or a distinguishing game.
The problem lives **entirely in the name and the docstring**. `DecisionMLWEHardQuant`'s own doc says *"The
**intended** `adv` is a `DecisionFamily.adv`"* — **intended**, never enforced. That is precisely the
`CoCurvilinearity` defect (a constraint stated in prose is not a constraint), one level up: here the prose
is the whole problem statement.

### The five tests

1. **Prove it trivially?** Yes — `MSISHardQuant (fun _ => fun _ => 0)` is `negl_zero`. But the tree *knows*
   this and offers `guessAdv` instead, so triviality is not the interesting defect. → see test 4.
2. **Falsifier refutes statement or matrix?** **MATRIX.** `CryptoFloorTeeth.proper_floor_is_genuine` offers
   `⟨msisHardQuant_guess_holds, msisHardQuant_const_one_refuted⟩` as evidence the floor is "a GENUINE
   assumption — satisfiable AND refutable — not a theorem". Refuting `MSISHardQuant` **at `adv := const 1`**
   refutes the predicate *at a chosen argument*. It says nothing about whether any consumer carries content.
   **Proved:** `sheep_floor_passes_the_same_non_vacuity_test` — `SheepCountingHardQuant` (name chosen to mean
   nothing) passes that exact test, and `sheep_floor_is_msisHardQuant` proves it **is** `MSISHardQuant` by
   `Iff.rfl`. The test measures the *shape* of a predicate over an arbitrary `adv`; it cannot see whether a
   floor is *about* its named problem.
3. **Constraint in a docstring?** **Yes** — "the intended `adv`", "the MSIS solver the reduction extracts".
   The reduction is named in prose and absent from every statement.
4. **False as named?** **Proved: a DILEMMA, both horns from the tree's own lemmas** (`hardquant_dilemma`):
   - **Horn A — tie `adv` to MSIS and the floor is FALSE at deployed parameters.** The only `adv` in the tree
     genuinely indexed by MSIS solving is `FloorBridge.msisSolverAdv`, and the tree's own
     `msisHardQuant_solverAdv_iff_msisHard` proves `MSISHardQuant (msisSolverAdv A β) ↔ Lattice.MSISHard A β`
     — the Boolean floor verbatim, FALSE at compressing `A` by pigeonhole. On the honest instantiation every
     consumer is **vacuously true**. (`horn_A_msis_tied_floor_is_false_at_deployed_params`)
   - **Horn B — leave `adv` untied and the floor holds while MSIS is BROKEN.** `guessAdv = fun l => 1/2^l`,
     the tree's *own* non-vacuity witness, mentions no `A`, no `β`, no `IsMSISSolution`.
     `horn_B_floor_holds_while_msis_is_broken` proves `MSISHardQuant (fun _ : Unit => guessAdv)` holds
     **simultaneously with** `¬ MSISHard (augmented id 1) 0` — the floor is satisfied in a world where the
     problem it is named after is refuted. It constrains nothing about MSIS.

   There is no third instantiation in the tree. Either horn kills the MSIS content of every consumer.
5. **Do consumers get what they need?** **No — they get their own hypothesis back.** Every consumer has the
   shape `(adv) (s) (hfloor : <X>HardQuant adv) : Negl (adv s)`, whose hypothesis unfolds to
   `∀ s, Negl (adv s)` and whose conclusion is that hypothesis at `s`. It is `hfloor s` — a `P → P`
   instantiation.

   **The sharpest tooth** (`the_vrf_keystone_accepts_the_hash_floor`) does not restate a consumer — it
   **calls the real one**, passing a `HashCRHardQuant` proof into the argument
   `VrfRegrounded.lattice_vrf_uniqueness_advantage_bound` declares as `MSISHardQuant`. **It typechecks.**
   A theorem named "lattice VRF uniqueness" that proves equally well from the Poseidon2 collision floor is
   not about lattice VRF uniqueness.

**Consumers (statement-identical, all confirmed):** `VrfRegrounded.lattice_vrf_uniqueness_advantage_bound`,
`VrfRegrounded.lattice_vrf_uniqueness_with_guessing_bound`,
`ThreadAdvantageBound.forger_advantage_bound_under_msis`,
`ThreadAdvantageBound.forger_advantage_with_challenge_bound`,
`ThreadAdvantageBound.decision_distinguisher_advantage_bound`,
`ThreadAdvantageBound.lossy_id_advantage_bound`.

**⚑ HONEST SCOPE — what is NOT claimed.** **No downstream theorem is false.** They are all true. The finding
is that they are true *for a reason that has nothing to do with their names*, so they transport no hardness.
This is not a live exploit and nothing deployed becomes unsafe today; it is that the lattice/PQ column's
"quantitative re-grounding" currently banks bits it has not earned. Nor is the concrete-security *direction*
wrong — it is right, and the machinery (`Negl`, `winProb`, `Ensemble`) is real. The wiring stops one step
short.

**Why this matters more than the three precedents.** `Arity8FiberBound` had *zero consumers*.
`CoCurvilinearity` had two. This family is the **repair** that was applied when the Boolean floors
(`Lattice.MSISHard := ¬∃ z, IsMSISSolution`) were found vacuous — the fix for a vacuity, itself content-free.
`HashFloorHonesty`'s header says it best about its own predecessor: *"the pre-existing non-vacuity witnesses
give FALSE COMFORT"*. The same sentence applies here, to the successor.

**REPAIR — APPLIED 2026-07-16, and it did not go where this section said it would.**
`metatheory/Dregg2/Crypto/FloorGames.lean` (lake-green, `sorry`-free, 18 keystones `#assert_all_clean`).
The five floors are restated as the standard cryptographic games. The paragraph this replaces prescribed
*"the `CollisionResistant` treatment"*; the first thing the repair did was try to prove that floor false,
and **it succeeded** — see the sub-finding below. So the repair is the game shape, with the adversary class
as an explicit parameter, and the residual is named rather than dressed.

**What was built.** One schema, five problems. A `Game` carries a λ-indexed finite instance space, an
answer space, and a **win relation**; `Hard G Eff := ∀ A, Eff A → Negl (gameAdv G A)` where `gameAdv` is
`ProbCrypto.winProb` of the win event. The five floors are `Hard` at five different games:

| floor | `wins` is, definitionally | tooth |
|---|---|---|
| `MSISHardQuant F Eff` | `Lattice.IsMSISSolution (F.A l i) (F.β l) z` | `msisGame_wins_iff` (`Iff.rfl`) |
| `MLWEHardQuant F Eff` | `s = F.secret l i`, with `mlweFamily_isSample` proving every instance IS a `Lattice.IsMLWESample` | `mlweFamily_isSample` |
| `DLHardQuant F Eff` | `(F.C l).smul x (F.gen l) = F.chal l i` | — |
| `HashCRHardQuant F Eff` | `p.1 ≠ p.2 ∧ F.H l k p.1 = F.H l k p.2` | `hashGame_wins_iff` (`Iff.rfl`) |
| `DecisionMLWEHardQuant F Eff` | `|Pr[D(A·s+e)] − Pr[D(uniform)]|`, ONE `D` on both worlds | `distAdv_mem_unit` |

The old content-free predicates are KEPT, renamed `ProbCrypto.MSISHardQuantShape` &c. and doc-marked
BROKEN — §1–§4 of this finding are stated about them and must keep compiling. The rename is not cosmetic:
every consumer still riding the shape now says so in its own signature.

**⚑ THE GATE — the sweep's sharpest tooth, retired, and canaried.** `the_vrf_keystone_accepts_the_hash_floor`
(passing a `HashCRHardQuant` proof into `lattice_vrf_uniqueness_advantage_bound`'s `MSISHardQuant` slot)
**no longer elaborates**: the slot is `Hard (msisGame (vrfMsisFamily F)) Eff` and a hash floor is `Hard` at
a different game. `HardQuantVacuity` §6 pins the refusal permanently with `fail_if_success` (the tree's
negative-test idiom — there is no `#guard_msgs` anywhere in `Dregg2`), four horns: the hash floor, the
decisional floor, `SheepCountingHardQuant`, and `MSISHardQuantShape` itself. Plus the positive pole
(`the_repaired_keystone_fires_on_the_right_floor`) — a gate that refuses everything is a broken keystone,
not a fixed one. **Canaried:** feeding the gate the RIGHT floor makes `fail_if_success` fail, so the test
discriminates rather than always passing.

**⚑ SUB-FINDING — `HashFloorHonesty.CollisionResistant` IS FALSE AT DEPLOYED PARAMETERS.** The pattern this
section prescribed as *"the correct pattern already in the tree"* has the identical defect it was built to
cure. `collisionResistant_iff_hashCRHardQuant_top` proves `CollisionResistant F ↔ HashCRHardQuant F ⊤`, and
`collisionResistant_false_of_compressing` proves that FALSE whenever the family is compressing (a collision
at every key — the defining property of a hash, forced by pigeonhole). The `Classical.choice` finder that
outputs a collision at every key IS a `CollisionFinder`: that structure bounds nothing. `mod2Family_not_CR`
fires it on `HashFloorHonesty`'s **own** compressing example — the same file whose `mod2_dumb_negligible`
shows one DUMB finder has advantage `0`, which is true and says nothing about a `∀`-quantified floor. The
file's satisfiability witness `idFamily_CR` is the identity hash. **Toy witness satisfiable, real hash
false** — its own header's diagnosis of its own predecessor, for the third time in a row. Keying does not
fix it. This is why the lattice floors did not get "the `CollisionResistant` treatment".

**⚑ THE DILEMMA: NOT ESCAPED — GENERALIZED, then LOCALIZED. This is the load-bearing result.**
`hard_top_iff_solvableFrac_negl` proves, for **any game whatsoever**:

    Hard G (fun _ => True)  ↔  Negl (solvableFrac G)

At the unrestricted adversary class a game floor **IS** the probabilistic existence floor. So Horn A was
never about `msisSolverAdv` and never about the old shape — it is a theorem about **every**
unrestricted-adversary formulation, the repaired one included. §4's "there is no third instantiation **in
the current shape**" understates it: **no restatement of the win relation can escape, because the `↔` is an
`↔`.** `Classical.choice` is the adversary and the win relation cannot see it coming
(`msisHardQuant_top_false_of_compressing`; `mlweHardQuant_top_false` and `dlHardQuant_top_false`
unconditionally — the MLWE secret and the DL exponent are *fields of the family*).

**The escape is `Eff`, and only `Eff`** — the standard form's "for every EFFICIENT adversary". `Eff :=
Computable` does not restrict anything (`solvableIsAFiniteSearch`: every answer space is a `Fintype`, so
brute force is a total computable function — what disqualifies it is that the search is astronomically
large, and "large" is a statement about COST); Mathlib has no polynomial-time model over an arbitrary
carrier; stating one needs a deep embedding of the adversary (SSProve/EasyCrypt/FCF each carry one).
Inventing a shallow imitation would have been the fourth costume.

So `Eff` is a **parameter**, with both poles PROVED beside it — `⊤` makes every floor false at deployed
parameters, `⊥` makes it vacuous (`hard_bot_vacuous`) — so a reader can price any instantiation exactly.

**The cost-model residual, PARTIALLY DISCHARGED — query counting is in-tree.** For oracle/hash-shaped
floors the tree now states a genuine `Eff`: `Dregg2.Crypto.{RomOracle, RomCounting, RomQueryFloor}`
(imported with annotations at `metatheory/Dregg2.lean:705-707`) build a query-counting adversary class —
`OracleComp` decision trees with `QueryBounded Q` bounding the calls along every path, lazy sampling as
pure finite counting (no measure theory), and `romCollision_hard` proving the **unconditional** birthday
bound `(Q² + 1)/|R|`: a floor that is PROVED, not assumed. Both escapes are proved beside it — the class
is not `⊤` in disguise (the `Classical.choice` adversary is excluded) and not `⊥` (a genuine query-using
member is exhibited); `RomQueryDial` proves the budget is a load-bearing dial, not a costume. **Named
residual (narrowed): a general PPT cost model.** Query counting prices hash/oracle adversaries; it
constrains lattice adversaries not at all, so the gap between the lattice floors and cryptographic
assumptions remains that one object — now one object instead of five names and a docstring.

**What the repair buys, stated exactly** (it is not nothing, and it is not a floor):
1. the problem is IN the statement (`msisGame_wins_iff` unfolds `wins` to `IsMSISSolution` by `Iff.rfl`);
2. the five floors are pairwise non-interchangeable — at the TYPE level, pinned by the §6 gate;
3. consumers must EXHIBIT a reduction, not cite one;
4. the dilemma is localized to one named object with both poles proved.

**Consumers — 1 of 6 routed through a real reduction; the other 5 named honestly.**
`VrfRegrounded.lattice_vrf_uniqueness_advantage_bound` is re-grounded for real: `vrfUniqGame` makes the
uniqueness-breaker a first-class adversary, `uniqBreakToMsisSolver` IS the extractor
`(z₁ − z₂, −(y₁ − y₂))` as a function, `uniqBreak_reduces_to_msis` is
`VRF.lattice_vrf_uniqueness_reduces_to_msis` **applied** (win-preservation), and
`uniqBreak_adv_le_msis_adv` is the advantage inequality by `winProb_le_of_imp`. The reduction is the only
bridge between hypothesis and conclusion, and a canary in the file proves the keystone does NOT follow from
the floor alone — a tooth that was impossible to write before, when hypothesis and conclusion were the same
`Negl (adv s)`. Its one carried side condition, `hEff` ("the extracted solver is in the class"), is the
standard "the reduction is efficient", is undischarged, and is in the open at the use site.

The other four (`ThreadAdvantageBound.forger_advantage_bound_under_msis`,
`forger_advantage_with_challenge_bound`, `decision_distinguisher_advantage_bound`, `lossy_id_advantage_bound`)
plus `lattice_vrf_uniqueness_with_guessing_bound`'s shape-era twin **have no reduction in the tree** and are
NOT re-grounded. They are retained, TRUE, and doc-marked ⚠ with their obligations named:
  * the two forking legs have a REAL partial leg (`ProbCrypto.ForkingFamily.bound` is proved;
    `HermineTSUF.prob_forger_forkProb_yields_msis` genuinely extracts an `IsMSISSolution`) but nothing
    connects `forkProb` to the advantage of an adversary against an `MSISFamily`. **Undischarged
    obligation: `forkProb ≤ msisAdv (extracted solver)`.**
  * the two decisional legs have no reduction at all. **Undischarged obligation: the game hop.**

That is an honest undischarged obligation, not a costume — and it is the answer to "which consumers have
real reductions": one did, and the sweep said so.

---

## ⚑⚑ FINDING 2 — the injective-hash floor class is ~5× bigger than the four that were flagged

`HashFloorHonesty.lean` (2026-07) proved FOUR injectivity floors FALSE for any range-bounded hash —
`Poseidon2SpongeCR`, `compressNInjective`, `compressInjective`, `HashCR` — doc-marked them BROKEN, built the
proper keyed `CollisionResistant` replacement, and re-grounded their consumers
(`FloorRegroundedConsumers`, `Poseidon2KeyedBridge`, `HermineHashCRRegrounded`). Good work. **It did not
sweep the class.** A census of `metatheory/Dregg2` finds **~20 more carriers with the identical predicate
shape**, still doc-marked "REALIZABLE", none pointing at the teeth, and — verified by grep against every
honesty/re-grounding file — **none re-grounded**:

`Poseidon2WideCR` (Emit/EffectVmEmitRotationR:256) · `compress4Injective` (CommitDifferential:82) ·
`cellLeafInjective` / `logHashInjective` (StateCommit:230/238 — **the same file as two flagged siblings**) ·
`HashInjective` (Exec/Factory:75) · `Compress8CR` (DeployedCapTree:630) · `Compress1CR`
(Crypto/CommitmentBinding:52) · `RootCR`/`LeafCR`/`PairCR`/`LenBindCR` (Apps/QueueRoot) · `KeySetCR`
(Apps/PreRotation:103) · `RosterCR` (CouncilCommit:161) · `CommitTreeInjective`
(Spike/EffectVmConstraints2:373) · `CompressInjective` (FriVerifier:214) · `FloorDigestBinds`
(Deos/InAirAuthorityDigestGadget:128) · `Blake3NoCollision` (Blake3FloorReduce:78) · `BindingHashCR`
(Authority/MacaroonDischarge:171) · `HonestSlotCR` (Crypto/RandomnessBeacon:79) · `CompressionCR`
(Crypto/SpongeReduction:146) · `DomainSeparatedCR` (Poseidon2KeyedBridge:146).

**Verdict: FALSE-AS-NAMED at deployed parameters, with consumers.** Two representatives proved:

- **`poseidon2WideCR_false_babyBear`** — the most load-bearing unflagged carrier (7 hypothesis uses). Its own
  docstring says it is *"the EXACT analogue of `Poseidon2SpongeCR`"* — which
  `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` had **already proved FALSE**. The analogy was exact;
  the conclusion did not travel. Proved by the same counting core (`not_injective_of_finite_range`) plus
  `finite_width8_bounded`: an 8-lane squeeze into bounded lanes has finite range, and `List ℤ` is infinite.
- **`compress8CR_false_babyBear`** — `Compress8CR` is a **field of the `Cap8Scheme` structure** (`chip8CR`),
  so *every* 8-felt cap-tree theorem carries it, and a real deployed `Cap8Scheme` **value cannot exist**. Its
  non-vacuity argument (*"`Reference8` exhibits one; `badChip8_not_CR` falsifies a colliding one, so it is not
  `True`"*) is verbatim the **FALSE COMFORT** `HashFloorHonesty`'s own header already named: *"they satisfy the
  floor with a toy injective sponge, while the REAL compressing Poseidon2 refutes it."* Toy witness
  satisfiable; real instantiation false.

**Scope:** same as the flagged four — these are hypotheses, so nothing is *wrong*; the consumers are
vacuously true at real parameters and `#assert_axioms` is blind to it (axiom-clean ≠ hypothesis-free). The
honest replacement already exists (`HashFloorHonesty.CollisionResistant`) and is unused by any of them.

**REPAIR — APPLIED IN TWO STAGES, and the second stage is the one that mattered.**

*Stage 1 (2026-07-17, `InjectiveFloorRegrounded`).* The three highest-value carriers — `Poseidon2WideCR`,
`Compress8CR`, `compress4Injective` — were re-grounded onto real collision GAMES with an explicit `Eff`.
But the file states plainly: *"The OLD injective-floor consumers are KEPT UNTOUCHED — this file only ADDS
siblings."* So the regrounding was **additive**, and every consumer still rode the false hypothesis. A
regrounding that leaves the vacuous form in place has not removed the vacuity; it has only put a sound
theorem next to it. That is the failure mode this whole document is about, one level up again.

*Stage 2 (2026-07-20) — the carriers are DELETED, not re-grounded-beside.* Two of the three are gone:

| carrier | what replaced it | scope |
|---|---|---|
| `compress4Injective` | `CommitDifferential.effectVmCommit_binds_record_digest_or_collides` / `_binds_cap_root_or_collides` + `Coll4` — UNCONDITIONAL: bind, or EXHIBIT the collision at two NAMED quads | 3 files |
| `Poseidon2WideCR` | `EffectVmEmitRotationR.wireCommitR8_binds_or_collides` + `WireColl`, riding the extractors (`chainCollFind`, `wireCommit8Find`) MOVED DOWN from the regrounding file; 9 downstream keystones rewired | 5 files, 11 binder sites |

Also deleted as regrounded-and-unused: `effectVmCommit_binds_all`, `chainFrom8_inj`, `wireCommitR8_binds`.

**The shape of the honest replacement.** Not the game (a game bounds a probability; it cannot substitute for
an equality inside a `⟺` proof) and not `∃ collision` (unconditionally true at deployed parameters by
pigeonhole — §"the extractors are constructive functions"). It is **extraction as data**: a total function
that, from the equivocation, RETURNS the specific pair at which the deployed hash collides, plus a theorem
that the returned pair is a genuine collision. `root_distinct_extracts_collision` and `findCollisionZ` were
already the tree's own best practice; this generalises them to the two deleted carriers.

**Strength, stated honestly.** Every rewired conclusion became a disjunction, so as a *formula* it is weaker.
As *content at deployed parameters* it is strictly stronger: the deleted premises are unsatisfiable by the
real Poseidon2, so the old theorems said nothing about the deployed system, while the new ones hold OF it.
Nothing that was genuinely proved was given up. The teeth were RETAINED and restated about
`Function.Injective` directly (`compress4_not_injective_babyBear`, `widePerm_not_injective_babyBear`) — the
record must outlive the carrier it refuted.

**⚑ THERE IS NO FREE DELETION LEFT.** A census of the remaining 15 censused carriers (`Compress1CR`,
`RootCR`, `LeafCR`, `PairCR`, `LenBindCR`, `KeySetCR`, `RosterCR`, `CommitTreeInjective`,
`CompressInjective`, `FloorDigestBinds`, `Blake3NoCollision`, `BindingHashCR`, `HonestSlotCR`,
`CompressionCR`, `HashInjective`) found **every one USED**, 4–13 live sites each — none is an orphan that
can simply be dropped. Thirteen already have a paired `*Regrounded` / `*FloorReduce` module, and those
modules' own refutation teeth (`¬ KeySetCR hash`, …) *consume the carrier in order to refute it*, so a
naive deletion would delete the evidence that the carrier is false. That objection is answered by the
method used above and is not a blocker: restate the tooth about `Function.Injective h` directly, and the
refutation outlives the carrier. But it means each remaining carrier costs a full delete-teeth-consumers
pass, not a line removal.

**⚑ PRIORITY ORDER FOR THE REMAINDER: the non-inhabitable STRUCTURE FIELDS first.** A carrier that is a
`Prop` hypothesis makes the theorems above it vacuous; a carrier that is a *structure field* makes the
structure itself uninhabitable at deployed parameters, so every theorem quantifying over a value of that
type is vacuous — a strictly larger blast radius, and invisible at each individual use site. The known
members of that class:

| structure | field | file |
|---|---|---|
| `Cap8Scheme` | `chip8CR : Compress8CR` | `metatheory/Dregg2/Circuit/DeployedCapTree.lean` |
| `CapHashScheme` | `chipCR : Compress1CR` | `metatheory/Dregg2/Circuit/DeployedCapTree.lean` |
| `Compress2` | `compress1CR : Compress1CR` | `Crypto/CommitmentBinding.lean` |
| `LeafRealization` / `LogRealization` | carry `Poseidon2SpongeCR` | `metatheory/Dregg2/Circuit/Poseidon2Binding.lean` |
| `Heap8Scheme` / `Fields8Scheme` | own `chip8CR` twins | `DeployedHeapTree` / `DeployedFieldsTree` |

`FactoryBindingFloorRegrounded` already proves `Compress2` uninhabitable at deployed parameters, and
`StateCommitFloorRegrounded` proves the same of `LeafRealization`/`LogRealization`. The proofs exist; the
deletions do not.

**⚑ ONE CATEGORY CAVEAT — do not sweep `BindingHashCR` in with the rest.** It is `Tag → Bytes` with BOTH
sides potentially finite, so pigeonhole does NOT apply; `FactoryBindingFloorRegrounded` records this as a
deliberate non-verdict and its teeth are explicitly conditional (`card Bytes < card Tag`, or
`Infinite Tag`). Treating it as pigeonhole-false would be a category error — the kind this document
exists to catch.

**REMAINDER (named, not applied).** `Compress8CR` is the priority and is NOT yet deleted: it sits inside the
`Cap8Scheme` structure as `chip8CR`, so it is not merely a hypothesis but a **non-inhabitable field** — a
real deployed `Cap8Scheme` VALUE cannot exist, which makes *every* theorem quantifying over `S8 : Cap8Scheme`
vacuous at deployed parameters. That is the largest single vacuity left. Deleting the field is a 3-file
change (`DeployedCapTree`, `EffectVmCapFamilyComplete`, `EffectVmEmitRotationV3`) because
`recomposeUp8_inj_of_path` must become an extraction; deleting the predicate is a 7-file change that also
reaches `DeployedHeapTree` / `DeployedFieldsTree`, whose `Heap8Scheme` / `Fields8Scheme` carry their own
identically-shaped `chip8CR` field. Deferred here only because `EffectVmEmitRotationV3` was co-tenant
work-in-progress. Beyond it: `Poseidon2SpongeCR` (~237 files), `logHashInjective` (~335 binder uses),
`cellLeafInjective` (~160), `compressInjective` (~55) — the same defect at a scale that needs its own
campaign, and `Poseidon2Binding.LeafRealization` / `LogRealization` carry `Poseidon2SpongeCR` as a FIELD,
so they are non-inhabitable in exactly the `Compress8CR` way.

---

## ⚑ FINDING 3 — `MembersAt` / `MembersAt8`: the depth is in the docstring

**Carriers:** `CapHashScheme.MembersAt` (`DeployedCapTree.lean:210`), `Cap8Scheme.MembersAt8`
(`DeployedCapTree.lean:713`), + `Fields8Scheme.MembersAt8` (`DeployedFieldsTree.lean:101`),
`Heap8Scheme.MembersAt8` (`DeployedHeapTree.lean:97`). **153 references across 20 files.**

**Verdict: DOCSTRING-CONSTRAINT (not vacuous — and proving that distinction is the point).**
`cap_root.rs` pins `CAP_TREE_DEPTH = 16` (`DeployedCapOpen.DEPTH := 16`) and the file header says "depth-16"
three times. The `Prop` has **no length clause**, and `recomposeUp8 S8 cur [] = cur`. **Proved:**
`membersAt8_at_own_digest := ⟨[], rfl⟩` — a depth-0 opening is a "membership". The tree already leans on
this: `CircuitCompletenessAuthorityConstruct.lean:108` is literally `⟨[], rfl⟩` against an
`authConstructedRoot` defined *as* the leaf digest.

**⚑ This is NOT a soundness hole, and the sweep proves it rather than assuming either way.** Unlike
`CoCurvilinearity`, `root` is a **parameter**, not chosen by the existential — so the carrier has genuine
content (`membersAt8_not_vacuous_general`: it is refutable). The defect is **faithfulness**, polarity-dependent:

- **Negative position** (`DeployedFaithfulEff8.backed`, `DeployedFaithful8.backed`): an over-broad `MembersAt8`
  makes the **assumption stronger** — demands backing for depth-0 openings the depth-16 circuit never emits.
  Assumes more than deployed; falsifies nothing.
- **Positive position** (`deployedCapOpen_implies_authorizedEffB`'s `hopen`): the degenerate witness is
  available, so "membership" there is weaker than the circuit's.

No theorem is wrong; **the model is coarser than the circuit**. The tree states the matching problem itself in
`Emit/MembershipDepthGeneralRung2.lean:170` ("CR alone does NOT forbid different-length folds from
coinciding") and closes it *there* with the named `LeafNodeSep` carrier — at depth 4. The cap tree does not.

**REPAIR (named, not applied — 153 refs / 20 files, and it re-opens `CircuitCompletenessAuthorityConstruct`'s
minimal opening, which would need a genuine 16-step padded path):** carry `path.length = DEPTH`, or carry
`MembershipDepthGeneralRung2.LeafNodeSep` alongside and prove the cross-depth leg as that file already does.

---

## Reported CLEAN (a clean carrier is a real result)

Two adversarial read-only sweeps (94 `∃`-shaped carriers; ~40 docstring-smell candidates) came back with the
findings above and **otherwise clean**. Worth recording, because "three-for-three" predicted a bloodbath and
the `∃` axis did not deliver one:

- **Exemplary:** `RomUniform`/`RomUniformDerive` (`OodRomBound.lean:105,194`) — real distribution equality,
  *both poles proved*. `TranscriptOfPolynomial` / `ColumnsCVS` (`FriExtractNonCircular.lean:235,249`) — every
  doc'd hypothesis is in the body, and its falsifier correctly refutes the **existential**, not the matrix.
- **Witness genuinely pinned:** the 10 `*LeafFriFloor` carriers (`*BindingFromFold.lean`) — `E.verify q = true`
  **and** the commit equation pin `q`; the `LeafSat` parameter is a *dual-carrier* design, not a hole
  (trivializing it makes the companion `SatXFold.leafCV` unsatisfiable). `ExtractsTo`/`SatBindsProduced`
  (`LightClientUC.lean:146,151`) — same discipline, airtight: vacuity cannot hide, it only moves.
  `BadChallengePoly`, `RSListBound`, `FriProximityGapChallenges`, `CorrelatedAgreementLineAt`, `ImtVecCorr`,
  `PrivLegHolds`, `SimFrom`/`DupSim`, `StarkResidual`, `WitnessDecodes`.
- **Deliberately trivial, documented as such:** every `def … : Prop := True` in the tree (`bumpEdge`,
  `IsLossyKey`, `noteCreateAdmit`, `revokeAdmit`) — total executor arms / uniform lossy support. Not defects.
- **Already self-flagged:** `LossyIdentification.DecisionMLWEHard` ("⚠ BROKEN as a hardness floor", honest
  replacement named). `Arity8FiberBoundNaive` — retained deliberately as the carrier of its own falseness,
  zero consumers, correctly superseded.
- **Half-vacuous but DISCLOSED, completeness-class:** `SatFloor` / `TransferSatFloor`
  (`CircuitCompletenessSatFloor.lean:74`, `CircuitCompletenessTransferConstruct.lean:73`). The `Satisfied2`
  conjunct can always take the empty trace (`satisfied2_transferV3_empty` — the tree's own theorem), so
  contradictory gates would satisfy it. It is **not** provable outright (the opaque `tracePublishedCommit`
  leg survives), it is **completeness-class** (cannot falsify a soundness theorem), and the file's header
  states the limitation *itself* rather than contradicting it. **This is what an honest residual looks like**
  — it is the control group for this sweep. Named residual (still open): a non-empty Lean transfer trace;
  currently witnessed only in Rust.

## Coverage — honest

- **Population:** 949 capitalized named `Prop`s under `metatheory/Dregg2` (1,260 counting lowercase).
  Exhaustive five-test-by-hand coverage of all 949 was not attempted and is not the right shape of work.
- **Swept, load-bearing-first:** every carrier used as a hypothesis and never concluded, ranked by
  hypothesis-use count (top ~60 read); every `∃`-shaped carrier (94, agent-swept, all of `Circuit/`, `Crypto/`,
  `Consensus/`, `Deos/`, `Lightclient/`); every named hardness/CR floor (read individually — this is where both
  systemic findings are); every `:= True` body.
- **Not swept:** the ~700 structural/spec `Prop`s that are neither floors nor hypothesis carriers
  (`RowEncodes*`, `RestIffNo*`, `EffectSpec*` — these are *definitions the tree proves things about*, not
  assumptions it rests on). The `Paco/`, `Polis/`, `Games/`, `Apps/` trees got census-only coverage.
- **Highest-value un-swept residue:** the remaining ~18 injective-floor carriers listed in Finding 2 are
  *known* by class argument to be false at deployed params; only two are proved so here. Proving the rest is
  mechanical (the core lemma exists) but each needs its own bounded-range hypothesis in the right shape.

## The base rate, answered

Of the **named cryptographic floors** — the carriers that stand for an assumption — the honest count is now:
4 flagged-and-repaired (`HashFloorHonesty`), **~20 unflagged and false at deployed params** (Finding 2),
**5 that are one content-free predicate** (Finding 1), 2 Boolean floors already doc-marked broken
(`MSISHard`, `MLWESearchHard`), 1 trivially-true-at-finite-params (`SchnorrDLHard`, doc-marked). Against that,
the `∃`-shaped carriers and the structural specs are in good shape, and `SchnorrDLHard`/`toy_dl_not_hard`,
`RomUniform`, `CollisionResistant` show the tree knows exactly what a good floor looks like when it builds one.

**The pattern is not "the tree is sloppy". It is: a floor gets found vacuous → a repair is built → the repair
is checked with a test that measures shape, not content → the repair inherits the defect in a new costume, and
the header now advertises the repair.** `MSISHard` (existence-refutation) → `MSISHardQuant` (probabilistic
costume, `msisSolverAdv`) → `MSISHardQuant` (abstract `adv`, content-free). Three costumes, one hole.
The load-bearing lesson is the one Finding 1 §4 proves in Lean: **"satisfiable AND refutable" is necessary and
not sufficient.** The sufficient test is the one this sweep used — *can the consumer be proved from the WRONG
floor?* If yes, the name is doing the work.
