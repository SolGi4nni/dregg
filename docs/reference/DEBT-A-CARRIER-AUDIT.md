# DEBT-A CARRIER AUDIT — hunting `permOutZ`-class toys (2026-07-10)

> Companion to `CARRIER-CENSUS.md`. Prompted by commit `810d0dc65`: `Satisfied2Faithful`'s four
> "realizations" are all at `permOutZ : List ℤ → List ℤ := fun _ => List.replicate CHIP_OUT_LANES 0`
> (`FloorsNonVacuous.lean:108`) — the CONSTANT-ZERO permutation, which also forces `hash = 0`. Those
> are NON-VACUITY witnesses, not deployed discharges (`ZMod 5 ≠ BabyBear`, one layer over). This audit
> reads the ARGUMENT of every DEBT-A realization to find the rest of that class. Every verdict has a
> file:line. Method: `rg` for def / hypothesis-position / goal-position, then READ the term.

## HEADLINE COUNTS (DEBT-A / STARK-FRI-AIR carriers)

- **NON-VACUITY-ONLY (the permOutZ class — realized ONLY at a toy/degenerate argument): 3**
  `ChipTableSoundN`, `FriExtract`, `FriProximity` (FriSoundness sense).
- **ASSUMED (0 deployed realizations; open obligation): 5**
  `StarkSound`, `AlgoStarkSound`, `FriLowDegreeSound`, `EngineSound`, `FriProximity` (AirSoundness sense).
- **DISCHARGED-AT-DEPLOYED (realized at the real object): 3**
  `ChipTableSound` (legacy 1-felt, parametric in `hash`), `RangeTableSound`, `GuardDecodes`/`…2`.
- **FLOOR (named crypto idealisation): 2**
  `Poseidon2RealizedSponge` (= `Poseidon2SpongeCR`), `QROMInjective` (QROM RO idealisation, superseded by O2H).
- **NAME-COLLISION: 1** — `FriProximity` is TWO different Props (see its row).

**Bottom line:** the STARK/FRI verifier-soundness core of DEBT-A (`StarkSound` and its bridge
`AlgoStarkSound`/`FriLowDegreeSound`, the whole-history `EngineSound`, the per-node `FriExtract`, the
low-degree `FriProximity`) is **NOT discharged at the deployed BabyBear object anywhere.** It is either an
open class with 0 instances (5 carriers) or realized only at a toy (constant-zero permutation / `verify :=
fun _ => true` / a `ZMod 5` Reed-Solomon setup) (3 carriers). The AIR *chip/range/guard* support layer
(`ChipTableSound` legacy, `RangeTableSound`, `GuardDecodes`) IS genuinely discharged at deployed objects —
good news, but it is the easy layer; it does not carry the FRI extraction.

---

## THE NON-VACUITY-ONLY LIST (the toys) — degenerate argument quoted

### `ChipTableSoundN` — the wide (8-felt) chip-soundness predicate
- Def: `DescriptorIR2.lean:1220` `ChipTableSoundN (permOut : List ℤ → List ℤ) (tbl) := ∀ r ∈ tbl, ∃ ins, ins.length ≤ CHIP_RATE ∧ r = chipRowN permOut ins`.
- (a) ASSUMED: **139** hypothesis-position sites (`rg "\[ChipTableSoundN|\(ChipTableSoundN|: ChipTableSoundN"`). The load-bearing DEBT-A one is `chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)` in `Satisfied2Faithful.lean:118`, `RotatedKernelRefinement.lean:107`, `EffectVmEmitV2.lean:487`.
- (b)+(c) REALIZED — **all at a constant permutation, none at deployed Poseidon2:**
  - `FloorsNonVacuous.lean:122` `genuineChipTbl_sound : ChipTableSoundN permOutZ genuineChipTbl` — arg `permOutZ := fun _ => List.replicate CHIP_OUT_LANES 0` (`:108`).
  - `Satisfied2FaithfulActive.lean:107` `activeChipTbl_sound : ChipTableSoundN permOutZ (tfOf2 transferV3 realRow lastRow .poseidon2)` — the "active" keystone; despite REAL per-row transition gates, the chip permutation is STILL `permOutZ` (comment: "every one of the 40+40 evaluated chip tuples has an ALL-ZERO 8-lane squeeze").
  - `NoteSpendingLeafRefine.lean:394` `witness_chipSound : ChipTableSoundN witnessPerm (...)` — arg `witnessPerm := fun _ => [K0, 0, 0, 0, 0, 0, 0, 0]` (`:383`), a constant K₀-headed block.
- **VERDICT: NON-VACUITY-ONLY.** Zero realizations at `Poseidon2BabyBearW16.perm` (searched; none). This is the exact `permOutZ` class the census flagged — the chip-permutation faithfulness that `Satisfied2Faithful` needs for the DEPLOYED chip is never proved.

### `FriExtract` — per-node in-circuit verifier soundness (recursion floor)
- Def: `AggAirSound.lean:140` `FriExtract (ChildVerifierSat) := ∀ c s, ChildVerifierSat c s → ∃ p, verify p = true ∧ vkCommit p = c ∧ exposedPI p = s`.
- (a) ASSUMED: taken as `(hagg : FriExtract E.Proof E.verify …)` in ~10 `*BindingFromFold.lean` files (`BlindedMembershipBindingFromFold:93`, `CustomBindingFromFold:98`, `PresentationBindingFromFold:88`, `FactoryBindingFromFold:98`, `BridgeBindingFromFold:118`, `DecoBindingFromFold:94`, `DslBindingFromFold:106`, `SovereignBindingFromFold:102`, `HatcheryBindingFromFold:83`) — and it is `EngineSound`'s residual FRI leg after grounding (below).
- (b)+(c) REALIZED once, at a toy: `AggAirSound.lean:266` `wit_friExtract : FriExtract WitProof witVerify witVkCommit witExposedPI witCVS` where `witVerify := fun _ => true` (`:256`, a verifier that ACCEPTS EVERYTHING) and `witCVS := fun _ _ => True` (`:261`). The sponge used is `zSponge := fun _ => 0` (`:231`).
- **VERDICT: NON-VACUITY-ONLY.** The single realization is over an always-accept verifier — it proves the Prop is inhabited, nothing about a real FRI verifier.

### `FriProximity` (FriSoundness sense) — low-degree closeness `closeN S.C d f`
- Def: `FriSoundness.lean:403` `FriProximity (S : FriSetup F ι κ) (d) (f) := closeN S.C d f`.
- (b) The discharge `friProximity_discharge` (`:403`ff) IS a genuine, FIELD-GENERIC proof (proximity-gap → codeword), and the folding lemma `fold_close_of_two_alpha` is real math.
- (c) BUT the only `FriSetup` it is instantiated at is the `§5` toy: `ZMod 5`, `L = {1,2,3,4}` indexed by `Fin 4`, rate-1/2 Reed–Solomon (`FriSoundness.lean:455`, `pVal : Fin 4 → ZMod 5 := ![1,2,3,4]` `:469`, `rsGeom : FriGeom (ZMod 5) (Fin 4) (Fin 2)` `:478`). Never instantiated at BabyBear / the deployed rate / query count.
- **VERDICT: NON-VACUITY-ONLY at the deployed object.** The lemma is real and reusable; the deployed instantiation (BabyBear, rate 1/6, 19 queries) does not exist. This is the census's honest "PARTIALLY discharged" row, confirmed.

---

## THE ASSUMED LIST (0 deployed realizations — honest open obligations)

### `StarkSound` — the p3 batch-STARK `accept ⟹ ∃ Satisfied2 witness`
- Def: `CircuitSoundness.lean:382` `class StarkSound (hash) (R) : Prop where extract : ∀ pi π, verifyBatch (vkOfRegistry R) pi π = accept → ∃ …, Satisfied2 … ∧ tracePublishedCommit t = pi.toPublished`.
- (a) ASSUMED: **35** `[StarkSound …]` hypothesis sites.
- (b) 0 concrete `instance : StarkSound`. The ONLY "realization" is `FriVerifierBridge.lean:113` `starkSound_of_verifyAlgo … : StarkSound hash R`, but it takes `[carrier : AlgoStarkSound …]` (`:111`) + `(href : DeployedRefines …)` (`:112`) — i.e. it RELOCATES the floor to `AlgoStarkSound`, it does not discharge it.
- **VERDICT: ASSUMED (class, 0 instances).** The bridge is honest engineering (verifier-out-of-TCB) but its inputs are still an un-instanced floor class + a code-refinement assumption.

### `AlgoStarkSound` — the FRI extraction floor re-stated over the specified `verifyAlgo`
- Def: `FriVerifierBridge.lean:75` `class AlgoStarkSound … : Prop where extract : ∀ pi π, verifyAlgo … = true → ∃ …, Satisfied2 …`.
- (a) ASSUMED at 3 sites (the bridge theorems). (b) 0 instances (`rg` finds none). **VERDICT: ASSUMED (class, 0 instances).**

### `FriLowDegreeSound` — FRI low-degree soundness for the wrap verifier
- Def: `FriVerifier.lean:832` `class FriLowDegreeSound [Inhabited F] [DecidableEq F] …`.
- (a) ASSUMED (the `wrap_sound` payoff carries it). (b) 0 instances. **VERDICT: ASSUMED (class, 0 instances).**

### `EngineSound` — the three whole-history recursion hypotheses
- Def: `RecursiveAggregation.lean:121` `structure EngineSound … where recursive_sound … ; leaf_sound (Forall₂ …) ; binding_sound …`.
- (a) ASSUMED: **28** `(es : EngineSound …)` sites (apex/assurance-case).
- (b)+(c) The `engineSound_*` builders (`GroundedApex.lean:118/149`, `EngineSoundOfApex.lean:217`, `WitnessRealizing.lean:224`, `RecursiveSoundFromNodes.lean:190`) DERIVE `leaf_sound` (from `descriptorRefines`) and `binding_sound` (from `BindingAirSound`, resting on `Poseidon2SpongeCR`) — genuine — but REDUCE `recursive_sound` to the per-node `FriExtract` floor (`engineSound_grounded_v2` threads `PTree + NodeCarrier`). Since `FriExtract`'s only realization is the toy above, the FRI residual is un-discharged at deployed.
- **VERDICT: ASSUMED.** Two of three legs are grounded on `Poseidon2SpongeCR`; the recursion leg bottoms out at `FriExtract` (NON-VACUITY-ONLY). No deployed-object realization of the whole structure.

### `FriProximity` (AirSoundness sense) — `verifyLD ⟹ transition constraints`
- Def: `AirSoundness.lean:219` `FriProximity (applyEff) (verifyLD) (openTr) := ∀ π com, verifyLD π com → satisfiesTransition applyEff (openTr com).1 (openTr com).2`.
- (a) ASSUMED: `circuit_sound_via_fri` (`:244`) takes `(hfri : FriProximity applyEff verifyLD openTr)`. (b) NOT discharged in this file (the docstring says "the interface unit 2b must PROVE — never assumed closed here", but no discharge is provided here). **VERDICT: ASSUMED.**

---

## THE DISCHARGED-AT-DEPLOYED LIST (good news — realized at the real object)

### `ChipTableSound` (legacy 1-felt digest) — DISCHARGED, parametric in `hash`
- Def: `DescriptorIR2.lean:1150` `ChipTableSound (hash) (tbl) := ∀ r ∈ tbl, ∃ ins lanes, … r = chipRow hash ins lanes`.
- (c) `EffectVmEmitIvcStateTransitionRung2Full.lean:161` `arTf_sound (hash) : ChipTableSound hash ((arTrace hash).tf .poseidon2)` and `EffectVmEmitIvcStateTransitionRung2.lean:333` `honTf_sound (hash) : ChipTableSound hash ((honTrace hash).tf .poseidon2)` are proved **∀ hash** — the chip table is literally constructed as `chipRow`s of the parameter, so instantiating `hash :=` the deployed Poseidon2 gives a genuine statement. `#assert_axioms arTf_sound` clean (`:285`).
- CAVEAT: some sibling realizations ARE toys — `MultiStepChainRefine.lean:223` `wChipSound : ChipTableSound (fun _ => 0) …`, `CommittedThresholdRefine.lean:433` `ChipTableSound (fun _ => 0) …`, `EffectVmEmitIvcStateTransitionRefine.lean:288` `demo_chip_sound : ChipTableSound hash0 …`. The parametric ones are genuine; the `fun _ => 0` ones are demos.
- **VERDICT: DISCHARGED-AT-DEPLOYED** for the parametric traces. Note this is the WEAK 1-felt predicate; the wide `ChipTableSoundN` (which is what binds the light-client commitment) is the NON-VACUITY-ONLY one above.

### `RangeTableSound` — DISCHARGED at the deployed range table
- Def: `NonRevocationRefine.lean:89` `RangeTableSound (bits) (tbl) := …` (each row decodes to a `bits`-bounded value).
- (c) `NonRevocationRung2Full.lean:116` `fixTrace_rangeSound : RangeTableSound ORDERING_BITS (fixTrace.tf .range)`, `NonRevocationRung2.lean:234` `hn_rangeSound`, `:364` `cheat_rangeSound`, `:532` `flr_rangeSound` — over `rangeRows BAL_LIMB_BITS` / `ORDERING_BITS`, the DEPLOYED range-AIR height (a genuinely finite concrete table, not a toy stand-in). 16 hypothesis sites still assume it, but the realizations are at the real table.
- **VERDICT: DISCHARGED-AT-DEPLOYED.**

### `GuardDecodes` / `GuardDecodes2*` — DISCHARGED per deployed effect
- Def: `EffectCommit.lean:409` (+ `…2/2Dual/2Triple/2Quad/2Quint` variants).
- (c) ~20 realizations at the REAL deployed effect specs: `EffectInstances2.lean:138` `GuardDecodes2 (mintE D hD)`, `:321` `noteSpendE`, `Inst/transfer.lean:149` `balanceE`, `Inst/revoke.lean:175` `revokeE`, `Inst/delegate.lean:170` `delegateE`, `Inst/receiptArchiveA.lean:109` `receiptArchiveE`, etc.
- **VERDICT: DISCHARGED-AT-DEPLOYED.** (Per-effect obligation, not really DEBT-A/STARK, but real.)

---

## THE FLOOR LIST

### `Poseidon2RealizedSponge` — content IS `Poseidon2SpongeCR`
- Def: `Poseidon2Binding.lean:178` `structure Poseidon2RealizedSponge (sponge) where params ; params_are_real : params = babyBearD4W16 ; spongeCR : Poseidon2SpongeCR sponge`.
- (b) `Poseidon2Binding.lean:289` `refRealizedSponge : Poseidon2RealizedSponge refSponge` — params tagged `babyBearD4W16` (REAL), but the concrete `sponge` is `refSponge (xs) := Encodable.encode xs` (`:276`), an injective ℕ ENCODER stand-in, NOT the real Poseidon2 permutation; `spongeCR := refSponge_CR` proved from encode-injectivity (`:278`).
- **VERDICT: FLOOR** (its only content is the honest `Poseidon2SpongeCR` assumption; instantiate at the real sponge + the CR floor for deployment). NOTE the concrete non-vacuity witness is at an `Encodable.encode` stand-in with params merely *tagged* real — inhabitation is honest, but do not read `refRealizedSponge` as "the real Poseidon2 is realized."

### `QROMInjective` — QROM random-oracle idealisation, superseded by O2H
- Def: `MlKemIndCca.lean:286` `def QROMInjective (H : Msg → SS) := Function.Injective H`.
- (b)+(c) Per `FoQrom.lean:34/104`, the headline ML-KEM statements do NOT take `QROMInjective` as a hypothesis; it is discharged/superseded by the real O2H reprogramming bound (`OneWayToHiding.o2h_bound`), bottoming out at `MLWESearchHard`. Teeth on a `Bool × ZMod 2`, q=1 toy.
- **VERDICT: FLOOR** (named QROM idealisation) → reduced to O2H + `MLWESearchHard`. This is a crypto-floor carrier, NOT a DEBT-A/STARK toy; listed for completeness.

---

## THE `FriProximity` NAME-COLLISION VERDICT

`FriProximity` is **TWO DIFFERENT Props in two namespaces, with NO bridge between them:**

1. **`Dregg2.Circuit.AirSoundness.FriProximity`** (`AirSoundness.lean:219`): `∀ π com, verifyLD π com → satisfiesTransition applyEff (openTr com)…`. A *verifier-accept ⟹ AIR-transition-holds* interface. Carried purely as a hypothesis in `circuit_sound_via_fri` (`:244`); **ASSUMED**, not discharged.
2. **`Dregg2.Circuit.FriSoundness.FriProximity`** (`FriSoundness.lean:403`): `closeN S.C d f`, i.e. *the oracle `f` is `d`-close to the Reed–Solomon code*. Genuinely discharged by the field-generic `friProximity_discharge`, but instantiated only at the `ZMod 5`/`Fin 4`/rate-1/2 toy `FriSetup` (`:455`ff); **NON-VACUITY-ONLY** at the deployed object.

They are different statements (one about a whole-verifier accept relation, one about codeword proximity) that a real STARK argument would CHAIN (proximity → the spot-checked constraints bind the actual low-degree trace → transition holds), but **no such bridge term exists in the tree** — the collision is nominal, and each half is separately un-deployed (one assumed, one toy-only).

---

## WHAT DEBT-A ACTUALLY HAS TO PROVE

DEBT-A's real obligation is a **STARK/FRI verifier-soundness argument instantiated at the DEPLOYED
BabyBear object**, in four connected pieces. (1) Realize `ChipTableSoundN` at the genuine
`Poseidon2BabyBearW16` permutation — prove the deployed chip AIR's squeeze block IS the real
permutation output, replacing the constant-zero `permOutZ` (this is `Satisfied2Faithful`'s
`chipTableFaithful` and the census's "DEBT-A brick 4"). (2) Instantiate the field-generic FRI
proximity/folding machinery (`FriSoundness.FriProximity`, already proven abstractly) at BabyBear with the
deployed rate/blowup/query-count, discharging the `ZMod 5` toy. (3) Chain proximity → AIR transition
binding → the `AirSoundness.FriProximity` interface, and thence produce an actual `instance : StarkSound`
(equivalently discharge `AlgoStarkSound` + `FriLowDegreeSound`) — turning the 35 `[StarkSound]` sites from
assumption into theorem. (4) Realize the per-node `FriExtract` at a real recursion verifier (not
`witVerify := fun _ => true`), which grounds `EngineSound.recursive_sound` and the whole-history apex.
Only the crypto FLOOR (`Poseidon2SpongeCR`) and one `DeployedRefines` Rust-refines-spec residual should
remain. Everything else in DEBT-A today is either a 0-instance class or a constant-function witness.
