# CARRIER CENSUS — every assumed Prop/class in the metatheory, classified (2026-07-09)

> Companion to `METATHEORY-GROUND-TRUTH.md`. Prompted by ember's "naming IS faking": a `def C : Prop` or
> `class C` used as a hypothesis `[C]` is an ASSUMPTION `#assert_axioms` cannot see. This census sorts every
> such carrier into: **FLOOR** (legitimately irreducible) / **realized** (actually proved somewhere) /
> **PROVE?** (a real obligation, dischargeable) / **REFINE?** (unrealizable *as stated* — needs a data
> refinement to become provable). Method: mechanical grep pass + targeted reads; **every verdict has a grep
> line, but the buckets are heuristic — spot-verify before trusting a single row.**

## The headline: it is NOT "all fake." Three clusters, very different leverage.
Counts (carrier-shaped Props/classes that appear in ≥1 hypothesis position): **FLOOR 9 · realized ~37 ·
PROVE? ~38 · REFINE? ~17.**

### 1. FLOOR (9) — legitimate, keep them
`Poseidon2SpongeCR` (423 uses), `HashCR` (47), `SchnorrDLHard` (27), `Poseidon2WideCR` (8), `MSISHard` (6),
`DecisionMLWEHard` (3), `MLWESearchHard` (3), `SchnorrDLHardF` (3), `HintMLWEHard` (2). Assuming a concrete
hash is CR and a lattice/DL problem is hard IS the floor. **These are the honest TCB** (plus leanc/FFI for the
extracted native code, and — separately — seL4's cited kernel proofs).

### 2. HASH-INJECTIVITY — NOT a debt, a PLUMBING alias (~1200 uses, ~5 carriers)
`compressNInjective` (464), `logHashInjective` (363), `cellLeafInjective` (195), `compressInjective` (155),
`compress4Injective` (3). Their definitions are literally collision-resistance, e.g.
`compressNInjective h := ∀ xs ys, h xs = h ys → xs = ys`. **The reduction to the floor already exists** —
`Poseidon2Binding.compressNInjective_of_poseidon2CR`, `cellLeafInjective_of_realization`,
`HistoryAggregation.lean:92` states `compressNInjective compressN = Poseidon2SpongeCR compressN`. They show as
"PROVE?" only because callers assume the *alias* `[compressNInjective]` in 464 places instead of threading the
existing reduction. **Debt: mechanical — route everything through the single `Poseidon2SpongeCR` floor** so the
crypto residual of the whole commitment machinery is ONE assumption, not a scattered injectivity set. (Modulo
the finite-encodability caveat in cluster 4: injectivity-from-CR needs the hashed value to be finitely
serializable — which is exactly what the data refinement guarantees.)

### 3. realized (~37) — genuinely proved (spot-verified: trustworthy)
`ChipTableSound`/`ChipTableSoundN` (`FloorsNonVacuous.genuineChipTbl_sound … := by`, `arTf_sound`, `honTf_sound`
over real poseidon2 chips), `GuardDecodes` (12 realizations), `RangeTableSound`, `FriExtract`, the `*CR` app
carriers, `Poseidon2RealizedSponge`, `QROMInjective`, `HintTranscriptSimulatable` (proved via `hint_mlwe`), the
UC residuals, etc. Grounded; individual rows still merit a look but the bucket is real.

## THE TWO REAL DEBTS

### DEBT A — STARK/FRI verifier soundness (~5 carriers, ~50 uses)
`StarkSound` (38, `class`, 0 instances — the p3 batch-STARK "accept ⟹ ∃ satisfying trace"), `AlgoStarkSound`,
`FriLowDegreeSound`, `FriProximity` (3 — PARTIALLY discharged: `FriSoundness.friProximity_discharge` proves it,
but only instantiated over a `ZMod 5` toy; the folding lemma `fold_close_of_two_alpha` is field-generic and
REAL), `EngineSound` (32), `FriExtract`. **The grind:** model the Plonky3/FRI-over-**BabyBear** verifier
(AIR quotient check + FRI low-degree test + Poseidon2 Merkle openings), instantiate the field-generic FRI
soundness at BabyBear/rate/rounds, prove `accept ⟹ ∃ t, Satisfied2`, produce an actual `instance : StarkSound`.
Not a research open (BBHR18 + the p3 design); large, multi-session.

### DEBT B — DATA REFINEMENT of function-valued state (~15 carriers, ~250 uses)  ← highest leverage
`RestHashIffFrame` (199), `RestFrameDecodes2` + `…Dual/Triple/Quad/Quint` (~44), `DeployedFaithfulEff` /
`…Eff8` / `DeployedFaithful` / `FaithfulCapTree` (~33), `Satisfied2Faithful` (34), `LeafRealization` /
`LogRealization` (11). **Root cause (the tree admits it — `KeystoneAuditArgusReceipt.lean:34`: "the ONLY
carrier with no realization into ℤ is `RestHashIffFrame`"):** the kernel models `caps : CellId → List Auth`,
`delegations`, `heaps` as TOTAL FUNCTIONS over an infinite `CellId` domain. A commitment `RH : … → ℤ` cannot
injectively bind an infinite-domain function, so `RestHashIffFrame` (which asserts exactly that binding) is
**unsatisfiable**, and every whole-kernel binding downstream is vacuous-in-application.

**THE FIX (ember's data-refinement idea — the unlock):** remodel the function-valued kernel fields as **finite
maps** (`Finsupp` / sorted association lists over the finitely-many touched cells). Then:
- the state is finitely serializable ⇒ the hash-injectivity reductions (cluster 2) actually apply;
- `RestHashIffFrame` becomes a PROVABLE lemma (finite encode is injective under CR), not an assumption;
- `RestFrameDecodes2*` and the `DeployedFaithful*` faithfulness carriers follow.
Keep the deployed Rust impl efficient (it already uses finite maps — `caps` is a sparse map at runtime, not a
total function); connect the efficient impl to the finite-map proof model by a **refinement relation**
(`impl_refines_model`), so the proof gets a finitely-committable object and the impl pays nothing. This is the
classic proof-vs-performance data refinement, and it discharges the single largest carrier cluster in the tree.

### misc PROVE? (~25) — assorted per-effect obligations
`GuardDecodes2` (25) + `…Dual/Triple/Quint/Quad`, `SoundPolicy`, `VouchSound`, `EffectDecodeBridge`,
`ClosedWitness`, `SoundSubstitution`, `JointBinding`, `RedBinding`, `BridgeRowBinds`, `CellBridgeMintSpec`, …
Each is a real, individually-dischargeable soundness obligation (many are per-effect variants of the same
argument). Lower leverage than A/B; do them as the effects they gate get grounded.

## Recommended grind order
1. **DEBT B first (data refinement)** — highest leverage (~250 direct carrier-uses + it *enables* cluster 2's
   injectivity reductions to actually apply). Finite-map the state, prove `RestHashIffFrame`, thread the
   refinement relation to the impl.
2. **Cluster 2 plumbing** — once the state is finite, collapse the ~1200 injectivity hypotheses to the single
   `Poseidon2SpongeCR` floor.
3. **DEBT A (StarkSound)** — the p3/FRI verifier soundness, in parallel (independent of B).
4. **misc PROVE?** — per effect, as grounded.

## Honesty notes
- The buckets are a HEURISTIC (regex for "hypothesis position" vs "goal position"). Known false-"PROVE?":
  `FriProximity`, `HintTranscriptSimulatable` are discharged under hypotheses my grep didn't credit. Spot-verify
  any row before acting on it.
- "realized" ≠ "realized for the DEPLOYED object" — verify the realization isn't a toy (the `ZMod 5` lesson).
- This census counts CIRCUIT/soundness carriers. The crypto-floor reductions (DL/MSIS/MLWE) are separately
  audited in `METATHEORY-GROUND-TRUTH.md`.


## ⚠ CORRECTION (2026-07-10): `Satisfied2Faithful` / `DeployedFaithful*` are NOT DEBT-B carriers
This census filed `Satisfied2Faithful` (32 uses) and `DeployedFaithful*` (9) under DEBT-B ("provable from the
simulation"). **That was wrong.** Read at HEAD: `Satisfied2Faithful` (Dregg2/Circuit/Satisfied2Faithful.lean:109)
`extends Satisfied2` and asserts AIR/STARK CHIP-LAYER facts — `permOut` exposing `CHIP_OUT_LANES`,
`chipHashIsLane0` (the v1 digest is lane 0 of the genuine Poseidon2 permutation), `chipTableFaithful :
ChipTableSoundN permOut (t.tf .poseidon2)`. This is the SAME family as `StarkSound` (DEBT A) — the AIR being
faithful to the effect step at the CHIP level. The finite-map data refinement (`denote`, `FinKernelState`,
`FinFrameHash`, `FinInterp`) never mentions `permOut`/chip-tables/`Satisfied2` (verified: zero occurrences), so it
CANNOT and does NOT discharge them. RECLASSIFIED to DEBT A / the AIR-chip layer. DEBT-B's actual carriers are
`RestHashIffFrame` + the 4 injectivity carriers (state-commitment binding) — DISCHARGED to `Poseidon2SpongeCR` on
the reachable subclass by `FinBindsKernel.recStateCommit_binds_kernel_fin` (3b6ed68af, non-vacuous per 8cd504be3).

## DEBT-B terminus (2026-07-10) — the mathematical core is PROVED; the tail is named
- ✅ `RestHashIffFrame` + `compressInjective`×2 + `compressNInjective` + `cellLeafInjective` → `Poseidon2SpongeCR`
  ALONE, on the reachable denote-image subclass (`recStateCommit_binds_kernel_fin`, instantiable). `LeafRealization`
  CONSTRUCTED, not assumed. All 30 deployed `*Stmt` program commuting squares proved (R1's `hpres` gate discharged).
- ◑ The ~1200-use injectivity CLUSTER (`compressNInjective`/`cellLeafInjective` as bare hypotheses across ~139
  files) is MECHANICAL PLUMBING, not debt: the reductions (`compressNInjective_of_poseidon2CR`,
  `poseidon2CommitSurface`) EXIST and are proved. Threading them through all 139 downstream theorems (so each takes
  `Poseidon2SpongeCR` instead of the alias) is a large mechanical sweep that COLLIDES with the active
  import-slimming lane — NAMED here as the remaining tail, not force-churned into a live tree. The floor is
  singular WHERE IT BINDS (the R4 path); making it singular everywhere is bounded mechanical work for a calm tree.
- → `Satisfied2Faithful` / `DeployedFaithful*` reclassified to DEBT A (above).


## ⚠ FINDING (2026-07-10): `RestFrameDecodes2` is NOT a separate carrier — it IS `RestHashIffFrame.mp`
`RestFrameDecodes2 S E := ∀ k k', S.RH k = S.RH k' → E.restFrame k k'` (EffectCommit2.lean:377). Its realized
instances discharge it as `fun k k' h => (hRest k k').mp h` where `hRest : RestHashIffFrame S.RH` — i.e. it is
DEFINITIONALLY the forward (`.mp`) direction of `RestHashIffFrame`, already realized this way for ≥5 effects
(mintE, noteSpendE, attenuateE, noteCreateE, revokeDelegationE). Since R4 discharged `RestHashIffFrame (RH_fin)`
to `Poseidon2SpongeCR` on the reachable denote-image (`restHashIffFrame_of_fin`), `RestFrameDecodes2` is on the
SAME floor by the same result — no separate debt. Re-threading the remaining assumed sites through the
`finCommitSurface` RH is mechanical (`.mp` of the R4 iff).

## ✅ DEBT-B CARRIER FAMILY — final accounting (2026-07-10)
Every DEBT-B carrier is a PROVED theorem or reduced to `Poseidon2SpongeCR` on the reachable subclass:
- `RestHashIffFrame` (199) → `restHashIffFrame_of_fin` ⟸ `Poseidon2SpongeCR` (R4 `3b6ed68af`, non-vacuous
  `8cd504be3`).
- `RestFrameDecodes2*` (44) → `= RestHashIffFrame.mp` ⟸ same floor (finding above).
- `compressInjective`×2 / `compressNInjective` / `cellLeafInjective` → `injectivity_collapses_to_poseidon2CR`
  ⟸ `Poseidon2SpongeCR` (`d046dfb3d`); `LeafRealization` CONSTRUCTED (`finLeafRealization`), not assumed.
- `Satisfied2Faithful` (34) / `DeployedFaithful*` (33) → RECLASSIFIED to DEBT A (AIR/chip layer — `extends
  Satisfied2`; the finite-map files never touch `permOut`/chips). NOT DEBT-B.
All 30 deployed `*Stmt` program commuting squares proved (R1 `hpres` gate discharged). Whole tree green 4537.
REMAINING (mechanical, NOT a carrier debt): re-thread the ~10 `recStateCommit_binds_kernel` consumers + the
`RestFrameDecodes2` sites through `finCommitSurface`/`RH_fin` on the reachable subclass. Tree-wide injectivity
uses on the DEBT-A/AIR paths are DEBT-A's.

## ⚠ EFFECT-COVERAGE CORRECTION (2026-07-10, stop-hook-forced)
"hpres discharged for EVERY deployed effect" was an OVERCLAIM. The 30 proved `*Stmt` squares cover the
RecStmt-expressible effects. SIX deployed Effect variants have distinct apply methods and NO proved square:
GrantCapability (apply_grant_capability), SpawnWithDelegation (apply_spawn_with_delegation), ShieldedTransfer
(apply_shielded_transfer), and Notify/React/Promise (Reactive "Track 2", turn/src/reactive.rs). Some MAY reduce
to covered machinery (React/Promise ↔ noteSpend/noteCreate nullifier set; GrantCapability ↔ grant), but that is
UNVERIFIED. hpres is discharged for RecStmt-expressible effects ONLY. This is a real remaining DEBT-B gap, not a
count quibble — the DEBT-B carrier result (RestHashIffFrame→Poseidon2SpongeCR) is unaffected.

## measured (2026-07-10): the 6 uncovered effects have NO Argus model
None of GrantCapability/SpawnWithDelegation/ShieldedTransfer/Notify/React/Promise has an Argus `*Stmt` program —
they are UNMODELED in the finite-map RecStmt kernel (no square to prove within DEBT-B). Classification:
ShieldedTransfer = DEBT-A (STARK-verified); Notify/React/Promise = reactive "Track 2" subsystem (turn/src/
reactive.rs, promise-hole-is-a-nullifier); GrantCapability/SpawnWithDelegation = distinct apply, no Argus program
(possibly compositions). The finite-map refinement covers the Argus-modeled kernel (30 programs); these 6 are a
named scope boundary. DEBT-B carrier result (RestHashIffFrame→Poseidon2SpongeCR) unaffected.

## measured (2026-07-10): the reactive trio SPLITS — Promise/Notify are OFF-KERNEL, React is a nullifier-spend
Read at HEAD (turn/src/executor/apply.rs):
- **Promise (apply_promise:1315), Notify (apply_notify:1349)** mutate `self.reactive_registry.lock()` — an
  EXECUTOR-side structure. `reactive_registry is NOT kernel state`: RecordKernelState (Lean) has no such field.
  So they do NOT mutate the finite-map kernel — there is NO commuting square to prove. A precise SCOPE BOUNDARY
  (the reactive registry is a separate subsystem), not a coverage gap.
- **React (apply_react:1405)** spends a nullifier: records `pending_id` into the note_nullifiers set = the SAME
  kernel mutation as NoteSpend (`nullifiers := nf :: k.nullifiers`, RecordKernel.lean:968). React's kernel effect
  IS noteSpend → a square IS provable (in flight, FinReactSquare.lean).
- **ShieldedTransfer** — kernel mutation is nullifier-spend + balance (noteSpend + transfer, both covered); the
  STARK verification (verify_stark_side) is the DEBT-A part. Its KERNEL square is potentially reducible; the STARK
  soundness is DEBT-A.
So the finite-map effect ceiling: React closable (nullifier); Promise/Notify off-kernel (no square exists);
ShieldedTransfer kernel-part reducible but STARK = DEBT-A. Nothing faked; each boundary is measured.

## ⚠ AUDIT FINDING (2026-07-10, DEBT-A brick-4 scout): Satisfied2Faithful's "realizations" are at a TOY permutation
The census recorded `Satisfied2Faithful` as assumed=32 / realized=0. BOTH numbers need correcting, in opposite
directions, and the second one matters more:
- There ARE four constructed terms (`satisfied2Faithful_transferV3/_active/_inhabited/_satisfiedVm`) and
  `genuineChipTbl_sound : ChipTableSoundN permOutZ genuineChipTbl` is PROVED, no carrier hypothesis, axiom-clean.
- **BUT `permOutZ : List ℤ → List ℤ := fun _ => List.replicate CHIP_OUT_LANES 0` (FloorsNonVacuous.lean:108) is
  the CONSTANT-ZERO function** — NOT the deployed `Poseidon2BabyBearW16` permutation. With `permOut = zeros`,
  `chipHashIsLane0 : hash ins = (permOut ins).headD 0` forces `hash = 0` as well. Both levers are trivial.
- So those terms are **NON-VACUITY witnesses** (the Prop is inhabited — which is exactly what `FloorsNonVacuous`
  honestly claims and is genuinely valuable), NOT a discharge of `Satisfied2Faithful` for the DEPLOYED chip.
  Reading them as "Satisfied2Faithful is realized" would be the `ZMod 5 ≠ BabyBear` mistake one layer over.
- 26 sites still take `Satisfied2Faithful` as a HYPOTHESIS.
**DEBT-A brick 4 (scoped precisely):** realize `Satisfied2Faithful` with `permOut :=` the REAL deployed
permutation (`Poseidon2BabyBearW16.perm`, sorry-free) — prove `permWidth` / `chipHashIsLane0` (the v1 digest IS
lane 0 of the genuine squeeze) / `chipTableFaithful : ChipTableSoundN` over the real poseidon2 chip table. THEN
the 26 hypothesis-sites can be discharged. Non-vacuity ≠ deployed discharge.
