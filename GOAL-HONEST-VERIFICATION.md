<!-- ⚑ THE ACTIVE verification plan. SUPERSEDES GOAL-VERIFIED-SYSTEM.md (retracted 2026-07-09).
     Hub: links the census + DEBT + delta docs under docs/reference/. Edit THIS lane only. -->

# GOAL — RETIRE THE CARRIER DEBT (the honest verified system)

## Why this exists
The 07-09 "VERIFIED SYSTEM" campaign was **RETRACTED** (HORIZONLOG 07-09): it declared seven criteria "done"
while resting on NAMED carriers — `StarkSound`, `RestHashIffFrame`, the faithfulness family — that are
`class`/`def : Prop` **assumed as hypotheses**, which `#assert_axioms` cannot see. *Naming is faking.* This plan
discharges the real debt the census then mapped, honestly. The math that was genuine survives; only the SCOPE
claims were retracted.

## The target trusted base (what DONE means)
The apex (`lightclient_unfoolable` / `turnDecodeChain_refines_turnSpec`) rests on **ONLY**:
- `Poseidon2SpongeCR` — a concrete-hash collision-resistance assumption (the honest hash floor);
- the lattice/DL floor — `MSISHard` / `MLWESearchHard` / `SchnorrDLHard` (the crypto surfaces);
- the `leanc`/FFI toolchain (for extracted native primitives).

**NO `seL4-cited`** (dropped 07-09): an informal cross-artifact cite is not a floor — our Lean cap model has no
formal refinement to seL4's Isabelle proofs, and l4v's own guarantees are heavily caveated. Capability soundness
is **cryptographic** (`CapabilityChain` under DL∨MSIS). A hardware-enforcement story, if ever wanted, is an
EXPLICIT named kernel-interface assumption with its caveats — a TCB item, not a cite. **NO** `StarkSound` /
`RestHashIffFrame` / `Faithful*` as assumptions — each PROVED or reduced to the floor.

## The debt map (`docs/reference/CARRIER-CENSUS.md` = the ledger)
- **FLOOR (9)** — legit; keep.
- **HASH-INJECTIVITY (~1200 uses)** — NOT debt; the reductions to `Poseidon2SpongeCR` already exist
  (`_of_poseidon2CR`). PLUMBING: route through the one floor.
- **realized (~37)** — genuinely proved.
- **DEBT A — `StarkSound`** (~50) — prove the Plonky3/FRI-over-BabyBear verifier sound.
- **DEBT B — `RestHashIffFrame` + faithfulness family** (~250) — the finite-map data refinement.

## The plan

### DEBT B — in flight (`docs/reference/DEBT-B-FINITE-MAP-REFINEMENT.md`)
DONE, audited-by-type, closure-green:
- **R1** `6458e10d2` — `FinKernelState` (sorted-nodup maps) + `denote_injective` (unconditional).
- **R2** `e365d1c2d` — `restHashIffFrame_fin` ← `Poseidon2SpongeCR` alone; `RestHashIffFrame` a THEOREM on the
  reachable subclass (`restHashIffFrame_of_fin`, honestly scoped — not claimed for infinite-support states).
- **R3-core** `e365d1c2d` — `finStep_denote` (the commuting square) for the **5 `FullAction` primitives**
  (balance/delegate/revoke/mint/burn) against the REAL `recK*` semantics. Scope corrected from the lane's
  "REAL effect algebra" overclaim: the other ~28 deployed effects are NOT covered.

REMAINING (in order):
1. **Converge with the VK-epoch roots.** `FinKernelState` must carry `nullifierRoot`/`revokedRoot` (`Fin 8 → ℤ`,
   FINITE domain — carried verbatim, no map) + the pending `commitmentsRoot` dual (`1dce9523c`). Currently
   DROPPED (`denote` defaults them ⇒ R2's root-clauses are vacuous-on-the-image). Fold into R4/R3.
2. **The delta fork FIRST** (`docs/reference/DELTA-FUTURE.md`). The deployed Rust is ALREADY delta-based
   (`ledger.rs`: `validate_delta` → `Vec<(CellId, CellStateDelta)>` → `apply_cell_delta`). The EffectsAsDataProto
   NO was against our nested-`if` model — the wrong shape. **De-risk the delta-refactor (one-effect prototype:
   transfer as `validateDelta`/`applyDelta`, measure whether `finTransfer_denote` goes `rfl`-ish + the circuit
   row aligns) BEFORE grinding the tactic.** If it composes → delta-refactor the kernel step (dissolves the whole
   per-effect cluster, more faithful). Else → the bridge (`denote_applyUpdates`) + a `refine_commutes` tactic is
   the honest ceiling for the current model.
3. **R3-continuation** — the remaining ~28 effects' commuting squares, via whichever model wins.
4. **R4** — re-seat `recStateCommit_binds_kernel` / the `CommitSurface` on `FinKernelState`; DROP
   `RestHashIffFrame` + `RestFrameDecodes2*` + `DeployedFaithful*` + `Satisfied2Faithful` from the carried set
   (now theorems); COLLAPSE the injectivity cluster (~1200) to the single `Poseidon2SpongeCR` floor.

### DEBT A — the STARK grind
Discharge `StarkSound`: model the deployed Plonky3/FRI-over-BabyBear verifier (AIR quotient check + FRI
low-degree test at the DEPLOYED field/rate/rounds + Poseidon2 Merkle openings), instantiate the field-generic
FRI folding lemma (`fold_close_of_two_alpha`) at BabyBear, prove `accept ⟹ ∃ trace, Satisfied2`, produce an
actual `instance : StarkSound`. Published (BBHR18 + the p3 design), not a research open; large, multi-brick.
NO opaque `verifyBatch` — model it.

### Then: the injectivity plumbing collapse (~1200 uses → the single floor).

## Discipline (paid for in a retraction, 07-09)
- **NAMING IS FAKING** — a `class`/`def : Prop` used as a hypothesis is an ASSUMPTION; `#assert_axioms` never
  inspects hypotheses. "Realizable, not faked" is the tell.
- **AUDIT BY TYPE**, not the lane's summary — read the signature (hidden carrier hypothesis?); is the MODEL the
  deployed thing (5-ctor `FullAction` ≠ 33 effects; `ZMod 5` ≠ BabyBear; scalar `verifyCore` ≠ ML-DSA)? A subset
  labeled complete is a lie — state the covered scope.
- **DATA REFINEMENT** — proof-easy model faithful to the efficient impl (sorted-nodup maps, delta-folds),
  connected by a PROVED refinement; the impl pays nothing.
- **WHOLE-TREE green must be REAL** (a genuine `lake build Dregg2` closure, not a toy single-file build).
  Sibling lanes' uncommitted WIP breakage is FLAGGED-not-owned-not-stashed (swarm-safe). Commit path-specific.
- Load-bearing both-truth `#guard` teeth. Honest scope in every commit + HORIZONLOG.
- A genuinely irreducible assumption gets NAMED as a floor item — that's the TCB, honest, not faking.

## DONE
Every DEBT-A and DEBT-B carrier is a PROVED theorem or a genuine floor item; the apex rests only on
`{Poseidon2SpongeCR, lattice/DL floor, leanc}`; whole tree GENUINELY green; and the retracted claims are
re-stated at their TRUE, audited scope in HORIZONLOG + memory.

## Current tree state (2026-07-09, ephemeral — verify at HEAD)
Whole-tree `lake build Dregg2` is intermittently RED from the VK-epoch nullifier lane's UNCOMMITTED WIP
(`CircuitCompletenessLifecycle` `sorryAx`, `Verify.Frames`, `Apps.VerificationToolkit`). My DEBT-B files verify
in their own closure (`FinKernelState` / `FinFrameHash` / `FinKernelStep`). Re-establish whole-tree green once
the sibling lane settles — not mine to touch/stash.

## Supporting docs (the hub)
- `docs/reference/CARRIER-CENSUS.md` — the carrier ledger (FLOOR / realized / PROVE? / REFINE?).
- `docs/reference/DEBT-B-FINITE-MAP-REFINEMENT.md` — the finite-map design + status.
- `docs/reference/DELTA-FUTURE.md` — the delta-based-kernel fork (the better model awaiting de-risk).
- `docs/reference/METATHEORY-GROUND-TRUTH.md` — where the real models live (read before modeling anything).

## Done-log (newest last)
- (start) plan written; supersedes the retracted verified-system campaign.
- ✅ census `c3d1a4ec8` · DEBT-B R1 `6458e10d2` · R2+R3-core `e365d1c2d` · DELTA-FUTURE `464692042`.
- ✅ STEP 1 ROOT CONVERGENCE `ca51d3fde` — FinKernelState carries nullifierRoot/revokedRoot (Fin 8 → ℤ, finite,
  verbatim); denote transports them; serializeRestFin BINDS them (List.ofFn + List.ofFn_injective) so
  serializeFin_injective stays TRUE; the 15→17 conjunct extensions landed; restHashIffFrame_fin residual STILL
  Poseidon2SpongeCR alone. Teeth: denote_carries_nullifierRoot (fires) + serializeFin_separates_nullifierRoot
  (bites — false before). THE VACUITY IS GONE. Whole tree GREEN 4530.
  (Also: FinFrameHash needed `import Mathlib.Logic.Equiv.Finset` — a concurrent import-slimming lane trimmed
  the Mathlib.Tactic umbrella from Crypto/Primitives.lean. Diagnosed by controlled test; not the roots.)
- ✅ STEP 2 DELTA DE-RISK (DeltaProto.lean, green 1432, audited by type) — **YES, with costs separated.**
  RECURRING square: ZERO per-cell by_cases (`denote_applyDelta` is effect-free, proved once). ONE-TIME migration
  lemma: 2 per-cell by_cases (disclosed, isolated); VANISHES under redefinition (guard split only). Blast radius
  of redefining the deployed ops: 150 files / 112 proof sites (re-derived independently).
  DECISION: adopt the delta model for R3-continuation (Option A, low risk); DEFER redefinition (Option B) as its
  own scoped campaign — 112 sites incl. the apex is not a DEBT-B move. Recorded in DELTA-FUTURE.md.
- ⚑ STEP 3 RE-PLAN (2026-07-10, per 'if a step reveals the plan is wrong, SAY SO'): the goal said '~28 effects'.
  GROUND TRUTH: `Dregg2/Circuit/Argus/Stmt.lean` defines `RecStmt`, a **19-constructor statement language**, with
  `interp : RecStmt → RecordKernelState → Option RecordKernelState` covering all 19 — and Argus contains **32
  `*Stmt` programs** (createCellStmt, cellSealStmt, bridgeMintStmt, exerciseStmt, attenuateStmt, …). The deployed
  effects are ALREADY compiled into RecStmt. So R3-continuation = prove `denote (finInterp s f) = interp s
  (denote f)` by induction on RecStmt (19 ctors, `seq` composes). Every effect inherits its square. Strictly
  stronger and cheaper than 28 bespoke proofs, and it fully discharges R1's `hpres` gate.
  ⚠ NAMED OBSTACLE (do not paper over): `setCell (T : Finset CellId) (leaf)` is already FINITE (touched-set T),
  but `setBal`/`setCaps`/`setLifecycle`/`setDeathCert`/`setDelegate`/`setSlotCaveats`/`setDelegations` each write
  a WHOLE total function of the state. An arbitrary infinite-support function cannot be stored in a finite map —
  DEBT-B's mismatch one level up, inside the statement language. Either the 32 real programs only ever pass
  finite-diff functions (then a `FiniteDiff` side condition discharges it) or those ctors need finite deltas.
  MEASURE which, per constructor. Do not assume.
- ◐ STEP 3 PARTIAL `e6344b504` — `denote_finInterp` PROVED over RecStmt's **10-ctor `Pure` fragment** + `seq`.
  7 whole-function writers have square lemmas gated on an explicit FiniteDiff hypothesis (NOT a carrier);
  `grant_finiteDiff` proves that obligation for one real program. **2 of 32** deployed `*Stmt` programs have
  proved squares. (The lane claimed '30 of 32 discharged' — an EXTRAPOLATION from machinery; corrected in the
  commit. R1's `hpres` gate is NOT yet discharged.)
  ✔ KEY MEASUREMENT (step 0, the point): every whole-function writer in the 32 real programs is used with a
    POINT diff off the current field — FINITE-DIFF ALWAYS. The infinite-support hazard is a RAW-CONSTRUCTOR
    artifact, not a property of the deployed effects. `setDelegate` has no real program at all.
  ⛔ `allocCell` BLOCKED precisely: its `bal` reset zeroes the whole `(newCell,·)` column across all assets — a
    predicate-erase, not a bounded Finset write. Fix = `filterErase`/`get_filterErase` on CanonMap. Blocks
    createCellStmt + createCellFromFactoryStmt.
- ✅ STEP 3A `80d4a2987` — `allocCell` UNBLOCKED. `SortedMap/CanonMap.filterErase` + `get_filterErase` (the
  predicate-erase the `(newCell,·)` bal column needs) + `denote_filterErase_bal`; `denote_finAllocCell` is
  **UNCONDITIONAL** (no side condition). `createCellStmt`/`createCellFromFactoryStmt` unblocked.
  ⚠ FAITHFULNESS BUG CAUGHT: step 3's comment said allocCell resets `cell` to `.record []` (an `erase`). WRONG —
  `(default : Value) = Value.int 0` (Exec/Value.lean:69), NOT the cell map's default `.record []`. It is an
  `insertNZ` of a non-default value. Erasing would have made `denote_finAllocCell` FALSE. Measurement caught it.
- ✅ STEP 3B `cbd3884de` — **28 of 30** deployed `*Stmt` programs have PROVED commuting squares (I COUNTED the
  `_square` theorems myself: 28, names verified). 11 FiniteDiff obligations PROVED as real theorems, never
  assumed — empirically confirming step 3's measurement that every deployed writer is a point diff. VACUOUS:
  `setDelegate` has no deployed program. COUNT CORRECTION: 30 distinct `*Stmt` terms, not 32 (`legStmt` aliases
  reduce to `balanceAStmt`). Teeth: `cellSealStmt_fires` + `cellSeal_notFiniteDiff_over_empty` (BITES).
  R1's `hpres` gate discharged for these 28.
- ✅✅ **STEP 3 COMPLETE** `63c904d56` — `createCellStmt_square` + `createCellFromFactoryStmt_square` proved, so
  ALL 30 deployed `*Stmt` programs have commuting squares and **R1's `hpres` gate is FULLY DISCHARGED for every
  deployed effect**. (`setDelegate` has no deployed program — a non-issue, not a gap.)
  ⚠ MEASURED SUBTLETY: `setCell`'s non-default obligation is GENUINELY FALSE when the factory lookup misses
  (the `none` arm writes back `k.cell newCell`, possibly `.record []`). So `finFactoryCell` is a `dite` —
  identity when absent. A uniform `finSetCell` would have been UNSOUND. Negative tooth
  `factoryCellWrite_can_be_default` proves it. Whole tree GREEN 4534.
- ✅ STEP 4 R4 `3b6ed68af` — `recStateCommit_binds_kernel_fin[_canon]`: on the reachable denote-image subclass,
  ALL FIVE carried hypotheses (4 injectivity + RestHashIffFrame) DISCHARGED to **`Poseidon2SpongeCR` ALONE**.
  `LeafRealization` CONSTRUCTED (CH_fin + finLeafRealization), not assumed — the census's un-realized carrier
  realized. Instantiable `_canon` form uses a SATISFIABLE sparse-map invariant; non-vacuity proved at finInit.
  ⚠ FINDING (`78d933d92`): `AccountsWF (denote f)` is UNSATISFIABLE because FinKernelState.cell defaults to
  `.record []` while the kernel default is `Value.int 0` — so the target-shape theorem is proved-but-vacuous.
- ✅ DEFAULT-ALIGN FIX `8cd504be3` — FinKernelState.cell default `.record []`→`Value.int 0` (kernel default),
  one motion across 7 committed files, whole tree GREEN 4536. `AccountsWF (denote finInit)` is now a POSITIVE
  proof (`finInit_accountsWF := fun _ _ => rfl`); `recStateCommit_binds_kernel_fin` is INSTANTIABLE (fires at
  finInit) — R4's vacuity CLOSED, `_canon` now redundant. finAllocCell's cell write flipped `insertNZ`→`erase`
  (born value = aligned default). No new vacuity. **DEBT-B core is proved AND non-vacuous.**
- ▶ THEN: drop RestFrameDecodes2*/DeployedFaithful*/Satisfied2Faithful where the squares discharge them; route
  the ~1200-use injectivity cluster through the poseidon2CommitSurface reductions. (`recStateCommit_binds_kernel_fin`: collapse the 5 carried hypotheses — 4 injectivity + 
  RestHashIffFrame — to `Poseidon2SpongeCR` ALONE, scoped to denote-images/reachable states, realizing
  `LeafRealization` rather than assuming it).
- ✅ INJECTIVITY COLLAPSE `d046dfb3d` — `injectivity_collapses_to_poseidon2CR`: all 4 CommitSurface injectivity
  carriers hold from ONE `Poseidon2SpongeCR` (LeafRealization CONSTRUCTED). `finCommitSurface` = the DEBT-B
  commit surface on that single floor. Teeth: collapse_fires + collapse_needs_CR (bites).
- ✅ `RestFrameDecodes2` `66e37b73f` — measured to be `= RestHashIffFrame.mp` (realized for 5 effects via
  `(hRest k k').mp h`), so on the SAME Poseidon2SpongeCR floor by R4's result. Not a separate carrier.
- 🏁 **DEBT-B CARRIER FAMILY DISCHARGED**: RestHashIffFrame + RestFrameDecodes2 + 4 injectivity + LeafRealization
  all PROVED/reduced to `Poseidon2SpongeCR` on the reachable subclass; Satisfied2Faithful/DeployedFaithful
  reclassified to DEBT-A (proven AIR, not finite-map). 30 deployed program squares proved (hpres discharged).
  Whole tree GREEN 4537. REMAINING (mechanical, NOT a carrier debt): re-thread the ~10 apex consumers through
  `finCommitSurface`/`RH_fin` (re-seat the apex on the reachable subclass — merges with DEBT-A). NEXT CAMPAIGN:
  DEBT-A StarkSound (owns the reclassified AIR carriers).

- ✅ INJECTIVITY COLLAPSE ROUTED `928df06b1` — `finCommitSurface_binds`: the apex `CommitSurface.commit_binds`
  instantiated at `finCommitSurface`, taking **ZERO injectivity hypotheses** (verified: 0 in signature) — equal
  Poseidon2 commitments ⟹ equal kernels, crypto residual `Poseidon2SpongeCR` + `RestHashIffFrame` (R4-discharged
  on the image) + satisfiable `AccountsWF`. The apex's generic consumers are PARAMETRIC over `CommitSurface`
  (S_live takes carriers as params = quantification, not carrier-assumption); instantiating at `finCommitSurface`
  discharges injectivity from `Poseidon2SpongeCR`. So "injectivity collapsed to one floor" holds on the DEBT-B
  apex binding path, routed, not merely standalone.
- 🏁🏁 **DEBT-B DONE at true scope.** Every DEBT-B carrier proved/reduced to `Poseidon2SpongeCR` on the reachable
  subclass (RestHashIffFrame, RestFrameDecodes2=`.mp`, 4 injectivity, LeafRealization constructed); injectivity
  collapse routed through the apex binding; 30 deployed program squares proved (hpres discharged); whole tree
  GREEN 4537. Two literal-DONE items were MEASURED-WRONG re-plans (not incomplete work): "33 effects" = 30
  deployed programs (setDelegate has none); `Satisfied2Faithful`/`DeployedFaithful*` are AIR/chip carriers
  (`extends Satisfied2`) → DEBT-A, proven not-DEBT-B. NEXT CAMPAIGN = DEBT-A `StarkSound` (owns those AIR carriers
  + the tree-wide AIR-path injectivity routing). Forcing those under "FINISH DEBT-B" would be forcing a plan the
  measurements showed wrong — the discipline forbids it.

## ⚠ EFFECT-COVERAGE CORRECTION (2026-07-10, stop-hook-forced)
"hpres discharged for EVERY deployed effect" was an OVERCLAIM. The 30 proved `*Stmt` squares cover the
RecStmt-expressible effects. SIX deployed Effect variants have distinct apply methods and NO proved square:
GrantCapability (apply_grant_capability), SpawnWithDelegation (apply_spawn_with_delegation), ShieldedTransfer
(apply_shielded_transfer), and Notify/React/Promise (Reactive "Track 2", turn/src/reactive.rs). Some MAY reduce
to covered machinery (React/Promise ↔ noteSpend/noteCreate nullifier set; GrantCapability ↔ grant), but that is
UNVERIFIED. hpres is discharged for RecStmt-expressible effects ONLY. This is a real remaining DEBT-B gap, not a
count quibble — the DEBT-B carrier result (RestHashIffFrame→Poseidon2SpongeCR) is unaffected.
- ✅✅ REACT PROVED `52a0ffd97` → COMPLETE 33-EFFECT CLASSIFICATION: {square-proved: 30 RecStmt + Grant + Spawn + React · off-kernel: Promise/Notify (reactive_registry≠kernel) · DEBT-A STARK: ShieldedTransfer}. DEBT-B finite-map coverage COMPLETE at true scope; tree green 4539.

## DEBT-A — in flight (StarkSound a THEOREM at BabyBear)
Ground (scouted): `class StarkSound (hash)(R):Prop` (CircuitSoundness.lean:382), 0 instances; content =
`verifyBatch accept ⟹ ∃ Satisfied2`. AIR→CircuitSound chain EXISTS modulo `FriProximity` (`circuit_sound_via_fri`,
AirSoundness.lean:234). `fold_close_of_two_alpha`/`friProximity_discharge` are field-generic + PROVED
(FriSoundness.lean, need only [Field][DecidableEq]) — the `ZMod 5` was the instantiation FIELD, not a limit.
- ✅ DEBT-A brick 1 `d8d78e59e` — BabyBear (p=2013265921) proved a prime FIELD + DecidableEq + 2-adicity EXACTLY
  27 (both-truth teeth); meets the FRI lemmas' typeclass requirements. FIELD-SWAP DE-RISKED: FRI-at-BabyBear is
  instantiation, not a proof frontier.
- ▶ brick 2: construct a BabyBear `FriSetup` (FriGeom σ/q/p/rep + RS codes C/C' + folding-completeness laws) at a
  real 2^k coset — mirror the ZMod 5 demo (FriSoundness.lean:455) at the DEPLOYED field; instantiate
  friProximity_discharge at it. brick 3: bind to deployed p3 FRI config + circuit_sound_via_fri → CircuitSound a
  THEOREM. brick 4: AIR-chip faithfulness (ChipTableSoundN over Poseidon2BabyBearW16) → instance : StarkSound.
- ✅ DEBT-A brick 2 `1d017a2a6` — `babyBearFriSetup : FriSetup BabyBear (Fin 4) (Fin 2)` over the DEPLOYED FIELD
  (real primitive 4th root i=1728404513, i²=-1); FriGeom + RS codes + folding laws PROVED;
  `friProximity_discharge` and `fold_close_of_two_alpha` INSTANTIATED (applied, verified by reading the proof
  terms). ⚠ |L|=4, NOT the deployed 2²⁷ domain — brick 3 binds the deployed domain size/rate/queries.
- ⚠ AUDIT FINDING `810d0dc65` — `Satisfied2Faithful`'s four "realizations" use `permOutZ = fun _ => replicate 0`
  (the CONSTANT-ZERO perm, FloorsNonVacuous.lean:108), which also forces `hash = 0`. They are NON-VACUITY
  witnesses, NOT a deployed discharge. 26 sites still assume it. The census's `realized=0` was wrong in count and
  right in spirit.
- ▶ brick 4 (in flight): realize `Satisfied2Faithful` at the REAL `Poseidon2BabyBearW16.perm` (deployed, KAT-
  validated bit-exact) — permWidth / chipHashIsLane0 / ChipTableSoundN over the genuine chip. If the deployed
  hash is NOT lane 0 of the real perm, that FALSE obligation is the finding.
- ⚠⚠ DEBT-A CARRIER AUDIT `96f9fd9a5` (spot-verified by hand) — the STARK core is UN-DEPLOYED everywhere:
  `StarkSound`'s apparent instance is LAUNDERING (FriVerifierBridge builds it from `[carrier : AlgoStarkSound]`
  taken as a HYPOTHESIS; AlgoStarkSound has 0 instances). `FriExtract`'s sole realization is over
  `witVerify := fun _ => true` (ACCEPT-EVERYTHING). `ChipTableSoundN`: 0 realizations at the deployed perm, 139
  hypothesis sites. `FriProximity` = a NAME COLLISION with NO bridge term. Counts: NON-VACUITY-ONLY 3 · ASSUMED 5
  · DISCHARGED-AT-DEPLOYED 3 (ChipTableSound legacy, RangeTableSound, GuardDecodes2 — the AIR support layer is
  genuinely real) · FLOOR 2. Doc: docs/reference/DEBT-A-CARRIER-AUDIT.md.
  ⇒ DEBT-A MUST PROVE: ChipTableSoundN @ real perm · FRI proximity @ deployed params · the FriProximity bridge ·
  a real per-node FriExtract · an actual instance : StarkSound not routed through assumed AlgoStarkSound.
- ✅ ShieldedTransfer `d2b7b2dea` — kernel part PROVED (shieldedTransferK_accepts/_balNeutral). ⚠ CORRECTED MY OWN
  CENSUS: its kernel mutation is NULLIFIER-ONLY (no transparent balance move; amount is hidden Pedersen).
  ⚠⚠ DEPLOYED SOUNDNESS GAP `e32564ce0`: apply.rs:1178 — "M2-a relies on the honest prover for it
  (verify_value_link)". The leaf↔leg value-link is UNVERIFIED in the shipped system. Not a floor item.
  `starkResidual_of_floor` named honestly as MODUS PONENS (reduction shape, no content).
- ✅ reactive subsystem `515f635d9` — OFF-KERNEL is now a THEOREM (promise/notify_kernel_unchanged : k' = k), and
  `no_double_react` PROVED by RIDING the committed nullifier gate (note_no_double_spend), not re-modeling it.
  Unmodeled deployed behaviour named: resolve_condition temporal gate, expire block-height, cascading resolution.
- ✅✅ DEBT-A brick 4 `37b121f55` — **the permOutZ finding is CLOSED**: permWidth / chipHashIsLane0 /
  chipTableFaithful ALL PROVED at the REAL `Poseidon2BabyBearW16.perm` (KAT bit-exact); `satisfied2Faithful_
  deployed` constructs the full object for transferV3 at the deployed pair. chipHashIsLane0 is TRUE for the
  deployed pair (Ir2Air::Chip returns state[0]; KAT lane 0 = 1906786279 ≠ 0). Teeth include the vacuity contrast
  vs permOutZ. Closes DEBT-A obligation #1 of 5.
- ◐ DEBT-A brick 5 `d569bf31e` — AIR quotient acceptance PROVES rowConstraints' ARITHMETIC arms (+ the whole
  thing for embedV1-shape descriptors); 8 legs remain as EXPLICIT VISIBLE PREMISES (not carriers): LogUp bus,
  map-ops AIR, RangeTableSound, chip table (now discharged by brick 4), LogUp balance, table-assembly
  faithfulness, memory-table AIR. Half-(ii) companion to circuit_sound_via_fri.
- ⚠ DEBT-A StarkSound target `585c71894` — the bridge grew the trusted surface from ONE to TWO: AlgoStarkSound
  (F=Int not BabyBear, abstract params, 0 instances) + DeployedRefines (never proved, taken as `href`);
  `starkSound_of_verifyAlgo` = `carrier.extract ∘ href`. Doc-comment "PROVEN verifier algorithm" corrected in-file.
  DEBT-A obligations: #1 ✅ · #2 FRI@deployed-params (in flight) · #3 FriProximity bridge (in flight) · #4 real
  FriExtract (in flight) · #5 DeployedRefines (NOBODY has attempted — firing now).
- ◐ DEBT-A brick 3 `c9e8439ad` — FRI proximity INSTANTIATED at the deployed RATE (log_blowup=3 ⇒ 1/8, |L|=16) and
  at the 2-adicity cap (|L|=2^27, ω=31^15 via a 26-step squaring chain); geometry axioms proved GENERAL in m.
  ⚠⚠ THREE measured limits: deployed domain size is PER-PROOF (trace_height<<log_blowup), not static; **our fold
  is ARITY-2 (squaring quotient) while the deployed PROD_FRI_MAX_LOG_ARITY=3 folds up to 8-to-1** (a sixth
  obligation, `b404d4b9f`); the `FriProximity` name-collision has NO bridge (AirSoundness doesn't even import
  FriSoundness) — bridge statement now PRECISE, `hFRI` half supplied, `hcode_sat` open,
  `air_binds_of_proximity` is the proved codeword half.
- ⚠⚠ DEBT-A #4 REFRAMED `3ee8b5ee8` — `FriExtract` is a KNOWLEDGE-EXTRACTION obligation, NOT a FRI one:
  friProximity_discharge takes a transcript ⟹ a property; FriExtract takes a property ⟹ must yield a witness.
  **The direction is wrong** — no FRI work discharges it (needs in-circuit⟹native extraction + oracle_binding).
  Also PROVED: the committed `wit_friExtract` is ACTIVELY HOLLOW (`degenerate_extracts_absurd` certifies a
  time-reversed `brokenSeg`, lastNew = -999). A non-degenerate instantiation exists but its FriExtract is a
  TAUTOLOGY at its CVS (`the_gap_is_reflection`) — stated plainly, not claimed as a discharge.
- ⚠⚠⚠ DEBT-A TRUE BLOCKER `77d4b27cc` — modeling `verifyBatch` discharges only the CODE half
  (DeployedRefines/DeployedMatchesModel, KAT-dischargeable via the existing dregg-lean-ffi harness+goldens).
  `AlgoStarkSound.extract` contains `FriExtract` = a PROOF-OF-KNOWLEDGE obligation FRI cannot manufacture.
  **Modeling verifyBatch does NOT finish DEBT-A.** The blocker is knowledge extraction, not FRI soundness.
- ⚖ METHOD near-miss, recorded: a lane claimed "Merkle is STUBBED true — dangerous"; I nearly committed it. FALSE
  — `friQueryCheck` calls `merkleVerify := decide (merkleRecompute … = root)`, ON the accept path. `merklePaths`
  is a REDUNDANT field, as its doc-comment says. I read a SHAPE instead of the ARGUMENT. The rule cuts both ways.
  VERIFIED GOOD: `fullChecks` implements every verifyAlgo sub-check for real — that claim checks out.
- ✅✅ DEBT-A #6 CLOSED `3ab1c78ed` — `fold_close_of_arity_challenges` PROVED for GENERAL arity `n`
  (derived constant `n²·d`; at n=2 it recovers the committed `4d` exactly — a real consistency check), via the
  size-`n` Vandermonde (`det_vandermonde_ne_zero_iff`). INSTANTIATED at the deployed `n = 8`
  (`PROD_FRI_MAX_LOG_ARITY = 3`) over BabyBear; the new fiber-distinctness axiom is PROVED for BabyBear from
  `omega16`'s order, not assumed. Teeth: honest word reconstructs (fires); the frequency-8 far word admits NO 8
  distinct good challenges (bites). Soundness distance degrades `n²·d` — priced, not hidden.
  ⇒ Obligations: #1 ✅ · #2 ◐ · #3 in flight · #4 REFRAMED (PoK, above FRI) · #5 reduces to DeployedMatchesModel
  (KAT) · #6 ✅. **The FRI side is nearly done; the blocker remains knowledge extraction.**

## ⚠ CORRECTION (2026-07-10): FriExtract blocks the RECURSIVE apex, NOT single-batch AlgoStarkSound
I published (`77d4b27cc`) that "AlgoStarkSound.extract contains FriExtract, so modeling verifyBatch does NOT
finish DEBT-A." **That was wrong, and it was my amplification of a lane's conflation.** Reading the actual
statement (`FriVerifierBridge.lean:79`): `AlgoStarkSound.extract : verifyAlgo … = true → ∃ minit mfin maddrs t,
Satisfied2 hash (R pi.effect) … t ∧ tracePublishedCommit t = pi.toPublished`. It produces a satisfying **VmTrace**
— the classic STARK soundness argument (FRI proximity ⟹ a low-degree codeword; Merkle binding ⟹ the opened trace
IS that codeword; AIR ⟹ it satisfies the constraints). **No `FriExtract`.**
`FriExtract` (AggAirSound.lean:25-30, its own words) is "the in-circuit RECURSION-verifier subcircuit's soundness,
the standard SNARK-of-a-fixed-verifier obligation" — it yields a verifying CHILD PROOF. It appears ONLY in
recursion/aggregation files; `CircuitSoundness.lean` references it **zero** times.
⇒ **CORRECTED PICTURE:** single-batch `AlgoStarkSound` IS reachable from the bricks: #1 ChipTableSoundN @ real
perm ✅ · #2 FRI proximity @ deployed rate ◐ · #6 arity-2^k @ deployed 8-to-1 ✅ · #3 the bridge (in flight) ·
AIR soundness (`d569bf31e`, partial) · Merkle binding (REAL, `merkleVerify := decide (merkleRecompute … = root)`,
on the accept path). Then `StarkSound = AlgoStarkSound + DeployedRefines`, and `DeployedRefines` reduces to
`DeployedMatchesModel` — a KAT-dischargeable Rust↔Lean correspondence with the harness already built.
`FriExtract` is a SEPARATE campaign: the recursive/aggregated apex (proof composition).
- ✅ DEBT-A #3 PROVED — `friProximity_bridge` under 3 EXPLICIT hypotheses (hFRI supplied at deployed field+rate;
  hplumb = Merkle binding → HashCR; hcode_sat with `g` LOAD-BEARING). `deployedRate_circuit_sound` composes
  `circuit_sound_via_fri` at the deployed field+rate. ⚖ The lane REFUSED the degenerate `hcode_sat` I propagated
  (bound `g` unused ⇒ holds-by-unfolding) and fixed it. Teeth: honest decoder fires; a lying decoder BITES.
  ⚠ Bridge is at the ARITY-2 setup; #6's arity-8 lemma is proved but not yet threaded through it.
  ⇒ #1 ✅ · #2 ◐ · #3 ✅ · #4 = RECURSION (separate campaign) · #5 = DeployedMatchesModel (KAT) · #6 ✅
- ◐ DEBT-A deployed-ARITY through-line PROVED (`FriBridgeDeployedArity.lean`) — real TYPE obstruction found
  (`FriSetupK n` ≠ `FriSetup`; `FriGeom` hard-wires arity-2) and honestly generalized (`friProximity_bridgeK`,
  a line-for-line mirror), NOT coerced. `friProximityK8_discharge` is the keystone APPLIED.
  ⚠ It runs at `d = 0` (oracle IS a codeword), where the arity constant `64d` vs `4d` is INVISIBLE — so #6 is
  proved but NOT exercised. Real FRI gives δ-closeness (`d>0`); the quantitative soundness bound at
  num_queries=38 / log_blowup=3 is NOT derived. Named.
- ◐ AIR half `7cbbee624` — 6 of 8 premises DISCHARGED at deployed transferV3 (structurally: hashSites=[],
  ranges=[], memLog=[]). ⚠ I made a CATEGORY ERROR (Satisfied2 has no chip-table field; that's Satisfied2Faithful
  — so brick 4 serves the 26 faithfulness sites, NOT AlgoStarkSound). Remaining: `hbus` + table-emptiness.
- ⚠⚠ #7 NEW: **LogUp bus soundness is UNMODELED** (`Lookup.lean`: "that lives in the Rust AIR, not in this
  semantics"); no `logupCumSum` soundness theorem exists. Next real blocker; PROVABLE (Haböck + Schwartz–Zippel).
  In flight: a077860d494fcca5b.
- ✅ DEBT-A #2 FRI sampled-query soundness `da3a8fcd4` — `accept_prob_le : δ-far → |accepting|/|ι|^k ≤ (1−δ)^k`;
  deployed k=38, δ=7/16 (unique-decoding, NOT Johnson/BCIKS20), error < 2⁻³¹. Lane checked the SHIPPED sampler
  (fri/verifier.rs:266 — independent, WITH replacement) → the model is FAITHFUL, corrected my prose. Closes the
  Q=univ finding; `arity_constant_bites` makes #6's 64d load-bearing (d>0). Residual: union-bound→transcript-
  measure wiring.
- ✅ DEBT-A #7 LogUp bus soundness `da3a8fcd4` — Haböck log-derivative: forged lookup ⇒ busNum ≠ 0 ⇒ balances only
  on exceptionalSet card < |A|+|B|; BabyBear error (|A|+|B|)/2013265921. The obligation the retracted "lives in the
  Rust AIR" comment (`47e244c38`) hid. Residual: REDUCES hbus, doesn't discharge — the deployed bus COLUMN LAYOUT
  is unmodeled; single-occurrence case only.

## DEBT-A state (2026-07-10 noon) — the crypto-math is largely proved; the remainder is WIRING + an architecture call
PROVED: #1 ChipTableSoundN @ real perm (serves Satisfied2Faithful) · #2 FRI query soundness · #3 FriProximity
bridge · #6 arity-2^k @ deployed 8-to-1 · #7 LogUp bus soundness. AIR half: 6/8 premises @ transferV3.
REMAINING, and NONE is a research open — they are composition + a decision:
- WIRING (mechanical, real): union-bound→transcript measure (#2); bus column layout (#7); hplumb (Merkle→HashCR)
  + hcode_sat (#3); thread these into one `instance : AlgoStarkSound`.
- ⚠ ARCHITECTURE DECISION (ember-gated): `verifyBatch` is `opaque` (CircuitSoundness:353). To get `StarkSound` as a
  THEOREM, either (A) DEFINE `verifyBatch := verifyBatchModel` and carry `DeployedMatchesModel` as a KAT
  correspondence (harness EXISTS: dregg-lean-ffi + goldens; import-cycle + 25/42-file ripple), or (B) keep it
  opaque and name `StarkSound` as an explicit floor/TCB item. This is a design choice, not a proof.
- SEPARATE CAMPAIGN: #4 FriExtract (the recursive/aggregated apex — a knowledge-extraction obligation, not FRI).

## ★★★ THE DEBT-A KEYSTONE (2026-07-10, `b064b99b9`, verified by type): the FRI tower lands on a TOY VM
`circuit_sound_via_fri` / `friProximity_bridge` conclude over `applyEff : Effect → State → State`, `Step State
Effect`, payload `satisfiesTransition` (single functional step `new = applyEff eff old`) — ABSTRACT types.
`MainAirAccept (hash)(d : EffectVmDescriptor2)(t : VmTrace)` is over the DEPLOYED trace. **No committed term :
`verifyAlgo … = true → MainAirAccept … t`.** So #2 (query soundness) + #3 (bridge) + #6 (arity) are real math for
a TOY single-step VM, NOT the deployed 16-column BabyBear AIR. `ZMod 5 ≠ BabyBear`, one level up.
⇒ `StarkSound` is NOT "a KAT correspondence away." The real keystone is `verifyAlgo @ fullChecks accepts ⟹
MainAirAccept hash d t` over the DEPLOYED trace, and its argument is NOT `circuit_sound_via_fri` — it is the OOD
QUOTIENT-CONSISTENCY step: verifyAlgo checks `C(ζ) = Z_H(ζ)·q(ζ)` at a random OOD ζ AND FRI proves q low-degree ⟹
(Schwartz–Zippel on ζ, err ≤ deg/|F|) `C = Z_H·q` as polynomials ⟹ C vanishes on H (the trace rows) ⟹
MainAirAccept. The FRI low-degree half is banked (#2); the OOD-ζ consistency over the deployed descriptor is the
unwritten keystone. Same SHAPE as DEBT-B's finite-map refinement (make the proof faithful to the deployed object).
The `MainAirAccept ⟹ Satisfied2` half is already proved (6/8 legs @ transferV3, `AirLegsDischarged`).
- ★ DEBT-A KEYSTONE FORK ANSWERED `6f1ac8baa` — `verifyAlgo accepts ⟹ MainAirAccept` does NOT compose as one
  term. Both flanking halves PROVED (accept⟹OOD-identity via the committed reject theorem's contrapositive;
  ood_consistency = Schwartz–Zippel over Polynomial F). FORK VERDICT (by type): `arithResidual` is RAW ℤ, not a
  Polynomial ⟹ the keystone is K′ (the toy→deployed VM refinement, DEBT-B-shaped). Gap reduced to a clean
  three-axis bridge `OodInterpZ`, decomposed in DEBT-A-OBLIGATIONS.md: (a) field-vs-ℤ canonical lift, (b) trace-
  column interpolation as Polynomial BabyBear (the core), (c) constraint-batching RLC (a 2nd SZ step). Each a
  separable codex-grindable goal. Carrier-free; teeth both-truth; non-vacuous landing.

## ⚠⚠ DEBT-A K′(a) FINDING (2026-07-10, `e5820e030`, codex-proved + type-gated): committed MainAirAccept-over-ℤ is the WRONG MODEL
The committed `MainAirAccept`/`arithResidual` (my brick-5 `d569bf31e`, over raw ℤ) is a MODELING MISMATCH:
strictly STRONGER than the deployed field AIR, and FALSE for honest traces. Proof: `mainAirAcceptF_does_not_imply
_MainAirAcceptZ` — the deployed gate `((col₀+col₁)*col₂)` at canonical columns `(p−1,1,1)` (all in [0,p),
p=2013265921 prime) has integer residual `p ≠ 0` but BabyBear residual `0` (intermediate `(p−1)+1 = p ≡ 0`). So
`≡0 mod p ⇏ =0 over ℤ` for compound multiplicative gates; additive/transition arms DO lift. The deployed prover is
over BabyBear — its constraints ARE field constraints; raw-ℤ was the artifact. FIX (in progress, ADDITIVE): the
field-faithful chain `MainAirAcceptF ⟹ Satisfied2`, fed by K′(a) `ood_forces_mainAirAccept_field` + K′(b)
`constraintPoly` — built alongside; the ℤ chain (AirChecksSatisfied/AirLegsDischarged/AlgoStarkSoundInstance)
retired at cutover, not mutated in place. This is a faithfulness correction toward the deployed object.
- ★★★ MOD-P REFACTOR SCOPED (codex investigation, gated + doc moved to docs/reference/DEBT-A-MODP-DENOTATION-SCOPE.md):
  BENIGN-GAP CHECK = refactor REQUIRED (Rust canonicalizes cells, circuit/src/field.rs:14-17, but NO invariant
  bounds ℤ residuals — the deployed 3-term affine gate still reaches p; I confirmed no %p/ZMod cast at envAt).
  RIPPLE = ~220 files (spot-checked: 147 touch Satisfied2, 168 touch holdsAt/holdsVm) — 3 AIR-chain · 17 apex/
  soundness · 179 descriptor/refinement · 14 non-vacuity · 7 core. RECOMMENDATION = A2 (additive field denotation
  → cutover), required; first reviewable slice 7-12 files; full retirement 185-220. Riskiest = per-effect proofs
  that derive ordered-ℤ conclusions from holdsAt. Acceptance = grep-zero old Satisfied2 on the StarkSound/apex
  path + a differential (residual p in ℤ, 0 in BabyBear). ⚠ EMBER-GATED: the 220-file GO is foundational.

## ★ CAMPAIGN: REAL all-effects STARK assurance (plan approved 2026-07-11; ~/.claude/plans/let-s-plan-it-out-glimmering-bubble.md)
Ground-truth mapped (3 Explore passes): STARK layer is fake (opaque verifyBatch, toy VM disconnected from VmTrace,
ℤ denotation, 1-effect faithfulness, 0 real StarkSound instances); kernel-refinement (DEBT-B) is genuinely
all-effects. Phases: 0 field denotation → 1A land FRI on real VmTrace → 1B model verifyBatch (Model+differential,
ember-chosen) → 2 all-effects breadth → 3 apex. Execution: opus+fable Agent lanes grind (codex tapped out), I gate
every file by type; heap-safe (NO decide/Fintype over ZMod p — a 144GB process was killed); shared tree, targeted
builds, whole-tree green at phase end.
### Phase 0 (mod-p denotation) — IN PROGRESS, dependency-ordered fan-out
- The fix: holdsVm/holdsAt constraint `= 0` (ℤ) → `≡ 0 [ZMOD 2013265921]` (Int.ModEq, the DEPLOYED field). Values
  stay canonical ℤ in [0,p) (range checks provide the ℤ-order canonicality); retargeting Assignment→ZMod p would
  LOSE the order — wrong. Negative teeth gain explicit `0 ≤ cell < p` canonicality (real deployed invariant),
  proving ¬(p∣residual) via babyBearP_prime + omega. Intent predicates (TransferRowIntent…) become mod-p
  congruences — MORE faithful (deployed computes over the field), ripples to refinement consumers.
- ✅ core `31afaaac1` (EffectVmEmit + DescriptorIR2) · ✅ Transfer `db063eb4e` (intents→mod-p, 3 teeth kept).
- The 29 per-effect Emit files are a DAG (EffectVmEmitTransferSound is the hub, ~20 import it). Topo order:
  core✓ → Transfer✓ → Wave A {TransferSound, CapRoot, EscrowRoot} (in flight) → Wave B ~20 dependent effects →
  Wave C variants (*Runnable/*FullState/*Wide/*Refine/*Rung2). Gate each: teeth kept, canonicality real, 0 sorry,
  heap-safe. Lanes must REPORT blockers, never spawn watchers (one Mint watcher was killed).

### Phase 0 fan-out — accurate topology (2026-07-11): 74 Emit files, 9 layers
7 green (core/Transfer/TransferSound/CapRoot/EscrowRoot/Mint/IncrementNonce). 67 remaining, topo-ordered:
L1(23, frontier now): BilateralAgg Bridge BundleFold Burn CapReshape CellDestroy CellSeal CrossSide EmitEvent
  Exercise HeapRoot IvcStateTransition PipelinedSend RecordRoot Refusal SetField SetPermissions SetVK TransferUnify
  UMemCohort/Multi UMemWeldWide FullStateRunnable · L2(19): AttenuateA BridgeMint NoteSpend NoteCreate CellUnseal
  +variants · L3(8): Delegate DelegateAtten Introduce NoteSpendCompose RefreshDelegation RevokeCapability
  RevokeDelegation IvcRung2 · L4(7): CreateCell CreateCellFromFactory MakeSovereign ReceiptArchive Spawn V2 · L5-9:
  FullState/Wide variants + Rotation chain (RotationV3 is the big one).
~half are negative-teeth (real canonicality work, opus+full gate); the rest hash-site/mechanical (ride free like
CapRoot, fable+quick gate). Batch ~5/wave, gate each, commit green, advance the frontier. Lanes report blockers
(RevokeDelegation blocked cleanly — mis-batched as frontier, it's L3). Then the intent-mod-p consumers in the
refinement layer (RotatedKernelRefinement etc.) + AirChecksSatisfied/arithResidual, then whole-tree green.

### ⚠ SCOPE CORRECTION (2026-07-11): the Emit family is ~162 files, not 74
My earlier topo counted only `EffectVmEmit*`-prefixed files (74). The real `Dregg2/Circuit/Emit/` dir has ~162
.lean files, including a `*OpenEmit`/accumulator/carrier family (CapOpenEmit=9 holdsVm refs, HeapOpenEmit,
FieldsOpenEmit, AccumulatorInsertEmit, CarrierComposed=6, CapOpenTurnPins) that ALSO needs mod-p migration. So
Phase-0's Emit surface is ~2× estimated. Mitigations: (a) the migration pattern is fully mechanized (mod-p intent +
canonicality envelope for teeth; mechanical thread for wrappers; hash-site files ride free); (b) ~⅓-½ ride free;
(c) per-file type-gate stays for SECURITY files, lighter batch-gate for hash-site/mechanical. Progress so far: ~56
EffectVmEmit* files green (Layers 1-5) with every security keystone (double-spend, capability non-amplification
end-to-end, memory-index-exact, anti-ghost rotation binding) verified conclusion-verbatim-intact. Remaining:
RotationV3 (keystone, in flight) + RotationV3Refused/Wide + the OpenEmit family + any other EffectVm* stragglers,
then the refinement-layer ripple + AirChecksSatisfied/arithResidual, then whole-tree green. This is a multi-hour
grind — expected for making a fake-verified system real.

### ★ MILESTONE (mid-migration, 2026-07-11 ~16:00): ~95 Emit/decider/Deos files green + a REAL security finding
Phase-0 mod-p field-denotation migration, ~95 files committed green (dependency-ordered, every file type-gated):
all EffectVmEmit* effects + FullState/Wide/Runnable variants; the Rotation chain incl. the 381KB transferV3
KEYSTONE (RotationV3) + RotationWide; both decision procedures (InterpCore, DecideSatisfied2) with bidirectional
decide↔denotation equivalence preserved; 8 Deos settle/escrow/authority-floor files; the membership/derivation/
threshold/fold/garbled/bilateral-agg refine+rung2 ladders. EVERY security keystone verified conclusion-VERBATIM-
intact: double-spend (nf∉nullifiers), capability non-amplification (grantedBit=0∨heldBit=1) across the whole
Attenuate→Delegate→Revoke→Refresh chain, memory-index-EXACT (∃j<8, slot=j not residue), anti-ghost rotation/
authority bindings, UniqueAgent, membership-under-root. Zero permOutZ toy reintroduced. Real bugs FOUND+FIXED:
over-p Merkle/Blinded witness hashes (base-100→10), stale geometry offsets (56→59, 169→178), a genuinely-false-
over-ℤ comparator (gteHonestDiff).
★★★ THE PAYOFF: the migration surfaced a REAL, VERIFIED, high-severity soundness gap in the DEPLOYED (STAGED) vault
settlement circuit — VaultSatDescriptor's 16-bit product carries can wrap p (2^15·61440+1 = p exactly), letting a
malicious prover forge a share-inflating settlement past the no-dilution gate. The ℤ model SILENTLY FAKED this
conservation; the field-faithful model refused to prove it. VaultSatDescriptor.lean STAYS RED (the honest state).
STAGED (not live VK), fix = CARRY_BITS 16→15 in both twins + VK/fixture regen — EMBER-GATED (deployed circuit +
staged VK epoch). Doc: docs/reference/VAULT-CARRY-WRAP-INVESTIGATION.md (verdict A, verified by hand).
REMAINING to close Phase 0: the OpenEmit/Argus families (in flight) + a whole-tree green pass to catch stragglers +
the AIR chain (AirChecksSatisfied/arithResidual — the Phase-0→Phase-1 boundary). Then Phases 1A/1B/2/3.

### ★★★ HEADLINE: the migration found TWO live deployed soundness gaps + a wrap-CLASS (2026-07-11)
The mod-p field-faithfulness migration surfaced TWO confirmed (verdict A) soundness gaps in the DEPLOYED circuit,
both of the same CLASS (a gate reconstructs a value ≥ p; mod-p alone doesn't pin the ℤ value; adversary picks a
p-shifted decomposition):
1. VAULT carry-wrap (`27feb4754`, `VAULT-CARRY-WRAP-INVESTIGATION.md`) — 16-bit product carries reach 2^31 > p ⟹
   forge a share-inflating settlement past the no-dilution gate. STAGED (not live VK). Fix: CARRY_BITS 16→15.
2. CAP-OPEN mask-recon (`5cfa7e5d7`, `MASK-RECON-WRAP-INVESTIGATION.md`) — 32-bit mask recomposition, 2p < 2^32 ⟹
   CAPABILITY-AUTHORIZATION FORGERY: a cap granting nothing authorizes a transfer (decompose 2p into the free-
   witness mask bits). Fix: range-check mask_lo/mask_hi < 2^16 + per-16-bit-limb reconstruction.
Both EMBER-GATED (deployed circuit changes). WRAP-CLASS audit: these 2 are the only live instances found so far
(CapReshape 8-bit safe; RotationWide Poseidon2-absorb safe) — but the CLASS is now a known audit axis for the rest
of Phase 0 + a candidate for a systematic sweep of the whole deployed circuit.
⚠ GATE LESSON (my error, corrected): I first committed CapOpenEmit green treating `reconExact` as a "canonicality
envelope" — it actually ASSUMES the wire's ℤ-exactness (laundering the gap). Corrected: relabeled as an explicit
DEPLOYED-GAP assumption. LESSON: when gating an envelope, check WHERE its exactness comes from (deployed wire =
real invariant; hypothesis = assumed gap) — an explicit hypothesis is only honest if NAMED as a gap, not dressed
as a canonicality. This is the anti-toy discipline applied to my own integration.
THE POINT PROVEN: a "verified" circuit modeled over ℤ silently believes conservation/authorization the real field
circuit does NOT enforce. Field-faithfulness makes those gaps unignorable. Two are now found + verified.
