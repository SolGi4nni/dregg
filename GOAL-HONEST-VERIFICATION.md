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
