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
- ▶ NEXT: STEP 2 the delta de-risk (one-effect prototype) — decides delta-refactor vs bridge+tactic.
