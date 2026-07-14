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

## ⚠⚠ DEBT-A AUDIT HEADLINE (2026-07-10) — the STARK core is un-deployed everywhere
Full table: `docs/reference/DEBT-A-CARRIER-AUDIT.md`. I spot-verified the three load-bearing rows MYSELF:
- **`StarkSound`'s "instance" is LAUNDERING.** `FriVerifierBridge` builds `StarkSound hash R where extract :=
  carrier.extract …` from `[carrier : AlgoStarkSound …]` **taken as a hypothesis**, and `AlgoStarkSound` has
  **ZERO instances**. It reads as a discharge; it is a relabel onto an assumed carrier that `#assert_axioms`
  cannot see. (`feedback-no-named-carrier-laundering`: relabeling ≠ fixing.) StarkSound = ASSUMED.
- **`FriExtract`'s sole realization is VACUOUS.** `wit_friExtract` (AggAirSound.lean:266) is over
  `witVerify : WitProof → Bool := fun _ => true` (:256, ACCEPT-EVERYTHING) and `witCVS := fun _ _ => True` (:261).
- **`ChipTableSoundN`: ZERO realizations at the deployed permutation** (all use `permOutZ = fun _ => replicate 0`
  or `witnessPerm = fun _ => [K0,0,…]`); 139 hypothesis sites. Even `activeChipTbl_sound` uses `permOutZ`.
- `FriProximity` is a NAME COLLISION: `AirSoundness.lean:219` (verifyLD ⟹ transition; ASSUMED-only) vs
  `FriSoundness.lean:403` (`closeN S.C d f`; discharged but only at the ZMod 5 / Fin 4 / rate-1/2 toy).
  **No bridge term exists** between them — yet `circuit_sound_via_fri` needs exactly that bridge.
COUNTS: NON-VACUITY-ONLY 3 (ChipTableSoundN, FriExtract, FriProximity-FriSoundness) · ASSUMED 5 (StarkSound,
AlgoStarkSound, FriLowDegreeSound, EngineSound, FriProximity-AirSoundness) · DISCHARGED-AT-DEPLOYED 3
(ChipTableSound legacy 1-felt, RangeTableSound at deployed rangeRows, GuardDecodes2 at ~20 real effect specs —
the AIR SUPPORT layer, genuinely good) · FLOOR 2 (Poseidon2RealizedSponge, QROMInjective).
**WHAT DEBT-A MUST ACTUALLY PROVE:** ChipTableSoundN at the REAL Poseidon2BabyBearW16 perm · FRI proximity at the
deployed BabyBear params · the FriProximity bridge · a real per-node FriExtract · then an ACTUAL
`instance : StarkSound` that does not route through an assumed AlgoStarkSound.

## ⚠⚠⚠ DEPLOYED SOUNDNESS GAP (2026-07-10) — ShieldedTransfer's value-link trusts the prover
Found while scoping ShieldedTransfer (`d2b7b2dea`). **`turn/src/executor/apply.rs:1178`, the shipped code's own
comment:** "secret opening; **M2-a relies on the honest prover** for it (the `verify_value_link` …)". The
leaf↔leg value-link is NOT verified — deployed soundness rests on prover honesty at that step. This is NOT a
proof-modeling artifact and NOT a floor item: it is a gap in the SHIPPED system, orthogonal to StarkSound.
Distinct from the Lean carriers; needs a product decision (verify the link, or document the trust assumption).

## correction (2026-07-10): ShieldedTransfer's kernel mutation is NULLIFIER-ONLY
I previously recorded it as "nullifier + balance". WRONG. `apply_shielded_transfer` performs NO transparent
balance move — the amount is a hidden Pedersen commitment checked by `verify_full_conservation_bytes`; the
transparent move is the separate `Unshield` effect. The kernel part is iterated noteSpend-nullifier (the exact
primitive DEBT-B covered). Proved: `shieldedTransferK_accepts` + `shieldedTransferK_balNeutral` (bal/commitments/
cells/caps/revoked all unchanged). Corrected by reading the deployed code, not by trusting my own earlier note.

## ⚠⚠ DEBT-A STARKSOUND TARGET (2026-07-10) — the bridge grew the trusted surface from ONE to TWO
Spec: `docs/reference/DEBT-A-STARKSOUND-TARGET.md`. Verified by hand at `FriVerifierBridge.lean`:
- `class AlgoStarkSound (hash : List Int → Int) …` (:75) — `F = Int`, **NOT BabyBear**; `perm`/`params`/`vk`/
  `checks`/`view` are ABSTRACT binders, never pinned to the deployed config. **ZERO instances.**
- `DeployedRefines` (:92) — a `def` (`verifyBatch accept → verifyAlgo = true`), **never proved**; taken as the
  hypothesis `href` at :112/:131/:167. ASSUMED.
- `starkSound_of_verifyAlgo` (:114) — PROVED, but its body is `carrier.extract ∘ href`: modus ponens over the
  two assumptions above. So the apparent `StarkSound` instance rests on TWO assumed, abstract carriers.
- The doc-comment "the apex on the PROVEN verifier algorithm" was FALSE and is corrected in-file.
VERDICT: the decomposition SHAPE is good — algorithm-soundness ⟂ deployment-refinement, the same shape as
DEBT-B's `denote` refinement, and the reject-teeth (`verifyAlgo_full_rejects_tampered_quotient`) are real work.
But it is currently **under-discharged and laundering-by-indirection**: the positive extraction direction is
untouched, both carriers are assumed AND abstract, and the trusted surface grew from one to two.
TO DISCHARGE: FRI-proximity @ BabyBear + AIR soundness (positive dir) + ChipTableSoundN @ real perm + a real
FriExtract ⟹ `instance : AlgoStarkSound`; PLUS prove `DeployedRefines` (the deployed verifyBatch refines
verifyAlgo — the deployment-refinement half, which nobody has attempted).

## ⚠⚠ DEBT-A ARITY GAP (2026-07-10, brick 3 `c9e8439ad`) — our FRI fold is 2-to-1; the deployed fold is 8-to-1
`circuit/src/plonky3_prover.rs:98` — `PROD_FRI_MAX_LOG_ARITY = 3`: the shipped FRI folds up to **8-to-1** per
round. Lean's `FriGeom.q : ι → κ` is the **squaring quotient (2-to-1)**, and `fold_close_of_two_alpha` is the
TWO-challenge Vandermonde reconstruction (BBHR18 arity-2). **Instantiating it at the right field/rate/domain does
NOT close this** — the folding map itself differs from deployment. This is a sixth DEBT-A obligation, provable
(BBHR18/DEEP-FRI generalize to arity `2^k` via a size-`2^k` Vandermonde) but not yet done.
ALSO measured: the deployed FRI evaluation-domain size is NOT static — `padded_trace_height << log_blowup`, fixed
per-proof, bounded by 2-adicity 2^27. Static params: log_blowup=3 (rate 1/8), num_queries=38, query_pow_bits=16,
log_final_poly_len=0 (`plonky3_prover.rs:96-100`). Other shipped configs: `stark_zk.rs:113` (lb=3,q=38),
`descriptor_ir2.rs:4740` (lb=6,q=19, rate 1/64).

## DEBT-A obligations, live tally (2026-07-10)
1. ChipTableSoundN @ the real Poseidon2BabyBearW16 perm — ✅ **CLOSED** (`37b121f55`).
2. FRI proximity @ deployed params — ◐ rate 1/8 modeled + 2-adicity cap instantiated (`c9e8439ad`); domain size
   is per-proof (no single k); **arity gap open**.
3. The `FriProximity` bridge (geometric ⟶ operational) — statement now PRECISE; `hFRI` half supplied by brick 3;
   `hcode_sat` + plumbing open; `air_binds_of_proximity` (FriSoundness:423) is the proved codeword half.
4. A real (non-degenerate) `FriExtract` — open; current witness is over `witVerify := fun _ => true`.
5. `DeployedRefines` (verifyBatch refines verifyAlgo) — never attempted; first question: is `verifyBatch` defined
   or opaque?
6. **Arity-2^k folding soundness** (NEW, above).
Then: 1+2+3+4+6 ⟹ `instance : AlgoStarkSound`; + 5 ⟹ `instance : StarkSound` with no assumed carrier.

## ⚠⚠⚠ THE DEBT-A KEYSTONE (2026-07-10, `35ee89ec9`): `verifyBatch` is OPAQUE — StarkSound CANNOT be discharged
`CircuitSoundness.lean:353` — `opaque verifyBatch : VerifyKey → BatchPublicInputs → BatchProof → Verdict`. **No
body.** Its own doc-comment is honest: "Its only SPECIFIED behaviour is via the `StarkSound` class below — we make
NO unjustified claim about its internals."
CONSEQUENCE: `StarkSound` is not a hard theorem awaiting proof — **it is the ONLY specification an opaque function
has.** It cannot be discharged while `verifyBatch` has no definition. Neither FRI-at-BabyBear (bricks 1–3), nor AIR
soundness (brick 5), nor ChipTableSoundN@real-perm (brick 4, CLOSED) touches it. `DeployedRefines` is likewise
UNPROVABLE-AS-STATED: nothing can be derived from an uninterpreted function's acceptance.
⇒ **THE DEBT-A CAMPAIGN AS ORIGINALLY SCOPED WAS WRONG.** "Prove the FRI verifier sound" is not the keystone. The
keystone is: **MODEL `verifyBatch` in Lean** (the p3 batch verify = Merkle openings + quotient check + FRI query
loop) and establish the Rust↔Lean correspondence — precisely the discharge `Poseidon2BabyBearW16` already has
(KAT-validated bit-exact against the deployed permutation). Note `verifyAlgo` (FriVerifier.lean:557) IS already a
real `Bool` function of exactly that shape; the gap is that opaque `verifyBatch` is merely ASSUMED to refine it
(`DeployedRefines`, never proved). The honest fix: DEFINE `verifyBatch` as the model and carry
`DeployedMatchesModel` as an explicit, KAT-dischargeable correspondence obligation.
Then and only then do bricks 1–5 + the arity fix + the bridge compose into a real `instance : StarkSound`.

## ⚖ METHOD (2026-07-10): "read the argument, not the name" — the rule cuts BOTH ways
A lane reported: "Merkle is STUBBED `true` (FriVerifier.lean:511); merkleRecompute_binds is off the accept path
— dangerous." I read `merklePaths := fun _ _ => true` and was one commit from publishing it. **It is FALSE.**
`friQueryCheck` (:321) calls `merkleVerify core.compress q.index l0.leaf l0.siblings traceCom`, and
`merkleVerify := decide (merkleRecompute compress idx leaf siblings = root)` (:226) — a REAL recompute-and-compare,
ON the accept path inside `foldConsistent`. The `merklePaths` field is REDUNDANT, precisely as its doc-comment
states. I read a SHAPE (`:= true`) instead of the ARGUMENT — the same error as trusting `genuineChipTbl_sound`
by its name, mirrored. **A stub-shaped field may be subsumed elsewhere; a genuine-sounding name may be a
constant-zero function. Only reading what the code CHECKS distinguishes them.**
VERIFIED GOOD: `fullChecks` (:673) implements every `verifyAlgo` sub-check for real (`batchTablesCheck`,
`queryPowCheck`); its claim "every verifyAlgo sub-check is now a real algorithm" CHECKS OUT.

## ★ THE TRUE DEBT-A BLOCKER (2026-07-10, `77d4b27cc`)
Modeling `verifyBatch` (the keystone from `35ee89ec9`) discharges only `DeployedRefines`/`DeployedMatchesModel`
— the CODE half, KAT-dischargeable via the existing `dregg-lean-ffi` differential harness + goldens, exactly as
`Poseidon2BabyBearW16` was. But `AlgoStarkSound.extract` contains `FriExtract`, which is a **PROOF-OF-KNOWLEDGE**
obligation (`3ee8b5ee8`): FRI proximity takes a TRANSCRIPT and yields a PROPERTY; extraction takes a PROPERTY and
must yield a WITNESS. Wrong direction. **So modeling verifyBatch does NOT finish DEBT-A**, and neither does any
amount of FRI-at-BabyBear work. The true blocker is knowledge extraction — a different mathematical object from
FRI soundness (needs an in-circuit⟹native extractor + `oracle_binding`/HashCR pinning). Worth knowing BEFORE
spending weeks on the FRI side expecting it to close.

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

## ⚠⚠ NEW DEBT-A OBLIGATION (2026-07-10, `7cbbee624`): LogUp interaction-bus soundness is UNMODELED in Lean
`Dregg2/Circuit/Lookup.lean`, the tree's own words: "The DENOTATION of a lookup is membership-in-the-table (the
meaning); LogUp is merely how the prover ENFORCES it efficiently — **that lives in the Rust AIR, not in this
semantics**." There is NO `logupCumSum` soundness theorem in `Dregg2/Circuit/` — only NAMED dependencies. So the
bus-balance ⟹ multiset-membership bridge, a core STARK component, has no Lean model. It is honest work
(Haböck's log-derivative identity + Schwartz–Zippel), not a hidden hole, and it is the next blocker after FRI.

## ⚠ CORRECTION (2026-07-10): `Satisfied2` ≠ `Satisfied2Faithful` — brick 4 does NOT serve AlgoStarkSound
I briefed a lane that `hHashes`/`hRanges` were closable from brick 4's `deployedChipTbl_sound` /
`RangeTableSound`. **Category error.** Those are about the chip and range TABLES (which feed `hbus`).
`Satisfied2`'s `rowHashes`/`rowRanges` concern the DESCRIPTOR'S IN-ROW `hashSites`/`ranges`, and
`structure Satisfied2` contains ZERO chip-table fields — chip-table faithfulness lives in the strictly stronger
`Satisfied2Faithful`. The real discharge is structural: `transferV3.hashSites = []` (rfl).
⇒ **Brick 4 (`37b121f55`) serves the `Satisfied2Faithful` family (the 26 hypothesis sites), NOT `AlgoStarkSound`,
which needs only `Satisfied2`.** Both are worth having; they are not the same obligation.

## DEBT-A live tally (2026-07-10, after `7cbbee624`)
#1 ChipTableSoundN @ real perm ✅ (serves Satisfied2Faithful) · #2 FRI proximity @ deployed rate ◐ (domain
per-proof) · #3 FriProximity bridge ✅ (3 explicit hyps) · #4 FriExtract = RECURSION, separate campaign ·
#5 DeployedRefines ⟶ DeployedMatchesModel (KAT, harness exists) · #6 arity-2^k ✅ (deployed 8-to-1) ·
**#7 NEW: LogUp bus soundness (unmodeled)** · #8 table-assembly emptiness (`t.tf .memory = [] ∧ .mapOps = []`,
irreducible, never AIR-forced). AIR half: 6/8 premises discharged at deployed transferV3.

## ⚠⚠ DEBT-A #2 SHARPENED (2026-07-10): our FRI proximity runs in the QUERY-EVERYTHING regime, not the deployed sample
`FriSoundness.friProximity_discharge (Q : Finset κ) (hcover : disagree f' (Fold S.geom α f) ⊆ Q) …
: FriProximity S 0 f` — the query set `Q` must COVER the disagreement set, and then the oracle is EXACTLY a
codeword (`d = 0`). Every BabyBear instantiation passes **`Finset.univ`** (`BabyBearFriSetup.lean:158`,
`BabyBearFriDeployed.lean:200`, via `Finset.subset_univ _`): **query every point.**
The deployed FRI samples `PROD_FRI_NUM_QUERIES = 38` points (`plonky3_prover.rs:99`) and obtains PROBABILISTIC
δ-closeness. The tree is honest at the definition (`query_sound_of_cover`: "if the sampled set covers the
disagreement set"), but **the probabilistic step — a random 38-subset covers a large disagreement set with high
probability — is NOT modeled**, and that step is precisely where FRI's soundness ERROR comes from.
CONSEQUENCES, stated plainly:
- The `d = 0` exactness in every through-line (incl. `deployedArity_circuit_sound`) is an artifact of `Q = univ`.
- Because `d = 0`, the arity constant `n²·d = 64d` is INVISIBLE — so obligation #6 (arity-2^k, PROVED) is not
  exercised by any current through-line.
- "FRI proximity at the deployed field + rate + arity" is TRUE and is real work, but it does NOT yet model the
  deployed SAMPLING that makes FRI a succinct argument. #2 is therefore more open than "rate ✓" suggested.
- The missing piece is the standard FRI soundness-error bound at `num_queries = 38`, `log_blowup = 3`
  (rate 1/8): the probability that 38 uniform queries miss a δ-far disagreement set. That is the quantitative
  step no lane has taken, and it is the honest content of "the FRI verifier is sound at the deployed params."

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

## ⚠⚠⚠ DEBT-A DEEP FINDING (2026-07-10): the deployed descriptor denotation Satisfied2/holdsAt is over ℤ — unsound IN GENERAL
Drilling the K′(a) finding one level DOWN: `VmRowEnv.loc` is ℤ-valued; `WindowConstraint.holdsAt := w.body.eval
env = 0` and `VmConstraint2.holdsAt`/`Satisfied2.rowConstraints` are all over ℤ (`DescriptorIR2.lean:372/589/608`).
So `Satisfied2` — the CORE deployed descriptor denotation, the target of `StarkSound.extract` and used tree-wide —
is over ℤ, and by K′(a) (`e5820e030`) is provably UNSOUND IN GENERAL: an honest field trace with a compound gate
whose ℤ eval hits exactly `p` (via an `add` of two columns) fails `Satisfied2`-ℤ though the deployed field verifier
accepts it.
SEVERITY IS GATE-STRUCTURE-DEPENDENT (careful scope, not alarmist):
- SAFE: the deployed range-check gate (`EffectVmEmitV2.lean:1344`, a degree-8 `∏ slotMinus k` = product of
  DIFFERENCES) does NOT bite — satisfaction means one factor is EXACTLY 0 (operands canonical in [0,p) ⟹ ≡0 ⟹ =0),
  zeroing the ℤ product. Difference-products are safe.
- BITES: any deployed gate with an `add` of two column VARIABLES that can sum to exactly `p` before a `mul`. K′(a)'s
  counterexample (`(col₀+col₁)*col₂` at `(p−1,1,1)`) is that shape. Whether a DEPLOYED gate has it needs a per-gate
  audit of every `.gate`/`.windowGate` body across the real descriptors.
THE FORK (foundational, EMBER-GATED — comparable to verifyBatch A/B, bigger):
  (A) Move the descriptor-IR semantics (`VmRowEnv`, `holdsVm`, `holdsAt`, `Satisfied2`) to BabyBear/mod-p — the
      FAITHFUL model (the deployed prover is over BabyBear). Correct, but ripples through EVERYTHING using Satisfied2.
  (B) Audit that every deployed gate is difference-product/degree-1-safe (no add-then-mul overflow), and NARROW the
      ℤ model's validity to that audited class with an explicit "deployed gates are overflow-safe" lemma.
Not launching either unilaterally — this is the deployed AIR's semantic foundation. K′(a)'s field companion
(`ood_forces_mainAirAccept_field`, `MainAirAcceptF`) is the (A)-direction beachhead already built.

## ⚠⚠⚠ SEVERITY SETTLED (2026-07-10, gate audit): deployed LINEAR gates bite — the ℤ denotation is UNFAITHFUL, (A) required
The Satisfied2-over-ℤ mismatch is NOT confined to hypothetical compound-mul gates. The DEPLOYED
`accumulator-nonrev-emit-v2` descriptor has LINEAR copy-constraint gates, e.g. `1·var12 + (−1)·var32 + 1·var0`
(= `col12 − col32 + col0 = 0`). A 3-term linear gate bites with NO multiplication: the field-valid assignment
`col12 = p−1, col32 = 0, col0 = 1` (all canonical in [0,p)) satisfies it mod p, but its ℤ residual is
`(p−1) − 0 + 1 = p ≠ 0`. So `holdsAt`/`Satisfied2` over ℤ REJECT a field-valid assignment — a SOLUTION-SET
argument (no reachability assumption): the ℤ denotation's solution set is strictly ⊊ the field constraint's, for
an ACTUAL deployed gate. SAFE gates remain the difference-product range gate (`gSlotRange`, satisfaction ⟹ a
factor is exactly 0). CONSEQUENCE: the committed ℤ AIR chain (`MainAirAccept`/`airAccept_forces_satisfied2`,
brick 5) is VACUOUS-IN-APPLICATION for such traces (the same pattern as DEBT-B's AccountsWF), and the field
version (K′(a) `MainAirAcceptF`) is the non-vacuous faithful one. ⇒ FORK RESOLVES TO (A): move the descriptor-IR
denotation (`holdsVm`/`holdsAt`/`arithResidual`/`Satisfied2`) to BabyBear/mod-p. (B) narrowing is NOT viable —
even affine deployed gates bite. Scope of (A) is the open question (Satisfied2 is used tree-wide); codex has the
(A) beachhead (`MainAirAcceptF`, `ood_forces_mainAirAccept_field`). EMBER-GATED: greenlight + scope the
holdsAt/Satisfied2 → mod-p refactor.

## ⚠⚠⚠ POSSIBLE DEPLOYED SOUNDNESS GAP (2026-07-11, mod-p migration surfaced it): VaultSatDescriptor carry-wrap
The ℤ→mod-p field-faithfulness migration EXPOSED a concrete instance of the K′(a) multi-term-wrap finding in the
DEPLOYED vault settlement circuit. `Dregg2/Deos/VaultSatDescriptor.lean`'s overflow-safe schoolbook-product gates
use `CARRY_BITS = 16` carries multiplied by `2^15`, so a single gate residual can reach `2^15·(2^16−1) = 2^31−1 =
2147483647 > p = 2013265921`. Consequence: the per-gate `≡ 0 [ZMOD p]` → ℤ `= 0` lift is UNSOUND in isolation — a
concrete adversarial witness `(t1 = 1, cb = 61440)` satisfies gate B mod p for `V = 0` while the ℤ equation forces
`0`. So `vaultSatV3_forces`'s exact-ℤ settlement conclusions (asset/share conservation via `linear_combination`
over the limb gates) CANNOT be discharged from mod-p + the existing range checks alone.
SEVERITY UNRESOLVED — two possibilities:
  (A) LIVE DEPLOYED GAP: if the deployed Rust vault range-checks carries to [0, 2^16), an attacker could forge a
      wrapping carry to satisfy the product gate mod p while violating the true ℤ conservation → forged vault
      settlement. HIGH severity if so.
  (B) LEAN-MODEL-ONLY: if the deployed Rust actually range-checks carries to [0, 2^15) (max residual < 2^30 < p,
      safe), then only the Lean CARRY_BITS=16 is wrong and the fix is tightening it to 15 to match deployed.
INVESTIGATION NEEDED: the deployed vault circuit's actual carry range-check width (15 vs 16 bits), + whether a
global bounded-reconstruction theorem (Σ limbs < p) holds. The Lean lane HONESTLY REFUSED to paper over it with a
possibly-unsound lift (VaultSatDescriptor.lean:254 stays red pending resolution) — the right call. This is the
migration doing its job: a field-faithful denotation makes carry-wrap UNIGNORABLE where the ℤ model hid it.

## ✅ VAULT CARRY-WRAP — VERDICT (A) CONFIRMED (2026-07-11, claude-verified by hand): REAL gap, STAGED, ember-gated fix
Full analysis: `docs/reference/VAULT-CARRY-WRAP-INVESTIGATION.md`. Every load-bearing claim verified independently:
- ★ BOTH Lean (`VaultSatDescriptor.lean:76`) AND deployed Rust (`circuit/src/effect_vm/vault_weld.rs:76`) set
  `CARRY_BITS = 16` and range-check the product carries (PCB/QCB/…) to 16 bits (`range_specs`, vault_weld.rs:142-166).
  The Lean is a FAITHFUL mirror ⟹ the gap is REAL in the deployed circuit, NOT model-only.
- ★ Arithmetic exact: `p = 2^15·61440 + 1` precisely; `61440 < 2^16` passes the loose check; max gate-B residual at
  16-bit carry = `2^31−1 > p` (gap), at 15-bit = `2^30−1 < p` (safe).
- ★ EXPLOIT concrete: a diluting deposit (`Ta·m > Sa·d`) is forgeable — a malicious prover picks the wrapping carry
  (`QT1+=1, QCB+=61440, …`) so `Q_limbs = Sa·d + 2^15·p`, all limbs in range, gates A/C/D exact-ℤ, gate B `≡0 mod p`;
  the borrow-compare then passes and the no-dilution gate ACCEPTS a share-inflating settlement. Nothing pins QCB.
- ★ STAGED: `vault_weld.rs:2,40` — tag-19 vault is "PIECE 2 of the VK epoch, STAGED", rides the big-bang flip, NOT
  in the live VK / not live-routed. So LATENT (close before flip), not a currently-exploitable production hole.
DECISION (honest state): VaultSatDescriptor.lean STAYS RED. Tightening only the Lean to CARRY_BITS=15 would make the
model claim a conservation the deployed circuit does NOT enforce — the anti-toy sin. The red file IS the faithful
state. FIX = `CARRY_BITS 16→15` in BOTH twins (vault_weld.rs:76 + VaultSatDescriptor.lean:76) — provably faithful
(honest carries fit 15 bits for operands in [0,2^30)), restoring R_B ∈ (−p,p) — PLUS regen the staged VK / fixture
(`vault-sat-v3-staged.json`) / producer aux-fill / drift-gate FP pin. This touches deployed circuit logic + the
staged VK epoch ⟹ EMBER-GATED. The mod-p migration EARNED this: the field-faithful denotation refused to prove a
conservation the ℤ model had silently faked, exposing a real staged vulnerability. This is the campaign working.

## ⚠⚠⚠ SECOND DEPLOYED SOUNDNESS GAP — MASK-RECON-WRAP VERDICT (A) CONFIRMED (2026-07-11): capability-auth forgery
Doc: `docs/reference/MASK-RECON-WRAP-INVESTIGATION.md`. The mod-p migration's SECOND live gap, same CLASS as the
vault (reconstruct-a-value-≥-p, mod-p doesn't pin the ℤ value). This one is arguably WORSE — a CAPABILITY-
AUTHORIZATION FORGERY:
- `DeployedCapOpen.lean:335` `maskReconGate` = `(mask_lo + mask_hi·65536) − Σ_{i<32} bitᵢ·2ⁱ ≡ 0 mod p`, deployed as
  a generic mod-p gate. `2p = 0xF0000002 < 2^32`, so a committed mask `M < p` has a p-shifted 32-bit boolean
  decomposition (`M+p`, `M+2p`) that ALSO vanishes mod p, with DIFFERENT bits.
- DEPLOYED: `trace_rotated.rs:2882` fills the 32 mask bits as FREE witness columns; `mask_lo/mask_hi` are NOT
  range-checked `< 2^16` (only Merkle-pinned via leafLookup→rootPin). So the adversary CONTROLS the decomposition.
- EXPLOIT: a cap with empty mask `M=0` (grants nothing), opened for `n=1` (EFFECT_TRANSFER): set the bit columns to
  the boolean decomposition of `2p = 0xF0000002` (bits boolean ✓, `0−2p ≡ 0 mod p` ✓, `bit₁=1` ✓) →
  `authorizedFacetEffB … (1<<1) = true`. A cap granting nothing authorizes a transfer. Generalizes to any effect n.
- ⚠ MY GATE ERROR (corrected): I initially committed CapOpenEmit green calling `CapOpenRowCanon.reconExact` a
  "canonicality envelope" — but it ASSUMES the exactness the wire doesn't enforce (laundering the gap, the sin the
  vault lane refused). RELABELED in-file (`CapOpenEmit.lean:162`) as an explicit ⚠ DEPLOYED-GAP assumption: the
  `_authorizes` keystones are CONDITIONAL on an UNFIXED deployed gap and do NOT prove capability authorization until
  the fix lands. Green stands only because the assumption is now NAMED as a gap, not dressed as a real invariant.
- FIX (unlike vault's narrow 16→15, narrowing is UNAVAILABLE — `EFFECT_ALL = 0xFFFFFFFF ≥ p` is legit): range-check
  `mask_lo, mask_hi < 2^16` + reconstruct PER 16-bit limb (each sum `< 2^16 < p`, unique) ⟹ reconExact DERIVED.
  EMBER-GATED (deployed circuit change).
WRAP-CLASS AUDIT (from the investigation): 2 live verdict-A instances — vault carry (16-bit) + this maskRecon
(32-bit). CapReshape gMaskRecon (MASK_BITS=8, <256<p) SAFE by width. RotationWide limbs = Poseidon2 chip absorbs
(equality-bound) SAFE. CapOpenRowCanon is the ONLY migrated RowCanon laundering a wrap. No 3rd live instance found —
but the CLASS is now a known audit axis for the rest of Phase 0 + the deployed circuit.

## ⚠⚠⚠⚠ GAP #4 — CORE-TRANSFER OVER-DEBIT (verdict A, HIGH, the DEEPEST wrap-class instance) — 2026-07-11
Found by the systematic WRAP-CLASS-AUDIT (`docs/reference/WRAP-CLASS-AUDIT.md`), hand-verified. The ROOT value gap,
deeper than vault/cap-open/cross-cell. DEPLOYED transfer debit gate `after.bal_lo = before.bal_lo + amount·(1−2dir)
− fee` (`trace_rotated.rs:694`) range-checks ONLY the AFTER balance (`EffectVmEmitTransfer.lean:224`, 2 ranges);
`amount` is NOT range-checked in-circuit. The design's "underflow lands ≥2^30 so the range-check rejects" is FALSE
for `amount − before ∈ (939M, 1074M)`: then `after = p − (amount−before)` lands back in `[0,2^30)`.
- ★ WITNESS (hand-verified): `before=1, amount=1006632961, after=1006632961` — `after − before + amount = p ≡ 0 mod p`
  ✓ AND `after = 1006632961 < 2^30 = 1073741824` ✓ (passes the after-range). Real debit would be `1 − 1006632961 < 0`
  (invalid), but the circuit ACCEPTS a cell going from balance 1 to balance ~10^9 ⟹ ~10^9 minted from nothing.
- Covers Transfer debit, Burn, fee-debit. Even a fixed cross-cell #3 won't catch it (published NET_DELTA off by p).
- ⚠ MY LAUNDERING (2nd occurrence, corrected): the Lean `transferVm_enforces_availability` / anti-ghost teeth carry
  `hcanonMove` (= `0 ≤ before − amount`, i.e. availability itself), declared "the interpreter-edge's job," enforced
  by NO deployed gate — same structure as cap-open reconExact. I gated the Transfer file EARLY accepting hcanonMove
  as "the deployed range-check invariant" — WRONG, amount is unranged. Marked in-file at `EffectVmEmitTransfer.lean:
  224` as an explicit ⚠ DEPLOYED-GAP.
- FIX (ember-gated, deployed circuit): range-check `param.AMOUNT < 2^30` (or the debited difference) — the
  committed-threshold/presentation/non-revocation comparators do this CORRECTLY (range-wire pins diff < p/2), so the
  fix pattern exists in-tree. Then availability is DERIVED, not assumed.

## WRAP-CLASS TALLY (2026-07-11): 4 verdict-A gaps + 1 suspect + safe-classified rest
1. VAULT carry-wrap — FIXED + PROVEN (CARRY_BITS 16→15, VaultSatDescriptor RED→GREEN, staged fixture regen owed).
2. CAP-OPEN mask-recon — verdict A, capability-auth forgery, fix pending (per-16-bit-limb recon + range mask_lo/hi).
3. CROSS-CELL conservation — verdict A, ≥2-cell balance sum wraps; ADDITIVE (not wired live); fix = multi-limb accum.
4. ★ CORE-TRANSFER over-debit — verdict A, HIGH, the deepest; fix = range-check amount < 2^30.
SUSPECT R1: bilateral-agg prefix sum over hash fingerprints — likely SAFE-BY-STRUCTURE (needs fingerprint-freedom check).
SAFE (audited): balance-limb decomp (<2^30), the threshold/presentation/non-revocation comparators (same class DONE
RIGHT — range-wire pins diff<p/2), cap-reshape 8-bit, Poseidon2/Merkle/schnorr (structure/carry-chained).
Blind spot: value/authority gates all have Lean twins (good); effect_action_air::Burn's doc-commented 2×32-bit
borrow is NOT emitted deployed (doc↔deploy mismatch, not a wrap); dregg-transfer-v1 unranged amt is TEST-ONLY.
COMMON ROOT: the deployed circuit reconstructs/moves values that can exceed p; a mod-p constraint alone doesn't pin
the ℤ value; where no range-check bounds the reconstruction < p, an adversary picks a p-shifted witness. THE ℤ
MODEL HID ALL FOUR. Field-faithfulness + the audit surfaced them.

## ✅✅✅✅ ALL FOUR WRAP-CLASS GAPS FIXED (2026-07-11) — DEPLOYED into the re-keyed VK epoch (GAP 1-6 flip 1e12d8886/764225f0c/72469afd0; no longer "staged")
Every gap the field-faithfulness migration + audit surfaced is now closed with a PROVEN-CORRECT in-circuit fix
(both twins: deployed Rust + Lean), claude-gated hard on the identical bar: the safety property DERIVED from
in-circuit range/borrow gates (NOT an assumed hypothesis), the exact forgery witness UNSAT, honest transactions
still pass (liveness). Common fix pattern: the vault's 15-bit-limb decomposition — every polynomial < 2^16 ≪ p, so
no residual reaches p and the wrap is STRUCTURALLY IMPOSSIBLE (a single 30-bit range check does NOT suffice, since
p ≈ 2·2^30 makes the wrap window overlap the valid range).
1. ✅ VAULT settlement carry-wrap — CARRY_BITS 16→15; VaultSatDescriptor RED→GREEN, bounded-lift DERIVED. `27feb…`/`17937c008`.
2. ✅ CAP-OPEN mask-recon (capability-auth forgery) — per-16-bit-limb reconstruction; the LAUNDERED `reconExact`
   DELETED, authorization now UNCONDITIONAL; maskReconLoGate_rejects_wrap UNSAT. `9cc377282`.
3. ✅ CROSS-CELL conservation — dual 3×15-bit-limb accumulators; ccc_conserves DERIVED, ccc_psum_forgery_unsat UNSAT;
   EMPIRICAL real-STARK liveness test (balanced total >p verifies). `7e2bc7a18`.
4. ✅ CORE-TRANSFER over-debit (the deepest) — 15-bit-limb borrow chain; transferAvail_derives_availability (amount ≤
   before DERIVED, NO hcanonMove), transferAvail_forgery_unsat UNSAT; honest 100→70 passes. `a1be7b5df`.
TWICE the fix DELETED a laundered assumption I had earlier gated through (cap-open reconExact, transfer hcanonMove) —
the property is now genuinely enforced by the circuit, not assumed. THE CAMPAIGN: found four exploitable deployed
soundness gaps the ℤ "verified" model hid, and closed all four with field-faithful in-circuit enforcement + proofs +
forgery-UNSAT witnesses.

### DEPLOYMENT UPDATE (2026-07-13): the availability / transfer-shaped cohort is DEPLOYED in the live VK
The **transfer-shaped availability class — GAP #4 core-transfer over-debit (transfer/burn/fee) + GAP #2 cap-open
mask-recon (cap-open-EFF/TB), 10 members with their wide twins — is CLOSED + DEPLOYED** in the live VK: the
provenance-clean regen `887b95e76` retargets every member to its `*Avail` descriptor (borrow-gated, amount
range-checked, wrap structurally impossible), FP constant re-stamped → new VK epoch, mint-from-nothing closed
(empirically validated: `avail_weld_live_roundtrip` 3/3, all forgery witnesses UNSAT). See
`docs/FINDING-modp-wrap-forgery-audit.md` RESOLUTION. **Still STAGED (not yet in a live VK):** the VAULT settlement
carry-wrap (#1, tag-19 — `effect_vm_descriptors.rs:2435` "STAGED discharge/vault") and CROSS-CELL conservation (#3,
additive). Those ride a later ember-gated regen; live routing for the transfer-shaped cohort HAS changed to the
hardened descriptors.

## ⚠⚠⚠ GAP #5 CONFIRMED — HEAP-SORTEDNESS UNFORCED → DOUBLE-SPEND (verdict B/adversarial, 2026-07-12) — 2026-07-12
Refusing to CARRY the `CanonicalHeapTree` fact (ember: "prove real config evolution, don't carry facts") exposed a
real question about the deployed memory/heap circuit. Doc: `docs/reference/CANONICAL-HEAP-TREE-INVESTIGATION.md`
(verdict B with a C caveat). The memory soundness of the 7 mapOp effects (NoteSpend nullifiers / NoteCreate
commitments / cell-creation / HeapWrite) needs the committed heap to be a genuine SORTED tree so ABSENCE proofs are
complete. Confirmed IN LEAN: `SortedTreeNonMembership{,Heap8}` carry `SpineCommits.sorted` as a HYPOTHESIS (never an
axiom; consumed, not forced) — the per-turn MapOps AIR forces path-binding + per-POSITION adjacency (idx_upper =
idx_lower+1, key_lo < k < key_hi) but the Lean model does NOT derive whole-tree key-ordering `key(pos i) <
key(pos i+1)`.
THE TENSION (unresolved — the two fixes differ): (a) REAL DEPLOYED GAP — if the deployed per-turn mapOps `.insert`
gate is an in-place position overwrite (investigation's read, trace_rotated.rs:~601) with NO sorted-splice
enforcement, then a malicious prover commits a NON-SORTED heap and forges an absence → DOUBLE-SPEND. Concrete
witness: heap [MIN,(20),(30),(25,n),MAX] with spent nullifier n at addr 25 OUT OF ORDER at position 3; prove n
absent via positions 1-2 (20<25<30 brackets 25, both open to the genuine root); the circuit never checks
pos2.key(30) < pos3.key(25) → forge accepted → re-spend n. vs (b) FAITHFULNESS DEBT — `heap_root.rs:39` claims
"genuine in-circuit sorted-tree update/insert gates" and `whole_image_fold.rs:165` is "a sorted-insert chain pinned
at both ends"; IF those force sorted placement on the per-turn insert path, sortedness is DISCHARGEABLE from
acceptance and the fix is in the LEAN (derive SpineCommits.sorted, stop carrying it).
RECONCILIATION NEEDED: does the DEPLOYED per-turn mapOps insert gate force sorted placement (heap_root sorted-tree
gates wired to the mapOps path → faithfulness debt) or not (in-place overwrite → real gap)? Investigating. FIX either
way is one shared lane for all 7 mapOp effects: (real gap) strengthen the .insert gate to sorted-splice + discharge
the chain invariant from sorted genesis (whole_image_fold pattern); (faithfulness) wire the deployed sorted-tree
gates into the Lean derivation. The config-evolution object carries `CanonicalHeapExtract` as the ONE named residual
until this resolves.

### RECONCILED (2026-07-12): CONFIRMED REAL GAP (not a faithfulness debt) — the 5th deployed soundness gap
Definitive (`CANONICAL-HEAP-TREE-INVESTIGATION.md` reconciliation): the deployed per-turn mapOp INSERT
(`nullifierInsertOp`/`commitmentsInsertOp`/`cellsInsertOp`, `descriptor_ir2.rs:2817-2845` Ir2Air::MapOps insert leg)
folds the new leaf up a PROVER-SUPPLIED path to new_root8 and range-checks the new key against NOTHING (verified: no
eval_lex_lt / key-range gate in the insert leg). The adjacency (diff==1) + key-gap (lo<key<hi, `eval_lex_lt`) gates
live ONLY in the separate Ir2Air::MapAbsent arm (`:2880-2926`, comment "THE GAP: lo_addr < key < hi_addr"), for
PROVING absence — never on insert. `heap_root.rs:41` confirms its "genuine sorted-tree insert gates" are the Phase-E
UNDEPLOYED lane (`:292/:295` "Phase-E AIR"). So sortedness is NOT forced in-circuit; the Lean carrying SpineCommits.
sorted as a hypothesis is HONEST (no forcing gate to under-model).
EXPLOIT (live under the adversarial SNARK model — the correct threat model for a ZK prover): a malicious prover
commits a NON-SORTED heap root (free-placement insert allows it), then proves a spent nullifier n ABSENT via an
out-of-order bracket — witness heap [MIN,(20),(30),(25,n),MAX], n@25 at position 3; the .absent arm brackets 25 by
positions 1-2 (20<25<30), both open to the genuine root; the circuit never checks pos2.key(30) < pos3.key(25) →
absence ACCEPTED → re-spend n → DOUBLE-SPEND. Also forges fresh-commitment / cell-creation (any mapOp absence).
Honest execution is safe (the trusted producer builds only sorted trees); the gap is the missing in-circuit
INDUCTION: genesis sorted is in-circuit-pinnable, but per-insert sorted-PRESERVATION is not enforced.
FIX (ember-approved, circuit): on each .insert row add the MapAbsent adjacency + lo<key<hi gap gate binding the new
key to a real sorted gap of the PRE-root + a sorted-splice post-root constraint. Chained from sorted genesis this
makes sortedness an in-circuit INDUCTIVE invariant ⟹ discharges CanonicalHeapTree for all 7 mapOp effects (one shared
lane). Then MapReconcileFamily's CanonicalHeapExtract reduces into {Poseidon2, FRI-LDT}, closing kernelConfigSound's
one genuine assumption. STAGED like the wrap-class fixes (rides the VK epoch flip).

### ★ GAP #5 CLOSURE VERDICT (2026-07-12): a per-row gate CANNOT fix it — IMT-MIGRATION is the sound closure (ember-gated)
The fix lane REFUSED to ship a laundering gate and returned a hard architectural verdict (`CANONICAL-HEAP-TREE-
INVESTIGATION.md`): the specified per-row sorted-splice is NOT faithfully forceable in the DEPLOYED representation.
- ROOT CAUSE: the deployed heap is a COMPACTED SORTED ARRAY (CanonicalHeapTree::new sorts + places contiguously,
  heap_root.rs:162/179; insert = FULL REBUILD, :399/823 "INSERT that shifts positions"). Splicing k shifts every
  real leaf after the insertion point — O(n) of 2^16. A fixed-width single-row AIR opens only O(depth) paths, so it
  CANNOT prove the O(n) shift happened.
- A LOCAL after-splice gate does NOT close the double-spend (proven): the strongest O(depth) local gate (open
  pre-neighbors lo<k<hi + post-positions consecutive) rejects the SPECIFIC §3 witness but the adversary commits a
  DIFFERENT non-sorted after (fold[MIN,20,25,30,15,MAX] — pos-4 15 out of order, UNOPENED, 30<15 never checked; the
  covering sibling is a free prover digest). Local gate = laundering (models-as-global what's forced only locally).
- ★ SOUND CLOSURE = INDEXED MERKLE TREE (IMT) migration: leaf hash[addr,value,nextAddr]. Absence = ONE low-leaf
  opening low.addr < k < low.nextAddr (POINTER bracket — no physical adjacency, so MapAbsent's pathPos adjacency
  retires); insert = update low-leaf nextAddr→k + APPEND (k,value,oldNext) at a free slot — TWO O(depth) paths, NO
  shift; sorted-preservation is a LOCAL per-row check. Chained from empty-IMT genesis ⟹ sorted(pre)⟹sorted(post)
  IN-CIRCUIT ⟹ CanonicalHeapTree discharges into {Poseidon2SpongeCR, FRI-LDT}. Standard Aztec construction; the
  combinatorial half already proven (SortedTreeNonMembership.sortedInsert_sorted:301, update_sound:338). Aligns with
  the existing sorted-Merkle-accumulator direction (project-vk-epoch-nullifier-flip / NULLIFIER-ACCUMULATOR-
  UNIFICATION) — IMT is its natural form.
- SCOPE: all 7 mapOp effects + descriptor_ir2.rs (:2721 MapOps, :2854 MapAbsent) + heap_root.rs + trace_rotated.rs
  (:1415/1516) + MapOpsColumnLayout.lean — a VK-REGEN + staged-artifact cutover. EMBER-GATED (a real accumulator
  redesign, not a per-row patch).
STATUS: gap #5 stays OPEN + CLASSIFIED (verdict B maintained-invariant assumption with a precise IMT closure), NOT
faked shut. kernelConfigSound's CanonicalHeapExtract remains a genuine assumption until the IMT migration. The other
4 wrap gaps had local gate fixes; this one needs the rep change — a deeper, correctly-scoped finding.

### ★★ GAP #5 CLOSURE OBSTRUCTION (2026-07-12): the insert soundness needs a MEMORY-COMMITMENT REDEFINITION (ember decision)
The IMT leaf-format + pointer-bracket ABSENCE landed (919b2b0b8) and the Lean IMT closure is PROVEN (531f2a009:
imtInsert_preserves / canonicalHeapExtract_of_imt / double-spend UNSAT). BUT the deployed INSERT two-path
(soundness-completer) is NOT buildable against the deployed heap-tree layout — a genuine architectural obstruction the
fix lane named rather than laundering:
- The deployed heap is a COMPACTED SORTED ARRAY: insert_witness (heap_root.rs:861-896) does splice-and-REBUILD
  (partition → splice → CanonicalHeapTree::new re-sort+re-compact), so the new leaf lands at its sorted-compacted
  position and the ENTIRE SUFFIX shifts up by one (O(n) positions change).
- The AIR binds "only this leaf changed" via a SHARED sibling path (cur_old→MAP_ROOT, cur_new→MAP_NEW_ROOT over shared
  (MAP_SIB0,MAP_DIR0)) — sound for VALUE-UPDATES (position stable), but for INSERT there is NO shared pre-image for the
  shifted suffix. Opening the two local edits leaves the shifted region FREE ⟹ a malicious new_root8 (de-linking any
  leaf) is still SAT. imtInsert_preserves needs "only low + the new slot changed, nothing else" — unbindable when the
  suffix shifts. This is the FLIP SIDE of the compacted-array-shift obstruction: the deployed tree IS the compacted
  array. The Lean IMT assumes APPEND-at-free-index (stable positions); the deployed circuit diverges on the insert.
- STATUS: gap #5's ABSENCE arm is CLOSED (pointer-bracket, 919b2b0b8); the INSERT arm remains OPEN — the committed
  root's sortedness is a PRODUCER-TRUST assumption, not an in-circuit forced invariant. Narrowed, not closed.
★ THE DECISION (ember-gated — a memory-commitment redefinition, the "be thoughtful, don't fire commitment changes from
thin context" case; NOT a per-row AIR patch): to get stable positions so the two shared-path openings bind —
  (a) APPEND-AT-FREE-INDEX storage — root becomes INSERTION-ORDER-DEPENDENT, breaking root_is_input_order_independent
      (heap_root.rs:1019) + the foundational "cell & executor compute byte-identical roots from the (addr→value) map"
      invariant (heap_root.rs:15-25); the cell must persist a position assignment; OR
  (b) SPARSE-BY-ADDR tree (position = addr bits, depth ~31) — order-independent but a different tree, ~2× path depth +
      full retree.
Both change EVERY committed heap root ⟹ VK + all heap-root fixtures regen + cell/executor recompute rewrite +
differential-test rebuild. The AIR side (2nd sibling path + the range gate via eval_lex_lt) is fixed-width-expressible
and NOT the blocker; the blocker is the deployed commitment/producer layout. Recommend surfacing to ember. Aligns with
the sorted-Merkle-accumulator unification direction — IMT-over-sparse-by-addr is likely the convergence (order-indep +
forceable insert), at the cost of depth.

## ⚠⚠ GAP #6 CONFIRMED — MUTABLE-CELL unforced-sortedness → forged cell birth (identity takeover), 2026-07-13
The gap-#5 mechanism applies UNCHANGED to the mutable cell/heap map (`MUTABLE-MAP-SORTEDNESS-INVESTIGATION.md`).
`cellsInsertOp` (createCell/CreateCellFromFactory/Spawn, `EffectVmEmitRotationV3.lean:2704`) stayed op=3 `.insert`
(the unforced compacted-array insert — at op=3 the pre-root bind + old-chain fold are gated OFF, `descriptor_ir2.rs
:2928/2929/3035; only the new-leaf chain fires :3049; no sorted-splice, no next_addr relink, no dedup). `cellsFreshOp`
(op=.absent, the IMT pointer-bracket :3196-3313) PRESUPPOSES the ImtSorted invariant ("sound relative to the maintained
well-linked ImtSorted invariant the insert-preservation gate installs") — but that gate only exists for the 3
append-only sets now on op=4; cells alone have no gate installing it.
EXPLOIT: adversary commits an accounts tree with forged next_addr links bracketing a PRESENT addr X → cellsFreshOp
accepts "X fresh" → createCell/factory/spawn forges a birth OVER the existing cell (identity/state takeover). Companion:
unforced dedup → duplicate addr → wrong cell read. Same class as #5.
TREE: same TYPE (CanonicalHeapTree8, shared MapOps/MapAbsent AIRs), separate INSTANCE (cells = limb 0). The op=4 AAFI
flip was applied per-emitter and just not routed to cellsInsertOp.
FIX: SAME as #5 — extend the AAFI op=4 flip to cellsInsertOp (+ the cell producer to insert_witness_aafi + the wide
createCell producer aafi=true + the capRoot-weld consistency). Value-updates (.write, op=1) are ALREADY sound
(position-stable). Rides the same VK epoch as gaps 1-5. Fix in flight.
