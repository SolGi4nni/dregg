# Lean: circuit soundness & unfoolability

What this subsystem IS at HEAD. The Lean proof that a light client which verifies a
batch proof and **runs nothing else** cannot be fooled: every accepted proof decodes
to a genuine kernel transition whose endpoints are the published commitments. Lives
under `metatheory/Dregg2/Circuit/` (the soundness story) and
`metatheory/Dregg2/Lightclient/` (the verifier-side data structures). Every
load-bearing claim below is cited to a `Module.decl` or file:line.

This is the Lean companion to the Rust `docs/reference/circuit.md` (the
prove/verify crates). Here the object is the *theorem*, not the prover.

## The target (what soundness means)

`Dregg2.Circuit.CircuitSoundness` states the goal directly: a light client verifies a
batch proof against the live VK and runs nothing; soundness is

> `verifyBatch vk pi π = accept ⟹ ∃ a genuine kernel transition s ⟶ s'` with
> `pi.pre = stateCommit s ∧ pi.post = stateCommit s'`

(`CircuitSoundness.lean:11-14`). The "genuine kernel transition" is the declarative
kernel `ActionDispatch.fullActionStep`, composed over a turn by `turnSpec` and
identified with the real executor `execFullTurnA` via `execFullTurnA_iff_turnSpec`
(`CircuitSoundness.lean:16-21`).

## The three load-bearing pieces

1. **`StateDecode`** — the faithful witness→kernel-state decode
   (`CircuitSoundness.StateDecode`, `CircuitSoundness.lean:187`). It says the
   witness's published OLD/NEW commitments *equal* the surface commitment of the
   bound kernels (`preBinds`/`postBinds`) over a fixed `CommitSurface`, and that
   those kernels are `AccountsWF`. Faithfulness is **not assumed**: it is a theorem.
   `stateDecode_pre_faithful` / `stateDecode_post_faithful`
   (`CircuitSoundness.lean:201`, `:210`) prove that two states decoding the *same*
   published commitment have *equal* kernels — by `CommitSurface.commit_binds`
   (`CircuitSoundness.lean:144`), which is `recStateCommit_binds_kernel` repackaged:
   the commitment binds the kernel under the Poseidon CR set, using **no** authority
   gate and **no** frame assumption.

2. **`descriptorRefines d kstep`** — the per-effect rung
   (`CircuitSoundness.descriptorRefines`, `CircuitSoundness.lean:232`): any
   `Satisfied2` witness of descriptor `d` whose published commitments decode (via a
   faithful `StateDecode`) to `pre`/`post` forces `kstep pre post`. Its antecedent is
   the named hash-CR carrier `Poseidon2SpongeCR hash` (`:234`) — the floor the
   per-descriptor published-PI↔limb binding consumes. This is the genuine obligation
   each effect discharges; the apex carries the registry-wide family of these.

3. **`lightclient_unfoolable`** — the apex (`CircuitSoundness.lean:453`). Its only
   data inputs are what a light client actually has — the public inputs `pi` and the
   proof `π`. It does **not** take `pre`/`post` or a `StateDecode` as hypotheses;
   those would hide the hardest rung. Instead it *derives* the decode from named
   floors and concludes the existence of a genuine kernel boundary.

## The apex and its carried floors

```
theorem lightclient_unfoolable
    (hash) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep) (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi) (π) (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    ∃ pre post, StateDecode S pi.toPublished pre post ∧ kstep pi.effect pre post
              ∧ pi.pre = S.commit pre.kernel pi.turn
              ∧ pi.post = S.commit post.kernel pi.turn
```
(`CircuitSoundness.lean:453-465`). The derivation chain: `StarkSound` extracts a
`Satisfied2` witness of the *claimed* descriptor whose published commitments are
`pi.toPublished` → `WitnessDecodes` produces `pre`/`post` with a `StateDecode` →
`hrefines` turns witness + decode into `kstep pi.effect pre post` → the decode's
binding re-exports `pi.pre`/`pi.post` as the genuine endpoint commitments
(`CircuitSoundness.lean:466-479`).

The **carried obligations ledger** — every named, deferred premise (nothing
laundered to `True` or an open hole):

- **`StarkSound hash R`** (`class`, `CircuitSoundness.lean:382`) — the p3
  batch-STARK soundness / FRI extraction: a verifying batch yields a `Satisfied2`
  witness of the claimed descriptor whose published PI agree with `pi`. **No longer
  terminal-by-design:** `starkSound_of_verifyAlgo` (`FriVerifierBridge.lean:106`) makes
  it a THEOREM over the specified `verifyAlgo`, resting on `AlgoStarkSound` (the FRI-LDT
  floor) + `DeployedRefines`. The BBHR18/BCIKS20 FRI proximity algebra is itself PROVED
  in `FriSoundness.lean` resting only on the hash floor `HashCR` (`friProximityK8_discharge`,
  composed at `d=0` via `FriBridgeDeployedArity`). The deployed-parameter `FriLdtDeployedBound`
  **as written is DISCHARGED** (`FriLdtJohnson.lean`, `friLdtDeployedBound_discharge`, axiom-clean):
  at the Johnson radius `δ_J = 1−√ρ = 7/8` the statement is the trivial counting else-branch
  (`accept_prob_le_of_farN`), so `ldt_bound_unconditional` re-derives the `2⁻⁵⁷` LDT payoff with no
  hypothesis. Its genuine BCIKS20 residual (words inside the `δ_J` ball, past unique decoding) is
  two precisely-named lemmas — `RSListBound` (RS list-size) and `FriProximityGapChallenges`
  (bounded good folding challenges) — each PROVED at `L=1` and instantiated on the deployed
  rate-`1/64` code (min-distance `127` → singleton at radius `63`); only their `L>1` generalization
  (the Johnson bound + correlated-agreement theorem) remains open. See `STARK-SOUNDNESS-CENSUS.md`.
- **`Poseidon2SpongeCR hash`** + the `CommitSurface` CR fields (`CommitSurface`,
  `CircuitSoundness.lean:113-134`) — the standard Poseidon collision-resistance set
  (`cmbInj`, `compInj`, `compNInj`, `leafInj`, `restFrame`) the full-state root
  `recStateCommit` binds under. Realizable; bundled, never an axiom.
- **`hrefines`** — the per-effect refinement family, the genuine remaining rung work
  (discharged effect-by-effect downstream).
- **`WitnessDecodes hash R S pi`** (`def`, `CircuitSoundness.lean:446`) — the
  witness→kernel-state **existence** rung: a witness publishing `pi` decodes to some
  `(pre, post)`. A light client cannot supply `pre`/`post`; this rung supplies them
  (the surjectivity of the commitment surface on the published roots). Carried
  explicitly, never discharged by assuming the conclusion.

The minimal honest STARK-batch interface (`VerifyKey`, `vkOfRegistry`,
`BatchPublicInputs`, `verifyBatch`, `Verdict.accept`, `StarkSound`,
`tracePublishedCommit`) is **defined here** because none existed
(`CircuitSoundness.lean:290-387`); `verifyBatch` is `opaque` — the apex reasons only
through the verdict and the `StarkSound` extraction (`:351-353`).

## Scope — what the apex proves, and the freshness boundary

`lightclient_unfoolable` proves **single-transition** soundness: every accepted batch
decodes to a genuine kernel step committing to `pi.pre`/`pi.post`, taking `pi.turn`
as given. It establishes **nothing** about whether that transition is *fresh*
(unreplayed) or its ordering (`CircuitSoundness.lean:412-435`).

Cross-turn freshness / no-replay is a **separate** theorem,
`Dregg2.Circuit.CrossTurnFreshness`. `no_replay` (`CrossTurnFreshness.lean:164`)
proves a proof is applicable at most once; `replay_rejected_after_apply`
(`:177`) is the mutation-confirm. It rides the agent nonce bound *into*
`recStateCommit` (it lives in the agent cell's leaf and strictly increases each
turn, so the commitment sequence never cycles) — `commit_neq_of_nonce_neq`
(`:72`), `TurnChain.commit_no_repeat` (`:130`). The named residual is wiring the
full `runTurn`-driven accepted sequence into a monotone `TurnChain`; the
prologue-bump legs are proved (`runTurn_failed_strictly_advances`, `:229`;
`runTurn_strictly_advances_agentNonce`, `:246`).

## Whole-turn composition: the chain and its derived frame

§4–§9 of `CircuitSoundness` lift the single-effect apex to a whole turn. A turn is a
`List` of per-step circuit witnesses, each publishing its own OLD/NEW commitment (the
prover's chained-root column). The cross-step **frame** — that one step's post-state
*is* the next step's pre-state — is **derived, not assumed**:

- `stateDecodeChain_frame_continuous` (`CircuitSoundness.lean:279`) — equal published
  seam commitments + faithfulness force `a.post.kernel = b.pre.kernel`.
- `TurnDecodeChain` (`structure`, `CircuitSoundness.lean:570`) — a turn threaded
  left-to-right; `turnDecodeChain_seam_kernel_derived` (`:593`) proves the kernel
  half of every seam from the published kernel-root column (the frame **tooth**: a
  prover whose published seam disagrees with the threaded kernel is rejected).
- `turnDecodeChain_refines_turnSpec` (`:633`) folds the per-step `descriptorRefines`
  along the chain into `∃ acts, turnSpec start acts fin`.
- `lightclient_turn_unfoolable_forest` (`:836`) — the whole-turn headline: a verified
  turn + the per-effect family + floors ⟹ a genuine `execFullTurnA s acts = some s'`
  whose endpoints commit to the published turn-level `(pre, post)`.

### The receipt-log seam (§9)

`recStateCommit` is kernel-only — it does not bind the `RecChainedState.log` receipt
chain — so the full-state seam carried its **log** half as a free residue. §9 closes
it, mirroring the kernel tooth: `LogDecode` (`CircuitSoundness.lean:891`) binds
published log commitments to `pre.log`/`post.log` through the realizable
`logHashInjective LH` carrier; `logDecodeChain_frame_continuous` (`:914`) forces
`a'.log = b.log` across a seam; `turnDecodeChainLog_seam_full_derived` (`:985`)
recovers the whole `RecChainedState` continuity `a.post = b.pre` on both components;
`turnDecodeChainLog_rejects_forged_log` (`:1008`) is the mutation-confirm — a forged
intermediate receipt-log is UNSAT. Non-vacuity of the `logHashInjective` carrier is
exhibited inline (`:1031` — a collapsing hash cannot be injective).

## The closed apex and the per-effect taxonomy

`lightclient_unfoolable` carries `hrefines : ∀ e, descriptorRefines …` as a
hypothesis. The closure layer *discharges* that family from genuine per-effect rungs:

- `Dregg2.Circuit.ClosureAll` holds one `<effect>_closedLog` rung per effect family
  (transfer tag 0 `transfer_closedLog`, `ClosureAll.lean:152`; cellSeal 52, revoke 2,
  delegate 1, attenuate 12, mint 3, burn 4, noteSpend 27, … — 56 `_closedLog`
  theorems covering the effect set). Each is a one-liner over the generic combinator
  `closedLog_of_encode` (`:121`): it derives the `.log` advance through
  `logHashInjective` and bridges to `kstepAll` via the effect's landed
  `<effect>_descriptorRefines` rung. The dominant class is **CLASS A** — the
  effect's write is *forced from a deployed `Satisfied2` descriptor* (e.g.
  `cellSeal_closedLog_sat` forces the seal from the deployed `cellSealV3`,
  `ClosureAll.lean:189`; the cap family from the shape-matched keystone wrappers
  `delegateWriteCapOpenV3` (→ `effCapInsertV3`),
  `revokeDelegationWriteCapOpenV3` (→ `effCapRemoveV3`),
  `attenuateCapOpenEffV3` (→ `effCapOpenWriteV3`), etc., `:934-1349` — see
  [`faithful-commitment.md`](faithful-commitment.md) for the cap-write family
  close), not a modelled gate. The earlier per-effect refinement classes
  (`VALUE_FORCED`, whole-kernel-freeze) appear in `RotatedKernelRefinement*` (e.g.
  `RotatedKernelRefinementMisc.lean:30,629`).

- `Dregg2.Circuit.ClosureFinal` bundles them into **one** parametric floor.
  `ClosedWitness` (`structure`, `ClosureFinal.lean:131`) carries, for the published
  effect only, the `WitnessDecodes` existence rung + the single `ClosedLogExtract`
  decode + the `logHashInjective` log enrichment — "one floor, parametric in
  `pi.effect`; NOT a 36-way family" (`:117-123`).
  `lightclient_unfoolable_circuit_sound` (`:161`) is the headline on exactly the
  standard SNARK-soundness foundations. `closedWitness_of_readouts` (`:202`) builds
  that floor from the genuine `ClosureReadouts` bundle whose `ext` routes through
  every proven `<e>_closedLog` rung (`:190-196`) — keeping the per-effect rungs
  load-bearing, not decorative.

- `Dregg2.Circuit.ClosureForest.lightclient_unfoolable_circuit_sound_turn`
  (`ClosureForest.lean:144`) is the **whole-turn closed apex** over heterogeneous
  effects (`hidx` identifies each step's descriptor as `Rfix e` for any effect, freely
  mixed) — no transfer-only residual. Non-vacuity is exhibited:
  `closedLogExtract_family_covers_mixed` (`:190`) inhabits the rung at cellSeal/revoke/
  mint simultaneously; `lightclient_unfoolable_circuit_sound_turn_empty` (`:239`)
  shows the floors jointly compose.

- `Dregg2.Circuit.CircuitSoundnessAssembled` instantiates the apex at the concrete
  `Rfix`/`kstepAll`/`hrefinesAll`: `kstepAll := dispatchArm`
  (`CircuitSoundnessAssembled.lean:546`), `EffectDecodeBridge` *is*
  `descriptorRefines … (kstepAll e)` (`:576`), and `hrefinesAll` (`:593`) assembles
  the per-effect bridge family into the apex's `∀`.
  `lightclient_unfoolable_assembled` (`:606`) and
  `lightclient_turn_unfoolable_forest_assembled` (`:629`) are the capstones. The
  registry the apex quantifies over is `v3RegistryHeap` (`:139`, 59 entries `:254`)
  — the DEPLOYED after-spine/insert descriptors: the faithful 8-felt heap/fields
  writes (`Rfix 56`/`Rfix 39`), the three accumulator sorted-INSERTs over
  `effAccumInsertV3` (`Rfix 27/28/17`, `:227-253`), and the cap-write family's
  keystone wrappers (`Rfix 1/2/10/11/14/19/55`, `:498-537`) — grounded in
  [`faithful-commitment.md`](faithful-commitment.md). `#assert_axioms` pins at
  `:752-775`.

### `Effect::Custom` — apex-covered IN LEAN under the named recursion carrier (VK-lift remains)

`Effect::Custom` (`circuit/src/effect_vm/effect.rs:281` — custom cell-program
dispatch) is the deployed AUTHORIZATION MODE (`Authorization::Custom { predicate }`,
`turn/src/action.rs`), not a kernel state-transition verb: it carries a recursive
sub-proof and binds it to the row's `custom_proof_commitment` / `custom_program_vk_hash`
columns. Its in-circuit soundness content is therefore the PROOF-BINDING (the bound
sub-proof verified, its PI-commitment determines its program VK), not a `FullActionA`
state move. That content is now **discharged in Lean** by `Dregg2.Circuit.CustomApex`,
under the named `EngineBinding E` (FRI-recursion) carrier — closing the
program-correctness gap the deployed STARK leaves:

- **The STAGED in-AIR verifier.** `VmConstraint2.holdsAtStaged` is the deployed row
  semantics with the ONE flip the VK epoch will carry: the `proofBind` row gate goes
  from the vacuous `True` (`DescriptorIR2.lean:570`, deployed — UNCHANGED) to the
  in-AIR recursion check `ProofBind.boundAt E env` (the row commits to a VERIFYING
  sub-proof). It is the Lean twin of laying `verify_p3_batch_proof_circuit`
  (`~/dev/plonky3-recursion`) through the Custom columns, mirroring the turn-leaf wrap
  in `circuit-prove/src/joint_turn_recursive.rs` / `ivc_turn_chain.rs`. STAGED beside
  the deployed gate — additive, no VK / registry / default touched.
  `satisfied2Staged_toCustom` PROVES a staged witness IS a `Satisfied2Custom` (the
  binding leg is CIRCUIT-FORCED, not assumed externally).
- **The companion apex.** `lightclient_unfoolable_custom` /
  `lightclient_unfoolable_custom_binds` route the Custom index through
  `Satisfied2Custom` / `proofBind_bound` / `proofBind_determined` (the §6c keystones,
  `DescriptorIR2.lean:885,911`; the local Emit lemmas `EffectVmEmitV2.lean:1286`,
  `EffectVmEmitRotationV3.lean:4307`) under a `StarkSoundCustom` staged-AIR extraction
  carrier (the exact analog of `StarkSound`). The apex now genuinely CLAIMS, for a
  verifying Custom batch: a genuine decoded kernel boundary committing to
  `pi.pre`/`pi.post` AND every active proof-binding row binds to a VERIFYING sub-proof
  whose attested VK is DETERMINED by its commitment (the anti-ghost — a forged
  commitment cannot ride). `lightclient_custom_v3_binds` CONSUMES
  `customV3_binds_proof` at the deployed `customV3` columns
  (`prmCol CUSTOM_COMMIT`/`CUSTOM_VK`). `#assert_axioms`-clean (carriers
  `EngineBinding`/`StarkSoundCustom`/`Poseidon2SpongeCR` are HYPOTHESES).

So the custom claim no longer rests on an out-of-circuit Rust trust step: it rests on
the staged in-AIR verifier + the named recursion carrier. **What remains is the
deployed VK epoch ONLY** (out of scope here): flipping the deployed `holdsAt`
`proofBind` gate `True → boundAt` is VK-affecting (re-emit the effect-VM descriptor),
and the `custom_proof_commitment` column is 4-felt / ~62-bit
(`custom_proof_bind.rs:61-70`), below the 8-felt / ~124-bit faithful-commitment floor —
the 4→8-felt lift + column re-pin is the same gated VK epoch (coordinated with the
parked umem flip). A `FullActionA.customA` executor verb is likewise bundled there (it
is a deployed-semantics change; the companion apex needs no such constructor). The
deployed Rust `dregg_circuit_prove::custom_proof_bind::verify_proof_bind`
(`circuit-prove/src/custom_proof_bind.rs`) is the realization of the staged in-AIR
verifier the light client / SDK runs until that epoch lands. Full grounding:
`docs/deos/CUSTOM-VK-AUTHORIZATION.md`; the Lean close is `Dregg2/Circuit/CustomApex.lean`.

### Other trusted-out-of-circuit surfaces — the sovereign off-AIR pair

`Effect::Custom` is not the only check the EffectVM AIR records-but-does-not-force.
Two sovereign-cell surfaces are also off-AIR (honest, named in the Rust, but the
bare aggregate STARK does not witness them):

* **Sovereign witness signature + sequence** — the AIR carries only a 4-felt key
  digest (`SOVEREIGN_WITNESS_KEY_COMMIT`) + a `SOVEREIGN_WITNESS_SEQUENCE`
  (`pi.rs:223-235`); the actual Ed25519 signature is verified off-AIR
  (`turn/src/executor/authorize.rs:889 verify_ed25519_signature`) and replay is the
  off-AIR monotonic chain-walk. By design the signature binds the full 256-bit key
  off-circuit (`pi.rs:217-222`).
* **Sovereign inner transition proof (Phase 2)** — `SOVEREIGN_TRANSITION_PROOF_*`
  (`pi.rs:240-250`) is recursively verified off-AIR (`pi.rs:209-213`;
  `proof_verify.rs:2485`); the VK binding is **sentinel-zero today** (STAGED — the
  recursive verifier is a follow-up).

A full op-by-op audit (every AIR op classified genuinely-enforced / fail-closed-bus
/ trusted-out-of-circuit, plus the re-verdict on "proofBind was the last vacuous
gate" and `countOpenFronts = 0`) is `docs/deos/EFFECTVM-AIR-VERIFICATION-CENSUS.md`.

## Whole-history aggregation (the light client over a chain)

`Dregg2.Circuit.RecursiveAggregation` lifts single-turn soundness to a whole history.
`light_client_verifies_whole_history` (`RecursiveAggregation.lean:200`): a verified
aggregate root attests every per-step executor transition, the ordering, the genesis
pin, and a genuine final fold (`AggregateAttests`). `attested_history_is_run`
(`:234`) exposes the whole history as a `Run recChainedSystem` from genesis;
`attested_history_conserves` (`:247`) and the verification-derived
`conserves_from_verification` (the CRITICAL-3 closure, `:252` ff.) inherit
conservation over the whole history **without re-executing a single turn**. The named
residual is exactly the uncommitted receipt **log**: it blocks the full `Run` (which
needs `StateChained`) but never conservation, which reads only the kernel
(`:227-233`).

## Settlement soundness

`Dregg2.Circuit.SettlementSoundness.settlement_soundness`
(`SettlementSoundness.lean:210`) extends single-transition unfoolability across a
settlement: authority is live-at-settlement (`settled_revocation_bounded` `:139`,
`settled_revocation_immediate` `:150`, `finalized_commit_binds_revoked` `:168`).
`settlement_soundness_single_machine` (`:251`) is the n=1 collapse; `settlement_bites`
/ `settlement_gap_real` (`:314`,`:324`) witness it non-vacuous.

## The light-client data structures

`Dregg2.Lightclient/` carries the verifier-side proofs (crypto enters only as the
named `Poseidon2SpongeCR` carrier; `#assert_axioms` clean on every theorem):

- `MMR` (`Lightclient/MMR.lean`) — the Merkle Mountain Range append-only log. Perfect
  binary trees (`PTree`), `hashOf_injective` under CR (`:101`), `Forest` push/append
  (`:152` ff.), `forestLeaves_peaksOf` round-trip (`:202`).
- `AttestedQuery` (`Lightclient/AttestedQuery.lean`) — verified range queries with
  **completeness**: `Gap` exclusion (`:97`), `answer_sound` / `answer_complete`
  (`:157`,`:166`), `gapsOf_covers` (proves no key in the range is omitted, `:259`),
  `verifies_iff_exact` (`:323`), and `root_pins_verifies` tying it to a committed
  root under CR (`:348`).
- `HistoryIndex` (`Lightclient/HistoryIndex.lean`).

## Axiom hygiene

The whole apex chain is `#assert_axioms`-clean — its axiom footprint is
`⊆ {propext, Classical.choice, Quot.sound}` (no `sorryAx`). Asserted on
`lightclient_unfoolable`, `lightclient_turn_unfoolable`, the §9 log-seam theorems, and
the `CommitSurface`/`StateDecode` faithfulness lemmas (`CircuitSoundness.lean:1047-1064`);
on `lightclient_unfoolable_one` and `lightclient_unfoolable_circuit_sound`
(`ClosureFinal.lean:267-270`); on `lightclient_unfoolable_circuit_sound_turn` and the
non-vacuity teeth (`ClosureForest.lean:280-283`); on `lightclient_unfoolable_assembled`,
`hrefinesAll`, and the `Rfix` registry pins (`CircuitSoundnessAssembled.lean:752-775`);
on `settlement_soundness`
(`SettlementSoundness.lean:244`,`:282`). The crypto facts (`StarkSound`,
`Poseidon2SpongeCR`, the CR set, `logHashInjective`) are **typeclass/Prop hypotheses**,
never axioms.
