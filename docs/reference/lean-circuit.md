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
(`CircuitSoundness.lean:16-22`).

## The three load-bearing pieces

1. **`StateDecode`** — the faithful witness→kernel-state decode
   (`CircuitSoundness.StateDecode`, `CircuitSoundness.lean:190`). It says the
   witness's published OLD/NEW commitments *equal* the surface commitment of the
   bound kernels (`preBinds`/`postBinds`) over a fixed `CommitSurface`, and that
   those kernels are `AccountsWF`. Faithfulness is **not assumed**: it is a theorem.
   `stateDecode_pre_faithful` / `stateDecode_post_faithful`
   (`CircuitSoundness.lean:204`, `:213`) prove that two states decoding the *same*
   published commitment have *equal* kernels — by `CommitSurface.commit_binds`
   (`CircuitSoundness.lean:147`), which is `recStateCommit_binds_kernel` repackaged:
   the commitment binds the kernel under the Poseidon CR set, using **no** authority
   gate and **no** frame assumption.

2. **`descriptorRefines d kstep`** — the per-effect rung
   (`CircuitSoundness.descriptorRefines`, `CircuitSoundness.lean:235`): any
   `Satisfied2` witness of descriptor `d` whose published commitments decode (via a
   faithful `StateDecode`) to `pre`/`post` forces `kstep pre post`. Its antecedent is
   the named hash-CR carrier `Poseidon2SpongeCR hash` (`:237`) — the floor the
   per-descriptor published-PI↔limb binding consumes. This is the genuine obligation
   each effect discharges; the apex carries the registry-wide family of these.

3. **`lightclient_unfoolable`** — the apex (`CircuitSoundness.lean:570`). Its only
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
(`CircuitSoundness.lean:570` ff.). The derivation chain: `StarkSound` extracts a
`Satisfied2` witness of the *claimed* descriptor whose published commitments are
`pi.toPublished` → `WitnessDecodes` produces `pre`/`post` with a `StateDecode` →
`hrefines` turns witness + decode into `kstep pi.effect pre post` → the decode's
binding re-exports `pi.pre`/`pi.post` as the genuine endpoint commitments.

The **carried obligations ledger** — every named, deferred premise (nothing
laundered to `True` or an open hole):

- **`StarkSound hash R`** (`class`, `CircuitSoundness.lean:482`) — the p3
  batch-STARK soundness / FRI extraction: a verifying batch yields a `Satisfied2`
  witness of the claimed descriptor whose published PI agree with `pi`. **No longer
  terminal-by-design:** `starkSound_of_verifyAlgo` (`FriVerifierBridge.lean:101`) makes
  it a THEOREM over the specified `verifyAlgo`, resting on `AlgoStarkSound` (the FRI-LDT
  floor) + `DeployedRefines`. The BBHR18/BCIKS20 FRI proximity algebra is itself PROVED
  in `FriSoundness.lean` resting only on the hash floor `HashCR` (`friProximityK8_discharge`,
  composed at `d=0` via `FriBridgeDeployedArity`). The deployed-parameter `FriLdtDeployedBound`
  **as written is DISCHARGED** (`FriLdtJohnson.lean`, `friLdtDeployedBound_discharge`, axiom-clean):
  at the Johnson radius `δ_J = 1−√ρ = 7/8` the statement is the trivial counting else-branch
  (`accept_prob_le_of_farN`), so `ldt_bound_unconditional` re-derives the `2⁻⁵⁷` LDT payoff with no
  hypothesis. Its genuine BCIKS20 residual (words inside the `δ_J` ball, past unique decoding) is
  two precisely-named lemmas — `RSListBound` (RS list-size) and `FriProximityGapChallenges`
  (bounded good folding challenges) — and both are DISCHARGED at `L>1` on the deployed
  rate-`1/64` code, past the unique-decoding radius: `rsListBound_johnson_112`
  (`FriLdtJohnsonList.lean:193`) proves `RSListBound (codeC 6 ω) 112 15` at the Johnson radius
  `112 = ⌊(7/8)·128⌋` by a Fisher/packing double-count (the dimension-2 code's pairwise agreement
  `≤ 1` makes the quadratic bite), and `FriProximityGapWitness.lean` CONSTRUCTS the BCIKS20
  `BadChallengePoly` witness at `L > 1` (`wrap_friProximityGap_johnson`: `dOut = 112`, `dIn = 42`,
  `L ≤ 26`), discharging `FriProximityGapChallenges` — both `#assert_axioms`-clean. The packing
  method's honest scope is `dIn ≤ 42` of `64` (not the folded code's own Johnson radius `56`);
  relative-distance preservation past that is the correlated-agreement statement. The `L>1`
  correlated-agreement primitive is PROVED at deployed-relevant list sizes by the ordered-pair counting method
  (`FriCorrelatedAgreementSharp.lean`): `L ≤ 186` at the **interior** radius `dIn=52` (relative
  `13/16`, GS-non-degenerate — `wrap_correlatedAgreementLine_interior`) and `L ≤ 292` at the
  **boundary** radius `dIn=56` (relative `7/8` — `wrap_correlatedAgreement_sharp_proved`); the
  deployed analysis prefers the interior. The **GS-ideal `L ≤ 2·|κ| = 128` is BLOCKED** — the
  Guruswami–Sudan interpolation delivers no bound for the constant-fold *multiset* received word
  (fibre-concentration; `metatheory/Dregg2/ForMathlib/GuruswamiSudan.lean:20-33` is the authority),
  so `186`/`292` is the sharpest counting reach, not the GS ideal. Security is unaffected: the list
  term is `L/|F|` with `|F| ≈ 2^124`, ~`2⁻¹¹⁶` of headroom. See `STARK-SOUNDNESS-CENSUS.md`.
- **`Poseidon2SpongeCR hash`** + the `CommitSurface` CR fields (`CommitSurface`,
  `CircuitSoundness.lean:116-137`) — the standard Poseidon collision-resistance set
  (`cmbInj`, `compInj`, `compNInj`, `leafInj`, `restFrame`) the full-state root
  `recStateCommit` binds under. Realizable; bundled, never an axiom.
- **`hrefines`** — the per-effect refinement family, the genuine remaining rung work
  (discharged effect-by-effect downstream).
- **`WitnessDecodes hash R S pi`** (`def`, `CircuitSoundness.lean:563`) — the
  witness→kernel-state **existence** rung: a witness publishing `pi` decodes to some
  `(pre, post)`. A light client cannot supply `pre`/`post`; this rung supplies them
  (the surjectivity of the commitment surface on the published roots). Carried
  explicitly, never discharged by assuming the conclusion.

The minimal honest STARK-batch interface (`VerifyKey`, `vkOfRegistry`,
`BatchPublicInputs`, `verifyBatch`, `Verdict.accept`, `StarkSound`,
`tracePublishedCommit`) is **defined here** because none existed
(`CircuitSoundness.lean:295` ff.); `verifyBatch` runs the *specified* batch-STARK
verifier — only low-level primitives stay `opaque`, validated by the differential
KAT corpus against the deployed Rust (`:356-365`) — and the apex reasons only
through the verdict and the `StarkSound` extraction.

## Scope — what the apex proves, and the freshness boundary

`lightclient_unfoolable` proves **single-transition** soundness: every accepted batch
decodes to a genuine kernel step committing to `pi.pre`/`pi.post`, taking `pi.turn`
as given. It establishes **nothing** about whether that transition is *fresh*
(unreplayed) or its ordering (the SCOPE note, `CircuitSoundness.lean:512-543`).

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

- `stateDecodeChain_frame_continuous` (`CircuitSoundness.lean:282`) — equal published
  seam commitments + faithfulness force `a.post.kernel = b.pre.kernel`.
- `TurnDecodeChain` (`structure`, `CircuitSoundness.lean:687`) — a turn threaded
  left-to-right; `turnDecodeChain_seam_kernel_derived` (`:710`) proves the kernel
  half of every seam from the published kernel-root column (the frame **tooth**: a
  prover whose published seam disagrees with the threaded kernel is rejected).
- `turnDecodeChain_refines_turnSpec` (`:750`) folds the per-step `descriptorRefines`
  along the chain into `∃ acts, turnSpec start acts fin`.
- `lightclient_turn_unfoolable_forest` (`:953`) — the whole-turn headline: a verified
  turn + the per-effect family + floors ⟹ a genuine `execFullTurnA s acts = some s'`
  whose endpoints commit to the published turn-level `(pre, post)`.

### The receipt-log seam (§9)

`recStateCommit` is kernel-only — it does not bind the `RecChainedState.log` receipt
chain — so the full-state seam carried its **log** half as a free residue. §9 closes
it, mirroring the kernel tooth: `LogDecode` (`CircuitSoundness.lean:1008`) binds
published log commitments to `pre.log`/`post.log` through the realizable
`logHashInjective LH` carrier; `logDecodeChain_frame_continuous` (`:1031`) forces
`a'.log = b.log` across a seam; `turnDecodeChainLog_seam_full_derived` (`:1102`)
recovers the whole `RecChainedState` continuity `a.post = b.pre` on both components;
`turnDecodeChainLog_rejects_forged_log` (`:1125`) is the mutation-confirm — a forged
intermediate receipt-log is UNSAT. Non-vacuity of the `logHashInjective` carrier is
exhibited inline (`:1148` — a collapsing hash cannot be injective).

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
  (`CircuitSoundnessAssembled.lean:630`), `EffectDecodeBridge` *is*
  `descriptorRefines … (kstepAll e)` (`:660`), and `hrefinesAll` (`:667` ff.) assembles
  the per-effect bridge family into the apex's `∀`.
  `lightclient_unfoolable_assembled` and
  `lightclient_turn_unfoolable_forest_assembled` are the capstones. The
  registry the apex quantifies over is `v3RegistryHeap` (`:141`, 61 entries
  `v3RegistryHeap_length` `:285`) — the DEPLOYED after-spine/insert descriptors:
  the faithful 8-felt heap/fields writes (`Rfix 56`/`Rfix 39`), the three
  accumulator sorted-INSERTs over `effAccumInsertV3` (`Rfix 27/28/17`,
  `:235-260`), and the cap-write family's keystone wrappers
  (`Rfix 1/2/10/11/14/19/55`, `:553-617`) — grounded in
  [`faithful-commitment.md`](faithful-commitment.md). `#assert_axioms` pins at
  `:836-860`.

### `Effect::Custom` — binding proven FROM THE FOLD (`CustomBindingFromFold`)

`Effect::Custom` (`circuit/src/effect_vm/effect.rs:289` — custom cell-program
dispatch) is the deployed AUTHORIZATION MODE (`Authorization::Custom { predicate }`,
`turn/src/action.rs`), not a kernel state-transition verb: it carries a recursive
sub-proof and binds it to the row's `custom_proof_commitment` / `custom_program_vk_hash`
columns. Its in-circuit soundness content is therefore the PROOF-BINDING (the bound
sub-proof verified, its PI-commitment determines its program VK), not a `FullActionA`
state move. That content is **discharged in Lean** by
`Dregg2.Circuit.CustomBindingFromFold` — grounded in the DEPLOYED fold path, with
`EngineBinding` DERIVED internally (`engineBinding_of_floor`: it reduces to
{Poseidon2-CR, FRI-factoring}), never carried as a hypothesis:

- **The deployed row gate binds nothing — proven, not suspected.** The deployed
  `proofBind` row denotation is the vacuous `True` (`DescriptorIR2.lean:601`; its
  deployed-status note `:588-593`). `Dregg2.Circuit.CustomCarrierAttack` proves this
  with a forged trace (`deployed_admits_unbacked`) and proves no uniform bridge
  `Satisfied2 ⇒ Satisfied2Staged` exists over the deployed True-gate AIR
  (`starkSoundCustom_unsound_over_deployed`): any claim routed through a staged-AIR
  extraction carrier is carried entirely by that ungrounded hypothesis.
  `Dregg2.Circuit.CustomApex` is the SUPERSEDED apex and keeps ONLY the staged-AIR
  model that refutation operates over (`Satisfied2Staged` / `holdsAtStaged` /
  `satisfied2Staged_toCustom`); the former companion theorems
  (`lightclient_unfoolable_custom` / `lightclient_unfoolable_custom_binds` /
  `lightclient_custom_v3_binds`) and the `StarkSoundCustom` carrier are RETIRED —
  the main apex carves `Effect::Custom` out (`no_customA_arm`), so nothing consumes
  them. `Satisfied2Custom` (`DescriptorIR2.lean:998`) and the
  `proofBind_bound` / `proofBind_determined` keystones (`:1008`,`:1024`) survive, as
  does the Emit lemma `customV3_binds_proof`
  (`Emit/EffectVmEmitRotationV3.lean:6076`, `#assert_axioms` at `:6096`) — its
  light-client consumer is the fold path below.
- **The grounded discharge.** `custom_binding_from_fold`
  (`CustomBindingFromFold.lean:147`): a verifying per-turn AGGREGATE — the fold
  including the custom leaf — FORCES the effect-vm leg's published custom-commitment
  PI to be backed by a verifying sub-proof (binding) whose attested program VK is
  uniquely DETERMINED by that commitment (anti-ghost). It rests ONLY on
  {the FRI floor via `AggAirSound.FriExtract` + `Poseidon2SpongeCR` + the connect} —
  the SAME floor as everything else, no custom carrier. `custom_companion_grounded`
  is the Custom light-client guarantee consuming it. Non-vacuity holds in BOTH
  polarities (`honest_companion_fires` / `forged_unsat`). `#assert_axioms`-clean
  (the floor carriers appear only as Prop HYPOTHESES).

So the custom claim rests on the per-turn aggregate FOLD binding, not on a
staged in-AIR verifier and not on an out-of-circuit Rust trust step. The commitment
columns are at the faithful floor: `custom_proof_commitment` and
`custom_program_vk_hash` are each 8 felts / ~124-bit
(`circuit-prove/src/custom_proof_bind.rs:55-71`), and on the deployed FOLD path the
custom leaf computes the PI commitment IN-CIRCUIT from the sub-proof's real public
inputs (`custom_leaf_adapter::incircuit_custom_pi_commitment`,
`circuit-prove/src/custom_leaf_adapter.rs:373`) and `connect`s it lane-by-lane to
the claimed column — a swapped or fabricated commitment has no satisfying partner
and the aggregation is UNSAT. **Named seam (VK-affecting, out of scope here):** the
deployed `proofBind` row gate stays the vacuous `True` — the binding is enforced at
the FOLD, not the row; flipping `True → boundAt` in-row is a VK epoch (re-emit the
effect-VM descriptor), bundled with a `FullActionA.customA` executor verb. Full
grounding: `docs/deos/CUSTOM-VK-AUTHORIZATION.md`; the Lean discharge is
`Dregg2/Circuit/CustomBindingFromFold.lean`.

### Other trusted-out-of-circuit surfaces — the sovereign off-AIR pair

`Effect::Custom` is not the only check the EffectVM AIR records-but-does-not-force.
Two sovereign-cell surfaces are also off-AIR (honest, named in the Rust, but the
bare aggregate STARK does not witness them):

* **Sovereign witness signature + sequence** — the AIR carries only a 4-felt key
  digest (`SOVEREIGN_WITNESS_KEY_COMMIT`, `pi.rs:240-241`) + a
  `SOVEREIGN_WITNESS_SEQUENCE` (`:247`); the actual Ed25519 signature is verified
  off-AIR (`turn/src/executor/authorize.rs:933 verify_ed25519_signature`) and
  replay is the off-AIR monotonic chain-walk. By design the signature binds the
  full 256-bit key off-circuit (`pi.rs:202-221`).
* **Sovereign inner transition proof (Phase 2)** — `SOVEREIGN_TRANSITION_PROOF_*`
  (`pi.rs:257-262`) is recursively verified off-AIR; the VK binding is
  **sentinel-zero today** (STAGED — the recursive verifier is a follow-up).

A full op-by-op audit (every AIR op classified genuinely-enforced / fail-closed-bus
/ trusted-out-of-circuit, plus the re-verdict on "proofBind was the last vacuous
gate" and `countOpenFronts = 0`) is `docs/deos/EFFECTVM-AIR-VERIFICATION-CENSUS.md`.

## Whole-history aggregation (the light client over a chain)

`Dregg2.Circuit.RecursiveAggregation` lifts single-turn soundness to a whole history.
`light_client_verifies_whole_history` (`RecursiveAggregation.lean:206`): a verified
aggregate root attests every per-step executor transition, the ordering, the genesis
pin, and a genuine final fold (`AggregateAttests`). `attested_history_is_run`
(`:297`) exposes the whole history as a `Run recChainedSystem` from genesis;
`attested_history_conserves` (`:310`) and the verification-derived
`conserves_from_verification` (the CRITICAL-3 closure, `:327` ff.) inherit
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

- `MMR` (`metatheory/Dregg2/Lightclient/MMR.lean`) — the Merkle Mountain Range append-only log. Perfect
  binary trees (`PTree`), `hashOf_injective` under CR (`:101`), `Forest` push/append
  (`:152` ff.), `forestLeaves_peaksOf` round-trip (`:202`).
- `AttestedQuery` (`metatheory/Dregg2/Lightclient/AttestedQuery.lean`) — verified range queries with
  **completeness**: `Gap` exclusion (`:97`), `answer_sound` / `answer_complete`
  (`:157`,`:166`), `gapsOf_covers` (proves no key in the range is omitted, `:259`),
  `verifies_iff_exact` (`:323`), and `root_pins_verifies` tying it to a committed
  root under CR (`:348`).
- `HistoryIndex` (`metatheory/Dregg2/Lightclient/HistoryIndex.lean`).

## Axiom hygiene

The whole apex chain is `#assert_axioms`-clean — its axiom footprint is
`⊆ {propext, Classical.choice, Quot.sound}` (no `sorryAx`). Asserted on
`lightclient_unfoolable`, `lightclient_turn_unfoolable`, the §9 log-seam theorems, and
the `CommitSurface`/`StateDecode` faithfulness lemmas (`CircuitSoundness.lean:1164-1181`);
on `lightclient_unfoolable_one` and `lightclient_unfoolable_circuit_sound`
(`ClosureFinal.lean:267-270`); on `lightclient_unfoolable_circuit_sound_turn` and the
non-vacuity teeth (`ClosureForest.lean:280-283`); on `lightclient_unfoolable_assembled`,
`hrefinesAll`, and the `Rfix` registry pins (`CircuitSoundnessAssembled.lean:836-860`);
on `settlement_soundness`
(`SettlementSoundness.lean:244`). The crypto facts (`StarkSound`,
`Poseidon2SpongeCR`, the CR set, `logHashInjective`) are **typeclass/Prop hypotheses**,
never axioms.
