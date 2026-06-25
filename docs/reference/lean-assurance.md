# Lean: the assurance case

The assurance case is the *reading* artifact of the `Dregg2` Lean metatheory: it states the
top-level guarantees the system makes to a light client and, under each one, assembles exactly
the keystone theorems that discharge it as a small theorem-DAG. It answers "why should I trust a
Q-chain?", organized by guarantee rather than by when the work landed.

Two files carry the case:

- `metatheory/Dregg2/AssuranceCase.lean` — the load-bearing apex, organized **by guarantee**.
- `metatheory/CLAIMS.md` — the skeptic-facing human-readable ledger; its machine-checked half is
  `Dregg2/Claims.lean`, the corpus-wide CI pin-net.

`AssuranceCase` proves little new mathematics: each guarantee is either a thin new aggregation
theorem conjoining its existing keystones into one statement, or a re-pin of a single existing
theorem that already *is* the apex (`AssuranceCase.lean:12-16`).

## The hygiene check: `#assert_axioms`

The credibility mechanism is the `#assert_axioms` command (defined in `Dregg2/Tactics.lean`). It
elaborates to an *error* unless the named declaration's entire axiom set is exactly the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}`
(`Dregg2.cleanAxioms`, `Tactics.lean:31`; the elaborator, `Tactics.lean:50-52`). In particular it
fails on any kernel open-hole / faked-green axiom (`Tactics.lean:47-49`). So `lake env lean
Dregg2/Claims.lean` is itself the credibility artifact: a silently-regressed keystone breaks the
build *at the ledger* (`CLAIMS.md:7-13`).

Every guarantee apex in `AssuranceCase.lean` is immediately followed by `#assert_axioms` on itself
plus on each keystone in its DAG. The §8 cryptographic carriers enter as typeclass parameters /
`Prop` hypotheses, not `axiom`-keyword declarations, so they do **not** appear in `collectAxioms`
— a theorem taking them as hypotheses is genuinely kernel-clean and is pinned
(`CLAIMS.md:45-50`, `AssuranceCase.lean:24-26`).

## The assumption floor (§8 carriers)

The guarantees are kernel-unconditional *modulo* an explicit set of cryptographic-hardness /
liveness assumptions, enumerated in `AssuranceCase.lean:21-48`. These enter as `Prop`-portals,
never as `axiom`:

1. Poseidon2-permutation collision-resistance (sponge / Merkle / state-commitment / MMR CR reduce
   to it).
2. BLAKE3 collision-resistance (out-of-circuit content/transcript hash).
3. ed25519 EUF-CMA (turn / strand-block signatures).
4. HMAC (PRF/MAC) unforgeability (macaroon caveat-chain tags, `Authority.CaveatChain`).
5. AEAD confidentiality+integrity (sealed-value / disclosure payloads).
6. Discrete-log hardness (Pedersen value commitments, `Crypto.Pedersen`).
7. FRI / the STARK soundness chain (the one recursion obligation
   `RecursiveAggregation.EngineSound.recursive_sound`).
8. PostGSTProgress — post-GST network synchrony (the consensus liveness carrier
   `World.gst_liveness`).

The case asserts no other load-bearing assumption: no trusted executor, no out-of-band "this turn
was authorized" premise, no uncommitted post-state field (`AssuranceCase.lean:43-48`).

## The five guarantees

Stated `AssuranceCase.lean:52-61`, each realized as a named theorem with its DAG pinned.

### A — Authority

*No effect confers more authority than was held.* Apex: `authority_guarantee`
(`AssuranceCase.lean:166`) conjoins (1) an introduction's conferred cap is a non-amplifying subset
of the held cap (`EffectsAuthority.introduce_non_amplifying`) with (2) the teeth — a grant
conferring an authority the holder lacks is rejected, so the predicate is two-valued, not `:=
True` (`EffectsAuthority.amplifying_grant_rejected`).

The CapTP-handoff dispatcher gate is `AuthModes.captp_granted_le_held` (when a handoff admits,
`granted.rights ≤ held.rights`), with per-mode soundness `captp_sound` / `bearer_sound` /
`token_sound` (`AssuranceCase.lean:112-120`, pinned `:177-180`). A per-mouth coverage list pins
every authority-conferring verb path — `introduceA`, `delegateAttenA`, `attenuateA` /
`refreshDelegationA`, `revokeDelegationA`, `exerciseA`, `setPermissions`, stored caps
(`CapSlotFactory.no_forge_from_storage`), and production/mint gated on the issuer cap
(`AssuranceCase.lean:124-148`, pins `:186-195`). The WHO leg (`credentialValid`) is the §8
`AuthPortal` portal routed to ed25519/HMAC, not a proven scheme (`:149-152`).

### B — Conservation

*Per asset, the resource sum is identically zero on every reachable state.* W1 (DREGG3 §2.2):
`AssetId := CellId`; every asset is its issuer cell, the issuer's own balance row carries
−supply, and no verb moves any asset's sum (`AssuranceCase.lean:204-209`).

- `conservation_guarantee` (`:259`): on every state reachable from a value-empty genesis,
  `∀ a, recTotalAsset s.kernel a = 0` (body: `ReachableConservation.reachable_total_zero`).
- `conservation_guarantee_step` (`:269`): a transfer (`src ≠ dst`) leaves the moved asset's total
  invariant and every other asset pointwise untouched (no cross-asset leakage).
- Non-vacuity tooth: `IssuerMove.recKMintAsset_breaks_exact` — the *legacy* supply-increment mint
  provably breaks the value law, so the issuer-move reshape is a repair, not a relabeling (`:293-296`).
- Production-authority E2: `Circuit.Spec.SupplyCreation.mintA_authorized`, bound as a genuine iff
  over the independent `MintASpec` via `execMintA_iff_spec` — not a bare gate-extract (`:287-292`).

Floor: none beyond integer arithmetic (`:231`).

A **deployment correspondence** section names — does not claim closed at that point — that
devnet genesis seeding and the legacy atomic fee epilogue were outside the value-empty-genesis
hypothesis (`:235-249`). The later rotation section reports these **discharged on the deployed
chain**: signed-well `i64` balance, genesis value entering only by issuer-moves
(`node::genesis::GenesisMove`), and fees routed as moves to a fee well (`TurnExecutor::fee_well_cell`)
(`AssuranceCase.lean:1045-1056`).

### C — Integrity

*A receipt binds the WHOLE post-state; a tampered input is rejected.*

- `integrity_guarantee` (`:412`): over the live executable move (`recCexec`), the total
  projection (`uproj`) of the post-state — every kernel field + the receipt log onto one
  domain-tagged universal address space — equals the fold of the verb's emitted Blum trace over
  the pre-state projection. Body: `UniversalBridge.move_is_memory_program`. This is "the executor
  is a memory program" re-exposed as the integrity apex, no longer a `True` anchor (`:401-411`).
- `integrity_guarantee_whole_turn` (`:452`): the per-verb binding composed to the whole gated
  forest run `execFullForestG s f = some s'` — the body behind the `dregg_exec_full_forest_auth`
  FFI — with the per-step coverage as an explicit hypothesis `hcov`.
- `integrity_guarantee_whole_turn_covered` (`:486`): the same with `hcov` **derived** from the
  syntactic covered-language condition (`∀ p ∈ lowerForestG f, IsCoveredPair p`), covering both
  the field-write arm (`setFieldA`/gwrite) and the value-transfer arm (`balanceA` / `recCexecAsset`),
  non-vacuously (`:472-485`).

Supporting keystones: `argus_commits_to_one_receipt`, `argus_circuit_executor_receipts_agree`,
`CommitmentCrossBind.runnable_binds_same_system_roots`, and the field-drop teeth
`CommitmentCrossBind.chC_bad_not_bridge` (a commitment that drops a field is not a faithful bridge)
(`AssuranceCase.lean:316-326`, pins `:516-523`). The §149 strengthening discharges the cross-AIR
PI-binding hypothesis onto the published MMR via `argus_published_index_pins_receipt` /
`published_position_pins_value` (`:328-340`, pins `:526-528`). Floor: Poseidon2-permutation-CR
(`:352-355`).

### D — Freshness

*No replay / double-spend; a committed spend's nullifier was fresh; revocation at finality.* Apex:
`freshness_guarantee` (`:581`) — if `interp (noteSpendStmt nf) k = some k'`, then `nf` was not
already spent, is now in the set, and a same-nullifier spend on the result fails closed (bodies:
`noteSpendStmt_no_double_spend` / `_inserts` / `_then_reject`). The anti-replay is the term's own
`interp`, not an out-of-band side table (`:543-545`).

Supporting: `noteSpendStmt_replay_rejected` (the two-valued teeth), `NonMembership.nonmembership_sound`
/ `_complete` (the sorted-tree non-membership witness), `Liveness.revocation_needs_consensus`
(revocation is consensus-bound), and the R7 stored-cap retrieval-epoch rule
`CapSlotFactory.{stored_cap_only_fresh_if_epoch_unrevoked, revoke_stales_stored_cap,
store_then_revoke_refused}` (`AssuranceCase.lean:542-564`, pins `:592-604`). Floor: Poseidon2-CR
and PostGSTProgress for the revocation leg (`:566-567`). A named residual: the node's MCP gateway
binds biscuit-cap height-expiry but consults no revocation registry, outside this guarantee's
statement (`:569-574`).

### E — Unfoolability

*A light client verifying a Q-chain learns A–D for the whole history while re-witnessing nothing.*
Apex: `unfoolability_guarantee` (`:666`) conjoins (1) `light_client_verifies_whole_history` — checking
only `verify agg.root = true` ⇒ every turn executed correctly, correctly ordered, final root is the
genuine fold — with (2) `conserves_from_verification`: the whole history conserves value, **derived
from verification** with no prover-supplied `StateChained` hypothesis (the CRITICAL-3 closure)
(`:655-664`).

Supporting: `tampered_aggregate_cannot_bind` (a reordered chain forces `ChainBound = False`),
`leaf_pairing_defeats_swap`, `HistoryAggregation.root_tooth_pins_kernel` (the matching roots ⇒
adjacent kernels coincide as *state*, not just commitment), and the game-based reduction
`Crypto.LightClientUC.unfoolable_of_floor` / `fooling_breaks_floor` (light-client soundness reduces
to STARK/Fiat-Shamir extractability + sponge-CR binding) (`AssuranceCase.lean:614-642`, pins
`:684-709`). Floor: FRI/STARK soundness, Poseidon2-CR, ed25519, PostGSTProgress (`:640-642`).

## R — the running entry

The five guarantees above are stated over the abstract kernel. `running_entry_sound` (`:763`)
re-establishes A∧B∧C over `execFullForestG` — the body behind the `dregg_exec_full_forest_auth`
FFI the deployed node actually invokes (`AssuranceCase.lean:712-727`). For one committed gated
forest run it conjoins: B (every asset's `recTotalAsset` preserved, unconditionally, via
`execFullForestG_conserves_exact`), A (every delegation edge non-amplifying, `execFullForestG_no_amplify`),
and C-c1 (every node attests `gatedActionInvG`, `execFullForestG_each_attests`). The gate is
two-valued — `execFullForestG_unauthorized_fails`: any failing leg ⇒ `none` (`:793-794`). The
cap-authority leg is annotated as grounded in transcribed seL4 `derive_cap` semantics under the
named `SeL4DeriveNonAmpBridge` assumption (`:771-777`).

## The composed security theorem

`deployed_system_secure` (`:886`) is the single apex whose conclusion is the **conjunction** A ∧ B
∧ C ∧ D ∧ E over the deployed system's actual products (`AssuranceCase.lean:798-825`). Crucially the
authority/value/integrity legs all bind the **same** committed forest `execFullForestG s f = some s'`
/ the same `s → s'` transition (the MEDIUM-7 subject-unification): A = `execFullForestG_no_amplify`,
B = `execFullForestG_conserves_exact`, C-c1 = `execFullForestG_each_attests`, C-c2 = the whole-turn
memory program `execFullForestG_is_memory_program` (`MemProgTrans UC s s'`) over the *same* `(s,f,s')`,
D = the noteSpend anti-replay triple, E = `light_client_verifies_whole_history` +
`conserves_from_verification` over a published aggregate (`:850-878`, proof `:922-940`). The
guarantees chain — a single committed forest is simultaneously non-amplifying, conserving, and
integrity-attesting; the same verified history is fresh and unfoolable (`:822-824`).

## Named boundary seams

Beyond the §8 floor, the case names exactly three host-side seams between the verified surface and
the deployed node — *not* Lean hypotheses (nothing `#assert_axioms`-rests on them), but the
admission/coverage boundary of the running system (`AssuranceCase.lean:946-999`):

1. **The prover partition** — the Lean-emitted descriptor prover (`EffectVmDescriptorAir`) is the
   default for the graduated turn shapes (`sdk/src/full_turn_proof.rs` `CUTOVER_READY_SELECTORS`);
   other shapes fall back, logged, to the legacy hand-written AIR
   (`circuit/src/effect_vm_p3_full_air.rs`) — for those, circuit⟺kernel agreement is test-attested,
   not theorem-attested (`:956-966`).
2. **`ShadowHostCtx` host-fed admission inputs** — five values the host supplies
   (`turn/src/lean_shadow.rs`); the IF–THEN is discharged by `Exec.HostCorrespondence`
   (`admissible_sound_of_reflects` + the obligation teeth), leaving a producer-coverage engineering
   obligation, not a cryptographic one (`:968-990`).
3. **Producer coverage** — which turns route to the verified Lean executor
   (`lean_shadow::producer_root_agreeing_effects`); `running_entry_sound` quantifies over every
   forest the FFI is invoked on, and this seam is which turns get there (`:992-999`).

A low-severity circuit residual (the F3-retired field-seal `RESERVED` column, prover-chosen but
depended on by no surviving semantics) is also named (`:1001-1006`).

## The CLAIMS ledger and honesty labels

`CLAIMS.md` is the human-readable half. What "PROVED" means is load-bearing, not preface: exactly
the cited theorem and its labelled seams — a green ledger is **not** a verified distributed OS, not
verified consensus, not verified cryptography (`CLAIMS.md:15-21`). The labels (`CLAIMS.md:25-30`):

- **PROVED-axiom-clean** — `collectAxioms` is exactly the three kernel axioms; pinned in
  `Dregg2/Claims.lean` (build-enforced).
- **PROVED (home-pinned, parked)** — same strength and self-pinned in its home module, but its
  `.olean` is not yet in `Claims.lean`'s import closure (a concurrent-edit race); central pin
  commented out so `lake env lean` stays exit-0.
- **rests-on-§8-primitive** — real and open-hole-free, but stated over an explicit labelled
  interface obligation (a `CryptoKernel` / `World` / `Verifiable` law, the `Privacy` predicates);
  these enter as typeclass parameters, so downstream theorems stay clean.
- **honest-OPEN** — a genuine open obligation carried as a named residual `Prop`, an explicit
  hypothesis, or a prose `-- OPEN:` note — never an open hole.

The corpus has **zero open holes, zero `admit`s, zero `native_decide`** (`CLAIMS.md:32-34`,
verified by a whole-corpus scan). The only `axiom`-keyword declarations are the two clearly-named
demo axioms in `Dregg2/Widget/Basic.lean` (`demoEd25519VerifyExtern` / `demoUnvettedAssumption`),
deliberately not pinned (`CLAIMS.md:34-37`).

`Dregg2/Claims.lean` currently build-enforces 165 theorem pins plus 50 whole-namespace pins (plus 20
parked, commented out) per the count stated in `CLAIMS.md:59-61`; the file itself is the authoritative
inventory. The still-genuinely-open debt list is tabulated `CLAIMS.md:148-159` (CordialMiners
liveness/dissemination/Stingray, the synchronizer↔`World.rand` coupling, the `Coordination`
mu-recursion projection, the `Proof.Refine` full simulation diagram, the handler-transformer upper
tiers, and the three epoch/snapshot circuit-soundness write-forcing residuals).

## How to re-check

```
cd metatheory
lake env lean Dregg2/Claims.lean   # must exit 0 — reads oleans, writes none; never `lake build` mid-swarm
```

Exit 0 ⇒ every pinned keystone is free of the kernel open-hole axiom. A non-zero axiom-hygiene
FAIL means a claimed keystone silently inherited an open hole — that breakage, at the ledger, is
the whole point (`CLAIMS.md:180-191`).

## Division of labor

- **`AssuranceCase.lean`** — the load-bearing assurance apex, by guarantee; the five guarantee
  aggregations + their direct-DAG keystones, kernel-triple clean (`AssuranceCase.lean:1088-1092`).
- **`Claims.lean`** — the comprehensive per-keystone CI pin-net (corpus-wide), subordinate to
  `AssuranceCase`; retired as a chronological journal, retained as the whole-corpus pin-ledger
  (`AssuranceCase.lean:1080-1086`).
- **`scripts/axiom-hygiene-guard.sh`** — the textual whole-corpus open-hole grep
  (`AssuranceCase.lean:1092`).
