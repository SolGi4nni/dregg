# dregg — Navigation Map (where is X?)

The *where-is-X* index for the dregg tree. The repo is large — **~63 Rust workspace crates**
(repo root) and **hundreds of Lean modules** under `metatheory/Dregg2/`. This file maps each major
subsystem → its directory, entry-point files, and the key theorems/types, plus how the pieces
connect. Paths are relative to the **repo root** (`…/breadstuffs/`) unless prefixed `metatheory/`.

Companion docs:
- **[`metatheory/README.md`](../README.md)** — what dregg2 *is* (the layer cake, honest assurance).
- **[`docs/rebuild/_INDEX.md`](rebuild/_INDEX.md)** — index of every design/ledger doc.
- **[`docs/guides/`](guides/)** — readable subsystem orientations (executor, circuit, distributed, authority).

The mental model: **dregg = Lean-primary truth** (`metatheory/Dregg2/*` is the source of
semantics), **dreggrs = Rust heritage** (fast shadows pinned by a Lean model + differential, or
pure infra). The runtime is mostly Rust; the *source of truth* is the Lean kernel. See
[`docs/rebuild/_DREGG-DREGGRS-MANIFEST.md`](rebuild/_DREGG-DREGGRS-MANIFEST.md).

---

## The two Lean libraries (`metatheory/`)

| Library | Root | What it is |
|---|---|---|
| **`Metatheory.*`** | `metatheory/Metatheory/*.lean` | The candidate-independent *logic of constructive knowledge & authority* (`ConstructiveKnowledge.lean`, `Categorical.lean`, `EpistemicDial.lean`, `EpistemicConsensus.lean`). Research-grade; the spec is *derived*, not postulated. |
| **`Dregg2`** | `metatheory/Dregg2.lean` (sources `metatheory/Dregg2/`) | The verification of dregg2 — the l4v-shaped library. **This is the bulk of the tree.** |

Build: `lake build` (needs the pinned mathlib). Single file during swarm work:
`lake env lean Dregg2/<Module>.lean` (race-free). Honesty artifact:
`lake env lean Dregg2/Claims.lean` re-pins every "PROVED" keystone with `#assert_axioms`.

---

## Subsystem → location index

### 1. The executor + effect model  → guide: [`guides/executor.md`](guides/executor.md)

The verified state-transition machine. dregg's ONE credential-gated turn entry.

| Piece | Location | Entry points / keystones |
|---|---|---|
| **Gated turn entry** (the ONE) | `metatheory/Dregg2/Exec/FullForestAuth.lean` | `execFullForestG` / `execFullTurnG` (the credential-gated forest executor); `execFullForestG_unauthorized_fails:949` (gate is sound). |
| **Record kernel** (verified core) | `metatheory/Dregg2/Exec/RecordKernel.lean` | `recKExec:640` (the per-turn transition); `recKExec_conserves:686`, `recKExec_authorized:703`, `recKExec_unauthorized_fails:712`, `recKExec_frame:721`; multi-asset `recKExecAsset_no_cross_asset_leak:846`. |
| **Universe-A executor** | `metatheory/Dregg2/Exec/FullForest.lean`, `Exec/EffectsState.lean`, `Exec/Effect*.lean` | `execFullA` + the per-effect `*Spec`s (the richer abstract surface circuit emission projects from). |
| **Effect catalog** | `metatheory/Dregg2/CatalogEffects.lean`, `Exec/Effect.lean`, `Exec/Handlers/` | The ~56 `CellEffect` constructors + their handlers. |
| **Concrete/efficient kernel** | `metatheory/Dregg2/Exec/ConcreteKernel.lean` | HashMap-backed; the l4v data-refinement that transfers abstract soundness to a fast runtime. |
| **Step-completeness spine** | `metatheory/Dregg2/Exec/StepComplete.lean`, `Boundary.lean` | `stepComplete_preserves` (the proved coinductive keystone over the `νF` cell). |
| **CapTP (object-cap transport)** | `metatheory/Dregg2/Exec/CapTP*.lean` | `CapTPHandoffSound.handoff_unforgeable:348`, `CapTPGC.captp_no_premature_reclaim:106` / `captp_gc_by_lease:94`, `CapTPConsentLace.*`. |
| **FFI exports** | `metatheory/Dregg2/Exec/FFI.lean` | `@[export dregg_exec_full_forest_auth]:3487` (the production entry); the ungated `dregg_exec_handler_turn` export was REMOVED:3831. |
| **Rust executor (legacy dregg1, in-flight swap)** | `turn/src/`, `cell/src/` | `TurnExecutor::execute`; `turn/src/apply.rs`. Becomes pure-dregg at cutover. |
| **The FFI bridge** | `dregg-lean-ffi/src/lib.rs` | `extern "C" fn dregg_exec_full_forest_auth_str:177`; differentials in `state_differential.rs`, `full_turn_differential.rs`. |

### 2. Circuit emission + descriptor + assurance  → guide: [`guides/circuit.md`](guides/circuit.md)

Verified-by-construction emission of the EffectVM circuit from Lean.
**Read [`docs/rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md`](rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md)
first — assurance is NOT uniform** (~12 of ~56 effects are genuine class A; ~40 are class C).

| Piece | Location | Entry points / keystones |
|---|---|---|
| **Per-effect descriptor emitters** | `metatheory/Dregg2/Circuit/Emit/EffectVmEmit*.lean` (54 modules) | `EffectVmEmitTransferSound.transferDescriptor_full_sound:238` (the class-A keystone) + `.transferDescriptor_commit_binds_state:346` + `.tampered_rejected:413`. |
| **Genuine side-table root recompute** | `metatheory/Dregg2/Circuit/Emit/EffectVmEmitEscrowRoot.lean` | `escrowRecomputeSites` / `escrowRootAdvance_forced` — promoted the escrow/bridge family to class A. |
| **Anti-ghost commitment** | `metatheory/Dregg2/Circuit/StateCommit.lean`, `EffectCommit*.lean`, `CommitmentCrossBind.lean` | The 13-column `state_commit`; `absorbed_determined_by_commit`. |
| **Witness → STARK** | `metatheory/Dregg2/Circuit/Witness/`, `Circuit/TransferWitness.lean`, `TurnWitness.lean` | Executor-derived witness → real Plonky3 `prove`/`verify` with forged-state rejection. |
| **Turn / coordinated turn emit** | `metatheory/Dregg2/Circuit/TurnEmit.lean`, `CoordinatedTurnEmit.lean`, `EmitAllJson.lean` | Whole-turn binding to ONE authenticated state root. |
| **Rust circuit (Plonky3 AIRs)** | `circuit/src/` | Hand-written AIRs (`effect_vm/*.rs`, `*_air.rs`); kept as diversity (`_RUST-CIRCUIT-CONSOLIDATION.md`). Plonky3 rev `82cfad73` (pinned in `Cargo.toml`). |
| **Verifier / codec** | `verifier/`, `wire/`, `metatheory/Dregg2/Crypto/VerifierKernel.lean`, `Exec/CodecRoundtrip*.lean` | `verify` defined as "extracted circuit is satisfiable"; FILL-J codec roundtrip proofs. |

### 3. Distributed / consensus / federation  → guide: [`guides/distributed.md`](guides/distributed.md)

The *Secure-Scuttlebutt-on-crack* federation: blocklace (block-DAG-lace) + strands (SSB feeds).

| Piece | Location | Entry points / keystones |
|---|---|---|
| **Blocklace finality** | `metatheory/Dregg2/Distributed/BlocklaceFinality.lean` | `computeRounds`, `finalLeaders_one_per_wave:332`, `findAllFinalLeaders_deterministic:320`. |
| **Strand integrity (SSB feed)** | `metatheory/Dregg2/Distributed/StrandIntegrity.lean` | `Strand:61`, `forkFree_iff_seqMonotone:138`, `strandTipSeq`. |
| **CRDT lace-merge (join)** | `metatheory/Dregg2/Distributed/LaceMerge.lean` | `mergeLace:103`; `laceIds_mergeLace:111` (the join), `merge_{comm,assoc,idem,monotone}` (semilattice). |
| **Membership safety** | `metatheory/Dregg2/Distributed/MembershipSafety.lean` | `Constitution:105`, `computeThreshold:99`, `membership_change_reparameterizes_finality:486`. |
| **Finality gate** | `metatheory/Dregg2/Distributed/FinalityGate.lean` | `gate_admits_iff_verified_finalizes:187`. |
| **Cell migration (cross-federation)** | `metatheory/Dregg2/Distributed/CellMigration.lean` | `Voucher:106`; `handoff_conserves_balance:384`, `handoff_conserves_caps:395`, `handoff_aggBalance_conserved:435`. |
| **Joint / entangled turns (N-cell atomic)** | `metatheory/Dregg2/Distributed/EntangledJoint.lean` | `jointApplyAll_atomic:162`, `jointApplyAll_conserves:244`, `joint_sound_of_binding:490`. |
| **Threshold decryption / BLS QC** | `metatheory/Dregg2/Distributed/{ThresholdDecrypt,BlsQuorumCert}.lean` | + differential `federation/src/threshold_decrypt_diff.rs`. |
| **Catchup / checkpoint / crash / epoch** | `metatheory/Dregg2/Distributed/{CatchupConverges,CheckpointPrune,CrashRecovery,EpochReconfig}.lean` | sync convergence, prune-safety, replay = checkpoint ⊕ overlay. |
| **Coordination (Stingray budget, 2PC)** | `metatheory/Dregg2/Coord/{CausalOrder,TwoPhaseCommit,SharedBudgetDynamics,StingrayCertReconcile}.lean` | `StingrayCertReconcile` (cross-epoch cert-reconciliation, REAL-Ed25519 differential). |
| **Consensus theory** | `metatheory/Dregg2/Distributed/Consensus.lean`, `Proof/{CordialMiners,Stingray,BFT,GST,Synchronizer}*.lean` | Sridhar resilience PAIR (`ResiliencePair`, `dreggDeployment`); post-GST liveness. |
| **Rust engines (dreggrs shadows)** | `blocklace/`, `coord/`, `federation/`, `net/` | The live consensus engine; Lean is its verified model + golden differential (`tau`). |
| **Node (devnet)** | `node/src/` | `main.rs`, `finality_gate.rs`, `blocklace_sync.rs`, `catchup.rs`, `executor_setup.rs` (runs through the Lean shadow). |

### 4. Authority / capabilities / caveats / tokens  → guide: [`guides/authority.md`](guides/authority.md)

Constructive knowledge: to hold a capability is to exhibit a verifying witness.

| Piece | Location | Entry points / keystones |
|---|---|---|
| **The verify/find seam** | `metatheory/Dregg2/Laws.lean`, `Spec/Guard.lean` | `Predicate ⊣ Witness`; `attenuate_narrows` (meet-semilattice). |
| **Generative capability graph** | `metatheory/Dregg2/Spec/Authority.lean`, `Authority/Positional.lean` | introduce/amplify/mint/endow + attenuate/revoke; `gen_step_traces`, `lossy_attenuation_only:200` (Miller: only connectivity begets connectivity). |
| **Caveat chains (macaroons)** | `metatheory/Dregg2/Authority/CaveatChain.lean`, `Caveat.lean`, `MacaroonDischarge.lean` | `append_narrows:230`, `chain_unforgeable:402`, `forgery_requires_mac_query:302`. |
| **Third-party discharge** | `metatheory/Dregg2/Authority/ThirdPartyDischarge.lean`, `Discharge.lean` | `honest_discharge_accepted:275`, `stale_discharge_rejected:303`, `unbound_discharge_rejected:317`. |
| **Credentials / revocation** | `metatheory/Dregg2/Authority/{Credential,CredentialAttenuation,ClearanceGraph}.lean` | `credential_verifies_iff_issued_and_not_revoked:155`, `revoke_blocks_verify:180`. |
| **Selective disclosure / DV / biscuit** | `metatheory/Dregg2/Authority/{SelectiveDisclosure,DesignatedVerifier,BiscuitGraph,CDT,CSpace}.lean` | the caveat/attestation dial-cube faces. |
| **Executor admission (token gates exec)** | `metatheory/Dregg2/Exec/{Admission,AuthModes,AuthTurn,Caps}.lean` | the credential model on the critical path. |
| **Rust crates (dreggrs)** | `macaroon/`, `token/`, `credentials/`, `discharge-gateway/` | pinned by `Authority/*` (real HMAC fold relative to `MacUnforgeable`). |

### 5. Intent / agents

| Piece | Location | Entry points |
|---|---|---|
| **Intent core (receipt ⊣ intent)** | `metatheory/Dregg2/Intent/{Core,Resource,Match,Kernel,KernelBridge}.lean` | the four-faced Intent + fulfill (counit); coend `Match`. |
| **Intent lifecycle / centers / auctions** | `metatheory/Dregg2/Intent/{Lifecycle,Centers,Ring,RingFFI,SealedAuction}.lean` | conservation-as-`AddMonoidHom`, Drinfeld centers, ring-of-intents. |
| **Agent mandate** | `metatheory/Dregg2/Agent/Mandate.lean` | the mandate predicate the executor enforces. |
| **Rust** | `intent/`, `demo-agent/` | verified-gate finalize lifts the executor reference in. |

### 6. Crypto portals (§8 — soundness is the portal's job, never Lean's)

| Piece | Location | Entry points |
|---|---|---|
| **Primitives (Layer A)** | `metatheory/Dregg2/Crypto/{Pedersen,Merkle,NonMembership,CommitmentBinding}.lean` | Poseidon2 `compress` / Pedersen `commit`+`commit_hom` (algebraic laws proved); hardness as honest `Prop` carriers. |
| **Verifier kernel (Layer B)** | `metatheory/Dregg2/Crypto/VerifierKernel.lean` | `verify` = "extracted circuit satisfiable"; `*_verify_sound` derived. |
| **Predicate kernel (Layer C)** | `metatheory/Dregg2/Crypto/PredicateKernel.lean` (+ `PrivacyKernel.lean`) | per-kind `KindObligation`s wiring `EpistemicDial`. |
| **Named crypto hyps ledger** | [`docs/rebuild/_CRYPTO-HYPOTHESIS-LEDGER.md`](rebuild/_CRYPTO-HYPOTHESIS-LEDGER.md) | every load-bearing assumption: DISCHARGED vs IRREDUCIBLE PRIMITIVE. |
| **Rust** | `commit/`, `hints/` (BLS12-381+KZG), `secrets/` | CR portals + crypto primitives. |

### 7. Apps (verified userspace)

| Piece | Location | Notes |
|---|---|---|
| **Gated app templates** | `metatheory/Dregg2/Apps/*Gated.lean` | every app runs on the credential-gated executor (template: `NameserviceGated.lean`). |
| **Spec layer (RDII loop)** | `metatheory/Dregg2/Protocol/WorkflowGuard.lean` | authorization/ordering/attestation gates as `Spec.Guard` instances. |
| **What "verified app" means** | [`docs/rebuild/APP-THEOREM-SUITE.md`](rebuild/APP-THEOREM-SUITE.md), `Dregg2/Apps/VERIFICATION-TOOLKIT-GUIDE.md` | |
| **Rust apps** | `starbridge-apps/*` (nameservice, identity, subscription, governed-namespace, privacy-voting, sealed-auction, …) | clients over the gated kernel. |

### 8. Program logic + DSL (making it useful to a developer)

| Piece | Location | Entry points |
|---|---|---|
| **WP / VCG calculus** | `metatheory/Dregg2/Proof/WP.lean`, `WPCatalog.lean` | `wp`/`Triple`/`vcg`; `vcg_run_sound` reduces to `stepComplete_preserves`. |
| **Cell-program eDSL** | `metatheory/Dregg2/DSL.lean`, `DSLEffect.lean`, `DSLChoreo.lean` | `dregg_program {…}` — a parser onto proved smart-constructors. |
| **Catalog metaprogramming** | `metatheory/Dregg2/Catalog.lean` | `#assert_namespace_axioms`, `catalog … where` codegen, the `discharge` tactic. |
| **Rust DSL** | `dregg-dsl{,-runtime,-tests,-differential}/` | ⟷ `Exec/CellProgram` with a differential. |

### 9. The SDK / CLI / clients / web

| Piece | Location | Notes |
|---|---|---|
| **SDK** | `sdk/src/` | `client.rs`, `full_turn_proof.rs`, `committed_turn.rs` (full-turn proof routed through the Lean producer). |
| **CLI / bots** | `cli/`, `discord-bot/`, `wasm/`, `app-framework/` | clients over the gated kernel. |
| **Web surfaces** | `site/`, `web/`, `extension/` | explorer / playground / studio (reviews: `docs/rebuild/REVIEW-*.md`). |

---

## The Rust crates, at a glance (dregg vs dreggrs)

Full classification + LOC: [`docs/rebuild/_SILVER-COVERAGE-LEDGER.md`](rebuild/_SILVER-COVERAGE-LEDGER.md)
and [`_DREGG-DREGGRS-MANIFEST.md`](rebuild/_DREGG-DREGGRS-MANIFEST.md).

- **dregg (Lean-truth / bridge / client):** `dregg-lean-ffi`, `node`, `sdk`, `intent`, `verifier`,
  `circuit`, `wire`, `cli`, `discord-bot`, `wasm`, `app-framework`, `demo*`, `starbridge-apps/*`,
  `preflight`, `dregg-dsl*`, and (in-flight) `turn`, `cell`.
- **dreggrs B.1 (verified Rust shadow, Lean model + differential):** `blocklace`, `coord`,
  `federation`, `macaroon`, `token`, `credentials`, `captp`, `discharge-gateway`, `commit`,
  `persist`, `dfa`, `bridge`, `storage`.
- **dreggrs B.2 (pure infra / crypto-primitive / tooling):** `hints`, `secrets`, `tokenizer`,
  `trace`, `audit`, `observability`, `types`, `rbg`, `dregg-storage-templates`, `directory`, `net`,
  `tests`, `protocol-tests`, `teasting`.

`chain/` and `chain/program/` are standalone workspaces (SP1 guest); excluded from the root
workspace (`Cargo.toml` `exclude`).

---

## Common "I'm looking for…" answers

| Looking for… | Go to |
|---|---|
| The single verified turn entry | `Dregg2/Exec/FullForestAuth.lean` → `execFullForestG`; FFI `@[export dregg_exec_full_forest_auth]` in `Exec/FFI.lean:3487`. |
| Whether the circuit really verifies effect X | [`docs/rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md`](rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md) — the per-effect class (A/B/C/D) ledger. |
| How finality works | `Dregg2/Distributed/BlocklaceFinality.lean` + [`guides/distributed.md`](guides/distributed.md). |
| The crypto trust assumptions | [`docs/rebuild/_CRYPTO-HYPOTHESIS-LEDGER.md`](rebuild/_CRYPTO-HYPOTHESIS-LEDGER.md), `Dregg2/CryptoKernel.lean`. |
| What's still open / not done | "What the `sorry`s mean" in [`README.md`](../README.md); `Dregg2/*/CircuitOpenFronts.lean`, `Exec/HandlerOpenFronts.lean`; [`docs/rebuild/_EXECUTOR-COMPLETENESS-GAPMAP.md`](rebuild/_EXECUTOR-COMPLETENESS-GAPMAP.md) (distance from `execFullForestG` to full execution) and [`docs/rebuild/_SWAP-COMPLETE-STATUS.md`](rebuild/_SWAP-COMPLETE-STATUS.md) (the Lean-producer boundary). |
| The honesty / axiom-clean artifact | `Dregg2/Claims.lean` (`lake env lean Dregg2/Claims.lean`). |
| Threat model / info-flow | [`docs/rebuild/_THREAT-MODEL.md`](rebuild/_THREAT-MODEL.md). |
| What a Rust crate is / does | [`docs/rebuild/_SILVER-COVERAGE-LEDGER.md`](rebuild/_SILVER-COVERAGE-LEDGER.md). |
