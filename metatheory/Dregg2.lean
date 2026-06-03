-- Dregg2: the dregg2 vat model — candidate-independent core + coinductive boundary.
--
-- Candidate-independent modules (shared across all dregg2 candidates):
--   * Dregg2.Core              — symmetric-monoidal cells/turns + Σ_k conservation
--   * Dregg2.Laws              — Predicate ⊣ Witness Galois connection + verify/find seam
--   * Dregg2.Authority.Positional — the l4v integrity lift / vat-boundary law template
--   * Dregg2.Confluence        — I-confluence / tier-1 eligibility (third judgement)
--
-- The Boundary/Soundness module is candidate-dependent: dregg2 uses the coinductive
-- (▶-guarded bisimulation) shape (see docs/rebuild/dregg2.md §1.3/§8).
import Dregg2.Tactics       -- shared proof automation
import Dregg2.Core
import Dregg2.Resource
import Dregg2.Resource.TokenAutonomy   -- idempotent resources (capability lattice / GSet) admit no sound retract into a cancellative foreign token: no_substitution_of_idempotent + gset_not_substitutable_by_int; cancellative payment does substitute (honest discriminator); #assert_axioms-clean, #eval non-vacuity
import Dregg2.Laws
import Dregg2.Authority.Positional
import Dregg2.Authority.Caveat   -- keys-as-caps token layer (biscuit/macaroon/caveat/discharge): attenuation chain + attenuate_narrows + token-as-Verify bridge + #eval
import Dregg2.Confluence
import Dregg2.Confluence.CRDT   -- CRDT instance catalog: G/PN-counter, G/OR-set, LWW register (each a MergeState + invariant), bounded-counter non-confluence + escrow/quota-partition refinement; #assert_axioms-clean
import Dregg2.Boundary
import Dregg2.StepCamera     -- step-indexed Iris camera (higher-order resources; shares Boundary's ▶)
import Dregg2.JointTurn      -- cross-cell ⊗ : equalizer + CG-2 pullback + CG-5 aggregate, binding-as-hypothesis
import Dregg2.Finality       -- judgement 2: the 4-tier finality lattice + cross-tier join
import Dregg2.Privacy        -- field / value (Pedersen) / graph (stealth+nullifier) privacy tiers
import Dregg2.Coordination   -- MPST global type G → projection → protocol-cell; deadlock-freedom
import Dregg2.Projection     -- cand-D choreography front-end: blue/red split + epp_correspondence (= boundary_law at two altitudes)
import Dregg2.Await          -- algebraic effects + one-shot continuations; turn-as-rollback-handler
import Dregg2.Liveness       -- GC-as-cell-liveness; lease-expiry; cross-vat cycle leak (impossibility)
import Dregg2.Upgrade        -- anti-brick set_program: AIR_VERSION pin + signature fallback
import Dregg2.Execution      -- userspace programs: configurations, runs, invariant-preservation
import Dregg2.CryptoKernel    -- §8 portal: crypto ops as an uninterpreted interface (Lean⟷Rust); verify/find seam instantiated; cross-vat bridge closed
import Dregg2.PrivacyKernel   -- privacy realized over the portal: committed_conservation + nullifier anti-double-spend via the interface laws
-- ─── The 3-layer CryptoKernel split (docs/rebuild/PHASE-CRYPTOKERNEL.md) ───
import Dregg2.Crypto.Primitives      -- layer A: CryptoPrimitives (Poseidon2, Pedersen commit+commit_hom, nullifier); collisionHard/binding/unlinkable as Prop carriers (not idealized hash_inj)
import Dregg2.Crypto.Merkle          -- §8 discharge #1: CircuitIR + merkleCircuit + merkle_bridge (Satisfies ↔ MerkleMembers, both directions; path-recomposition sound and complete, no primitive seam)
import Dregg2.Crypto.VerifierKernel  -- layer B: verify defined as circuit-satisfiable; merkle_verify_sound derived (accept ⇒ membership, given the STARK extractable carrier) — the §8 verify-law, derived not assumed
import Dregg2.Crypto.PredicateKernel -- layer C: per-kind KindObligation (statement+relation+Dial floor); merkle_registry_cascade (registry_sound ∘ verify_sound) + merkle_dial_wired (EpistemicDial pinned to the Merkle verifier at the acceptanceOnly ZK floor)
import Dregg2.Crypto.PortalFloor      -- 8 §8 @[extern] crypto-portal floor (post-cutover TCB): SignatureKernel(ed25519)/VerifierKernel(STARK)/PedersenKernel(DLog+commit_hom)/Poseidon2Kernel/Blake3Kernel/NullifierKernel/SealKernel(AEAD+X25519)/MacKernelE(HMAC); each = @[extern] oracle + soundness Prop carrier + *_floor_sound taking the carrier as an explicit hypothesis; Reference instances discharge carriers True only in toy ℤ/ℕ (non-vacuity); #assert_axioms-clean
import Dregg2.World           -- sibling portal: network/clock/randomness oracle for consensus; quorum finality derived + Byzantine/GST OPEN
import Dregg2.Exec.Value      -- Preserves data substrate (dregg2 §5): name-keyed records over a Schema; type-directed flatten with proved fixed width (circuit-over-records foundation)
import Dregg2.Exec.Program    -- RecordProgram structure-map over records (mirrors dregg1 cell/program.rs): StateConstraint catalog + Cases/TransitionGuard dispatch + default-deny; Heyting fragment + #eval
import Dregg2.Exec.Cell        -- the living coinductive cell: cexec as a Boundary.TurnCoalg; livingCell_sound = bisimulation-to-golden-oracle; checkpoint/replay as theorems
import Dregg2.Exec.CellReal    -- coinductive living cell over the real per-asset executor: livingCellA_sound = bisimilar to the per-asset conservation oracle forever; livingCellA_obs_invariant = no drift along the unbounded trajectory; livingCellA_supply_disclosed = mint/burn boundary is disclosed (no hidden leak)
import Dregg2.Exec.CellConfine   -- livingCellA_confinement: with a fixed authority ceiling U and initially-confined kernel, every held cap's authority stays ⊆ U forever — coinductive lift of Authority.Positional.confinement_preserved onto the real executor
import Dregg2.Exec.CellNullifier -- livingCellA_no_double_spend: any spent nullifier stays spent at every index forever (registry grow-only); a non-conservation safety on the spent-note set, dual to conservation's equality
import Dregg2.Exec.CellCommit    -- livingCellA_commitments_persist: published commitments persist at every index of the unbounded trajectory (grow-only registry); structural dual of the conservation frame
import Dregg2.Exec.Durability    -- write-ahead log over the real executor: wal_crash_recovery_sound (recover∘crash = live) + wal_torn_write_no_lost_commit + durTraj_recoverable (recovery succeeds along any unbounded turn stream)
import Dregg2.Exec.CellCarry    -- livingCellA_carries: any predicate `Good` preserved by one step holds along the entire unbounded trajectory; app authors supply a one-step proof and get "holds forever" free. Conservation is the trivial instance; livingCellA_logMono (log is append-only forever) is the demo instance. #assert_axioms-clean; #eval non-vacuity
import Dregg2.Exec.VatBoundary -- vat-boundary authority law on the living cell: intra-vat=authorizedB (Integrity.intra) / cross-vat=token discharges (Integrity.cross); unifies Cell+Caveat+Authority + #eval
import Dregg2.Exec.Kernel     -- executable kernel (Design-Spec layer): exec checks conservation+authority, fail-closed + #eval
import Dregg2.Exec.Generators -- mint/burn conservation generators (mint_delta/burn_delta)
import Dregg2.Exec.Caps        -- capability ops (grant/attenuate/derive/revoke/invoke) + integrity bridge
import Dregg2.Exec.Unified      -- unified KernelOp + step: conservation (step_delta) + ledger
import Dregg2.Exec.StepComplete -- step-completeness spine: cexec attests all 4 StepInv conjuncts; conservation_step realized; end-to-end soundness
import Dregg2.Exec.RecordKernel -- concrete cell: KernelState's bal:ℤ lifted to a content-addressed Value record; recKExec_conserves/recKExec_authorized/recCexec_attests proved over the named `balance` field (#assert_axioms-clean)
import Dregg2.Exec.FFI         -- @[export] scalar + record-cell entries → the Lean⟷Rust cascade beachhead (Rust hosts the compiled kernel; PoC round-trips)
import Dregg2.Exec.CodecRoundtrip -- parse∘encode roundtrip theorem (number/digest/string/lit/flag/enum/scalar-value/bal-entry); removes those codec primitives from the Lean-side TCB; #assert_axioms-clean
import Dregg2.Circuit          -- circuit-from-Lean: CCS IR + bridge (satisfied kernelCircuit ↔ fullStepInv); verify-law derived, not assumed
import Dregg2.Exec.CellProgram -- CellProgram DSL = executable coalgebra structure-map; denote_conserves
import Dregg2.Proof.Refine    -- Exec ⊑ Abstract: conservation + integrity-intra refinement, simulation diagram OPEN
-- Executable protocols (concrete, computable):
import Dregg2.Protocol.Transfer  -- two-cell atomic token transfer + payment-channel run; conservation/CG-5/atomicity proved + #eval
import Dregg2.Protocol.Workflow  -- authenticated, capability-gated, attested multi-party workflow; all guarantees proved + #eval
-- ─── Living-cell growth: additional safety and authority slices ───
import Dregg2.Authority.Discharge   -- discharge = the await authority-face: admits_mono_discharge (resolves forward, never un-resolves)
import Dregg2.Authority.CDT          -- capability-derivation-tree spine: path_attenuates (authority shrinks down any derivation chain) + CDT≡biscuit bridge to Caveat
import Dregg2.Authority.Intent       -- intent = the ∃-resolver / inverse-vat-boundary await face: intent_fill_verifies (soundness-by-verification vs adversarial matcher); FIND stays undecidable/OPEN
import Dregg2.Exec.MultiAsset        -- multi-asset conservation: maExec_conserves_per_asset (per-asset Σ_k) + camera-FPU bridge
import Dregg2.Exec.RecordCell        -- RecordProgram as the structure-map on a record cell: recExec_admitted (nothing commits the program rejects)
import Dregg2.Exec.JointCell         -- executable bilateral JointTurn: joint_cg5_conserves (cross-side conservation, no global ledger) + binding-as-hypothesis
import Dregg2.Exec.CrossCaveat       -- cross-cell state caveats as a further equalizer on the joint turn: crossCaveat_sound = CG-5 ∧ CG-2-equalizer (SharedBinding) ∧ φ; caveated_check_eq_use = no TOCTOU; crossCaveat_rejects + covenant_rejects_high (teeth); cost is the Agreement dial (free single-machine, blocking distributed)
import Dregg2.Exec.CellFinality      -- finality tier on the cell: commit_at_join (max) + I-confluence tier-1 eligibility gate (enforced, not prose)
import Dregg2.Exec.CellPrivacy       -- value-rib: committed_transfer_conserves (conservation over Pedersen commitments / hidden amounts)
import Dregg2.Exec.CellUpgrade       -- anti-brick upgrade turn: execUpgrade_never_bricks + stale→owner-signature fallback
import Dregg2.Exec.NullifierCell     -- nullifier set as an I-confluent tier-1-safe cell: spend_no_double_spend + balance≥0 NOT tier-1
import Dregg2.Exec.CellLiveness      -- GC = cell-liveness: death_is_timed_out (lease-expiry; death never decided) + cross-vat-cycle impossibility
-- ─── Storage-as-cell-programs + verification key layer ───
import Dregg2.Exec.Factory          -- FactoryDescriptor: constructor_transparency (a factory mints cells carrying exactly its contract)
import Dregg2.Authority.VerificationKey -- content-addressed circuit identity (mirrors dregg1's canonical_vk_v2): proof_binds_current_vk + proved_state + ChildVkStrategy; §8 collision-resistance kept as an oracle hypothesis
import Dregg2.Exec.CapInbox          -- CapInbox cell-program pattern: inbox_fifo (tail≤head, cursors monotone) + sender-auth via the token layer
import Dregg2.Exec.PubSubTopic       -- PubSubTopic cell-program pattern: pubsub_append_only (log grows, cursors only forward)
import Dregg2.Exec.BlindedQueue      -- BlindedQueue (commitments-in/nullifiers-out): blinded_no_double_spend + consume_needs_verify (§8 oracle)
import Dregg2.Exec.RelayOperator     -- RelayOperator (bonded relay): bond_floor_held + bond_decrease_needs_dispute + quota_enforced
-- ─── Predicate registry / algebraic effects / receipt chain / verifiable credentials ───
import Dregg2.Authority.Predicate     -- verify/find predicate registry: registry_sound + adversarial_find_cannot_forge (matcher untrusted, verifier TCB)
import Dregg2.Exec.Effect             -- algebraic effects as turns: conservation_of_effects + disclosed_non_conservation + exhaustive linearity
import Dregg2.Exec.Receipt            -- per-cell WitnessedReceipt chain: chain_tamper_evident (HInj/HFresh hyps) + cexec_appends_receipt
import Dregg2.Authority.Credential    -- verifiable credentials as keys-as-caps: credential_verifies_iff_issued_and_not_revoked + revoke_blocks_verify + revocation no-loss I-confluence; §8 attestation = oracle
import Dregg2.Exec.RecordCellLive     -- Value/RecordProgram cell as a real Boundary.TurnCoalg: recCexec_attests (4-conjunct step-completeness) + recReplay_preserves_sumEquals (conservation over name-keyed records) + stepComplete_preserves instance; #assert_axioms-clean
import Dregg2.Exec.CellRuntime        -- OS-level cell runtime theorems: checkpoint_restore_roundtrip + replay_deterministic_run + replayFrom_conserves + time_travel_fork (two admissible diverging suffixes from one snapshot) over both the ℤ-ledger and name-keyed record cell; #assert_axioms-clean; #eval non-vacuity
-- ─── Proof infrastructure: conservation library, tactics, consensus bridge ───
import Dregg2.Conserve                 -- shared conservation lemma library + `conserve`/`commit_cases` tactics (fail-loud, structural; #assert_axioms-clean)
import Dregg2.Catalog                  -- catalog code-gen (`catalog … where` → smart-ctor + admits-char + auto-#assert_axioms triple) + `discharge` guard-seam tactic + `Dregg2` aesop rule-set + `#assert_namespace_axioms` (all fail-loud; #assert_axioms-clean)
import Dregg2.Exec.Consensus          -- quorum→finality-tier bridge: committedByQuorum→bft tier, net_no_downgrade, finality_monotone_on_net; axiom-clean
-- ─── Atomic hyperedge: turn = wide pullback over shared TurnId ───
import Dregg2.Hyperedge               -- Hyperedge = wide pullback over TurnId + N-ary CG-5; hyperedge_sound proved; SharedTurnId/ring are special cases
-- ─── Abstract spec layer (Dregg2.Spec): the factored dregg2 semantics ───
import Dregg2.Spec.Guard              -- unified verify/find seam (demand⊣supply, first-party|witnessed, meet-semilattice attenuate_narrows, OneOf coproduct); legacy constraints/auths as derived instances
import Dregg2.Spec.Conservation       -- multi-domain LinearityClass-typed conservation: committed_iff_cleartext (hidden-yet-conserved) + multi_domain_independent; range-rib is §8 portal
import Dregg2.Spec.Authority          -- generative capability graph: introduce/amplify/mint + "only connectivity begets connectivity" (gen_step_traces proved); whole-history closure OPEN
import Dregg2.Spec.Lifecycle          -- lifecycle as the attested dual of creation: creation_and_death_are_dual + archival_is_fold(IVC) + reclaim_by_lease + creation_provable_death_temporal; co-witnessability OPEN
-- ─── Spec cross-links: choreography↔hyperedge, await, vat-boundary Φ ───
import Dregg2.Spec.JointViaHyper      -- N-ary joint soundness derived from hyperedge_sound; hyperedge_is_validity_not_canonicity (validity=proof-check, canonicity=consensus)
import Dregg2.Spec.Choreography       -- blue/red projection-split: red_projects_to_hyperedge, blue_needs_no_hyperedge; operational refinement OPEN
import Dregg2.Spec.Await              -- await family = temporal Guard (conditional_is_temporal_guard + resolve_monotone) ⊕ dataflow DAG (Promise); zkpromise/zkawait unification proved; topo-sort OPEN
import Dregg2.Spec.VatBoundary        -- Φ the named-lossy caps↔keys functor: phi_drops_confinement (permission survives, authority doesn't) + forwarded_cap_is_revocable + biscuit/macaroon=Φ-domain; functoriality OPEN
import Dregg2.Spec.Coherence          -- coherence web: guard_is_authority_conferral, conservation_is_hyperedge_cg5, lifecycle_revoke_is_authority_restrictive, choreography_red_conserves, guard_attenuate_narrows_is_meet ⇄ authority_confers_narrows_is_meet
import Dregg2.Spec.ExecRefinement     -- Exec ⊑ Spec beachhead: exec_refines_conservation (toy ℤ ledger = balance domain) + exec_authz_refines_guard (authorizedB = Guard.firstParty); operational LTS OPEN
-- ─── Program logic, §8 discharges, app Spec layer, operational LTS ───
import Dregg2.Proof.WP                 -- VCG/WP calculus over the Option-monad transition: wp/Triple + vcg + vcg_run_sound (reduces to stepComplete_preserves); monotonic-counter + single-ledger escrow proved; cross-vat escrow OPEN
import Dregg2.Exec.AuthTurn            -- authority-mutating turn (dual of the balance turn): recKDelegate/recKRevokeTarget edit `caps`; cap-edit matches Spec.addEdge/removeEdge (Endow/Revoke); dual frame with recTotal fixed
import Dregg2.Proof.LTS                -- single-cell operational LTS: recAbsStep_forward + authAbsStep_forward united in absStep'_forward; cross-cell whole-history closure residual OPEN
import Dregg2.Crypto.NonMembership     -- §8 discharge #3: nonmembership_bridge (Satisfies ↔ NonMember, both directions; sorted_gap_excludes the combinatorial heart, no seam) + nonmembership_verify_sound (derived) + dial at acceptanceOnly floor
-- ─── §8 discharges #4–5, BFT adversary model, cross-cell LTS, closed userspace-verification loop ───
import Dregg2.Crypto.Temporal          -- §8 discharge #4: temporal_bridge (Satisfies ↔ InWindow, both directions; no primitive seam) + temporal_verify_sound (derived) + dial at `selective`
import Dregg2.Crypto.Dfa               -- §8 discharge #5: dfa_bridge (Satisfies ↔ DfaAccepts, both directions; no seam) + dfa_verify_sound (derived) + dial at `fullDisclosure`; reference kernel OPEN
import Dregg2.Proof.BFT                -- Byzantine/honesty model over World: bft_safety (conflicting quorums ⇒ ⊥ via honest-witness intersection, n−f quorum) + GST liveness; all model assumptions are structure fields, #assert_axioms-clean
import Dregg2.Proof.CrossCellLTS       -- cross-cell operational LTS: crossAbsStep_forward (bilateral jointApply square: conservation + authority + grounding) + crossAbsRun_forward; machine-checked that cross-cell does NOT reduce to single-cell (tensor-non-finality); N-ary forest OPEN
import Dregg2.Proof.WPCatalog          -- userspace-verification loop closed end-to-end: vcg_discharge (fail-loud) + eDSL multi-field ledgerSM → vcg → vcg_discharge → vcg_run_sound (conservation + monotonic seq)
-- ─── BFT liveness pacemaker, cross-cell forest, contention dichotomy, §8 discharge #6 ───
import Dregg2.Proof.BFTLiveness        -- closes the GST liveness OPEN: GSTRound obtained from DLS88-GST + ELRS-synchronizer + HotStuff-responsive-quorum Pacemaker; World.gst_liveness derived; randomized synchronizer construction OPEN
import Dregg2.Proof.Synchronizer       -- randomized leader-rotation synchronizer: expected_views_O1 + honest_hit_as (a.s. hit); reduces Pacemaker.synchronizes to the randomness+honest-fraction model; World.rand probability-measure bridge OPEN
import Dregg2.Proof.CoinductiveAdversary -- unbounded-interleaving adversary: obsBisim_traj_of_bisim (confluence-up-to-bisimulation over νF) proved for the safe fragment; deriving it from the finite dichotomy needs up-to-context closure — OPEN
import Dregg2.Proof.BeaconSpace        -- probabilistic oracle layer: Measure over beacon streams + Bernoulli(h) independence; noHonestEverGe_measure_zero + honestLeader_index_exists discharge Synchronizer.hhit; Dirac h=1 boundary witness suffices (interior-h needs an unbuilt mathlib module)
-- ─── §8 kinds 7+8 (registry complete), catalog phase (ii), eDSL-B, dregg1 semantics mirrors ───
import Dregg2.Crypto.BlindedSet        -- §8 #7: blindedset_bridge (= merkle_bridge; a BlindedSet membership IS Merkle vs the issuer root) + HolderAnonymity carrier + dial acceptanceOnly (holder hidden)
import Dregg2.Crypto.Custom            -- §8 #8 (registry complete; extensibility OPEN): custom_bridge parametric over a CustomRegistration's own bridge field; any future kind registers (vk,circuit,relation,bridge) and inherits the cascade
import Dregg2.CatalogInstances         -- dregg1's StateConstraint(27)/Authorization(9) catalogs as derived Guard smart-constructors + Effect::linearity coloring; 101 thms #assert_namespace_axioms-clean
import Dregg2.DSLChoreo                -- `dregg_choreo {…}` choreography eDSL → Coordination.GlobalType; auction inherits deadlock_freedom + privacy_by_projection; #check_projectable elaboration gate
import Dregg2.Exec.CapTP               -- CapTP transport: pipelining_preserves_seam + handoff_is_introduce/_non_amplifying/_forwarder_revocable (3-vat Granovetter handoff = Spec.Authority.Introduce crossing Φ); distributed-GC liveness OPEN
import Dregg2.Authority.Blocklace      -- byzantine-repelling DAG (Cordial-Miners C-spine): equivocation_detectable + honest_no_equivocation + cdt_is_blocklace bridge + attested finality; eventual-exclusion-under-partition OPEN
import Dregg2.Exec.DfaRouting          -- DFA message-routing automaton (mirrors dregg1): routed_message_followed_accepting_route (delivery soundness, fail-closed) + route_authorization (per-hop Guard) + unique_route + routing_projects_message_flow
import Dregg2.Crypto.UCBridge          -- UC cross-system bridge: FComDischarge bundles CryptHOL's Pedersen F_com guarantees as Prop carriers; binding_unlinkable_discharged_by_crypthol proved (#assert_axioms-clean). CAVEATED: trust widens to Isabelle/HOL + transport fidelity; Isabelle theory in uc-crypthol/ (local build blocked by afp-devel↔RC3 skew, see PHASE-UC-TRANSPORT.md)
-- ─── Wire emission, distributed GC, full op-set, cross-cell forest ───
import Dregg2.Exec.CircuitEmit         -- circuit extraction emitter: emit (ConstraintSystem→wire) + emit_faithful + emittedKernel_bridge (emitted kernelCircuit ↔ fullStepInv); fingerprint-bound to the real Rust AIR via dregg-lean-ffi
import Dregg2.Exec.CapTPGC             -- CapTP distributed GC by lease: captp_gc_by_lease + captp_no_premature_reclaim + captp_cycle_leak_is_the_price (the impossibility, not faked)
import Dregg2.CatalogEffects           -- all 52 dregg1 Effect variants colored onto Spec.Conservation LinearityClass + per-class obligations + Regime discriminator; 69 thms #assert_namespace_axioms-clean
import Dregg2.Exec.TurnExecutor        -- turn-executor: Turn = call-forest of catalog-typed Actions run all-or-nothing; execTurn_attests = all 4 StepInv conjuncts over the whole multi-action turn + execTurn_conserves/_balance_domain/_unauthorized_fails
import Dregg2.Exec.TurnForest          -- nested call-forest executor: execForest_no_amplify (Granovetter via derive_no_amplify) + execForest_conserves (N-ary CG-5, Σ=0 whole tree) + execForest_attests (4 StepInv conjuncts); cross-cell forest OPEN
import Dregg2.Paco                      -- vendored+ported from hxrts/paco-lean (MIT): parametrized coinduction (paco/upaco/gpaco/gupaco + companion/up-to + the `pcofix` tactic), 23 modules; powers CoinductiveAdversary's up-to-context closure (obsBisim_of_uptoComm)
import Dregg2.Proof.ForestLTS          -- N-ary cross-cell forest LTS: forestAbsStep_forward (forestApply square, Finset.sum conservation, Σ=0 binding hypothesis-routed) + forestAbsRun_forward; bilateral = ι=Fin 2 slice
import Dregg2.Proof.ContendedCrossCell -- contention dichotomy (both poles): contended_commits_confluent (disjoint/I-confluent ⇒ schedule-agnostic) + coupled_no_schedule_agnostic_commit (coupled Σ=0 ⇒ ¬∃ schedule-agnostic commit — BEC/CAP impossibility); bridged to Confluence
import Dregg2.Crypto.Bridge            -- §8 discharge #6: bridge_bridge (Satisfies ↔ BridgeRelation, both directions; no seam) + bridge_verify_sound (derived) + dial at `selective`
import Dregg2.Crypto.Pedersen         -- §8 discharge #2: pedersen_conservation_bridge (Satisfies ↔ Conserves, both directions; commit_hom-grounded, range-gadget non-negativity, no seam) + pedersen_verify_sound (derived) + dial at `selective`
import Dregg2.Protocol.WorkflowGuard  -- Workflow's authz/order/attest gates as Spec.Guard instances; 3 refinement ↔s + whole-step Guard.all equivalence + exec⇒admits bridge + discriminating #eval
import Dregg2.DSL                      -- `dregg_program {…}` cell-program eDSL → RecordProgram; counter/escrow elaborate by rfl; #eval admit/reject
-- ─── Full op-set, eDSL-C, state migration, circuit gadgets to wire, Temporal/Stingray ───
import Dregg2.Exec.TurnExecutorFull    -- full op-set executor: FullAction = balance | delegate/revoke | mint/burn; execFull_attests = StepInv per kind + execFullTurn_ledger transaction-level conservation
import Dregg2.Exec.CrossCellForest     -- cross-cell nested forest: crossForest_no_amplify + crossForest_conserves (N-ary cross-cell Σ=0) + crossForest_attests; bilateral = Fin-2 slice; overlapping-cells OPEN
import Dregg2.Exec.FullForest          -- FullActionA call-forest (wholesale-swap keystone): execFullForestA = recursive all-or-nothing tree over the full per-asset op-set, proven equal to execFullTurnA over the pre-order lowering; execFullForestA_conserves_per_asset (conservation vector, not scalar) + execFullForestA_no_amplify + execFullForestA_each_attests; cross-target routed to CrossCellForest
import Dregg2.Exec.FullForestAuthPortal -- real §8 AuthPortal: RealAuthPortal bundles ed25519/STARK/HMAC floors; portalVerifyReal routes each Authorization variant to its own oracle; realAuthPortal.soundness = ed25519.unforgeable ∧ STARK.extractable ∧ HMAC.unforgeable (not True, not one shared collisionHard); per-variant security theorems take the carrier as an explicit hypothesis; unchecked_arm_rejects + no_reachable_arm_is_trivially_true (anti-vacuity); #assert_axioms-clean
import Dregg2.Exec.FullForestAuth      -- executed credential+caveat auth gate on the call-forest: gated tree FullForestG with NodeAuth (10-variant Authorization + tiered caveats + macaroon chain); gateOK = credentialValid (§8 AuthPortal) ∧ capAuthorityG (granted≤held verified) ∧ caveatsDischarged; execFullForestG_conserves_per_asset/_no_amplify derived via eraseG; gatedNode_check_eq_use = no TOCTOU; non-vacuous (forged cred, false caveat, and per-asset launder all yield none)
import Dregg2.Exec.SigningMessage      -- byte-exact signing-message preimages (guards the §8 AuthPortal's opaque `stmt` Digest), ported from dregg1 (authorize.rs:1713–1880): 6 preimage builders (sigMsgFull/Partial/Custom/Stealth/Bearer/HandoffCert) + domain-separator theorems (sigMsg*_hasPrefix, domainSep_injective — 15 pairs distinct) + binding teeth (tampered field ⇒ different preimage); #assert_axioms-clean, non-vacuous (#eval tamper ⇒ false)
import Dregg2.Exec.Admission           -- fail-closed admission prologue in front of the FullForestAuth kernel fold (admission ≠ kernel): `admissible` = 8 host-fed gates (expiry + agent-existence + nonce-replay + fee-coverage + write-set/agent freeze + receipt-chain self-binding + Stingray budget); `commitPrologue` (fee-debit + nonce-tick) is never rolled back — prologue_survives_failed_body proves fee−balance ∧ nonce+1 even on body failure (anti-DoS + replay-closed); pure_fold_loses_prologue proves the naive all-or-nothing bind discards the prologue; #assert_axioms-clean; #eval non-vacuity
import Dregg2.Apps.OrbitalScreen       -- continuous-time-sound orbital screen: screen_clear_imp_continuous_clear (a `clear` verdict holds at every continuous time, not just samples; between-samples closest approach covered) + crossing-pair teeth; coarse Lipschitz fallback for speed-bounded trajectories; curvature term OPEN
import Dregg2.Apps.WhoYields           -- graph-symmetry who-yields bridge (computable WL color-refinement): rigid_of_discrete (asymmetric ⇒ forced role) + symmetric_needs_negotiation (tie ⇒ negotiation) + three_mutual_conflict_needs_three_roles + outOfFuel_breaks_symmetry
import Dregg2.Apps.EpistemicSheaf      -- constellation as a sheaf of verifiers: consensus_on_clearance (H⁰ = global section = honest distributed knowledge of a screened fact) + byzantine_section_does_not_glue (witnessed non-gluing obstruction); cohomology-as-object is POETRY (honest)
import Dregg2.Apps.ConservationBridge  -- conservation_is_flow_balance: JointCell Σδ=0 (committed avoidance maneuver) = conjunction graph's flow-balance across the symmetry boundary; multi-edge generalization OPEN
import Dregg2.Apps.RightOfWay          -- verified collision-avoidance referee: referee_sound (adversary-proof) + referee_sound_physics (committed ⇒ clear on the whole continuous step, via OrbitalScreen) + outOfFuel_cannot_burn + forced_trade_excludes_naive + collisionSafety_must_escalate
import Dregg2.Apps.AgentOrchestration
-- NOTE: Dregg2.Apps.AgentOrchestration is intentionally not imported — the file has unresolved
-- sorryAx and a decide/type-mismatch in its auth-gate theorems. Isolated pending a proper repair;
-- the Rust counterpart (demo-agent/examples/orchestration_demo.rs) is green.
import Dregg2.Apps.NameService         -- nameservice cell-programs (register/transfer/revoke): nameservice_registration_forever carried via livingCellA_commitments_persist; nameCommit_inj + revoke tombstone; transfer preserves both old registration and new ownership binding forever
import Dregg2.Apps.Identity            -- identity cell-programs (present/verify/revoke): livingCellA_identity_revoked_forever = a revoked identity can never be re-validated, carried via livingCellA_carries on the grow-only `revoked` registry
import Dregg2.Apps.Subscription        -- subscription cell-programs: §A slot automaton safety (seq_tail ≤ seq_head, no-overflow) + subscription_consumer_safe_forever; §B subscription_wellformed_forever carried by the real execFullForestA living cell against any adversary
import Dregg2.Exec.CellRuntime         -- OS-level cell runtime theorems: checkpoint_restore_roundtrip + replay_deterministic_run + replayFrom_conserves + time_travel_fork; νF fork noted
import Dregg2.Exec.StateMigration      -- schema-upgrade state migration: migrate_conforms + migrate_conserves (balance survives) + migrate_anti_brick (gate-fail ⇒ signature fallback, never bricks)
import Dregg2.Exec.CircuitEmitGadgets  -- emits the remaining §8 gadgets to the wire: emittedTemporal/NonMembership/Pedersen/Dfa_bridge (each composes emit-faithfulness with the gadget's *_bridge)
import Dregg2.DSLEffect                -- `dregg_effect <name> : <Class>` effects eDSL → Spec.Conservation LinearityClass coloring + inherited obligation; #assert_namespace_axioms-clean
import Dregg2.Exec.Gas                  -- gas-metering layered beside execFullTurn: gasCost_pos (no free action) + gas_exhaustion_fails_closed (over-budget ⇒ none, no partial mutation) + gas_sufficient_runs (pure guard, identical state) + gas_conserves/_preserves_attests (removes no safety); Nat-resource orthogonal to ℤ-conservation
import Dregg2.Proof.BeaconSpaceInterior -- interior-h non-vacuity witness: Measure.infinitePi (Bernoulli 3/4)^ℕ at h=3/4, indep_block via infinitePi_pi; BeaconSpace is non-vacuously instantiable at a genuine interior honest-fraction
import Dregg2.Exec.ProofForest         -- proof-carrying forest composition: per-node StepProofValid × Linked ⇒ whole-run StepInv via execForest_attests; aggregation deferred
import Dregg2.Exec.TriDomain            -- tri-domain conservation (balance + authority + metadata): triConserved_of_execFull; the three domains that dregg1's atomic.rs enforces conserve independently
import Dregg2.Exec.AuthModes           -- 6 authorization modes (OneOf/Custom/CapTpDelivered/Bearer/Token/Unchecked) with witness dispatch + soundness; captp_granted_le_held proves non-amplification
import Dregg2.Exec.EffectTransfer      -- Transfer effect vertical-slice reference template: conserves → authorized → metadata → forward-sim (AbsStep); the pattern remaining effects instantiate
import Dregg2.Spike.TransferAirSoundness -- real air.rs:473 Transfer constraint over BabyBear: field-constraint+range ⇒ ℤ balance update + transfer_underflow_attack (off-circuit wrap gap, now closed in-circuit by the RANGECHECK lane)
import Dregg2.Exec.EffectsPaired       -- Conservative/Paired effects (escrow/notes/obligations/queues/bridge-Σ=0) via the EffectTransfer template; generic pairedStep spine
import Dregg2.Exec.EffectsSupply       -- Generative/disclosed-supply effects (CreateCell/Factory/Spawn/BridgeMint/Lock/Cancel/Finalize); foreign-finality §8-portal
import Dregg2.Exec.EffectsAuthority    -- authority-edit effects (Introduce/Attenuate/Exercise/ValidateHandoff/Refresh/Drop/SetPermissions/RevokeDelegation), each with non-amplification
import Dregg2.Exec.EffectsState        -- Neutral/Monotonic/Terminal field+lifecycle effects (setField/seal/sovereign/emit/refusal/archive/destroy/refs…) via the generic field-write + non-interference
import Dregg2.Spec.ExecRefinementFull  -- general forward-sim refinement: exec_full_refines_spec (every execFull step is a permitted abstract step) + full operational square; whole-history closure OPEN
import Dregg2.Exec.ConditionalTurn     -- executable conditional/await turns: execConditionalTurn (topo-sort + EventualRef slots) + condTurn_conserves/_atomic/_dependency_sound/_forward_sim; EventualRef read ↔ Await.Op.await
import Dregg2.Spike.EffectVmConstraints -- real EffectVmAir constraints in Lean: selector exactly-one, NoOp identity, transfer hi/dir, balance-lo range soundness, nonce tick; underflow_now_impossible proves the RANGECHECK closes the wrap gap
import Dregg2.Proof.CordialMiners       -- Cordial-Miners DAG-BFT model (dregg1's actual consensus): cordial_agreement (no two conflicting committed leaders) + cordial_agreement_from_lace (SuperRatification derived); liveness/GST/dissemination/Stingray OPENs
import Dregg2.Spike.EffectVmConstraints2 -- more EffectVmAir constraints: SetField per-field gating + balance_hi range-soundness + state_commitment binding-shape (hash as §8 portal); setfield_aux_honesty_gap (SetField intended-value rests on an off-circuit free aux column — a known gap, as a theorem)
import Dregg2.Proof.Stingray            -- concurrent-spend budget slice: sliceCeiling = balance·(f+1)/(2f+1); stingray_no_concurrent_overspend + stingray_schedules_disagree (concrete two-schedule counterexample) + inbudget_both_commit_schedule_agnostic (in-budget = coordination-free); f=0 ⇒ ceiling=balance degenerate case
import Dregg2.Proof.Temporal            -- temporal logic over the living cell: □/◇/◯ on execFullForestA trajectories + proof algebra + always_of_reachable_invariant bridge; always_conserved + always_logMono + always_revoked_persists + always_conj_safety (□(conservation ∧ log-append-only ∧ revoked-persist))
import Dregg2.Authority.CaveatChain      -- real macaroon HMAC append-only chain: verify_iff_wellTagged + append_narrows + integrity_tail_binds + forgery_requires_mac_query (forge ⇒ break-HMAC) + removal_breaks_tail; HMAC = §8 MacKernel portal
import Dregg2.Authority.ThirdPartyDischarge -- real third-party discharge protocol: accepts_iff (ticket/VID key-recovery ∧ bind-to-parent ∧ freshness ∧ predicate) + honest_discharge_accepted + rejection teeth; AEAD = §8 portal
import Dregg2.Authority.SelectiveDisclosure -- hidden-attribute predicate proofs (Gte/Lte/InRange) + selective reveal + anonymous unlinkable multi-show wired to credentials; ZK soundness = §8 portal
import Dregg2.Authority.DesignatedVerifier -- verifier-indexed DischargedFor + transferability dial (public = ∀V ⇒ non-repudiable; designated = V₀-only ⇒ deniable via the simulator property); DV-ZK = §8 portal
import Dregg2.Consistency               -- global soundness witness: dregg_consistent_nonempty = a single axiom-clean SystemModel instantiating all 11 Prop-carriers jointly; no carrier-pair derives False; not vacuous, not contradictory at the system level
import Dregg2.HandlerTransformer        -- higher-order handler-transformer: SafeStep preorder + instSafeStepFpu (camera Fpu = safe-composition instance) + safe_transformer_composes + conservation_is_safe_transformer + overshare_rejected (unsafe transformer is genuinely refused); unifies 'safe handler-transformer' with 'frame-preserving update' (Iris handler frame-rule); Fpu=gluing weld + comodel-morphism/sheaf-of-handlers tier are OPENs
import Dregg2.Confluence.DriftStable     -- drift-stable bridge: IConfluentUnder (conditional drift-stability = confluence in the sublattice E cuts out) + driftStable_composes (an I-confluent caveat survives forward drift, no re-check) + locked_driftStable (single-writer collapses merge ⇒ any φ drift-stable) + teeth (monotone composes free; bounded_caveat_needs_coordination) + TieredCaveat (carry the tier-proof, dispatch on DriftTier); #assert_axioms-clean, #eval non-vacuity
