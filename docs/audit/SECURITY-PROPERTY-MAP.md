# Security-Property Map — what dregg PROVES *about* its constructs (vs REFINEMENT vs ASSUMED)

Answering ember's question precisely: *"do we have Lean proofs about these constructs that they're
actually SAFE and UC/secure?"* — as distinct from the refinement/soundness proofs (there are tons of
those, and they are NOT the question).

This is a read-only survey. Every claim is grounded at `file:line` against HEAD. All paths are under
`metatheory/`.

## The three-way distinction used throughout

- **SECURITY-PROPERTY** — the construct has property P *as a property*: a bad state is unreachable /
  an invariant is preserved / authority cannot amplify / a value cannot be forged or diluted /
  something is unwinnable. Universally quantified over transitions (or the full state/witness space).
- **REFINEMENT** — "circuit/executor satisfaction ⟹ the kernel took this exact step" (the
  `descriptorRefines` / `*_is_memory_program` / `deco_verify_sound` / gate-forcing family). Soundness
  of a *mechanism*, not a property *of* the modelled world. This is the bulk of the corpus and is
  NOT what ember is asking about. A **GATE-REJECTION** ("this specific bad witness fails the gate") is
  a refinement-flavored sub-case, listed as such.
- **ASSUMED-FLOOR** — a `Prop`-class assumption or hardness carrier (Poseidon2-CR, FRI/STARK,
  ed25519 EUF-CMA, HMAC, AEAD, DLog, PostGSTProgress). Entered as a typeclass field / hypothesis,
  never an `axiom`. Correctly named as the trust boundary.

The one-line answer: **dregg has GENUINE security-property proofs for authority non-amplification,
value conservation, freshness/anti-replay, and several capacity invariants (vault no-dilution,
membrane non-amplification, lease budget-conservation, hatchery invariant-forever, obligation cursor
monotonicity). Its "UC" layer is almost entirely an abstract, un-wired theory shelf — the one
exception is settlement soundness. And every capacity's circuit-side / light-client witness is
STAGED, not in the deployed VK: the safety properties hold over pure math / the kernel / the
executor / an off-AIR gate predicate, not yet over the emitted AIR a pure light client checks.**

---

## 1. The system apex — `Dregg2/AssuranceCase.lean`

The five guarantees, and whether each is a security-property or a refinement re-pin.

| Guarantee | Theorem (file:line) | Class | What it actually states / rests on |
|---|---|---|---|
| **A — Authority** | `authority_guarantee` (`AssuranceCase.lean:166`) | **SECURITY-PROPERTY** | `IsNonAmplifying held (attenuate keep held) ∧ ¬ IsNonAmplifying held granted`. `IsNonAmplifying` is the genuine subset `capAuthConferred granted ⊆ capAuthConferred held` (`Exec/EffectsAuthority.lean:197`); the conjunct's second half is the *teeth* — an amplifying grant is rejected. Non-amplification proven AND shown discriminating. Floor: ed25519/HMAC for the WHO-leg credential (assumed). |
| **B — Conservation** | `conservation_guarantee` (`AssuranceCase.lean:259`) | **SECURITY-PROPERTY** (reachability invariant) | `∀ a, recTotalAsset s.kernel a = 0` on every `Reachable s`. Delegates to `ReachableConservation.reachable_total_zero` (`Exec/ReachableConservation.lean:49`): a nonzero-sum state is *unreachable* from a value-empty genesis. Not "invariant across a step" — identically zero, no zero-net side condition. Floor: NONE beyond integer arithmetic. |
| **C — Integrity** | `integrity_guarantee` (`AssuranceCase.lean:412`) | **REFINEMENT / BINDING** | `uproj C s' = (moveTrace C s t).foldl step (uproj C s)` — the executor's total post-state projection equals the fold of the verb's emitted Blum trace. "A receipt binds the whole post-state" is a *faithfulness* (memory-program) refinement, not a property of the world. Strengthened to the whole turn (`integrity_guarantee_whole_turn_covered`, `:486`). Floor: Poseidon2-CR. |
| **D — Freshness** | `freshness_guarantee` (`AssuranceCase.lean:581`) | **SECURITY-PROPERTY** (anti-replay) | `nf ∉ k.nullifiers ∧ nf ∈ k'.nullifiers ∧ interp (noteSpendStmt nf) k' = none`: a committed spend was fresh, is now spent, and a replay of the same nullifier fails closed. Double-spend impossible at the term level. Floor: Poseidon2-CR (nullifier-set openings); PostGSTProgress for revocation-at-finality. |
| **E — Unfoolability** | `unfoolability_guarantee` (`AssuranceCase.lean:666`) | **REFINEMENT + derived SECURITY** | `AggregateAttests … ∧ recTotal (lastStateOf …) = recTotal g` from `verify agg.root = true` alone. The first conjunct is a soundness refinement of the aggregate (accept ⟹ the whole history executed/ordered correctly); the second (`conserves_from_verification`) is conservation-over-history *derived from verification* (a security property lifted with no `StateChained` hypothesis). Floor: FRI/STARK soundness, Poseidon2-CR, ed25519, PostGSTProgress. |

**The composed theorem — `deployed_system_secure` (`AssuranceCase.lean:886`).** This is a GENUINE
composed theorem, not a side-by-side pile: its conclusion is the conjunction A ∧ B ∧ C(c1) ∧ C(c2) ∧
D ∧ E, with A/B/C over the SAME committed forest `execFullForestG s f = some s'` (the body behind the
`dregg_exec_full_forest_auth` FFI the node invokes), D over a committed noteSpend, E over a published
aggregate the light client verifies. It mixes **security-properties** (A = `execFullForestG_no_amplify`,
B = `execFullForestG_conserves_exact`, D = the noteSpend triple, E's conservation-from-verification)
with **refinement/binding** legs (C-c1 per-node `gatedActionInvG` attestation, C-c2 the whole-turn
memory program, E's `AggregateAttests`). It is conditional on the §8 floor (entering as hypotheses,
never `axiom`) plus the named per-step coverage seam `hcov` (dischargeable on the covered verb arms).
So: **not a conjunction of pure refinements** — three of the five legs are genuine safety properties —
but it is not a monolithic "UC-secure" statement either; it is "these five guarantees hold at once
over one deployed turn, modulo the crypto floor."

**Named boundary seams (`AssuranceCase.lean:946+`)** — the prover partition (non-graduated turn shapes
fall back to test-attested hand-AIR), the `ShadowHostCtx` host-fed admission inputs (now discharged to
`admissible_sound_of_reflects`), and producer coverage. These are the deployment boundary, not Lean
hypotheses; the case names them honestly.

---

## 2. The keystone audits — `Dregg2/Verify/KeystoneAudit*.lean`

Structural fact: every `KeystoneAudit*` file is an **audit harness** — it re-pins an already-proven
keystone from its home module via `@[load_bearing_keystone] def NAME_KS := @home.keystone`, attaches a
`*_satisfiable` (non-vacuity) and `*_teeth` (discrimination) witness, and runs a CI gate. The file's
*own* new content is the witnesses; the load-bearing *statement* lives in the aliased keystone. So the
class below is of what the re-pinned keystone establishes. **No file is a pure assumed-floor** — where
a CR/extractability floor appears it is either *consumed* by the keystone or *realized* in-file by the
proven-injective `encodeSponge` carrier.

| Audit file | Apex keystone (file:line) | Class |
|---|---|---|
| KeystoneAuditNonAmp | `attenuate_non_amplifying_KS` (`:60`) | **SECURITY-PROPERTY** (non-amplification, every cap-conferring mouth) |
| KeystoneAuditAuthModes | `captp_granted_le_held_KS` (`:90`) | **SECURITY-PROPERTY** (the CapTP dispatcher performs `granted ≤ held`, teeth two-valued) |
| KeystoneAuditConservation | `reachable_total_zero_KS` (`:276`) | **SECURITY-PROPERTY** (imbalance unreachable; teeth = legacy mint/burn break `ExactConservation`) |
| KeystoneAuditFreshness | `noteSpendStmt_no_double_spend_KS` (`:56`) | **SECURITY-PROPERTY** (anti-replay; replay refused) |
| KeystoneAuditIntegrity | `stateCommit_binds_cellCommit_KS` (`:79`) | **SECURITY-PROPERTY** (commitment binding) + 3 REFINEMENT verbs (`*_is_memory_program`, `:95/:102/:109`) |
| KeystoneAuditSupply | `mintA_authorized_KS` (`:119`) | **SECURITY-PROPERTY** (supply authorization) + 1 REFINEMENT (`execMintA_iff_spec`, `:124`) |
| KeystoneAuditUnfoolability | `verified_history_conserves_KS` (`:100`) | **SECURITY-PROPERTY** (unfoolability; tampered aggregate cannot bind) + the UC reduction `unfoolable_of_floor` (`:124`) |
| KeystoneAuditSystemRoots | `runnable_binds_same_system_roots_KS` (`:138`) | **SECURITY-PROPERTY** (side-table root binding); CR floor realized in-file |
| KeystoneAuditTransport | `recKDelegateAtten_non_amplifying_KS` (`:143`) | mixed: **SECURITY-PROPERTY** + REFINEMENT (`moveAsset_is_memory_program`, `:180`) |
| KeystoneAuditTerminalAdapters | `cap_leaf_value_codec_KS` (`:108`) | **SECURITY-PROPERTY** (cap-leaf tuple binding) + REFINEMENT canonicity (`:113`); CR floor realized |
| KeystoneAuditArgusReceipt | `argus_circuit_executor_receipts_agree_KS` (`:266`) | **SECURITY-PROPERTY** (receipt integrity / cross-corner agreement); CR floors realized |
| KeystoneAuditRunnable | `execFullForestG_unauthorized_fails_KS` (`:376`) | mixed: **SECURITY-PROPERTY** (fail-closed, non-amp, conservation, attestation) + REFINEMENT (forest = memory program, `:333`) |

Takeaway: the audit layer re-certifies genuine security-properties for A/B/D/E and the binding
backbone; the only REFINEMENT entries are the `*_is_memory_program` verbs, `execMintA_iff_spec`, and
the MMR index-canonicity adapter — none of the twelve files is exclusively refinement-shaped.

---

## 3. The UC / crypto layer — `Metatheory/*` (+ `Metatheory/Open/PerfectUC.lean`)

The crux question: are these real UC-security proofs applied to a dregg construct, or an abstract
theory shelf? **Answer: almost entirely an abstract, un-wired shelf. Exactly one file
(SettlementSoundness) is genuinely wired to a deployed construct.**

| File | Apex (file:line) | Class | Wired to a dregg construct? |
|---|---|---|---|
| **SettlementSoundness** | `settlement_soundness` (`:153`); `revoke_before_tip_unsettleable` (`:192`) | **SECURITY-PROPERTY** | **YES** — the KeyLeak capability/revocation model (`is_attenuation` mirror) + a restatement of the deployed circuit gate `Dregg2.Circuit.SettlementSoundness.honorsAtSettlement`. Instantiated non-tautologically on `deployedSettle` (`:289`); the tautological `liveSettlement_binds` is flagged as such (`:220`). Residual (Rust wire-conformance) named honestly (`:553`). |
| PerfectUC (`Open/`) | `perfectUC_composition` (`:200`) | **SECURITY (fragment)** | Perfect/statistical UC composition `π ⊑ F → ρ^π ⊑ ρ^F`, with `⊑` = equality of the environment's view (the perfect collapse of `≈`). WIRED to the **selective-disclosure functionality** `Dregg2.Privacy.project` (`realπ_realizes_idealF`, `:448`) — a real dregg tier-1 privacy primitive. **NOT** wired to DECO or the kernel. The COMPUTATIONAL UC theorem (PPT, negligible advantage) is explicitly OPEN (module header + `:502`). |
| SafetyGame | `kernel_invariant` (`:68`), `kernel_maximal` (`:77`) | **SECURITY** (viability-kernel / unwinnable safety game) | Abstract `Game`; edge-wired to the **Polis governor**, not the crypto kernel. |
| ReachGame | `attr_least` (`:89`), `reachWithin_sound` (`:140`) | ABSTRACT game-theory (liveness/reachability) | Abstract `Game`; edge-wired to the **Polis sandbox gate game**. |
| EnergyGame | `energy_safe` (`:156`) | **SECURITY** (budget-safety) | Abstract `CostGame`; wired to the **PolisGrade** quantale. |
| ConstructiveKnowledge | `verifier_learns_only_acceptance` (`:212`), `no_forge_step` (`:316`), `find_realizes` (`:108`) | ABSTRACT metatheory | Self-described **candidate-independent**; reuses Dregg2 *seams* as a library, proves over abstract `Preorder R` rights — not a deployed authority object. Knowledge-soundness (`find_realizes`) is conditional on an explicit search-contract hypothesis. |
| EpistemicDial | `real_priv_is_dial_bot` (`:471`), `accepts_invariant_under_dial` (`:199`) | REFINEMENT / abstract order theory | Thin bridge embedding the real `Dregg2.Privacy.Visibility` enum into an abstract `Dial`; substance is abstract. |
| EpistemicConsensus | `honest_dist_knowledge_iff_holds` (`:175`) | ABSTRACT epistemic logic | Sibling lib, NOT in the Dregg2 root; abstract `Frame`. |
| Disputation | `byzantine_majority_cannot_uphold` (`:79`) | ABSTRACT adjudication | Abstract (built on EpistemicConsensus frames). Records the "adjunction thesis" was refuted 4/4 and is NOT formalized. |
| CommonSecret | `threshold_jump` (`:221`) | ABSTRACT threshold crypto | Abstract `ThresholdFrame`; Shamir K-of-N epistemic cliff. Not wired. |
| ResharingChain | `reshareChain_forward_secret` (`:108`) | ABSTRACT forward-secrecy | Abstract `ReshareLink`/`Chain`; names `Apps.PreRotation` only as a dual/analogy. |

**On PerfectUC specifically (ember's UC question):** `perfectUC_composition` is a real composition
theorem, but ONLY for the *perfect/statistical* case (`≈` collapsed to `=`), only for *deterministic*
ideal functionalities, and it is wired to the **disclosure** functionality — NOT to DECO, not to
settlement, not to the kernel. It has genuine teeth (the context provably reshapes information;
`⊑` both holds and fails; the composition hypothesis is load-bearing). But it is a *fragment*: the
computational UC theorem (PPT environments, probabilistic ensembles, a simulator with negligible
advantage) is left explicitly OPEN. So "we have a UC-security proof" is true only in this narrow,
honestly-scoped sense, and it does not cover the payment/attestation constructs.

---

## 4. The new constructs (the real gap-hunt)

### DECO / zkTLS fiat money-in — `Dregg2/Crypto/Deco.lean`

| Theorem (file:line) | Class | What it is |
|---|---|---|
| `deco_authenticates_payment` (`:315`) | **REFINEMENT / soundness** (unforgeability ASSUMED) | `verify stmt proof = true → ∃ w, SK.Signed … ∧ MK.Tagged … ∧ opening ∧ 1 ≤ amountCents`. "An accepting proof proves a genuine Stripe-authenticated payment." This is *accept ⟹ the DECO relation holds and lifts to the §8 facts* — a soundness refinement. |
| `deco_bridge` (`:191`), `deco_verify_sound` (`:296`) | REFINEMENT | `Satisfies ↔ DecoRelation`; accept ⟹ ∃ satisfying trace. The bridge is fully proved (range gadget); the four chain gates are threaded. |
| `deco_binds_payment` (`:228`), `deco_commitment_binds` (`:249`) | ASSUMED-FLOOR lift | Lifts the runnable gates to `Signed`/`Tagged`/unique-opening **given** ed25519 EUF-CMA + HMAC + Poseidon2-CR carriers. |

**Answer to "is the payment unforgeable proven as a property?"** No — the unforgeability is
**ASSUMED**, carried by ed25519 EUF-CMA (`SK.unforgeable`) and HMAC (`MK.unforgeable`) entering as
hypotheses, plus the external Web-PKI/Stripe floor (`serverKey`-is-Stripe, `encode`-is-the-schema).
`deco_authenticates_payment` is a *binding refinement* on top of that floor (accept ⟹ the payment
facts genuinely hold), not a proof that the payment *cannot be forged*. And **PerfectUC is not wired
to DECO** — there is no UC/simulator argument for the payment attestation. So DECO = refinement +
named crypto floor, no security-property/UC proof of its own.

### Capacities (escrow / obligation / vault, tags 17/18/19)

**Critical cross-cutting fact:** the capacity `*Gate` predicates (`SettleGate`, `DischargeGate`,
`VaultDepositGate`) are Lean `abbrev … : Prop` modelling an **off-AIR manifest re-evaluation** over
committed `before/after` heap views — every docstring states "the AIR constraint polynomials — the VK
bytes — UNCHANGED." The in-AIR weld that would let a **pure light client** witness these
(`Deos/CapacitySatisfaction.lean`) is built **STAGED** (`circuit/src/effect_vm/satisfaction_weld.rs`)
and **NOT emitted into a committed VK, NOT flipped onto the live path** (`CapacitySatisfaction.lean`
docstring §"What is and is NOT witnessed yet", `:46-54`). So the capacity safety facts hold over pure
math / the executor / an off-AIR gate predicate — *not yet* over the deployed AIR.

| Construct | Genuine SECURITY-PROPERTY? | Headline (file:line) | Proven over |
|---|---|---|---|
| **Vault** (`Deos/Vault.lean`) | **YES — economic** | `deposit_no_dilution` (`:175`): `T * sharesOut T S d ≤ S * d`; `deposit_price_non_decreasing` (`:187`): `T*(S+sharesOut) ≤ S*(T+d)` — price-per-share never decreases, ∀ deposits; `withdraw_no_dilution` (`:196`) | **pure share-math** (the property). ERC-4626 inflation-attack immunity is REAL, as a property. |
| Vault — gate face | GATE-REJECTION | `inflation_attack_rejected` (`:369`), `dilution_rejected` (`:378`), `assets_not_conserved_rejected` (`:387`) | off-AIR `VaultDepositGate` predicate |
| Vault — light-client | REFINEMENT / binding, **STAGED** | `vault_satisfaction_witnessed` (`CapacitySatisfaction.lean:406`), `vault_gate_root_bound` (`Vault.lean:401`) | committed state-commit; NOT in deployed VK |
| **SealedEscrow** (`Deos/SealedEscrow.lean`) | **YES — economic no-theft (reachability)** + one-shot + binding | `sealedescrow_no_theft` (`:753`, reachability invariant: per-leg `paid+locked=entered` ∧ never-funded party receives nothing), `escrow_solvent` (`:769`, payouts ≤ deposits); teeth `honest_swap_reachable`/`halfopen_theft_unreachable`/`phantom_extraction_unreachable`; plus `replay_rejected` (`:257`), `settle_gate_forces_atomic` (`:361`), `partial_settle_rejected` (`:372`), `phantom_settle_rejected` (`:383`); root-binding `leg_status_bound_in_root` (`:303`), `settle_gate_root_bound` (`:397`) | reachability over deployed ops (deposit/settle/reclaim); executor `settle` + off-AIR `SettleGate` + committed root |
| **StandingObligation** (`Deos/StandingObligation.lean`) | **YES — monotonicity** | `cursor_strict_mono` (`:208`): `j < k → cursorAt t j < cursorAt t k`; teeth `replay_rejected` (`:277`), `early_discharge_rejected` (`:286`), `over_discharge_rejected` (`:294`) | pure arithmetic (property); `DischargeOk`/`DischargeGate` (teeth) |
| **Membrane** (`Deos/Membrane.lean`) | **YES — purest, over the KERNEL** | `reshareN_attenuates` (`:122`): any reshare chain confers `⊆` the original authority; `reshare_refuses_amplification` (`:145`); `membrane_non_amplifies` (`:223`) | **the kernel `Exec.attenuate` / `capAuthConferred`** — no gate, no circuit |
| **PrepaidLease** (`Deos/PrepaidLease.lean`) | **YES — economic conservation** | `budget_never_overdrawn` (`:378`); `remaining_plus_drawn_conserved` (`:396`): `remaining + drawn = budget` (Σδ=0); `cursor_strict_mono` (`:236`) | pure budget model (property); off-AIR `DischargeGate` (teeth) |
| **Hatchery** (`Deos/Hatchery.lean`) | **YES — temporal, over the EXECUTOR** | `invariant_forever` (`:233`): under every admitted-turn schedule the declared invariant holds at every index; `attested_enforces_forever` (`:291`) gated on a non-forgeable attestation | **the executor `evalStep` transition** |
| **DerivedCell** (`Deos/DerivedCell.lean`) | No — forge-detector + binding only | `forged_value_rejected` (`:184`, refinement `claim = fold sources`); `claim_bound_in_root` (`:235`) | `Verifies` predicate + committed root |

### Gentian carrier-floor (a declared capacity is always caught) — `Deos/{CapacityCarrier, CarrierBoundFloorGadget, BareCohortFloorRefuse, BareCohortFloorRefuseDeployed, ConstraintBinding}.lean`

**Answer: YES — the floor gadget's completeness IS proven as a universally-quantified property, not
just a per-descriptor refuse.** But it is STAGED (nothing emitted into the deployed VK; the docstrings
say so).

| Theorem (file:line) | Class | What it is |
|---|---|---|
| `ConstraintBinding.omission_caught_under_binding` (`:151`) | **SECURITY-PROPERTY / COMPLETENESS** | ∀ declaration/manifest: an omitted required tag is rejected whatever alternate declaration the prover presents (given the declaration commit binds). The soundness core. |
| `CapacityCarrier.carrier_omission_impossible` (`:106`), `carrier_manifest_forced` (`:86`) | **COMPLETENESS** | ∀ two manifests sharing a caveat-commit: the published manifest is FORCED equal to the committed one — omission on the bound leg is impossible for a *pure light client*. |
| `BareCohortFloorRefuse.declared_tag_unsat_under_bare` (`:442`); `BareCohortFloorRefuseDeployed.declared_capacity_unsat_deployed` (`:288`) | **COMPLETENESS** (whole-cohort) | ∀ capacity tag `T`, ∀ bare-cohort member: a declared-capacity turn is UNSAT under a gate-less descriptor — it cannot be silently routed around the gate. `non_declared_floor_zero` (`:249`) is the matching no-false-reject direction. |
| `CarrierBoundFloorGadget.gentian_forged_floor_unsat_carrier` (`:466`) | SECURITY-PROPERTY, tag-17 in-AIR | ∀ satisfying trace: a forged floor omitting the escrow tag is UNSAT — the tag-17 in-AIR refinement of the coverage property. |

All gentian-floor files close `#assert_all_clean` under a single named `Poseidon2SpongeCR` /
`DeclCommitBinds` collision-resistance hypothesis, never an axiom. Separately,
`Circuit/CustomCarrierAttack.lean` (`deployed_admits_unbacked`, `:122`) is a NEGATIVE result — an
adversarial refutation that a *different* (custom-effect) carrier's `proofBind` gate is vacuous over
the deployed AIR — unrelated to the capacity floor, listed so it is not mistaken for one.

---

## THE HONEST GAPS — refinement/floor, but no security-property proof (yet)

1. **DECO payment unforgeability is ASSUMED, not proven, and has no UC proof.** `deco_authenticates_payment`
   (`Crypto/Deco.lean:315`) is a soundness refinement resting on ed25519 EUF-CMA + HMAC + the external
   Web-PKI/Stripe floor. There is no security-property theorem that the payment attestation *cannot be
   forged* independent of those carriers, and **PerfectUC is not wired to DECO** — no simulator/UC
   argument for the payment construct.

2. **Every capacity's circuit-side / pure-light-client witness is STAGED, not deployed.** The vault
   no-dilution, escrow atomicity, and obligation discharge safety are proven over pure math / the
   executor / an **off-AIR gate predicate** whose VK bytes are explicitly unchanged
   (`Vault.lean` §6, `SealedEscrow.lean` §6b, etc.). The in-AIR satisfaction weld that would let a pure
   light client witness them (`CapacitySatisfaction.lean`, `CarrierBoundFloorGadget.lean`) is built but
   NOT emitted into a committed VK and NOT flipped onto the live path
   (`CapacitySatisfaction.lean:46-54`). So in production today a *re-executing validator* is witnessed,
   a *pure light client* is not. This is the "circuit tooth is the executor tooth's named shadow" seam.

3. ~~**SealedEscrow has no standalone economic no-theft invariant.**~~ **CLOSED** (`SealedEscrow.lean`
   §9, `sealedescrow_no_theft` `:753`). Escrow now carries the economic no-theft world-property Vault
   (`deposit_no_dilution`) and PrepaidLease (`remaining_plus_drawn_conserved`) already had: a
   *reachability invariant* over the FULL deployed op set — **deposit / settle / reclaim** (the last
   was previously absent from the Lean model). Every reachable escrow satisfies **per-leg value
   conservation** (`paid s + locked s = entered s` — no leg pays out beyond what entered it; a
   never-deposited leg pays nothing) and **no free lunch** (`status s = Empty → recv s = 0`: a party
   that never funded receives nothing), with `escrow_solvent` (`:769`, `recvTotal ≤ enteredTotal`) as
   the total-value corollary. Anti-vacuity both poles: `honest_swap_reachable` (a reachable settle
   genuinely extracts — A gets B's leg, B gets A's) fires; `halfopen_theft_unreachable` (taking a
   counterparty's leg without funding one's own is UNREACHABLE) + `phantom_extraction_unreachable`
   bite. `#assert_axioms`-clean; registered as row 21 of `NON-VACUITY-MANIFEST.md`.

4. **The "UC layer" is an abstract theory shelf, not wired to the deployed system.** Of ten
   `Metatheory/*` files, only **SettlementSoundness** is genuinely connected to a deployed construct.
   The game files (SafetyGame/ReachGame/EnergyGame) are wired to **Polis** governance, not the crypto
   kernel. ConstructiveKnowledge / EpistemicConsensus / Disputation / CommonSecret / ResharingChain are
   self-described **candidate-independent** abstract results (realizability, epistemic logic, threshold
   secret-sharing) that reuse dregg *seams* as a library but prove nothing about a specific deployed
   dregg object. The computational UC theorem is explicitly OPEN (`PerfectUC.lean:502`).

5. **The integrity guarantee (C) and the E-attestation leg are refinements, not properties.** "A
   receipt binds the whole post-state" (`integrity_guarantee`, `AssuranceCase.lean:412`) and
   "verify agg.root ⟹ the history executed/ordered correctly" (`AggregateAttests`) are faithfulness /
   soundness refinements — they belong in ember's "we have tons of these" bucket, not the
   security-property bucket. (The conservation-from-verification leg IS a derived security property.)

---

## THE STRENGTHS — genuine security-properties we DO have proven

1. **Authority non-amplification, as a property with teeth.** `IsNonAmplifying` is a real subset
   relation (`EffectsAuthority.lean:197`); `introduce_non_amplifying` + `amplifying_grant_rejected`
   prove no cap-conferring mouth grows authority AND the predicate rejects amplifying grants
   (`AssuranceCase.lean:166`). Extended over arbitrary delegation chains through the KERNEL by
   `Membrane.reshareN_attenuates` (`Deos/Membrane.lean:122`) — the cleanest security-property in the
   corpus (no gate, no circuit). Re-certified `KeystoneAuditNonAmp` / `KeystoneAuditAuthModes`.

2. **Value conservation as a reachability invariant.** `reachable_total_zero`
   (`ReachableConservation.lean:49`): a nonzero-sum state is *unreachable* — `∀ a, Σ_c bal c a = 0`,
   identically zero, floor NONE beyond integer arithmetic. Teeth: the legacy mint/burn ops provably
   *break* it. The deployment-correspondence legs (signed wells, genesis issuer-moves, fees-as-moves)
   are reported CLOSED on the deployed chain (`AssuranceCase.lean:1045+`).

3. **Freshness / no-double-spend.** `freshness_guarantee` (`AssuranceCase.lean:581`): a committed
   spend was fresh and a same-nullifier replay fails closed. Double-spend impossible at the term level.

4. **Economic safety of the vault (ERC-4626 inflation immunity), as a property.** `deposit_no_dilution`
   / `deposit_price_non_decreasing` (`Deos/Vault.lean:175/:187`): price-per-share never decreases over
   *any* deposit, proven over the share arithmetic — the strong property ERC-4626's rounding lacks.

5. **Lease budget-conservation, as a property.** `remaining_plus_drawn_conserved`
   (`Deos/PrepaidLease.lean:396`): `remaining + drawn = budget` (Σδ=0); `budget_never_overdrawn`
   (`:378`) — no value appears or vanishes, ∀ periods.

6. **Hatchery temporal invariant-forever, over the executor.** `invariant_forever`
   (`Deos/Hatchery.lean:233`) / `attested_enforces_forever` (`:291`): under every admitted-turn
   schedule the declared cell invariant holds at every index — a genuine ∀-trajectory safety property
   over the executor `evalStep` transition, gated on a non-forgeable attestation.

7. **Obligation cursor monotonicity.** `cursor_strict_mono` (`Deos/StandingObligation.lean:208`) — the
   arithmetic backbone of the one-shot / no-double discharge discipline.

8. **Settlement soundness, wired to the deployed model.** `settlement_soundness`
   (`Metatheory/SettlementSoundness.lean:153`) + `revoke_before_tip_unsettleable` (`:192`): a settled
   turn's authority was LIVE at the tip; a revoked-before-tip cap is *unsettleable*. Instantiated
   non-tautologically on `deployedSettle` (a restatement of the deployed circuit gate). The one
   genuinely-wired UC-flavored security-property.

9. **Capacity-floor completeness (a declared capacity is always caught).** `omission_caught_under_binding`
   (`Deos/ConstraintBinding.lean:151`), `carrier_omission_impossible` (`Deos/CapacityCarrier.lean:106`),
   `declared_tag_unsat_under_bare` (`Deos/BareCohortFloorRefuse.lean:442`) — universal coverage under
   Poseidon2-CR. (Strength of statement; deployment is STAGED — see gap 2.)

10. **Light-client unfoolability, over the whole history.** `unfoolability_guarantee` /
    `conserves_from_verification` (`AssuranceCase.lean:666`) + the game-based reduction
    `LightClientUC.unfoolable_of_floor`: a `verify agg.root`-only client learns A–D for the whole
    history, and a tampered aggregate cannot bind. (The attestation leg is refinement; the
    conservation-from-verification leg is a derived security property.)

---

## Precise answer to ember

- **Proven-safe as security-properties:** authority non-amplification (with teeth, and over the kernel
  via Membrane), value conservation (imbalance unreachable), freshness/no-double-spend, vault
  no-dilution / inflation-immunity, lease budget-conservation, hatchery invariant-forever, obligation
  cursor monotonicity, settlement soundness, capacity-floor completeness.
- **Only-refined (soundness, not a property of the world):** integrity / receipt-binds-whole-post-state
  (the memory-program family), the E-attestation leg, DECO `deco_authenticates_payment`, and every
  capacity `*Gate` forcing/rejection. These are ember's "we have tons of these."
- **Assumed floor (correctly named):** Poseidon2-CR, FRI/STARK, ed25519 EUF-CMA, HMAC, AEAD, DLog,
  PostGSTProgress — and DECO's unforgeability + Web-PKI/Stripe floor rest here, not on a proof.
- **UC specifically:** we have `perfectUC_composition` (perfect/statistical, deterministic ideals)
  wired ONLY to the disclosure functionality; the computational UC theorem is OPEN; no UC proof exists
  for DECO, settlement (which has its own non-UC soundness), or the kernel. The rest of `Metatheory/*`
  is an abstract theory shelf, not wired to the deployed system.
- **The single biggest honest gap:** the capacity safety properties (vault/escrow/obligation) and the
  floor-completeness are witnessed today only by a *re-executing validator*; the pure-light-client
  in-AIR weld is STAGED, not in the deployed VK.
