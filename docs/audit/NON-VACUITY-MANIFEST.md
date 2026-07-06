# Non-Vacuity Manifest — every load-bearing security-property theorem + its biting tooth

**Elevated-Assurance Pillar 4b** (`docs/deos/ELEVATED-ASSURANCE-PROGRAM.md` §4b). The poster's law:
*a green only counts if it reds when the thing it guards breaks.* This manifest is the total ledger
that makes that law a **gate** — one row per load-bearing security-property theorem (the ones that
claim a WORLD property, per `docs/audit/SECURITY-PROPERTY-MAP.md`), each pinned to:

- **fires** — a NAMED, `#assert_axioms`-clean non-vacuity companion: the theorem's hypotheses are
  jointly satisfiable AND its conclusion is exercised on a concrete instance (not vacuously true), and
- **bites** — a NAMED biting companion: a hostile forge/mutation that makes the guarded property
  FALSE, so the theorem is two-valued (not `:= True`).

The **meta-gate** that enforces this manifest — `circuit/tests/security_property_nonvacuity_gate.rs` —
is a static ledger (the `keystone_descriptor_deployment_gate.rs` idiom, because Lean theorems are not
reflectively enumerable from Rust). It REDS when a load-bearing theorem is `Missing` a tooth, when a
`SpotCheckedOnly` row lacks a `promote:` closure lane, or when a named companion is **absent from the
metatheory Lean source** (the ledger cannot go stale silently — deleting a Lean tooth reds the gate).
Its companion in-band check is Lean's `#keystone_audit_tagged` (`Dregg2/Verify/KeystoneLint.lean`),
which sweeps every `@[load_bearing_keystone]` and throws at elaboration if a tagged keystone loses its
`satisfiable`/`teeth`. This gate is the **totality** layer over that per-keystone discipline.

## Status classes

- **HAS-BITING-TOOTH** — a NAMED fires + a NAMED bites, both source-grounded. The gate passes.
- **SPOT-CHECKED-ONLY** — only `#guard`/`example` witnesses (they red at elaboration but are not
  registrable NAMED companions). Allowed ONLY with a `promote:` closure lane.
- **MISSING** — no non-vacuity companion. Always fails the gate. *(The finding — none remain.)*

## The ledger

| # | Security-property theorem (file:line) | Class | fires | bites |
|---|---|---|---|---|
| 1 | `authority_guarantee` (AssuranceCase.lean:166) | HAS-BITING-TOOTH | `attenuate_non_amplifying_satisfiable` | `attenuate_non_amplifying_teeth` |
| 2 | `conservation_guarantee` (AssuranceCase.lean:259) | HAS-BITING-TOOTH | `reachable_total_zero_satisfiable` | `reachable_total_zero_teeth` **(added 4b)** |
| 3 | `freshness_guarantee` (AssuranceCase.lean:581) | HAS-BITING-TOOTH | `noteSpendStmt_no_double_spend_satisfiable` | `noteSpendStmt_teeth` |
| 4 | `unfoolability_guarantee` (AssuranceCase.lean:666) | HAS-BITING-TOOTH | `light_client_fires_on_real_chain` | `tampered_aggregate_cannot_bind` |
| 5 | `integrity_guarantee` (AssuranceCase.lean:412) *(refinement, but load-bearing + toothed)* | HAS-BITING-TOOTH | `writeCell0_receipt_eq` | `writeCell0_receipt_observable` |
| 6 | `introduce_non_amplifying` / `IsNonAmplifying` (Exec/EffectsAuthority.lean:197) | HAS-BITING-TOOTH | `introduce_non_amplifying_satisfiable` | `introduce_non_amplifying_teeth` |
| 7 | `reshareN_attenuates` (Deos/Membrane.lean:122) | HAS-BITING-TOOTH | `reshareN_attenuates_satisfiable` **(added 4b)** | `reshare_refuses_amplification` |
| 8 | `reachable_total_zero` (Exec/ReachableConservation.lean:49) | HAS-BITING-TOOTH | `reachable_total_zero_satisfiable` | `reachable_total_zero_teeth` **(added 4b)** |
| 9 | `deposit_price_non_decreasing` (Deos/Vault.lean:187) | HAS-BITING-TOOTH | `established_deposit_accepts` | `dilution_rejected` |
| 10 | `settlement_soundness` (Metatheory/SettlementSoundness.lean:153) | HAS-BITING-TOOTH | `deployedSettle_nonvacuous` | `deployedSettle_revoke_unsettleable` |
| 11 | `mintA_authorized` (Circuit/Spec/SupplyCreation.lean) | HAS-BITING-TOOTH | `mintA_authorized_satisfiable` | `mintA_rejects_unauthorized` |
| 12 | `captp/token/custom_sound` (Exec/AuthModes.lean) | HAS-BITING-TOOTH | `custom_sound_satisfiable` | `custom_sound_teeth` |
| 13 | `custom_binding_from_fold` (Circuit/CustomBindingFromFold.lean:147) | HAS-BITING-TOOTH | `honest_companion_fires` | `forged_unsat_demo` |
| 14 | `factory_binding_from_fold` (Circuit/FactoryBindingFromFold.lean:145) | HAS-BITING-TOOTH | `honest_companion_fires` | `forged_childvk_unsat_demo` |
| 15 | `bridge_binding_from_fold` (Circuit/BridgeBindingFromFold.lean) | HAS-BITING-TOOTH | `honest_companion_fires` | `forged_mint_hash_unsat_demo` |
| 16 | `sovereign_binding_from_fold` (Circuit/SovereignBindingFromFold.lean) | HAS-BITING-TOOTH | `honest_companion_fires` | `forged_keycommit_unsat_demo` |
| 17 | `membership_binding_from_fold` (Circuit/MembershipBindingFromFold.lean) | HAS-BITING-TOOTH | `honest_companion_fires` | `forged_tuple_unsat_demo` |
| 18 | `dsl_binding_from_fold` (Circuit/DslBindingFromFold.lean) | HAS-BITING-TOOTH | `honest_companion_fires` | `forged_rc_unsat_demo` |
| 19 | `hatchery_binding_from_fold` (Circuit/HatcheryBindingFromFold.lean) | HAS-BITING-TOOTH | `honest_companion_fires` | `forged_contract_unsat_demo` |
| 20 | `deco_binding_from_fold` (Circuit/DecoBindingFromFold.lean) | HAS-BITING-TOOTH | `honest_companion_fires` | `forged_payment_hash_unsat_demo` |
| 21 | `sealedescrow_no_theft` (Deos/SealedEscrow.lean:753) | HAS-BITING-TOOTH | `honest_swap_reachable` | `halfopen_theft_unreachable` |
| 22 | `deco_attestation_unforgeable` (Crypto/DecoUnforgeable.lean) | HAS-BITING-TOOTH | `attestation_fires` | `attestation_bites` |

**Tally: 22 rows / 22 HAS-BITING-TOOTH / 0 SPOT-CHECKED-ONLY / 0 MISSING** (after Pillar 4b + escrow no-theft + DECO attestation unforgeability).

**Row 22 — DECO payment-attestation unforgeability (survey gap #1, closed — rung 4).** DECO's
authenticity was ASSUMED, not proven (`SECURITY-PROPERTY-MAP.md:192`): `deco_authenticates_payment`
is a soundness *refinement* (accept ⟹ facts hold, given the §8 carriers), with no proof that a payment
*cannot be forged*. `deco_attestation_unforgeable` (`Crypto/DecoUnforgeable.lean`) is the rung-4 world
property: modelling the ideal functionality `F_attestation` (on `F_LC`) and the game `AttForgery`/
`AttUnforgeable`, the reduction `forgery_yields_break` turns any forged attestation of a session that
did NOT happen into a CONCRETE ed25519 `SigForgery` OR HMAC `MacForgery` (the binding leg
`deco_binding_forgery_to_collision` reduces to a Poseidon2 collision). The floor is EXACTLY
`deco_binds_payment`'s trust base — ed25519 EUF-CMA + HMAC + Poseidon2 CR + STARK extractability — all
standard, NO dregg-specific parked assumption. **fires** — `attestation_fires`: a genuine reference
attestation IS `decoAuthenticated` (F_attestation would emit) and verifies. **bites** —
`attestation_bites` (`Forge` namespace): a DECO forge-kernel over which a concrete `AttForgery` exists
and the reduction extracts a genuine ed25519 `SigForgery` (sharpened by `attestation_bites_is_sig_forgery`).
Both `#assert_axioms`-clean. Registered as `attestationDynamics` / `deco_attestation_via_schema` in the
`governed_holds` schema (`Metatheory/Adversary/Instances.lean` §3.9), composing with — distinct from —
`decoCarrierDynamics` (the fold-backing): unforgeability ∘ backing = the mint credited real money.

**Row 21 — SealedEscrow's economic no-theft (survey gap #3, closed).** SealedEscrow (escrow capacity,
tag 17) previously had only refinements (one-shot replay, gate-refinement, commitment-binding) — no
standalone WORLD-property invariant, unlike Vault (`deposit_price_non_decreasing`) and Lease
(`budget_never_overdrawn`). `sealedescrow_no_theft` (`Deos/SealedEscrow.lean` §9) closes it as a
reachability invariant over the FULL deployed op set (deposit / settle / reclaim — the last was missing
from the Lean model): every reachable escrow satisfies per-leg value conservation (`paid + locked =
entered` — no leg pays out beyond what entered it) AND *no free lunch* (a never-funded party receives
nothing), with `escrow_solvent` (payouts ≤ deposits) as the total-value corollary. **fires** —
`honest_swap_reachable`: a reachable honest settle that legitimately extracts (party A gets B's leg,
B gets A's, value DOES leave). **bites** — `halfopen_theft_unreachable`: the half-open theft (A takes
B's locked leg without funding its own) is UNREACHABLE. Both `#assert_axioms`-clean.

## The finding (what 4b closed)

Before this lane, two load-bearing property apexes each had **one leg of the tooth as a `#guard`
only**, not a NAMED companion the meta-gate could register:

1. **`reachable_total_zero`** (Guarantee B) had a NAMED `reachable_total_zero_satisfiable` (fires) but
   its biting forge lived only as `#guard` witnesses in `ReachableConservation.lean` (the unauthorized
   mint / non-live-issuer refusals). **Added** `reachable_total_zero_teeth` + `nonzero_state_unreachable`
   (`Dregg2/Verify/KeystoneAuditConservation.lean`): a fabricated single-cell state carrying value with
   no matching issuer-well debit FAILS `ExactConservation` and is therefore **unreachable** — the value
   law provably discriminates and constrains the reachable state space. `#assert_axioms`-clean.

2. **`reshareN_attenuates`** (Guarantee A extension, over the kernel) had a NAMED
   `reshare_refuses_amplification` (bites) but its non-vacuity fired only as `#guard`s. **Added**
   `reshareN_attenuates_satisfiable` (`Dregg2/Deos/Membrane.lean`): a concrete two-hop reshare chain
   whose `⊆` conclusion is exercised AND whose attenuation is STRICT (a `grant` authority held upstream
   is darkened downstream) — the subset is proper, so the theorem is non-vacuous. `#assert_axioms`-clean.

Both are now registered rows above, and the meta-gate cross-checks that these exact names exist in the
Lean source, so deleting either tooth reds the build.

## How the meta-gate is itself non-vacuous

`meta_gate_bites` (`security_property_nonvacuity_gate.rs`) proves the gate REDS on: a `Missing` row, an
un-laned `SpotCheckedOnly` row, a `HasBitingTooth` naming a companion absent from the source (the
stale-ledger catch), and an empty companion name — and PASSES a fully-grounded row (so it is not
red-for-everything). The decisive case removes the real `reachable_total_zero_teeth` name from the
scanned source-set and asserts the gate reds on exactly that row. A coverage gate that passed vacuously
would be the exact sin it polices; this one is proven to bite.

## Adding a new security property

When a new WORLD-property apex lands: add its `*_satisfiable` (fires) + a biting `*_teeth`/`forged_*`
(bites) companion in Lean, then add a `HasBitingTooth` row here and in the gate's `security_property_manifest()`.
A new property added without a row does not appear in the ledger — pair this with review of new
`@[load_bearing_keystone]` / `#assert_axioms` blocks. If you genuinely cannot name the tooth yet, use a
`SpotCheckedOnly("… promote: <lane>")` row — a conscious, reviewed decision, never a silent gap.

## The unified schema — every row above, as ONE `governed_holds`

`metatheory/Metatheory/Adversary/Schema.lean` collapses the deployed guarantees into a single
abstract schema `GovernedDynamics` = (Control, run, accept, invariant, `holds : GovernedProperty`),
consumed by ONE lemma `governed_holds : ∀ D c, D.accept (D.run c) → D.invariant (D.run c)`.
`metatheory/Metatheory/Adversary/Instances.lean` re-states the WHOLE deployed assurance case as
instances of that schema — each instance's `holds` field **IS** the already-registered deployed
theorem (reused, not re-proven), so the schema view inherits every row's cleanliness and teeth:

| deployed property (registered row) | schema instance | `holds :=` | schema-level anti-vacuity |
|---|---|---|---|
| `settlement_soundness` (row 10) | `settlementDynamics` | `settlement_soundness` | `settlement_accept_bites` + `settlement_invariant_bites` |
| `light_client_verifies_whole_history` (row 4) + genesis anchor | `wholeHistoryDynamics` | `light_client_verifies_anchored_history` | `wholeHistory_accept_bites` + `wholeHistory_invariant_bites` |
| `custom_binding_from_fold` (row 13) | `customCarrierDynamics` | `custom_binding_from_fold` | `customCarrier_bites` |
| `factory_binding_from_fold` (row 14) | `factoryCarrierDynamics` | `factory_binding_from_fold` | `factoryCarrier_bites` |
| `bridge_binding_from_fold` (row 15) | `bridgeCarrierDynamics` | `bridge_binding_from_fold` | `bridgeCarrier_bites` |
| `sovereign_binding_from_fold` (row 16) | `sovereignCarrierDynamics` | `sovereign_binding_from_fold` | `sovereignCarrier_bites` |
| `membership_binding_from_fold` (row 17) | `membershipCarrierDynamics` | `membership_binding_from_fold` | `membershipCarrier_bites` |
| `dsl_binding_from_fold` (row 18) | `dslCarrierDynamics` | `dsl_binding_from_fold` | `dslCarrier_bites` |
| `hatchery_binding_from_fold` (row 19) | `hatcheryCarrierDynamics` | `hatchery_binding_from_fold` | `hatcheryCarrier_bites` |
| `deco_binding_from_fold` (row 20) | `decoCarrierDynamics` | `deco_binding_from_fold` | `decoCarrier_bites` |
| `deployed_system_secure` (rows 1–5 composed) | `assuranceApexDynamics` | `deployed_system_secure` | inherits rows 1–5 teeth (the 5-guarantee invariant) |

The payoff `assurance_case_governed` runs non-domination, unfoolability, settlement soundness and
whole-history through `governed_holds` against ONE `Adversary` — the entire top-level security of
dregg as one lemma, N instances, one adversary. All `*_via_schema` / `*_bites` are `#assert_axioms`-
clean (asserted at the foot of `Instances.lean`). These add NO new WORLD-property (the underlying
rows above are the registered properties); the schema is a unification over them, so the Rust
meta-gate `security_property_manifest()` is unchanged.

### Named folded-hypothesis seams (the schema's honest discipline)

Where a per-control realizability floor is needed for `accept`, it is folded in FAITHFULLY and NAMED
(the `WitnessDecodes` precedent from `circuitDynamics`): `wholeHistoryDynamics` folds `EngineSound`
into accept; `assuranceApexDynamics` folds the per-step coverage `EachStepMemProg` (`hcov`),
`EngineSound`, and `KernelGenesisPin`/`SeamStruct` — each already an explicit hypothesis of
`deployed_system_secure`. Settlement and the 8 carriers fit with NO folded seam (the binding
discipline / crypto floor is fixed at instance-build, not per-control).
