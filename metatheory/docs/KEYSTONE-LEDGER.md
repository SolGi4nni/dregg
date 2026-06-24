# Keystone ledger — the AssuranceCase apex, honestly classified

The 110 `#assert_axioms` pins in `Dregg2/AssuranceCase.lean` are an axiom-hygiene ledger, NOT 110
units of debt. Each is one of five shapes; collapsing them into "unaudited" is the over-pessimism
error ([[feedback-named-seam-is-not-a-hole]]). This ledger classifies the real apex universe (~115:
the 110 pins ∪ 5 family-only audited keystones) so "what is left" reads truthfully.

The discipline: `@[load_bearing_keystone satisfiable:=W teeth:=T]` + `#keystone_audit`
(`Dregg2/Verify/KeystoneLint.lean`) — an apex theorem is audited iff it carries a GENUINE
non-vacuity witness (conclusion exercised on a concrete instance, not vacuous) + discriminating
teeth (a hostile instance refuted) + axiom-cleanliness.

## The honest classification (headline)

| class | count | meaning |
|---|---|---|
| **AUDITED** (`@[load_bearing_keystone]` PASS) | **43** | NonAmp 8 · AuthModes 5 · Integrity 8 · Freshness 10 · Unfoolability 12 |
| **AUDITABLE-not-yet · CHEAP** | **~28** | the real near gap — `def`+`decide`/`rfl`/concrete-instance witnesses; many teeth already exist |
| **AUDITABLE-not-yet · HARD** | **~13** | runnable-circuit / `VmRowEnv` / stepped-strand / gated-forest witnesses — genuine-witness-only care |
| **TERMINAL-CRYPTO-FLOOR** | **3** | CR/MMR adapters — terminal BY DESIGN, do NOT witness away |
| **IMPOSSIBILITY / NON-PATTERN** | **1–2** | `dead_undecidable` (`¬∃ decider`); `revocation_needs_consensus` (necessity-shape) |
| **CALIBRATION / TEETH-attached / CLOSED-apex** | **~24** | the 11 local conjunction apexes + the teeth/witness defs the linter already consumes |

**"Left to audit" = the CHEAP + HARD AUDITABLE-not-yet ≈ 41, not 67.** The floor portals proper
(`StarkSound`, `Poseidon2SpongeCR`, the `S_live` CR set, `logHashInjective`, `WitnessDecodes`,
ed25519/HMAC/AEAD, `PostGSTProgress`) enter as Prop-portals/typeclasses and are correctly NOT pins.

## TERMINAL (do not force a witness — misclassifying these as debt is the error)
- `cap_leaf_value_codec` (AC:534), `index_boundary_mroot_derived` (AC:535),
  `published_position_pins_value` (AC:526) — CR/MMR-canonicity adapters, terminal under `Poseidon2SpongeCR`.

## IMPOSSIBILITY / NON-PATTERN
- `Liveness.dead_undecidable` (AC:604) — a halting-reduction `¬∃ decider`; a `satisfiable` would
  contradict it. Audited by its proof; operationally resolved via `Lease`/`leaseExpired`.
- `Liveness.revocation_needs_consensus` (AC:598) — necessity/lower-bound (`CrossVatSound`); HARD-if-witnessed, else accept as necessity-shape.

## AUDITABLE-not-yet — the campaign (cheap-first; HARD = genuine witnesses only)
**Wave 1 (CHEAP, teeth already exist):** the mint family — `mintA_authorized`, `execMintA_iff_spec`,
`recKMintAsset_delta`, `recKBurnAsset_delta`, `recKMintAsset_requires_live_issuer` (teeth:
`mintA_rejects_unauthorized` supplycreation:259, `recK{Mint,Burn}Asset_breaks_exact` IssuerMove:293,305).

**Wave 2 (CHEAP, arithmetic/library):** `Conserve.*` (sum_transfer_conserve, sum_indicator,
sum_pointUpdate, sum_conserve_of_deltas_zero), `recTransferBal_*`, `recKExec_conserves`,
`recTransfer_balanceSum_conserve`, `turnConserves_balance`, `conservation_over_monoid`,
`committed_iff_cleartext`, `ledgerDeltaAsset_eq_zero`, `reachable_total_zero`,
`execFull{A,TurnA}_conserves_exact`.

**Wave 3 (CHEAP, transport from an audited sibling):** `recKDelegateAtten_non_amplifying`,
`execFullA_{introduceA,attenuateA,delegateAttenA}_non_amplifying`; `writeCell0_receipt_binds_tail`,
`argus_circuit_executor_receipts_agree`, `stateCommit_binds_cells_and_rest`; `balanceA_step_memprog`,
`moveAsset_is_memory_program`, `eachStepMemProg_of_all_covered`, `forest_of_covered_is_memory_program`.

**Wave 4 (HARD — individual care; never a `True`-ish stub):** `runnable_binds_same_system_roots`
(VmRowEnv pair); `argus_strand_{light_client,conserves}` (step `interpChained` for one real strand —
teeth exist); `{argus,transfer}_published_index_pins_receipt` (concrete MMR opening); the 7
`execFullForestG_*` running-entry keystones (a concrete committed gated `FullForestG` run with real
`AuthPortal`/`MacKernel`); `revocation_needs_consensus` (only if pursued).

Status: 43 AUDITED. Driving Wave 1–3 (cheap) first; Wave 4 flagged for genuine witnesses.
