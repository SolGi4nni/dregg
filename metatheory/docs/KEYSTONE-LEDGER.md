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
| **AUDITED** (`@[load_bearing_keystone]` PASS) | **86** | NonAmp 8 · AuthModes 5 · Integrity 8 · Freshness 10 · Unfoolability 12 · Supply 5 · Conservation 15 · Transport 7 · **Runnable (Wave-4 HARD) 16** |
| **AUDITABLE-not-yet · CHEAP** | **~1** | only stragglers remain (Waves 1–3 audited; the residue is the few teeth/witness defs the linter already consumes) |
| **AUDITABLE-not-yet · HARD** | **~1** | the Wave-4 HARD family is now WELDED with genuine runnable witnesses (gated-forest run · stepped Argus strand · `VmRowEnv` · MMR opening — all over REALIZABLE CR carriers `encodeSponge`/`refSponge`); residue is `revocation_needs_consensus` (only if pursued) |
| **TERMINAL-CRYPTO-FLOOR** | **3** | CR/MMR adapters — terminal BY DESIGN, do NOT witness away |
| **IMPOSSIBILITY / NON-PATTERN** | **1–2** | `dead_undecidable` (`¬∃ decider`); `revocation_needs_consensus` (necessity-shape) |
| **CALIBRATION / TEETH-attached / CLOSED-apex** | **~24** | the 11 local conjunction apexes + the teeth/witness defs the linter already consumes |

**"Left to audit" ≈ 2** (the Wave-4 HARD family CLOSED, see below). The floor portals proper
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

**Wave 4 (HARD — WELDED with genuine runnable witnesses).** All 16 carry a `*_satisfiable` that
EXERCISES the conclusion on a CONCRETE runnable instance + discriminating `*_teeth`, audited GREEN +
axiom-clean. The KEY FINDING: the named CR floors are REALIZABLE — `Poseidon2SpongeCR` is inhabited by a
proven-injective concrete sponge (`FloorsNonVacuous.encodeSponge` / `Poseidon2Binding.refSponge`), and
`compressNInjective`/`cellLeafInjective`/`logHashInjective` are discharged from it via the
`*_of_realization` helpers. So the "crypto-injectivity-conditioned" keystones are NOT terminal — they
weld by supplying the realizable carrier + an honest concrete instance:

  * **the gated memory-program / FOREST family** (`Dregg2/Verify/KeystoneAuditRunnable.lean`):
    `balanceA_step_memprog` / `eachStepMemProg_of_all_covered` / `forest_of_covered_is_memory_program`
    + the 7 `execFullForestG_*` (conserves_per_asset / conserves_exact / ledger_per_asset / no_amplify /
    each_attests / root_attests / unauthorized_fails). Fixtures: a COMMITTED gated `transferForestG` (a
    single covered `.balanceA` node, concrete `NodeAuthS = mkAuth goodCred [trueCaveat]`, gate passed) +
    the delegation-bearing `goodFullForestG` (for `no_amplify`, two real edges); teeth = `forgedCredForestG`
    (a forged gate ⇒ `none`).
  * **the stepped Argus strand** (`KeystoneAuditRunnable.lean`): `argus_strand_{conserves,light_client}`
    — `argusStrand teethGenesis [honestTurn]` steps `interpChained` on one real transfer; light_client
    fires through a concrete inhabited `EngineSound` (accepting verifier, toy zero-hashes); teeth =
    `tampered_argus_strand_rejected`.
  * **`runnable_binds_same_system_roots`** (`KeystoneAuditSystemRoots.lean`): a concrete `VmRowEnv`
    satisfying `siteHoldsAll encodeSponge · wideHashSites` + the carrier pin, over `encodeSponge_cr`.
  * **`argus_circuit_executor_receipts_agree` + `{argus,transfer}_published_index_pins_receipt`**
    (`KeystoneAuditArgusReceipt.lean`): the `writeCell0` receipt + a concrete MMR `Opens` opening at a
    dense position, over the realized injective carriers (`refLeafRealization`/`refLogRealization`/
    `encodeSponge_cr`). The `mroot`-PI premises hold concretely with `k' = k₂` / `L' = L`.

NO Wave-4 keystone was reclassified TERMINAL — the realizable-CR route discharged each. The only
remaining HARD candidate is `revocation_needs_consensus` (a necessity/lower-bound shape, only if pursued).

Status: 86 AUDITED (70 Waves 1–3 + 16 Wave-4 HARD, GENUINE runnable witnesses, in
`Dregg2/Verify/KeystoneAudit{Runnable,SystemRoots,ArgusReceipt}.lean`).
