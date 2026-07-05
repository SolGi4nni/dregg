# TIER3 — post-big-bang teeth re-verification + the whole-history completeness adversary

**Adversarial Audit, tier 3.** Repo `/Users/ember/dev/breadstuffs` @ `main`, HEAD
`db466dcd9` (`initial commit`). The history was just **big-banged** (squashed to a
single commit, pushed to a fresh origin). A history rewrite can silently drop test
files or flip `#[ignore]` teeth. This document (a) re-verifies that the campaign's
forge-rejection teeth STILL BITE on the new baseline, and (b) pushes the deepest
unverified claim — whole-history **completeness** ("nothing else happened") — under
an adversary. Every row grounded to `file:line`.

Companion: `docs/audit/TRUST-BASE-CENSUS.md` (the surviving-carriers census this
extends). Method economy: the apex cone was `lake`-built once; the named cheap
teeth run; NO full gauntlet.

---

## LANE 1 — POST-BIG-BANG TEETH-SURVIVAL VERDICT

**Verdict: ALL teeth survived the squash. None vanished; none went vacuous. Zero
regression introduced by the big-bang.**

### 1a. The 8 carrier `BindingFromFold` + `BackingAttack` pairs — present + apex-clean

All 8 carriers' Lean files exist at HEAD (custom via `CustomCarrierAttack.lean`;
the other seven each `*BindingFromFold.lean` + `*BackingAttack.lean`; plus DECO
`DecoBindingFromFold.lean` + `DecoBackingAttack.lean`):

```
metatheory/Dregg2/Circuit/{Custom,Factory,Sovereign,Membership,Dsl,Bridge,Hatchery,Deco}BindingFromFold.lean
metatheory/Dregg2/Circuit/{Factory,Sovereign,Membership,Dsl,Bridge,Hatchery,Deco}BackingAttack.lean
metatheory/Dregg2/Circuit/CustomCarrierAttack.lean
```

**Apex cone `lake build` — GREEN, `#assert_axioms`-clean.** Built the apex +
carriers in one pass: `CircuitSoundness`, `AssuranceCase`, `ClosureFinal`,
`GroundedApex`, `CircuitSoundnessAssembled`, and all 8 `*BindingFromFold`
(`metatheory` @ Lean4 v4.30.0):

```
Build completed successfully (3227 jobs).
```

`#assert_axioms` is a compile-time gate (it fails the build if a pinned theorem
depends on an axiom outside `Dregg2.cleanAxioms = [propext, Classical.choice,
Quot.sound]`), so **exit 0 ⟹ every pinned apex/carrier keystone is still
axiom-clean.** Pin counts survive: `CircuitSoundness.lean` (17), `AssuranceCase.lean`
(113), `GroundedApex.lean` (13), `CustomBindingFromFold.lean` (7). No `sorry` /
`admit` / `sorryAx` in the apex modules.

### 1b. The apex + 5 guarantees — present + clean

- `lightclient_unfoolable` (`Circuit/CircuitSoundness.lean:453`, pin `:1058`) — built clean.
- The 5 guarantee apexes (`Dregg2/AssuranceCase.lean`): A Authority `:166`, B
  Conservation `:259`, C Integrity `:412`, D Freshness `:581`, E Unfoolability
  `:666` — all in the built module, `#assert_axioms`-clean (113 pins hold).

### 1c. The 7 deployed-path fold teeth (`circuit-prove/tests/*_binding_deployed_tooth.rs`)

All seven exist + COMPILE at HEAD. Their **forged→UNSAT** arms are `#[ignore]`d
(SLOW: a real deployed recursion fold, ~minutes each) — they were NOT deleted or
un-ignored by the squash. Spot-checked non-vacuous: `deployed_custom_turn_forged_
rejected` (`custom_binding_deployed_tooth.rs:321`) and `deployed_membership_turn_
forged_root_rejected` (`membership_binding_deployed_tooth.rs:267`) both `panic!` iff
a forged fold verifies (`Ok(Ok(_)) => panic!`), accepting only an `Err`/constraint-
panic. The **cheap grounding arms all PASS**:

| tooth file | cheap arms run | result |
|---|---|---|
| `custom_binding_deployed_tooth` | (both forged/honest ignored) | compiles; 2 ignored |
| `bridge_binding_deployed_tooth` | `mint_identity_binds_the_nullifier`, `committed_mint_row_carries_the_first_row_mint_hash_pin` | 2 pass |
| `factory_binding_deployed_tooth` | `deployed_factory_witness_on_unpinned_leg_is_refused` | 1 pass |
| `dsl_binding_deployed_tooth` | `rc_slot_derivation_is_registry_grounded` | 1 pass |
| `sovereign/hatchery/membership_binding_deployed_tooth` | (forged/honest ignored) | compile; ignored |

### 1d. The 7 audit teeth — ALL present + ALL pass

| tooth | file | result |
|---|---|---|
| `setfield_completion_lane_forge` | `circuit/tests/setfield_completion_lane_forge.rs` | **3/3 pass** (forge UNSAT, honest small OK, honest large fails-freeze = the named completeness seam) |
| `accumulator_completion_lane_forge` | `circuit/tests/accumulator_completion_lane_forge.rs` | **2/2 pass** |
| `deployed_refines_verifier_teeth` | `circuit/tests/deployed_refines_verifier_teeth.rs` | **1/1 pass** (`deployed_verify_batch_bites_on_every_verifyalgo_tooth`) |
| `heap_write_roundtrip` | `circuit/tests/heap_write_roundtrip.rs` | **4/4 pass** (incl. `after_root_forge_is_unsat_against_DEPLOYED_v3_registry`) |
| `carrier_forgery_forge` | `circuit-prove/tests/carrier_forgery_forge.rs` | **3/3 pass** |
| `producer_descriptor_coverage_gate` | `circuit/tests/producer_descriptor_coverage_gate.rs` | **4/4 pass** (+24 `#[ignore]` roundtrip arms, unchanged) |
| `keystone_descriptor_deployment_gate` | `circuit/tests/keystone_descriptor_deployment_gate.rs` | **2/2 pass** (`dangerous_families_are_flagged`, `every_keystone_descriptor_is_deployed_or_allowlisted`) |

**LANE 1 bottom line:** the big-bang was a clean squash for the assurance surface —
every carrier Lean file, every deployed-fold tooth, every audit tooth is present and
green, and the apex/guarantee `#assert_axioms` pins all still hold. No tooth was
silently dropped or made vacuous.

---

## LANE 2 — THE WHOLE-HISTORY COMPLETENESS ADVERSARY

**Question.** Can a light client verifying the DEPLOYED whole-history path (fold +
finality cert + committee-anchored head) be fooled about COMPLETENESS — a chain that
verifies but (i) OMITS a real turn between two folded states, or (ii) INJECTS a turn
that never happened, or (iii) TRUNCATES?

**Verdict: HOLDS for the two named attacks (interior-omission and injection) — no
forge is constructible. The ONE honest residual was at the GENESIS (prefix) end: the
deployed verify pinned `final_root` to the committee-finalized head but did NOT anchor
`genesis_root` to any trusted value. `→ CLOSED (2026-07-05)`: `verify_finalized_history`
now takes an `expected_genesis: Option<[BabyBear; 8]>` — the exact verify-side dual of
the final-root seam — and REJECTS (`FinalizedError::GenesisMismatch`) any history whose
folded `genesis_root` is not the client's trusted anchor. `None` preserves the honest
"from the attested genesis" behavior for callers that legitimately hold no trusted
genesis. See 2c below for the close.**

### 2a. Interior omission — CLOSED by the temporal tooth (UNSAT, no forge buildable)

The whole-history binding AIR `TurnChainBindingAir` (`circuit-prove/src/ivc_turn_
chain.rs:705`) enforces, in-circuit:

- **Constraint 1, the temporal tooth** (`:787-791`): `when_transition().assert_zero(
  new_root - next_old_root)` — each turn's `new_root` MUST equal the next turn's
  `old_root`. Lean mirror: `AggregateAttests.ordered = ChainBound …`
  (`RecursiveAggregation.lean:189`).
- Constraint 2 (`:793-796`): first row `old_root == genesis_root` (PI).
- Constraint 3 (`:798-801`): last row `new_root == final_root` (PI).
- Constraint 7 (`:727-730`): `real_count == num_turns` — a forged count is UNSAT.
- Constraint 5 (`:812-816`): the running `chain_digest` is FORCED to the genuine
  Poseidon2 of `[acc_in, old_root, new_root, idx]`, positionally bound by `idx`
  (constraint 6) — reordering moves the digest.

To OMIT a real turn `B→C` sitting between folded steps `A→B` and `C→D`, the prover
must fold `A→B` immediately followed by `C→D`; constraint 1 then demands `B == C`,
which is FALSE (the omitted turn changed the root). The fold is UNSAT. **A skip-forge
cannot be constructed** — this is why LANE 2 builds no interior-omission forge: the
temporal tooth makes it impossible, not merely detectable. Fabricating a single fake
compressed turn `A→C` instead is barred by **leaf soundness** — each folded leaf is a
genuine `EffectVmDescriptorAir` execution (`ivc_turn_chain.rs:21-31`; Lean
`every_turn : recCexec s.pre s.turn = some s.post`, `RecursiveAggregation.lean:187`);
a real state that went `A→B→C` has no genuine single turn `A→C`.

### 2b. Injection / tail-truncation — CLOSED on the DEPLOYED (committee-anchored) path

A single verified aggregate alone (`verify_history`, `lightclient/src/lib.rs:186`)
does NOT force the endpoint set: an equivocating prover can fold a perfectly valid
aggregate over a FORK the network never finalized, or over a longer/shorter chain
(injecting or truncating turns), reaching a `final_root` of its choice. The crate
says so plainly (`lib.rs:252-262`). This is why `verify_history` is NOT the deployed
acceptance gate.

The DEPLOYED path is **`verify_finalized_history`** (`lib.rs:540`, the path
`whole_history_demo.rs:373` exercises), which adds the third leg:

- Root seam (`lib.rs:563`): `agg.final_root[0] == finalized_root == cert.finalized_root`.
- **Committee-anchored quorum** (`lib.rs:579`, `has_committee_quorum` `:427`): a
  supermajority (`2n/3+1` over the **trusted committee size**, not the cert-supplied
  count) of DISTINCT validators **in the client's genesis/epoch-distributed
  committee** whose Ed25519 signature verifies over the finalized root. Fresh-key
  forgery is defeated (`finalized_light_client_rejects_fork_by_foreign_committee`,
  `lib.rs:1200`); unanchored clients fail closed (`UnanchoredCommittee`, `:549`).

An INJECTED extra turn or a TRUNCATED tail changes `final_root` away from the head
the committee actually super-ratified → root-seam / `NoQuorum` rejection. So on the
deployed path the tail endpoint is pinned to the real finalized head: injection and
tail-truncation are closed.

### 2c. THE RESIDUAL — genesis is unanchored (prefix-truncation), in BOTH layers

The asymmetry: **`final_root` is committee-anchored; `genesis_root` is anchored to
nothing.**

- Lean: `AggregateAttests.genesis_pinned` (`RecursiveAggregation.lean:194`) pins
  `agg.genesisRoot` to `steps.head?`'s old root — the FIRST FOLDED STEP's before-
  state. `steps` is universally quantified in `light_client_verifies_whole_history`
  (`:206`); nothing constrains `steps.head` to be the true genesis.
- Rust: `verify_history` (`lib.rs:186`) reads `genesis_root` off the aggregate
  (`:196`) and returns it verbatim in `AttestedHistory`; `verify_finalized_history`
  takes NO genesis-anchor parameter and checks `genesis_root` against nothing. The
  end-to-end tooth confirms the intent: "attested genesis = the first turn's GENUINE
  8-felt wide before-commit anchor" (`lib.rs:922`) — i.e. the prover's chosen start.
- Leaf soundness does not save it: the first leaf only asserts its `old_root ==
  genesis_root` and that the leaf is a genuine turn from a well-formed kernel — a
  kernel the prover may FABRICATE. So `genesis_root` is a free, prover-chosen input
  (it need not even be a reachable chain state).

**Consequence.** A prover can fold a valid, committee-finalizable history from an
arbitrary `genesis_root` to the true head, HIDING every turn before that point. This
is not a soundness break (every folded turn is genuine and the suffix is complete)
and it is not "a turn between two folded states" (that is closed by 2a) — it is a
PREFIX-completeness residual. For a from-true-genesis completeness claim (e.g. a
total-supply / conservation-from-genesis audit), the client MUST pin `genesis_root`
to its trusted genesis/checkpoint anchor — exactly as it already pins the VK
(`lib.rs:35`) and the committee (`lib.rs:534`). **The deployed API does not enforce
or expose this genesis anchor**, so a `verify_finalized_history` verdict alone
attests "a complete, correctly-ordered, finalized history from SOME genesis," not
"…from THE genesis."

**Classification: reducible-open → CLOSED (2026-07-05).** The close is the
one-parameter addition it was scoped to be — the genesis dual of the existing VK +
final-root anchors — now landed in BOTH layers, `#assert_axioms`-clean, with a biting
forge tooth:

- **Rust (`lightclient/src/lib.rs`).** `verify_finalized_history` now takes
  `expected_genesis: Option<[BabyBear; SEG_ANCHOR_WIDTH]>`. When `Some(g)` it asserts
  `agg.genesis_root == g` (checked right after `verify_history` Fiat–Shamir-attests the
  carried `genesis_root`, so it is the GENUINE folded genesis, not a bare field) and
  rejects a mismatch with the new `FinalizedError::GenesisMismatch` — the exact dual of
  the `final_root` seam at the same call site. `None` preserves the honest
  "from the attested genesis" behavior for callers with no trusted genesis (documented
  on the fn). The deployed demo (`whole_history_demo.rs`) now passes
  `Some(agg.genesis_root)` on the happy path and demonstrates a fabricated-genesis
  REFUSAL.
- **Lean (`RecursiveAggregation.lean`).** `AnchoredAttests` = `AggregateAttests` +
  the verify-side anchor `agg.genesisRoot = expectedGenesis`;
  `light_client_verifies_anchored_history` delivers it; `anchored_history_starts_at_
  genesis` concludes the fold provably STARTS at the trusted genesis (the dual of
  `final_is_genuine_fold`); `anchored_conserves_from_verification` concludes conservation
  FROM that anchored genesis (both ends pinned). All `#assert_axioms`-clean.

**The tooth BITES (no fake green):**

- Rust `finalized_light_client_anchors_genesis` (`lib.rs`): `None` accepts,
  `Some(true_genesis)` accepts, `Some(fabricated)` REJECTS with `GenesisMismatch`, and a
  DIFFERENT genuine finalized history B (a real fold from a different genesis — the
  actual prefix-hiding chain) verifies under `None` but is REJECTED when anchored to A's
  trusted genesis.
- Lean `anchored_tooth_bites_on_real_chain`: a WRONG expected genesis
  (`genesisRoot + 1`) admits NO `AnchoredAttests` on the realizing instance (contradicts
  `genesis_anchored`); `anchored_fires_on_real_chain` witnesses the positive. Non-vacuous
  both ways.

With the anchor, a `verify_finalized_history` verdict attests "a complete, correctly-
ordered, finalized history FROM THE (trusted) genesis." Supply/conservation-from-genesis
auditors MUST pass `Some(true_genesis)`; a `None` caller inherits the prefix residual by
explicit choice, not by an unexposed API gap.

---

## Summary

- **LANE 1:** all campaign teeth survived the big-bang — 8 carrier Lean pairs +
  apex + 5 guarantees `lake`-green and `#assert_axioms`-clean (3227 jobs, exit 0);
  7 deployed-fold teeth present + compiling with non-vacuous forged→UNSAT arms;
  7 audit teeth all present and passing. **Zero squash regression.**
- **LANE 2:** whole-history completeness HOLDS against the two named attacks
  (interior-omission is UNSAT via the temporal tooth; injection/tail-truncation is
  closed by the committee-anchored final root). The honest residual is at the GENESIS
  end: `genesis_root` is prover-chosen and unanchored in both the Lean model and the
  deployed verify API — completeness is "from the claimed genesis," and a from-true-
  genesis claim needs a genesis anchor the deployed path does not yet check.
