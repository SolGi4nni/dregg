# Whole-Tree Gauntlet Report

Date: 2026-07-14 · Branch: `main` · HEAD: `b96acd81a`
Method: full-tree build + key suites, routed through WARM pbuild lanes (Rust)
and the local warm `.lake` (Lean). Read/build-only — no code edits. Rust suites
run with `DREGG_REQUIRE_LEAN=0` where a lane lacks the seeded `libdregg_lean.a`
(the Lean closure is verified separately by the local `lake build`).

## Status table

| Gate | Result | Counts |
|------|--------|--------|
| Rust workspace build | PASS* | all committed crates compile; the one failure was uncommitted WIP (dregg-pay), re-verified green |
| Circuit teeth | **FAIL** | lib unit: 668 pass / **13 fail**; +2 integration targets compile-broken (pre-existing) |
| Turn / executor | PASS (+2 broken targets) | integration: **37/37 pass**; 1 target compile-broken today-drift, 1 pre-existing; production lib compiles |
| Bridge escrow | **FAIL** | dregg-bridge lib: 295 pass / **1 fail**; solana-lock 54 pass; cosmos-lock 12 pass |
| Lean Dregg2 | PASS | 9637 jobs, keystones kernel-clean, 0 errors |
| Lean Market | PASS | 3064 jobs, keystones kernel-clean, 0 errors |
| forge (chain/) | PASS | 160/160 across 10 suites, 0 failed |
| codegen-consistency | PASS | 6/6 (EVM real-proof, Solana alt_bn128, Cosmos arkworks all accept-real/reject-tampered) |

`*` The workspace `cargo build --workspace` reported a single error — see FAIL #4
(dregg-pay) — which is uncommitted mid-landing WIP, not a committed regression.
A targeted re-build of dregg-pay against the current tree finished green.

## VERDICT (3 lines)

- The committed PRODUCTION stack is green: both Lean libraries, forge (160),
  the 3-chain codegen consistency, the escrow contracts (solana-lock 54 /
  cosmos-lock 12), and the turn executor (37/37 integration) all pass; every
  committed workspace crate compiles.
- BUT there IS a real RED UMBRELLA from today's parallel swarm: the GAP#5 IMT
  leaf-arity-3 geometry migration + availability-weld / VK regen shifted the
  descriptor geometry (643→667 cols; welded width 1668) and left downstream
  soundness/consistency teeth RED that per-lane greens missed — 13 circuit
  refusal teeth, the bridge ETH calldata ground-truth fixture, and the turn
  rotation-witness test.
- These are geometry/VK-regen DRIFT (commit `919b2b0b8` self-labels its
  soundness-completer as "STILL OWED"), concentrated in the arity-3 / weld-regen
  family — they need the circuit-geometry and settlement-VK lane owners to
  reconcile the teeth/fixtures to the new geometry; not fixed here.

## FAIL detail (precise, with culprit + classification)

### FAIL #1 — Circuit teeth: 13 lib-unit refusal/weld teeth (geometry drift, TODAY)

`cargo test -p dregg-circuit --lib`: 668 pass / 13 fail. All 13 are soundness
"refusal" teeth reporting an accepted forgery ("… tooth OPEN"):

- `descriptor_ir2::tests::` (11): `ir2_forged_digest_refuses`,
  `ir2_forged_map_opening_refuses`, `ir2_forged_output_lane_refuses`,
  `ir2_tampered_read_refuses`, `ir2_amplified_submask_refuses`,
  `ir2_wide_absorb_forged_carrier_lane_refuses`,
  `ir2_node8_full_width_compression_binds_both_children`,
  `deployed_heap_splice_rejects_content_mismatch`,
  `rotation_probe_r24_r32_spot_tamper_refusal`,
  `rotation_probe_refuses_every_tampered_column_and_pi`,
  `rotation_caveat_probe_refuses_forged_domain_and_tampered_key`
- `effect_vm::bare_floor_refuse_weld::tests::deployed_cohort_bytes_carry_the_refuse`
- `effect_vm::carrier_floor_weld::tests::tag_cols_are_the_deployed_bound_columns`

Signature = GEOMETRY DRIFT, not a plain logic break:
`effect_vm/carrier_floor_weld.rs:349` asserts `left: 667 == right: 643` (column
count), and `bare_floor_refuse_weld.rs:651` reports cohort row
`…-deployed-bare-refuse has unexpected welded width 1668 (base 1623; expected
the standard 1647, distinct 1619, or avail-padded base)`. The refusal teeth key
off specific column indices/widths; the descriptor geometry moved under them.

Likely culprit (all TODAY, 2026-07-13): `919b2b0b8` "GAP #5 deployed IMT
rewiring (CORE: leaf arity-3 + absence pointer-bracket) — ★ insert two-path
(soundness-completer) STILL OWED", `2baaf0562` / `22a3d4f50` "HeapLeaf arity-3
downstream migration", `aa282f8c0` "AVAILABILITY WELD LIVE … 15-bit IR-2 range
tables … emission retargeted", `764225f0c` "producer-reconcile … regenerated
deployed descriptors".

Classification: NEW red from today's swarm, but a KNOWN-CLASS drift — the arity-3
migration's soundness-completer is self-labeled OWED, and `2f451a20c` ("refresh
the drifted PI-count guard 47→51") is active reconciliation of the same family.
Broader than the coordinator's single named `ir2_umem` test. Whether the
"accepted forgery" is a spurious tamper-lands-off-shifted-columns artifact or a
genuine open path is exactly what the geometry lane must resolve when it lands
the OWED completer. NOT thin-context-fixed here.

Also compile-broken (pre-existing, NOT today): 2 integration targets under
`circuit/tests/` (a note-spend full-width binding test and a garbled private
joint-settlement test, both since removed) imported
`dregg_circuit::dsl::{note_spending::prove_note_spend_dsl, garbled::prove_private_threshold_dsl, …}`
— symbols DELETED by `f04b2dd1e` "stark-kill" (2026-07-09). The failing lines
blame to before stark-kill and were never updated. Same stark-kill debt class as
the known items. (The lib + the other 65 integration targets compile clean.)

### FAIL #2 — Bridge: ETH calldata ground-truth fixture drift (TODAY)

`cargo test -p dregg-bridge --lib`: 295 pass / 1 fail —
`ethereum::tests::real_fixture_settle_calldata_matches_foundry_ground_truth`
(`bridge/src/ethereum.rs:1488`): `settle() calldata must be byte-identical to the
cast/Foundry encoding` — 32-byte hash mismatch (left `7f2dc8…` vs right
`45190c…`).

Likely culprit (all TODAY): `bridge/src/ethereum.rs` + the settlement circuit
were churned — `d62e5d333` "SHRINK SettlementCircuit 12.87M → 4.98M",
`151ba219e` "deploy the 4.98M shrunk circuit on-chain + trusted-setup PARAM
CACHE". The shrink/redeploy changed the proof/VK; the committed foundry
ground-truth fixture the Rust encoder is diffed against wasn't regenerated.

Classification: NEW red from today's circuit-shrink + VK-redeploy — VK/fixture
drift, adjacent to the coordinator's named `vk_epoch_misc` drift class. Owned by
the settlement/VK lane; the fixture needs regen. NOTE: the 3-chain
codegen-consistency gate (which checks the on-chain verifier + a real proof on
all three chains) PASSED — the on-chain path is consistent; only this Rust-side
foundry-encoding fixture drifted.

### FAIL #3 — Turn: nullifier_root_faithful_fill compile drift (TODAY) + stark debt (pre-existing)

`turn/tests/nullifier_root_faithful_fill.rs` fails to compile (6 errors):
`E0061` "this function takes 7 arguments but 6 arguments were supplied"
(`turn/src/rotation_witness.rs:376`) and `E0277` `[[u8; 32]]: Default` not
satisfied. Culprit: `4cb39210a` (TODAY) "circuit: unrot the setPerms/setVK weld
+ regen, and de-rot five registry drift teeth" added a 7th arg to the
rotation-witness fill fn; this test wasn't updated. NEW today-drift.

Separately, the `dregg-turn` lib-unit-test target (`turn/src/tests.rs`,
`turn/src/executor/membership_verifier.rs`) fails to compile: 14 errors,
unresolved `dregg_circuit::stark`, `effect_action_air::prove_effect_action`,
`predicate_air::{prove_in_range, prove_predicate}`, `TemporalPredicateProof` —
all DELETED by stark-kill (2026-07-09); the failing lines blame to the pre-
stark-kill base. PRE-EXISTING stark-kill debt (same class as the known items).

Production `dregg-turn` lib compiles, and all 37 turn integration targets that
compile PASS (running them with explicit `--test` flags sidesteps the broken
lib-unit-test) — the executor logic, including today's HeapLeaf arity-3
migration, is green.

### FAIL #4 — Rust workspace build: dregg-pay (uncommitted WIP, NOT a committed break)

`cargo build --workspace` reported exactly one error: `E0433 cannot find module
or crate curve25519_dalek` at `dregg-pay/src/nft_mint.rs:326`. Ground-truth:
`nft_mint.rs` is a BRAND-NEW file NOT in HEAD, and `dregg-pay/Cargo.toml` +
`lib.rs` are uncommitted-modified — an agent is mid-landing the NFT-mint feature
(the treasury/NFT lane, `f0d9a0efc` / roadmap `d94c55c00`). The warm-lane rsync
caught a transient state before the `curve25519-dalek` dep line was in place. A
targeted `cargo build -p dregg-pay` against the current tree finished GREEN.

Classification: NOT a committed regression — in-flight WIP snapshot on the shared
tree. At HEAD, dregg-pay has no such code and compiles. Every other workspace
crate compiled. (Note: the working tree is actively dirty — `Cargo.toml`,
`dregg-pay/*`, `intent/*`, sdk locks, a metatheory lean file — other lanes are
editing live; treat non-committed reds as swarm-in-flight.)

## What ran green (for the record)

- Lean `lake build Dregg2` (9637 jobs) + `lake build Market` (3064 jobs), local
  warm `.lake`, all keystones `#assert_all_clean` kernel-clean, 0 errors.
- `forge test` in `chain/`: 160 tests, 10 suites, 0 failed (settlement,
  launchpad, vault/escrow, upgradeable-VK registry, DVN, ISM, state-oracle,
  credential-gate, real-proof).
- `chain/codegen/check_consistency.sh`: 6/6 — one VK spec, three verifiers
  (EVM/Solana/Cosmos), the same real proof settles and rejects tampered on all.
- Escrow contracts: `solana-lock` 54 pass, `cosmos-lock` 12 pass.
- Turn executor integration: 37/37 pass.
- Circuit: lib 668/681 pass; 65/67 integration targets compile clean.
