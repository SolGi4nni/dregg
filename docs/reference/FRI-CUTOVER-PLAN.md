# FRI-CUTOVER-PLAN — cutting the deployed proof system to the proven-120 configuration

**Target:** `d = 8, lb = 6, q = 36, pow = 16, WRAP_LOG_CEIL = 15` — **λ = 122.60 on every shipped
config** (2.6 bits of margin), per [`PROVEN-120-CONFIG.md`](./PROVEN-120-CONFIG.md) §3.4/§6. The
deployed posture is `d = 4` at the apex: **51 proven commit bits** at `|D⁰| = 2^22`
(`FriDeployedHeightPairing.deployed_wrap_commitBits`; the `57` once quoted at ibid. §2–3.1 is the `m=3`
best-case ceiling / a `2^19`-mispairing, refuted as the deployed number by
`deployed_wrap_is_not_the_proven120_number`). This document is the
operator checklist for the cutover: the file-and-site inventory (counted, not inherited), the ordered
steps, the gates at each step, the cost expectations and how to re-measure them, the rollback story,
and what does not change.

**Companions:** [`PROVEN-120-CONFIG.md`](./PROVEN-120-CONFIG.md) (the design and every number),
[`FRI-BOTH-WIN-LEVERS.md`](./FRI-BOTH-WIN-LEVERS.md) (the lever map), `docs/VK-REGEN-LOG.md` (the
re-key audit trail this cutover appends to).

**Scale of the work:** the field layer is free (`BinomialExtensionField<BabyBear, 8>` ships in the
pinned plonky3 — no fork, `W` stays 11, two-adicity gains a bit). The tail is the gnark wrap
(2–4 weeks) plus Groth16 re-setup and a full VK re-key. PROVEN-120 §6 scopes the whole cutover at
**4–8 weeks**, dominated by the wrap. Nothing in Phase 3+ starts until the two Phase-1
measurements report (§2, gate G1).

---

## 1. Site inventory — counted from the tree, 2026-07-16

Both predecessor figures are off: `FRI-BOTH-WIN-LEVERS.md` §3.6's "~16 gnark files / 136 `BBExt`
sites" over-counts by including test files; `PROVEN-120-CONFIG.md` §6's "85 `[4]`/`BBExt{…}` literal
sites across 10 Go files" under-counts by missing the challenger/ref twins, the FRI leaf-hash
packing, and the 16 bound-constant call sites. The counts below are from the tree at the date above;
each row carries its reproduction command.

### 1.1 `chain/gnark/` — non-test Go files: **~119 degree-coupled lines across 14 files**

Broad sweep (117 raw hits, 15 poseidon2/PCS-round false positives excluded, +16 bound-call sites and
+1 comment site the sweep misses):

```
cd chain/gnark
grep -nE '\[4\]|BBExt\{|bbExtRef\{|i < 4|j < 4|k < 4|4\*c|big\.NewInt\(4\)|, 4,|!= 4\b|4 \* sh\.|X\^4|p\^4|degree-4|four base' *.go | grep -v '_test.go'
grep -nE 'ReduceBounded\((c[0-3]|acc\[[0-3]\]|accX\[[0-3]\]|api\.Add\(c\[)' *.go | grep -v _test
```

**False positives to leave alone** (round counts and PCS structure, not extension degree):
`poseidon2_w16.go` / `poseidon2_w24.go` / `poseidon2_bn254_constants.go` `[4][W]` external-round
arrays and the `sums [4]` M4 block kernels; `settlement_circuit.go:146 inputRootDigOff [4]int`
(4 PCS rounds: trace/quotient/preprocessed/permutation).

The real sites, grouped by the unit of work:

| # | work unit | files : anchors | lines |
|---|---|---|---:|
| W1 | **Type-level arity** — `type BBExt [4]frontend.Variable`, `type bbExtRef [4]uint32` | `babybear_ext.go:23`, `babybear_ext_ref.go:7` | 2 |
| W2 | **Unrolled schoolbook kernels** (4 of them, not 3): `ExtMul` (`babybear_ext.go:57-84`), `extMulRawInto` (`stark_open_input.go:201-217`), `ExtFromBasisCoefficients` (`stark_verify_native.go:181-202`), host twin `bbExtMulRef` (`babybear_ext_ref.go:25-44`) | as listed | ~30 |
| W3 | **Bound constants that fail silently** — `ReduceBounded(·,68)` ×4 (`babybear_ext.go:80-83`), `(·,77)` ×4 (`stark_open_input.go:292-295`), `(·,71)` ×4 (`stark_open_input.go:461-464`), `(·,37)` ×4 (`stark_verify_native.go:197-200`) + their derivation comments | as listed | 16+ |
| W4 | **ExtInv** — Fermat exponent `p^4−2` (`stark_verify_native_ref.go:42-58`), hint arity 4 + `len(inputs) != 4` (`stark_verify_native.go:118-155`) | as listed | ~8 |
| W5 | **Challenger ext sampling** — `SampleExt`/`ObserveExt` loop `range e` (d-generic; comments pin 4): `challenger.go:76-107`, `multifield_challenger.go:229,327`, `challenger_ref.go:25,84-85`, `fri_verify_native_ref.go:44` | as listed | ~7 |
| W6 | **FRI leaf-hash packing — STRUCTURAL**: 2 ext evals = 8 base coords = exactly one rate-8 block of the W16 sponge (`fri_query.go:150-170`, `fri_verify_native.go:205-230`). At d=8 that is 16 coords = **two rate-8 blocks = one extra Poseidon2W16 permutation per commit-phase leaf, per query, per round** — a real R1CS cost the ~7.5–12M estimate must absorb, and a transcript-shape change (KAT `fri_leaf_hash_kat_test.go` re-pins) | as listed | ~10 |
| W7 | **Quotient recomposition** — chunk width = D: `OpenInputMatrixShape{lh, 4, 1, 0}` (`stark_open_input.go:119`), `chunks [][4]BBExt` + `flat[4*c : 4*c+4]` (`stark_verify_native.go:399,572,623`; ref `:88,183,235`) | as listed | ~10 |
| W8 | **LogUp permutation width = D per lookup**: `4 * sh.NumLookups` (`stark_open_input.go:129`, `stark_verify_native.go:291-292`, comment `settlement_circuit.go:141`) | as listed | 4 |
| W9 | **Constraint-interp bytecode carries D**: opcode `ec(v: [4]u32)` (`stark_constraint_interp.go:36,151-157`) plus its `BBExt{v[0..3]}` decode sites (`:181,237,243,273,329`) — the serialized symbolic-constraint format itself changes; fixture `fixtures/shrink_symbolic_constraints.json` regenerates | as listed | ~9 |
| W10 | **`BBExt{…}`/`bbExtRef{…}` 4-element literals** everywhere else (zeros, ones, `{v,0,0,0}` embeddings) — mechanical | `stark_verify_native.go` (11), `stark_verify_native_ref.go` (14), `stark_open_input.go` (9), `stark_constraint_interp.go` (7), `stark_open_input_ref.go` (1), `babybear_ext.go` (2) | ~44 |
| W11 | **Per-coord loops** `i < 4` in fold/select paths | `fri_query.go:100,159`, `fri_verify_native.go:215`, kernels above | ~6 |

What does **not** change in the wrap: `W = BBExtW = 11` (d=8 keeps `X⁸ − 11`); the arity-2 fold
count `R = log₂|D⁰| − lb = log₂T = 15` (lb rises 3 → 6 with the domain, PROVEN-120 §4.2); digest
widths (8 BabyBear inner, 1 BN254 outer); all Poseidon2 permutations; the Groth16 curve and the
26 public inputs (VK stays 2,576 B).

### 1.2 `chain/gnark/` — test files and fixtures (re-pin, don't port blindly)

~45 genuine degree-coupled lines across 11 test files (`babybear_ext_test.go` 11,
`stark_algebra_real_fixture_test.go` 9, `apex_shrink_real_fixture_test.go` 8,
`fri_leaf_hash_kat_test.go` 4, `fri_query_test.go` / `fri_verify_test.go` /
`fri_verify_native_test.go` 3 each, others 1–2). Fixtures that regenerate from the Rust side:
`fixtures/apex_shrink_fri_real.json`, `apex_vk_identity.json`, `shrink_symbolic_constraints.json`,
`gnark_witness_minimal.json`, `settlement_groth16.vk`. (`transcript_w16.json` is base-field; check
rather than assume it survives.)

### 1.3 Rust — the degree knobs

- **25 literal `const D: usize = 4` hits across 24 files** (20 `circuit-prove/src` — 13 leaf
  adapters, 2 clearing AIRs, `apex_shrink.rs`, `apex_shrink_gnark_export.rs`, `accumulator.rs`,
  `ivc_turn_chain.rs`, `joint_turn_recursive.rs`, `gpu_backend.rs` — and 4 tests:
  `descriptor_leaf_recursion.rs`, `ivc_turn_chain_rotated.rs`, `apex_shrink_trace_anatomy.rs`,
  `gpu_recursion_fold_e2e.rs`). Reproduce: `grep -rn 'const D: usize = 4' circuit-prove/`.
- **The named knobs — five, not two**: `circuit/src/plonky3_prover.rs:106` `PROD_EXT_DEGREE = 4`
  (the root; `circuit/src/descriptor_ir2.rs:5460` `IR2_EXT_DEGREE` derives from it),
  `circuit/src/stark_zk.rs:70` `ZK_EXT_DEGREE = 4`, `dregg_outer_config.rs:125`
  `OUTER_EXT_DEGREE = 4`, `plonky3_recursion_impl.rs:90` `RECURSION_EXT_DEGREE = 4`.
  (`dregg_outer_config.rs:120` already keys its local `D` off the named knob — the model the
  25 literal sites should follow.)
- **The recursion fork needs an `8 =>` arm**: `p3-recursion` is pinned to
  `emberian/plonky3-recursion` rev `0a4a554` (`Cargo.toml:236` — already ours, an edit not a fork);
  `recursion/src/backend/fri.rs:405-489` matches `proof.ext_degree` over `1 | 2 | 4 | 5`, ~20
  monomorphized lines per PROVEN-120 §6. Challenger routes through the base-field
  `BABY_BEAR_D1_W16` per the d=5 precedent (no `BABY_BEAR_D8_W16` Poseidon2 config exists).
- **FRI shape/config sites** (the authoritative enumeration is
  `fri_params_soundness_budget.rs::shipped()`, all 7 configs × 6 knobs):
  `dregg_outer_config.rs:378-430` (outer: lb 3, q 38, pow 16 → lb 6, q 36),
  `circuit/src/descriptor_ir2.rs:5423` `ir2_config` (lb 6, q 19 → q 36) with its
  `IR2_INNER_*` mirror consts at `ivc_turn_chain.rs:869-872`, the recursion consts in
  `plonky3_recursion_impl.rs` (`RECURSION_FRI_LOG_BLOWUP` 3 → 6, `…NUM_QUERIES` 38 → 36,
  `…QUERY_POW_BITS` 14 → 16 — the AIR's degree-7 S-box needs lb ≥ 3, which 6 satisfies),
  `prodV1Config`/`zkConfig` via `plonky3_prover.rs`/`stark_zk.rs` (lb 3 → 6, q 38 → 36), and
  `WRAP_LOG_CEIL` 16 → 15 (`accumulator.rs:236`, applied as `with_min_trace_height` at `:247`).
- **VK anchor — a Rust/Go pinned pair**: `apex_shrink_gnark_export.rs:219-220`
  `DREGG_APEX_RECURSION_VK` (blake3-32 of the apex `RecursionVk`, enforced fail-closed by
  `check_apex_vk_identity_pin`) mirrored by `chain/gnark/settlement_circuit.go:122`
  `DreggApexRecursionVk` (enforced by `loadApexVkIdentity`). Deployed value `3ad1c9c6…5503`;
  both re-key together, in one commit.

### 1.4 Lean — one pin flips, the ledger machinery does not

`metatheory/Dregg2/Circuit/ExtFieldChallenge.lean:218`
`theorem deployed_extDeg_four : ir2LeafWrapConfig.extDeg = 4 := rfl` — self-catching by design; it
goes red the moment the Rust-mirrored config changes and gets re-stated at 8. The
`FriLedger.lean` / `FriLedgerSound.lean` machinery is parametric and untouched (§6 below);
what does update in `FriLedgerSound.lean` is bookkeeping: the five deployed-config mirror
literals carrying `extDeg := 4` (+ per-config lb/q/pow, at `:237,249,259,265,279`) and the dated
numeric rows they feed (§3).

### 1.5 Consumers of the VK

`chain/contracts/DreggGroth16Verifier25.sol` and `DreggGroth16VerifierUpgradeable.sol` (+ built
copies under `chain/out/` and the generated `chain/codegen/out/DreggGroth16Verifier25.vk.sol`),
the pinned Rust/Go fingerprint pair (§1.3), `chain/gnark/fixtures/settlement_groth16.vk` and
`fixtures/apex_vk_identity.json`, and any node/light-client config that carries the apex VK hash.
All re-key in Phase 4.

---

## 2. The ordered cutover

Phases are sequential; each has a gate. **G1 is the go/no-go: Phase 3 onward does not start until
G1 passes.**

### Phase 0 — pre-work (free, correct today, independent of the degree decision)

These are PROVEN-120 §6 steps 1–3; they stand alone.

- [ ] **0.1** `WRAP_LOG_CEIL` 16 → 15 (`accumulator.rs:236`). Buys +2 proven bits at d=4 (57 → 59)
      and ~2× less apex prover work. Gate: `wrapped_running_vk_is_constant_across_depth`
      (`circuit-prove/tests/accumulator.rs:561`, the depth-invariance test) stays green.
      ⚠ **Free in bits and prover time, NOT free of re-key ceremony**: the floored `degree_bits`
      go 16 → 15, so the running-VK fingerprint changes (it hashes `degree_bits`), the pinned
      `DREGG_APEX_RECURSION_VK`/`DreggApexRecursionVk` pair re-derives, the apex fixtures
      regenerate, and the gnark fold depth over the inner shape shortens by one Merkle level.
      Depth-INVARIANCE is preserved; the fingerprint VALUE is not. If the d=8 cutover is
      proceeding, land 0.1's knob with Phase 2 and pay the re-key once in Phase 4; land it
      standalone (with its own mini Phase-4 re-key + VK-REGEN-LOG row) only if the cutover is
      deferred.
- [ ] **0.2** Correct the three wrong artifacts (PROVEN-120 §2): `FriLedgerSound.lean:692` row 4
      (lb-3/height mispairing), `fri_trace_height_measure.rs:133` `DEPLOYED_WORST_LOG_D0` (+ its
      `:293-299` assert), the stale comment `plonky3_recursion_impl.rs:385-392`. Add the missing
      `ir2LeafWrapRotatedConfig` rows at recursion heights.
- [ ] **0.3** Fix the two stale `ReduceBounded` bound comments that are wrong at d=4 **today**:
      `babybear.go:11-12` ("qBits ≤ 38") and `:84-85` ("< 2^68"; the widest accumulation is 2^77 at
      `stark_open_input.go:292`). These are soundness constants that fail silently.
- [ ] **0.4** Put a **golden absolute R1CS count** on `settlement_profile_test.go` (today it
      compares twin-vs-real only, `:209-214`; a 2× regression passes silently) and update
      `chain/gnark/README.md:42`'s stale "~12.2M". gnark does not run in CI
      (`.github/workflows/armed-teeth.yml`) — the golden count is the only tripwire the degree work
      lands inside.

**Gate G0:** `cargo test -p circuit-prove --test fri_trace_height_measure`,
`lake env lean metatheory/Dregg2/Circuit/FriLedgerSound.lean`, `go test ./...` in `chain/gnark`
(fast tier), all green. If 0.1 lands standalone, its mini re-key (see the 0.1 warning) is part of
G0 — the depth-invariance test proves constancy across depth at the new shape, and the natural
max staying ≤ 2^15 (`accumulator.rs:225-227`, measured at depths 2 and 3) is the assumption it
checks.

### Phase 1 — the deciding measurements (two lanes, before any rewrite)

- [ ] **1.1** Parameterize `BBExt` by a degree constant; run `TestSettlementGadgetMarginalCosts`
      (`settlement_profile_test.go:396-412`, reproduces the measured 92 R1CS/ExtMul at d=4) at
      d=8, plus a phase-stripped whole-circuit compile at `(d=8, lb=6, q=36)`. **This replaces the
      one ESTIMATED gate number — Groth16 setup memory (~15–25 GB est.) — with a measurement.**
- [ ] **1.2** Measure the outer `lb` 3 → 6 prover cost (outer LDE domain 2^18 → 2^21; 8× the outer
      shrink's base-field FFT/Merkle work). The one cost this design introduces that is unpriced.

**Gate G1 (go/no-go):** measured setup peak fits the build box with margin (hbox under
`swarm-build`, `MemoryMax=96G`); measured outer-shrink prove time is acceptable on the apex path.
If either fails, stop — the fallback posture is Phase 0's 59 bits plus the BCSS25 mechanization
route (PROVEN-120 §7), not a partial rewrite.

### Phase 2 — Rust degree flip (mechanical, ~2–3 days)

- [ ] **2.1** Land the `8 =>` arm + challenger route in `emberian/plonky3-recursion`; bump the
      `Cargo.toml:236` rev pin.
- [ ] **2.2** Re-key the 25 `const D` sites to the two named knobs (follow
      `dregg_outer_config.rs:120`'s pattern), then flip `OUTER_EXT_DEGREE` / `RECURSION_EXT_DEGREE`
      4 → 8. GPU site `gpu_backend.rs` included; GPU path is unmeasured at d=8 — expect to re-tune.
- [ ] **2.3** Flip FRI configs: all six shipped configs to `lb=6, q=36, pow=16`
      (v1/zk/outer/recursion rise lb 3 → 6; leaf/wrap rise q 19 → 36).
- [ ] **2.4** Re-state `deployed_extDeg_four` → `deployed_extDeg_eight` (Lean goes red at 2.3's
      mirror; that red is the gate working).

**Gate G2:** `cargo test -p circuit-prove --test fri_params_soundness_budget` (re-pinned, §3),
`--test ext_degree_cost_measure`, `--test descriptor_leaf_recursion`; one leaf→fold→apex prove
e2e (`--test ivc_turn_chain_rotated`); `lake env lean …/ExtFieldChallenge.lean`. Rust-side proofs
verify at d=8 end to end **before** the wrap is touched (the wrap still verifies d=4 fixtures until
Phase 3 — the two sides are decoupled by fixtures, which is what makes this ordering safe).

### Phase 3 — the gnark wrap rewrite (the tail: 2–4 weeks)

Work units W1–W11 from §1.1, in dependency order:

- [ ] **3.1** W1 type arity `[4]` → `[8]` (or degree-parameterized from 1.1's work), W2 kernels
      re-unrolled (`X⁸ = 11` wraparound), W4 `ExtInv` exponent `p^8 − 2` + hint arity 8.
- [ ] **3.2** W3 bounds **recomputed, not guessed**: `boundBits(d) = 62 + ⌈log₂(1 + W·(d−1))⌉`
      (reproduces the deployed 68 at d=4). At d=8: `extMulRawInto` 69, `S_z` 78, `S_x` 71,
      `ExtFromBasis` 38 (PROVEN-120 §4.2). Every `ReduceBounded` call site gets its derivation
      comment updated in the same edit.
- [ ] **3.3** W6 leaf-hash: two-block sponge for 16 coords; re-pin `fri_leaf_hash_kat_test.go`
      against a plonky3-side KAT (ground truth first — generate the KAT from the Rust prover, then
      make gnark match it, never gnark-vs-gnark).
- [ ] **3.4** W7 quotient chunk width, W8 perm widths, W9 interp opcode `ec(v:[8]u32)` + bytecode
      version bump, W5 comments, W10/W11 mechanical literals.
- [ ] **3.5** Ref twins (`*_ref.go`) in lockstep — the differential tests are the verification
      spine; regenerate all `fixtures/*.json` from the Phase-2 Rust prover.

**Gate G3:** full `go test ./...` in `chain/gnark` including env-gated heavy tests; golden R1CS
count updated deliberately (record the measured number); a **real** d=8 apex-shrink proof from
circuit-prove verifies inside the gnark circuit (`apex_shrink_real_fixture_test.go` regenerated) —
not a synthetic witness.

### Phase 4 — config/descriptor regen + VK re-key

- [ ] **4.1** Groth16 setup at the new circuit (on hbox: `swarm-build`, measured peak from G1
      bounds it). Cache per `groth16_cache.go`; keep the **old** VK artifacts in place untouched.
- [ ] **4.2** Re-key the anchor pair in one commit: run
      `derive_deployed_apex_vk_identity_and_check_fixture`, then update
      `DREGG_APEX_RECURSION_VK` (`apex_shrink_gnark_export.rs:219-220`) **and**
      `DreggApexRecursionVk` (`settlement_circuit.go:122`) **and**
      `fixtures/apex_vk_identity.json`; regenerate `DreggGroth16Verifier25.sol` /
      `…Upgradeable.sol` / `codegen/out/…vk.sol` and `settlement_groth16.vk`. Negative check:
      `check_apex_vk_identity_pin` / `loadApexVkIdentity` REJECT the old artifact after the
      re-pin (fail-closed both directions).
- [ ] **4.3** Descriptor provenance: leaf AIR descriptors do not change shape (the degree is a
      config knob, not an AIR column), so this is `stamp-existing` unless a descriptor diff proves
      otherwise; either way the run goes through `scripts/emit_descriptors.py` so it **appends the
      VK-REGEN-LOG row** — the entry format (from `docs/VK-REGEN-LOG.md`, append-only, never edit
      rows; git history is the tamper-evidence):

      `| <when UTC> | <operator> | emit\|stamp-existing | <HEAD:metatheory/Dregg2> | <repo HEAD> | YES\|no | <changed files> |`

      Do the re-key from a **clean** tree so `source dirty` reads `no` for the flip row.

**Gate G4:** VK-REGEN-LOG row appended; new VK fingerprint check-fails against a doctored identity
(the self-binding check in `apex_shrink_gnark_export.rs` is the test); Solidity verifier compiles
and verifies a fresh d=8 settlement proof.

### Phase 5 — apex re-verify + flip

- [ ] **5.1** Full-chain re-verify on real artifacts: leaf prove → rotated aggregation → apex fold
      → apex shrink → gnark wrap → Groth16 verify → Solidity verify, at the target config,
      including the depth-invariance test at the new `WRAP_LOG_CEIL = 15`.
- [ ] **5.2** Record measured numbers (prover Δ, proof size, R1CS, setup peak, wrap prove time) next
      to PROVEN-120's expectations (§4 below); investigate any expectation missed by >10% before
      flipping, per MEASURE-BEFORE-BELIEVING.
- [ ] **5.3** Flip deployed consumers (node config VK hash, contract address/upgrade, light-client
      pins) in one commit; ember-gated — deployment flips are not lane-autonomous.

**Gate G5:** an end-to-end turn on the devnet path settles under the new VK; the old-VK proof is
**rejected** by the new verifier and vice versa (the negative test proves the re-key actually
re-keyed).

---

## 3. Which existing tests pin the OLD config (expect these red, re-pin deliberately)

| test | pins | phase it re-pins |
|---|---|---|
| `circuit-prove/tests/fri_params_soundness_budget.rs` | THE PIN — all 7 configs × 6 knobs incl. `ext_deg: 4`, `lb 6/q 19/pow 16`, `lb 3/q 38/pow 16` literals (`:331-392`) | 2.3 |
| `metatheory/…/ExtFieldChallenge.lean:218` `deployed_extDeg_four` | `extDeg = 4` by `rfl` | 2.4 |
| `circuit-prove/tests/fri_trace_height_measure.rs` | `DEPLOYED_WORST_LOG_D0` + height asserts | 0.2, then 2.3 |
| `circuit-prove/tests/ext_degree_cost_measure.rs` | measured d=4 baseline rows | 2 (gains a d=8 row; keep the d=4 row as history) |
| `chain/gnark/fri_leaf_hash_kat_test.go` + `fixtures/*.json` + `babybear_ext_test.go` KATs | d=4 transcripts, proofs, kernels | 3.3/3.5 |
| `chain/gnark/settlement_profile_test.go` golden R1CS (added in 0.4) | d=4 circuit size | 3 (G3, deliberate update) |
| `FriLedgerSound.lean` pinned numeric rows (`:647,657,692,714`) | d=4 config numbers | 0.2 corrects row 4; Phase 2 **adds** target-config rows, keeps d=4 rows as historical statements (they remain true theorems about that config) |

A red in any of these outside its scheduled phase is a stop signal, not noise.

## 4. Cost expectations (and how to re-measure)

| quantity | expectation | label | re-measure with |
|---|---|---|---|
| prover time | **+25%** vs d=4 | MEASURED (proxy AIR; plausibly higher with LogUp EF fractions — PROVEN-120 §7) | `cargo test -p circuit-prove --test ext_degree_cost_measure` (min-of-3, width 128) |
| proof size | **+20%**; apex ~120 → **252 KiB** | MEASURED d-scaling × fitted model | same harness; fitted model `20561 + q·(3971 + 239·lb)` |
| verify time | +0.5–0.9 ms | MEASURED | same harness |
| VK size | **unchanged**, 2,576 B | MEASURED (d-independent) | gnark export |
| wrap R1CS | ~7.5–12M (vs 4.98M measured at d=4) | **ESTIMATED — the gate** | Phase 1.1: `TestSettlementGadgetMarginalCosts` at d=8 + phase-stripped compile |
| Groth16 setup peak | ~15–25 GB (23 GB / 13m11s measured at 12.2M R1CS) | **ESTIMATED — the gate** | Phase 1.1 compile + a setup run under `swarm-build` with RSS logging |
| outer shrink prove (lb 3→6) | 8× the outer LDE base-field work | **UNMEASURED** | Phase 1.2 |
| GPU prover at d=8 | unknown | UNMEASURED | after 2.2, the GPU e2e test |
| wrap query loop | **0.95×** today's (36 queries vs 38) — the lb 3→6 knob is what keeps the wrap affordable | DERIVED | falls out of G3's golden count |

## 5. Rollback

Every step is a normal commit on main and every generated artifact is regenerable, so rollback is
`git revert` of the phase's named commits — with three specifics:

1. **The old VK is never deleted.** Phase 4 writes new artifacts beside the old ones; the flip
   (5.3) is one commit re-pointing consumers. Rollback of the flip = revert that one commit; the
   old Groth16 VK, Solidity verifier, and fixtures are still in tree and still pass their (old)
   tests at that revision.
2. **VK-REGEN-LOG is append-only.** A rollback appends a new row (the reverting regen/stamp); it
   never edits or removes the cutover's row. The log records the round-trip.
3. **Fixtures re-cut both ways.** `chain/gnark/fixtures/*` regenerate from whichever Rust prover
   revision is checked out, so a reverted tree is self-consistent after one fixture-regen run.
   Until Phase 3 lands, the wrap continues to verify d=4 artifacts — Phases 0–2 are independently
   revertable without touching the wrap at all.

The Groth16 setup output (multi-GB) is cached outside git (`groth16_cache.go` keying); keep the
d=4 cache entry until G5 has held on devnet for an agreed soak.

## 6. What does NOT change

- **The Lean ledger machinery.** `FriLedger.friCommitLedger` is parametric in every knob; the
  target-config numbers in PROVEN-120 §3.4 (λ = 122.60 on all six configs, ceilings 183–201) are
  computed by an exact transcription of it, validated against **all 14** numbers
  `FriLedgerSound.lean` proves (PROVEN-120 header + Provenance row 1;
  `FriLedger.lean:322-339`, `FriLedgerSound.lean:647,657,692,714`). The structural theorems —
  `query_ledger_does_not_determine_perFold`, `query_and_pow_cannot_pass_epsC` — are
  config-independent and already cover the target. New pinned rows at
  `(d=8, lb=6, q=36, pow=16)` get **added**; no proof is rewritten.
- **No plonky3 fork.** `BinomialExtensionField<BabyBear, 8>` and `octic_mul_packed` ship in the
  pinned upstream rev; only our already-owned `emberian/plonky3-recursion` gains an arm.
- **`W = 11`** (`X⁸ − 11`), so the wrap's wraparound constant, `BBExtW`, and every W-coupled
  derivation keep their constant — only the arity changes. Two-adicity improves 29 → 30.
- **The gnark fold structure**: `R = log₂|D⁰| − lb = log₂T = 15` at both the old (lb 3, 2^18) and
  new (lb 6, 2^21) outer shape — the circuit's loop structure is unchanged; only the d² arithmetic
  and the leaf-hash block count grow.
- **All Poseidon2 hashing** (W16/W24 inner, BN254 outer), digest widths, the Groth16 curve, the 26
  public inputs, and the VK size.
- **`pow = 16`** — no grind escalation (the practical cap is 27 and "grinding is nearly free" is
  twice-refuted; PROVEN-120 §3.4).
- **The verification-mode lattice and everything above the proof system** — turn semantics,
  receipts, descriptors' AIR shapes, the settlement boundary's meaning. This cutover changes how
  strong the proof is, not what it says.
