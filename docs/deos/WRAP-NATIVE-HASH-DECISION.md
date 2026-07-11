# The wrap must hash BN254-native, not emulate BabyBear (measured decision)

*2026-07-11. A panel of three cryptoarchitect research agents + a red-teaming
synthesis, prompted by ember's question "are we sure this is as efficient as
possible?" Verdict: **our current gnark wrap is on the expensive emulated path;
the fix is the production-standard BN254-native-hash outer layer. High confidence,
production-anchored, measured.** Corrects the efficiency assumption in
`ETH-NATIVE-WRAP.md`.*

## The problem (measured, not assumed)

dregg's proof is BabyBear (31-bit) + Poseidon2. The gnark wrap circuit (BN254)
verifies it — but BabyBear does not fit BN254 natively, so every BabyBear op is a
BN254 mul + range checks. **Measured in our own `chain/gnark` today:**

- emulated BabyBear Poseidon2-w16 = **16,837 R1CS/permutation**
- emulated BabyBear Poseidon2-w24 = **27,213 R1CS/permutation**

A FRI verifier is **hash-dominated**: ~19 queries × (~24-deep input Merkle path +
~7 FRI-round paths) × several tables + the NPO Poseidon2 tables ≈ **~1,000–3,000
permutations**. At ~16.8k each that is **~20–70M constraints for hashing alone** →
a GPU-class Groth16 prove (SRS 2²⁵+, tens of GB, minutes-to-tens-of-minutes) —
**no better than the SP1 RISC-V path we are replacing.** The SP1 slowness was the
*same emulation tax*; a naive gnark FRI verifier just relocates it from RISC-V
cycles to BabyBear-in-BN254 field emulation.

## The fix (what RISC0 and SP1 both actually do)

Insert **one BN254-native-hash outer "shrink" recursion layer** between the apex
and gnark — the analogue of **RISC0's `identity_p254`** and **SP1's `shrink`
stage**. It re-verifies the current `ir2_leaf_wrap` apex and **re-commits its FRI
Merkle tree with Poseidon2-over-the-BN254-scalar-field**, with Fiat–Shamir over a
`MultiField32Challenger` (pack BabyBear→BN254 on absorb, split BN254→BabyBear limbs
on squeeze). Trace/quotient arithmetic stays over BabyBear; **only the hash field
switches.** The gnark verifier then hashes **natively**.

- RISC0 docs, verbatim: *"In Groth16 over BN254, it is much more efficient to
  verify a STARK that was produced with Poseidon over the BN254 base field
  compared to using Poseidon over BabyBear."* Their production `stark_verify.circom`
  (native Poseidon254) = **5,676,573 R1CS** (SRS 2²³) — the real size of a
  native-hash STARK→SNARK wrap, i.e. ~5.7M, not tens of millions.
- SP1 does the identical thing (`crates/recursion/circuit/src/hash.rs` +
  `challenger.rs`: inner layers over SP1Field, the **outer/wrap layer switches to
  `outer_perm` = Poseidon2 over Bn254Fr** with a `MultiField32ChallengerVariable`).
- Counter-example (the expensive path we're on): Polygon plonky2→gnark keeps
  Goldilocks-Poseidon, ~75% of the circuit is emulated hashing.

## The number (measured, this is the whole point)

| | per Merkle compress | full wrap (hashing) | Groth16 |
|---|---|---|---|
| **Emulated BabyBear** (current) | 16,837 R1CS (w16), 27,213 (w24) | ~20–70M R1CS | GPU, tens of GB, minutes+ |
| **Native BN254 Poseidon2** (fix) | **187 R1CS** (measured, gnark std) | ~1–6M R1CS | CPU/modest-GPU, seconds–~2min |

**Swing on the dominant term: 90–145×.** Destination anchored to RISC0's real
5.68M-constraint native wrap.

## We already have the primitives (this is instantiation, not new crypto)

dregg's pinned Plonky3 checkout (`82cfad7`) **already ships everything**:
`bn254/src/poseidon2.rs::Poseidon2Bn254<3>` (t=3, α=5, 8 full + 56 partial),
`challenger/src/multi_field_challenger.rs::MultiField32Challenger`, the merkle-tree
MMCS. The recursion verifier is **field-generic** (`recursion/src/backend/fri.rs`:
`Val<SC>: PrimeField64`, not BabyBear-hardcoded). The gap is only that
`DreggRecursionConfig` hard-codes BabyBear Poseidon2 and there is **no outer BN254
config** — and `ETH-NATIVE-WRAP.md` planned the gnark circuit around BabyBear
gadgets (the emulated path).

## What we keep vs. redo

- **KEEP:** the plonky3-recursion BabyBear IVC (folding / `expose_claim` / VK-pin),
  the Groth16 EVM verifier + `IDreggSettlement.sol` + `bridge/src/ethereum.rs`
  (unchanged), the FRI verify **structure** in `chain/gnark` (`VerifyFri`, the fold
  logic, grinding, the query walk — the *algorithm* is unchanged), and `babybear.go`
  (still needed for the outer AIR's quotient-eval arithmetic).
- **REDO:** `chain/gnark`'s **hash + challenger** gadgets — `poseidon2_w16.go` /
  `poseidon2_w24.go` for *Merkle hashing* and `challenger.go` switch from emulated
  BabyBear Poseidon2 to **native `Poseidon2Bn254`**; regenerate transcript fixtures
  against the MultiField sponge. The emulated w16/w24 gadgets survive ONLY for the
  small BabyBear quotient-eval arithmetic, not for hashing. So the challenger /
  grinding / FRI-query / VerifyFri **work is not wasted** — the structure carries;
  the hash primitive underneath swaps.

## Red-team (the one place it could underperform)

The outer shrink layer's *prover* cost: Poseidon2-over-BN254 is a big-field hash,
slower per node than BabyBear. Rebuttal: the shrink trace is **tiny** (re-verify
ONE apex, re-expose 25 lanes), bounded, paid once off-chain, and dwarfed by the
gnark Groth16 prove it saves — RISC0/SP1 eat exactly this and land at seconds. It
**holds, but must be measured**, and the single risk is if dregg's apex has an
unusually large opening/public-value surface making the shrink trace big.

## Validate before re-architecting (the disciplined path)

Do NOT rip out gadgets yet. Two cheap experiments settle dregg's real numbers:

1. **Count the real perms** (~½ day): instrument the Rust apex verifier (the FRI
   Merkle-path walks at `ir2_leaf_wrap_config`) with a Poseidon2-permutation counter
   → the true current-path total (is it ~800 or ~3,000 perms?).
2. **Minimal native-hash FRI verify in gnark** (~1–2 days): build N native-BN254-
   Poseidon2 Merkle openings at the real ir2 depth/query count, compile, count → the
   real end-to-end constraint number, confirming ~1–6M before committing.

Then: prototype the Rust shrink layer (`DreggOuterConfig` = `Poseidon2Bn254` MMCS +
`MultiField32Challenger`), a bit-exact Rust↔gnark transcript differential
(TWO-GATES-PROVABLY-AGREE), and plan the Groth16 SRS for the ~1–6M circuit
(Perpetual Powers of Tau 2²³ covers it) before regenerating the settlement verifier.
Resolve the gnark version gap: dregg is on gnark v0.11.0 (no native Poseidon2 std);
bump to v0.15+ (ships `std/permutation/poseidon2`, 187 R1CS measured) or hand-roll a
~187-constraint native BN254 Poseidon2.
