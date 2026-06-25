# Codex — the height-1 FRI opening fix (2026-06-25)

The precise math for the IVC same-endpoint residual: a height-1 (base-domain-size-1) Poseidon2 table's nonzero FRI reduced-opening asserted-zero in the recursive aggregation verifier.

## The bug: zeta_next computed wrong for size-1 (NOT the zero-assertion)

For log_size==0: next_point(x)=x*subgroup_generator, generator=1 -> **zeta_next == zeta** (next row wraps to row 0, no distinct point). A height-1 column is degree-0, so p(zeta)==p(zeta_next)==p(x), every reduced-opening term is genuinely ZERO. The recursive verifier computes a DISTINCT zeta_next (from the LDE/extended generator, not the base trace generator) -> opens 'next' at a wrong point -> nonzero reduced opening -> assert-zero fails on the HONEST path. (Holds even with next_slice: 'next row' is semantic wraparound, not a 2nd polynomial point.)

## The fix (recursion/src/pcs/fri/verifier.rs open_input, base_domain_log_size==0)
```
if base_domain_log_size == 0 {
    zeta_next = zeta;                 // NOT the extended/LDE generator
    assert trace_next[j] == trace_local[j]  // every next-row-opened column
    // same for preprocessed/permutation next openings
}
```
Keep the native opening SHAPE (still open the 2nd slot) but at the SAME point with the SAME value. Do NOT relax reduced_opening==0 — the bug is reaching it with a non-native distinct zeta_next.

---

## UPDATE 2026-06-25 — the zeta_next hypothesis above is REFUTED by direct verification

Empirical investigation (Opus, fork-level reproducer + instrumented dregg `k_fold` runs) DISPROVES the "distinct zeta_next from the LDE generator" hypothesis:

- **`zeta_next` IS computed correctly for size-1.** `recursion/src/verifier/batch_stark.rs` (trace :909-917, preprocessed :1041-1049, permutation :1081-1089) computes `generator = trace_dom.next_point(first_point) * first_point.inverse()` using the **BASE** `trace_domains[i]`, NOT the extended/LDE domain. For a size-1 base coset `subgroup_generator()=two_adic_generator(0)=1`, so `generator=1` and `zeta_next = zeta*1 = zeta` (value-exact). This is byte-identical to native (`batch-stark/src/verifier/mod.rs:486`, `batch-stark/src/prover.rs:521`). Native verifies the same proof and PASSES.
- A **faithful fork reproducer** (`recursion/tests/height1_w24_aggregation.rs`, single- AND two-level) that aggregates a proof carrying a height-1 W24 `poseidon2_perm` table AND height-1 LogUp permutation instances opened at (zeta, zeta_next) **FOLDS + VERIFIES** — the reduced opening is correctly zero. So a height-1-with-next-row matrix is NOT inherently broken.

### What the dregg failure ACTUALLY is (instrumented `k_fold`, 3 runs)

Splitting the height-1 reduced-opening assert per-round (trace/quotient/preprocessed/permutation) and per-point pinpoints it:

1. The nonzero height-1 reduced opening comes from the **PERMUTATION (LogUp) round** (round 3), NOT trace/quotient/preprocessed. (Asserting only round-3's incremental contribution still fails; the others are individually zero.)
2. Per-point split: a single `(p_at_z - p_at_x)` term is genuinely nonzero (e.g. `[562760840, 44235848, 332774421, 929283905]`) for the height-1 permutation matrix. i.e. **the in-circuit opened value at the challenge point z DIFFERS from the MMCS leaf value at the query point x** for a matrix that is supposed to be degree-0 (height-1, so p_at_z must == p_at_x).
3. The instance genuinely has `degree_bits==0` (the circuit-prover derives degree_bits from the PADDED height — `batch_stark_prover.rs:1285` — so a min-height pad would give degree_bits>0 and NOT land in the height-1 group; min_trace_height for the recursion default packing is 1, so this permutation matrix really is 1-row).
4. **Native verification of the same proof passes** → this is a CIRCUIT-MODEL-vs-NATIVE divergence, NOT a prover/forgery issue and NOT the zero-assertion.

### Precise open hand-off (the next investigator's lead)

For a genuinely degree-0 (height-1) permutation matrix, `p_at_z != p_at_x` in the CIRCUIT only. Both `p_at_z` (prover's claimed opening, native-accepted) and the eval point `x`/`zeta_next`/`mat_domain` were verified to match native. The remaining suspect is the **in-circuit MMCS leaf opened value `p_at_x` (= `mat_opening` / `batch_opened_values`) for the height-1 permutation matrix** — i.e. how `verify_batch_circuit` assembles/orders the permutation-round leaf openings and how `open_input` (`verifier.rs:1185-1206`) zips `mat_opening` (p_at_x) with `mats` (p_at_z) per matrix when a size-1 permutation matrix shares the round with taller instances. A misaligned leaf slice (or a wrong leaf height/grouping for the size-1 permutation matrix inside the height-grouped Merkle verify) would yield `p_at_x != p_at_z` exactly here. Compare the recursive permutation-round leaf assembly against native `open_input`'s `batch_opening.opened_values.iter().zip(mats.iter())` for the size-1 instance. Do NOT re-pursue the zeta_next fix — it is refuted.
