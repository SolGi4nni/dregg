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

---

## UPDATE 2026-06-25 (#2) — empirical witness-provenance trace (Opus): ext/base contamination REFUTED; it is a height-1 reduced-opening ARITHMETIC/GROUPING divergence

Method: instrumented `p3-circuit` `set_witness` (conflict-time dump of every `DBG`-tagged
slot + its first-writer op) and tagged, in `open_input`, the per-batch / per-matrix /
per-column leaf (`p_at_x`) and OOD (`p_at_z`) targets of every `log_height == log_blowup`
matrix. Ran the real dregg `k_fold_turn_chain_proves_and_verifies` (~65s) as the oracle.
All fork instrumentation has been removed; only the `log_blowup=6` coverage test remains.

### What the conflict actually is (rock-solid, every run)
- The panic is a `WitnessConflict` at the height-1 `ro==0` assert
  (`recursion/src/pcs/fri/verifier.rs` ~:1326, `builder.connect(*ro0, zero)`), widx `164440`:
  the in-circuit reduced opening `ro0` for the `log_blowup` (height-1) group computes to a
  **full-extension NONZERO** value, which is then connected to `0`.
- **Native FRI ACCEPTS the same proof.** `p3_batch_stark::verify_batch` runs
  `pcs.verify(...)?` (the FRI/PCS check incl. the height-1 `ro==0` assert,
  `batch-stark/src/verifier/mod.rs:502`) BEFORE the LogUp global-sum check (`:639`). My
  native-verify probe failed only at the later lookup stage (`GlobalCumulativeMismatch`, a
  wrong-public-inputs artifact of the probe), so native FRI reached the lookup stage =
  native FRI computed `ro0 == 0`. So this is a **circuit-vs-native FRI reduced-opening
  divergence**, NOT a prover/forgery bug.

### REFUTATIONS (do not re-pursue)
- **ext/base "full-extension contamination" is REFUTED.** Every opened-value slot in the
  height-1 group (`p_at_x` and `p_at_z`, all rounds) is base-embedded `[v,0,0,0]`. No
  full-ext slot, no `col2==col3` repeated-adjacent signature, no multi-expr DSU collapse,
  no `decompose_ext_to_base_coeffs` / `ext_recompose_coeffs` involvement. The earlier
  "p_at_z[2] full-ext" hand-off was wrong.
- **"perm_next == 0" is NOT the stable signal.** A transient circuit state showed a height-1
  matrix with `local==leaf==const, next==0`; in the stable/current state ALL height-1
  matrices (every round, every column, both `zeta` and `zeta_next`) are CONSISTENT
  (`leaf == local == next`). The raw proof has `permutation_local == permutation_next`
  per instance (both nonzero, or both zero) — so the perm next-term is genuinely 0.

### The genuine open lead (the paradox to resolve)
`ro0` is full-ext NONZERO even though every per-matrix/per-column `(p_at_z - p_at_x)` term
sampled is 0. Two facts narrow it:
1. The dump tags only the FIRST query's matrices (duplicate-tag errors keep later queries
   from re-tagging). `open_input` runs **per FRI query**; each query opens DIFFERENT
   committed rows. So the divergence is on a query OTHER than the one sampled.
2. The `ro0` value CHANGES run-to-run (`[231554781,..]` vs `[1630836230,..]`), i.e. the
   dregg proof/challenges are non-stationary — the shared worktree was being recompiled by
   concurrent agents mid-investigation (the documented swarm hazard), so the failing proof
   shifted between runs.

LEADING HYPOTHESIS: a matrix with a genuinely degree-`>0` opening is being bucketed into the
`log_height == log_blowup` (height-1) group, where its reduced opening is nonzero on the
queries whose committed row `!=` the OOD value. Native folds that contribution at the
correct (taller) height; the recursion asserts it `==0` at `log_blowup`. The suspect is the
**`mat_domain.log_size()` / `log_height` assignment** for one round's matrix in
`verify_batch_circuit` (`recursion/src/verifier/batch_stark.rs` trace/preprocessed/permutation
round `*ext_dom` push) vs native `ext_trace_domains` — OR the per-query leaf↔OOD pairing in
`open_input` (`verifier.rs:1185` zip) for that matrix. NEXT STEP: tag per-query (disambiguate
the duplicate-tag suppression) on a FROZEN proof (pin the dregg tree / no concurrent rebuild),
find the query+matrix whose `(p_at_z - p_at_x) != 0` at the height-1 group, then compare that
matrix's `log_height` to native's. Do NOT chase ext/base or perm_next=0.
