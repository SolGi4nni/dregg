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
