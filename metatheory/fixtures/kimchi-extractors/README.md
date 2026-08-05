# Kimchi reality-gate extractors — preserved because they were one `git clean` from gone

These four files produce the **ground truth** for the Mina/Kimchi reality gates
(`metatheory/kimchi_real_proof.json` → `KimchiRealProofGate.lean`, and the Poseidon-firing
fixture → `KimchiPoseidonGate.lean`). Without them the fixtures cannot be regenerated and the
gates' differentials become unreproducible numbers.

**They lived only as UNTRACKED files inside a third-party checkout** (`~/dev/proof-systems/kimchi/
examples/`), which `docs/MINA-REALITY-GATE.md` described as "committed in that repo" — false, and
caught by `docs/AUDIT-MINA-KIMCHI.md`. Copied here verbatim on 2026-07-27 so the gate's provenance
survives a `git clean`, a re-clone, or a rev bump in that checkout.

## Provenance

- Source checkout: `~/dev/proof-systems` (o1-labs `proof-systems`), rev **`f6d958dc05`** at copy time.
- `reality_gate_export.rs` — builds `create_circuit(0, 5)`, proves it over Vesta/Pasta, asserts the
  real `kimchi::verifier::verify` ACCEPTS, then dumps every oracle value via `proof.oracles(...)`
  (the exact `to_batch` path) as JSON. This is the fixture the C5/C8 differentials consume.
- `reality_gate_poseidon_export.rs` — the same, plus a full `create_poseidon_gadget`, so the emitted
  proof has `poseidon_selector(ζ) ≠ 0`. This is what makes the six transcribed custom-gate bodies
  and the C3 `v`/`u` challenge re-derivation NON-VACUOUS rather than a source reading.
- `pickles_p6_fq_export.rs` (added 2026-07-28, rev `f6d958dc05` recorded from `git describe`, not
  hardcoded) — two outputs in one run, both feeding `metatheory/kimchi_p6_prev2_proof.json`:
  1. **`fq_kimchi` Poseidon KATs** over `Fq = Vesta::BaseField`, driven through the UPSTREAM
     `ArithmeticSponge::absorb`/`squeeze` state machine at BOTH input parities, plus the
     double-permute anti-values. These are the gold vectors `PastaPoseidonFq.lean` pins to; the
     constants themselves are `mina_poseidon::pasta::fq_kimchi::static_params()` dumped whole.
  2. **A real Kimchi proof with `prev_challenges = 2`** (`create_recursive` + two genuine
     `RecursionChallenge` accumulators, the `kimchi/src/tests/recursion.rs` recipe), asserted
     accepted by the real `kimchi::verifier::verify`, with every phase-1 Fq-sponge INPUT dumped in
     `verifier.rs:159-276` order so β/γ/α′/ζ′ are re-derivable rather than carried. It also
     independently REPLAYS the Fq-sponge in Rust and asserts the replay reproduces
     `proof.oracles(...)` — the line
     `[cross-check] independent Fq-sponge replay reproduces beta/gamma/alpha'/zeta'/digest : true`
     is that assertion, and it is an `assert!`, not a print. Consumers:
     `PastaPoseidonFq.lean`, `KimchiRecursionGate.lean`.

- `step_vk_index_export.rs` (added 2026-08-04, REPLACES `wrap_key_index_export.rs`) — the **W-KEY**
  ground truth, feeding `metatheory/kimchi_step_key_index.json` and `KimchiWrapMain` §14's
  `STEP_VK_XY`. It reads **o1-labs' released `step-transaction` gate blob** (`circuit-blobs`,
  `berkeley-devnet`, md5 `c33ec5211c07928c87e850a63c6a2079` — the release filename IS the OCaml
  constraint-system digest), 17 806 rows at 67 public inputs, and dumps the 28 index commitments of
  MINA'S OWN STEP KEY as 56 Fq coordinates in **`index_to_field_elements` order**
  (`pickles_base/side_loaded_verification_key.ml:159-183`: `sigma_comm` 7, `coefficients_comm` 15,
  then `generic`/`psm`/`complete_add`/`mul`/`emul`/`endomul_scalar`), which is the order
  `wrap_verifier.ml:521-530` absorbs to produce `index_digest`.

  ⚠ **Six `assert!`s, not prints, and every one is load-bearing.**
  1. Rust kimchi's `VerifierIndex::digest` (`kimchi/src/verifier_index.rs:451-530`) absorbs those
     eight fields AND THEN `range_check0/1`, `foreign_field_add/mul`, `xor`, `rot` and the whole
     `lookup_index` **when present**. Pickles' `Plonk_verification_key_evals.t` has no such fields,
     so the two agree ONLY for an index carrying none of them — the extractor asserts every one is
     `None` before it dumps. Without that, the 56 numbers would be a PREFIX of the digest's preimage
     wearing the name of the whole of it.
  2. An independent `absorb_fq` replay over exactly those 56 coordinates reproduces
     `verifier_index.digest::<BaseSponge>()`. So the dump is that digest's preimage.
  3. **`n_points_at_infinity == 0`.** See below — this is the whole reason the file exists.
  4. The SRS it committed against has `h == MinaStepSrsLagrange.URS_H_XY`, so the key and the x_hat
     Lagrange table come from the SAME step URS and not from two SRSs with the same name.
  5. All 56 coordinates occur among `wrap-transaction`'s gate coefficients — Mina's own wrap circuit
     holds the step keys as `Inner_curve.constant` (`wrap_verifier.ml:189-204`), so it BAKES THIS KEY
     IN. Measured 56/56 against 995 distinct coefficients.
  6. **None** of them occurs in `wrap-blockchain`'s 584. Without leg 6, leg 5 is unfalsifiable.

  ⚑ **WHY IT REPLACED `wrap_key_index_export.rs` (deleted 2026-08-04).** That extractor dumped the
  index of kimchi's own generic-gate test circuit — `create_circuit(0, 5)`. It has no Poseidon,
  CompleteAdd, VarBaseMul, EndoMul or EndoMulScalar row and writes 8 of the 15 coefficient columns,
  so **seven of its 28 commitments were the point at infinity**: `verifier_index.rs:230-238` commits
  `sigma_comm` and `coefficients_comm` with `commit_evaluations_non_hiding`, UNMASKED, and a zero
  column lands on the identity. (The six selectors below them go through `mask_fixed`, blinder 1, so
  a zero selector lands on the SRS blinding base `h` — which is why five of that key's singles were
  the same point, and that point was `URS_H_XY`.)

  `index_to_field_elements` flattens infinity as the fake point `(0,0)`, W-COMBINE folds the 28
  points with `Ops.add_fast` — the INCOMPLETE add — and a chord through `(0,0)` is not on
  `y² = x³ + 5`. So `combined_polynomial`, `p_prime`, `q`, `cq` and `lhs` were all off-curve and
  `wrap_main.ml:419`'s `Boolean.Assert.is_true bulletproof_success` had no honest witness at all. It
  was the FIXTURE, not the gadget. The old extractor is deleted rather than kept beside the new one
  because a fixture generator that reproduces a degenerate key is a trap, and `git log` keeps it.

⚠ The `36a8b510` rev cited in the Lean headers is a hardcoded `println!` in the extractor, not a
recorded fact — true for the original fixture (reflog-confirmed) but nothing enforces it. The rev
above is what the checkout reads TODAY. If you regenerate, re-record both.

## To regenerate

Copy the file back into `<proof-systems>/kimchi/examples/`, then `cargo run --release --example
reality_gate_export` (resp. `..._poseidon_export`, `step_vk_index_export`) from that checkout, and
replace the JSON / the Lean literals. The Lean side byte-matches the JSON (audited: all 30 literals).

`step_vk_index_export` writes its whole output to stdout as JSON:

    cargo run --release --example step_vk_index_export -p kimchi > metatheory/kimchi_step_key_index.json

and refuses (panics) rather than dumping if ANY of its six assertions fails. It needs the three
`circuit-blobs` gate lists in `~/.mina/circuit-blobs/berkeley-devnet/` (or
`$MINA_CIRCUIT_BLOBS_BASE_DIR`); it does not fetch.
