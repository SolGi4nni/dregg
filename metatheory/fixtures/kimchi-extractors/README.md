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

- `wrap_key_index_export.rs` (added 2026-08-03) — the **W-KEY** ground truth, feeding
  `metatheory/kimchi_wrap_key_index.json` and `KimchiWrapMain` §14's `STEP_VK_XY`. It rebuilds the
  SAME `VerifierIndex` `pickles_p6_fq_export.rs:158-174` builds and dumps its 28 index commitments as
  56 Fq coordinates in **`index_to_field_elements` order**
  (`pickles_base/side_loaded_verification_key.ml:159-183`: `sigma_comm` 7, `coefficients_comm` 15,
  then `generic`/`psm`/`complete_add`/`mul`/`emul`/`endomul_scalar`), which is the order
  `wrap_verifier.ml:521-530` absorbs to produce `index_digest`.

  ⚠ **Two `assert!`s, not prints, and both are load-bearing.**
  1. Rust kimchi's `VerifierIndex::digest` (`kimchi/src/verifier_index.rs:451-530`) absorbs those
     eight fields AND THEN `range_check0/1`, `foreign_field_add/mul`, `xor`, `rot` and the whole
     `lookup_index` **when present**. Pickles' `Plonk_verification_key_evals.t` has no such fields,
     so the two agree ONLY for an index carrying none of them — the extractor asserts every one is
     `None` before it dumps. Without that, the 56 numbers would be a PREFIX of the digest's preimage
     wearing the name of the whole of it.
  2. It asserts `verifier_index.digest::<BaseSponge>()` equals the `VKDIGEST` already recorded in
     `PastaPoseidonFq.lean`, AND that an independent `absorb_fq` replay over exactly those 56
     coordinates reproduces it. So the dump is that digest's preimage, not a second copy of some
     other index's coordinates.

  ⚠ **Seven of the 28 commitments are the identity** (unused coefficient columns of a small
  generic-only test circuit) and `DefaultFqSponge::absorb_g` (`poseidon/src/sponge.rs:332-345`)
  absorbs the FAKE POINT `(0,0)` for infinity, so they contribute 14 zero coordinates rather than
  being skipped. A model that skipped them would produce a different digest, silently.

⚠ The `36a8b510` rev cited in the Lean headers is a hardcoded `println!` in the extractor, not a
recorded fact — true for the original fixture (reflog-confirmed) but nothing enforces it. The rev
above is what the checkout reads TODAY. If you regenerate, re-record both.

## To regenerate

Copy the file back into `<proof-systems>/kimchi/examples/`, then `cargo run --release --example
reality_gate_export` (resp. `..._poseidon_export`, `wrap_key_index_export`) from that checkout, and
replace the JSON / the Lean literals. The Lean side byte-matches the JSON (audited: all 30 literals).

`wrap_key_index_export` writes its whole output to stdout as JSON:

    cargo run --release --example wrap_key_index_export -p kimchi > metatheory/kimchi_wrap_key_index.json

and refuses (panics) rather than dumping if either assertion above fails.
