# Bound-eight symmetric BFV zero conversion: retained measurement receipt

This directory retains the raw receipt for the ring-aware exact-zero
specialization in `fhegg-fhe/src/fhir/logic_zero_observation_symmetric.rs`.
Every one of the 11 release-mode samples evaluated the same four live SIMD
residuals (`0, 1, 4, 6`) with fresh keys and ciphertexts, decrypted both outputs
with a test-only single-key oracle, and obtained `[40320, 0, 0, 0]` from both.

The exact work result is independent of timing: the generic factor tree uses
seven ciphertext multiplications for zero conversion; symmetric root pairing
and common-subexpression elimination use three, at the same output depth four
when the depth-one residual is included. Thus the eight-equality total is
`8 + 3 = 11`, versus `8 + 7 = 15` for the generic residual path and 15 for the
balanced Boolean baseline.

The wall-clock measurement covers only zero conversion. The generic median was
82.028 ms and the symmetric median 38.317 ms on `persvati` (2.141x ratio over
these samples). This is not an end-to-end result: setup, encryption, residual
evaluation, same-opening proof verification, opening/decryption, and transport
are excluded. The `fhe.rs` noise readings are observations, not a proof of
remaining decryption margin or a general noise theorem.

Files:

- `raw.jsonl`: one complete machine-readable output receipt per fresh-key run.
- `summary.json`: deterministic aggregation of those 11 rows.
- `META.txt`: host, toolchain, source/lock hashes, exact command, and cost scope.
- `SHA256SUMS`: integrity hashes for the retained files.

The formal plaintext identity and finite-domain correctness proof live in
`metatheory/Dregg2/Logic/CertifiedHybridProofFheSymmetricZeroObservation.lean`.

The following shell fragment checks that every raw line is JSON and reproduces
the sorted timing/noise vectors from which `summary.json` was calculated:

```sh
jq -s '{
  samples: length,
  generic_ns: map(.generic_zero_conversion_elapsed_ns) | sort,
  symmetric_ns: map(.symmetric_zero_conversion_elapsed_ns) | sort,
  generic_noise: map(.generic_observed_noise_bits) | sort,
  symmetric_noise: map(.symmetric_observed_noise_bits) | sort,
  outputs: (map(.opened_by_single_key_oracle) | unique)
}' raw.jsonl
shasum -a 256 -c SHA256SUMS
```
