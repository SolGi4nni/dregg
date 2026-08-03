# Private preference N4K4 — reusable winner-only proof organ

*2026-07-19. A real fixed-shape private-ballot receipt for games and collective
decisions. It hides from the verifier/public, but the trace-building prover sees
the ballots: Tier 1, not Tier 0.*

## Exact family

`metatheory/Dregg2/Games/PrivatePreferenceDescriptor.lean` authors a fixed
four-participant, four-option bounded-score election:

- every participant privately scores every option in `0..3`;
- scores add per option, so every private total is in `0..12`;
- the winner is the lowest option index with maximal aggregate score;
- the public statement is exactly 11 BabyBear felts:
  `(session, rule, ballotRoot[0..8), winner)`;
- aggregate totals and the winning score remain private.

Each four-score ballot is one injective base-4 byte. Participants 0/1 and 2/3
form two injective base-256 16-bit packs. The commitment preimage is
`(PRF4-domain, session, PRN4-rule, packedLow, packedHigh, blind[0..8), 0,0,0)`.
It uses the deployed Poseidon chip's full arity-16 seed mode and exposes all
eight permutation output lanes. There is no scalar-felt cryptographic
intermediate. Commitment uniqueness remains the ordinary computational
wide-Poseidon collision-resistance assumption, never a false finite-field
injectivity theorem.

The emitted AIR recomputes both packs, all sixteen score decompositions, four
totals, a one-hot winner, global maximality, and the lowest-index tie tooth. The
last one subtracts whether a later option was selected from each max-difference;
an earlier tie would require a negative four-bit slack and therefore cannot
satisfy the AIR.

## Lean boundary

The semantic checker is exact and kernel-clean:

- `packedScores_injective` proves the two public-source packs lose no score;
- `argmaxUpto_max` and `argmaxUpto_strict_before` establish exact maximum and
  deterministic lowest-index tie behavior;
- `winner_eq_of_optimal_and_lowest` is the uniqueness endpoint for an integer
  AIR decode;
- `check_sound` binds rule/root/winner and exposes both argmax teeth;
- `two_distinct_openings_yield_root_collision` isolates the external
  computational binding assumption;
- `privatePreferenceN4K4_emitted_air_sound` starts from actual `Satisfied2`,
  arbitrary verifier PIs, canonical cells, and `ChipTableSoundN`, then extracts
  every modular semantic gate, every PI pin, and the genuine wide permutation
  result;
- `privatePreferenceN4K4_private_bits_decoded` goes further: BabyBear primality
  and canonical cells force every score, selector, max-difference, and
  lowest-index slack bit to an honest integer `0/1` directly from `Satisfied2`;
- `semantic_gate_exact` closes the generic
  `Satisfied2 + complete-residual no-wrap -> exact integer gate` step;
- `score_recompose_exact` and `four_bit_recompose_exact` then close every
  two-bit score and four-bit max-difference/lowest-slack recomposition over the
  integers; score columns are proved in `0..3`;
- `total_column_exact`, `packed_columns_decode`, `select_sum_exact`, and the
  max/difference/slack lemmas close the bounded affine decode with no field
  wrap;
- `column_winner_semantic` identifies the emitted winner as the semantic
  lowest-index aggregate argmax;
- `root_input_decoded` and `column_root_semantic` identify the complete
  16-lane emitted Poseidon seed and all eight output lanes with the semantic
  ballot commitment;
- `privatePreferenceN4K4_descriptor_to_accepts` closes
  `PrivatePreferenceDescriptorToAccepts`: actual `Satisfied2`, canonical trace
  cells, canonical external PI representatives, and `ChipTableSoundN` imply
  exact semantic `Accepts` for the decoded witness. Canonicality on the PIs is
  explicit because `Satisfied2` pins public values modulo BabyBear.

The next residual is downstream, not another hidden functional gap in this
descriptor: weld authenticated/censorship-resistant ballot ingestion to the
committed session/root, add a Tier-0 FHE/MPC producer if no plaintext
aggregator is allowed, and widen the fixed N/K/rule family as product needs
require.

## Rust privacy API

`circuit-prove::private_preference` consumes the exact emitted JSON:

- `PrivateBallot::try_new` and `PrivatePreferenceWitness` fail closed outside
  exactly four ballots, four options, two-bit scores, canonical sessions, and
  canonical eight-felt blindings;
- `prove_zk` / `verify_zk` use `DreggZkStarkConfig` and `HidingFriPcs` with fresh
  OS-seeded salts, random trace rows, and random FRI codewords;
- `prove_ballots_zk` also rejection-samples the eight commitment blind felts;
- `prove_non_hiding` is explicitly compatibility/debug only;
- `verify_decision_zk` returns a `VerifiedDecision` whose winner is safe to map
  to an application option only after proof verification.

The focused tests check exact PI exposure, shape refusal, fresh commitment
blinds, the lowest-index tie, sensitivity to score/session/every blinding lane,
genuine hiding randomness, changed-private-ballot binding, and forged root or
winner refusal.

## Game and voting integration seam

No dependency was added to `starbridge-privacy-voting` or `dreggnet-party`.
That is deliberate: privacy-voting is in browser/wasm dependency trees and
`dreggnet-party` is an embedded game surface, while `dregg-circuit-prove` owns
the heavy recursion/prover stack. Pulling the prover into either crate would
invert the existing verify/prove boundary.

The clean host composition is:

1. bind the poll/fork/quest identifier into the canonical BabyBear `session`;
2. collect exactly four private score vectors through the intended custody
   path;
3. call `prove_ballots_zk` in a prover service;
4. call `verify_decision_zk` at the application host;
5. require the returned root/session to match the poll's committed source, then
   map `VerifiedDecision.winner` to the same option ordering used by
   `PartyFork.paths`, the privacy-voting choice table, matchmaking candidates,
   or quest branches;
6. commit the chosen application turn through the existing executor.

The source-ingestion/root weld in step 5 is an application integration
obligation. This proof alone does not establish eligibility, one-person-one-
ballot, quorum, or uncensorable inclusion; the existing ballot-cell/collective
surfaces supply those independent teeth.

## Privacy audience and non-claims

`HidingFriPcs` hides witness openings from the verifier and public transcript.
The single process building the trace sees all four ballots. A Tier-0/no-viewer
version must jointly produce the same relation from FHE/MPC or prove a source
relation from its transcript without one plaintext aggregator.

This family is intentionally small and fixed. It does not claim arbitrary N/K,
weighted eligibility, Condorcet/STV semantics, malicious-secure MPC, or a full
batch-STARK simulator theorem. An authorized provenance/VK installation remains
a separate epoch operation; this WIP adds reproducible Lean bytes without
silently performing that ceremony.

## Verification record

- `lake env lean Dregg2/Games/PrivatePreferenceDescriptor.lean`: green, nineteen
  kernel-clean keystones.
- `lake build Dregg2.Games.PrivatePreferenceDescriptor`: green.
- fresh `EmitByName` payload equals the checked-in artifact byte-for-byte;
  SHA-256 `e7e2c7dbf4d34b104f2478b4c745a399936b5b127afa4f8b793e9ef177cc902d`.
- `scripts/check-no-degraded-felt.sh`: green. **Scope caveat (added 2026-08-02):**
  this was measured 2026-07-19 under the then 3-file rule, which matched only the
  spelling `fold_bytes32_to_bb`. The rule was widened twice since — 2026-07-31
  (scope 3 files → 8) and 2026-08-01 (the aliases `fold_bytes32` / `fold_value32`)
  — and the gate does **not** pass at HEAD: two real production wounds remain,
  `cell/src/commitment.rs:561` and `node/src/turn_proving.rs:1159`, both of which
  the 07-19 rule was structurally unable to see. The verdict above is a true
  record of a narrower rule, not a current green. See the header of
  `scripts/check-no-degraded-felt.sh`.
- `cargo nextest run -p dregg-circuit-prove --lib private_preference` on the
  warm persvati lane: 3/3 green, 225 skipped; hiding/tamper test 0.204s after
  build.
