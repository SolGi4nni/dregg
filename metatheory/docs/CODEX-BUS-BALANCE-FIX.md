# Codex — the WitnessChecks bus-balance fix (2026-06-25)

ROOT CAUSE (codex, the expose_claim bus designer): the W24 segment-digest expose_claim READS (mult=-1) have NO matching WRITES (mult=+1) in the aggregation child proof, because the W24 poseidon2_perm/baby_bear_d4_w24 table (whose output CTL emits the +1 writes) is registered at the LEAF layer but MISSING from the AGGREGATION layer's proof construction (only the W16 challenger + expose_claim are registered there). -> WitnessChecks global cumulative != 0 -> native verify_all_tables rejects GlobalCumulativeMismatch.

## The fix
Include the W24 poseidon2_perm/baby_bear_d4_w24 table in the AGGREGATION layer's: preprocessing + AIR construction + table proving + verifier registration (the FriRecursionBackend non_primitive_{provers,air_builders,preprocessors} for the aggregation/build_and_prove_aggregation_layer path), mirroring its leaf-layer registration. Its output CTL then sends +1 per exposed digest output witness, matching the expose_claim -1 reads -> the bus balances to 0.

## The invariant (per proof carrying the segment)
- child segment values: PublicAir +1, expose_claim -1
- count: AluAir +1, expose_claim -1
- W24 digest lanes: W24 Poseidon2 output CTL +1, expose_claim -1
- expose table is READER-ONLY (never the writer)
The bus does NOT carry upward — each aggregation layer re-exposes a new segment (new readers) needing new same-proof writers.
