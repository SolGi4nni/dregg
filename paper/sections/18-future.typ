// =============================================================================
// Section 18: Future Work - the Golden Vision
// =============================================================================

= Future Work: Toward the Golden Vision

The Silver Vision (integration-complete, executor-trusted-but-coherent, every loop closed) is operational today. The Golden Vision---*full distributed-semantics algebraic constraint*, a folded DAG of attestations where the joint mesh of cells' interactions is internally consistent and re-derivable from witness data---is the eventual north star. This section names the path.

== The framing

The user's framing: *"unstructured mesh of interactions, with Effect VM braiding attestable causality over it."* Chains are convenient but the actual semantic is a DAG: Bob's cap exercise depends causally on Alice's grant, which depended on Carol's introduction (different cells' chains). Today's receipt chain linearizes one cell's history; Stage 7-$gamma$.2 Phase 1 compresses one turn's bilateral view; the full vision is *folded mesh*: the whole graph of attested events up to "now" provable as one statement.

Deep research finds no public production system explicitly targeting DAG-shaped IVC with selective subgraph re-verification as a first-class feature. The pragmatic path keeps the *proof composition layer* tree-shaped (recursive verifier AIR over a tree of leaf proofs) and puts DAG semantics in the *statement layer* (Merkleized state graphs, intent commitments). Anoma, Aztec, and Penumbra all do this.

== The aggregation roadmap

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Stage*], [*State*]),
    [Per-cell Effect VM AIR with $tilde$151 columns], [Operational],
    [Sequential IVC chains via `build_recursive_ivc_chain`], [Operational],
    [Stage 7-$gamma$.0 shared-PI bundle (per-cell proofs of one turn share PI)], [Landed],
    [Stage 7-$gamma$.2 Phase 1 (PI-only bilateral binding + off-AIR `dregg-verifier bilateral-pair`)], [Landed],
    [Sovereign-witness Phase 1 (`WITNESS_KEY_COMMIT` AIR teeth)], [Designed in `SOVEREIGN-WITNESS-AIR-DESIGN.md`],
    [Lane Golden-Edge Block 1: lift `plonky3_recursion_impl` past `P3MerklePoseidon2Air` placeholder], [In flight],
    [Stage 7-$gamma$.2 Phase 2 (joint aggregation AIR via the generalized recursive substrate)], [Depends on Lane Golden-Edge],
    [Sovereign-witness Phase 2 (`transition_proof` recursive verification inside the AIR)], [Depends on Lane Golden-Edge],
    [Folded DAG of attestations (full Golden Vision)], [Long-term, statement-layer DAG + tree-shaped proof],
  ),
  caption: [Aggregation roadmap. Silver delivers the input substrate; Golden compresses it.],
)

== Two production paths to the recursive layer

The codebase carries two alternative outer recursive layers:

=== Fix the verifier AIR (transparent path)

Lift `plonky3_recursion_impl` past the `P3MerklePoseidon2Air` placeholder into a real verifier-as-AIR, generic over the inner AIR shape. The corrected aggregation architecture (per the corrected-folding-research synthesis):

```
inner proof bytes -> canonical parser ->
  verifier AIR enforcing accept = 1 ->
  acceptance bit constrained to 1 ->
  recursive compression tree ->
  optional final wrapper for export
```

The "hash chain over leaf-proof bytes" approach in the earlier Stage 7-$zeta$ design is *unsound*: a hash chain is metadata after acceptance is enforced, not the soundness mechanism. Acceptance must live *inside* the AIR. Stays transparent end-to-end; same field (BabyBear), same hash (Poseidon2), same toolchain. The work item is non-trivial---making the placeholder functional generic over arbitrary AIRs is its own engineering task---but holds the "transparent all the way down" property.

=== Kimchi/Pickles (production-proven outer layer)

The codebase carries $tilde$9.7K LOC of `circuit/src/backends/kimchi_native/` (predicate circuits), $tilde$5.8K LOC of `circuit/src/backends/mina/` (assisted-recursion `pickles.rs` + dual-curve step/wrap), and a $tilde$3.2K LOC `stark_in_pickles.rs` skeleton. Mina compresses a whole chain to $tilde$22 KiB with $tilde$864-byte state proofs and $tilde$200ms verification. The cost: a curve substrate dependency at the outer layer only (the transparent inner stack stays).

The honest framing: Mina has done the recursive layer; we can use it. Loses transparency-all-the-way-down; gains a production-proven recursive primitive. RISC Zero shape, with Kimchi instead of Groth16. Engineering cost: a Kimchi circuit that verifies a Plonky3 STARK isn't off-the-shelf, but the precedent (`stark_in_pickles.rs` skeleton + the Mina assisted-recursion path) is on disk.

The decision is open. The deep research leans toward "fix the verifier AIR" for soundness aesthetics; the practical argument is "ship Kimchi/Pickles and stop blocking Phase 2."

== Sovereign-Witness Phase 2

Once Lane Golden-Edge lands the generalized recursive verifier AIR, sovereign-witness Phase 2 becomes straightforward: when the `SovereignCellWitness.transition_proof: Option<Vec<u8>>` is present, the Effect VM AIR calls the recursive verifier on the inner proof and constrains acceptance = 1. This replaces the witness-vs-proof-carrying fork (today mutually exclusive) with a layered spectrum: witnesses always carry signature teeth (Phase 1); witnesses with `Some(transition_proof)` additionally carry algebraic-validity teeth (Phase 2). Closes threat T9 algebraically.

== Full Privacy Pipeline

The privacy migration (Section 5) proceeds through six phases. The most impactful near-term change---removing `final_root` from public inputs and replacing it with a blinded presentation tag---provides full unlinkability with minimal circuit additions. The unified recursive proof (Phase 4) eliminates structural information leakage from the multi-proof composition. Phase 5 (revocable unlinkability) closes the issuer-revoke / verifier-unlink tension via in-circuit revocation-handle derivation.

== Federation Privacy: from Layer 1 to Layer 3

Encrypted turn ordering (@sec-federation-privacy) requires either threshold decryption ceremonies or full validity proofs for every turn. The substrate is real: `federation::threshold_decrypt` (Shamir over GF(256) + ChaCha20-Poly1305) is the same primitive the trustless intent engine now uses. The intermediate step is validium-style blind ordering: Bloom filter conflict sets for parallelism detection, lightweight STARKs for nonce/fee validity, and threshold decryption after ordering. Full elimination of decryption (Layer 3) requires encoding conservation and authorization verification in the validity AIR.

== Two-Language Authoring: dreggscript

The current authoring discipline is *bottom-up*: imagine the runtime API a behavior/protocol language would compile to; implement primitives as ugly Rust method-chains in `dregg-sdk` first; if chains are awkward, that awkwardness identifies the SDK gap; macro the chains once they work; *then* consider a surface language. The two-language model the project has in mind:

- *dregg-dsl* (exists, sparse, stays focused): caveat predicate language descended from macaroons/biscuits. Row-shaped, constraint-shaped, multi-backend.
- *dreggscript* (new, exploratory): behavior/protocol language for cell authoring, CapTP composition, app-framework primitives. Compiles down to typestate `ActionBuilder` calls + cell program declarations + CapTP wire protocols.

They compose: dreggscript invokes dregg-dsl when it needs a caveat predicate; they don't compete.

The verified-compile-target survey landed on CakeML > PureCake > Lean 4 > custom: CakeML's strict semantics + verified compilation to native code + verified Candle HOL Light kernel makes it the most credible target. Year-scale integration; near-term experiment is a one-page proof-of-life linking a hand-written cell behavior in CakeML to CapTP via FFI.

== Effect VM Optimization

- Batch proving multiple turns in a single trace (amortized cost).
- Hardware acceleration (GPU/FPGA proving for throughput).
- Sub-10ms proof generation for simple authority checks (latency-sensitive coordination).
- Sub-1 KiB proofs for bandwidth-constrained gossip (Binius backend may deliver this).

== EVM Bridge Maturation

The SP1-based EVM bridge is architecturally complete but the guest program requires regeneration against the current Plonky3 backend. Remaining: regenerate SP1 guest ELF, deploy VK registry contract with governance (multisig parameter updates), production incremental Merkle tree for deposits, gas optimization for the on-chain verification path.

== Post-Quantum Migration

The STARK path is post-quantum today. Classical components have a staged migration: BLS12-381 threshold signatures $arrow.r$ lattice threshold (awaiting standardization), Ed25519 $arrow.r$ ML-DSA, X25519 $arrow.r$ ML-KEM. These migrations are confined within federation trust boundaries and can be executed per-federation without protocol-wide coordination.

== Open Questions

- *Genesis ceremony design*: how is authority bootstrapped without a single root of trust?
- *Shared mutable state*: how do agents share state that multiple parties can read/write?
- *Sealable witness bundle*: should `WitnessedReceipt` scope-2 bundles be sealable to a chosen audit-key, rather than ship as JSON artifacts with no audience predicate?
- *CDT-revocation $arrow.l.r$ revocation-channel link*: two disjoint revocation mechanisms exist today. Should a CDT revocation trip a channel?
- *Federation scaling*: for very large committees ($N > 100$), committee-sampling approaches.
- *Treasury governance*: voting mechanism for treasury spending (deferred to governance design).
- *The Authorization::Unchecked carve-out list*: explicit and CI-guarded, but inevitably grows with new CapTP/peer_exchange shapes. Long-term path is to eliminate the variant entirely; near-term path is auditable carve-outs.
- *Equivocation rule unification*: finality-layer (`same (creator, seq)`) and ordering-layer (`same (creator, round)`) flavours differ; should they unify?

== The two visions, together

The Silver Vision *is* the input to Golden. A coherent pre-algebraic runtime produces real `WitnessedReceipt` chains; folding compresses those chains; algebraic binding makes the joint statement sound. Silver without Golden is "we trust the executor"; Golden without Silver is "we prove nothing happened." The handoff is structural: Silver delivers an integration-complete runtime; Golden compresses its receipts.

The discipline that follows: every dispatch question---should we work on X or Y?---gets routed through *"does X close a Silver-Vision integration gap?"* until Silver is in place; *then* Golden work begins. Stage 7-$gamma$.2 Phase 1 is the first concrete Golden step; the "carry-everything" WitnessedReceipt chains are the input substrate Golden eventually compresses.
