# Codex cross-model soundness review — dregg unbounded IVC (2026-06-24)

Adversarial review by codex-cli 0.131.0 (cross-model). Found GENUINE soundness holes — the IVC VERIFIES the honest prover's proof but a FORGED whole-chain claim can verify. 'Test passes' != 'sound'. Every file:line below was spot-checked accurate.

**Findings**

1. **Critical: the root proof is not linked to the carried binding proof or the claimed chain publics.**  
   [ivc_turn_chain.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1199) verifies three things independently: the supplied binding proof, the root VK fingerprint, and the recursive root proof. It never checks that the binding proof is the binding leaf folded into that root. The verifier also calls `verify_all_tables(proof)` with no expected public-input vector in [plonky3_recursion_impl.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/plonky3_recursion_impl.rs:718). The module doc already flags the missing linkage at [ivc_turn_chain.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:127).  
   **Attack:** take a valid recursive root proof for history A with the expected root VK shape, pair it with a separately valid binding proof claiming history B/endpoints/digest. The final verifier has no in-band equality tying those objects together, so false whole-chain claims can verify.

2. **Critical: the binding AIR does not constrain the advertised chain digest, and does not constrain `num_turns`.**  
   [ivc_turn_chain.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:375) enforces seam continuity, first root, final root, and accumulator carry-forward, but never enforces `acc_out = H(acc_in, old_root, new_root, idx)`. It explicitly says `numTurns` is unconstrained at [ivc_turn_chain.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:378). The honest trace generator computes the hash at [ivc_turn_chain.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:457), but that is prover-side discipline, not verifier soundness.  
   **Attack:** produce a binding proof for arbitrary `chain_digest` and arbitrary `num_turns` by choosing accumulator columns that satisfy only the carry constraints. This breaks the claimed ordered-history commitment even before considering recursion.

3. **Critical/High: the real accumulator silently disables VK pinning on mismatch.**  
   [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:529) sets `pin_this_fold` only if the current running preprocessed commitment equals the saved pin. If it differs, the code falls through to `running.into_recursion_input::<BatchOnly>()` at [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:535), meaning the fold proceeds unpinned instead of rejecting. The test at [accumulator.rs test](/Users/ember/dev/breadstuffs/circuit-prove/tests/accumulator.rs:296) uses `probe_pinned_fold`, which always calls the pinned path, so it does not test this branch.  
   **Attack/gap:** after a pin is captured, a changed or foreign running proof commitment should be fatal. Today it becomes an unpinned child proof. That contradicts the load-bearing claim that subsequent folds are VK-pinned.

4. **High: depth-4 == depth-5 is not a proof of constant VK forever.**  
   The claim is made in [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:67), while the test only samples depth 4 and 5 at [tests/accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/tests/accumulator.rs:370). One equality measurement is not an induction. To prove fixed point, the code needs a structural argument that the wrapped input proof shape, rows, non-primitive manifest, preprocessed metadata, and verifier op-list are identical under another fold. The file itself still says the structural half is residual at [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:129).  
   **Impact:** this is a succinctness overclaim. The verifier may be fixed for the measured depths, but the code has not proved depth-4 == depth-N.

5. **High: finalization uses an unpinned final fold and default aggregation params.**  
   [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:648) folds the running proof with the binding leaf using `into_recursion_input`, not the pinned path, and [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:651) uses `ProveNextLayerParams::default()` instead of the wrap params.  
   **Gap:** even if the running accumulator stabilizes, the terminal proof may have a depth/shape-dependent root VK. That weakens the “constant verifier forever” story unless separately anchored and measured for every relevant finalization shape.

6. **High: public-input threading is real, but it does not by itself bind the final claim.**  
   The fork does thread genuine table publics into child verification in [recursion.rs](/Users/ember/dev/plonky3-recursion/recursion/src/recursion.rs:138) and packs them at [public_inputs.rs](/Users/ember/dev/plonky3-recursion/recursion/src/public_inputs.rs:676). That is good. But the final verifier does not take expected root public values, nor compare child binding-leaf publics against the carried claim.  
   **Gap:** lever b fixes intra-recursion witness plumbing, not the final “this root proves these exact genesis/head/digest/turns” statement.

7. **Medium/High: VK pinning pins the preprocessed commitment, not the full VK identity used by the fingerprint.**  
   `pin_preprocessed_commit` connects all flattened preprocessed commitment elements to constants at [batch_stark.rs](/Users/ember/dev/plonky3-recursion/recursion/src/verifier/batch_stark.rs:194). That part is sound when invoked. But the root VK fingerprint hashes more than that: rows, degree bits, table packing, non-primitive manifest, and metadata in [plonky3_recursion_impl.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/plonky3_recursion_impl.rs:647).  
   **Gap:** calling this “full VK identity” is too strong unless the remaining VK fields are otherwise fixed by the parent/root VK anchor. The pin itself is partial.

8. **Medium: the accumulator is not O(1) state as implemented.**  
   The code stores all seam pairs in `seam_pairs` at [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:256), and finalization rebuilds the binding proof from them. The comment at [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:241) admits `O(num_turns)` scalar witness state.  
   **Impact:** proof memory may be bounded, but the running accumulator state is not strictly constant-size.

9. **High, as assurance evidence: the Lean induction assumes the hard soundness facts instead of deriving them from this verifier.**  
   `EngineSound` assumes recursive soundness, positional leaf-to-step pairing, and binding soundness at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:115). The unbounded accumulator stores a `leanWitness` directly at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:487), and `acc_attests_whole_history` is just projection at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:628).  
   **Gap:** the theorem is a clean spec invariant, not a proof that Rust’s recursive proof object binds root proof, binding proof, child publics, and ordered leaves. It currently hides exactly the implementation gaps above.

**Actually Sound Pieces**

- When `pin_preprocessed_commit` is actually used, it does connect every preprocessed commitment target to the expected constants. The flaw is call-site enforcement and scope of identity, not that constraint itself.
- `genuine_table_public_inputs` is a real improvement: child public inputs are threaded into the recursive verifier circuit. It just does not close the final external claim-binding problem.
- Host-side `Accumulator::accumulate` checks descriptor participation and seam continuity, but that is not enough for adversarial proof soundness because the verifier must reject maliciously assembled proof objects without trusting the host construction path.
