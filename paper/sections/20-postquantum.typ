// =============================================================================
// Section: The post-quantum floor
// =============================================================================

#import "../defs.typ": lean
= The post-quantum floor <sec-postquantum>

Two rows of the assumption floor (@sec-assurance) break structurally under a
quantum adversary: Shor's algorithm recovers ed25519 signing keys and computes
the discrete logarithms that bind Pedersen value commitments. The remaining
cryptographic rows face only generic search speedups. This section states what
is proven about the system against a quantum adversary: a mechanized quantum
oracle model, game reductions for the two lattice replacement primitives, a
hybrid signature keystone, and finality safety under a disjunctive floor. The
development is connected end-to-end, from the adversary model to the deployed
signing surface, with one named hypothesis remaining on the signature path.

== The adversary model

The quantum adversary is modeled directly over Mathlib's finite-dimensional
inner-product spaces: a state is a vector of $"EuclideanSpace" CC B$, a
computation step is a norm-preserving linear bijection, and the random oracle
is the basis permutation $lr(|x, y angle.right) arrow.r.bar lr(|x, y + H(x) angle.right)$, a genuine
unitary by construction (#lean("QuantumOracle.oracleUnitary")). An adversary
interleaves its own unitaries with $q$ oracle calls. Over this model the
one-way-to-hiding lemma bounds how well any such adversary distinguishes an
oracle from a reprogrammed one: the semiclassical form gives
$2 sqrt(q dot P_"find")$ (#lean("OneWayToHiding.o2h_bound")), and the
double-sided form removes the $sqrt(q)$ when the per-query difference vectors
are pairwise orthogonal --- the condition supplied by a deterministic,
injective encryption whose reprogrammed point is efficiently recognisable
(#lean("DoubleSidedO2H.double_sided_o2h")). The orthogonality hypothesis is
load-bearing rather than decorative: on an exhibited non-orthogonal pair the
Pythagorean identity the proof rests on is false
(#lean("DoubleSidedO2H.orthogonality_load_bearing")).

The parameter-level payoff is a change of governing floor, not only a tighter
constant. The tight KEM bound is
$min("mlweBits", "foCorrectnessBits" - log_2 q) - 2$
(#lean("DoubleSidedO2H.kemTightAdv_le")): the lattice term enters linearly, and
the query budget survives only in the correctness term. At the recorded
lattice estimate and a $2^20$-query budget this is 152 bits, against 107 for
the semiclassical bound (#lean("DoubleSidedO2H.deployed_tightness_gain")), and
it tracks the MLWE estimate --- degrading the lattice floor degrades the bound,
where the semiclassical figure would sit unchanged behind the message entropy.

== The primitive games

*ML-KEM (FIPS 203).* IND-CCA security of the Fujisaki--Okamoto transform is
grounded in MLWE together with the quantum random-oracle model
(#lean("MlKemIndCca.ml_kem_ind_cca_reduces_to_mlwe")). On the correctness
side, the encaps and decaps cores are executable Lean definitions compiled to
native code and called over FFI; the decode margin at the deployed modulus
$q = 3329$ is a theorem with the flipping instance one past the bound exhibited
(#lean("Fips203Kem.decode_correct")), the encaps-to-decaps round trip is
derived (#lean("Fips203Kem.kyber_honest_roundtrip")), and the KEM round-trip
hypothesis is discharged for the extracted cores
(#lean("Fips203Kem.extractedKemApi_fips203")) --- no crate is trusted for it.

*ML-DSA (FIPS 204).* Unforgeability of the deployed scheme reduces to
Module-SIS with the forking extraction proved rather than assumed: a forgery
yields two self-target MSIS solutions on a shared commitment with distinct
challenges (#lean("ForkingDischarge.dregg_pq_is_eufcma_under_msis_discharged"),
resting on `MSISHard` and a stated realizability bridge). Correctness holds at
the real ML-DSA-65 dimension --- the ring
$R_q = ZZ_q [X] slash (X^256 + 1)$ at $q = 8380417$, modules $R_q^5$ and
$R_q^6$, an arbitrary matrix, an arbitrary Fiat--Shamir hash and challenge
sampler, and an arbitrary secret
(#lean("Fips204FullDim.fullDimApi_fips204")). The residual there is the
standard Dilithium rejection-termination fact: the seed carries the mask the
rejection loop accepted, so the probabilistic termination of that loop is
named as the boundary, not proved.

== The hybrid keystone

Finalization votes carry an ed25519 *and* ML-DSA hybrid signature, and the
composition is conjunctive: a certificate verifies only if both halves do.
The keystone is that a total classical break buys the adversary nothing ---
with the classical verifier replaced by one that accepts every string, the
hybrid remains unforgeable as long as the post-quantum half is
(#lean("HybridQuorum.hybrid_survives_classical_break")). The disjunction cuts
both ways: a still-unforgeable classical half carries the hybrid through a
future lattice break (#lean("HybridQuorum.hybrid_survives_pq_break")). The
hypotheses are discriminating --- with both halves broken, a concrete forgery
verifies (#lean("HybridQuorum.both_broken_is_forgeable")).

== Quantum-safe finality

The keystone reaches the ordering fabric (@sec-ordering) at two levels. At the
node, the vote collector admits a vote only if both signature halves verify,
and the quorum counts only admitted votes; under a total classical break, an
accepted quorum for a root still implies the honest committee signed it
(#lean("HybridFinalizationQuorum.hybrid_quorum_survives_classical_break")).
At the protocol, no two conflicting blocks finalize at a height under
$n > 3f$ together with the disjunction of the discrete-log and Module-SIS
floors (#lean("ConsensusSafety.consensus_safe_under_floor")); each honest
member's unforgeability is produced from either floor by
#lean("HybridCombiner.hybrid_secure_if_either_floor"). A quantum adversary
that breaks discrete log still faces MSIS, and the safety argument never
consults the broken half.

== The deployed surface and the one remaining hypothesis

The proofs above are about the shipped `dregg-pq` API, not a parallel model.
The refinement relation states that the modeled signature scheme reads back
exactly the API's public behavior --- key derivation, context-separated
signing, and the fail-closed Boolean verify --- and it holds by construction
(#lean("DreggPqRefinement.dregg_pq_refines_sigscheme")), with a
context-blind model exhibited as failing to refine. Domain separation is
carried by unforgeability: a signature minted for one context does not verify
under another (#lean("DreggPqRefinement.dregg_pq_ctx_domain_separated")).

Exactly one FIPS hypothesis remains on the deployed signature path:
#lean("DreggPqRefinement.Fips204Correct") --- for every seed, context, and
message, `verify (keygen seed) ctx msg (sign seed ctx msg) = true` ---
instantiated at the API backed by the `fips204` crate. It says the crate
implements the ML-DSA sign-to-verify round trip. It is load-bearing: without
it, correctness of the deployed scheme is underivable
(#lean("DreggPqRefinement.badApi_not_correct")). Its specification-level
counterpart is discharged at full dimension
(#lean("Fips204FullDim.fullDimApi_fips204")), so the open gap is
crate-versus-spec --- that the crate's byte-level behavior matches the modeled
algorithm --- rather than crate-versus-nothing. The KEM side carries no such
hypothesis; its round trip is a theorem about the extracted cores.

== What the development does not cover

The connected proof strengthens the floor; it does not eliminate it. Lattice
hardness itself is assumed, not proved: MLWE and MSIS enter as hypotheses at
stated boundaries and as recorded bit estimates in the parameter arithmetic,
and every quantitative figure above is conditional on those estimates. The
adversary model is the query model over unitary oracles; it counts oracle
calls and does not model side channels or implementation leakage. The
rejection-loop termination of ML-DSA signing is a named probabilistic
boundary. The extracted KEM and verify cores trust the `leanc`/FFI toolchain
that compiles them, and their full-dimension byte codecs (the $n = 256$ ring
interop) are named engineering residuals. Finally, the quantum posture of the
rows the floor table marks "generic speedups only" --- the hash, MAC, AEAD,
and FRI carriers --- is the recorded absence of a known structural attack,
not a theorem of this development.
