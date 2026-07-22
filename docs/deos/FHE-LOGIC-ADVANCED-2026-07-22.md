# Exact private logic in fhEgg: a ring-aware zero compiler, not “FOL for free”

**Status (2026-07-22):** one new specialization is proved in Lean, implemented
against real BFV ciphertexts, and measured with a retained fresh-key artifact.
This note separates that result from the larger research directions it suggests.

## Executive result

The corrected hybrid logic carrier reduces a bounded conjunction of equalities
to an encrypted nonnegative residual

\[
r = \sum_j (x_j-y_j)^2.
\]

When a proof certifies that each live SIMD slot satisfies `0 ≤ r ≤ B`, the
generic exact encrypted zero observation is

\[
Z_B(r)=\prod_{i=1}^{B}(i-r).
\]

It returns `B!` exactly when `r=0`, and zero for every certified positive
residual. For `B=8`, a generic balanced product needs seven
ciphertext-by-ciphertext multiplications. The new compiler specialization pairs
roots symmetric about nine:

\[
u=r^2-9r,
\qquad
Z_8(r)=(u^2+28u+160)(u^2+32u+252).
\]

That schedule needs **three** ciphertext multiplications: `r²`, `u²`, and the
final product. It has the same dependency depth as the generic balanced tree.
Including the eight residual squarings, the exact arithmetic ledger is therefore
`8 + 3 = 11` ciphertext multiplications, down from `8 + 7 = 15` and below the
15-multiplication balanced-Boolean reference ledger.

This is not a heuristic approximation:

- `CertifiedHybridProofFheSymmetricZeroObservation.lean` proves the polynomial
  identity over the entire deployed plaintext field, exactness on `0..8`, and
  the symbolic cost/depth statements with no axioms.
- `logic_zero_observation_symmetric.rs` refuses any residual certificate other
  than bound eight, checks the same-opening statement digest and cost manifest,
  and executes the exact schedule on real `fhe.rs` BFV ciphertexts.
- The integration test evaluates packed residuals `0, 1, 4, 6`; both the generic
  and specialized circuits decrypt to `[40320, 0, 0, 0]`.
- Eleven fresh-key release-mode samples on `persvati` measured an 82.028 ms
  generic median and a 38.317 ms specialized median for the **zero-conversion
  region only**, a 2.141× ratio. Raw JSON, scope, toolchain, hashes, and summary
  are retained in
  `docs/deos/artifacts/fhe-symmetric-eight-zero-2026-07-22/`.

The algebraic and primitive-count result is portable. The timing is one-machine,
one-parameter-set evidence, not an end-to-end latency claim and not a general
BFV noise theorem.

## What the existing formalization actually establishes

The surrounding Lean development already resolves a foundational ambiguity
that informal “logic directly to polynomials” pitches often hide: evaluating a
polynomial whose zero set represents truth is not the same operation as
producing a canonical encrypted Boolean truth value.

### Whole-field exact zero has a degree obstruction

For plaintext field `F_p`, any polynomial that evaluates to one at zero and zero
at every nonzero field element has degree at least `p-1`. The deployed modulus
is `p = 1,032,193`, so an arithmetic carrier made only of constants, addition,
subtraction, and multiplication needs multiplicative depth at least 20 for an
exact whole-field zero indicator. Fermat's construction
`1 - r^(p-1)` meets the semantic requirement, but it is not a cheap boundary
operation.

The theorem
`deployed_exact_zero_test_depth_at_least_twenty` formalizes this statement.
SIMD packing and rotations amortize many slots but do not change the scalar
polynomial-degree obstruction in each slot.

### A certified small domain changes the problem

If a proof binds the ciphertext to the same input opening used to establish
`0 ≤ r ≤ B < p`, `Z_B` is an exact finite-domain indicator. The unnormalized
`B! / 0` output avoids multiplication by the large field inverse of `B!`, which
was empirically hostile to the selected BFV noise envelope. A downstream
consumer can treat `B!` as the true scale rather than pretending that
normalization is free.

The range proof is therefore not decorative metadata. It is the premise that
makes the low-degree zero circuit sound. The implementation's
`SameOpeningReceipt` presently binds digests supplied by an external verifier;
it does not itself execute that proof verifier. Closing that producer/verifier
seam remains necessary before the receipt is a cryptographic end-to-end claim.

### Opening the residual is cheap computation but different leakage

The alternative n-of-n threshold boundary opens `r` and tests zero outside FHE.
It avoids the encrypted conversion cost, but reveals the complete residual in
every live slot—not merely the final truth bit. If an enclosing encrypted
program needs the result, it must re-encrypt after the intermediate predicate
has become public to the opening participants.

Threshold decryption is also not secure merely because shares are split.
Chosen-plaintext attacks against distributed decryption and the need for
properly distributed smudging are concrete protocol obligations; see the
analysis of threshold lattice schemes by Boudgoust and Scholl
([IACR 2024/116](https://eprint.iacr.org/2024/116)). fhEgg's share transcript,
bounds, proofs, and transport should be assessed against that threat model
before a threshold opening is described as production private.

## The new compiler law

For arbitrary roots `a,b` in any commutative ring,

\[
(a-r)(b-r)=r^2-(a+b)r+ab.
\]

For a consecutive interval `1..B`, pairing `i` with `B+1-i` gives every pair
the same encrypted quadratic

\[
u=r^2-(B+1)r,
\qquad
(i-r)(B+1-i-r)=u+i(B+1-i).
\]

The shared `u` turns a product of `B` encrypted affine factors into a product of
roughly `B/2` affine functions of one shared encrypted value. For even `B`, the
straight paired schedule uses one multiplication for `r²` and `B/2-1` to
multiply the paired factors: roughly half the generic `B-1` count. Further
common-subexpression elimination can do better at particular bounds.

At `B=8`, the four factors are `u+8`, `u+14`, `u+18`, `u+20`. Pairing them by
equal coefficient sums gives

\[
(u+8)(u+20)=u^2+28u+160,
\]

\[
(u+14)(u+18)=u^2+32u+252.
\]

Both blocks reuse the same `u²`. This is the extra multiplication saved beyond
ordinary root pairing.

| Exact encrypted strategy for eight equalities | Residual ct×ct | Zero-conversion ct×ct | Total ct×ct | Output depth including residual | What is revealed by conversion |
|---|---:|---:|---:|---:|---|
| Balanced Boolean equalities/conjunction | — | — | 15 | 4 | nothing |
| Residual + generic `Z₈` | 8 | 7 | 15 | 4 | nothing |
| Residual + symmetric/CSE `Z₈` | 8 | 3 | **11** | 4 | nothing |
| Residual + threshold open | 8 | 0 | 8 | 1 before opening | complete residual |
| Whole-field Fermat zero | 8 | high; degree ≥ `p-1` | not competitive here | ≥21 including residual | nothing |
| TFHE/FHEW programmable bootstrap | carrier crossing required | often one LUT/PBS after crossing | not yet measured in fhEgg | refreshes noise | nothing if kept encrypted |

The table deliberately does not convert all rows to milliseconds. The carriers,
keys, parameter sets, and leakage boundaries differ; an operation count is only
comparable inside a declared carrier and measurement scope.

## Measurement receipt

The retained BFV artifact uses the existing depth-oriented
`BfvParams::correlation_set()` (degree 8192, plaintext modulus 1,032,193). Each
sample starts with fresh keys and ciphertexts. The timed region includes
plaintext-constant encoding, ciphertext/plaintext arithmetic,
ciphertext-by-ciphertext multiplication, relinearization, and local allocation
inside conversion. It excludes setup and keys, input encoding/encryption,
residual evaluation, same-opening verification, output decryption, threshold
shares/combine, transport, process startup, and build time.

| Metric, 11 fresh-key samples | Generic `Z₈` | Symmetric/CSE `Z₈` |
|---|---:|---:|
| Minimum | 78.150 ms | 34.761 ms |
| Median | 82.028 ms | 38.317 ms |
| Mean | 108.393 ms | 46.250 ms |
| Maximum | 217.102 ms | 80.744 ms |
| Library-reported observed noise bits | 157–160 | 158–160 |

All output vectors were exact. The noise figures are reported without assigning
them a security-margin interpretation: they are a test-only oracle observation,
not a proof that every admissible input, distributed key, or composition remains
decryptable. A production compiler needs a parameter/noise certificate in
addition to the polynomial certificate.

## Better carriers for different observation boundaries

There is no universal winner called “FOL.” The useful primitive depends on
whether truth must stay encrypted, the size of the certified domain, the number
of packed slots, and which carrier already holds the data.

### Programmable bootstrapping and lookup tables

TFHE/FHEW-style programmable bootstrapping can evaluate a unary lookup table
while refreshing noise. Exact zero on a suitably encoded bounded scalar is a
natural LUT. TFHE-rs exposes programmable bootstrapping and exact integer/
Boolean evaluation ([official repository](https://github.com/zama-ai/tfhe-rs));
OpenFHE exposes `EvalFunc` for arbitrary functions represented by lookup tables
([BinFHE API](https://openfhe-development.readthedocs.io/en/latest/api/classlbcrypto_1_1BinFHEContext.html)).
The TFHE Processor work demonstrates richer LUT-oriented processor construction
and also documents the practical limits of functional-bootstrap patterns
([IACR 2024/1201](https://eprint.iacr.org/2024/1201)).

For fhEgg this is a promising encrypted-observation target, not a completed
replacement. The live residual is BFV; BFV-to-TFHE scheme switching, switching
keys, distributed custody, failure probability, device memory, and measured
latency are not present in this lane. “One PBS” is not “free.”

Recent large-precision functional bootstrapping research constructs an external
product tree and a BFV-to-LFBS switching path, reporting large speedups over
traditional TFBS for 12- and 16-bit functions
([IACR 2025/022](https://eprint.iacr.org/2025/022)). It is relevant to bounded
logic programs, but its preprint performance is not evidence about the current
fhEgg implementation.

### Packed BFV/BGV polynomial evaluation

When many independent residuals already occupy BFV SIMD slots, the same
polynomial schedule evaluates all of them at once. Packing improves amortized
throughput but neither degree nor depth per slot. Compiler work should therefore
combine packing with ring-aware polynomial scheduling rather than cite SIMD as
a semantic shortcut.

HEIR already lowers polynomial evaluation through Horner and
Paterson–Stockmeyer strategies
([pass documentation](https://heir.dev/docs/passes/)). The new contribution here
is narrower and compositional: recognize a certified consecutive root set,
derive a symmetry/CSE schedule, and emit a proof that the replacement is the
same polynomial. It should eventually become an optimization in an IR such as
FHir or HEIR, not remain a hand-written `B=8` function.

### Proof/FHE hybrids and verifiable FHE

The clean division of labor is:

1. a proof establishes range, source binding, and same opening;
2. FHE evaluates the private data-independent arithmetic;
3. observation either remains encrypted through a certified bounded circuit or
   crosses an explicitly priced threshold/PBS boundary;
4. a receipt records exactly which boundary was used and what it leaked.

Proofs of correct FHE evaluation can strengthen integrity, but do not by
themselves guarantee output privacy, distributed-key security, or adequate
noise margin. Relevant concrete systems include lattice-SNARK verifiable FHE
([IACR 2024/032](https://eprint.iacr.org/2024/032)), Greco's proof of valid RLWE
ciphertext formation ([IACR 2024/594](https://eprint.iacr.org/2024/594)), and
verifiable approximate homomorphic encryption
([IACR 2025/286](https://eprint.iacr.org/2025/286)). These works supply candidate
components; none erases the need to state fhEgg's exact relation and leakage
boundary.

## Recommended next implementation

The immediate next contribution is a proof-carrying bounded-zero compiler pass:

1. **Recognize** consecutive certified root products and reject a missing or
   mismatched range/same-opening certificate.
2. **Pair** roots with equal sums, exposing `u = r²-(B+1)r`.
3. **Search** addition/multiplication schedules with a multi-objective cost:
   ciphertext multiplication count, dependency depth, plaintext coefficient
   magnitude/noise estimate, rotations, key material, and device memory.
4. **Emit** a small algebraic certificate checked in Lean, rather than trusting
   the optimizer's rewrite.
5. **Emit** a carrier-specific parameter/noise obligation. A low multiplication
   count with hostile constants is not automatically a viable BFV circuit.
6. **Benchmark** generic, specialized, PBS/scheme-switched, and threshold-open
   strategies under the same input shape, with setup and boundary costs broken
   out rather than hidden.

The compiler should choose among strategies; it should not canonize one of them
as “logic.” A private final predicate may favor PBS or the specialized BFV
polynomial. An intentionally public final decision may favor threshold opening.
A large arbitrary field input cannot borrow the small-domain circuit without a
range proof.

## Residual assurance ledger

What is closed in this lane:

- exact ring identity for the bound-eight optimization;
- exact finite-domain semantics on certified values `0..8`;
- exact symbolic primitive count and multiplicative depth;
- fail-closed bound, manifest, modulus, and same-opening-digest checks;
- real BFV execution on four SIMD values;
- retained repeated timing/raw-output receipt.

What is not yet closed:

- the external proof verifier behind `SameOpeningReceipt`;
- a formal BFV noise/decryption theorem for the emitted schedule;
- distributed-key execution of this exact conversion;
- BFV↔TFHE switching and a measured PBS/LUT alternative;
- malicious threshold-decryption security under the current transport and
  smudging choices;
- general certified schedule generation for arbitrary bounds;
- end-to-end latency including setup, proof verification, encrypted residual,
  observation, and network transport.

The result is consequently stronger than a white-paper claim and smaller than
a production privacy system. It is a checked compiler optimization with an
executable receipt—and a concrete path from “logic as a polynomial” to logic as
an audited, carrier-aware program.
