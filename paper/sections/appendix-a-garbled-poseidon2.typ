// =============================================================================
// Poseidon2 as Garbling Function for STARK-Provable Garbled Circuits
// =============================================================================

#import "../defs.typ": lean
= Poseidon2 as garbling function for STARK-provable garbled circuits <app-garbled>

This appendix details the garbled rung of the disclosure dial (@sec-guards): the
two-party gate at which each party learns the verdict and nothing else. The Lean
specification is `metatheory/Dregg2/Crypto/GarbledJoint.lean` --- correctness
(#lean("GarbledJoint.garbled_correct")), input privacy
(#lean("GarbledJoint.garbled_input_private")), the joint-turn weld
(#lean("GarbledJoint.joint_turn_private_gate")), and the disclosure floor pinned
to acceptance-only (#lean("GarbledJoint.garbledDialFloor_is_bot")). The
cryptographic realization is the garbling machinery in `circuit/src/garbled.rs`.
Its proof path is the descriptor #lean("GarbledEvalEmit.garbledEvalDesc")
(`metatheory/Dregg2/Circuit/Emit/GarbledEvalEmit.lean`), authored in Lean and
proved through `prove_vm_descriptor2`, with its correctness and mutation gate in
`circuit-prove/tests/garbled_eval_emit_gate.rs`.

== Motivation

Standard garbled-circuit constructions instantiate the garbling PRF with AES or
SHA-256, primitives optimized for hardware execution but expensive inside
arithmetic STARKs. Poseidon2 @poseidon2 is a permutation designed for efficient
arithmetization over prime fields. Used as the garbling function in a Yao-style
garbled circuit @yao86, it keeps the evaluation trace natively provable in a
BabyBear STARK. The result is a verifiable garbled circuit @jawurek13 whose
per-gate constraint cost is roughly three orders of magnitude below an AES-based
equivalent (@app-cost).

== The construction

=== Notation

Let $FF_p$ denote the BabyBear field ($p = 2^(31) - 2^(27) + 1$). A _label_ is a
vector $bold(l) in FF_p^8$: eight field elements, approximately 248 bits of
entropy. For a wire $w$ carrying a Boolean value $b in {0,1}$, $bold(l)_w^b$ is
the label encoding value $b$ on wire $w$. The function $"P2": FF_p^(16) ->
FF_p^8$ is the first 8 output elements of a width-16 Poseidon2 permutation with
S-box $x^7$ and 21 rounds (8 external, 13 internal), the parameterization pinned
in `circuit/src/poseidon2.rs`.

=== Gate garbling

For a gate $g$ with left input wire $a$, right input wire $b$, output wire $c$,
and Boolean function $f_g : {0,1}^2 -> {0,1}$, the garbling key for input pair
$(i,j)$ is

$ "key"_(i,j,g) = "P2"(bold(l)_a^i || bold(l)_b^j [0..6] || (bold(l)_b^j [7] + g)). $

The 16-element permutation input packs the full left label, the first seven
elements of the right label, and, in the final position, the right label's
eighth element plus the gate index (`garbling_hash` in
`circuit/src/garbled.rs`). Two distinct gates therefore feed the permutation
distinct inputs except on a collision of the wire labels themselves. The
garbled table consists of four ciphertexts,

$ bold(C)_g^(i,j) = bold(l)_c^(f_g (i,j)) + "key"_(i,j,g) quad forall (i,j) in {0,1}^2, $

where $+$ is component-wise addition in $FF_p$. Evaluation recovers the output
label by component-wise field subtraction:

$ bold(C)_g^(i,j) - "key"_(i,j,g) = bold(l)_c^(f_g (i,j)). $

=== Encryption over the field <app-field-pad>

A garbled table entry is a one-time pad: each ciphertext masks an output label
with a key used exactly once. Classical constructions take the pad over the XOR
group ${0,1}^lambda$; this construction takes it over the additive group of
$FF_p^8$. Both are one-time pads over a group, and the hiding argument is the
same: if the mask is indistinguishable from a uniform group element, adding it
hides the label. Under the PRF assumption each of a gate's four keys is an
independent pseudorandom vector --- the four permutation inputs are distinct ---
so each ciphertext individually reveals nothing about the label it masks.

The field pad and the XOR pad differ in two respects, one gained and one given
up. Gained: the field pad stays inside the arithmetization. Decryption,
$"output" = "table entry" - "hash"$, is a single linear constraint per element
in a BabyBear AIR, and it is exactly the decryption constraint the deployed
descriptor enforces (#lean("GarbledEvalEmit.decryption_body_zero_iff")). A
bitwise XOR over the 32-bit integer representations would leave the field (the
result can exceed $p$) and would cost a bit decomposition of roughly 31 binary
constraints per element --- the cost the choice of Poseidon2 is meant to avoid.
Given up: the two-torsion structure of XOR ($x xor x = 0$), on which free-XOR
optimizations rely (@app-prior). The construction samples every wire's two
labels independently and correlates nothing across wires, so no algebraic
relation spans two ciphertexts for the field structure to preserve --- and no
free-XOR-style optimization is available. Every gate carries four ciphertexts.

=== Point-and-permute

The garbled table rows are ordered by the least significant bit of the first
element of each input label: $pi(bold(l)) = bold(l)[0] mod 2$. The evaluator
uses $(pi(bold(l)_a), pi(bold(l)_b))$ as a 2-bit index and performs one
decryption instead of four trial decryptions. Label generation forces opposite
color bits: the two labels of a wire are sampled independently, then the first
element's low bit is cleared on the zero-label and set on the one-label
(`random_label_pair`).

=== The comparison circuit

The deployed application is a private threshold comparison: the garbler holds a
threshold $t$, the evaluator holds a value $v$, and the joint predicate is $v
>= t$ over 31-bit values. The circuit is an LSB-first borrow chain
(`garble_comparison_circuit`): the borrow out of bit position $i$ is a Boolean
function of the borrow into it and the evaluator's bit $v_i$, with the garbler's
known bit $t_i$ wired into the gate's truth table. Each bit position is one
two-input garbled gate, so a 31-bit comparison is 31 gates; the garbler's input
occupies no gates at all. The comparison holds exactly when the final borrow is
zero, so the zero-label of the last borrow wire is the "true" output label.

Two commitments bind the artifact. The circuit commitment is a domain-separated
Poseidon2 sponge hash (`WideHash`: eight field elements, approximately 124-bit
birthday collision resistance) over all garbled table entries; each output
label is committed by the same hash. The evaluator's input labels are specified
to arrive by oblivious transfer; the in-tree tests hand the evaluator its labels
directly, and the repository contains no wire-level OT implementation.

== Security argument

=== Garbling privacy

Privacy is argued in the simulation framework of Bellare, Hoang, and Rogaway
@bhr12.

#quote(block: true)[
*Theorem (informal).* If Poseidon2 (width-16, $x^7$, 21 rounds over $FF_p$)
truncated to its first eight outputs is a pseudorandom function of its
16-element input, then the construction above satisfies garbling privacy
(prv.sim) with computational security $lambda >= 124$ bits at the garbling
layer.
]

*Proof sketch.* The simulator, given only the circuit topology and the output
labels of the true output, must produce garbled tables indistinguishable from
real ones. Under the PRF assumption on P2:

+ For each gate $g$ and each input pair $(i,j)$ off the evaluation path, the
  ciphertext $bold(C)_g^(i,j) = bold(l)_c^(f_g (i,j)) + "key"_(i,j,g)$ is
  indistinguishable from uniform: the key is pseudorandom, and adding a fixed
  value to a uniform element of $FF_p^8$ yields a uniform element (the group
  one-time pad of @app-field-pad).

+ For the single on-path row $(i^*, j^*)$, the evaluator recovers
  $bold(l)_c^(f_g (i^*, j^*))$ and learns nothing about the opposite label,
  whose rows remain pseudorandom.

+ Gates are domain-separated through the key's final input element (the gate
  index added to a label element): two gates collide on a permutation input
  only if their wire labels collide, which the 248-bit label space makes
  negligible.

The 248-bit label space gives a birthday bound of $2^(124)$: an adversary must
evaluate P2 on the order of $2^(124)$ distinct inputs before observing a
collision that could distinguish real garbled tables from simulated ones.

=== The mechanized privacy carrier

The Lean development states the privacy property over an abstract garbling
kernel rather than the concrete permutation.
#lean("GarbledJoint.garbled_input_private") proves that the evaluator's
transcript equals a simulator applied to the output bit alone;
#lean("GarbledJoint.garbled_input_private_indistinguishable") sharpens this to:
two runs with the same outcome produce identical transcripts, whatever the
private inputs. #lean("GarbledJoint.joint_turn_private_gate") welds the kernel
to the joint turn: a two-cell turn whose admission gate is a garbled predicate
admits exactly when the joint condition holds, discloses only that one bit, and
inherits the joint turn's atomicity unchanged. The floor of the disclosure dial
for this rung is acceptance-only, formally the dial's bottom
(#lean("GarbledJoint.garbledDialFloor_is_bot")). These theorems model the
protocol --- garble, evaluate, transcript --- not the STARK trace layout; the
PRF assumption on Poseidon2 is the carrier connecting the model to the concrete
construction.

=== What the STARK proves <app-stark-scope>

The proof layer wraps evaluation in a STARK: the evaluator proves it performed
the decryption chain correctly, so a third party can check the verdict without
trusting the evaluator's report. The circuit statement is the 56-column
descriptor #lean("GarbledEvalEmit.garbledEvalDesc"), authored in Lean with its
emitted wire string byte-pinned by a `#guard`, and proved through
`prove_vm_descriptor2`, the production descriptor prover. One trace row is one
gate evaluation. The constraint families are:

- decryption correctness on every non-padding row --- $"output"(i) = "table
  entry"(i) - "hash"(i)$ for each of the eight label elements, the
  field-subtraction decryption of @app-field-pad
  (#lean("GarbledEvalEmit.decryption_body_zero_iff"));
- booleanity of the six selector columns and exclusivity of the four gate-type
  flags;
- wire chaining across rows: where a row's chain flag is set, the next row's
  left label equals this row's output label (eight two-row window gates);
- first-row binding of the circuit commitment and output-label hash to the
  public inputs, and a first-row gate-index boundary (the every-row constraint
  families are additionally re-lowered as last-row boundaries, so no row
  escapes them).

The gate test `circuit-prove/tests/garbled_eval_emit_gate.rs` decodes the
descriptor, checks it against an independently hand-built twin, proves an
honest two-gate evaluation and re-verifies it, then refuses six mutated
witnesses --- a forged commitment input, a forged table ciphertext, a
non-boolean selector, an ambiguous gate type, a broken wire chain, and a forged
first-row boundary --- each mutation biting a distinct constraint family.

Three scope facts bound what such a proof establishes; each is named in the
artifact itself.

+ *The garbling hash is not constrained in-circuit.* The hash columns are free
  witness values; the digests --- the per-gate P2 keys and both commitments ---
  are computed by the witness generator in `circuit/src/garbled.rs`. The AIR
  proves the decryption algebra over those digests, and the digest-correctness
  binding is a named executor-verified carrier, stated as such in
  `GarbledEvalEmit.lean`.

+ *The commitments are bound in-circuit by a four-element prefix* of the
  eight-element digest. The full-digest equality is specified as a
  verifier-side check that has not been written; the repository prices the
  enforced prefix at roughly 62 bits.

+ *The path has no live consumer.* The descriptor, its gate test, and the
  garbling machinery exist and are exercised; no deployed surface currently
  issues or verifies garbled-evaluation proofs.

=== Composed security posture

The 124-bit figure above is a privacy bound at the garbling layer; it is not
the security level of the composed artifact. A garbled-evaluation proof is
checked by the same engine as every other proof in the system, and the engine's
quantified posture bounds what acceptance is worth. At the deployed recursion
apex (logarithmic blowup 6, 19 queries, 16 bits of proof-of-work grinding,
tables floored at $2^(16)$ rows), the analysis of record prices the apex at
about 58 bits under the BCIKS20 accounting and about 71 bits under BCSS25
(`docs/reference/FRI-BOTH-WIN-LEVERS.md`). Those figures are analytic bounds on
a supplied proof; the mechanized ledger carries no adversary or grinding model.
The composed posture is therefore the minimum across layers: about 58 bits of
engine soundness at deployed parameters, about 62 bits of enforced commitment
binding, and 124 bits of garbling privacy. The engine posture and the
commitment prefix, not the garbling function, set the composed level; both have
identified, costed levers in the same analysis.

== Why Poseidon2 (not AES, not SHA-256) <app-cost>

The choice of garbling PRF is dictated by constraint cost inside a BabyBear
STARK. The figures below are analytic estimates --- constraint counts derived
from each primitive's structure, not measured prover benchmarks. They price the
design point at which the garbling hash is proved in-circuit; in the deployed
descriptor the hash is an executor-verified carrier (@app-stark-scope), so the
estimates bound the cost of closing that seam and explain why the seam is
closable at all.

*AES-128.* Each of the 160 S-boxes (10 rounds, 16 bytes) computes an inversion
in $"GF"(2^8)$; expressed over $FF_p$ this costs several hundred to a thousand
multiplication constraints per S-box, on the order of $10^5$ constraints per
AES call.

*SHA-256.* The compression function performs roughly 1,100 32-bit AND, XOR,
and rotate operations; each requires bit decomposition in a prime field. With
gadgets that amortize decomposition across related operations, the cost is on
the order of $2.5 times 10^4$ constraints per call.

*Poseidon2 (width-16, BabyBear).* The permutation is native to the STARK: 141
S-boxes (8 external rounds of 16 lanes plus 13 internal rounds of one lane),
each a single degree-7 constraint, with the linear layers constraint-free in
the AIR --- on the order of $1.5 times 10^2$ constraints per permutation.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, right),
    table.header([*Garbling PRF*], [*Constraints/call (est.)*], [*31-gate circuit (est.)*]),
    [AES-128], [$tilde 100,000$], [$tilde 3,100,000$],
    [SHA-256], [$tilde 25,000$], [$tilde 775,000$],
    [Poseidon2], [$tilde 150$], [$tilde 4,650$],
  ),
  caption: [Analytic constraint-cost estimates per garbled-gate decryption
  inside a BabyBear STARK. The 31-gate column is the deployed comparison
  circuit (one gate per bit of a 31-bit comparison). No entry is a measured
  benchmark.],
)

The gap of roughly three orders of magnitude is the design's premise: with
Poseidon2 the garbling hash is affordable in-circuit; with AES it is not.

== Concrete parameters

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Parameter*], [*Value*]),
    [Label entropy], [8 $times$ BabyBear $approx$ 248 bits],
    [Circuit topology], [31 gates (LSB-first borrow chain, threshold wired into truth tables)],
    [Garbled table size], [31 gates $times$ 4 rows $times$ 32 bytes = 3,968 bytes],
    [Commitments], [`WideHash`: 8-element Poseidon2 sponge, $tilde$124-bit birthday collision resistance],
    [STARK trace dimensions], [32 rows $times$ 56 columns],
    [In-circuit public inputs], [8 field elements (a 4-element prefix of each commitment)],
  ),
  caption: [Parameters of the 31-bit comparison garbled circuit, derived from
  `circuit/src/garbled.rs` and `GarbledEvalEmit.lean` at the revision of
  record.],
)

Proof size and timing are deliberately not restated. Earlier figures for this
construction predate both the cutover to the descriptor prover and the current
GPU prover, and no re-measurement accompanies this revision.

== Limitations and assumptions

=== One-time evaluation

Each garbled circuit supports exactly one evaluation, the standard Yao
limitation. A wire's labels encode a single Boolean value; reuse would let the
evaluator learn both labels and decrypt all four rows of downstream gates.
Repeated comparisons against the same threshold require freshly garbled
circuits.

=== Evaluator learns the output

The evaluator necessarily learns the comparison result: the output labels ship
with the circuit for decoding, and the evaluator identifies which one it
recovered. Only the threshold, wired into the truth tables by the garbler,
stays hidden from the evaluator. The STARK proof conveys the result to third
parties without revealing anything else.

=== Semi-honest security

The construction provides security against semi-honest adversaries: both
parties follow the protocol but may try to extract information from their
views. Against a malicious garbler --- one who garbles an incorrect circuit ---
standard techniques exist: cut-and-choose (garble $kappa$ circuits, open half
for inspection, evaluate the rest) and dual execution (both parties garble and
evaluate, then compare via an equality test, with one bit of leakage). Either
composes with STARK verification, which proves correct evaluation of whichever
circuit is selected. Neither is implemented in the repository.

=== PRF assumption on Poseidon2

Poseidon2 @poseidon2 is a 2023 construction. The permutation has been analyzed
for collision resistance, preimage resistance, and algebraic attacks
(Gröbner basis, interpolation, differential and linear), with claimed
complexities above $2^(128)$ for this parameterization, but it has not received
the decades of cryptanalysis applied to AES. A future break of Poseidon2's PRF
security would invalidate garbling privacy; it would not affect the integrity
properties of the surrounding STARK.

== Relation to prior work <app-prior>

*Yao @yao86* introduced garbled circuits as the foundational technique for
secure two-party computation. The construction here follows the standard Yao
framework, differing in the garbling PRF and in the encryption group.

*Bellare, Hoang, and Rogaway @bhr12* formalized garbling-scheme security via
simulation-based definitions. The security argument above targets prv.sim: the
garbled circuit together with the output labels is simulatable from the circuit
topology and the output alone.

*Jawurek, Kerschbaum, and Orlandi @jawurek13* introduced verifiable garbled
circuits, where the evaluator proves correct evaluation in zero knowledge,
using Sigma protocols and cut-and-choose. Replacing that mechanism with a STARK
yields a non-interactive, publicly verifiable, succinct proof of evaluation.

*Grassi et al. @poseidon2* designed Poseidon2 as an arithmetization-friendly
hash for use inside SNARKs and STARKs. The construction here extends its role
from commitment and hashing to garbling: a PRF for encryption rather than a
compression function for Merkle trees.

*CAPSS @capss24* builds signatures from arithmetization-oriented permutations
inside proof systems --- the closest prior work in spirit: an AO primitive
supplying cryptographic functionality (signatures there, garbling here) inside
an arithmetic circuit.

*Free XOR and half-gates* (Kolesnikov and Schneider 2008; Zahur, Rosulek, and
Evans 2015) reduce garbled-circuit size using the involutive structure of XOR
over correlated labels (a global offset). The field-additive encryption used
here samples labels independently and has no two-torsion, so these
optimizations do not transfer; every gate carries four ciphertexts. For the
31-gate comparison circuit the absolute cost is small.

== Security definitions

For completeness, the formal target.

*Definition (prv.sim, adapted from @bhr12).* A garbling scheme $cal(G) =
("Garble", "Eval", "Decode")$ satisfies prv.sim if there exists a PPT simulator
$cal(S)$ such that for all PPT distinguishers $cal(D)$, circuits $C$, and
inputs $x$:

$ |Pr[cal(D)("Garble"(C, x)) = 1] - Pr[cal(D)(cal(S)(C, C(x))) = 1]| <= "negl"(lambda) $

where $"Garble"(C, x)$ outputs the garbled circuit $tilde(C)$ and input labels
$tilde(x)$, and $cal(S)(C, C(x))$ receives only the circuit topology and the
output value.

*Claim.* Under the assumption that $"P2": FF_p^(16) -> FF_p^8$ (the first 8
outputs of the width-16 Poseidon2 permutation) is a $(t, epsilon)$-secure PRF
for $t = 2^(124)$ and $epsilon = 2^(-124)$, the construction satisfies prv.sim
with $lambda = 124$ at the garbling layer.

The reduction is standard: the simulator replaces all non-output labels with
fresh random values and computes ciphertexts as $"P2"("random input") +
"random label"$; distinguishing real from simulated tables then requires
distinguishing P2 outputs from uniform, contradicting the PRF assumption. The
composed posture of a proof-carrying verdict remains as stated in
@app-stark-scope: the engine's quantified soundness at the deployed apex, not
this bound, is the governing figure.
