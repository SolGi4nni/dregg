# fhEgg / shielded systems research frontier — 2026-07-22

This is an implementation-facing research pass, not a literature catalogue. It
asks which primary results published or revised in 2025–2026 change the next
fhEgg, HidingFRI, Dark Bazaar, game-operation, and portable-GPU cuts at the
current tree. “Latest” means discoverable by Kagi plus primary-source follow-up
on 2026-07-22; it is not a claim that every 2026 preprint has been found.

The local reading corpus is under `tmp/pdfs/frontier-2026/`. That directory is
gitignored working material. Durable citations below point to the authors,
IACR, arXiv, NIST, or the publishing venue.

## Result in one sentence

The most valuable immediate change is to make the existing dealerless fhEgg
formation explicitly **chosen-input-VOLE-shaped**; the most valuable new apex
is a **t-private collaborative transparent/PQ prover** over the existing
HidingFRI/WGPU substrate; and the most important threshold-FHE correction is to
adopt a named malicious/UC decryption profile instead of accumulating local
proof patches around ad-hoc partial decryption.

The GPU papers largely validate the direction already visible at HEAD:
resident data, fused workflows, batched independent inputs, and memory-hierarchy
measurement matter more than isolated arithmetic-kernel wins. The newest FRI
soundness survey also validates, rather than overturns, Dregg's current honest
ledger: capacity-radius folklore is not a proven deployment budget, and the
Johnson/proven columns must remain separate.

## Adoption labels

- **Adapt now** — the paper exposes an interface that matches a live named seam.
- **Prototype beside production** — the construction is compelling, but its
  statement/security model does not yet equal Dregg's.
- **Research direction** — useful design evidence, not an implementation recipe.
- **Warning** — a result that prevents an attractive but unsound shortcut.

## Immediate adoption matrix

| Rank | Construction | Label | Existing seam | Next concrete artifact | Falsifier before promotion |
|---|---|---|---|---|---|
| A | chosen-input VOLE boundary, with LogVOLE/C-VOLE candidates | **Adapt the boundary now; prototype the provider** | `fhegg-fhe/src/mpc_distributed_mac.rs` has the exact cross-term algebra but only a test ideal-OT driver | a receipt-returning `PairwiseCrossTermProvider` whose output is bound to `DistributedMacManifest`, the candidate manifest, ordered sender/receiver identities, and one-use session | omission, direction swap, chosen-input substitution, replay, reused sender setup under a new roster, and a diagonal-only implementation must refuse |
| B | malicious/UC threshold-FHE decryption and robust threshold profiles | **Adapt now** | `distributed_bfv_correlation.rs` has real n-of-n DKG and multiparty relinearization, but lacks transferable proofs of hidden-short/correct contributions, encrypted-bitness/application validity, and decryption-share correctness | a versioned `ThresholdFheSecurityProfile` plus verified DKG/relin contribution, admissible-ciphertext, encrypted application-input, and decryption certificates | malformed ciphertext share, wrong bit/order shape, wrong key epoch, wrong relin key, omitted party, partial-decryption leakage, and cross-profile transcript replay |
| C | t-private code-based collaborative SNARK + distributed FRI/BaseFold work | **Prototype beside production** | HidingFRI is hiding to the verifier and its full PCS commitment path has a WGPU hook, but one source viewer still owns the complete witness | `DistributedHidingFriManifest`: witness shards, collaborative masking, local WGPU commitments, authenticated partial roots, batched global fold, accountability evidence, and an exact monolithic-proof differential | no worker coalition up to the selected threshold reconstructs the witness; corrupt partial fold is attributable/refused; output proof equals the accepted public statement; reordered/missing shards refuse |
| D | corrected lattice verifiable mixnet | **Prototype beside production** | Dregg already has private shuffle/preference/game proof surfaces, but classical group constructions are not the final PQ primitive | a typed `PrivatePermutation`/`VerifiablePermutation` game operation shared by Dungeon, guild voting, matchmaking, and Bazaar allocation | reproduce the ring-splitting attack against the older relation, then show it fails against the selected construction; injected/dropped/substituted committed items refuse |
| E | resident/fused GPU FHE and ZK workflows | **Adapt now** | WGPU NTT, PBS/CMUX, HidingFRI fold, and whole-tree Merkle paths exist, but some compositions still cross host boundaries | persistent arenas, fused stage groups, packed/interleaved Merkle layouts, batch-aware PBS scheduling, and portable counters for uploads, dispatches, waits, and readbacks | exact CPU/tfhe-rs parity; no secret-dependent indexing; cold and warm measurements; explicit CPU-fallback counters; promotion only when the whole operation, not one kernel, wins |

## 1. Dealerless authenticated bits: use a VOLE boundary, not a nicer fake OT

### Primary result

[LogVOLE, ePrint 2026/925](https://eprint.iacr.org/2026/925) gives
chosen-input VOLE in which a receiver privately chooses a vector `x`, a sender
fixes `Δ`, and they obtain additive shares of `x·Δ` with polylogarithmic
communication under Ring-LWE. It includes separate staged and non-interactive
public-key modes and a malicious extension in the random-oracle model. The
paper's Section 10 is load-bearing: the malicious theorem disables the
golden-seed optimization, certifies sender setup, and needs receiver-input
extraction/consistency. The evaluated implementation is the optimized
**semi-honest** golden-seed protocol over a 55-bit prime field; the authors do
not implement the malicious construction and estimate materially higher cost.
An exact GF(2^128) provider therefore still needs a binary-extension-field
instantiation, security analysis, and implementation.

This is unusually close to fhEgg's live algebra. In
`mpc_distributed_mac.rs`, party `i` owns `α_i`, party `j` owns bit vector
`x_j`, and the missing term is exactly `α_i·x_j`. The current
`PairwiseOtSenderDriver` shape should become a more semantic provider boundary,
not gain a production implementation that merely co-locates both secrets.

[Committed Vector OLE, ePrint 2025/1037](https://eprint.iacr.org/2025/1037)
is the second relevant shape: its ideal functionality has native `F_(2^128)`
semantics and binds a precommitted vector consistently across counterparties.
This can link the party-local candidate commitment barrier to MAC formation
instead of treating “same bits” as a comment. Its concrete protocol is still
stated in correlation/OT hybrid models, including a selective-failure leakage
surface, and does not supply a turnkey PQ base-correlation stack.

[A maliciously secure post-quantum OPRF from Crypto Dark Matter, ePrint
2026/533](https://eprint.iacr.org/2026/533) contributes authenticated VOLE and
shared-input authenticated VOLE interfaces plus useful cut-and-choose and
correlated-randomness techniques. Its implemented OPRF uses `F_(2^256)` and
ML-KEM base OTs, not a benchmarked GF(2^128) provider. It is supporting
machinery, not a drop-in proof that every LogVOLE mode has Dregg's desired
PQ/malicious statement.

### Exact implementation cut

1. Replace the production-facing name `PairwiseOtSenderDriver` with an
   interface that states the relation it must realize:
   `CrossTermShare(sender α_i, receiver x_j) -> (u_ij, v_ij, transcript)` with
   `u_ij ⊕ v_ij = α_i·x_j` in the exact GF(2^128) representation.
2. Bind the parties' authenticated receipt digests to `DistributedMacManifest`,
   candidate-manifest root, ordered roster identities, direction, vector
   length, security profile, and a one-use setup/session id.
3. Make the ideal adapter `#[cfg(test)]`; production construction must be
   impossible without a concrete provider and verifier.
4. If committed-input VOLE is used, bind the receiver input commitment to the
   already-sealed `CandidateCommitmentMessage`, not a newly caller-supplied
   digest.
5. Carry mutual receipt agreement into the final distributed-MAC certificate;
   “the call returned bytes” is not a formation certificate. LogVOLE proves a
   simulation-security statement, not a publicly transferable transcript. A
   third-party verifier would be an additional Dregg protocol, not a free
   consequence of the paper.

## 2. Threshold BFV/TFHE: select a security profile before adding proofs

### Primary results

[Threshold (Fully) Homomorphic Encryption, ePrint
2025/699](https://eprint.iacr.org/2025/699) is a useful preliminary Zama/NIST
construction manual:
robust threshold key generation and decryption for BGV, BFV, and TFHE in named
malicious-adversary/honest-majority regimes, with generic offline MPC and
valid-encryption proof machinery. It maps closely to the missing transferable
validity proofs around the DKG/relinearization substrate already present in
`distributed_bfv_correlation.rs`; it is not itself an established standard.

[High-Throughput Universally Composable Threshold FHE
Decryption](https://web.eecs.umich.edu/~cpeikert/pubs/threshold-fhe.pdf)
replaces noise flooding with an MPC rounding path and an offline/online split.
Its ideal functionality is deliberately only decryption in an arithmetic-black-
box hybrid; admissible-ciphertext restrictions, secure key generation, and
ciphertext well-formedness remain composition obligations. [Efficient MPC-Based
Modulus Conversion for Threshold FHE Decryption, ePrint
2026/1058](https://eprint.iacr.org/2026/1058) advances the same line with
statistical UC security against malicious adversaries and dramatically less
preprocessed correlated randomness under its mild input bound. It does not
supply DKG, ciphertext validity, or dealerless generation of that preprocessing.

[Threshold (T)FHE without smudging, ePrint
2026/901](https://eprint.iacr.org/2026/901) is relevant to the TFHE side, but
its concrete route uses threshold Paillier around a sanitized LWE `b` term.
That makes it a **classical-hybrid research route**, not a post-quantum or UC
completion of fhEgg. It must never be cited as “threshold TFHE therefore PQ end
to end.”

[Ajax, ePrint 2025/1834](https://eprint.iacr.org/2025/1834) is further evidence
that no-noise-flooding threshold decryption can be substantially faster. Its
concrete FHEW-like protocol and proofs are semi-honest; active security is only
overviewed, so it is not the malicious profile. Meanwhile,
[the CPAD analysis, ePrint 2024/116](https://eprint.iacr.org/2024/116) is the
warning: removing smudging from BFV/BGV/CKKS without a replacement proof/security
argument can expose partial-decryption leakage.

### Exact implementation cut

`CorrelationCertificate` should name and bind a profile, not imply one:

- corruption threshold and availability mode;
- security-with-abort versus guaranteed output delivery;
- static/adaptive corruption and UC/stand-alone target;
- synchronized designated-set versus asynchronous decryptor selection, plus
  channel/network assumptions;
- admissible-ciphertext/decryption policy and concrete decryption-failure budget;
- DKG and relinearization proof-system, verification-key, statement-domain,
  and certificate identifiers;
- separate correct-encryption and application-plaintext validity certificates
  (for fhEgg orders: packed shape, one quantity, side/range, padding, identity,
  and funding binding—not bitness alone);
- decryption-share validity plus verified modulus-conversion execution and
  public openings, not a demand to publish private MPC messages;
- preprocessing provenance/realization and component-by-component PQ status;
- CPAD/noise-leakage defense used by this profile.

The current two-party threshold-BFV correlation remains useful executable
substrate. It is not promoted to malicious threshold FHE until those fields
have a verifier, hostile teeth, and a proof/reduction matching the selected
profile.

## 3. No single source viewer: collaborative code privacy is the stronger lead

### Primary results

[Code-based Scalable Collaborative SNARKs, ePrint
2026/729](https://eprint.iacr.org/2026/729) is the most directly relevant new
result for Dregg's “no viewer” objective. It defines `(t,l)`-zero-knowledge
collaborative codes: a coalition of up to `t` corrupted parties, even after a
bounded number of codeword queries, learns no additional message information.
It builds foldable tensor Reed–Solomon codes, a collaborative ZK proximity
test, a quantum-sound compiler, and a transparent PQ collaborative SNARK. This
is closer to the desired privacy statement than merely splitting prover work.
The base construction analyzes corrupted provers as honest-but-curious;
malicious-with-abort/deviation privacy uses a separate compiler and is not the
benchmarked base system.

[FRIttata](https://cic.iacr.org/p/2/4/26) supplies a horizontally scalable,
transparent, plausibly-PQ FRI PCS. Its Fold-and-Batch pattern—partial folds at
workers followed by a central batched FRI—is a natural match for the existing
GPU PCS-commitment seam; distributed fold/orchestration remains new work. The
published construction is not zero-knowledge or formally accountable: a bad
worker can make the final proof fail, while identification is future work.

[DEPIPFRI / Shred-to-Shine](https://www.usenix.org/conference/usenixsecurity26/presentation/li-weihan)
adds distributed single-polynomial support and accountability by identifying
bad sub-provers. PIPFRI has a proved honest-verifier-ZK masking transform, but
the paper presents distributed Protocol 5 only in non-ZK form and asserts,
rather than formalizes, its ZK extension. Accountability assumes an honest
master and is orthogonal to coalition privacy.

[HyperFond, ePrint 2025/1349](https://eprint.iacr.org/2025/1349) and
[UltraFold, ePrint 2026/266](https://eprint.iacr.org/2026/266) are valuable
BaseFold-side comparison points for transparent distributed proving, packed
Merkle layout, and communication/proof-size tradeoffs—including HyperFond's
linear growth and UltraFold's worker-count-independent proof.
They do not by themselves substitute for a no-coalition-viewer definition.

### Soundness correction largely reflected at HEAD

The July [SoK on hash-based PCS and low-degree tests, ePrint
2026/1367](https://eprint.iacr.org/2026/1367) reports that strong
capacity-soundness conjectures, including the mutual-correlated-agreement form
used by newer schemes, were disproved over large fields in late 2025. FRI's own
capacity conjecture was not directly refuted but lost downstream support; the
Johnson-bound line remains unaffected. This is not a newly discovered Dregg
hole: `GOAL-FRI-PRODUCT.md`, `docs/reference/FRI-BOTH-WIN-LEVERS.md`, and the
Lean-exported FRI ledger already separate proven/Johnson/capacity statements
and explicitly record the capacity refutation. The action is regression
discipline: cite the new SoK, keep conjectural columns out of acceptance policy,
add a source-version pin to any future BaseFold/WHIR parameter import, and fix
the remaining stale “capacity-bound target” label in `circuit/src/stark_zk.rs`.

### Exact implementation cut

Build a parallel experimental path rather than replacing `HidingFriPcs`:

1. `DistributedHidingFriManifest` fixes public statement, descriptor/VK,
   roster, threshold privacy claim, shard geometry, salts/masks, fold schedule,
   query budget, and security parameters.
2. Owners encode/share the witness before any FRI challenge. No worker receives
   all systematic coordinates.
3. Workers keep shard/fold data GPU-resident and return authenticated partial
   commitments. Accountability and coalition privacy are a new composition
   theorem/protocol obligation; no cited paper supplies both.
4. The aggregator performs only the specified batch/fold composition and cannot
   ask adaptive out-of-manifest openings.
5. Differential acceptance compares the resulting public statement and
   verifier result with the monolithic HidingFRI path; proof bytes need not be
   identical when masking/randomness differs.
6. Finite regression tests enumerate every coalition up to `t` for tiny
   parameters and compare simulated/real observations under an enforced query
   budget. These exercise the implementation; the cryptographic privacy claim
   still rests on a proved simulator theorem.

## 4. A reusable PQ private-permutation game operation

[Efficient Verifiable Mixnets from Lattices, Revisited, ePrint
2025/658](https://eprint.iacr.org/2025/658) finds a soundness flaw in an older
lattice shuffle argument caused by polynomial-ring splitting, then gives a
corrected compact lattice verifiable mixnet. The immediate lesson is negative
and important: a classical shuffle relation translated componentwise into a
ring is not automatically a sound PQ shuffle.

[PQKryvos](https://petsymposium.org/popets/2026/popets-2026-0164.pdf) shows how
BDLOP lattice commitments and Ligero proofs can support flexible constrained
ballots and proofs about the intended result. It does not construct a shuffle.
Its strongest public privacy statement requires no corrupted tallier; with at
least one honest tallier but corrupted talliers, individual votes remain hidden
but the aggregate tally is exposed. Its election shell is not required for
Dregg, but the constrained-ballot/result-proof grammar maps to:

- guild/party sealed voting;
- private raid-role or loot-order allocation;
- preference aggregation and matchmaking where the selected result may be
  revealed.

The right engine abstraction is a typed operation receipt—not “a voting app.”
For actual permutation, the corrected mixnet proves a decryption-and-permutation
relation over ciphertext vectors and returns shuffled inner ciphertexts or
plaintexts. A Dregg `VerifiablePermutation` receipt is a new composition over
that relation, not an API supplied by the paper. Lean should own multiset
preservation—no injected or dropped committed item; applications that need
semantic uniqueness must also bind unique item identities. Backend soundness
depends on the proof system's witness-extended emulation and Ajtai commitment,
while privacy rests on the lattice encryption assumptions. A hostile test must
instantiate the paper's ring-splitting counterexample against any candidate
backend.

[FLOSS, ePrint 2026/672](https://eprint.iacr.org/2026/672) is a complementary,
non-PQ operation lane: malicious dishonest-majority UC two-party computation
with abort for arithmetic permutation circuits over finite fields. It is useful
for a fast secret-shared game operation, not a publicly verifiable lattice
mixnet. Its preprocessing must be formed in one initialization before secrets;
on-demand generation exposes a selective-failure/input-guessing surface.

## 5. Portable GPU: optimize the resident workflow

[Theodosian](https://arxiv.org/abs/2512.18345), [BOLT-FHE
(TCHES 2026)](https://tches.iacr.org/index.php/TCHES/article/view/13089),
[FHECore](https://arxiv.org/abs/2602.22229),
[FlashTFHE](https://users.cs.duke.edu/~lkw34/papers/ma-flashtfhe-isca2026-preprint.pdf),
and [TIGER](https://arxiv.org/abs/2604.04783) converge on a practical point:
memory placement, on-chip tiling, batching, and whole-workflow scheduling
dominate many FHE workloads. The TFHE papers apply to Dregg's all-TFHE fallback
or a future genuinely nonlinear crossing, not to the adopted carry-free BFV
additive fold plus output-boundary MPC.

In bellperson's Groth16-style stack on an NVIDIA A40/CUDA 12.8,
[ZKProphet](https://arxiv.org/abs/2509.22684) finds that NTT reaches roughly 91%
of time after optimized MSM and that CPU/GPU transfer dominates the NTT phase.
That supports residency and underfilled-dispatch work, not a claim that NTT is
Dregg's next bottleneck: current Dregg measurements have a much larger MMCS
share and a small DFT share.

Only the design principles are portable. Theodosian is measured CUDA on an RTX
5090; BOLT's one-block megakernel relies on CUDA warp/register/shared-memory
geometry. Custom or simulated GPU extensions and ASICs in FHECore, FlashTFHE,
UniZK, and MTU are hypotheses about data movement, not WGPU measurements. CUDA
graphs, thread-block clusters, tensor-core mappings, replayable command buffers,
and independent compute/copy queues are not portable WebGPU APIs. Portable WGSL
also has a 16 KiB/256-invocation guaranteed floor and no core concrete `i64`.
For Dregg the faithful translation is:

- retain NTT/PBS/FRI/Merkle buffers across stages;
- batch independent ciphertext blocks and proof instances;
- fuse only stage groups that fit queried adapter limits; retain a native
  Vulkan/CUDA specialization for 64-bit or large-shared-memory megakernels;
- cache pipelines, bind groups, and schedule metadata, then encode each run into
  one or a few fresh command buffers without assuming copy/compute overlap or
  reordering transcript-visible stages;
- pack/interleave Merkle leaves to reduce transactions;
- measure upload bytes, dispatches, waits, readbacks, total operation time, and
  CPU parity—not kernel time alone. L2/occupancy data may come from an external
  native profiler, never a portable browser gate;
- assert adapter/size thresholds and CPU-fallback counters: the sync BN254 MMCS
  path still falls back for oversized commits, while the all-BabyBear inner path
  is the more plausible browser-resident target;
- keep independent CPU/tfhe-rs exactness oracles and secret-independent access
  rules.

This confirms the existing WGPU direction. It does not justify replacing
dalek where the measured public MSM remains hundreds of times slower, nor does
it make CUDA-only upstream TFHE an acceptable portability dependency.

## 6. A Dregg-native proving stack beside Plonky3

### Verdict

Do not rewrite Plonky3 as one heroic replacement. Preserve Lean plus
DescriptorIR/IR2 as the proof-system-neutral definition of the semantic
relation, keep the current Plonky3/HidingFRI path as an executable reference,
and split the backend at three explicit interfaces:

1. relation/AIR evaluation and exact public-statement encoding;
2. PCS/LDT/MMCS/transcript;
3. recursion, accumulation, and PCD.

Then prototype a second, Dregg-native backend at interfaces 2 and 3. “Better”
here means share-native no-viewer proving, transparent/PQ components, portable
GPU residence, semantic-step/graph composition, and a Lean-owned soundness
ledger. It need not beat Plonky3 as a general-purpose library to be decisively
better for Dregg.

### What the new papers actually contribute

The collaborative tensor-RS/FRI/BaseFold construction in
[ePrint 2026/729](https://eprint.iacr.org/2026/729) is the foundation for the
PCS experiment: it gives `(t,l)` code privacy, scalable local work, transparent
PQ compilation, and a corruption threshold up to `t <= (1/2-epsilon)N` for its
R1CS path. Its main construction analyzes corrupted provers as
honest-but-curious; the cited malicious compiler is an additional layer whose
overhead and deployment behavior must be measured separately.

[UltraFold, ePrint 2026/266](https://eprint.iacr.org/2026/266) contributes the
packed/interleaved Merkle layout and distributed BaseFold schedule: arbitrary
worker counts and proof size independent of worker count, at the cost of a
heavy all-to-all exchange. It is distributed proving, not witness privacy or
malicious accountability by itself. [HyperFond, ePrint
2025/1349](https://eprint.iacr.org/2025/1349) is a useful comparison point, but
its sub-provers trust each other, witness privacy is not its claim, and proof
size grows with worker count.

[Collaborative IVC, ePrint 2026/410](https://eprint.iacr.org/2026/410) supplies
an elegant blueprint for t-private Nova folding: keep witness shares at degree
`t`, cross/error terms at degree `2t`, and reconstruct only their homomorphic
commitment, yielding constant per-party communication per step under honest
majority. The paper instantiates Nova with Pedersen commitments, so it is
classical rather than a PQ recursion backend as written; it also still needs a
traditional ZK final proof.

[Holography accumulation, ePrint
2026/538](https://eprint.iacr.org/2026/538) is the stronger architectural match
for distributed semantic operations. It separates witness-dependent checks
from public computation-structure checks, models the latter as generalized
bilinear forms, and accumulates them into stateless PCD compatible in principle
with arithmetizable FRI/STIR/WHIR/Binius/BaseFold verification. This is a
framework and theorem, not a benchmarked drop-in backend.

### First falsifiable prototype

The same Lean descriptor and witness must run through current Plonky3
HidingFRI and a collaborative tensor-RS/BaseFold backend. Require identical
canonical public statements and verifier decisions—not identical randomized
proof bytes—plus hostile mutation refusal. Measure proof size, wall time, RSS,
network bytes/rounds, verifier time, GPU transfers/dispatches, and every worker
coalition allowed by the privacy profile. Plonky3 remains the differential
oracle until the second path clears those gates.

The first Lean targets are deliberately below a whole SNARK theorem:

- the tensor-code encode/fold commutation law;
- a finite `(t,l)` observation/non-identifiability model for selected tiny
  parameters;
- packed/interleaved Merkle commitment equivalence to the canonical tree;
- distributed fold composition equals monolithic fold;
- generalized-bilinear-form accumulation preserves the public check;
- backend observational equivalence at the canonical statement boundary.

This lets formalization falsify the architecture early. It also keeps
cryptographic assumptions explicit instead of proving a clean algebraic shell
and silently inheriting an unsuitable commitment or corruption model.

## 7. Graph-native semantic computation

The research sweep found useful neighboring work on interaction nets,
incremental verifiable computation, and proof-carrying graph execution, but no
2025–2026 construction that should displace Dregg's current graph-rewrite +
Lean-semantics + transparent-proof composition. Treat this as a research lane,
not an excuse to pause the nearer protocol closures above.

The promising experiment is narrower. [Sato's interaction-net
result](https://arxiv.org/abs/2410.00540) gives a usable syntactic condition:
pairwise-distinct conditional nested active-pair rules are confluent, and
nested rules can be compiled to fresh-agent nonnested rules while preserving
reduction. Use that as a rule-compiler and confluence-checker design reference,
not as a proof system.

At HEAD, Dregg's list-context/DPO-like `GraphRewrite` relation still needs an
executable certificate with dangling, freshness, and interface checks. The
current private graph leaf is local in semantics but monolithic in its tiny
four-slot commitment/witness; it has no per-node Merkle-DAG path. The first
experiment therefore needs a hierarchical faithful graph commitment with
canonical node/edge content identities and authenticated ancestor paths.

Measure cold one-step leaf proving plus full history/tree refolding against
cached local semantic leaves plus ancestor-frontier recomputation. The reusable
cache key must separate a stable private semantic core from the current
session/index-bound hiding commitment; otherwise a public stable key leaks
equality and reuse is limited to the identical public statement. Proof-node
identities and occurrence bindings must also prevent a DAG leaf from being
consumed twice. “An Agda program is a distributed reduction” is a good
semantic-computer frame; it is not yet a security or complexity theorem.

## Promotion order

This is dependency order, not calendar or cost framing:

1. close the dealerless MAC cross-term provider with malicious transcript
   binding;
2. choose and encode the threshold-FHE security profile, then close input and
   decryption-share validity;
3. build the collaborative tensor-RS/BaseFold experiment against the current
   exact Plonky3/HidingFRI differential;
4. expose a reusable verified-private-permutation game operation;
5. push resident/fused WGPU scheduling under end-to-end operation benchmarks;
6. prototype stateless holographic accumulation at the canonical semantic-step
   boundary;
7. use the graph-native experiment to learn where semantic proof memoization
   actually wins.

None of these papers turns a prototype into a deployment claim by citation.
Each promotion still requires Dregg's normal exact wire binding, hostile
substitution/replay teeth, Lean-owned algebra where applicable, and a captured
end-to-end gate.
