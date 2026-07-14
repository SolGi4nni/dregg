# Executive verdict

fhEgg’s defensible advantage is not “FHE makes auctions fast.” It is the verified separation between:

1. untrusted search,
2. small optimality/validity certificates,
3. exact translation validation, and
4. proof-bound settlement.

That architecture is genuinely differentiated. The highest-value refinement is:

> The crossing’s nonlinearity is irreducible; paying for it inside TFHE is not.

Because `p*` is deliberately public, the best likely Tier-0 architecture is an output-boundary protocol: retain the aggregate curve under exact RLWE encryption, compute the crossing through malicious-secure threshold comparison, reveal only the deterministic comparison path or `p*`, and prove the two boundary inequalities against the committed aggregate. That can remove the BFV→TFHE scheme switch entirely.

The strongest pure-FHE alternative is not automatically binary search. For `K=64`, compare:

- a parallel, batched 64-way sign scan with a priority encoder;
- a six-round adaptive search, whose encrypted indexing/CMUX costs may erase its comparison-count advantage;
- a candidate proposer followed by two exact boundary checks.

On FPGA, the parallel scan may win latency even while losing work.

For the launchpad, the mechanism-design principle should be:

> Make misconduct structurally impossible whenever possible; bond only the residual conduct that cannot be forbidden.

In particular, creator schedule violations should be prevented by an immutable provenance-aware vesting escrow. A rolling, quote-denominated, exposure-indexed bond should cover the remaining bounded harm. A flat bond is strictly less capital-efficient unless exposure is constant.

## Three important corrections to the supplied snapshot

The current tree has advanced beyond several statements in the brief:

- [StreamingCert.lean](/Users/ember/dev/breadstuffs/metatheory/Market/StreamingCert.lean) now exists. It proves an independent per-batch additive error composition. It does not yet prove state-coupled frequent-batch optimality with inventory/risk potentials.
- An [N-leg shielded-ring AIR](/Users/ember/dev/breadstuffs/circuit-prove/src/shielded_ring_clearing_nleg_air.rs) now exists. The remaining seams are closer to full commitment semantics, deployed widths/VKs, and reveal-nothing—not “no N-leg AIR.”
- The [constant-product pool](/Users/ember/dev/breadstuffs/chain/contracts/launchpad/DreggSolventPool.sol) is now implemented, with the floor refinement represented in [GraduationPool.lean](/Users/ember/dev/breadstuffs/metatheory/Market/GraduationPool.lean). Its economic-quality properties remain open; its existence does not.

There is also a numerical correction: `180 PBS-equiv` is roughly 9–13 seconds at the measured M2 CPU PBS rate. At the stated FPGA model it is approximately:

- 18–36 ms on one modeled 5–10k PBS/s VU47P;
- 2.3–4.5 ms across a 40–80k PBS/s eight-FPGA F2;
- about 14 ms at Zama HPU’s reported 13k PBS/s.

Thus 12–17 seconds is a plausible CPU residual, not the modeled F2 crossing latency. On F2, the unmeasured scheme-switch, key loading, PCIe, and orchestration seams may dominate.

I use these labels below:

- **Known:** established result or known construction.
- **Derived:** a direct, fairly safe application to fhEgg.
- **New proposal:** a system/mechanism composition that appears genuinely new, but is not yet a theorem or implementation.

---

# Q1. The execution-engine frontier

## 1. The family is missing time and composition more than another static optimizer

The eight mechanisms cover a remarkably broad static frontier. The important omissions are mechanisms whose correctness depends on state across time, shared constraints across privacy domains, or adversarial solver selection.

### A. State-coupled frequent-batch clearing

**New proposal.** Let batch `t` have fills `f_t` and inventory/risk state

\[
z_t=z_{t-1}+B_t f_t.
\]

The current streaming result essentially certifies independent batches and sums their errors. A real frequent-batch product needs dual variables that price continuation inventory and telescope across time. Schematically, the certificate should yield

\[
\operatorname{OPT}_{1:T}-V(f_{1:T})
\leq \sum_{t=1}^T \varepsilon_t
+\Phi_T(z_T)-\Phi_0(z_0),
\]

where `Φ_t` is a certified dual potential for inventory, collateral, liquidity, or risk capacity. The local proof carries:

- batch feasibility and conservation;
- the transition `z_{t-1}→z_t`;
- local reduced-cost/dual feasibility;
- the previous and next state roots;
- a commitment to the continuation dual potential.

Summing the per-batch inequalities cancels the internal potential terms. This is the substantive telescoping result; simply summing independent duality gaps does not capture intertemporal coupling.

There is an unavoidable semantic qualification: an online system cannot certify ex post welfare optimality against orders that have not arrived. It can certify one of:

1. optimality conditional on the current state and accepted batch;
2. a finite-horizon optimum against a declared order-arrival set;
3. a regret bound against a feasible comparator trajectory;
4. prefix optimality given a certified terminal value function.

This makes frequent-batch auctions a natural fhEgg product, but the receipt must distinguish allocation optimality from inclusion/censorship fairness. Frequent batch auctions remove the continuous latency race, but batch-boundary inclusion still matters; that distinction is central in the original market-design case for frequent batching. [Budish, Cramton, and Shim](https://www.cramton.umd.edu/papers2015-2019/budish-cramton-shim-hft-frequent-batch-auctions.pdf).

### B. Cross-tier atomic clearing

**Derived, with a genuinely new proof-composition problem.** Suppose `r∈{0,1,2}` indexes privacy tiers. The sound joint primal is

\[
\max \sum_r w_r^\top f_r
\quad\text{s.t.}\quad
\sum_r A_r f_r=0,\qquad
0\le f_r\le c_r.
\]

A single dual price `π` and tier-local slacks `s_r` satisfy

\[
A_r^\top \pi+s_r\ge w_r,\qquad s_r\ge0,
\]

giving the joint upper bound

\[
U=\sum_r c_r^\top s_r
\]

and certificate

\[
U-\sum_r w_r^\top f_r\le\varepsilon.
\]

The algebra is sound across a privacy boundary. Privacy does not change weak duality.

But `c=c⁰+c¹+c²` alone is not enough. The proof system must also establish:

- each `f_r` belongs to its tier-tagged order root;
- roots and nullifier domains are disjoint or explicitly linked;
- all tiers use the same asset, unit, quantization, and operator semantics;
- the shared dual `π` is the same object in every subproof;
- the tier-local imbalances sum to zero;
- settlement is atomic—no tier can reveal/prove its favorable leg and abort another.

If every tier separately proves `A_r f_r=0`, the system forbids actual cross-tier exchange. The useful construction proves hidden tier-local boundary flows `b_r=A_r f_r` and only exposes/proves `Σb_r=0`.

The right implementation shape is prepare/lock at each tier, a recursively aggregated joint certificate, and one settlement root. The leakage functor must explicitly decide whether tier-local imbalances remain hidden.

### C. A two-sided solver proof market

**New proposal.** Solver competition should not select only a winning primal solution. Run two permissionless competitions:

- primal solvers maximize a certified lower bound `V`;
- dual solvers minimize a certified upper bound `U`.

Any feasible primal from solver A can be combined with any feasible dual from solver B. The market selects

\[
L=\max_i V(f_i),\qquad U=\min_j U(y_j)
\]

and settles when `U−L≤ε`.

This is stronger than ordinary solver competition:

- a primal solver does not need to construct a good dual;
- a dual solver can improve the guarantee without finding a new allocation;
- an incumbent cannot monopolize the entire algorithmic stack;
- rewards can be paid for marginal lower-bound improvement and marginal upper-bound tightening.

CoW-style solver competition already demonstrates the value of competing intent solvers, but fhEgg can add a machine-checkable optimality envelope rather than relying only on validity and competition rules. The novel part is the independently spliceable primal/dual proof market.

Commit/reveal or delayed attribution is needed to prevent proof-copying, and the reward rule must avoid paying repeatedly for economically identical bounds.

### D. A comparison-metered market family

**New proposal.** If additions are cheap and comparisons are the metered resource, mechanisms should expose a comparison budget as a first-class product parameter.

One useful design is a public reference-price corridor backed by certified inventory:

- the price for the next batch is fixed or selected from a small public corridor;
- orders aggregate additively;
- a buffer market maker absorbs bounded net imbalance;
- only capacity, floor, and perhaps two boundary comparisons are required;
- the endogenous price is re-anchored less frequently through a full auction.

This trades continuous price discovery for dramatically cheaper dark clearing. The state-coupled dual potential above can certify that the buffer remains within inventory and loss limits.

A fully endogenous exact crossing cannot be reduced to pure addition. A posted-price or buffered mechanism is the honest way to avoid the crossing: it changes the economic problem instead of disguising the nonlinearity.

### E. Other material product gaps

The next important certificate families are:

- portfolio-margin and liquidation clearing with cross-period collateral;
- conic/SOCP risk constraints;
- network-constrained energy or cross-chain liquidity clearing;
- robust clearing under bounded oracle/model uncertainty;
- default waterfalls and close-out netting;
- multi-period lending and refinancing auctions.

The current `CrossMargin` and `Lending` Lean layers are useful models, but they are not yet the equivalent of the eight concrete private optimizer modules. The missing theorem is often not weak duality; it is correspondence between the economic state transition, oracle provenance, settlement, and the certificate.

---

## 2. Package bids: the sandwich is universal, but cannot be universally multiplicative

The sandwich

\[
V(x)\le \operatorname{OPT}_{IP}\le \operatorname{OPT}_{LP}\le U
\]

is logically tight: no step is invalid. It can nevertheless be economically loose for two independent reasons:

1. the submitted LP dual is not optimal;
2. the LP relaxation has a large integrality gap.

For arbitrary balanced binary packages, no meaningful universal multiplicative guarantee follows from the natural LP. A one-dimensional example already shows why:

\[
2x_1-3x_2=0,\qquad x_i\in\{0,1\}.
\]

The only binary feasible point is the empty selection, but the relaxation admits `x₁=1, x₂=2/3`. With positive values, `OPT_IP=0` while `OPT_LP>0`. The relative integrality gap is therefore unbounded. Public topology does not cure this.

### Structure must be part of the type

A useful `fhIR` refinement would type package families by the approximation theorem they support:

| Package structure | Honest guarantee |
|---|---|
| Network/TU matrix | Integral LP; exact `Cert-F` |
| Gross-substitutes demand | Walrasian/integral equilibrium structure |
| Matroid/submodular constraints | Pipage or swap-rounding family |
| `k`-set packing | Structure-dependent constant-factor certificate |
| Arbitrary balanced packages | Additive LP sandwich only |

Gross substitutes are special precisely because they support Walrasian equilibrium and tractable price structure; they are not representative of arbitrary combinatorial demand. [Gul and Stacchetti](https://www.sciencedirect.com/science/article/pii/S0022053199925310). Pipage/swap rounding similarly depends on matroid/submodular structure and is not a generic package-bid remedy. [Chekuri, Vondrák, and Zenklusen](https://arxiv.org/abs/0909.4348).

For the standard `k`-set-packing LP, the integrality gap can approach `k−1+1/k` through projective-plane constructions. Constant factors therefore require an explicit structural assumption and often a strengthened relaxation or local search. [Bansal et al.](https://theoryofcomputing.org/articles/v008a024/v008a024.pdf).

### The fhEgg-native approximation certificate

**Derived and important.** Do not prove the rounding algorithm in AIR. Let any untrusted randomized, iterative, or learned solver propose an integral feasible `x`. Then check directly:

\[
U\le \alpha V(x).
\]

Since `OPT_IP≤U`, this immediately gives

\[
\operatorname{OPT}_{IP}\le\alpha V(x).
\]

The certificate consists only of:

- bitness and package feasibility of `x`;
- LP-dual feasibility;
- the value computations;
- the ratio inequality.

The randomized algorithm’s expected guarantee becomes a completeness/liveness statement: it predicts how often the solver will find a certifiable solution. Soundness is deterministic and per-instance.

This is the package analogue of the Tier-0 quantization rule:

> Rounding proposes; a direct approximation-ratio certificate disposes.

For instances with `V(x)=0`, negative values, or badly scaled objectives, retain an additive bound or a normalized hybrid:

\[
U-V(x)\le \Delta
\quad\text{or}\quad
U\le \alpha V(x)+\Delta.
\]

Valid inequalities—clique, cover, odd-cycle, blossom, or problem-specific cuts—can tighten `U`. Each cut should be supplied with a small proof of validity or drawn from a pre-certified family. Full branch-and-bound proof logs are possible, but they abandon the small trace-independent certificate advantage.

---

## 3. The private crossing

## 3.1 What cannot work

Let `g_j=D(j)-S(j)` under a convention that makes `Clears(j)` monotone. An exact crossing computes a threshold or first-one function from the vector `g`.

No affine map over the ciphertext ring can implement this function on a nontrivial domain. On a finite field, the threshold can formally be represented by a polynomial, but the degree, digit decomposition, or bootstrap is precisely where the nonlinearity reappears.

Consequences:

- The prefix/difference-polynomial multiply is excellent: it produces all cumulative buckets with one linear operation.
- It does not make the sign of a coefficient linear.
- Unary or redundant encodings move the work to encoding size, carry management, or nonlinear decoding.
- A “one-lattice-operation comparison” either assumes a trusted decryptor, hides a bootstrap, or has an impractical message-domain polynomial.

The goal is therefore to reduce, batch, relocate, or reveal the minimum necessary nonlinearity.

## 3.2 Candidate assessment

| Candidate | Actual result |
|---|---|
| Read threshold from packed coefficients | No; coefficient extraction is linear, sign/first crossing is not |
| One packed LUT PBS for all buckets | Amortization is possible; one ordinary PBS does not compare `K` independent LWE inputs |
| Binary search | Six comparisons at `K=64`, but only cheaply if the midpoint can become public; private adaptive addressing needs CMUX/oblivious selection |
| Two boundary checks | Excellent verification cost; does not itself find the candidate |
| CKKS polynomial sign | Good untrusted proposer when margins are large; exact validation still required |
| Threshold-decrypt `p*` | Viable only if an MPC computes `p*`; there is no ciphertext of `p*` before performing the comparison |
| Change the mechanism | Posted-price or buffered clearing can reduce the task to one or two comparisons, at the price of weaker endogenous discovery |

### Batched PBS is valuable, but not magic

Multi-value functional bootstrapping can evaluate several functions of the same LWE input. It does not make `K` unrelated coefficient signs one input. Architectural batching can still share decomposition, NTT traffic, and key access across many bootstraps. Recent systems report large improvements from precisely that batching; BatchBoot reports 2.4× over a prior batched design and 43.8× over non-batched `tfhe-rs` in its evaluated setting. [BatchBoot](https://www.usenix.org/conference/usenixsecurity26/presentation/li-zhihao).

That favors a parallel scan on a wide FPGA.

### Binary search has an encrypted-index trap

If each comparison result stays encrypted, the next midpoint is private. Selecting the next `g_j` then requires an encrypted decision tree, CMUX network, or oblivious packed lookup. Consequently:

\[
O(\log K)\text{ signs}
\not\Rightarrow
O(\log K)\text{ total FHE work}.
\]

If each sign is safely made public during the protocol, the midpoint remains public and the six-comparison result is real. Because the sign path is a deterministic function of the final crossing under a fixed tie rule, a simulator given `p*` can reproduce the path. It need not increase leakage beyond `p*`.

The trade is six rounds of threshold interaction and liveness dependency.

### Two-boundary validation is still the correct certificate

Given a proposed `j`, proving

\[
\neg\operatorname{Clears}(j-1)
\;\wedge\;
\operatorname{Clears}(j)
\]

is sufficient under certified monotonicity. This reduces authoritative verification to two comparisons. But the proposal must come from somewhere:

- threshold MPC;
- approximate CKKS polynomial evaluation;
- a previous-price corridor search;
- pure-FHE scan/search;
- a party that is permitted to see the aggregate.

“Two comparisons” is a verification result, not a private-search algorithm.

## 3.3 Best pure-FHE construction

For an exact-quantized design:

1. Choose an exact BFV/BGV plaintext ring with degree large enough for the `K` coefficient representation.
2. Bound the cumulative imbalance by `B` and choose the plaintext modulus so centered reduction is unambiguous, typically `t>2B`, while satisfying batching/NTT requirements.
3. Aggregate difference polynomials using native RLWE additions.
4. Multiply by the public prefix polynomial to place all cumulative `g_j` in known coefficients.
5. Sample-extract selected coefficients into LWE ciphertexts.
6. Key/modulus-switch into the TFHE/FHEW domain.
7. Apply a sign LUT or radix comparison.
8. Compute the monotone first crossing and bind `j` into the STARK/settlement receipt.

CHIMERA is the closer conceptual precedent for exact BFV↔TFHE interoperability; it develops a common mapping among TFHE, B/FV, and HEAAN. [CHIMERA](https://eprint.iacr.org/2018/758). PEGASUS is highly relevant for packed CKKS↔FHEW switching and non-polynomial evaluation, but its approximate input path still needs exact translation validation for authoritative clearing. [PEGASUS](https://eprint.iacr.org/2020/1606).

The switch is not a free adapter. Measurements must include:

- RLWE decomposition and sample extraction;
- key-switch-key size and HBM residency;
- modulus/noise conversion;
- wide signed-message comparison, not merely a Boolean LUT;
- threshold key generation and partial-decryption semantics;
- cold versus warm key loading;
- PCIe and multi-FPGA scheduling.

I would implement two pure-FHE modes:

- **Latency mode:** extract all `K`, batch the sign bootstraps, then use a monotone priority encoder.
- **Work mode:** adaptive search with encrypted CMUX/lookup, interleaved across many markets to hide its serial dependency.

Do not assume the second is faster before measuring it.

## 3.4 Best architecture when `p*` is public: output-boundary MPC

**New proposal; highest-value candidate.**

1. Orders aggregate into an exact RLWE ciphertext of the cumulative curve.
2. Threshold parties convert selected coefficients into malicious-secure additive shares using verifiable partial decryption and appropriate smudging.
3. They compare the shares to zero inside MPC.
4. They perform either:
   - six public-path binary-search comparisons; or
   - a batched comparison of all `K` coefficients.
5. They reveal only `p*` or the monotone sign vector.
6. A ZK/STARK receipt proves:
   - order-root and aggregate binding;
   - exact quantized aggregation/no-wrap;
   - monotonicity;
   - the two boundary inequalities;
   - settlement conservation.

The full monotone sign vector leaks no more than `p*`, because under the declared tie rule it is determined by `p*`. Magnitudes must not be reconstructed.

Threshold exact-FHE decryption needs careful active-security and noise-smudging treatment; it is not enough to concatenate partial decryptions. Recent threshold BFV/BGV/CKKS work explicitly treats these decryption-security details. [Threshold FHE treatment](https://eprint.iacr.org/2024/116).

This construction eliminates the TFHE scheme switch, but introduces an online threshold/MPC dependency. That is likely the right trade if the product already accepts threshold output release.

### The threshold trust correction

A standard threshold FHE public key does not cryptographically constrain key holders to decrypt only `p*`. A threshold subset can apply the decryption protocol to any submitted order ciphertext.

Therefore:

> “The protocol requests decryption only of `p*`” is a policy statement, not a cryptographic no-viewer guarantee.

Zama’s own KMS description is explicit that a global FHE key and threshold nodes support user and public decryption operations. [Zama KMS architecture](https://docs.zama.org/protocol/protocol/overview/kms).

Tier-0 has four honest choices:

1. state an honest-threshold confidentiality assumption;
2. use secure-aggregation masks so individual orders are not decryptable from the shared aggregate interface;
3. use multi-key/constrained/functional decryption machinery;
4. weaken “nobody can ever see an order” to “the compute server and public cannot see orders; threshold collusion remains trusted.”

This is not a small wording issue. It is one of the highest-priority cryptographic model corrections.

## 3.5 Recommended crossing bake-off

Build and measure these three exact paths before substantial RTL work:

1. **Threshold-MPC output boundary:** six-round search and batched `K`-sign variant.
2. **Pure-FHE parallel scan:** BFV/BGV extraction → batched TFHE signs → priority encoder.
3. **Pure-FHE/private search:** extraction plus CMUX/oblivious addressing.

For each, report:

- `K=16,32,64,128`;
- 32/48/64-bit aggregate bounds;
- one market versus 64+ concurrent markets;
- warm/cold key loading;
- total latency, throughput, HBM traffic, and proof latency;
- failure probability and exact-no-wrap parameter margin.

My expectation is:

- lowest work: interactive public-path binary search;
- lowest single-market FPGA latency: batched parallel scan;
- simplest certificate: any proposal plus two exact boundaries;
- best noninteractive CPU/GPU path: unresolved until key-switch and private-index costs are measured.

---

# Q2. Driving FPGA forward

## 1. Build a crossing appliance, not a generic FHE company

After the additive fold, `N` largely disappears from the expensive work. Native RLWE additions may be cheap enough on CPU/GPU that shipping them to F2 is counterproductive. The FPGA-specific problem becomes:

- coefficient extraction;
- key switching;
- PBS or comparison;
- first-crossing selection;
- market/key/context binding.

The minimal differentiated block should be a **monotone-crossing engine** wrapped around a reusable FHE core:

1. HBM-resident evaluation and switching keys;
2. banked, double-buffered coefficient streams;
3. fused sample-extraction/key-switch/PBS stages;
4. a parallel sign mode and an adaptive-search mode;
5. a monotone priority encoder;
6. a receipt/public-input binder;
7. multi-market interleaving.

Multi-FPGA scale should initially distribute independent markets, not attempt to reduce one six-step binary search across eight cards. Independent markets provide nearly perfect parallelism and hide serial bootstrapping latency.

## 2. Wrap Zama’s HPU, but treat “wrap” as a port

Zama’s HPU is the right reference point: an open SystemVerilog FHE accelerator with reported 13k PBS/s at 350 MHz on an Alveo V80. Zama itself describes it as an open accelerator project rather than a turnkey production appliance. [Zama HPU announcement](https://www.zama.org/post/announcing-hpu-on-fpga-the-first-open-source-hardware-accelerator-for-fhe).

However, V80→VU47P is not bitstream portability:

- different FPGA generation and hardened resources;
- different shell, clocking, PCIe/QDMA, and HBM integration;
- different placement/routing and memory-bank pressure;
- possible frequency/resource regressions.

AWS F2 provides the HBM-rich VU47P platform, but its advertised resources do not establish HPU timing closure. [AWS F2 specifications](https://aws.amazon.com/ec2/instance-types/f2/).

The leverage-maximizing boundary is:

**Reuse/port**

- arithmetic kernels and parameter formats;
- PBS scheduling ideas;
- `tfhe-rs` interoperability;
- known-answer vectors;
- decomposition/NTT organization where portable.

**Build in-house**

- AWS shell and HBM streamers;
- exact BFV/BGV→LWE extraction/switch seam;
- crossing scheduler;
- monotone priority/selection block;
- market/key/batch domain separation;
- receipt and STARK public-input binding.

**Do not initially build**

- a new NTT architecture;
- a new programmable-bootstrap algorithm;
- a custom ASIC-style network;
- a multi-FPGA single-ciphertext fabric.

The first stop/go gate should be a placed-and-routed single-card subset with real key sizes—not a cycle model.

## 3. Sharpen the verified-core boundary

The current “verified conservation plus comparator core” proposal trusts more hardware than the verify-not-find architecture requires.

If the FPGA is merely an untrusted search accelerator and the STARK proves the crossing and conservation, then:

- an NTT bug produces a bad proposal or failed proof;
- a comparator bug produces the wrong `p*`, which cannot receive a valid proof;
- neither bug compromises soundness.

The soundness TCB should instead be:

1. the proof verifier;
2. the correspondence between Lean constraints and emitted AIR;
3. exact ring/field/quantization semantics;
4. binding between the accepted proof and the batch, parameters, assets, `p*`, allocation root, and settlement root.

The highest-value formal hardware-adjacent theorem is therefore:

> Any output accepted for `(batch_root, tier, parameter_hash, VK, settlement_root)` satisfies the Lean market transition for exactly those public inputs.

That theorem should cover stale-context and cross-market mixing, which are more realistic accelerator hazards than a faulty full adder.

Formal verification inside the FPGA remains valuable for availability and debugging:

- DMA address bounds;
- no stale key or batch reuse;
- deterministic reset;
- no bank-crossing/context aliasing;
- priority encoder correctness;
- exact sample-extraction index mapping;
- no arithmetic overflow relative to declared parameter bounds.

But unless the hardware itself gates settlement without a proof, these are not consensus soundness assumptions. If the comparator directly gates acceptance, either prove its semantic refinement all the way to the market theorem or remove that gate from the TCB.

## 4. FPGA milestone sequence

A contributor-efficient program would be:

1. **End-to-end benchmark harness.** Exact software vectors, noise bounds, cold/warm key timing, and proof-bound outputs.
2. **Single-card HPU feasibility port.** One supported parameter set; real HBM key residence; synth/P&R numbers.
3. **Fused crossing mode.** Sample extraction → key switch → batched signs → priority encoder.
4. **Adaptive-search mode.** Interleave many markets to hide round dependencies.
5. **Multi-card throughput.** Shard by market/key, not by individual comparison.
6. **Only then optimize the additive fold.**

The decisive number is not PBS/s. It is p50/p99 time from “aggregate ciphertext ready” to “proof-bound `p*` ready,” including key and transport overhead.

## 5. Confidential-compute architecture

Putting the Tier-1 plaintext solver and Tier-0 threshold custody on one SEV-SNP host creates an unnecessary common compromise domain.

Use three planes:

1. **Tier-0 compute plane:** F2 as an untrusted ciphertext accelerator.
2. **Tier-1 solver plane:** a separate confidential CPU/GPU host if operator confidentiality matters; ZK handles integrity.
3. **Key/custody plane:** independently administered threshold nodes or HSM-backed shares, used only for Tier-0 output protocols.

AWS currently limits SEV-SNP to specific AMD instance families such as `m6a`, `c6a`, and `r6a`; F2 is not one of them. [AWS SEV-SNP support](https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/sev-snp.html). Nitro Enclaves communicate through their parent via `vsock` and do not expose ordinary external networking or persistent storage; there is no clean enclave-to-F2 device-passthrough architecture. [AWS Nitro Enclaves](https://docs.aws.amazon.com/enclaves/latest/user/nitro-enclave.html).

Also keep the Tier-1 claim precise: it is committee-free public privacy, but one solver sees plaintext. ZK proves the solver computed correctly; it does not prove that the solver did not exfiltrate the order book.

---

# Q3. A world-class launchpad mechanism

## 1. Conduct bond: forbid first, bond second

### Make schedule violation structurally impossible

`soldSoFar(creator) > unlocked(schedule,epoch)` is difficult to define robustly from arbitrary address transfers:

- transfer to a new wallet is not necessarily a sale;
- a sale can occur through derivatives or an affiliate;
- address-based provenance is evadable;
- a creator may borrow tokens or short elsewhere.

The stronger mechanism is:

- mint the creator tranche directly into an immutable vesting escrow;
- represent releases as provenance-tagged tranche claims;
- allow only `unlocked(schedule,t)` to leave the escrow;
- make schedule changes impossible or subject to a long, buyer-visible timelock;
- separately track affiliated allocations when they can be credentialed.

Then the core schedule dump is not punishable—it is unrepresentable. The bond covers residual conduct such as undeclared affiliate coordination, promised-liquidity failure, oracle equivocation, or bounded governance abuse.

### A rolling exposure-indexed bond

**New proposal.** Let `a` range over replayably provable misconduct actions at time `t`. Let:

- `\bar G_t(a)` be a certified upper bound on the creator’s gain;
- `α_t(a)` be the probability of detection and enforceable slashing;
- `S_t(a)` be the slash;
- `C_t(a)` cover enforcement/restitution costs.

Risk-neutral deterrence follows if

\[
\alpha_t(a)S_t(a)\ge \bar G_t(a)+C_t(a)
\]

for every action, because

\[
EU(\text{deviate})-EU(\text{comply})
\le \bar G_t(a)-\alpha_t(a)S_t(a)-C_t(a)\le0.
\]

For automatically replayable predicates, `α≈1`. For statistical cohort or wash-trading accusations, `α` is neither objective nor close to one; those should not trigger automatic confiscation.

The required bond can be

\[
B_t\ge
\max_{a\in\mathcal A_t}
\frac{\bar G_t(a)+C_t(a)}{\alpha_t(a)},
\]

or the maximum over feasible portfolios of simultaneous attacks.

A flat bond must cover peak lifetime exposure, overcollateralizing quiet periods. A rolling bond tracks current exposure and can therefore provide equal deterrence with lower average locked capital.

### How to bound creator gain

Use observable, conservative quantities:

- cash extractable against the certified post-graduation depth curve;
- unlocked-but-unsold creator inventory;
- governance-controlled treasury/reserve value;
- promised liquidity not yet irrevocably deposited;
- bounded affiliate allocations;
- settlement and bridge exposure.

The bond should be denominated in the quote asset or high-quality collateral, not the launch token. A token-denominated bond loses value precisely when misconduct occurs.

No theorem can deter unbounded external shorts, undisclosed side payments, or off-platform collusion. The theorem must state a bounded-on-ledger-gain assumption. That is an honest and useful theorem; pretending to cover unbounded external wealth is not.

### Individual rationality

Posting is rational if the launch premium generated by the bond exceeds its capital cost and expected accidental-loss cost:

\[
\Delta R(B)
\ge (r+\rho_{\rm operational})B
+\mathbb E[\text{false/accidental slash}].
\]

Offer a menu of verified bond schedules. High-quality issuers can separate themselves by choosing stronger coverage, while the UI reports the coverage ratio without letting the platform sell “boosts.”

A practical funding structure is:

- creator posts initial stable collateral;
- a declared fraction of auction proceeds tops up the bond;
- undercollateralization pauses new creator releases and privileged governance actions;
- buyer exits and already-cleared settlement remain available;
- bond decays only after vesting, finality, and challenge windows expire.

### Restitution

“Pro rata to current holders” invites flash acquisition of claims after the violation. Instead use a pre-event time-weighted ownership snapshot:

\[
w_i=\int_{t-W}^{t^-}\operatorname{eligibleBalance}_i(u)\,du,
\qquad
R_i=S\frac{w_i}{\sum_j w_j}.
\]

Exclude creator, affiliates, treasury, AMMs, and known custody omnibus accounts where beneficial ownership is handled separately. For shielded holdings, claims can use launch-and-event-scoped nullifiers plus a ZK balance-history proof.

After measurable victim restitution, any excess should go to an insurance reserve or burn—not the platform.

## 2. Graduation: the curve cannot substitute for vesting

The constant-product pool is now built. It provides simplicity, continuous liquidity, and a clear reserve invariant. It does not prevent a large post-graduation sale from collapsing price. No finite-reserve curve can do that.

The choices are:

- **Constant product:** credible and simple; poor capital efficiency and severe tail slippage.
- **Constant sum:** appropriate only near a credible peg; otherwise it is a cheap reserve-drain mechanism.
- **Concentrated liquidity:** capital efficient, but an emptied range creates discontinuous price jumps and active-management/governance risk. Uniswap v3 formalizes this tradeoff. [Uniswap v3 whitepaper](https://uniswap.org/whitepaper-v3.pdf).
- **LMSR:** useful for bounded-outcome prediction markets; not a natural ordinary-token spot curve.
- **Dynamic curve:** can adapt depth, but introduces oracle and governance manipulability.

### Recommended v2: a proof-carrying depth ladder

**New proposal.** Use the constant-product pool as a solvent backstop, but make the authoritative post-graduation venue a frequent-batch piecewise-linear depth ladder:

- seed its reference price from the raise clearing price;
- publish buy/sell capacity by price bucket;
- derive capacities from reserves and the never-insolvent floor;
- batch trades and clear uniformly;
- update depth only between batches under a public bounded rule;
- expose a certified maximum price move and maximum quote outflow per batch.

This fits the existing `Cert-F` kernel more naturally than a path-dependent continuous AMM. It also:

- preserves the anti-ordering property after graduation;
- makes worst-case sale impact legible;
- produces the corridor certificate useful for cheaper dark crossing;
- permits deterministic circuit breakers;
- avoids an LP position manager or creator-controlled range.

A simpler intermediate step is a batch-CFMM: collect transactions during an interval and execute their net flow against the CPMM once, at one batch price.

### Circuit-breaker semantics

Halt only new matching when:

- reserve/floor margin falls below a declared threshold;
- price movement or batch flow exceeds a declared cap;
- the proof, oracle, or bridge is stale;
- the batch misses its finality deadline.

Never let the halt block:

- withdrawals;
- already-cleared settlement;
- restitution;
- proof challenge;
- safe unwinding.

Resume under a visible timelock and explicit receipt. “Admin may pause everything” is not institution-grade.

## 3. Bidding beyond commit–reveal

The correct target is one encrypted submission:

\[
(\operatorname{Enc}(\text{order}),\;
\pi_{\rm valid},\;
\text{collateral nullifier}).
\]

The proof establishes range, authorization, collateral reservation, and bid format. At the deadline, the system opens or computes automatically. No bidder reveal transaction is required, eliminating non-reveal griefing.

There are three honest postures:

- **Tier 1:** public ZK privacy; the solver sees plaintext.
- **Threshold-encrypted batch:** strong public privacy and good performance; committee confidentiality/liveness assumption.
- **Tier 0 FHE:** compute server does not see plaintext; threshold-key caveat and current performance frontier remain.

A single-phase ZK-sealed bid is not by itself “nobody sees”: someone must receive or decrypt the witness unless the computation remains FHE/MPC throughout.

The MVP commit–reveal can be improved with a reveal bond and forfeiture, but this remains a temporary mechanism because it retains metadata, capital lock, and two-round liveness.

## 4. Sybil resistance without public identity

No permissionless mechanism can infer “one human” from wallets alone. The clean composition is an anonymous credential:

1. an issuer or issuer set performs uniqueness/KYC/personhood checks;
2. the user receives a credential;
3. the user proves validity, policy satisfaction, and non-revocation in ZK;
4. the proof emits a launch-scoped nullifier

\[
N=\operatorname{PRF}_{sk}(\text{launchId}),
\]

preventing duplicate participation without cross-launch linkability.

Coconut provides a known threshold-issued, selectively disclosed credential construction. [Coconut](https://arxiv.org/abs/1802.07344). World ID’s action-scoped nullifiers illustrate the product pattern, although no single issuer should be treated as a universal identity oracle. [World ID overview](https://docs.world.org/world-id/overview).

Use a multi-issuer policy:

- personhood credential for retail anti-sybil;
- regulated KYC/accreditation credential for restricted offerings;
- reputation or community credential for optional tiers;
- no credential for the fully permissionless, split-invariant allocation.

The cryptography proves one credential per action. Whether a credential represents one human, is transferable, or excludes coercion remains an issuer/governance problem.

### Split invariance must be explicit

Without a uniqueness credential, the allocation rule should satisfy:

\[
A(b_1+b_2)=A(b_1)+A(b_2)
\]

up to deterministic rounding. Linear pro-rata allocation can satisfy this. Per-wallet caps, lotteries, concave rewards, and “small buyer bonuses” generally do not; they create a direct Sybil incentive.

Only enable anti-concentration caps or concave rewards in a credential-gated pool.

## 5. Anti-abuse beyond the existing three

### Sniping theorem scope

Uniform-price batching removes the value of ordering within a fixed accepted batch. It does not establish:

- truthful bidding;
- censorship resistance;
- equal access to the batch boundary;
- protection against demand reduction;
- immunity to validator delay across batches.

Multi-unit uniform-price auctions are known to admit demand reduction. [Ausubel and Cramton](https://www.ausubel.com/auction-papers/demand-reduction-2002.pdf). A truthful clinching or VCG-like design is possible in some settings, but it is more interactive and comparison-heavy; Ausubel’s clinching auction is the canonical reference. [Ausubel](https://www.aeaweb.org/articles?id=10.1257%2F0002828043052330).

Market the theorem as “no intra-batch ordering advantage,” not universal strategyproofness.

### Wash trading

Never reward raw volume. Rewarding volume creates the wash market you then need to detect.

If an attention or participation reward exists, base it on:

- net external capital;
- time at risk;
- credential uniqueness;
- net inventory change;
- realized exposure after excluding self/affiliate cycles.

Statistical wash or cohort detectors should produce a risk grade, enhanced disclosure, or bonded challenge—not automatic slashing. The system can prove that a declared classifier was run correctly; it cannot prove that the classifier’s behavioral hypothesis is true.

### Insider and affiliate allocations

Have the creator commit an affiliate-credential/nullifier set. Eligible bidders prove nonmembership when seeking public-allocation treatment. This catches declared or credential-linked affiliates, not undisclosed humans.

Make the receipt show separately:

- public allocation;
- creator tranche;
- treasury/community tranche;
- affiliate allocation;
- market-making inventory;
- bridge/custody balances.

### Cohort resistance

The robust mechanism is economic, not forensic:

- uniform batch price;
- split-invariant allocation;
- one-credential caps where identity is available;
- tranche provenance;
- no volume rebates;
- delayed, time-weighted rewards;
- batch-boundary inclusion proofs.

Cohort analysis can then inform surveillance without carrying the soundness claim.

## 6. Fair distribution and conviction

The cleanest conviction mechanism is to auction separate vesting claims:

- liquid-now tranche;
- 30/90/180-day vesting tranches;
- possibly a long-lock fee-sharing tranche.

Each tranche clears uniformly. The price discount for illiquidity emerges from demand rather than an administrator choosing a bonus.

This is more honest than retroactively rewarding wallets that merely held tokens. It also creates an institutionally legible term structure.

Caveat: if the vesting claim is transferable, economic exposure can be sold; if it is nontransferable, the system introduces illiquidity, identity, and custody complications. “Anti-flip” cannot be absolute without restricting transferability.

## 7. The minimal high-conviction receipt

The public receipt should contain:

\[
\begin{aligned}
(&\text{launch-spec hash},
\text{supply/tranche root},
\text{eligibility root},
\text{batch/order root},\\
& p^*,
\text{sold quantity},
\text{allocation root},
\text{proof/VK/version hash},\\
&\text{settlement/finality root},
\text{pool reserves/floor},
\text{bond state})
\end{aligned}
\]

A buyer-specific opening adds:

- order commitment or nullifier;
- submitted quantity/limit opening;
- own fill and payment;
- Merkle inclusion;
- vesting or restitution claim.

The UI must distinguish:

- **Open:** “recomputed from public orders.”
- **Shielded/Dark:** “verified by a proof over hidden orders.”
- **Attested:** “reported by a trusted hardware/operator boundary.”

A buyer cannot independently rederive the hidden curve in Tier 0 or Tier 1. Claiming otherwise would undermine the very privacy story.

Institutions should receive the same receipt in a stable machine-readable schema, including code, circuit, VK, quantization, policy, and upgrade identifiers.

## 8. What institutions will demand

Before material capital arrives:

- qualified custody and key recovery;
- clear legal rights, issuance authority, and token classification;
- KYC/AML/sanctions credentials and revocation;
- selective audit disclosure under a defined legal process;
- independent contract, circuit, and cryptographic audits;
- a non-toxic production setup or transparent/updatable alternative;
- persistent federation and availability SLAs;
- best-execution and solver-governance policy;
- deterministic halt, unwind, and trade-bust semantics;
- bridge/finality risk limits;
- versioned upgrades with buyer-visible timelocks;
- redemption terms, if redemption is promised;
- disaster recovery and proof/key archival.

Lean proofs answer “does this transition satisfy this specification?” Institutions will still ask whether the specification gives them the legal and operational rights they think they bought.

---

# Q4. Adversarial roadmap read

## Where dregg is genuinely ahead

### 1. Verified semantic continuity

The unusual asset is not merely a formal auction theorem. It is the intended chain:

\[
\text{economic specification}
\to\text{Lean checker}
\to\text{emitted constraints}
\to\text{real STARK}
\to\text{proof-bound settlement}.
\]

Few systems attempt machine-checked correspondence across that entire path. The Cert-F checker/STARK bridge is the hardest-to-copy part.

### 2. Verify-not-find as a market architecture

Untrusted solvers plus small primal-dual certificates allow:

- algorithmic pluralism;
- solver competition;
- hardware acceleration outside the TCB;
- exact validation of approximate search;
- reuse across privacy tiers;
- independently competing lower- and upper-bound solvers.

That is a genuine architectural moat, not just a restatement of KKT conditions.

### 3. Privacy tier as a type

Making privacy posture compile-time/product-level rather than marketing-level is strong. It creates a disciplined answer to “which party sees what?”—provided the actual threshold and solver assumptions are represented in the type.

A future refinement should type not just `Dark/Shielded/Open`, but the viewer/corruption model:

- public-private, solver-visible;
- honest-threshold dark;
- malicious-threshold dark;
- TEE-confidential;
- aggregate-only decryptable.

### 4. Fairness by mechanism, not mempool concealment

Uniform batch price removes intra-batch ordering value independently of whether the bid layer is commit–reveal, ZK, threshold encrypted, or FHE. That primitive independence is defensible.

### 5. A plausible PQ route

The STARK/privacy architecture and lattice-additive plan are genuinely better positioned for PQ migration than DLog-heavy confidential-token systems. But this is an architectural lead, not yet an end-to-end PQ product.

## The hardest objections

### Cryptographer

1. **The reveal-nothing theorem is conditional.** Until `HidingFriPcs` is discharged against the actual PCS/transcript, unconditional ZK marketing is premature.
2. **Value binding remains DLog-based.** Shor breaks the no-mint/value-binding surface even if transcript privacy is PQ. This is a blocker for “end-to-end PQ,” not for classical deployment.
3. **Threshold Tier-0 is not no-viewer against threshold collusion.** The corruption model must be corrected or the key architecture changed.
4. **Ciphertext-to-proof correspondence is the attack surface.** The proof must bind the exact ciphertext aggregate, quantization, ring interpretation, and settled allocation.
5. **Field wrap and signed translation matter.** Exact integer statements do not survive silently reducing into BabyBear or an RLWE plaintext ring.
6. **Scheme switching is unmeasured.** Security parameters cannot be inherited informally from CHIMERA/PEGASUS examples.

### Quant/microstructure theorist

1. **Uniform price is not strategyproof.** Demand reduction, shading, marginal rationing, and false-name behavior remain.
2. **The proof certifies the stated objective, not that the objective is good.**
3. **Arrival and inclusion are outside static optimality.** A solver can be optimal on a censored book.
4. **Oracle/mark correctness is assumed, not proved.** An attested mark is still an economic input.
5. **CFMM solvency is not execution quality.** A pool can remain nonnegative while providing catastrophic price impact.
6. **Package approximation may be vacuous.** A small LP-solver gap does not imply a small integrality gap.
7. **Batch length is an economic parameter.** Longer batches improve aggregation/privacy and worsen immediacy/adverse selection.

### Institutional allocator

1. A solo live node is not a production network.
2. A pre-generated cross-chain fixture is not operational settlement.
3. A known-toxic-waste ceremony is unacceptable for production custody.
4. Unbuilt custody, legal, halt, upgrade, and recovery processes matter more than an additional mechanism theorem.
5. Tier-0 latency and threshold liveness are operational risks.
6. The launchpad’s most compelling conduct protections are not yet one end-to-end deployed covenant.
7. FPGA estimates are not capacity commitments.

## Product-killer versus scheduled sharpening

| Gap | Severity |
|---|---|
| `HidingFriPcs` undischarged | Product-killer for unconditional Tier-1 ZK/reveal-nothing claim; not for integrity |
| Classical Pedersen/Schnorr/Bulletproof binding | Product-killer for end-to-end PQ claim; scheduled migration for classical MVP |
| Threshold holders can decrypt arbitrary ciphertexts | Product-killer for “even a fully corrupt committee cannot see orders” |
| Tier-0 measured minutes on CPU | Product-killer for high-cadence dark markets today; not for Tier 1/Open |
| Scheme-switch unmeasured | Research/engineering blocker to choosing the Tier-0 architecture |
| Solo node, no durable federation | Product-killer for production availability/decentralization claims |
| Cross-chain fixture, selector mismatch | Product-killer for live cross-chain settlement claim |
| Known-toxic-waste dev ceremony | Product-killer for institutional production use |
| Conduct-bond weld incomplete | Major product differentiator missing, but not a soundness failure in the base launch |
| Constant-product policy quality | Scheduled mechanism refinement; the pool itself is now built |
| FPGA scaffolding only | Not a product-killer unless Tier 0 depends on its promised latency |
| N-leg ring AIR residuals | Sharpening/integration risk; the blanket “unbuilt” description is stale |

## Competitive interpretation

Zama is ahead on product surface, standards, mainnet use, SDKs, compliance narrative, and operating scale. ERC-7984 is a concrete standardization effort. [EIP-7984](https://eips.ethereum.org/EIPS/eip-7984).

dregg should not attempt to beat Zama by becoming another general FHE plumbing provider. Its viable position is:

> A proof-carrying financial mechanism layer whose economic correctness is machine-checked and whose privacy backend can be swapped or dialed.

That is narrower, more credible, and harder to copy.

“Committee-free Tier 1” remains a real distinction only in the public-verification sense: there is no threshold decryption committee, but the plaintext solver is a confidentiality principal. “PQ privacy” remains real only if it is not rhetorically expanded into PQ value binding.

---

# The three highest-leverage next moves

## 1. Ship one faithful launch receipt end to end—Open first

Build the smallest production-shaped vertical slice:

- persistent multi-node federation;
- fix faithful per-trader settlement;
- live turn → proof → shrink/wrap → public testnet settlement;
- production-safe or transparent/updatable setup;
- immutable creator vesting escrow;
- current constant-product pool/floor;
- buyer and institution receipt;
- explicit batch-inclusion and finality semantics.

Do it at Tier 2/Open first. This realizes the strongest existing moat without placing FHE, FPGA, or unfinished privacy assumptions on the critical path.

The first institutional demonstration should be: “Here is the launch, the exact accepted book, the proof, each allocation, supply authority, settlement, reserves, and creator covenant”—not “here is a simulated dark clear.”

## 2. Make the privacy statements literally true

Treat these as one security-claim closure program:

1. discharge `HidingFriPcs` against the deployed transcript;
2. land PQ value binding/range/conservation;
3. specify and implement the Tier-0 corruption model—honest threshold, aggregate-only decryption, or a stronger constrained/multi-key design.

This turns the privacy/PQ architecture from a promising design into a defensible advantage.

## 3. Run the crossing bake-off before committing to FPGA RTL

Implement and measure:

- exact RLWE additive aggregation;
- threshold-MPC output-boundary clearing;
- pure-FHE batched scan;
- pure-FHE adaptive search;
- two-boundary proof binding.

Only after the result should the project decide whether F2 needs:

- a PBS crossing appliance;
- only key-switch/extraction acceleration;
- or no crossing accelerator because output-boundary MPC wins.

This move has unusually high option value: it can eliminate the presumed bottleneck, prevent a costly V80→VU47P port in the wrong architecture, and determine the honest Tier-0 latency claim.

The conduct bond should be the next launch feature inside move 1: structural vesting first, then a quote-denominated rolling exposure bond. A new in-house NTT/PBS core should not enter the top-three roadmap.
tokens used
309,587
