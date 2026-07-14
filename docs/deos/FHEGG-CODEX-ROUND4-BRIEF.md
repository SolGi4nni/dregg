# fhEgg Round-4 Brief — the WHOLE-SYSTEM frontier, for a world-class analyst

*Self-contained aggregation of the fhEgg / DrEX / dregg-launchpad line, written to ground a top-tier
cryptographer + market-microstructure/mechanism-design theorist + hardware architect on the CURRENT
open frontier. Three prior `brief → codex → curate` rounds landed real content (R1: the `Cert-F`
duality certificate + the `ZKOpenRel_R` categorical frame; R2: the `fhIR` typed product language +
`Price-Cert` derivatives; R3: the sound-quantized Tier-0 unlock — "approximation proposes, exact
quantized translation-validation disposes" + the `mint_safe_quantization` Lean lemma + a valid
disproof-and-replacement of the `GuardedTraceClosure` conjecture). This round BROADENS from the pure
math frontier to the whole system: the trade EXECUTION ENGINE, the FPGA acceleration path, the
LAUNCHPAD product, and an adversarial ROADMAP read. Analysis + ideation, NOT code. Go deep; cite where
known results apply; flag genuine novelty vs restatement.*

---

## 0. The system in one screen

dregg is a proof-carrying state machine. A **turn** = "the exercise of an attenuable proof-carrying
token over owned state, leaving a receipt." **DrEX** is its private exchange. The **fhEgg kernel** is
the observation that a **batch uniform-price call auction is an AGGREGATION, not a matching**: limit
orders sum into a price-indexed cumulative demand/supply curve (a commutative-monoid fold of unary
step-increments), and clearing is a **single monotone crossing** `p* = min{p : D(p) ≥ S(p)}`. The
expensive "private matching" (oblivious sort, `O(N log²N)` bootstraps) evaporates into an `O(N·K)`
additive fold + an `O(K)` crossing (K = price-bucket resolution, N = orders).

Generalized (the **Private Convex Engine**): many financial products are convex programs, and a
first-order/operator-splitting solver run `T` times is exactly the fhEgg shape iterated — each
iteration is `x ← prox(x − τ·A·x)`: a homomorphic-linear step with a **public** matrix A over
committed/encrypted data (the cheap primitive) + one small prox (a clamp/soft-threshold/projection =
one bounded nonlinearity). fhEgg is `T=1`.

**The killer move — verify, don't find.** A convex optimum is certified by a **primal-dual pair with
small duality gap**, and the gap is a **linear functional**. So the solver is an *untrusted search*
and the **duality gap is the cheap checked certificate** — translation validation for optimization.
The STARK never proves convergence; it proves "here is a primal-dual pair, its gap ≤ ε."

**Three product tiers on one verified kernel.** Tier 0 DARK (FHE, no viewer — nobody ever sees an
order; threshold-decrypt only `p*`; PQ by construction); Tier 1 SHIELDED (STARK-ZK,
private-from-the-world, one solver sees plaintext; exposes only `[nullifier, merkle_root,
value_binding]` per leg); Tier 2 OPEN (public book + STARK of correctness). The tier is a **type in
`fhIR`** (the DSL): a product is well-typed at Tier T iff it compiles at tier T (monotone `Tier0 ⇒
Tier1 ⇒ Tier2`). Same soundness kernel at every tier; only privacy/generality/cost vary.

---

## 1. What is BUILT and VERIFIED (ground truth — grounded against the tree this pass; do not reconstruct it)

### 1.1 The execution engine — an **8-mechanism family** on ONE `Cert-F` verify-not-find kernel (`fhegg-solver/`, **60/60 tests, confirmed**)

The membership criterion (codex R3's sharpening): *does the mechanism admit a small, trace-independent
upper-bound certificate whose feasibility + conservation are cheaply checkable over **public**
operators?* The eight built modules (`fhegg-solver/src/`):

1. **Uniform-price call auction** (`clearing.rs`) — the fold + one crossing (`T=1`); cert = Σ-balance
   / crossing; Lean `FhEggClearing.lean` (`clearedBatch_conserves`, `clearedBatch_uniform`,
   `clearedBatch_optimal`, the `Fstep`-monotone least-fixed-point crossing).
2. **Volume-max circulation LP** (`clearing.rs` flow path) `max wᵀf s.t. Af=0, 0≤f≤c` — cert = the
   **`Cert-F` duality gap** `cᵀs − wᵀf ≤ ε`; Lean `CertF.lean` (`weak_duality`,
   `certifies_epsilon_optimal` KEYSTONE — *independent of how f,π,s were found*, `gap_nonneg`).
3. **Fisher / welfare-max (Eisenberg–Gale)** (`fisher.rs`) — KKT certificate `p_j ≥ β_i v_ij` +
   budget exhaustion + complementarity `x_ij(p_j − β_i v_ij)=0`; **quadratic**, not Cert-F-linear.
4. **Discriminatory / pay-as-bid** (`discriminatory.rs`) — allocation-LP dual (bid×fill is
   bilinear-in-witness; incentives *not* certified — an honest edge).
5. **CFMM routing** (`cfmm.rs`) — pool-local KKT / normal-cone (Angeris convex; convex until fixed
   venue costs).
6. **Price-Cert derivatives** (`pricecert.rs`) — state-price LP `max_{π≥0} hᵀπ s.t. Hᵀπ=a` +
   superhedging dual `min_y aᵀy s.t. Hy≥h`; American/Bermudan = the Snell-envelope LP; Lean
   `PriceCert.lean` (`price_cert_certifies`, `snell_feasible_upper_bound`).
7. **Convex QP** (`qp.rs`) `min ½xᵀPx + qᵀx` (public P) — cert = the **`CertQp` KKT/complementarity
   gap**; Lean `CertQp.lean` (`qp_certifies_epsilon_optimal`). Named edge: the keystone needs *exact*
   stationarity; the inexact-dual-residual case adds an `ε_stat·diam(box)` term, **not proved**.
8. **Package / combinatorial certified-approximation** (`package.rs`) — the NP-hard boundary. Exact
   all-or-nothing *selection* `max Σwᵢxᵢ s.t. Σxᵢaᵢ=0, xᵢ∈{0,1}` is subset-sum / set-packing
   (NP-hard; a public topology does **not** remove integrality). The resolution is the verify-not-find
   Lagrangian sandwich `V(x) ≤ OPT_IP ≤ OPT_LP ≤ U_LP`: an **LP dual certifies an
   additive-approximation guarantee** for the NP-hard mechanism (exact iff zero gap; **sufficient, not
   complete**). Plus the poly-time `[0,1]` partial-fill flow-LP relaxation certified by `Cert-F` (the
   integer boundary and the relaxation **must not be conflated**).

**The Tier-1 STARK bridge is REAL and grounded.** `fhegg-solver/src/air.rs` emits the `Cert-F` check
as a structured `ConstraintSystem` — the `n + 4m + 1` linear rows `conservation(==0) · box(≥0) ·
slack_sign(≥0) · dual_feas(≥0) · duality_gap(≤ε)` — the SAME rows `metatheory/Market/CertF.lean`
proves sound (`certCircuit`, `satisfied certCircuit ↔ certificate`). `circuit-prove/src/cert_f_air.rs`
proves a `Cert-F` certificate in a **REAL dregg BabyBear+FRI STARK** over that verified check
(`prove_cert_f`, **14/14 tests, confirmed, `--release`**) — i.e. the certificate is verified-EMITTED
from the Lean-proved checker into a real STARK, hiding `(f,π,s)`. `fhIR-0` (`fhir/`, **36/36 tests,
confirmed**) is the tier-as-type DSL (`ast.rs`, `tier.rs`, `compile.rs`, `products.rs`,
`solver_bridge.rs`); only `compiles ⇒ admissible` is proven — the full iff is a named target.

### 1.2 The verified categorical + soundness spine (`metatheory/Market/*.lean`, kernel-clean)

- **`RevealNothing.lean`** — `View ≈ Sim∘Q` over a leakage functor Q (batch size / price / total /
  root are *deliberately public*); the reveal-nothing theorem is proven **floor-conditional** on the
  `HidingFriPcs` PCS-ZK obligation (carried as a bundle FIELD, not `sorry`, not yet a discharged
  theorem — this is a live residual).
- **`ZKOpenRel.lean`** — the resource-graded open-relation category; `d` a strong-monoidal functor;
  **conservation = the zero-defect subcategory `d⁻¹(0)`**; all four objects (circulation / convex /
  auction / turn) recovered as instances. R3's `GuardedTraceClosure` result LANDED:
  `guardedTraceClosure_refuted` (the deployed general conjecture is FALSE — a `Bool`-negation feedback
  witness) + `traceAdmissible_guarded` (the true replacement, Knaster–Tarski via `OrderHom.lfp`,
  landing on the proven crossing operator `crossing_fixed`/`Fstep_monotone`); `ZKUnification` now
  INHABITED over the true `AdmissibleTraceClosure`.
- **PQ commitment posture.** Tier-1 privacy (Pedersen perfect hiding + `HidingFriPcs` statistical-ZK)
  is already PQ. **Value-binding today is classical DLog** (Pedersen/Ristretto + Schnorr excess +
  Bulletproof range = Shor-broken). Option A (Poseidon2 hash-commitment + in-AIR conservation +
  in-AIR range) is *scoped but not landed* — an "M-difficulty build." The PQ **lattice-additive**
  aggregation-fold (aggregating *independently-produced* commitments before a common proof exists —
  BDLOP `Ar + Gv mod q`, binding = Module-SIS) is the R3 named residual carrier.

### 1.3 The FPGA acceleration path (`FHEGG-FPGA-ACCELERATOR.md`, `FHEGG-RTL-VERIFIED-HARDWARE.md`) — **SCAFFOLDING + a seed, honestly**

- **No FPGA accelerator is built.** What exists: a Lean-4 netlist DSL that compiles (`lake build`, no
  mathlib) with a worked full-adder → ripple-adder emitting real synthesizable Verilog
  (`fullAdder_realizes` proven sorry-free); golden models for the mint-safe accumulator + NTT-butterfly
  combiner with soundness/invertibility theorems. Explicitly "**NOT the NTT, NOT the PBS, NOT a
  bitstream**."
- **Target hardware:** AWS EC2 **F2 rental** (`f2.48xlarge`: 8× AMD Virtex UltraScale+ HBM **VU47P**,
  16 GiB HBM @ 460 GB/s each, 9,024 DSP, ~$15.84/hr). **No in-house silicon** (custom silicon is
  rung-2: 1–2 yr, $50–200M). HBM is why F2 specifically (keeps NTT/PBS pipelines fed).
- **The workload:** the accelerator targets the **FHE fold (Tier-0 dark clear), NOT the STARK prover**
  (STARK stays on GPU). Under exact-integer TFHE, carry-propagating adds are PBS-class, so aggregation
  dominates — up to ~45× the crossing. Sizing (order-of-magnitude, ±3–5×): one F2 turns a measured
  ~488 s M2-CPU clear of a 512×64 batch into ~0.15–0.7 s (~700–3,000×), at ~40–80k aggregate PBS/s.
- **The verified-core / productive-bulk split:** a *small* formally-verified trusted core (the
  conservation/mint-safe gate + the **crossing comparator that gates acceptance**) vs a *productive*
  HDL bulk for the NTT/PBS datapath where a bug "costs speed or a failed proof, not soundness"
  (property-tested + differentially-checked against `tfhe-rs`, "must not be dark-washed as verified").
- **Zama HPU:** both docs recommend **wrapping Zama's open-source SystemVerilog HPU** for the PBS core
  (~13k PBS/s @ 350 MHz on 7nm Alveo V80) rather than rebuilding the NTT/PBS. dregg's differentiator
  is explicitly *not* the NTT core — it is "the datapath married to the STARK-attested,
  conservation-gated, Constitution-bound clearing."
- **Named residuals:** VU47P-vs-V80 node gap (±~2×, only P&R tightens it); un-modeled IO/orchestration
  (2–3×); a Tier-1 confidential-compute hole (F2 is Nitro-attestation-only; a Nitro Enclave cannot
  drive the FPGA — no PCIe passthrough; attested FPGA DMA is not available on EC2 F2); the co-sim seam
  (`toVerilog` trusted-by-construction, not proven — Lean does not model Verilog); no mature verified
  Lean-4 HDL exists.

### 1.4 The launchpad (`DREGG-LAUNCHPAD-DESIGN.md`, `LAUNCHPAD-OPPORTUNITY.md`) — "verify me, not trust me"

A launch is **four verified turns**: (1) disclosed-supply creation → (2) sealed-bid uniform-price
raise → (3) solvent-pool graduation → (4) non-custodial cross-chain settlement. Built EVM contracts
(`chain/contracts/launchpad/`): `DreggLaunchpad.sol`, `DreggLaunchToken.sol` (hard-capped single-mint),
`DreggSolventPool.sol`, `ILaunchEligibility.sol`, `IClearingAttestor.sol`. Gates: **`DreggLaunchpad.t.sol`
= 16/16 on-chain-enforced tests (confirmed)** + the **`launchpad-web` fairness gate = 29/29**
(`gate/e2e.mjs`: spins anvil, deploys the real contract, runs a full fair launch + adversarial checks
against deployed bytecode). Contract targets **Robinhood Chain** (Arbitrum-Orbit L2, chainId 46630).

**Three of seven abuse vectors are PROVEN UNCONSTRUCTABLE** (a theorem forbids them):
- **Snipe/front-run** — killed by **batch uniform-price clearing** (one price removes the value of
  ordering); `uniform_price_no_arbitrage` (`Market/Optimality.lean`). *Primitive-independent* — the
  robust lever; the sealed/shielded layer is defense-in-depth over it, not the load-bearing part.
- **Hidden supply** — the supply-authority biconditional `execMintA_iff_spec` (mints **iff**
  `MintASpec`) + `no_insert` on the cleared book (`KeystoneAuditSupply.lean`).
- **Silent LP/mint-drain rug** — `pool_solvent_forever` (`Market/Liquidity.lean`): pool reserve never
  negative under any fill schedule; no creator-withdrawal door + disclosed mint.

**The design-not-shipped residuals (honest):** the **conduct bond** ("bonded-not-boosted": creator
posts a bond slashed on replayable misconduct predicates — primary `dump_beyond_schedule` =
`soldSoFar(creator) > unlocked(schedule, epoch)`; slashes compensate holders pro-rata, never the
platform) has its bond+slash *conservation* PROVED for relay operators (`relay_dispute.rs`), but
**wiring it to launch predicates + the `MarketRefinement` slash-leg alignment is an OPEN weld**. The
**`x·y=k` graduation curve is UNBUILT** — layered as a pricing policy above the proven
never-insolvent floor. **Shielded/ZK-sealed bids** (`Market/ShieldedClearing.lean`) are SPEC/MODEL
(toy Merkle stand-ins, unbuilt ring AIR); the MVP floor is a sealed commit→reveal (`SealedAuction.lean`,
`reveal_binds_committed`, `uncommitted_cannot_win` — PROVED but a *weak* primitive: non-reveal
griefing, metadata leak, 2-tx capital lock). **Sybil is NOT solved** — uniform price neutralizes the
sybil *advantage* (proved), but one-human-≠-many-wallets is an out-of-scope identity-layer problem.

### 1.5 Deployment reality (`DEVNET-DEPLOYMENT-REALITY.md`) — the honest floor

- **devnet = solo-node, NOT federation.** A solo `dregg-node` (committee-of-ONE) is genuinely LIVE on
  private infra: `state_producer:"lean"` (links the compiled Lean executor), `full_turn_proving:true`
  (every committed turn gets a self-verified full-turn STARK). "This is not a mock." But it binds
  `127.0.0.1`, reachable only over LAN/tailnet — "nothing is on the public internet." The n=2/n=3
  federation is REAL CODE proven by *ephemeral* QUIC-test runs, **not a standing durable federation**.
- **cross-chain = fixture, NOT a live turn.** Base-Sepolia has a real dregg state-transition proof
  settled on-chain (STARK apex → BN254 shrink → gnark → Groth16), but it is a **pre-generated fixture
  proof** under a **dev single-party Groth16 ceremony** (toxic-waste-known), NOT a proof minted from a
  live `/settle`. Solana/Cosmos settlement programs are BUILT+tested, NOT deployed. The wrap linchpin
  "is not yet end-to-end from a live turn" (blocked partly on a rotated-IR `setFieldVmDescriptor2`
  selector bug that forces clearing to settle as value *moved*, not per-trader allocations).
- Public broadcast / mainnet / real tokens / production MPC ceremony are all ember-gated.

### 1.6 Competitive landscape (`ECLIPSE-ZAMA-CONFIDENTIAL-FINANCE.md`)

**Zama** is the reference product in confidential onchain finance: FHE-on-EVM (fhEVM) **live on
Ethereum mainnet since Dec 2025**, a Draft **ERC-7984** confidential-token standard (with OpenZeppelin
+ Inco), a live confidential-yield vault (Zama + Morpho), a Relayer SDK, and a Series B **$57M @ $1B+**
("first FHE unicorn"). Confidentiality rests on a **13-node threshold KMS (~9-of-13 honest-majority)**
in AWS Nitro enclaves that can decrypt on demand. dregg's claimed edges (each graded in the doc):
committee-free Tier-1 (no decryption committee), fair-by-proof (sniping un-representable as a Lean
theorem), machine-checked (vs audits-only), PQ on the privacy/proof surface, and a *dial*
(Dark/Shielded/Open) vs one fixed posture — but Zama is decisively ahead on **shipped mainnet product,
standardization (ERC-7984), SDK/UX, live yield, compliance framing, and funding**. "dregg is building
what Zama has shipped."

---

## 2. The empirical fact that reshaped the Tier-0 frontier (from R3, load-bearing here)

The kernel's original "addition ≈ free" premise is **REFUTED for exact-integer TFHE**: exact multi-bit
integer conservation needs **carry propagation**, and each carry is a **PBS-class** op — so the
`O(N·K)` fold is PBS-dominated (**minutes at N in the low hundreds**; breaks past a minute cadence at N
in the thousands). Published encrypted sorts: ~22 s for 128 elements (CKKS), ~36 s for 64 (rank-sort).

R3's unlock: a **lattice-additive / CKKS-additive fold** (native `R_q` ring addition — no carry, no
bootstrap) is **one object solving two problems** — it recovers Tier-0 speed AND closes the
PQ-commitment residual. **But this MOVES the bottleneck.** Once the additive fold lifts N off the cost
bill, the residual is the **crossing** — the private comparison `ge + select`, which is `O(K)`,
**N-independent**, and **cannot be additive** (sign/min/max/first-crossing are not affine; a PBS, an
approximate polynomial, MPC, or disclosure is *mathematically unavoidable*). On FPGA the crossing costs
`~2.8·K` PBS-equiv (~180 PBS-equiv at K=64). **So the crossing is the NEW Tier-0 floor** — on the
order of ~12–17 s of the residual private-comparison work at deployment K, and the **BFV/BGV→TFHE
scheme-switch** needed to reach it (CHIMERA/PEGASUS-style coefficient extraction + key-switch from the
exact-quantized fold ring into LWE/TFHE for one programmable-bootstrap LUT) is an **un-measured seam**.
This bottleneck — the private comparison / crossing — is the highest-value target of Question 1.

---

## 3. THE FOUR OPEN QUESTIONS (pose precisely; go deepest on the crossing and the launchpad mechanisms)

### Q1 ⚑ THE TRADE EXECUTION ENGINE FRONTIER (deepest on the private-comparison / crossing bottleneck)

**(a) Is the 8-mechanism family missing anything important?** Name novel mechanisms the verify-not-find
+ tiered structure uniquely enables: **dynamic/streaming clearing** (a certificate that composes across
batches — R3 floated telescoping dual-potentials `ε_{1:T} = Σε_t`; sharpen it into a real
frequent-batch product); **cross-tier atomic clearing** (part of the book Tier-0-dark, part
Tier-1-shielded, ONE joint certificate — R3 floated direct-summing tier capacities `c = c⁰+c¹+c²`;
is the joint dual actually sound across a privacy boundary?); **intent-based clearing** (solver-competition
/ CoW-style, but with a validity+optimality proof the incumbents lack); a mechanism *designed for the
FHE-cheap regime* where adds are free but comparisons are the metered resource.

**(b) The certified-approximation for package bids.** Is the Lagrangian sandwich `V ≤ OPT_IP ≤ OPT_LP ≤
U_LP` tight? Better rounding / a constant-factor guarantee (pipage, iterative, randomized-rounding with
a certified expected-value bound) rather than a mere additive gap? Where exactly does the
duality/integrality gap blow up, and is there a *certifiable* rounding that stays cheap in-AIR?

**(c) ⚑ THE PRIVATE COMPARISON / CROSSING — the Tier-0 floor. Make it cheaper.** After the additive
fold, the crossing (`p* = min{p : D(p) ≥ S(p)}`, an `O(K)` monotone threshold + select over the
encrypted aggregate) is the irreducible residual — and comparison is provably non-affine. **Concretely:
is there any way to make the private comparison cheaper?** Candidates to evaluate rigorously — a clever
*encoding* where the crossing becomes a lattice-native or arithmetic operation (e.g. the R3
coefficient-difference-polynomial prefix scan already gives all K cumulative buckets in one plaintext
multiply — can the *threshold* itself be read off the packed coefficients without a per-bucket PBS?);
a **batched / amortized comparison** (one PBS deciding many buckets via a packed LUT, or a
binary-search `O(log K)` crossing instead of `O(K)`); a **different mechanism that avoids the comparison
entirely** (e.g. a fixed-point / potential formulation whose optimum is read from an *additive*
invariant, or a design where the authoritative decision is only the two boundary comparisons
`¬Clears(j−1) ∧ Clears(j)` — R3's "comparison-metered clearing"); disclosing the crossing under a
threshold-decrypt of `p*` only (the current Tier-0 posture) and asking whether the comparison can be
*avoided in the encrypted domain* by proving the crossing *after* a minimal reveal. **The
BFV→TFHE scheme-switch seam** — give the best concrete construction (CHIMERA/PEGASUS ring/parameter
choices, the key-switch cost, whether a lattice-native comparison avoids the TFHE hop). This is the
single most valuable engineering-math target of the round.

### Q2 ⚑ DRIVING FPGA FORWARD (contributor-scaffolding, budget-constrained, F2-rental, no silicon)

Given the honest state (§1.3): **what is the HIGHEST-LEVERAGE FPGA work under these constraints?**

- **The datapath.** The FHE-fold accelerator (NTT / PBS datapath) — the key architectural choices for
  the VU47P/HBM target. Is the CKKS-additive-fold-then-crossing decomposition the right one to build to
  (it lifts N off the cost, collapsing per-batch cost to the `O(K)` crossing)? What is the crossing
  bottleneck *on FPGA* specifically, and is there a **novel accelerator idea for the private-comparison
  crossing** (a bespoke comparator pipeline, a packed-LUT PBS array, a systolic threshold-scan) that a
  generic FHE accelerator would not have?
- **Wrap vs build.** Is wrapping Zama's HPU (SystemVerilog PBS core) the right call vs building
  in-house — and if wrapping, what is the *minimal* in-house differentiator (the verified
  conservation/crossing core + HBM streamers + the STARK-attestation binding)? Where does the
  wrap-vs-build line actually maximize leverage per contributor-hour and per rental-dollar?
- **The verified-core / productive-bulk split — is it right?** Is verifying only the small
  conservation + crossing-comparator core (and leaving the NTT/PBS bulk property-tested +
  differentially-checked against `tfhe-rs`) the correct trust boundary, or is there a sharper split?
  What is the highest-value formal target inside the small core?
- The Tier-1 confidential-compute hole on F2 (no attested FPGA DMA; a Nitro Enclave cannot drive the
  FPGA) — is the "split Tier-1 solver + threshold-decrypt custody onto a separate SEV-SNP host" the
  right architecture, or is there a cleaner one?

### Q3 ⚑ LAUNCHPAD FEATURE / MECHANISM DEVELOPMENT (make the anti-rug launchpad WORLD-CLASS + institutional-grade)

The three proven-unconstructable abuses (snipe / hidden-supply / drain) are the wedge. **What features +
mechanisms make it world-class and institution-grade?** Deep mechanism-design ideation wanted:

- **The conduct bond.** Design it *right*: the bond size, the slashing predicates (esp.
  `dump_beyond_schedule`), the restitution routing (pro-rata to holders), and the incentive analysis —
  so a schedule-violating dump is *provably* punished and the bond is *individually rational* to post
  yet *sufficient* to deter. Is there a bonding structure that dominates a flat bond (e.g. a
  bond that scales with unlocked-but-unsold supply, or a continuously-topped skin-in-the-game escrow)?
  What is the game-theoretic equilibrium, and can the deterrence be a *theorem*?
- **The graduation curve.** `x·y=k` (constant-product) vs alternatives (constant-sum near peg,
  concentrated-liquidity, LMSR, a dynamic/step curve) — layered above the proven never-insolvent floor.
  Which graduation mechanism best resists the post-graduation dump and rewards genuine price discovery?
- **Shielded / sealed bidding** — the right primitive beyond the commit→reveal MVP (which has
  non-reveal griefing + metadata leak): a single-phase ZK-sealed bid, or a threshold-encrypted batch.
- **Sybil / uniqueness resistance (the identity layer)** — the honest open problem. What identity /
  proof-of-personhood layer is right for a permissionless launchpad, and how does it compose with the
  privacy tiers (can uniqueness be proven *without* deanonymizing)?
- **Novel anti-abuse mechanisms beyond the three proven** — wash-trading detection (a bonded attention
  market? an OCIP screener?), insider/pre-mine detection, coordinated-cohort (the "1,012 sniper
  cohorts") resistance, and any abuse a *verified* launchpad can forbid that a mitigation-based one
  cannot.
- **The verification / receipt UX** — what makes "verify me, not trust me" *tangible* to a buyer and an
  institution (buyer re-derives the clearing price, checks disclosed supply against its on-chain
  commitment, reads distribution from Transfer logs). What is the minimal receipt that carries maximal
  conviction?
- **Fair vesting / distribution.** Anti-concentration, anti-flip vesting; a distribution that rewards
  conviction over speed.
- **What would an institution demand** before touching this (custody, compliance/KYC composition with
  privacy, audit trail, redemption guarantees, circuit-breaker/halt semantics)?

### Q4 ⚑ CRITICAL ROADMAP READ (adversarial — an outside expert's honest assessment)

Read the whole system (§1) as a skeptical cryptographer + quant + institutional allocator. Precisely:

- **Where is dregg GENUINELY ahead?** The defensible, hard-to-replicate advantages (machine-checked
  soundness, verify-not-find, the tiered dial, committee-free Tier-1, PQ-on-privacy).
- **Where are the REAL risks and gaps?** Be adversarial. The floor-conditional reveal-nothing
  (`HidingFriPcs` PCS-ZK obligation undischarged), the classical-DLog value-binding (Shor-broken; PQ
  fix scoped not landed), the measured-slow Tier-0 (N ≈ 32–512 at minute cadence), the solo-node "not a
  federation", the fixture-not-live cross-chain, the toxic-waste-known dev ceremony, the design-not-shipped
  launchpad mechanisms, the FPGA being scaffolding-not-silicon. Which of these is a *product-killer* vs a
  *scheduled sharpening*? What would each of the three skeptics (cryptographer / quant / institution)
  poke at HARDEST?
- **The 3 highest-leverage next moves.** Given finite resources, what three moves maximize the ratio of
  (defensible-advantage realized) / (effort), and in what order?

---

*You are a world-class cryptographer + market-microstructure/mechanism-design expert + hardware
architect. Deepest NOVEL analysis + concrete ideas on the four areas — ESPECIALLY the
private-comparison / crossing bottleneck (Q1c) and the launchpad mechanism-design (Q3). Rigorous; cite
where known results apply; flag genuine novelty vs restatement. Analysis + ideation, not code — go
deep.*
