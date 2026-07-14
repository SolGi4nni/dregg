# fhEgg — Codex Round 4: the Whole-System Frontier, Captured + Assessed

*Fourth `brief → codex → capture+assess` round (the pattern that landed Cert-F/`ZKOpenRel_R` in R1,
`fhIR`/`Price-Cert` in R2, and the sound-quantized Tier-0 unlock + the `GuardedTraceClosure`
disproof-and-replacement in R3). This round BROADENED from the pure-math frontier to the whole system:
the trade EXECUTION ENGINE, the FPGA acceleration path, the LAUNCHPAD product, and an adversarial
ROADMAP read. This doc holds the run provenance, the single most valuable insight, and codex's analysis
organized by the four areas — each with an HONEST gold-vs-mid assessment. Curated, not pasted;
what-is, present tense; every edge names its grade.*

**The run (real, cited).** `codex exec --skip-git-repo-check` on the R4 brief + a
cryptographer/mechanism-designer/hardware-architect analyst ask; **codex-cli 0.144.1 / GPT-5.6-sol**;
exit 0; **309,587 tokens**; ~40 web searches + it read the durable record (REORIENT/HORIZONLOG/memory),
the eleven briefed deos docs, AND it re-grounded against **the actual tree at HEAD** — reading
`CertF.lean`, `StreamingCert.lean`, `shielded_ring_clearing_nleg_air.rs`, `GraduationPool.lean`,
`DreggSolventPool.sol` and correcting the brief where the tree had moved past it. Full log
`scratchpad/codex-round4.log`; the curated final answer `scratchpad/codex-round4-answer.md` (the brief
is `docs/deos/FHEGG-CODEX-ROUND4-BRIEF.md`). It engaged adversarially — it opened by **correcting three
of the brief's own factual claims and one load-bearing latency number** (below), which is the behavior
that makes the pattern worth running.

---

## Headline (the single most valuable insight)

**"The crossing's nonlinearity is irreducible; paying for it INSIDE TFHE is not."** Codex's crux move
on the private-comparison bottleneck (Q1c, the round's designated highest-value target) is to *reframe
the whole problem*. There is **no clever encoding** that makes an exact crossing an affine/linear
operation over the ciphertext ring (§Q1.3.1 below is a clean impossibility argument). But because
**`p*` is DELIBERATELY public**, you do not have to compute the comparison inside FHE at all. The
highest-value architecture is **output-boundary MPC**: keep the aggregate curve under exact RLWE
encryption, have the threshold parties convert only the *selected* coefficients into malicious-secure
additive shares (verifiable partial decryption + noise smudging), run the comparison in MPC, reveal
only `p*` (or the monotone sign vector, which under a fixed tie rule is *determined by* `p*` — no extra
leakage), and let the STARK receipt prove the two boundary inequalities against the committed
aggregate. **This eliminates the un-measured BFV→TFHE scheme-switch seam entirely** — the seam the
brief flagged as the crux — at the cost of an online threshold/MPC dependency the product's public-`p*`
posture already implies.

Riding on the same move, codex delivered the round's **most important cryptographic model correction**:
a standard threshold-FHE public key does **not** cryptographically constrain the key holders to decrypt
*only* `p*`. A colluding threshold subset can apply the decryption protocol to any submitted order
ciphertext. So **"nobody ever sees an order" is a POLICY statement, not a cryptographic no-viewer
guarantee** — Tier-0's headline privacy claim is overstated, and this is one of the highest-priority
model fixes (four honest repair options in §Q1.3.4). **Assessment: GOLD** — a genuine reframe of the
designated crux plus a load-bearing honesty correction, both verified against the real system posture.

**The three factual corrections + one numerical correction codex forced (all verified this pass):**
1. **`StreamingCert.lean` exists and proves only *independent* per-batch `Σε_t` composition** — I
   confirmed `streaming_cert_telescopes` sums independent-LP gaps (`lp : Fin T → FlowLP`, no state
   coupling); the *state-coupled* frequent-batch telescoping with inventory potentials is genuinely
   NOT yet proven (this is codex's Q1.A next-theorem — a correctly-identified real gap).
2. **The N-leg shielded-ring AIR exists** (`circuit-prove/src/shielded_ring_clearing_nleg_air.rs`,
   1129 lines) — the blanket "unbuilt ring AIR" in the launchpad residuals is stale; the real seams are
   full commitment semantics / deployed widths+VKs / reveal-nothing.
3. **The constant-product graduation pool exists** (`DreggSolventPool.sol` + `GraduationPool.lean`) —
   the brief's "`x·y=k` UNBUILT" is stale; its *economic-quality* properties remain open, its existence
   does not.
4. **The "~12–17 s crossing floor" is a CPU residual, NOT the modeled F2 latency.** `180 PBS-equiv` is
   ~9–13 s at the measured M2-CPU PBS rate, but ~**2.3–4.5 ms across an 8-FPGA F2** (~14 ms at Zama
   HPU's 13k PBS/s). On F2 the crossing compute is milliseconds; the **un-measured scheme-switch, key
   loading, PCIe, and orchestration seams may dominate** — so the honest open number is those seams,
   not the comparison itself. *(This corrects a load-bearing framing in my own brief.)*

---

# §A — Q1: THE EXECUTION-ENGINE FRONTIER (deepest on the private crossing)

### What codex proposed

**The family is missing TIME and COMPOSITION, not another static optimizer.** The eight mechanisms
cover a broad static frontier; the real omissions are mechanisms whose correctness depends on state
across time, shared constraints across privacy domains, or adversarial solver selection. Four
proposals:

- **A. State-coupled frequent-batch clearing (New proposal).** With inventory/risk state
  `z_t = z_{t-1} + B_t f_t`, the honest certificate is `OPT_{1:T} − V ≤ Σε_t + Φ_T(z_T) − Φ_0(z_0)`
  where `Φ_t` is a *certified dual potential* for inventory/collateral/liquidity/risk; the per-batch
  receipts telescope, cancelling the internal potentials. Distinct from `StreamingCert`'s independent
  sum. With the honest online qualification: an online system cannot certify ex-post welfare optimality
  against unarrived orders — it certifies one of {conditional-on-state, finite-horizon-vs-declared-set,
  regret-vs-comparator, prefix-optimal-given-terminal-value}. The receipt must distinguish *allocation*
  optimality from *inclusion/censorship* fairness (Budish–Cramton–Shim frequent-batch design).
- **B. Cross-tier atomic clearing (Derived, + a new proof-composition problem).** The joint dual is
  sound across a privacy boundary — "privacy does not change weak duality" — but `c = c⁰+c¹+c²` alone
  is insufficient: separately proving each `A_r f_r = 0` *forbids actual cross-tier exchange*. The
  useful construction proves **hidden** tier-local boundary flows `b_r = A_r f_r` and exposes only
  `Σ b_r = 0`, with one shared dual `π`, disjoint/linked nullifier domains, and **atomic** settlement
  (no tier reveals its favorable leg then aborts another).
- **C. A two-sided solver proof market (New proposal).** Run TWO permissionless competitions — primal
  solvers maximize a certified lower bound `V`, dual solvers minimize a certified upper bound `U`; any
  feasible primal splices with any feasible dual; settle when `U−L ≤ ε`. A primal solver needn't build
  a good dual; a dual solver improves the guarantee without a new allocation; no incumbent monopolizes
  the stack. Stronger than CoW-style single-winner competition — the independently-spliceable
  primal/dual proof market is the novel part.
- **D. A comparison-metered market family (New proposal).** Expose a comparison budget as a
  first-class product parameter; a posted-price/buffered mechanism (public reference-price corridor +
  buffer market-maker absorbing bounded net imbalance, re-anchored by a full auction less often)
  **changes the economic problem instead of disguising the nonlinearity** — the honest way to avoid the
  crossing.

**Package bids: the sandwich is universal but cannot be universally multiplicative.** `V(x) ≤ OPT_IP ≤
OPT_LP ≤ U` is logically tight but economically loose; the one-line counterexample `2x₁−3x₂=0,
xᵢ∈{0,1}` has `OPT_IP=0 < OPT_LP` (unbounded relative integrality gap; public topology does not cure
it). So **structure must be part of the type** — codex gives a table (TU/network → integral exact
Cert-F; gross-substitutes → Walrasian; matroid/submodular → pipage/swap-rounding; k-set-packing →
structure-dependent constant `≈ k−1+1/k`; arbitrary balanced → additive sandwich only). The
**fhEgg-native approximation certificate (Derived, important):** do NOT prove the rounding algorithm in
AIR — let any untrusted solver propose an integral feasible `x`, then check `U ≤ α V(x)` *directly*
(since `OPT_IP ≤ U`, this gives `OPT_IP ≤ α V(x)`). "Rounding proposes; a direct approximation-ratio
certificate disposes" — the package analogue of the Tier-0 quantization rule. Randomized-algorithm
guarantees become a *completeness/liveness* statement; soundness stays deterministic per-instance.

**The private crossing (Q1c — the crux).**
- *§3.1 What cannot work:* no affine map over the ciphertext ring implements a threshold/first-one
  function; the prefix/difference-polynomial multiply is excellent (all cumulative buckets in one
  linear op) but *does not make the sign of a coefficient linear*; a "one-lattice-operation comparison"
  either assumes a trusted decryptor, hides a bootstrap, or needs an impractical message-domain
  polynomial. Goal: **reduce, batch, relocate, or reveal** the minimum necessary nonlinearity.
- *§3.2 Candidate assessment:* batched/multi-value PBS shares decomposition+NTT traffic across many
  bootstraps (BatchBoot reports 43.8× over non-batched `tfhe-rs`) — favors a **parallel scan on a wide
  FPGA** — but does not make `K` unrelated signs one input. **Binary search has an encrypted-index
  trap:** if each comparison stays encrypted, the next midpoint is private → needs a CMUX/oblivious
  lookup, so `O(log K)` signs ⇏ `O(log K)` FHE work; BUT if each sign is safely made public during the
  protocol, the midpoint stays public, the six comparisons are real, and **the sign path is determined
  by `p*` under a fixed tie rule, so a simulator given `p*` reproduces it — no extra leakage**.
  Two-boundary validation `¬Clears(j−1) ∧ Clears(j)` is the correct *verification* (two comparisons)
  but is not itself a private-search *algorithm* — the proposal must come from somewhere.
- *§3.3 Best pure-FHE construction:* the 8-step exact-BFV/BGV pipeline (prefix-multiply → sample-extract
  → key/modulus-switch to TFHE → sign LUT → monotone first-crossing → bind `j` into the receipt);
  CHIMERA (2018/758) is the closer exact-BFV↔TFHE precedent, PEGASUS (2020/1606) for CKKS↔FHEW; the
  switch is NOT a free adapter (extraction, key-switch-key HBM residency, wide *signed* comparison,
  threshold partial-decrypt semantics, cold-vs-warm key loading, PCIe). Two modes: **latency** (extract
  all K, batch the sign bootstraps, priority encoder) vs **work** (adaptive search interleaved across
  markets to hide serial dependency) — "do not assume the second is faster before measuring it."
- *§3.4 Best architecture when `p*` is public — OUTPUT-BOUNDARY MPC (New proposal; highest-value):* the
  headline construction (above), eliminating the scheme switch. **+ the threshold trust correction**
  (the headline honesty item): threshold FHE is not no-viewer against threshold collusion; four honest
  repairs — {state an honest-threshold assumption / secure-aggregation masks so individual orders aren't
  decryptable from the aggregate interface / multi-key/constrained/functional decryption / weaken the
  claim to "compute-server-and-public cannot see; threshold collusion is trusted"}.
- *§3.5 Recommended crossing bake-off:* build+measure the three exact paths (threshold-MPC boundary /
  pure-FHE parallel scan / pure-FHE private search) across `K∈{16,32,64,128}`, 32/48/64-bit bounds,
  1-vs-64+ markets, warm/cold keys, **before substantial RTL**.

### Assessment — **GOLD** on the crux; solid-to-gold across the rest

- **The crossing reframe (§3.1 + §3.4) is the round's payoff and it is correct.** The impossibility
  argument (no affine map is a threshold) is right; the output-boundary-MPC construction genuinely
  *dissolves* the scheme-switch seam by exploiting the fact that `p*` is public anyway; and the
  "monotone sign vector leaks no more than `p*`" observation (simulator-reproducible under a fixed tie
  rule) is a clean, correct leakage argument. This is a real answer to the designated highest-value
  question, not a restatement.
- **The threshold-trust correction is load-bearing and I verified it against the posture.** The Tier-0
  framing throughout the docs is "no viewer — nobody ever sees an order"; codex is right that a plain
  threshold key does not enforce decrypt-only-`p*`, so the honest claim is compute-server-and-public
  privacy under an honest-threshold (or secure-aggregation) assumption. This should be threaded into
  `DREGGFI-PRIVACY-TIERS.md` and the Tier-0 marketing — it is exactly the kind of over-claim the
  "prove-the-floor-false" discipline is built to catch.
- **The state-coupled telescoping (Q1.A) is a correctly-identified, concrete next theorem.** I checked
  `StreamingCert.lean`: `streaming_cert_telescopes` sums independent-LP gaps with no `z_t = z_{t-1} +
  B_t f_t` coupling — so codex's `Φ_t`-potential telescoping is a genuine extension, not already done.
  The online-optimality qualification (four honest flavors + allocation-vs-inclusion) is the right
  sober framing.
- **The package approximation certificate is a genuine, buildable sharpening.** "Check `U ≤ α V(x)`
  directly rather than proving the rounding in AIR" is the correct verify-not-find move for the NP-hard
  boundary, and the "structure must be part of the `fhIR` type" table is the correct honesty (the
  unbounded-integrality-gap counterexample kills any universal multiplicative guarantee). Directly
  actionable on the `fhir/` product surface.
- **Net Q1:** the crossing reframe + threshold correction (gold), the state-coupled telescoping and the
  package certificate (solid-actionable), and the two-sided solver proof market + comparison-metered
  family (novel-in-assembly). **Flag hard:** output-boundary MPC as the Tier-0 crossing architecture,
  and the threshold-trust correction as a required privacy-claim fix.

---

# §B — Q2: DRIVING FPGA FORWARD

### What codex proposed

- **Build a crossing APPLIANCE, not a generic FHE company.** After the additive fold, `N` largely
  disappears; native RLWE adds may be cheap enough on CPU/GPU that shipping them to F2 is
  counterproductive. The FPGA-specific problem is extraction / key-switch / PBS / first-crossing /
  binding. The minimal differentiated block is a **monotone-crossing engine wrapped around a reusable
  FHE core** (HBM-resident keys, double-buffered coefficient streams, fused
  sample-extract/key-switch/PBS, a parallel-sign mode + an adaptive-search mode, a monotone priority
  encoder, a receipt binder, multi-market interleaving). Scale by distributing *independent markets*
  across the 8 cards, NOT by splitting one binary search across cards.
- **Wrap Zama's HPU, but treat "wrap" as a PORT.** V80→VU47P is not bitstream portability (different
  generation, shell, clocking, HBM integration, P&R). Clear boundary: **reuse/port** arithmetic
  kernels + parameter formats + PBS scheduling + `tfhe-rs` interop + known-answer vectors; **build
  in-house** the AWS shell + HBM streamers + exact BFV→LWE extraction/switch seam + crossing scheduler
  + priority block + domain separation + STARK public-input binding; **do NOT initially build** a new
  NTT, a new PBS algorithm, an ASIC-style network, or a multi-FPGA single-ciphertext fabric. First
  stop/go gate = a **placed-and-routed single-card subset with real key sizes**, not a cycle model.
- **⚑ Sharpen the verified-core boundary — the current proposal trusts MORE hardware than
  verify-not-find requires.** If the FPGA is an untrusted search accelerator and the STARK proves the
  crossing + conservation, then an NTT bug → bad proposal/failed proof, a comparator bug → wrong `p*`
  that cannot receive a valid proof — *neither breaks soundness*. So the soundness TCB is {proof
  verifier, Lean↔AIR correspondence, exact ring/field/quantization semantics, binding of the accepted
  proof to (batch, params, assets, `p*`, allocation root, settlement root)}. The **highest-value formal
  hardware-adjacent theorem** is: *any output accepted for `(batch_root, tier, parameter_hash, VK,
  settlement_root)` satisfies the Lean market transition for exactly those public inputs* — covering
  **stale-context / cross-market mixing**, a more realistic accelerator hazard than a faulty full
  adder. In-FPGA formal verification stays valuable for *availability/debugging* (DMA bounds, no stale
  key/batch reuse, no bank aliasing, priority-encoder correctness) — but only becomes a *soundness*
  assumption if the hardware gates settlement without a proof (in which case prove the comparator's
  refinement all the way to the market theorem, or remove it from the TCB).
- **Milestone sequence:** benchmark harness → single-card HPU feasibility port → fused crossing mode →
  adaptive-search mode → multi-card throughput → *only then* optimize the additive fold. The decisive
  number is **p50/p99 "aggregate ciphertext ready → proof-bound `p*` ready"**, not PBS/s.
- **Confidential compute: three planes, not one host.** Don't co-locate the Tier-1 plaintext solver and
  Tier-0 threshold custody on one SEV-SNP host (unnecessary common compromise domain). Tier-0 compute
  (F2 untrusted accelerator) / Tier-1 solver (separate confidential host; ZK handles integrity) /
  key-custody (independent threshold nodes or HSM). F2 is not a SEV-SNP family; Nitro Enclaves have no
  device passthrough. And keep the Tier-1 claim precise: **committee-free public privacy, but one solver
  sees plaintext; ZK proves correct compute, NOT non-exfiltration.**

### Assessment — **GOLD** on the verified-core boundary; correct engineering throughout

- **The verified-core-boundary sharpening is the most valuable FPGA output and it CORRECTS the docs'
  own framing.** The docs propose verifying "the conservation gate + the crossing comparator that gates
  acceptance." Codex's point is exactly right against the verify-not-find architecture: if the STARK
  re-proves the crossing, the FPGA comparator is *untrusted search* and does not belong in the
  soundness TCB — putting it there trusts more hardware than needed. The proposed real theorem
  (accepted-output ⇒ Lean market transition for exactly those public inputs, covering stale-context /
  cross-market mixing) is the correct high-value target and a genuinely sharper trust boundary than the
  "small verified core" the docs describe. This is a real correction to land in
  `FHEGG-FPGA-ACCELERATOR.md` / `FHEGG-RTL-VERIFIED-HARDWARE.md`.
- **"Crossing appliance not FHE company" + "wrap-is-a-port" are the right strategic calls.** The
  reuse/build/don't-build boundary is disciplined and correct; the "P&R single card with real keys as
  the first gate, not a cycle model" is exactly the anti-hand-wave the budget-constrained posture needs.
- **The p50/p99 "aggregate-ready → proof-bound `p*`-ready" metric is the correct north-star number** —
  it subsumes the un-measured scheme-switch/IO seams the numerical correction flagged, which PBS/s
  hides.
- **The three-plane confidential-compute split is correct and it sharpens the docs' "split onto a
  separate SEV-SNP host" into a cleaner separation-of-concerns**; the "ZK proves correct compute, not
  non-exfiltration" tooth is a real Tier-1 honesty item.
- **Net Q2:** the verified-core-boundary theorem (gold, corrects the docs) + the wrap-as-port /
  appliance / p50-p99 discipline (correct, actionable). **Flag hard:** move the comparator OUT of the
  soundness TCB and prove the accepted-output ⇒ Lean-transition theorem instead.

---

# §C — Q3: A WORLD-CLASS LAUNCHPAD MECHANISM

### What codex proposed

- **Conduct bond — FORBID FIRST, BOND SECOND.** `soldSoFar(creator) > unlocked(schedule,epoch)` is hard
  to define from arbitrary transfers (new-wallet ≠ sale; derivatives/affiliates; evadable provenance).
  The stronger mechanism: **mint the creator tranche directly into an immutable, provenance-aware
  vesting escrow**; only `unlocked(schedule,t)` can leave; schedule changes impossible or long-timelocked.
  Then the schedule dump is **unrepresentable, not merely punishable** — the bond covers only residual
  conduct (affiliate coordination, promised-liquidity failure, oracle equivocation, bounded governance
  abuse).
- **⚑ A rolling, exposure-indexed bond (New proposal).** Deterrence holds iff `α_t(a)·S_t(a) ≥ Ḡ_t(a) +
  C_t(a)` for every provable misconduct action `a` (`Ḡ` = certified upper bound on creator gain, `α` =
  detection/enforcement probability, `S` = slash, `C` = enforcement cost); required bond `B_t ≥ max_a
  (Ḡ_t(a)+C_t(a))/α_t(a)`. For auto-replayable predicates `α≈1`; statistical cohort/wash accusations
  have `α≪1` and must NOT trigger automatic confiscation. **A flat bond over-collateralizes quiet
  periods; a rolling bond gives equal deterrence at lower average locked capital.** Bound `Ḡ` by
  observable conservative quantities (extractable cash vs the certified depth curve, unlocked-unsold
  inventory, treasury value, promised-not-deposited liquidity), **denominate in the QUOTE asset not the
  launch token** (a token-denominated bond loses value exactly when misconduct occurs), state a
  bounded-on-ledger-gain assumption honestly (no theorem deters unbounded external shorts). IR:
  `ΔR(B) ≥ (r+ρ)B + E[accidental slash]`; offer a *menu* of verified bond schedules (issuers
  self-separate; the UI reports coverage ratio without the platform selling "boosts").
- **Restitution — a pre-event TIME-WEIGHTED ownership snapshot**, not "pro rata to current holders"
  (which invites flash-acquiring claims after the violation): `w_i = ∫_{t−W}^{t⁻} eligibleBalance_i`,
  excluding creator/affiliates/treasury/AMMs; shielded holders use event-scoped nullifiers + a ZK
  balance-history proof; excess → insurance reserve or burn, never the platform.
- **Graduation — the curve cannot substitute for vesting.** No finite-reserve curve prevents a large
  post-graduation sale from collapsing price. **Recommended v2: a proof-carrying depth ladder (New
  proposal)** — keep the constant-product pool as a *solvent backstop*, but make the authoritative venue
  a **frequent-batch piecewise-linear depth ladder** seeded from the raise clearing price, publishing
  buy/sell capacity per bucket derived from reserves+floor, batching+clearing uniformly, with a
  **certified maximum price move and maximum quote outflow per batch**. Fits the `Cert-F` kernel better
  than a path-dependent AMM; preserves the anti-ordering property post-graduation; permits deterministic
  circuit breakers (halt *matching* only — never withdrawals/settlement/restitution/challenge).
- **Bidding beyond commit–reveal:** one encrypted submission `(Enc(order), π_valid, collateral
  nullifier)`, auto-opened/computed at the deadline — **no reveal tx → no non-reveal griefing**. Three
  honest postures (Tier-1 ZK / threshold-encrypted batch / Tier-0 FHE); a single-phase ZK-sealed bid is
  NOT "nobody sees" unless FHE/MPC throughout.
- **Sybil resistance without public identity:** an anonymous credential (issuer checks uniqueness/KYC →
  ZK proof of validity+policy+non-revocation → launch-scoped nullifier `N = PRF_sk(launchId)`) —
  Coconut / World-ID pattern, multi-issuer policy. **Split invariance must be explicit:** without a
  uniqueness credential the allocation must satisfy `A(b₁+b₂) = A(b₁)+A(b₂)`; per-wallet caps,
  lotteries, concave rewards, "small-buyer bonuses" create a direct Sybil incentive and are safe only
  in a credential-gated pool.
- **Anti-abuse beyond the three:** uniform-price batching is NOT strategyproof (demand reduction —
  Ausubel–Cramton; market it as "no intra-batch ordering advantage," not universal strategyproofness);
  never reward raw volume (that *creates* the wash market); insider/affiliate via committed
  credential-set + ZK non-membership; cohort resistance is economic (split-invariant, one-credential
  caps, no volume rebates, time-weighted rewards) not forensic (a classifier can be *proven-run*, its
  hypothesis cannot be *proven-true*).
- **Fair distribution:** auction *separate vesting-claim tranches* (liquid-now / 30/90/180-day), each
  clearing uniformly — the illiquidity discount emerges from demand, not an admin bonus; honest
  transferability caveat (anti-flip can't be absolute without restricting transfer).
- **The minimal high-conviction receipt:** an explicit public tuple (launch-spec hash, supply/tranche
  root, eligibility root, batch/order root, `p*`, sold qty, allocation root, proof/VK/version hash,
  settlement/finality root, pool reserves/floor, bond state) + a buyer-specific opening; the UI must
  distinguish **Open** (recomputed from public orders) / **Shielded-Dark** (verified by proof over
  hidden orders) / **Attested** (trusted hardware/operator boundary) — a buyer CANNOT rederive the
  hidden curve in Tier-0/1, and claiming otherwise would undermine the privacy story.
- **What institutions demand:** qualified custody+key recovery, legal issuance authority + token
  classification, KYC/AML/sanctions + revocation, selective audit disclosure, independent audits, a
  non-toxic (or transparent/updatable) setup, persistent federation + SLAs, best-execution/solver
  governance, deterministic halt/unwind/trade-bust, bridge/finality limits, timelocked upgrades,
  redemption terms, disaster recovery + proof/key archival. "Lean proves the transition satisfies the
  spec; institutions still ask whether the spec gives them the legal/operational rights they think they
  bought."

### Assessment — **GOLD**, the deepest and most immediately actionable area

- **"Forbid first, bond second" is the correct mechanism-design spine and it strengthens the existing
  design.** The current conduct-bond design slashes on a `dump_beyond_schedule` predicate; codex's
  point — make the schedule dump *unrepresentable* via an immutable vesting escrow so the predicate is
  needed only for residual conduct — is exactly the "unconstructable-not-punished" philosophy the
  launchpad already sells for snipe/hidden-supply/drain, applied to the bond. This is a real upgrade to
  the open conduct-bond weld, not a restatement.
- **The rolling exposure-indexed bond is genuine mechanism design with a clean deterrence theorem.**
  `α·S ≥ Ḡ + C` with `B ≥ max_a (Ḡ+C)/α` is correct and the capital-efficiency argument (flat bond
  over-collateralizes quiet periods) is right; the quote-denomination tooth and the "α≪1 for
  statistical accusations must not auto-confiscate" honesty are the marks of a real designer. The
  **time-weighted pre-event restitution snapshot** (vs flash-acquired claims) is a subtle, correct
  anti-abuse fix that the naive "pro-rata to current holders" design would have shipped broken.
- **The proof-carrying depth ladder is the single sharpest launchpad idea** — it replaces the
  path-dependent AMM graduation with a frequent-batch PWL venue that (a) fits the already-verified
  `Cert-F`/`FhEggClearing` kernel, (b) *preserves the anti-ordering theorem past graduation* (the
  current design's anti-snipe guarantee currently dies at graduation), and (c) yields a certified
  max-price-move/max-outflow per batch — exactly the legible worst-case an institution demands. This is
  novel-in-assembly and directly aligned with the verified spine.
- **Split invariance made explicit is a correctness hinge the design needs.** The observation that
  per-wallet caps / lotteries / concave "fairness" rewards *create* the Sybil incentive they appear to
  fight — and are safe only behind a credential — is a sharp, correct constraint that should be written
  into the allocation rule.
- **Net Q3:** the depth ladder (gold, sharpest idea), the forbid-first vesting escrow + rolling
  exposure bond + time-weighted restitution (gold mechanism design), split-invariance + credential
  nullifier + Open/Dark/Attested receipt (correct, actionable). **Flag hard:** the proof-carrying depth
  ladder as the graduation-v2 that keeps the anti-ordering theorem alive post-graduation.

---

# §D — Q4: ADVERSARIAL ROADMAP READ

### What codex proposed

- **Where genuinely ahead:** (1) *verified semantic continuity* — the machine-checked chain
  spec→Lean-checker→emitted-constraints→real-STARK→proof-bound-settlement, the hardest-to-copy asset;
  (2) *verify-not-find as a market architecture* (algorithmic pluralism, solver competition, HW
  acceleration outside the TCB, exact validation of approximate search, reuse across tiers) — a genuine
  moat, not a KKT restatement; (3) *privacy-tier-as-type* — provided the *actual threshold/solver
  assumptions* are in the type (a future refinement should type the viewer/corruption model, not just
  Dark/Shielded/Open); (4) *fairness by mechanism, not mempool concealment*; (5) *a plausible PQ route*
  (architectural lead, not yet an end-to-end PQ product).
- **The hardest objections, by persona.** *Cryptographer:* reveal-nothing is conditional on
  `HidingFriPcs`; value-binding is DLog (Shor-broken) — blocks "end-to-end PQ"; threshold Tier-0 is not
  no-viewer against collusion; ciphertext↔proof correspondence is the attack surface; field-wrap/signed
  translation matter; scheme-switching is unmeasured. *Quant:* uniform price is not strategyproof
  (demand reduction); the proof certifies the *stated* objective, not that it is good; arrival/inclusion
  is outside static optimality (optimal on a *censored* book); oracle/mark correctness is assumed;
  CFMM solvency ≠ execution quality; package approximation may be vacuous; batch length is an economic
  parameter. *Institution:* a solo node is not a network; a fixture is not settlement; a toxic-waste
  ceremony is unacceptable; unbuilt custody/legal/halt/recovery matter more than another theorem;
  Tier-0 latency + threshold liveness are operational risks; the conduct protections aren't one
  end-to-end covenant yet; FPGA estimates aren't capacity commitments.
- **Product-killer vs scheduled-sharpening (a triage table).** Product-killers *for specific claims*:
  `HidingFriPcs` undischarged (unconditional Tier-1 ZK), DLog binding (end-to-end PQ), threshold can
  decrypt arbitrary ciphertexts ("even a fully corrupt committee cannot see orders"), Tier-0 CPU-minutes
  (high-cadence dark today), solo node (production availability/decentralization), cross-chain fixture
  (live settlement), toxic-waste ceremony (institutional production). Scheduled sharpenings: constant-
  product policy quality, FPGA scaffolding (unless Tier-0 depends on its latency), N-leg AIR residuals
  (the "unbuilt" label is stale), conduct-bond weld (a missing differentiator, not a soundness failure).
- **Competitive interpretation.** dregg should NOT try to beat Zama by becoming another general FHE
  plumbing provider. Its viable position: **"a proof-carrying financial mechanism layer whose economic
  correctness is machine-checked and whose privacy backend can be swapped or dialed"** — narrower, more
  credible, harder to copy. "Committee-free Tier-1" is real only in the public-verification sense (the
  plaintext solver is still a confidentiality principal); "PQ privacy" is real only if not rhetorically
  expanded into PQ value-binding.
- **The three highest-leverage moves.** (1) **Ship one faithful launch receipt end-to-end — OPEN
  first** (persistent multi-node federation + faithful per-trader settlement + live-turn→proof→testnet
  settle + immutable vesting escrow + the current pool + buyer/institution receipt) — realizes the
  strongest existing moat *without* FHE/FPGA/unfinished-privacy on the critical path. (2) **Make the
  privacy statements literally true** — one security-claim-closure program: discharge `HidingFriPcs` +
  land PQ value-binding + specify/implement the Tier-0 corruption model. (3) **Run the crossing bake-off
  before committing to FPGA RTL** — high option value (can eliminate the presumed bottleneck, prevent a
  wrong-architecture V80→VU47P port, and fix the honest Tier-0 latency claim). *Plus:* the conduct bond
  (structural vesting → quote-denominated rolling bond) is the next launch feature inside move 1; a new
  in-house NTT/PBS core should NOT be in the top three.

### Assessment — **GOLD** as a roadmap read; the triage table + the three moves are the deliverable

- **The product-killer-vs-scheduled-sharpening table is the single most useful roadmap artifact** — it
  is honest (it names dregg's real exposures: DLog binding, threshold-not-no-viewer, solo node, fixture
  settlement, toxic-waste ceremony) AND it is *scoped* (each killer kills a *specific claim*, not the
  system) — exactly the "prove the floor false at deployed params, then know what to sharpen" discipline.
  It matches this pass's independently-verified reality (the deployment doc's own honest gaps).
- **"Open first" is the correct and slightly counter-intuitive sequencing.** The strongest moat
  (verified semantic continuity + fair mechanism + machine-checked receipt) does not require FHE or
  FPGA; shipping one faithful end-to-end OPEN launch realizes it while the privacy/hardware frontier
  sharpens off the critical path. This aligns with the deployment reality (the biggest non-gated step is
  "stand up a persistent n≥2 federation and re-point the surfaces at it") and resists the temptation to
  gate the whole product on the un-measured Tier-0 crossing.
- **"Make the privacy statements literally true" is the right framing for the crypto residuals** — it
  bundles the three genuine over-claims (conditional reveal-nothing, DLog binding, threshold-not-no-viewer)
  into one closure program rather than treating them as separate footnotes. Consistent with the
  memory's "prove-the-floor-false" and "don't-launder-a-load-bearing-insecurity" feedback.
- **The competitive positioning is correct and disciplined** — "a proof-carrying mechanism layer with a
  swappable/dial-able privacy backend" is the defensible narrow lane vs Zama's shipped general FHE
  plumbing; it neither over-claims the eclipse nor concedes the moat.
- **Net Q4:** the triage table + the three moves + the positioning are a genuine outside-expert read
  that lands on the same reality this pass verified independently. **Flag hard:** the three moves as the
  actual near-term roadmap, in that order, with the conduct-bond vesting escrow folded into move 1.

---

## Overall honest read — did codex add genuine value?

**Yes — decisively, and it broadened cleanly to the whole system while staying adversarial.** Ranked:

1. **Q1 crossing reframe + threshold-trust correction — GOLD (the round's payoff).** "The crossing's
   nonlinearity is irreducible; paying for it inside TFHE is not" → output-boundary MPC dissolves the
   scheme-switch seam by exploiting the public-`p*` posture; the sign-vector-is-`p*`-determined leakage
   argument is clean; and "threshold FHE is not no-viewer against collusion" is a load-bearing honesty
   fix to the Tier-0 claim. A real answer to the designated crux + a required model correction.
2. **Q3 proof-carrying depth ladder + rolling exposure bond — GOLD (deepest, most actionable).** The
   depth ladder keeps the anti-ordering theorem alive *past graduation* on the already-verified kernel;
   the forbid-first vesting escrow + `α·S ≥ Ḡ+C` rolling bond + time-weighted pre-event restitution are
   genuine, correct mechanism design that upgrade the open conduct-bond weld.
3. **Q2 verified-core-boundary theorem — GOLD (corrects the docs).** Moving the crossing comparator OUT
   of the soundness TCB (it is untrusted search the STARK re-proves) and proving instead
   "accepted-output ⇒ Lean market transition for exactly these public inputs" (covering
   stale-context/cross-market mixing) is a sharper trust boundary than the docs' "small verified core."
4. **Q4 triage table + three moves — GOLD as a roadmap read.** Honest, scoped, and it lands on the same
   reality this pass verified; "Open first" is the correct sequencing.

**Adversarial corrections it forced (real value, thread back into the docs):**
- **Tier-0 "no viewer / nobody ever sees an order" is a POLICY claim, not a cryptographic guarantee**
  under threshold collusion — the highest-priority model fix. *(Corrects `DREGGFI-PRIVACY-TIERS.md` +
  the kernel framing.)*
- **The "~12–17 s crossing floor" is a CPU residual, not the modeled F2 latency** (~2.3–4.5 ms across
  F2); on F2 the un-measured scheme-switch/key-loading/PCIe/orchestration seams dominate — those are
  the real open number. *(Corrects the R4 brief + `FHEGG-FPGA-ACCELERATOR.md`.)*
- **The FPGA crossing comparator should NOT be in the soundness TCB** if the STARK re-proves it.
  *(Corrects `FHEGG-FPGA-ACCELERATOR.md` / `FHEGG-RTL-VERIFIED-HARDWARE.md`.)*
- **The current `StreamingCert` sums INDEPENDENT batch gaps** — state-coupled telescoping with
  inventory potentials is a genuine, un-proven next theorem. *(Sharpens the streaming-cert residual.)*
- **The N-leg ring AIR + constant-product pool now EXIST** — several "unbuilt" labels are stale.
- **No universal multiplicative package-approximation guarantee** follows from the natural LP (unbounded
  integrality gap); structure must be part of the `fhIR` type. *(Sharpens Q1.8/package.rs.)*

**Where it is disciplined rather than dazzling (honest):** Q2's engineering judgment (wrap-as-port,
appliance-not-company, p50/p99) and Q3's institutional-demands list are correct known-practice applied
well, not novelty; the crossing bake-off is a *measurement plan*, not a result (correctly — it insists
on measuring before RTL). Q4's persona objections are largely a well-organized restatement of residuals
this project already tracks — their value is the *triage* (killer-vs-sharpening, per-claim scoping), not
new facts. The genuine novelty concentrates in: output-boundary MPC for the crossing, the threshold-trust
correction, the two-sided solver proof market, the proof-carrying depth ladder, the rolling
exposure-indexed bond, and the accepted-output⇒Lean-transition hardware theorem.

**Verdict: GOLD, not mid.** Round 4 broadened to the whole system and hit all four areas with real,
correct, buildable content — the two designated highest-value targets landed hardest: a concrete
crossing architecture that *removes* the scheme-switch seam (output-boundary MPC, with a load-bearing
privacy-claim correction), and a launchpad mechanism suite (depth ladder + rolling bond + time-weighted
restitution + forbid-first vesting) that upgrades the open welds on the verified kernel. The immediate
build consequences: **(i)** correct the Tier-0 "no viewer" claim to an honest-threshold/secure-aggregation
posture and add it to `DREGGFI-PRIVACY-TIERS.md`; **(ii)** adopt the three-move roadmap — ship one
faithful OPEN launch receipt end-to-end first, run the crossing bake-off before FPGA RTL, and make the
privacy statements literally true; **(iii)** land the state-coupled `Φ_t`-potential telescoping theorem
and the `U ≤ αV(x)` package certificate; **(iv)** design the graduation-v2 proof-carrying depth ladder
and the forbid-first vesting escrow + rolling exposure bond.

---

*Provenance: full codex output `scratchpad/codex-round4.log`; curated final answer
`scratchpad/codex-round4-answer.md`; **309,587 tokens**; codex-cli 0.144.1 / GPT-5.6-sol; exit 0. Brief:
`docs/deos/FHEGG-CODEX-ROUND4-BRIEF.md`. HEAD deltas verified this pass: `metatheory/Market/StreamingCert.lean`
(independent-batch composition), `circuit-prove/src/shielded_ring_clearing_nleg_air.rs` (1129 lines),
`metatheory/Market/GraduationPool.lean` + `chain/contracts/launchpad/DreggSolventPool.sol`. Literature codex
cited (flag for a proof pass, not re-verified line-by-line here): CHIMERA (ePrint 2018/758); PEGASUS (ePrint
2020/1606); threshold FHE decryption security (ePrint 2024/116); BatchBoot (USENIX Security '26); Budish–
Cramton–Shim frequent-batch auctions; Ausubel–Cramton demand reduction + Ausubel clinching; Gul–Stacchetti
gross substitutes; Chekuri–Vondrák–Zenklusen pipage/swap rounding; Bansal et al. k-set-packing integrality
gap; Uniswap v3; Coconut (arXiv:1802.07344); World ID; ERC-7984 (EIP-7984); Zama HPU + KMS.*
