# The fhEgg Kernel — the computational kernel of private market clearing

*The foundational kernel doc for the fhEgg line. It states the core model precisely, grounds
each claim in the machine-checked Lean and the Rust that realizes it, and grades every edge:
what is **proven** (kernel-clean, at model/spec scope), what is **floor-conditional** (proven
modulo a named hypothesis), what is **measured** (a real performance envelope), and what is a
**named residual** (a build not yet done). Companions: `PRIVATE-CONVEX-ENGINE.md` (the convex
engine), `DREGGFI-PRIVACY-TIERS.md` (the three postures), `FHEGG-PRODUCT-ORDER-FRONTIER.md`
(the `fhIR` typed product DSL). What-is, present tense; no trajectory narrative.*

---

## 0. The kernel in one paragraph

A clearing is an **aggregation-monoid fold**, and trust in it is **verify-not-find**. Orders
sum into a price-indexed aggregate curve — a commutative-monoid fold of per-order increments,
order-independent and computable without decryption. Clearing reads a result off that
aggregate (a monotone crossing, for the uniform-price base case; a convex optimum, in
general). The result is **not** trusted because a solver produced it: an untrusted solver
*proposes* a candidate, and a small **certificate** — a set of linear feasibility rows plus a
duality gap — *disposes* it, proving the candidate is (ε-)optimal independent of how it was
found. The certificate is the object the proof carries; the solver is out of the trusted base.
This is the exact structural twin of the turn-kernel ("a turn is the exercise of an attenuable
proof-carrying token over owned state, leaving a receipt"): a clearing is an associative,
commutative, homomorphic fold of order-increments, resolved once, leaving a proof-carrying mark.

---

## 1. The two moves: the fold, and verify-not-find

### 1.1 The object and the fold

Fix a public price grid `P = {p₁ < … < p_K}` (`K` the chosen resolution). The market state is a
price-indexed vector of aggregates `D, S : P → 𝔸` (cumulative demand, cumulative supply) valued
in a commutative monoid `𝔸` that is additively homomorphic under commitment/encryption
(Pedersen `ValueCommitment`, a lattice-additive ciphertext, or plaintext). A limit order
`(side, qty, limit)` is **one curve increment**: a bid adds its `qty` to every bucket at or
below its limit, an ask to every bucket at or above. Aggregation is the bucketwise fold
`D = ⊕ bids`, `S = ⊕ asks`.

This is formalized directly in `metatheory/Market/FhEggClearing.lean`:

- `demand`/`supply` are the folds; `demand_cons`/`supply_cons` are the **fold homomorphism**
  (the histogram-grain analogue of `Market/Clearing.lean`'s `toBal_mul`);
- `demand_perm`/`supply_perm` prove **order-independence** (the fold is commutative — a CRDT;
  the `pool_as_perm` analogue) — no consensus on arrival order is needed to compute the total;
- `demand_antitone`/`supply_monotone`/`imbalance_antitone` prove the aggregate curves are
  monotone, so the excess-demand `imbalance = demand − supply` is non-increasing in price.

### 1.2 The uniform-price crossing (a fixpoint on a chain)

The uniform clearing price is the crossing `p* = min{ p : demand(p) ≤ supply(p) }`. Because the
curves are monotone this is a threshold search over `K` buckets — the least fixed point of the
explicit index update `F(j) = j if demand(j) ≤ supply(j) else min(j+1, K)`.

The load-bearing correction (codex Q2, `FHEGG-CODEX-INSIGHTS.md`): monotone *curves* are not a
monotone *operator*; the fixpoint is of `F`, not of `D, S`. `Fstep_monotone` proves **`F` is the
monotone operator** (using `imbalance_antitone`: the clearing guard is upward-closed), so
Knaster–Tarski applies. `crossing_is_least` proves `crossing` is the least clearing bucket and
`crossing_fixed` that it is a fixed point of `F` — **assuming a crossing exists**. That
hypothesis (`CrossingExists`) is stated honestly and is not free: a book whose demand exceeds
supply at every bucket does not clear (`noCrossBook_no_crossing`), and there is then only the
spurious top bucket, not a genuine fixpoint.

At the crossing the matched volume is `demand(p*)` (`clearedVolume_eq_demand`). The aggregate
cleared batch neither mints nor burns — `netFlow = 0` on every asset (`clearedBatch_conserves`,
the priced lift of `clearing_conserves_per_asset`) — and is uniform-price optimal
(`clearedBatch_optimal`, discharged through `Market/Optimality.lean`'s `uniform_price_optimal`:
no-arbitrage / value-neutral / individually rational). **Scope, stated plainly:** this is
model-level optimality over the `Fill` substrate; binding the histogram fold to the on-chain
fills in-circuit (**ledger-realization**) is a named circuit step, not proved here.

### 1.3 Verify-not-find: the certificate disposes

The kernel does not prove a solver converged. For the canonical general program — the
volume-max circulation LP `max wᵀf s.t. A f = 0, 0 ≤ f ≤ c` (`A` the **public incidence
matrix** of the trade graph; `w, c, f` the private amounts) — a primal-dual triple `(f, π, s)`
satisfying the linear certificate

```
   A f = 0,   0 ≤ f ≤ c,   s ≥ 0,   Aᵀπ + s ≥ w,   cᵀs − wᵀf ≤ ε
```

certifies that `f` is ε-optimal, **independent of how `(f, π, s)` was found**. This is `Cert-F`,
proven in `metatheory/Market/CertF.lean`:

- `weak_duality` — for every primal-feasible `f` and dual-feasible `(π, s)`, `wᵀf ≤ cᵀs`, using
  nothing about how either arose;
- `certifies_epsilon_optimal` (**the keystone**) — a certificate with gap `≤ ε` forces every
  primal-feasible `f'` to satisfy `wᵀf' ≤ wᵀf + ε`: no feasible flow beats the certified one by
  more than `ε`, and the proof reads only the certificate;
- `gap_nonneg` — a certified gap is `≥ 0`, so a "certificate" claiming a negative gap is vacuous.

The theorem is general (any ordered commutative ring), instantiated at `ℤ` on a worked 3-cycle
with teeth (`leakF_infeasible`, `zeroFlow_not_certifiable`, `zeroFlow_gap_refused`: an
unsound or non-optimal triple is refused). The check emits as linear circuit `Constraint`s of
size `O(m + nnz A)` — **not** `O(T·m)` (proving the `T` solver iterations) — with `certCircuit_sound`
the emit bridge. `circuit-prove/src/cert_f_air.rs` (`prove_cert_f`) carries those rows into a
real production STARK (`EffectVmDescriptor2`, BabyBear + FRI): the private `(f, π, s)` live only
in the trace under the hiding PCS, and the only public value exposed is the cleared volume `wᵀf`.

The solver that produces `(f, π, s)` is an **untrusted search** and out of the trusted base.
`fhegg-solver/` is that search: `pdhg.rs` is a fixed-`T`, topology-only-preconditioned PDHG for
the circulation LP; `clearing.rs` is the uniform-price fold-and-cross (the `T=1` base case). Each
emits a certificate a verified checker validates.

---

## 2. The mechanism family

Uniform-price is the **floor**, not the only clearing. Because the engine is verify-not-find —
an untrusted convex solve plus a checked certificate — **any convex program with a duality/KKT
certificate is a member**. The engine is defined by the certificate, not by a fixed rule. The
family carried in `fhegg-solver/` and formalized in `metatheory/Market/`:

| Mechanism | Program | Certificate (proven soundness) |
|---|---|---|
| Uniform-price call auction | fold + one crossing (`T=1`) | Σ-balance / crossing (`FhEggClearing.lean`, `clearedBatch_conserves`) |
| Volume-max circulation | `max wᵀf s.t. Af=0, 0≤f≤c` | `Cert-F` — `certifies_epsilon_optimal` (`CertF.lean`) |
| Convex QP (portfolio, execution) | `min ½xᵀPx+qᵀx s.t. Ax=b, l≤x≤u`, `P⪰0` public | `CertQp` — KKT/complementarity gap, `qp_certifies_epsilon_optimal` (`CertQp.lean`) |
| Derivatives family | state-price LP + superhedging dual | `Price-Cert` — `price_cert_certifies`; American = Snell-envelope LP, `snell_feasible_upper_bound` (`PriceCert.lean`) |
| Discriminatory (pay-as-bid), CFMM routing, Fisher/welfare-max | flow-LP / convex over public curve / Eisenberg–Gale | reuse `Cert-F` / mirror-descent prox (`fhegg-solver/{discriminatory,cfmm,fisher}.rs`) |

Each certificate has the same shape and the same honest scope: **verifying** a candidate is the
cheap, proven part; **selecting** the optimum is the untrusted solver's job. `CertQp` names its
edge case precisely (the keystone needs exact stationarity; the inexact-dual-residual case
`qp.rs` also accepts contributes an `ε_stat·diam(box)` term, not proved). `Price-Cert` names its
residuals (continuous/path-dependent payoffs are state-size hard, not solver-hard; general
finite-DAG Snell assembly).

**The integer boundary (named honestly).** For a *given* exact all-or-nothing book, verifying
that it clears is a **free homomorphic conservation check** (`exact_clears_iff`: clearability is
Σ-balance; `shielded_ring_clears`: a given ring clears over shielded notes, decrypting nothing).
But **selecting** the max-volume exact subset is `max Σwᵢxᵢ s.t. Σxᵢaᵢ=0, xᵢ∈{0,1}`, a 0-1
balancing problem that encodes subset-sum / set-packing and is **NP-hard**. A public topology
does *not* remove the integrality (codex Q3). So the tractable engine is deliberately the `[0,1]`
partial-fill **relaxation** — a poly-time flow-LP certified by `Cert-F` — not exact-subset
optimization. The two must not be conflated: verifying an exact-intent ring folds into the kernel
(proven); optimal exact-subset selection is integer-hard; the tractable optimizer is the
partial-fill oblivious flow-LP.

**The cheap-regime boundary is "matrices public," not "convex."** The operative efficiency line
is that the constraint matrix `A` (incidence/topology, tick grid, CFMM curve) is a **public
constant**, so the matvec is a linear combination of ciphertexts with public scalars — the
bootstrap-free primitive. The private data are the amounts. A program with a *private* matrix
(e.g. a private covariance) falls off the cheap public-matvec line regardless of convexity
(`PRIVATE-CONVEX-ENGINE.md` precision-correction #4; `fhir/src/lib.rs`). Work on the incidence
`A` directly, not a dense cycle basis: `A` is sparse and well-conditioned, a fundamental cycle
basis can be dense and ill-conditioned and enlarges the solver's fixed-point/modulus bounds
(codex Q3).

---

## 3. Three privacy postures over one kernel

The same verified kernel runs at three privacy postures (`DREGGFI-PRIVACY-TIERS.md`). The
soundness guarantee — fair, conserving, no-mint, certificate-carrying — is identical at every
posture; only the privacy carrier, mechanism-generality, and cost move.

- **Dark (no viewer).** The clearing runs entirely on ciphertexts; a threshold committee holds
  decryption-key shares and decrypts only the public result. No solver, relayer, enclave, or
  committee ever holds a plaintext order. FHE is lattice/LWE, hence post-quantum by construction.
  Privacy is unconditional on committee honesty; correctness is not (a committee can force a
  *wrong* result — an integrity fault the correctness proof catches — but still cannot *see* an
  order), and the two are stated separately.
- **Shielded (private-from-the-world).** The solver/prover sees plaintext; the public transcript
  reveals nothing else. Value, owner, key, path, offer/want, and allocation live only in the
  STARK witness under the hiding PCS (Poseidon2/FRI), and only `[nullifier, merkle_root,
  value_binding]` per leg plus the price is exposed. Fast (GPU), PQ hash-commitment. This is what
  `cert_f_air.rs` realizes.
- **Open (public).** The book is public; the clearing is a STARK of correctness over it. Widest
  generality (the full matcher), cheapest.

`fhIR` (`fhir/`) makes the posture a **type**: a product type-checks at the most private tier its
compiled form can honestly run at, and the compiler refuses to promise more. The soundness
direction — *compiles ⇒ admissible* — is proven (`FhIRAdmissible.lean`: `passes_runnable`,
`compiles_admissible`, monotonicity `Dark ⇒ Shielded ⇒ Open`); the full iff (with completeness /
resource-relative maximality) is a named research target, with a concrete counterexample
witnessing why the `⟹` is open.

### 3.1 The honest measured FHE reality (Dark)

The Dark posture is correct but bounded by a real, measured envelope
(`DREX-NO-VIEWER-SURPASS.md`), and the honest numbers matter:

- Uniform-price FHE clearing is tractable at **N ≈ 32–512 orders per pair at minute cadence** on
  one server today (published FHE sorts land 128 elements in ~22 s CKKS, 64 in ~36 s rank-sort);
  it **breaks** at N in the thousands (tens of minutes → hours).
- **Exact-integer TFHE is slower than approximate CKKS**, because exact-integer radix addition
  **carry-propagates** — the aggregation fold is not free at exact precision. A DEX needs exact
  conservation, which argues for exact TFHE with a range/precision discipline (paying the higher
  constant) rather than treating ciphertext addition as costless. The crossing itself is `O(K)`
  and cheap; the fold is where the exact-integer bill lands.
- **The sound-quantized / additive fold is the speed direction**, and it is mint-safe by
  construction (§3.2). This keeps the aggregation in the cheap additive layer without charging
  soundness to the approximation.

### 3.2 Mint-safe quantization: approximation proposes, exactification disposes

The tempting shortcut — charge approximate feasibility to `ε` and reuse
`certifies_epsilon_optimal` — is **unsound**, and `MintSafeQuantization.lean` corrects it (codex
Round-3 Q1). The deployed `Certified` predicate demands **exact** primal and dual feasibility;
quantization / FHE / iteration noise cannot be absorbed into `ε`. The sound discipline:

1. run the cheap **approximate** encrypted solver as an untrusted search;
2. **exactify** the candidate onto the integer grid → an exactly-feasible `(f, π, s)`;
3. recompute the **exact** gap `G_q = cᵀs − wᵀf` and feed it verbatim to the keystone — the
   certified target is literally `ε_cert = G_q` (`exactified_certified`, `exact_gap_feeds_keystone`).

Quantization governs **completeness** (does an honest clearing pass; how large is `G_q`) and
**parameter sizing** — never **soundness**; the keystone only ever sees the exact recomputed gap.
The no-mint gate is a cheap integer check made sound by **directional rounding**: over-approximate
outputs, under-approximate inputs. `mint_safe_quantization` proves the integer gate
`Σ qout ≤ Σ qin` then forbids a mint of the true rational values (`Σ vout ≤ Σ vin`), and the
directionality is discharged as a theorem for the concrete floor/ceil quantizer
(`mint_safe_floor_ceil`: floor the inputs, ceil the outputs), not left as a hypothesis. Teeth:
`wrong_direction_admits_mint` (flip a rounding and the gate launders a mint),
`genuine_mint_fails_gate` (a real mint with correct rounding provably fails the gate). The no-wrap
refinement `field_gate_refines_nat_eq` closes the modular-mint gap: a field equality without range
bounds admits a discrepancy of `p` (`field_gate_without_range_mints`); with the `VALUE_BITS`
range discipline the field equation is the integer equation. `sufficient_surplus_passes_gate`
bounds the completeness tolerance — the only clearings the quantizer can reject are within
`Δ·(n_in+n_out)` of breaking even, tunable by the step `Δ`.

---

## 4. Reveal-nothing and the categorical frame

### 4.1 Reveal-nothing — `View ≈ Sim∘Q`, floor-conditional

The Shielded transcript is **not** independent of the trades — it reveals the batch cleared, the
price, and the conserved totals. The honest statement is a **simulator over a leakage functor**
(`RevealNothing.lean`, codex Q2): there is a witness-free `Sim` with `View(clearing) = Sim(Q(clearing))`,
where `Q` is the public leakage (price, batch size, conserved total, committed root) and
explicitly *not* the per-leg owner / value / offer / want / allocation. So an observer learns
only the leakage class `Q`.

What is **proven** (kernel-clean): the `View = Sim∘Q` theorem and its consequence
`same_leakage_indistinguishable` (two clearings with the same leakage but genuinely different
trades produce the identical transcript — witnessed non-vacuously on `c_alpha ≠ c_beta`); the
teeth `leaky_no_simulator` (a transcript leaking a private value admits no simulator — the law is
falsifiable, not vacuous); perfect value-binding hiding `HidingValueBinding` with a Pedersen
witness (`addHVB`) and teeth (`leakyVB_not_hiding`); the `Q`-faithful simulator shell
`canonicalSim`; and the bridge onto the repo's `PerfectZK` machinery.

What is the **named floor**: the deployed bundle's `reveal_law` — the `HidingFriPcs`
statistical-ZK + hash-hiding + nullifier-unlinkability obligation (the PCS simulator) — is an
explicit bundle field, not yet a Lean theorem and not a `sorry`. Every reveal-nothing consequence
is *conditional on that field*, the same shape the linking tower's forgery bound is conditional on
`HashCR`. The ideal `shellBundle` satisfies it by construction; the deployed bundle satisfies it
only under the floor. **Honest grade: reveal-nothing at the clearing level is proved *conditional
on the PCS-ZK floor*, not unconditionally.**

### 4.2 The categorical frame — conservation = `d⁻¹(0)`, and the refuted-then-repaired closure

`ZKOpenRel.lean` gives the categorical home (codex Q2): a resource-graded category of open
relations, with a strong-monoidal **resource-defect functor** `d` to `(R,+,0)`, and **conservation
= the zero-defect subcategory `d⁻¹(0)`**. Proven: the category laws, the functor laws
(`dFunctor_tensor`, `dFunctor_unit`), that `d⁻¹(0)` is closed under composition and tensor
(`comp_conservative`, `tensor_conservative`), and that the four objects (turn / auction /
circulation / convex-engine) recover as instances living in `d⁻¹(0)`.

The **feedback closure** is the honest part. The tempting full-generality conjecture — that the
guarded trace of a conservative guarded morphism is guarded — is **false**, and
`guardedTraceClosure_refuted` proves it with a `Bool`-negation counterexample (conservative,
guarded, functional, yet its trace is the empty relation). It is **replaced** with the true
**Tarski feedback closure** `traceAdmissible_guarded`: when the feedback is a monotone self-map of
a complete lattice, its least fixed point witnesses that the loop clears. This lands on exactly the
proven monotone crossing operator (`crossing_gtrace_guarded` via `Fstep_monotone` / `crossing_fixed`),
fires non-vacuously on a real non-total monotone feedback, and the four instances are discharged as
`TraceAdmissible`. Privacy is the simulator natural transformation `PrivacyNatTrans`
(`View ≈ Sim∘Q`), with `RevealNothing.RevealBundle` shown to be exactly such a transformation.
**Grade:** the objects, functor, conservation-as-kernel, four instances, non-feedback composition,
and privacy transformation are proven unconditionally; the feedback closure is a proven refutation
of the false conjecture plus a proven replacement for the monotone/finite cases — the unification
holds for the admissible instances, not for the false full generality.

---

## 5. The verified substrate — what maps to what

The kernel is the name of a decomposition the repo has largely proved. All Lean below is
kernel-clean (`#assert_all_clean` / `#assert_axioms`) at model/spec scope.

| Kernel component | Lean / code | Status |
|---|---|---|
| aggregate curve, fold homomorphism, order-independence | `FhEggClearing.lean` (`demand_cons`, `demand_perm`); `Clearing.lean` (`toBal_mul`); `Aggregation.lean` (`pool_as_perm`, `aggregate_sound`) | proven |
| the monotone crossing operator (curves ≠ operator) | `FhEggClearing.lean` (`Fstep_monotone`, `crossing_is_least`, `crossing_fixed`) | proven; `CrossingExists` an honest hypothesis |
| conservation + uniform-price optimality of the cleared batch | `FhEggClearing.lean` (`clearedBatch_conserves`, `clearedBatch_optimal`); `Optimality.lean` (`uniform_price_optimal`) | proven at model scope; ledger-realization named |
| verify-not-find certificate (`Cert-F`) | `CertF.lean` (`weak_duality`, `certifies_epsilon_optimal`, `gap_nonneg`); `cert_f_air.rs` (`prove_cert_f`) | proven; STARK-realized |
| convex-QP / derivatives certificates | `CertQp.lean` (`qp_certifies_epsilon_optimal`); `PriceCert.lean` (`price_cert_certifies`, `snell_feasible_upper_bound`) | proven; named edge cases |
| mint-safe sound quantization (exactify-then-check) | `MintSafeQuantization.lean` (`mint_safe_floor_ceil`, `field_gate_refines_nat_eq`, `exact_gap_feeds_keystone`) | proven |
| exact-ring conservation over commitments (decrypt nothing) | `Clearing.lean` (`exact_clears_iff`); `ShieldedClearing.lean` (`shielded_ring_clears`); `Dregg2/Exec/ShieldedValue.lean` (`created_value_conservation`) | proven |
| reveal-nothing (`View ≈ Sim∘Q`) | `RevealNothing.lean` (`reveal_nothing`, `same_leakage_indistinguishable`, `leaky_no_simulator`) | proven **conditional** on the PCS-ZK floor |
| categorical unification (`d⁻¹(0)`, Tarski feedback closure) | `ZKOpenRel.lean` (`comp_conservative`, `guardedTraceClosure_refuted`, `traceAdmissible_guarded`) | proven for admissible instances; false conjecture refuted |
| the tier-as-type direction | `FhIRAdmissible.lean` (`compiles_admissible`); `fhir/` | `⟸` proven; full iff a named target |
| untrusted solver family + STARK apex | `fhegg-solver/` (`clearing.rs`, `pdhg.rs`, `qp.rs`, `pricecert.rs`, …); `circuit-prove/src/{accumulator,joint_turn_aggregation}.rs` | untrusted-by-design; checked by the certificate |

---

## 6. Honest feasibility envelope + named residuals

| Regime | Status | Basis |
|---|---|---|
| Uniform-price call auction (`T=1`), single pair | proven at model scope; fold + one crossing | `FhEggClearing.lean` |
| Verify a given exact-intent ring | proven; free homomorphic conservation check | `exact_clears_iff`, `shielded_ring_clears` |
| `Cert-F` / `CertQp` / `Price-Cert` optimality certificate | proven; verify-not-find keystone | `CertF.lean`, `CertQp.lean`, `PriceCert.lean` |
| Select the optimal exact all-or-nothing subset | **NP-hard** (0-1 balancing = subset-sum); use the `[0,1]` relaxation | codex Q3 |
| Partial-fill volume-max at scale, oblivious | poly-time flow-LP; scale is the frontier (worst-case padding is the tax) | `pdhg.rs` |
| Dark FHE clearing | **measured**: tractable N ≈ 32–512/pair at minute cadence; breaks at thousands; exact-integer TFHE > approximate CKKS | `DREX-NO-VIEWER-SURPASS.md` |
| Reveal-nothing at the clearing level | proven **conditional** on the `HidingFriPcs` statistical-ZK floor | `RevealNothing.lean` |
| Ledger-realization of the histogram fold in-circuit | named circuit build | `FhEggClearing.lean §2.4`-analogue |
| Post-quantum aggregate/binding layer | `Cert-F` STARK is PQ; the classical-DLog Pedersen commitment binding is the named cutover | `PQ-SHIELDED-COMMITMENT.md` |

The core does not move: a private clearing is an associative, commutative, homomorphic fold of
order-increments, resolved by a result whose optimality a **linear certificate** proves —
verify-not-find — provable by a STARK over the certificate, revealing only the market fact. The
solver is untrusted; the certificate is the trusted object; and the same fold-and-certify shape,
run once (uniform-price) or `T` times (the convex engine), is the whole of it.

---

## 7. See also

- `docs/deos/PRIVATE-CONVEX-ENGINE.md` — the oblivious first-order convex engine (the `Cert-F` factory).
- `docs/deos/DREGGFI-PRIVACY-TIERS.md` — the Dark / Shielded / Open postures over the one kernel.
- `docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md` — `fhIR`, the admissibility theorem, `Price-Cert`.
- `docs/deos/DREX-NO-VIEWER-SURPASS.md` — the measured FHE envelope for the Dark posture.
- `docs/deos/FHEGG-CODEX-INSIGHTS.md`, `FHEGG-CODEX-ROUND3.md` — the framing corrections cited above.
- `metatheory/Market/{FhEggClearing,CertF,CertQp,PriceCert,MintSafeQuantization,RevealNothing,ZKOpenRel,FhIRAdmissible}.lean` — the proven core.
- `fhegg-solver/`, `fhir/`, `circuit-prove/src/cert_f_air.rs` — the untrusted solver family, the typed DSL, and the STARK realization.
