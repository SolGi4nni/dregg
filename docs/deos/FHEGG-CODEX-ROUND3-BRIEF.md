# fhEgg Round-3 Brief — the current frontier, for a mathematical analyst

*Self-contained aggregation of the fhEgg private-clearing research line, written to ground a
world-class cryptographer + optimization theorist on the CURRENT open frontier. Two prior codex
rounds already landed (round 1: the `Cert-F` duality certificate + the `ZKOpenRel_R` categorical
frame; round 2: the `fhIR` typed product language + `Price-Cert` derivatives). This brief states
what is now BUILT and VERIFIED, the NEW empirical facts that reshaped the frontier, and the FIVE new
open questions. Analysis, not code. Go deep; cite where known results apply; flag genuine novelty.*

---

## 0. The system in one screen

dregg is a proof-carrying state machine. A **turn** = "the exercise of an attenuable proof-carrying
token over owned state, leaving a receipt." **DrEX** is its private exchange. The **fhEgg kernel** is
the observation that a **batch uniform-price call auction is an AGGREGATION, not a matching**: limit
orders sum into a price-indexed cumulative demand/supply curve (a commutative-monoid fold of unary
step-increments), and clearing is a **single monotone crossing** `p* = min{p : D(p) ≥ S(p)}`. The
expensive "private matching" (oblivious sort, `O(N log²N)` bootstraps) evaporates into `O(N·K)`
additions + an `O(K)` crossing (K = price-bucket resolution, N = orders).

Generalized (the **Private Convex Engine**): many financial products are convex programs, and a
first-order/operator-splitting solver run `T` times is exactly the fhEgg shape iterated — each
iteration is `x ← prox(x − τ·A·x)`: a homomorphic-linear step with a **public** matrix A over
committed/encrypted data (the cheap primitive) + one small prox (a clamp/soft-threshold/projection =
one bounded nonlinearity). fhEgg is `T=1`. The optimizer's "oblivious first-order" (fixed
data-independent step schedule, Arjevani–Shamir) coincides exactly with the cryptographer's
obliviousness (fixed data-independent control flow).

**The killer move — verify, don't find.** A convex optimum is certified by a **primal-dual pair with
small duality gap**, and the gap is a **linear functional**. So the solver is an *untrusted search*
and the **duality gap is the cheap checked certificate** — translation validation for optimization.
The STARK never proves convergence; it proves "here is a primal-dual pair, its gap ≤ ε."

**Three product tiers on one verified kernel.** Tier 0 DARK (FHE, no viewer — nobody ever sees an
order); Tier 1 SHIELDED (STARK-ZK, private-from-the-world, one solver sees plaintext); Tier 2 OPEN
(public). The tier is a **type in `fhIR`** (the DSL): a product is well-typed at Tier 0 iff
FHE-tractable, Tier 1 iff STARK-tractable. Same soundness kernel (`exact_clears_iff`, `toBal_mul`,
`created_value_conservation`, `Cert-F`) at every tier; only privacy/generality/cost vary.

---

## 1. What is BUILT and VERIFIED (ground truth — do not reconstruct it)

### 1.1 Verified Lean (`metatheory/Market/*.lean`, kernel-clean, `#assert_axioms`-pinned)

**`CertF.lean` — the `Cert-F` duality certificate, PROVEN.** For the volume-max circulation LP
`max wᵀf s.t. Af = 0, 0 ≤ f ≤ c` (public incidence `A`, private amounts `f`):
- `structure FlowLP`, `PrimalFeasible f := Af = 0 ∧ 0 ≤ f ≤ c`,
  `DualFeasible π s := s ≥ 0 ∧ Aᵀπ + s ≥ w`, `Certified f π s := primal ∧ dual ∧ (cᵀs − wᵀf ≤ ε)`.
- `weak_duality`: every feasible/dual-feasible pair has `wᵀf ≤ cᵀs`.
- `certifies_epsilon_optimal` (KEYSTONE): `Certified f π s → f is ε-optimal`, **independent of how
  f, π, s were found**. `gap_nonneg`.
- Non-vacuity BOTH polarities: `ringCert_valid` (a worked 3-cycle circulation certificate over ℤ,
  gap exactly 0) + `ringF_optimal`; teeth `leakF_infeasible`, `zeroFlow_not_certifiable`,
  `zeroFlow_gap_refused` (an unsound triple is REFUSED).
- **Emittability**: `encodeCert`, `certCircuit : ConstraintSystem`, `certCircuit_sound`,
  `certCircuit_accepts_valid`, `certCircuit_rejects_gap` — the certificate check is realized as
  linear AIR `Constraint`s (`Dregg2.Circuit`), i.e. the cert is STARK-checkable in-AIR.

**`FhEggClearing.lean` — the fold + crossing, PROVEN.** `LimitOrder`, `demand/supply` as list-fold
histograms; `demand_perm`/`supply_perm` (order-independence / CRDT); `demand_antitone`,
`supply_monotone`, `imbalance_antitone` (monotone curves); `crossing := Nat.find` with
`crossing_clears`, `crossing_least`, `crossing_is_least`; the **codex round-1 correction** made real:
the crossing operator `Fstep bk K j := if Clears bk j then j else min (j+1) K` with `Fstep_monotone`
and `crossing_fixed` (the least fixed point of the *operator*, not of the curves). `clearedBatch`
with `clearedBatch_conserves`, `clearedBatch_uniform`, `clearedBatch_optimal`. Worked non-vacuity
(`workBook_crosses` at bucket 2, volume 6) + teeth (`noCrossBook_no_crossing`, `leakBatch_refused`).
Emittable `clearingCircuit`.

**`RevealNothing.lean` — `View ≈ Sim∘Q` over a leakage functor, PROVEN floor-conditional.** The
reveal-nothing theorem in the honest shape codex round-1 forced: a **leakage functor**
`Q : Clearing → Leakage` (batch size, price, total, root — the *deliberately public* facts);
`structure RevealBundle` carries `reveal_law : view c = sim (Q c)` as a FIELD (the PCS-ZK floor is a
bundle hypothesis, not asserted); `reveal_nothing`, `view_factors_through_leakage`,
`same_leakage_indistinguishable`. A PROVEN witness-free `canonicalSim`/`shellBundle`;
non-vacuity `alpha_neq_beta ∧ alpha_beta_same_leakage ⇒ shell_indistinguishable` (two DIFFERENT
clearings, same leakage, one transcript); teeth `leaky_no_simulator`, `leakyVB_not_hiding`. Bridged
to `Metatheory.Open.PerfectZK`.

**`ZKOpenRel.lean` — the categorical unification, PROVEN except ONE named open theorem.** The
category `ZKOpenRel R` of resource-graded open relations (lightweight decorated cospans): objects
carry private state; morphisms carry a resource `defect ∈ R` and a feasibility `rel`. The
resource-defect **functor** `d` to `(R,+,0)` (`dGrade_comp`, `dFunctor_tensor` — strong monoidal);
**conservation = the zero-defect subcategory `d⁻¹(0)`** (`comp_conservative`, `tensor_conservative`,
`iterate_conservative`). All **four objects recovered as instances**: circulation
(`circulation_conservative`, from `CertF.FlowLP`), convex engine, auction (`clearing_is_conservative`),
turn (`turn_history_conservative`). Privacy = `PrivacyNatTrans` (`View ≈ Sim∘Q`), with
`ofRevealBundle` showing the `RevealBundle` IS such a natural transformation.

**THE ONE OPEN THEOREM — `GuardedTraceClosure`.** The ring = the **guarded trace** (feedback gluing
an output boundary back to an input, imposing the loop `Af = 0`). `Guarded f := ∀ x, ∃ y, f.rel x y`
(the open system CLEARS — a witness exists, not merely a wired topology). PROVEN: the non-feedback
fragment — `comp_guarded` (adaptive/sequential composition preserves clearing), `tensor_guarded`
(parallel preserves clearing), and the **grade side of feedback** `gtrace_defect`,
`gtrace_conservative` (feedback changes no resource accounting). The `gtrace` is
`rel x y := ∃ u : U.S, f.rel (x,u) (y,u)`. STATED, NOT PROVEN (carried as an explicit hypothesis
field of `ZKUnification`, never `sorry`):

```
GuardedTraceClosure R :=
  ∀ (X Y U) (f : X⊗U ⟶ Y⊗U), Conservative f → Guarded f → Guarded (gtrace f)
```

*"A trace wires a cycle; it does NOT prove the cycle clears"* — tracing a relation can produce the
EMPTY relation. The feasibility/non-vacuity of the feedback fiber surviving feedback (and composing
adaptively) is the research target. **It is false for general relations without extra structure** — a
genuine guarded/particle-style trace, or the flow-network structure (`Af = 0` has a solution in the
box), is what should rescue it. THIS IS OPEN QUESTION 3.

### 1.2 Built solver (`fhegg-solver/`, 26/26 tests) and `fhIR-0` (`fhir/`)

- `fhegg-solver`: exact flow-LP + QP + **`Cert-F` extraction** + `air.rs` (Cert-F → AIR/STARK
  constraints) + `pdhg.rs` (the first-order finder) + `gpu.rs`. The verify-not-find engine, running.
- `fhir/`: the typed DSL — `ast.rs`, `tier.rs` (**tier-as-type**), `compile.rs`, `products.rs`,
  `solver_bridge.rs`. `fhIR-0` = LP + public-Hessian QP; boxes/orthants/affine/CVaR; histogram-auction
  / circulation / Snell-tree macros; lagged affine triggers; receipt-compiled brackets; certificates
  only. PSD/exp-cone deferred to `fhIR-1`.

### 1.3 PQ commitment posture (`PQ-SHIELDED-COMMITMENT.md`) — LANDED, with a named residual

The shielded pool's **privacy** (Pedersen perfect hiding + `HidingFriPcs` statistical-ZK) is already
PQ. Its **value-binding** was classical discrete-log (Pedersen/Ristretto binding + Schnorr excess +
Bulletproof range = Shor-broken). **Option A landed**: the authoritative value-commitment is now the
Poseidon2 hash `value_binding = hash_fact(value, [asset_type, randomness, 0])` (binding = `HashCR`,
hiding = the randomness blinder), conservation is the fully-in-AIR field gate
`Σ value_in = Σ value_out` (`Poseidon2ChipArithSound`), range is the in-AIR `VALUE_BITS` gadget. All
DLog retired from the shielded value-binding TCB.

**The named residual (this is the crux of OPEN QUESTION 1):** Option A subsumes the Pedersen
homomorphism *only because all legs are folded into one clearing AIR*. The ONE thing the homomorphism
bought — aggregating **independently-produced** commitments *before a common proof exists* — is a
**separate frontier item**: a PQ **lattice-additive** commitment (Option B, `Com(v;r) = Ar + Gv mod q`
over `R_q = ℤ_q[X]/(Xⁿ+1)`, binding = Module-SIS, additively homomorphic). Round-1 codex Q4 noted:
binding needs a real MSIS reduction (not a named generator); hiding is a *separate* MLWE/leftover-hash
argument; and the **aggregate** opening radius `‖Σr_i‖ = O(σ√N)` heuristic / `O(Nβ)` worst-case
governs MSIS parameters, not the per-order one. In-AIR verification of `Ar` is NOT free (NTT
`O(kℓn log n)` + range checks + foreign-field carries if `q ≠ p_AIR`; a commitment is `≈ k·n·⌈log₂ q⌉`
bits, ~2 KiB for `n=256,k=2,q≈2³¹`). Round-1 verdict: lattice-at-ingress, bridge once per batch,
hash/STARK for the rest.

---

## 2. THE NEW EMPIRICAL FACTS that reshaped the frontier (include in your reasoning)

### 2.1 The FHE no-viewer envelope was MEASURED — and the "aggregation is cheap" premise is REFUTED for exact-integer TFHE

The kernel doc's headline economy was "addition ≈ free (µs, no bootstrap); the bootstrap
(comparison/sort) is the only cost." **This is true for approximate-CKKS and for *raw* TFHE
ciphertext addition, but it is FALSE for the EXACT-INTEGER arithmetic a DEX conservation invariant
actually needs.** Measured reality:

- A DEX needs **exact integer** conservation (`Σ value_in = Σ value_out`, no rounding). On TFHE, exact
  multi-bit integer addition requires **carry propagation** across the radix limbs, and each carry
  resolution is a **programmable-bootstrap (PBS)-class** operation — NOT a free ciphertext add. So the
  `O(N·K)` "additions" of the fold, done in exact-integer TFHE, are **PBS-dominated**, and a full
  uniform-price clear lands in the regime of published encrypted sorts: **~22 s for 128 elements
  (CKKS, approximate), ~36 s for 64 (rank-sort), and MINUTES for exact-integer TFHE at N in the low
  hundreds** — with N in the thousands blowing past a minute cadence.
- The **crossing** (`O(K)` monotone threshold / comparisons over the aggregate) is comparatively
  fast and N-independent — the crossing was never the problem.
- **Consequence:** the "aggregation-cheap, cross-small" asymmetry that made Tier 0 look easy holds
  only if the *additive fold itself is genuinely cheap*. In exact-integer TFHE it is NOT (carry
  propagation is PBS-class). **The fold is the bottleneck, not the crossing** — the opposite of the
  original framing. This is the empirical fact that motivates Question 1.

### 2.2 The corrected Tier-0 direction — the lattice-additive fold is ONE object solving TWO problems

The fix and the PQ-commitment residual are **the same object**. A **lattice-additive** carrier
(RLWE/Module-SIS-additive, `Com(v;r) = Ar + Gv mod q` over `R_q`) has **native ring addition as its
homomorphism** — `Com(v₁;r₁) + Com(v₂;r₂) = Com(v₁+v₂; r₁+r₂)` is a single `mod q` vector addition
with **NO carry propagation, NO bootstrap** (the modulus wraps; the fold is free the way Pedersen was
free, but PQ). So the lattice-additive fold:
1. **fixes the Tier-0 FHE speed problem** — the `O(N·K)` fold becomes genuinely cheap additions again
   (native `R_q` add), instead of PBS-class TFHE carry-management; only the small `O(K)` crossing /
   one comparison needs the expensive PBS-class step (on TFHE, or a bespoke lattice comparison), and
2. **closes the PQ-commitment residual** — it is exactly the Option-B "aggregate independently-produced
   commitments before a common proof" primitive that Option A cannot provide.

**One object, two wins.** This is the highest-value target of round 3.

---

## 3. THE FIVE OPEN QUESTIONS (pose precisely; go deepest on Q1 and Q3)

### Q1 ⚑ THE SOUND QUANTIZED / LATTICE-ADDITIVE FOLD (the convergent Tier-0 unlock — highest value)

**The reframe (ember's insight — this is the crux).** Do NOT merely seek an additive-homomorphic PQ
scheme. Seek a **SOUND QUANTIZED APPROXIMATION** that loosens *exact-integer* arithmetic (whose slow
carry-propagation is the measured Tier-0 bottleneck, §2.1) to **cheap carry-free approximate
arithmetic** — and prove it safe. The architectural fit is exact: **`Cert-F` is ALREADY ε-approximate**
(first-order PDHG returns an ε-optimal pair; the duality-gap certificate literally carries ε in
`Certified f π s := ... ∧ cᵀs − wᵀf ≤ ε`). So the **quantization / approximation noise FOLDS INTO the
certificate's ε** — verify-not-find is *built* for approximate compute: it certifies the result is
within ε and sound *despite* approximate arithmetic. Cheap approximate adds recover Tier-0 speed; the
`Cert-F` ε absorbs the approximation; a Lean-proved conservative rounding guarantees no-mint.

Requirements, all simultaneously: additions **CHEAP** (native `R_q` / CKKS-slot addition, no carry
propagation, no bootstrap) so the `O(N·K)` fold + the `T` PDHG iterations are genuinely cheap; the
**crossing / comparison** a *small* `O(K)`, N-independent residue; the whole thing **VERIFIABLE in a
hash-STARK** with binding checkable **in-AIR** alongside `Cert-F`. Answer these three precisely:

**(a) The concrete scheme.** **CKKS** (approximate fixed-point, SIMD-packed, carry-free cheap adds,
rescaling) vs a **QUANTIZED lattice-additive** commitment (RLWE / Module-SIS / BDLOP `Ar + Gv mod q`
with bounded quantization) — for the fold AND the `T` PDHG iterations AND the one crossing/comparison.
Which gives cheap adds + PQ + STARK-verifiability? State the concrete **noise / precision budget** for:
the depth-1-additive fold over N orders; `T` PDHG iterations (each `x ← clip(x − τ(w − Aᵀy))`, i.e.
additive matvec + one prox — how does approximate arithmetic interact with the prox and with the
`O(1/T)` gap rate?); and one comparison. For the lattice route, the aggregate opening radius `‖Σr_i‖`
(`O(σ√N)` heuristic / `O(Nβ)` worst-case) and the MSIS/MLWE parameters it forces; how to keep `q`
small enough that in-AIR `Ar` verification does not swamp the STARK (native `q = p_AIR`? RNS/CRT? a
per-batch bridge opening the lattice commitment to a Poseidon-committed aggregate?). Is there a scheme
where the comparison is **lattice-native** (no TFHE hop)?

**(b) The ε-ABSORPTION (error composition into ONE certified ε).** Give the **error-propagation bound**
by which the **quantization error + the CKKS approximation/rescale noise + the first-order duality gap
ALL compose into ONE certified ε** — the `Cert-F` duality gap the STARK checks. I.e. if the true LP
optimum is `OPT`, and the approximate solver returns `(f̃, π̃, s̃)` computed under approximate arithmetic
with per-op error δ over `T` iterations, bound the *certified* gap `cᵀs̃ − wᵀf̃` and show it is a valid
(possibly inflated) ε for which `certifies_epsilon_optimal` still holds. What is the honest ε as a
function of `(δ_quant, δ_ckks, T, condition number, ‖A‖)`? Does the approximate feasibility (`Af̃ ≈ 0`)
need a slack, and how does that slack enter the certificate?

**(c) ⚑ MINT-SAFETY (the load-bearing soundness, Lean-provable — the point of the whole exercise).**
Approximate conservation "`Σ ≈ 0`" must **NOT** admit a mint (value-creation within the tolerance):
`ε`-optimality is fine to be approximate, but **conservation must be exact-or-provably-mint-safe**. The
clean separation ember wants: **optimality approximate (bounded ε), conservation MINT-SAFE (a proven
rounding bound)**. Give the **concrete mint-safe quantized-conservation rule** — a **CONSERVATIVE
rounding** (round toward no-mint: floor outputs / ceil inputs, or a signed-slack discipline) such that
the *rounded* conservation constraint provably implies **`Σ value_out ≤ Σ value_in`** (no value
created) even though the *un*rounded arithmetic was approximate. State its **error bound** and the
exact **lemma we will prove in Lean** — `CertF.lean` already has `certifies_epsilon_optimal` (the
ε-optimality); we ADD `mint_safe_quantization` (the conservative-rounding no-mint bound). This is the
separation that lets Lean make us trust a complicated approximate construction: the STARK checks a
mint-safe rounded conservation gate (exact field constraint, no-wrap) while the optimality rides the
ε-certificate. **What is the conservative-rounding rule, its bound, and the precise Lean lemma
statement?**

Concrete construction wanted throughout. This is where Tier 0 becomes fast AND post-quantum AND
provably mint-safe — the reframed crux and the highest-value target of round 3.

### Q2 — THE CLEARING-MECHANISM FAMILY (beyond uniform-price)

Which clearing mechanisms are **`Cert-F`-certifiable** (convex + a duality/KKT certificate whose gap
is a small linear/quadratic functional, verify-not-find)? Map the family and its boundary:
welfare-max / Fisher-market (Eisenberg–Gale `max Σ bᵢ log⟨uᵢ,xᵢ⟩`); discriminatory-price;
CFMM-routing (Angeris convex); frequent-batch with concave utilities; combinatorial (the LP-relaxation
vs the NP-hard exact-subset boundary — recall exact all-or-nothing *selection* is
`max Σwᵢxᵢ s.t. Σxᵢaᵢ=0, xᵢ∈{0,1}` = subset-sum, NP-hard). For each: the exact certificate object, the
prox, and the cheap/hard boundary. **Any NOVEL mechanism the verify-not-find + tiered structure
uniquely enables** — dynamic/streaming clearing (a certificate that composes across batches)?
cross-tier clearing (part of the book Tier-0-dark, part Tier-1-shielded, one joint certificate)? a
mechanism *designed* for the cheap lattice-additive regime (where adds are free but comparisons are
metered)?

### Q3 — THE CATEGORICAL CLOSURE THEOREM (the `GuardedTraceClosure` conjecture)

PROVE or sketch, or identify the precise obstruction to:
```
GuardedTraceClosure R :=
  ∀ (X Y U) (f : X⊗U ⟶ Y⊗U), Conservative f → Guarded f → Guarded (gtrace f)
    where  gtrace f . rel x y := ∃ u, f.rel (x,u) (y,u)
```
The grade side is proven (feedback mints/burns nothing). The open content is the **feedback-feasibility
closure**: *feedback/guarded-trace preserves feasibility-clearing, not just the resource grade*. It is
FALSE for general relations (a trace can yield the empty relation — "wires a cycle, does not prove it
clears"). What extra structure makes it TRUE for the fhEgg setting? Candidates to evaluate: (i) the
flow-network structure — `Af = 0` in a box always has a solution (a circulation exists), giving a
non-vacuity witness the abstract relation lacks; (ii) a fixed-point / Tarski argument on a monotone
feedback map; (iii) a compact-closed vs merely-traced distinction; (iv) restricting to
*single-valued*/functional feedback fibers. Is `GuardedTraceClosure` provable under a Conservative +
box-feasible + monotone hypothesis? State the theorem you CAN prove and the exact obstruction to the
fully general one. (Bonus: adaptive/sequential composition of traced morphisms — does the closure
compose?)

### Q4 — PRICE-CERT DERIVATIVES (the one state-price LP + superhedging dual)

Round 2 proposed `Price-Cert`: over a public scenario grid Ω, no-arbitrage price
`p̄ = max_{π≥0} hᵀπ s.t. Hᵀπ = a`, superhedging dual `p̄ = min_y aᵀy s.t. Hy ≥ h`, certificate
`π≥0, Hᵀπ=a, Hy≥h, 0 ≤ aᵀy − hᵀπ ≤ ε`. Deepen the concrete constructions: **European via state-price
LP; American/Bermudan via Snell-envelope LP** (the occupation/stopping-flow dual — verify it is
exactly the Haugh–Kogan/Rogers martingale dual); barrier/autocall via finite-state expansion. **Any
NOVEL derivative the private-fair-mark enables** — a product whose *economic value is the
concealment* (dark cross-margin was round-2's; what else)? A derivative on the *certificate itself*
(e.g. trading the arbitrage-free interval width)? The precise expressiveness cliff (where does the
state-price LP stop being cheap — closed-form Black–Scholes normal-CDF, fractional power perps, LMSR
exp-cone)?

### Q5 — EFFICIENCY / NOVEL CONSTRUCTIONS (the homomorphic-native gigabrain openings)

The genuinely-clever openings for world-class private clearing that the above four don't cover.
Boundary-histogram `O(NK)→O(N+K)` (round 1); dyadic/`O(√K)` crossing; direct-sum batching of
independent markets; receipt-compiled integer-order linkage (round 2). What's LEFT? Homomorphic-native
tricks specific to the lattice-additive regime (packing the whole K-bucket curve into one RLWE
ciphertext and doing the prefix-scan by Galois rotations; a comparison that is itself a lattice
operation; SIMD across markets)? A construction where the STARK proof and the lattice fold share
work? Go where the deepest efficiency wins hide.

---

*You are a world-class cryptographer + optimization theorist. Deepest NOVEL analysis + concrete
constructions on the five questions — ESPECIALLY (1) the lattice-additive fold and (3) the closure
theorem. Rigorous; cite where known results apply; flag genuine novelty vs known-applied. Analysis,
not code — go deep.*
