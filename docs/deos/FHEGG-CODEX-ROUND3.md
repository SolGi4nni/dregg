# fhEgg — Codex Round 3: the Sound-Quantized Tier-0 Frontier, Captured + Assessed

*Third `brief → codex → capture+assess` round (the pattern that landed Cert-F/`ZKOpenRel_R` in R1 and
`fhIR`/`Price-Cert` in R2). This doc holds the self-contained brief (§A) and codex's captured analysis
organized by the five open questions, each with an HONEST gold-vs-mid assessment (§B) — curated, not
pasted. The two crux items (Q1 the sound-quantized/lattice-additive fold + its Lean mint-safety lemma;
Q3 the `GuardedTraceClosure` feedback theorem) are assessed HARDEST against the real `CertF.lean` /
`ZKOpenRel.lean` / `FhEggClearing.lean` structure. What-is, present tense; every edge names its grade.*

**The run (real, cited).** `codex exec --skip-git-repo-check --sandbox read-only` on the R3 brief +
analyst ask; codex-cli **0.144.1 / GPT-5.6-sol**; exit 0; **497,662 tokens**; ~40 web searches + read
the memory index, HORIZONLOG, `CertF.lean`, `ZKOpenRel.lean`, `FhEggClearing.lean`, and the seven deos
docs to ground itself. Full log `scratchpad/codex-round3.log` (final answer block L7206–8321). It
engaged adversarially — it opened by **correcting the brief's own Q1 premise** (below), which is the
behavior that makes the pattern worth running.

---

## Headline (the single most valuable insight)

**"Approximation PROPOSES; exact quantized translation-validation DISPOSES."** Codex's crux move on
Q1 is a correction to the brief's framing, and it is *right against the real Lean*: you **cannot**
"charge approximate feasibility to ε and reuse `certifies_epsilon_optimal`," because the deployed
`Certified` predicate (`CertF.lean:97`) requires **exact** primal and dual feasibility (`Af = 0`,
`0 ≤ f ≤ c`, `Aᵀπ + s ≥ w`). The sound architecture instead:

1. runs the cheap **approximate** encrypted solver (CKKS/BFV, carry-free adds) as an *untrusted search*;
2. **EXACTIFIES** the candidate onto the integer grid → `(f_q, π_q, s_q)` satisfying the exact
   constraints (dual repair `s_q = ⌈(w_q − Aᵀπ_q)₊⌉_Δ`; primal repair `d` via an untrusted solver the
   STARK only checks; Hoffman bound `dist(f̃, P) ≤ H_P·r_p`);
3. the STARK recomputes the **exact** gap `G_q = c_qᵀs_q − w_qᵀf_q` and the honest certified value is
   literally **`ε_cert = G_q`** — fed straight into the already-proven `certifies_epsilon_optimal`.

**Quantization/CKKS/PDHG-iteration noise governs COMPLETENESS (does the candidate pass, and how large
is `G_q`) and parameter SIZING — never SOUNDNESS.** The R3 thesis, in codex's own boxed form:

> approximate, private, lattice-based computation **proposes**; exact quantized translation-validation
> **disposes**; the duality gap bounds suboptimality; a separate exact/no-wrap theorem forbids minting.

This is a genuine sharpening of ember's "the `Cert-F` ε absorbs the quantization noise" — the ε does
*not* absorb it into soundness; the exactification does, and the ε is the *recomputed* gap of the
exact witness. Everything downstream (the mint-safe lemma, the carrier design) follows cleanly from
this separation, and it reuses the existing keystone **verbatim**. **Assessment: GOLD.**

---

# §A — THE BRIEF (as fed to codex, condensed)

*Full self-contained brief: `docs/deos/FHEGG-CODEX-ROUND3-BRIEF.md`. Synopsis of what codex was
grounded on and asked.*

**The system.** A **turn** = an attenuable proof-carrying token over owned state, leaving a receipt.
The **fhEgg kernel**: a batch uniform-price call auction is an **aggregation, not a matching** — orders
fold into a price-indexed cumulative demand/supply curve (commutative-monoid fold of unary
step-increments), clearing is one monotone crossing `p* = min{p : D(p) ≥ S(p)}`. The **Private Convex
Engine** generalizes: a first-order/operator-splitting solver run `T` times is the fhEgg shape iterated
(`x ← prox(x − τ·A·x)`, public `A`, one small prox/iter). The killer move — **verify, don't find**: a
convex optimum is certified by a primal-dual pair whose duality **gap is a linear functional**, so the
solver is an untrusted search and the gap is the cheap checked certificate. Three product tiers on one
verified kernel (Tier 0 DARK/FHE-no-viewer, Tier 1 SHIELDED/STARK-ZK, Tier 2 OPEN); the tier is a type
in `fhIR`.

**Ground truth (VERIFIED, not to be reconstructed).** `CertF.lean` — `Cert-F` duality certificate
proven (`weak_duality`, `certifies_epsilon_optimal` KEYSTONE, both-polarity non-vacuity + teeth,
emittable AIR `certCircuit`). `FhEggClearing.lean` — fold + crossing proven, incl. the R1-correction
`Fstep` monotone operator with `Fstep_monotone`/`crossing_fixed` (Tarski least fixed point on the price
chain). `RevealNothing.lean` — `View ≈ Sim∘Q` over a leakage functor, floor-conditional bundle.
`ZKOpenRel.lean` — the resource-graded open-relation category; `d` a strong-monoidal functor;
conservation = `d⁻¹(0)`; all four objects as instances; **the ONE open theorem** `GuardedTraceClosure`
(feedback-feasibility closure) carried as a hypothesis field, never `sorry`. Built: `fhegg-solver`
(26/26: flow-LP, QP, Cert-F→AIR/STARK, PDHG, GPU), `fhIR-0` (tier-as-type DSL). PQ posture: Option-A
Poseidon2 hash-commitment + in-AIR conservation LANDED; the PQ **lattice-additive** aggregation-fold
(aggregating *independently-produced* commitments) is the named residual.

**The two NEW empirical facts.** (a) The FHE no-viewer envelope was MEASURED: the "addition is free"
premise is **REFUTED for exact-integer TFHE** — exact multi-bit integer addition needs **carry
propagation**, each carry a PBS-class op, so the `O(N·K)` fold is PBS-dominated (minutes at N in the
low hundreds); the `O(K)` crossing was never the problem — **the fold is the bottleneck.** (b) The
corrected Tier-0 direction: a **lattice-additive** carrier (native `R_q` ring addition, no carry, no
bootstrap) is **one object solving two problems** — it fixes the Tier-0 speed AND closes the
PQ-commitment residual.

**The five questions.** Q1 (crux): the sound-quantized/lattice-additive fold — a concrete PQ
additive scheme with cheap carry-free adds + small crossing + in-AIR-verifiable binding; the
**ε-absorption** error-propagation bound; and the **`mint_safe_quantization`** conservative-rounding
Lean lemma (optimality approximate, conservation provably mint-safe). Q2: the Cert-F-certifiable
clearing-mechanism family + novel mechanisms. Q3 (crux): PROVE/sketch or find the obstruction to
`GuardedTraceClosure`. Q4: Price-Cert derivatives deepened + novel products. Q5: homomorphic-native
efficiency openings.

---

# §B — CODEX'S ANALYSIS, CAPTURED + ASSESSED

## Q1 — The sound quantized / lattice-additive fold **(CRUX)**

### What codex proposed

**(1) The concrete carrier — a linked three-layer object, not one scheme.** An additive commitment is
*not* an encryption (it binds + aggregates but cannot compute a hidden comparison); CKKS/BFV compute
but give no externally-auditable binding tying independent orders to the accepted batch. So each order
is `E_i = (ct_i, C_i, Π_i)`:
- `ct_i = Enc_pk(m_i; ρ_i)` — an FHE ciphertext (computes the fold/search),
- `C_i = Com_ck(m_i; r_i)` — a **BDLOP-family** additive lattice commitment (2016/997), binding =
  Module-SIS, hiding = separate MLWE/leftover-hash (the *actual* matrix distribution + opening set +
  reduction must be honored — "not an arbitrary matrix called A"),
- `Π_i` — a proof that both carry the *same* quantized `m_i`, in range, well-formed (bucket/side/
  asset/nullifier), owned, non-duplicated.

**Two arithmetic profiles.** For the **auction fold**, exact quantized **BFV/BGV** beats CKKS —
plaintext-ring additions are native modular adds (no carry, no PBS); the final crossing does
coefficient-extraction / key-switch into **LWE/TFHE/FHEW** for one programmable-bootstrap LUT
(CHIMERA 2018/758, PEGASUS 2020/1606 for the scheme-switch). For general **`T`-step PDHG**, CKKS is the
search carrier (2016/421). **Hard boundary codex insisted on:** there is **no comparison from additive
homomorphism alone** (sign/min/max/clamp/first-crossing are not affine) — a PBS, an approximate
polynomial, MPC, or disclosure is *mathematically unavoidable*; and verify-not-find removes the need to
*prove* the `T` iterations but **not their encrypted computation cost** (T nonlinear prox depths
remain). The "one small comparison" is a `T=1` auction fact, not a general-engine one.

**(2) The ε-absorption theorem — two levels (the headline).** *Level A (soundness):* exactify →
recompute exact `G_q` → `certifies_epsilon_optimal` (`CertF.lean:133`) gives `OPT_q − w_qᵀf_q ≤ G_q ≤ ε`,
independent of CKKS noise / quantization / iteration count / whether the solver even ran PDHG. *Level B
(completeness/capacity planning):* the inexact-PDHG error `E_T ≤ L_Φ^T·E_0 + Σ L_Φ^{T−1−t}·η_t` with
`η_t ≤ a_A·δ_quant + b_A·δ_CKKS + δ_prox` (matching inexact Chambolle–Pock, Rasch–Chambolle
arXiv:1803.10576), giving the honest planning bound `ε_honest ≤ C_PD/T + L_G·E_T + ‖w‖_*ρ_f + ‖c‖_*ρ_s`
— exposing a real precision/iteration trade-off (under mere nonexpansiveness, larger `T` eventually
*worsens* the implementation-error term). Budgets: plaintext no-wrap `N·2^s·V_max + B_alg + B_cert < t/2`
(illustratively `t≈2³¹, N=4096 ⇒ s≤17`, flagged "arithmetic illustration, not security"); aggregate
opening radius `‖Σr_i‖ ≤ σ√N(√d + √(2log(K/α)))` w.h.p. or `Nβ` worst-case, and the SIS witness
`A(r−r') + G(m−m') = 0` **includes the message difference**, so MSIS must be sized to the *accepted
aggregate* radius. AIR verification: prefer native `q_c = p_AIR` (needs `q_c ≡ 1 mod 2n`, no-wrap fits,
MSIS meets security), then small RNS/CRT, then external-lattice-proof; **bridge once per batch**.

**(3) Mint-safety — the Lean lemma.** Separate strictly: *optimality may have ε>0; settled conservation
may not.* Round **inputs down / outputs up** to their integer proxies (interval form: `qin = ⌊L_in/Δ⌋`,
`qout = ⌈U_out/Δ⌉`), settle the integers, check the exact gate `Σqout ≤ Σqin`. The precise lemma:

```lean
theorem mint_safe_quantization
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Δ : ℚ) (hΔ : 0 ≤ Δ)
    (vin : ι → ℚ) (vout : κ → ℚ) (qin : ι → ℕ) (qout : κ → ℕ)
    (hin  : ∀ i, Δ * (qin i : ℚ) ≤ vin i)
    (hout : ∀ j, vout j ≤ Δ * (qout j : ℚ))
    (hgate : (∑ j, qout j) ≤ ∑ i, qin i) :
    (∑ j, vout j) ≤ ∑ i, vin i
```

plus the load-bearing companion (the no-wrap refinement of the field gate):

```lean
theorem field_gate_refines_nat_eq
    (hleft : outSum + burn < p) (hright : inSum < p)
    (hfield : ((outSum + burn : ℕ) : ZMod p) = ((inSum : ℕ) : ZMod p)) :
    outSum + burn = inSum
```

"Without the two range hypotheses, a field equality permits a discrepancy of `p` — exactly a modular
mint. This lemma is as load-bearing as `mint_safe_quantization`."

### Assessment — **GOLD** (the crux delivered)

- **The "exactify + recompute, noise is completeness not soundness" reframe is correct against the real
  Lean, and it is the most valuable single output.** I verified: `certifies_epsilon_optimal`
  (`CertF.lean:133`) takes `Certified lp f π s`, and `Certified` (`:97`) unfolds to `PrimalFeasible ∧
  DualFeasible ∧ gap ≤ ε` with `PrimalFeasible := A *ᵥ f = 0 ∧ 0 ≤ f ∧ f ≤ c` (`:86`) — **exact
  equalities/inequalities, no slack**. So codex is right that approximate feasibility genuinely cannot
  reuse the keystone; the honest path is to exactify onto the grid and recompute the exact `G_q`. This
  corrects ember's own Q1 premise in the sound direction — the mark of a real second mind, not a
  compliant one.

- **`mint_safe_quantization` is a genuine, directly-provable, genuinely-mint-safe lemma.** I checked the
  proof: `Σvout ≤ Σ Δ·qout = Δ·Σqout ≤ Δ·Σqin = Σ Δ·qin ≤ Σvin`, where the middle step needs exactly
  `hΔ : 0 ≤ Δ` and the ℕ→ℚ cast monotonicity of `hgate`, and the endpoints are `hout`/`hin`. Valid,
  short, no `sorry`-bait. The **directionality is the subtle correct part**: outputs must be *over*-
  approximated by their proxy (`vout ≤ Δ·qout`) and inputs *under*-approximated (`Δ·qin ≤ vin`), so the
  cheap integer gate `Σqout ≤ Σqin` *provably* forbids `Σvout > Σvin` — a mint within the quantization
  tolerance is impossible, and the total deviation reserve is bounded by `Σω_k + (n_in+n_out)Δ`. Codex's
  own tooth — "if rounded quantities are only proxies not actual settlements, flooring outputs is unsafe
  because the real output may exceed the proxy" — is exactly the correctness hinge and shows it
  understood the direction, not just the algebra.
- **The `field_gate_refines_nat_eq` companion independently reconstructs the repo's landed no-wrap
  discipline.** This is precisely `shielded_ring_clearing_air.rs::VALUE_BITS` + `RealCrypto.lean::
  twoLeg_noWrap_conservation` (the `RING_LEGS · 2^VALUE_BITS ≤ p` assertion that upgrades the field gate
  to *integer* conservation). Codex arrived at "a field equality without range bounds is a modular mint"
  from scratch and correctly flagged it as co-load-bearing with the quantization lemma. Strong
  convergence with existing verified work — and it tells us the two lemmas ship *together* or not at all.
- **The linked `(ct, C, Π)` carrier is the correct architecture and it is honestly costed.** The
  separation "commitment binds asynchronously, FHE computes, proof links them, and neither replaces the
  per-order well-formedness proof" is right (an aggregate-only bridge lets malformed orders cancel). The
  "no comparison from additive homomorphism alone" and "T nonlinear depths survive verify-not-find" are
  correct, non-obvious *dampers* on the brief's optimism — the same adversarial-precision value as R1/R2.
- **Did codex give a concrete PQ additive scheme? Yes** — BDLOP (2016/997) additive commitment for
  binding + exact-quantized BFV/BGV for the carry-free fold + CHIMERA/PEGASUS scheme-switch to TFHE for
  the crossing — grounded in the actual papers, with the honest caveats (binding needs the real
  reduction; hiding is separate; size for the aggregate radius; a toy `n=256,k=2,q≈2³¹` "says nothing
  about 128-bit security without a lattice-estimator run"). It did **not** hand-wave a magic scheme.
- **Net Q1:** the reframe (soundness = exactify+recompute; noise = completeness) + the provable
  `mint_safe_quantization` + no-wrap companion + the linked carrier = a **directly buildable, correctly-
  Lean-grounded** answer to the highest-value question. This is the round's payoff.

---

## Q2 — The clearing-mechanism family

**What codex proposed.** The boundary is not "convex vs nonconvex" but *"does the mechanism admit a
small, trace-independent upper-bound certificate with feasibility + conservation cheaply checkable over
**public** operators?"* A table grades: divisible welfare/frequent-batch PWL (core Cert-F); discriminatory
/pay-as-bid (allocation-LP dual, but private bid×fill is bilinear-in-witness and incentives are *not*
certified); **Fisher/Eisenberg–Gale** (KKT certificate `p_j ≥ β_i v_ij` + budget exhaustion +
complementarity `x_ij(p_j − β_i v_ij) = 0` — trace-independent and small but **quadratic**, not
Cert-F-linear; Cole et al. arXiv:1609.06654); **CFMM routing** (pool-local KKT/normal-cone, Angeris
2204.05238, convex until fixed venue costs); **combinatorial** — the useful verify-not-find construction
`V(x) ≤ OPT_IP ≤ OPT_LP ≤ U_LP`, so an **LP dual certifies an additive-approximation guarantee for an
NP-hard mechanism** (exact iff zero gap; sufficient not complete). Three **novel mechanisms**: *streaming
certificate accumulation* (dual state-potentials `λ_t` telescope, `ε_{1:T} = Σε_t` — "the optimization
analogue of a recursive turn receipt"); *cross-tier clearing* (direct-sum the tier capacities
`c = c⁰+c¹+c²`, common dual prices certify the joint optimum); *comparison-metered clearing* (design the
rule so only two authoritative comparisons `¬Clears(j−1), Clears(j)` are certified — "particularly
natural when additions are cheap and comparisons are the metered resource").

**Assessment — solid, mid-to-gold.** The reframed boundary ("public operators + small trace-independent
certificate") is the correct and sharp criterion, and the per-mechanism certificates are known convex
results applied correctly (the Fisher KKT being *quadratic not linear* is an honest correction to any
"everything is Cert-F-linear" hope). The **LP-dual-certifies-an-approximation-bound** construction for
combinatorial clearing is genuinely useful — it extends verify-not-find to the NP-hard boundary with an
honest "sufficient, not complete." The three novel mechanisms are the real contribution: **streaming
telescoping certificates** (a cumulative receipt that never reopens past batches — a clean fit to the
turn-kernel) and **comparison-metered clearing** (a mechanism *designed* for the cheap-add/metered-
compare regime the lattice-additive carrier creates) are both novel-in-assembly and directly aligned
with the R3 carrier. Mid on the catalog, gold on those two.

---

## Q3 — The categorical closure theorem **(CRUX)**

### What codex proposed

**`GuardedTraceClosure` is FALSE as stated — a minimal counterexample.** Take `X = Y = 1`, `U = Bool`,
`defect(f) = 0`, and `f.rel ((*,u),(*,v)) ⟺ v = ¬u`. Then `f` is **conservative** (defect 0),
**guarded/total** (every `u` has output `¬u`), **deterministic and single-valued** — yet
`gtrace(f)(*,*) ⟺ ∃u, ¬u = u`, which is **false**. So **Conservative + Guarded + Functional does NOT
imply traced Guardedness**, and neither compact closure nor ordinary traced-monoidal structure rescues
it (`Rel` is compact closed, yet relational trace can be empty — "categorical trace supplies the wiring
algebra, not a fixed-point existence theorem"). The diagnosis: the module's `Guarded` is really
`Total`; genuine guarded-trace theory (Goncharov–Schröder arXiv:1802.08756) *restricts* admissible
cycles via guarded/Conway fixed-point operators.

**The TRUE replacement theorems.** (i) **Tarski feedback** — if `U` is a complete lattice and the
feedback admits a *monotone* self-map `Φ_x` with `f.rel (x,u) (Y_x u, Φ_x u)`, then `lfp(Φ_x)` witnesses
`Guarded(gtrace f)`; especially clean for a finite box `∏{0..b_i}` (a complete lattice, giving an
**exact integral** fixed point, unlike Brouwer). (ii) **Kakutani** — for a compact-convex `U` with
nonempty-compact-convex feedback correspondence `Γ_x` of closed graph, `u* ∈ Γ_x(u*)` gives the guard.
(iii) **Flow-network specialization** — codex *demolishes the brief's own candidate hypothesis*: "`Af=0`
in a box always has a solution" is true only weakly (`f=0` when lower bounds are 0) and does **not**
establish positive volume / required balances / lower-bound obligations; the right guard is a
**Hoffman/max-flow cut-feasibility** witness (+ total unimodularity for an integral vertex). **The
categorical repair:** replace the global conjecture with a **partial trace indexed by a typed
admissibility witness** `TraceAdmissible f := Monotone ⊎ Kakutani ⊎ Contractive ⊎ FeasibleCirculation`,
prove `TraceAdmissible f → Guarded(gtrace f)`, then `Conservative f ∧ TraceAdmissible f → Conservative
(gtrace f) ∧ Guarded(gtrace f)` — "defect-zero proves conservation; trace-admissibility proves
fixed-point existence; neither impersonates the other." Plus `GuardedOn(P, f)` (markets don't clear
every syntactic boundary state). Adaptive composition then rides the existing `comp_guarded`, with
Bekić/Conway for nested feedback.

### Assessment — **GOLD, arguably the sharpest single result of the round**

- **The counterexample is valid against the actual Lean definitions — I checked it.** `gtrace f`
  (`ZKOpenRel.lean:424`) has `rel x y := ∃ u, f.rel (x,u) (y,u)`; `Guarded` (`:398`) is `∀ x, ∃ y, rel x
  y`. With `f.rel ((*,u),(*,v)) ⟺ v = ¬u`: `f` is `Guarded` (∀(*,u), ∃(*,¬u)), `Conservative` (defect 0),
  functional — but `gtrace f . rel * * = ∃u, u = ¬u = False`, so `Guarded (gtrace f) = False`. This is a
  **genuine disproof of the deployed conjecture**, not a citation. It has a real consequence the module's
  prose missed: `GuardedTraceClosure R` is false for *any* `R` (the `Bool` feedback works uniformly), so
  the `ZKUnification R` structure whose one field is `feedback_closure : GuardedTraceClosure R`
  **can never be inhabited** — the R1 framing "to inhabit `ZKUnification` is exactly to discharge the
  open theorem" was chasing a *false* statement, not merely an open one. That is an important, correcting
  finding.
- **The replacement is the right mathematics AND it connects to already-proven Lean.** The **finite-box
  Tarski** theorem is the correct home for the fhEgg crossing — and `FhEggClearing.lean` *already proves*
  the enabling fact: `Fstep_monotone` (`:254`) + `crossing_fixed` (`:246`) establish the crossing is the
  least fixed point of a monotone operator on the price chain. So codex's "the trace is admissible
  because the feedback operator is a monotone self-map of a complete lattice, not because its grade is
  zero" lands exactly on machinery the repo has in hand. The **flow-network correction** (Hoffman cut-
  feasibility, not "f=0 exists") is a real fix to *my brief's* suggested hypothesis (i) — the brief was
  loose and codex caught it.
- **Did it discharge the conjecture or restate it? Neither — it REFUTED it and replaced it with a
  provable one.** That is the honest and most valuable outcome: the deployed `ZKOpenRel.lean` should stop
  carrying `GuardedTraceClosure` as a to-be-discharged hypothesis field and instead prove
  `TraceAdmissible f → Guarded (gtrace f)` (the finite-box Tarski case first, directly on `Fstep`). This
  is a concrete, buildable change to the verified tower, not a slogan. **LANDED** — `ZKOpenRel.lean` now
  carries `guardedTraceClosure_refuted` + `traceAdmissible_guarded` (kernel-clean), with the crossing case
  discharged directly on `crossing_fixed` (the honest witness — a naive `lfp` on `ℕ` would pick up the
  spurious top `K` a non-clearing book has, which is exactly why `CrossingExists` + `Nat.find` is used).
- **Net Q3:** a valid disproof (checked against the real definitions), the precise true theorems (Tarski/
  Kakutani/flow-Hoffman), a correction to the brief's own flow hypothesis, and a typed-admissibility
  categorical repair that is the verify-not-find pattern lifted to feedback. Gold.

---

## Q4 — Price-Cert derivatives

**What codex proposed.** European/static: the state-price LP `U = max_{π≥0}{hᵀπ : Hᵀπ = a}` with
superhedging dual `min_y{aᵀy : Hy ≥ h}`, certificate `π≥0, Hᵀπ=a, Hy≥h, 0 ≤ aᵀy − hᵀπ ≤ ε` (Barratt–
Tuck–Boyd arXiv:2003.02878); output an arbitrage-free **interval** `[L,U]`, not a fake unique price; any
tabulated public payoff (barrier/digital/fractional) is linear *data* on a finite grid — the cliff is
private off-grid evaluation or scenario explosion. American/Bermudan: the **Snell-envelope LP** `min
V_root s.t. V_n ≥ g_n, V_n ≥ d_n Σ P_nm V_m` with an occupation/stopping-flow dual `(μ_n = e_n + c_n)`,
entirely linear — with an **honest correction** to R2: the Haugh–Kogan/Rogers martingale dual is
*equivalent after a Doob/extended-formulation transformation*, **not** literally the same variable-by-
variable LP dual. Barrier/autocall = finite-flag state expansion, same LP, cliff = state explosion.
**Novel derivative — the arbitrage-width claim** `(W − K)₊` where `W = U − L` is the certified no-arb
interval width: it "trades market incompleteness / disagreement / calibration scarcity directly,"
verified from two Price-Certs + one PWL gate — with the sharp caveat that a derivative on the *submitted*
certificate's raw `ε` is economically **unsound** (a solver can submit a deliberately loose cert; needs
a canonical minimum gap / bonding / fixed public budget).

**Assessment — solid, with one genuinely novel product.** The Price-Cert packaging and the Snell LP are
known convex-finance correctly applied (as Q4 asked). The value adds are two honesty teeth: the **R2
correction** (martingale dual ≡-after-transformation, not identical — so the earlier "verify it is
exactly the martingale dual" was slightly overstated) and the **"don't trade the raw submitted ε"**
caveat. The **arbitrage-width claim** `(W−K)₊` is a genuinely novel derivative that is *native to the
certificate architecture* — it monetizes exactly the object (interval width) that only a verify-not-find
private-mark engine produces, while state-price witnesses stay hidden. Novel product, mid on the catalog.

---

## Q5 — Homomorphic-native efficiency openings

**What codex proposed.** The gem: **coefficient-packed difference curves for an `O(N+K)` prefix scan
without rotations.** Encode an order active on buckets `[a,b]` as the sparse difference polynomial
`d_i(X) = q_i X^a − q_i X^{b+1}`; aggregate by native addition `D(X) = Σ d_i(X)`; multiply **once** by
the public `H_K(X) = 1 + X + ⋯ + X^{K−1}` — the coefficient of `X^t` in `D·H_K` is exactly the prefix
sum `Σ_{j≤t} D_j` (with ring dim `n ≥ 2K` or guard padding, no negacyclic wrap). Result: `O(1)` sparse
plaintext contributions/order + native ciphertext/commitment adds + **one** plaintext polynomial
multiply for *all* `K` cumulative buckets + **no** Galois-rotation prefix network — "which is why NTT
structure becomes useful here even though it does not help a naive per-bucket fold." Plus: crossing by
proposal + two-comparison local certificate; **SIMD across markets** via block offsets `D(X) = Σ_m X^{o_m}
D_m(X)` with guard bands (one NTT for many markets, direct-sum certs `ε_total = Σε_m`); sparse-order
validity proofs `O(log K)` in index ranges not `O(K)` one-hot; and the lattice/STARK sharing boundary
(share the `2n`-th-root NTT domain, twiddle tables, GPU kernels, Fiat–Shamir-batched ring openings — but
**not** assumptions: "MSIS binding does not follow from STARK polynomial-identity checking; the systems
share arithmetic infrastructure without laundering one assumption into another").

**Assessment — GOLD on 5.1, correct on the rest.** The **coefficient-difference-polynomial prefix scan**
is a genuinely clever, novel-in-this-setting construction: it recasts the cumulative-curve fold as a
single convolution with the all-ones polynomial, collapsing the `O(log K)`-rotation prefix network into
one plaintext multiply and making the ring-coefficient (not SIMD-slot) encoding the right home — exactly
the "homomorphic-native gigabrain opening" Q5 asked for, and it composes directly with the lattice-
additive carrier of Q1 (the same `C_i` aggregates the same `d_i`). The SIMD-across-markets block-offset
packing and the sharp "share infrastructure, never assumptions" boundary are correct and directly
actionable. The `O(N+K)` claim's cost migration into sparse-order validity proofs is named honestly
(as in R1). Gold on the difference-curve trick; correct engineering judgment throughout.

---

## Overall honest read — did codex add genuine value?

**Yes — decisively, and its strength (novel math + adversarial precision) landed on exactly the two
crux questions.** Ranked:

1. **Q1 — GOLD (the round's payoff).** The "approximation proposes, exact quantized translation-
   validation disposes" reframe *corrected ember's own ε-absorption premise in the sound direction*, and
   it is right against the real `CertF.lean` (which needs **exact** feasibility). The
   `mint_safe_quantization` lemma is directly Lean-provable, genuinely mint-safe within tolerance (via
   directional rounding), and correctly separated from the ε-optimality keystone; its `field_gate_refines
   _nat_eq` companion independently reconstructs the repo's landed `VALUE_BITS` no-wrap discipline. The
   linked `(ct, C, Π)` carrier + BFV-fold/TFHE-crossing/CKKS-PDHG split is a concrete PQ scheme with
   honest costs. **A concrete PQ additive scheme AND a buildable Lean lemma — the crux was met.**
2. **Q3 — GOLD (sharpest single result).** A *valid disproof* of `GuardedTraceClosure` (checked against
   the actual `gtrace`/`Guarded` definitions), the precise true replacements (finite-box Tarski — which
   lands on the already-proven `Fstep_monotone`; Kakutani; flow-Hoffman-cut), a correction to the brief's
   own flow hypothesis, and a typed `TraceAdmissible` categorical repair. It **refuted and replaced** the
   conjecture rather than restating it — the honest and buildable outcome (the `ZKUnification` structure
   as written can never be inhabited).
3. **Q5#1 — GOLD (concrete construction).** The coefficient-difference-polynomial `O(N+K)` prefix scan by
   one plaintext multiply — a real homomorphic-native efficiency win native to the lattice-additive carrier.
4. **Q2, Q4 — solid mid, with novel edges.** Known convex results correctly applied, plus genuinely novel
   items: the streaming telescoping certificate + comparison-metered mechanism (Q2), and the
   arbitrage-width derivative (Q4).

**Adversarial corrections it forced (real value, thread back into the docs/Lean):**
- You **cannot** charge approximate feasibility to ε and reuse `certifies_epsilon_optimal` — the real
  `Certified` needs exact feasibility; exactify then recompute the exact gap. *(Reframes ember's Q1.)*
- **`GuardedTraceClosure` is FALSE as stated** (not merely open) — the `ZKUnification` field can never be
  inhabited; replace with typed `TraceAdmissible → Guarded (gtrace)`. *(Corrects `ZKOpenRel.lean`.)*
- "`Af=0` in a box always has a solution" is only weakly true (`f=0`); it gives no positive volume /
  balances — use a Hoffman cut-feasibility witness. *(Corrects the brief's Q3 hypothesis (i).)*
- **No comparison from additive homomorphism alone**; the "one small comparison" is `T=1` only; general
  PDHG keeps `T` nonlinear depths (verify-not-find removes proving them, not computing them).
- The Haugh–Kogan/Rogers martingale dual is *equivalent-after-transformation*, not the literal Snell LP
  dual. *(Corrects R2.)* And size MSIS to the *aggregate* opening radius (the SIS witness carries the
  message difference too). *(Sharpens R1 Q4.)*

**Where it is disciplined rather than dazzling (honest):** Q2/Q4 are predominantly known convex results
correctly applied (the right outcome for those questions); the Q1 carrier's *pieces* (BDLOP, CKKS,
BFV, CHIMERA/PEGASUS, inexact PDHG, interval rounding) are all known — the novelty is the **proof-
carrying composition** (asynchronous lattice binding + carry-free fold + approximate search + one
aggregate hash-STARK bridge + exactified Cert-F + a separately-proved no-mint refinement, with **noise as
a completeness theorem and the exact recomputed gap as the soundness theorem**). Q3's fixed-point
theorems are standard; the novelty is making feedback-admissibility a *typed proof-carrying witness* —
the categorical verify-not-find.

**Verdict: GOLD, not mid.** Round 3 hit both crux questions with real, correct, buildable answers: a
concrete sound-quantized PQ carrier + a Lean-provable `mint_safe_quantization` (assessed against the real
`CertF.lean` and confirmed genuinely mint-safe), and a valid disproof-plus-replacement of the
`GuardedTraceClosure` conjecture (assessed against the real `ZKOpenRel.lean` and confirmed the deployed
conjecture is false, with the true theorem landing on the already-proven `Fstep` monotonicity). The
immediate build consequences: **(i)** make Tier-0 "approximation proposes / exactification disposes" the
architecture, and land `mint_safe_quantization` + `field_gate_refines_nat_eq` in `CertF.lean` /
`RealCrypto.lean`; **(ii) — LANDED (`metatheory/Market/ZKOpenRel.lean`):** `GuardedTraceClosure` is now a
proven refutation (`guardedTraceClosure_refuted`, the `Bool`-negation witness) and the true replacement
`traceAdmissible_guarded : TraceAdmissible f → Guarded (gtrace f)` (Knaster–Tarski via `OrderHom.lfp`)
lands on the proven crossing operator (`crossing_gtrace_guarded` via `crossing_fixed`/`Fstep_monotone`);
the four instances are shown `TraceAdmissible`, the closure is non-vacuous on a real monotone `Prop`
feedback, is extended to adaptive composition + tensor (`gtrace_comp_guarded`/`gtrace_tensor_guarded`) and
partial guards (`GuardedOn`), and `ZKUnification` is now INHABITED (`zkUnification`) over the true
`AdmissibleTraceClosure`; **(iii)** prototype the linked
`(ct, C, Π)` carrier + coefficient-difference-polynomial prefix scan; **(iv)** add streaming
dual-potential receipts and the arbitrage-width derivative to the `fhIR` product surface.

---

*Provenance: full codex output `scratchpad/codex-round3.log` (final answer block L7206–8321; **497,662
tokens**; codex-cli 0.144.1 / GPT-5.6-sol; `--sandbox read-only`). Literature codex cited (flag for a
proof pass, not re-verified line-by-line here): BDLOP lattice commitments (ePrint 2016/997); CKKS (ePrint
2016/421); CHIMERA (ePrint 2018/758); PEGASUS (ePrint 2020/1606); inexact Chambolle–Pock / Rasch–
Chambolle (arXiv:1803.10576); PDLP/Applegate et al.; Cole et al. Fisher markets (arXiv:1609.06654);
Angeris et al. CFMM routing (arXiv:2204.05238); Sandholm combinatorial winner determination; Barratt–
Tuck–Boyd convex risk-neutral pricing (arXiv:2003.02878); Haugh–Kogan & Rogers American-option duals;
Goncharov–Schröder guarded traced categories (arXiv:1802.08756); Knaster–Tarski; Kakutani.*
