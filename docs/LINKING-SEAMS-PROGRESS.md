# Linking-seams goal — progress record

Goal: link the parallel PQ-crypto proofs into ONE integrated formal foundation. Close every
executable↔spec and quantitative↔Boolean seam; prove the bridge, never relabel. Work is on branch
`mldsa-sign-route` (a +N clean superset of `main`; `git merge --ff-only mldsa-sign-route` captures it).
The Crypto real-verify/NTT chain is OUTSIDE the default `lake build` — build modules explicitly
(`lake build Dregg2.Crypto.<M>`), or direct-`lean`/hbox when the shared lock stalls.

## Seam 1 — executable ↔ spec
**VERIFY: DONE.** `VerifyCoreEqSpec.verifyCore_eq_spec` — `verifyCore = the FIPS 204 Alg-8 verify
predicate, for-all`, axiom-clean (no `native_decide` in the ∀). Built on:
- `NttFaithful.lean` — **the entire Cooley-Tukey NTT proven correct from scratch** (Mathlib lacks it):
  `nttEvalsAtRoots_canonical` (ntt = eval-at-negacyclic-roots), `nttMulHom_proven` (ntt is a ring hom),
  `nttLeftInverse_proven`/`ringRepFaithful_proven` (intt inverts; NTT computes the R_q product) — via
  `omega_orthogonality`, the butterfly primitive `bfFold_spec`/`cast_bfSweep`, the stage inductions
  `stage_inv`/`inttStage_inv`. Guards: size=256 + reduced-range (the props are FALSE unguarded — 3 bugs caught).
- `VerifyCoreEqSpec.lean` — `toRq` coeff↔R_q bridge (`toRq_schoolbookMul`, `toRq_nttMul`,
  `toRq_intt_matmul_row` = the fast NTT matmul IS the spec's A·z−c·s over R_q), `unpackBits_packBits`
  (codec round-trip), `verifyCore_split`.
**SIGN: substantially linked.** `SignCoreSpec.lean` — 5 ring-faithfulness ∀ lemmas + `sign_produces_spec_valid`
(honest signCore output satisfies the FIPS Alg-8 verify predicate, via verifyCore_eq_spec). Residual: full
symbolic `signCore = Sign_internal` with the rejection loop (partial def, byte-exact-pinned), ExpandMask=spec.
**KEM: DONE (ring core).** `MlKemNttFaithful.mlkem_ntt_ring_faithful` — the INCOMPLETE Kyber NTT proven
correct from scratch (q=3329, 128 quadratic pair-leaves, forward `nttMulHom_proven` + inverse
`nttLeftInverse_proven`, axiom-clean). `DecapsCoreSpec.decrypt_ring_faithful` (`v−ŝᵀu` = the FIPS 203
K-PKE.Decrypt over R_q) + `EncapsCoreSpec.encrypt_ring_faithful` (`u=Aᵀy+e1`, `v=tᵀy+e2+Δm`) — decaps/encaps
ring computations = the spec, for-all, riding the Kyber NTT via the `toRqKem` bridge.

**ALL FOUR PQ DIRECTIONS' RING CORES = SPEC** (verify+sign+decaps+encaps), each on its own from-scratch
NTT-correctness proof. BOTH the complete (ML-DSA) and incomplete (ML-KEM) NTT are proven — Mathlib ships neither.
**BYTE-LEVEL `=spec` now closed for KEM both directions**: `DecapsCoreSpec.kpkeDecrypt_eq_spec` +
`EncapsCoreSpec.kpkeEncrypt_eq_spec` — the literal `Id.run do` byte executables = the FIPS 203 K-PKE
predicates, for-all (do-block unfold via the opaque-`f` route + honest-key reindex + the proven ring cores).
Verify is the full biconditional (`verifyCore_eq_spec`); sign is ring-faithful + `sign_produces_spec_valid`.
**Residuals (named, non-core):** the FO wrappers (`G`/`J`-KDF, Keccak generic slots), compress/decompress
rounding `μ=Δ·m` (rides `MlKemCorrect`), sign's full symbolic rejection loop (byte-exact-pinned partial def),
the byte round-trip bookkeeping; the abstract `MlDsaParams` module-map; KATs → full NIST ACVP.

## Seam 2 — quantitative ↔ Boolean: DONE
`FloorBridge.lean` — `MSISHardQuant→MSISHard` (+DL/HashCR) via the advantage-1 argument; migration template
`turnauth_forces_authorization_quant` (Boolean soundness as a corollary of the quant floor). Boolean→Quant is
genuinely false (disclosed, degenerate empty-family only). Tree can run on ONE quantitative foundation.

## Seam 3 — model ↔ reality: DONE
`ModelBridge.lean` elaborates kernel-clean (`lake env lean` → `#assert_all_clean: 32 keystones pinned
kernel-clean`; no `native_decide` in any `∀`). Both places the quantitative campaign quietly identified model
with reality are materialized.
- **§A — hybrid combiner: shared challenge → INDEPENDENT.** `IndepHybridForkingFamily` gives the two legs their
OWN challenge sets and prefix worlds; `winProb_prod_factor` is the product-measure factorisation, so
`hybridForgerAdv = classicalForgerAdv · pqForgerAdv` (`hybridForgerAdv_eq_mul`, an equality) and
`hybrid_forger_negl_under_floors_indep` re-proves `Negl` under `DLHardQuant ∨ MSISHardQuant` with the legs'
challenges genuinely independent — the shared-challenge assumption is gone. Teeth: one secure leg ⇒ `0`; both
broken ⇒ `4/25` (the independent PRODUCT, not the shared-challenge `2/5`).
- **§B–C — finite shadow ↔ real infinite RO: a THEOREM.** `TailIndependent` names the one thing not provable from
`Forger` structure (acceptance independent of the RO answers strictly above the fork index); it is load-bearing
with both poles exhibited — `exAbstractForger` (reads only the challenge) satisfies it, `exTailForger` (reads an
above-challenge coordinate) refutes it. §C BUILDS the genuine infinite-product random-oracle measure
(`roMeasure = Measure.infinitePi (uniform Rq)`, a real `IsProbabilityMeasure` on `ℕ → Rq`) and PROVES
`abstractShadow_advantage_eq_roMeasure`: the finite shadow's advantage EQUALS the real acceptance probability
under it (the tail genuinely marginalised via `acceptEvent_eq_cylinder` + `infinitePi_cylinder`, not frozen).
The model↔reality identification is a theorem — no residual, no assumption, no `sorry`.

## Seam 4 — trust-shrink + gaps: δ ROUTE CLOSED (one named arithmetic residual)
`MlKemDelta.lean` elaborates kernel-clean (`#assert_all_clean: 86 keystones`; no real `sorry` — the `sorry`
tokens are doc-comment prose). Two layers.
- **The union bound + the FIPS-δ capstone (PROVED).** `mlkem_decapsFail_le` (`Pr[fail] ≤ 768·τ`), and
`mlkem768_decapsFailure_le_delta : winProb (decapsFails ez) ≤ MlKemCorrect.mlKem768Delta` (the FIPS 203 δ =
`2⁻¹⁶⁴`) — conditional on the per-coefficient tail `PerCoeffHoeffdingTail ez 2⁻¹⁷⁴`. It FIRES end-to-end on a
genuine positive-variance model (`rademacher_delta_fires`) through the sub-Gaussian discharge
`perCoeffHoeffdingTail_of_subgaussianSum`. The named tail is load-bearing (`perCoeff_tail_satisfiable` /
`perCoeff_tail_refutable`).
- **The generic-concentration wall STANDS as proven fact — and the exact-MGF route clears it.** For the REAL
CBD-convolution-product noise no generic inequality reaches δ: the Hoeffding range proxy overshoots the variance
budget 16× (`hoeffding_budget_exceeds_2800`), Chebyshev is 166 bits short (`chebyshev_perCoeff_tail_ge_2pow_neg8`),
and even granting Bernstein the Kyber params fall short (best-case `≈ 2⁻¹¹⁷` after the union bound —
`bernstein_honest_misses_delta`). §12 escapes all three with the EXACT moment-generating function: the per-term
CBD MGF `cosh(s/2)⁴` (`mgf_cbd2_eq`), the convolution-PRODUCT MGF `E_r[cosh(s·r/2)⁴]` (`mgf_cbd2prod_factored` /
`mgf_cbd2prod_le`, the very cross-term §10 flagged), fed through Mathlib's EXACT Chernoff bound
(`measure_ge_le_exp_mul_mgf`) and the product-of-MGFs law for independent sums (`iIndepFun.mgf_sum`), assembled in
`winProb_abs_exactMgf_le`. It discharges the tail for the REAL convolution structure `CoeffIsExactMgfSum`
(`perCoeffExactMgfTail_of_exactMgfSum`; the tooth `cbd2prod_isExactMgfSum` fires on a genuine `e·r` product) and
PROVES in Lean `winProb (decapsFails ez) ≤ 2⁻¹⁴⁰` (`mlkem768_decapsFailure_le_delta_exactMgf`) — 23 bits past the
Bernstein best-case `2⁻¹¹⁷` the sub-Gaussian surrogates could not clear. **§18 (2026-07-13) TIGHTENS this to
`≤ 2⁻¹⁵³` AND makes it UNCONDITIONAL** (`rZ_decapsFailure_le_delta153`, on the true near-uniform compression-error
law `rZ`, R2 discharged, no `PerCoeffHoeffdingTail` hyp) — this **SUPERSEDES** the earlier `≤ 2⁻¹⁴⁸` "Chernoff
ceiling" framing (`mlkem768_decapsFailure_le_delta_unconditional_tight`, the `±104` envelope model, which stands but
is no longer the sharpest): refining `Δv` to the TRUE near-uniform compression error (`≈ e^{27.37}` vs the envelope's
`≈ e^{31.2}`) buys the per-coefficient Chernoff to `2⁻¹⁶³`, `2⁻¹⁵³` after the `768`-fold union.
- **The remaining residual — FIPS `2⁻¹⁶⁴` reduced to ONE decidable inequality (`R1`), certified-numerics PENDING.**
The gap from the proven `2⁻¹⁵³` to the exact FIPS δ (`2⁻¹⁶⁴`) is reduced (§16/§19) to a single per-coefficient exact
convolved-tail inequality `LightExactPerCoeffTail` (`≤ 2⁻¹⁷⁴`, true value `≈ 2⁻¹⁸⁰` near-Gaussian) — the exact-PMF
tail on the true light law, kernel-computable but not kernel-CHECKABLE by `decide` at the required precision. This is
the named **R1** residual: it needs a CERTIFIED numeric FFT-convolution evaluation (a different formalization),
which is **IN FLIGHT — PENDING**, not finalized. The gap is the **Bahadur–Rao prefactor the Chernoff rate discards at
~15.7σ**, NOT arithmetic slack. `2⁻¹⁵³` is the honest assumption-free UNCONDITIONAL bound today; `2⁻¹⁶⁴` awaits R1.
See `MlKemDelta.lean` §18/§19 (`rZ_decapsFailure_le_delta153`, `exactConvTailFrac_closes_delta`) for the authority.

## Circuit-soundness floor — FRI on the hash floor, deployed security on one named list-decoding Prop
`FriSoundness.lean` FORMALIZES the published FRI soundness argument (BBHR18 folding + the BCIKS20 refinement) as
actual Lean theorems, no `sorry`, no smuggled hardness — resting only on the standard hash floor `HashCR`
(Poseidon2 sponge collision-resistance) and concrete field/rate params. The folding key lemma
`fold_close_of_two_alpha` (distance preserved by folding, the two-point unique-decoding bound) and
`fri_fold_soundness` (an accepting-yet-far transcript forces an exceptional challenge OR a hash collision) are
proved. The arity-8 geometric proximity keystone `friProximityK8_discharge` / `friProximityK8_discharge0` is
`fold_close_of_arity_challenges` APPLIED at `n = 8` (proved, not a fresh assumption), and
`FriBridgeDeployedArity.lean` composes proximity → `CircuitSound` at `d = 0` — unique decoding, "the accepted
oracle IS a genuine codeword" — fully closed for the honest instance (`honest_deployedArity_circuit_sound`, no
open premises), with the residual hypotheses `hplumb` (Merkle binding, an appeal to `HashCR`) and `hcode_sat` (the
codeword-side AIR arithmetic, load-bearing).
**The `d > 0` regime is NOT composed there and IS a genuine open item.** Translating the geometric `64·d`
closeness into a concrete soundness-error bound at the deployed `num_queries`/`log_blowup` is a quantitative step
not taken; the deployed wrap runs only 19 queries because its security lives at the Johnson list-decoding radius
`δ_J = 1 − √ρ = 7/8`, carried as the NAMED Prop `FriLdtDeployedBound` (`BabyBearFriDeployedInstance.lean`).
**That Prop as-written is now DISCHARGED** (`FriLdtJohnson.lean`, `friLdtDeployedBound_discharge`, axiom-clean):
at `δ_J = 7/8` it is the trivial counting else-branch, so `ldt_bound_unconditional` supplies the `2⁻⁵⁷` payoff
with no hypothesis. Its genuine research-grade residual (words inside the `δ_J` ball, past unique decoding) is
two precisely-named lemmas — `RSListBound` and `FriProximityGapChallenges` — each PROVED at `L=1` and instantiated
on the deployed rate-`1/64` code (min-distance `127`); only their `L>1` generalization remains open.

## Seam 5 — deployment integrity: the GAUNTLET CLAUSE MET; deployment plumbing remains
**WHOLE-TREE gauntlet PASSED on hbox (`lake build Dregg2` + the full linking chain = 9560 jobs, exit 0)** — the
entire metatheory tree AND the from-scratch crypto chain compose as one, no errors (OOM history laid to rest).
**`main` CAPTURED at `d8020987c`** (the +251 clean superset fast-forwarded). So the done-condition's "composes
green in one whole-tree gauntlet on main" clause is MET.
Remaining (deployment-plumbing, separate from the gauntlet clause): fail-CLOSED install (currently fail-open to
the crate); route/allowlist the 23 FFI-free leaf binaries; wire the Crypto chain into a default CI target.

## STATUS: all five seams + the gauntlet clause substantially MET
Seam 1 (cores ARE the spec — both NTTs proven from scratch, 4 directions), Seam 2 (tree on quantitative floors),
Seam 3 (model↔reality is a theorem: independent-challenge combiner + the infinite-RO measure bridge), Seam 4 (δ
route closed via the exact-MGF convolution; capstone fires on a genuine model), Seam 5 gauntlet-clause (whole-tree
green on main). The linking + circuit-soundness tower rests on two named, non-axiom cryptographic floors: the hash
floor **`HashCR`** (Poseidon2 sponge collision-resistance — unavoidable; every hash-based system assumes it), and,
at the deployed low-query FRI parameters, the two BCIKS20 Johnson-radius lemmas **`RSListBound`** +
**`FriProximityGapChallenges`** — the `FriLdtDeployedBound` Prop as-written is now DISCHARGED
(`FriLdtJohnson.lean`, the trivial counting branch), and these two sharp lemmas are its genuine residual, each
PROVED at `L=1` (deployed RS min-distance `127` closed) with only the `L>1` generalization open. Neither floor is
smuggled; both are visible `Prop`s.

Honest named residuals (each a precisely-named obstruction, nothing laundered):
- **Seam 4:** the true-`Δv` refinement now proves `≤ 2⁻¹⁵³` UNCONDITIONAL in-kernel (§18,
  `rZ_decapsFailure_le_delta153`, R2 discharged — SUPERSEDES the earlier `2⁻¹⁴⁸` envelope ceiling); the gap to the
  exact FIPS δ `2⁻¹⁶⁴` is reduced to ONE decidable per-coefficient exact-convolution inequality (`R1`,
  `LightExactPerCoeffTail ≤ 2⁻¹⁷⁴`, true `≈ 2⁻¹⁸⁰`), the Bahadur–Rao prefactor the Chernoff rate discards at ~15.7σ —
  NOT arithmetic slack. Closing it needs a CERTIFIED numeric FFT-convolution evaluation, which is **IN FLIGHT —
  PENDING** (not finalized). `2⁻¹⁵³` is cryptographically negligible, so R1 is exactness, not security.
- **Circuit floor:** the two `L>1` Johnson/correlated-agreement lemmas `RSListBound` +
  `FriProximityGapChallenges` (the `FriLdtDeployedBound` Prop as-written is DISCHARGED, `FriLdtJohnson.lean`;
  these are its residual, each `L=1`-proved with the deployed RS min-distance `127` closed); the general
  `[StarkSound]` discharge across all sites (the `d = 0` deployed-arity composition IS proved).
- **Seam 1:** the FO wrappers (`G`/`J`-KDF, Keccak slots), compress/decompress rounding, sign's full symbolic
  rejection loop (byte-exact-pinned partial def), the byte round-trip bookkeeping, the `MlDsaParams` module-map,
  KATs → full NIST ACVP.
- **Tree-wide:** `native_decide`-shrink toward full kernel-checking; deployment plumbing (fail-CLOSED install,
  routing the FFI-free leaf binaries, wiring the Crypto chain into a default CI target).

CLOSED since the prior record: Seam 3's `TailIndependent` measure step (materialized in `ModelBridge` §C); Seam 4's
"δ needs Bernstein-not-Hoeffding" pessimism (the exact-MGF route reaches `2⁻¹⁴⁰`, 23 bits past Bernstein's ceiling).

## Prior campaign (context)
The PQ-TCB deployment is DONE + live-proven: ML-DSA verify+sign, ML-KEM decaps+encaps all route through the
verified Lean cores on the node (crate out of the TCB, each proven in a running-binary hbox test).
See `docs/CRYPTO-TCB-OVERNIGHT.md`.
