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

## Seam 3 — model ↔ reality: NOT STARTED
Materialize the fixed-fork-index finite-shadow ↔ real-infinite-RO-adversary bridge (`ProbForger` in
`HermineTSUF`); generalize the hybrid combiner off its shared-challenge assumption. The deepest remaining math.

## Seam 4 — trust-shrink + gaps: PARTIAL (with a key honest finding)
`MlKemDelta.lean` — δ decryption-failure: union bound PROVED (`Pr[fail]≤768·τ`), the counting-measure↔`winProb`
bridge (`winProb_eq_measureReal`) + Hoeffding's inequality (`winProb_abs_subgaussian_le`) WIRED, genuine CBD(η=2)
instantiation. **KEY FINDING (proven in Lean, `hoeffding_budget_exceeds_2800`): δ does NOT close via Hoeffding** —
the sub-Gaussian proxy dominates the variance (measured `47684 ≫ 2800`, 16× over; `Δv` alone `104²=10816`). The
correct closure needs a **variance-based Bernstein/sub-gamma** concentration (uncertain if Mathlib ships it) OR the
exact Kyber convolution δ — NOT Hoeffding. That is the precise named residual. `native_decide`-shrink (toward
kernel) + `[StarkSound]` discharge: not started.

## Seam 5 — deployment integrity: PARTIAL (crypto-subtree gauntlet GREEN)
**Crypto-subtree gauntlet PASSED on hbox (8524 jobs, exit 0)** — all linking modules (VerifyCoreEqSpec,
SignCoreSpec, DecapsCoreSpec, EncapsCoreSpec, FloorBridge, MlKemDelta, UcSignatureQuant, HybridThresholdQuant,
ProtocolSoundnessQuant + all deps) compose TOGETHER, not just piecewise. Remaining: fail-CLOSED install
(currently fail-open to the crate); route/allowlist the 23 FFI-free leaf binaries; wire the Crypto chain into
a CI target (it's outside default `lake build`); the FULL whole-tree gauntlet on `main` (crypto-subtree done,
whole-tree churn/OOM-blocked); land on `main`.

## Prior campaign (context)
The PQ-TCB deployment is DONE + live-proven: ML-DSA verify+sign, ML-KEM decaps+encaps all route through the
verified Lean cores on the node (crate out of the TCB, each proven in a running-binary hbox test).
See `docs/CRYPTO-TCB-OVERNIGHT.md`.
