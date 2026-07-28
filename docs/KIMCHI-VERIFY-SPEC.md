# KIMCHI-VERIFY-SPEC.md — what a Kimchi verifier checks, check-by-check (K5 scoping)

**Status:** research/spec only. No Lean, no build. Audience: Claude (review) + the K5 build.

> ## ⚑ CORRECTED 2026-07-27 — three protocol facts under an `[S]` tag were WRONG
>
> This document carried **three sourced-tagged protocol facts that its own pins refute**, and one of
> them had already propagated into a second document. A reader who built a verifier from the earlier
> version would have used the **wrong `shift_scalar` branch**, derived **different Fiat-Shamir
> challenges `v` and `u`**, and sized the **wrong SRS**. Evidence: `docs/AUDIT-IMPORTER-AND-DOCS.md`
> §4.1–4.3 (F-D1, F-D2, F-D3); every one re-verified first-hand against `~/dev/proof-systems`,
> `~/dev/mina` and `~/dev/mina-rust` during this pass.
>
> | # | Was | Is | Where |
> |---|---|---|---|
> | F-D1 | `Vesta::ScalarField = Fq`, `BaseField = Fp` ⇒ `shift_scalar` **else** branch | `vesta.rs:21-22`: `BaseField = Fq`, `ScalarField = Fp` ⇒ the **if** branch | §0 |
> | F-D2 | absorb `public_evals` **then** `ft_eval1` | `verifier.rs:381-392`: `ft_eval1` **first** | §C3 steps 16/17 |
> | F-D3 | "k = 16 for Mina's **wrap** SRS" | Wrap is **k = 15**; k = 16 is **Step** | §C9 |
>
> **The Lean is authoritative on F-D1, not this document.** `Dregg2/Circuit/Emit/PastaField.lean:120-132`
> has always named `pN` correctly ("the Pallas base / Vesta scalar prime"), and
> `KimchiVerify`/`KimchiRealProofGate` run over `ZMod pN`. The defect was confined to prose — do not
> "fix" the Lean toward the old text. `PICKLES-VERIFIER-SCOPE.md` §A (`:131,136`) and
> `MINA-KIMCHI-VERIFIER-PLAN.md` also always had it right; this file was the outlier.
>
> Corrections are marked **[CORRECTED 2026-07-27]** in place. Nothing in this pass was strengthened.

## Provenance (sourced vs reconstructed)

Everything marked **[S]** below was read directly from a local checkout of
o1-labs/proof-systems:

- Path: `~/dev/proof-systems`
- Commit: `36a8b510cd` — "Merge pull request #3564 from o1-labs/release/v0.7.0"
- Files cited: `kimchi/src/verifier.rs`, `kimchi/src/plonk_sponge.rs`,
  `kimchi/src/linearization.rs`, `kimchi/src/circuits/polynomials/permutation.rs`,
  `kimchi/src/circuits/polynomials/generic.rs`,
  `kimchi/src/circuits/constraints.rs`, `poly-commitment/src/ipa.rs`,
  `poly-commitment/src/commitment.rs`, `poseidon/src/sponge.rs`.

All line numbers are against that commit. Nothing material below is reconstructed;
the only reconstructed content is:

- **[R-est]** gate-count orders of magnitude (estimates, no source; reasoning shown);
- **[R-ctx]** Pickles/circuit-context remarks (how this verifier sits inside a
  circuit — not in the standalone Rust verifier);
- **[R-design]** v1 scoping decisions for our build (which knobs we freeze).

---

## 0. Where each field/curve lives (the Pasta 2-cycle) [S + R-ctx]

A Kimchi proof is verified over one curve `G` of the Pasta pair. For the proof
side we care about (the **Vesta** side — which is Mina's **Step** side, *not* the Wrap side;
**[CORRECTED 2026-07-27]** the earlier text called it *"the side Mina calls the 'wrap'/Vesta side"*,
and that mislabel is what produced the k = 15/16 error in §C9):

> **[CORRECTED 2026-07-27 — the field assignment in this section was INVERTED, under an `[S]` tag.]**
> The earlier text read: *"`G::ScalarField` = **Fq** (≈255-bit, modulus q), `G::BaseField` = **Fp**
> (modulus p < q)"*, and every downstream label in this section followed it. I opened the source
> myself: `~/dev/proof-systems/curves/src/pasta/curves/vesta.rs:21-22` is
> `type BaseField = Fq; type ScalarField = Fp;` — **exactly inverted** (`pallas.rs:21,23` is the
> mirror: `BaseField = Fp; ScalarField = Fq`). The pins the old text cited
> (`verifier.rs:111-116`, `ipa.rs:313-315`) are generic bounds and never said otherwise. **The
> consequence was not cosmetic: it produced the wrong `shift_scalar` branch below.**

- `G` = **Vesta**. `G::BaseField` = **Fq** (≈255-bit, modulus q), `G::ScalarField`
  = **Fp** (modulus **p < q**). [S — `curves/src/pasta/curves/vesta.rs:21-22`, read directly]
- The **Fq-sponge** (`EFqSponge`) absorbs Vesta **base**-field (**Fq**) elements — curve-point
  coordinates — and squeezes **Fp** scalars. It is instantiated with the *other*
  curve's Poseidon params: `EFqSponge::new(G::other_curve_sponge_params())`
  [S — `verifier.rs:159`]. (Kimchi's `Fq`/`Fr` sponge *names* are relative to the
  curve, not to the Pasta prime letters — a second source of the confusion above.)
- The **Fr-sponge** absorbs **Fp** elements directly (evaluations) and squeezes **Fp**
  [S — `verifier.rs:278-287`, `plonk_sponge.rs:16-32`].
- All polynomial evaluations, all challenges (β, γ, α, ζ, v, u, the IPA round
  challenges, c), and all scalar arithmetic in the checks below are in **Fp**.
- All commitments, MSMs, and the final IPA equation are **Vesta group operations**
  (point coordinates in **Fq**).
- Cross-check, independent of this doc: our own Lean names it correctly —
  `PastaField.lean:120-124` calls `pN` *"the Pallas base / Vesta scalar prime"*, and
  `KimchiVerify.lean:1201` states the scalar field is `Fp = ZMod pN` (Vesta::ScalarField).

**[R-ctx]** When this verifier is itself written as a circuit, the circuit's native
field is the *other* Pasta field. **[CORRECTED 2026-07-27]** The earlier text said *"the circuit
lives over Pallas's scalar field = **Fp**: Vesta point ops are then native-ish (affine coords in Fp),
while **all Fq arithmetic is non-native**."* Pallas's scalar field is **Fq**, not Fp, so that
sentence was self-refuting. Correctly: a circuit doing Vesta group ops natively lives over Vesta's
**base** field **Fq** — which *is* Pallas's scalar field — so Vesta point coordinates are native
(affine coords in Fq) and **all Fp arithmetic is non-native** and must be emulated (K1). This is the
standard Pickles arrangement; the standalone Rust verifier knows nothing of it. **It is also not
dregg's arrangement:** dregg's K5 emits over **BabyBear**, so *both* Pasta fields are non-native there
(9 limbs × 30 bits, `PastaField.lean:138-140`).

`shift_scalar` [S — `commitment.rs:273-288`, re-read this pass]: `n1 = ScalarField::MODULUS`,
`n2 = BaseField::MODULUS`, and the code branches
`if n1 < n2 { (x - (two_pow + one)) / two } else { x - two_pow }`. For `G = Vesta`,
`n1 = p < n2 = q`, so the **`if`** branch applies: **`x ↦ (x − 2^255 − 1) / 2`**
(`MODULUS_BIT_SIZE` of Vesta's ScalarField `Fp` = 255).
**[CORRECTED 2026-07-27 — the earlier text said *"scalar modulus (q) > base modulus (p), so the
`else` branch applies: `x ↦ x − 2^255`"*, which is the **Pallas** case. A verifier built from the old
line used the wrong shift.]** Independent confirmation from a third party's transcription:
`l-adic/snarky`'s `formal/pasta/Pasta/Shifted.lean` defines `shiftType1 s = (s − 2^numBits − 1)/2`
and documents it as *"the encoding of a scalar absorbed into the Fiat-Shamir transcript **when the
scalar modulus is below the base modulus** (`shift_scalar`, proof-systems
`poly-commitment/src/commitment.rs`)"* — i.e. exactly the Vesta case, exactly the `if` branch.
Used exactly once, when absorbing the combined inner product into the Fq-sponge [S — `ipa.rs:372`].

Challenge derivation [S — `poseidon/src/sponge.rs:190-226`]: a `ScalarChallenge`
is a raw 128-bit squeezed value (`CHALLENGE_LENGTH_IN_LIMBS` limbs,
`plonk_sponge.rs:47-49`); `to_field(endo_r)` maps it to **Fp** (**[CORRECTED 2026-07-27]** — read
"Fq" here before; same inversion) as `k = a·λ + b`
where a, b are accumulated over the 128 bits and λ = `endo_r` (the curve
endomorphism eigenvalue). β and γ are the **only** challenges used raw, without
the endo map [S — `verifier.rs:233,236`]; α, ζ, v, u and all IPA challenges go
through `to_field`.

---

## The checks, in verifier order

Call graph [S]: `verify` (`verifier.rs:1202-1227`) → `batch_verify_with_rng`
(`verifier.rs:1309-1373`) → per proof `to_batch` (`verifier.rs:781-1194`) →
`ProverProof::oracles` (`verifier.rs:126-634`) → finally
`OpeningProof::verify` = `SRS::verify` (`ipa.rs:1220-1233` → `ipa.rs:301-502`).

### C1 — Shape / length checks [S] — trivial, K1 only

- `proof.prev_challenges.len() == verifier_index.prev_challenges`
  (`verifier.rs:810-815`).
- `public_input.len() == verifier_index.public` (`verifier.rs:816-820`,
  re-checked at `834-839`).
- `chunk_size = ceil(domain.size / max_poly_size)` (`verifier.rs:823-830`).
- `check_proof_evals_len` (`verifier.rs:640-779`): every `PointEvaluations` in
  the proof (public, 15 w, z, 6 s, 15 coefficients, 6 selector evals, optional
  gate selectors, all lookup evals) has `zeta.len() == zeta_omega.len() ==
  chunk_size`.
- `t_comm.len() ≤ 7 * chunk_size` (`verifier.rs:259-266`).

*Gadget:* K1 (comparisons/lengths). *Cost:* O(1) gates. **[R-est]**

### C2 — Public-input commitment [S] — K2

`to_batch` commits to the **negated** public input polynomial in the Lagrange
basis of the domain (`verifier.rs:833-858`):

```
public_comm = mask_custom( MSM( srs.lagrange_basis(domain)[0..|public|], [-p_i] ), all-ones )
```

(empty public input ⇒ blinding commitment instead, `verifier.rs:844-845`.)

The same `public_comm` is absorbed into the transcript (C3) and enters the final
evaluation list (C8). *Gadget:* K2 (MSM over SRS Lagrange points, **Fp** scalars).
*Cost:* one MSM of |public| terms; |public| small (≤ ~hundreds) ⇒
**10⁴–10⁵** gates. **[R-est]**

### C3 — Fiat-Shamir transcript (the sponge order) [S] — K3

`ProverProof::oracles` (`verifier.rs:126-634`). Absorb/squeeze order, exactly:

**Fq-sponge phase** (Poseidon over **Fq**-state — Vesta's base field, the point coordinates —
squeezing **Fp**) **[CORRECTED 2026-07-27 — the two field letters here were swapped]**:

1. Absorb the verifier-index digest: `index.digest()` then `absorb_fq`
   (`verifier.rs:161-163`). The index digest binds the circuit being proven.
2. Absorb each `prev_challenges` commitment (recursion; empty for v1)
   (`verifier.rs:165-168`, `absorb_commitment` = `absorb_g(chunks)`,
   `commitment.rs:503-514`).
3. Absorb `public_comm` (`verifier.rs:170-171`).
4. Absorb the 15 witness commitments `w_comm` (`verifier.rs:173-177`).
5. *(lookup only)* absorb runtime-table commitment (`verifier.rs:179-195`).
6. *(lookup only)* squeeze **joint combiner j′**, map via endo to j
   (`verifier.rs:197-216`); absorb sorted commitments (`verifier.rs:218-229`).
7. Squeeze **β** (`verifier.rs:232-233`).
8. Squeeze **γ** (`verifier.rs:235-236`).
9. *(lookup only)* absorb lookup aggregation commitment (`verifier.rs:238-247`).
10. Absorb `z_comm` (permutation trace) (`verifier.rs:249-250`).
11. Squeeze **α′**, map endo → **α** (`verifier.rs:253-257`).
12. Check t_comm length (C1), absorb `t_comm` (`verifier.rs:259-269`).
13. Squeeze **ζ′**, map endo → **ζ** (`verifier.rs:272-276`).

**Fr-sponge phase** (Poseidon over **Fp**) **[CORRECTED 2026-07-27 — read "over Fq"]**:

> **[CORRECTED 2026-07-27 — steps 16 and 17 below were INVERTED, inside a block whose stated purpose
> is "Absorb/squeeze order, *exactly*".]** The earlier version numbered `public_evals`
> (`verifier.rs:391-392`) as step 16 and `ft_eval1` (`verifier.rs:381-382`) as step 17 — **its own
> line numbers refuted its own ordering.** I read the source: `ft_eval1` is absorbed **first**. For an
> order-sensitive sponge this changes the derived **`v` and `u`**, so a verifier built to the old
> numbering derives different challenges and rejects valid proofs. Verbatim from `verifier.rs`:
>
> ```
> 381  //~ 1. Absorb the unique evaluation of ft: $ft(\zeta\omega)$.
> 382  fr_sponge.absorb(&self.ft_eval1);
> ...
> 391  fr_sponge.absorb_multiple(&public_evals[0]);
> 392  fr_sponge.absorb_multiple(&public_evals[1]);
> 393  fr_sponge.absorb_evaluations(&self.evals);
> ```

14. `digest = fq_sponge.digest()`; fresh Fr-sponge; `fr_sponge.absorb(digest)`
    (`verifier.rs:278-287`).
15. Absorb a digest of all prev-challenges' scalar vectors, computed in a
    *separate* Fr-sponge (`verifier.rs:289-299`).
16. Absorb `ft_eval1` = ft(ζω) from the proof (`verifier.rs:381-382`). **(This is FIRST.)**
17. Compute `public_evals` (see C4) and absorb both `[ζ, ζω]` entries
    (`verifier.rs:391-392`). *(`public_evals` is computed earlier, at `verifier.rs:336-379`; it is
    the **absorb** that happens here, after `ft_eval1`.)*
18. Absorb **all proof evaluations** in the fixed order of
    `absorb_evaluations` (`plonk_sponge.rs:56-156`): z, generic_selector,
    poseidon_selector, complete_add, mul (VarBaseMul), emul (EndoMul),
    endomul_scalar, then w[0..15], coefficients[0..15], s[0..6], then optional
    gate selectors and all lookup evals if present. **Per polynomial, ζ first,
    then ζω** (`plonk_sponge.rs:152-155`). `public` is *not* absorbed here (done
    at step **17** — the "Mina annoyance", `plonk_sponge.rs:60`).
19. Squeeze **v′** (polyscale), endo → **v** (`verifier.rs:395-399`).
20. Squeeze **u′** (evalscale), endo → **u** (`verifier.rs:401-405`).

Later, inside the IPA check, the **same fq_sponge state continues**: absorb
`shift_scalar(combined_inner_product)`, squeeze a group element **U** via the
group map, then per round absorb (Lᵢ, Rᵢ) and squeeze challenge **uᵢ**
(`ipa.rs:372-383`, `ipa.rs:1261-1283`), absorb `delta`, squeeze **c**
(`ipa.rs:382-383`). See C9.

Derived values (`verifier.rs:301-308`): `zeta1 = ζⁿ`, `ζω = ζ·group_gen`,
`powers_of_eval_points_for_chunks = (ζ^max_poly_size, (ζω)^max_poly_size)`.
`powers_of_alpha` instantiated at α (`verifier.rs:328-330`).

*Gadget:* **K3** (PastaPoseidon sponge, both the Fq-sponge-over-**Fq**-state and
Fr-sponge-over-**Fp** flavors, plus the 128-bit challenge squeeze + endo map)
**[CORRECTED 2026-07-27 — field letters swapped here too]**.
**[2026-07-28 — the Fq-STATE flavour now EXISTS: `PastaPoseidonFq`, real `fq_kimchi` params from
`proof-systems@f6d958dc05`, KATs at both parities, and β/γ/α′/ζ′/digest of a real proof re-derived
end-to-end. Also: this section's absorb order (`ft_eval1` FIRST, corrected here 2026-07-27) had
NEVER been carried into the Lean `transcriptSchedule`, which still listed the public evaluations
first and omitted the prev-challenge digest entirely; both are fixed. The doc was right and the
code was not, for a day — the ORDER theorem was pinning a schedule this document had already
refuted.]**
*Cost:* ~25–35 commitments + ~40 eval pairs absorbed; each Poseidon permutation
(Kimchi params) is ~3×10² constraints ⇒ transcript total **10⁴–10⁵** gates.
**[R-est]**

### C4 — Public-input evaluation at ζ and ζω [S] — K1

If the proof carries no public evals and `chunk_size == 1`, the verifier
computes p(ζ), p(ζω) itself (`verifier.rs:336-379`):

```
p(ζ)  = (ζⁿ − 1) · n⁻¹ · Σᵢ ( −pᵢ · ωⁱ / (ζ − ωⁱ) )        (batch-inverted)
p(ζω) = ((ζω)ⁿ − 1) · n⁻¹ · Σᵢ ( −pᵢ · ωⁱ / (ζω − ωⁱ) )
```

(the code folds a single batch-inverted `zeta_minus_x` vector for both points,
`verifier.rs:338-346`.) If the proof *does* carry public evals they are used
verbatim (`verifier.rs:332-333`) — consistency is then discharged by the IPA
opening (C8/C9), not recomputation.

*Gadget:* K1 (**Fp** arithmetic, one batch inversion of 2·|public| elements).
*Cost:* **10³–10⁴** gates. **[R-est]**

### C5 — Permutation argument inside ft(ζ) [S] — K1

`ft_eval0` computation, `verifier.rs:411-490`. This is the copy-constraint
check folded into the quotient identity (evaluations, not polynomials, since
Maller's optimization moved everything to the ζ opening):

```
zkp(ζ)   = (ζ − ω^{n−3})(ζ − ω^{n−2})(ζ − ω^{n−1})           [zk_rows = 3]
           [permutation.rs:115-118; ZK_ROWS_BY_DEFAULT = 3, constraints.rs:801]
ft(ζ)    = z(ζω)·(w₆(ζ) + γ)·α⁰·zkp(ζ)·Π_{i<6}(β·σᵢ(ζ) + wᵢ(ζ) + γ)
         − p(ζ)                                              [public eval]
         − α⁰·zkp(ζ)·z(ζ)·Π_{i<7}(γ + β·ζ·shiftᵢ + wᵢ(ζ))
         + (1 − z(ζ))·(ζⁿ−1)·[α¹(ζ − ω^{n−3}) + α²(ζ − 1)] / ((ζ − ω^{n−3})(ζ − 1))
         − linearization.constant_term evaluated at ζ         [PolishToken]
```

Sourced terms, in order: numerator product `verifier.rs:429-438`, public
subtraction `verifier.rs:440-443`, denominator product `verifier.rs:445-453`,
the `(1−z)` boundary/zero-knowledge term `verifier.rs:455-462`, constant-term
subtraction `verifier.rs:479-487`. `index.w()` = `zk_w` = ω^{n−zk_rows}
(`permutation.rs:109-111`). Permutation consumes 3 powers of α
(`permutation.rs:74`, `CONSTRAINTS = 3`).

The **commitment side** of the same argument is `perm_scalars`
(`permutation.rs:392-430`): the scalar multiplying `sigma_comm[6]` in the f_comm
MSM is

```
− z(ζω)·β·α⁰·zkp(ζ)·Π_{i<6}(γ + β·σᵢ(ζ) + wᵢ(ζ))
```

i.e. the sigmas σ₀..σ₅ appear *inside ft(ζ)* as evaluations while σ₆ enters as a
commitment — the Maller split. The 7 `shiftᵢ` coset shifts are verifier-index
constants (`verifier.rs:448`).

*Gadget:* K1 (~50 **Fp** muls). *Cost:* **10²–10³** gates. **[R-est]**

### C6 — Gate constraints / the linearization at ζ [S] — K1 (+K2 for C7)

The gate constraints are not checked gate-by-gate; the prover index
pre-compiles them into a **linearization**: `constant_term` plus `index_terms`
(a map `Column → Vec<PolishToken>`), produced by `constraints_expr`
(`linearization.rs:45-…`), which sums the combined constraints of Poseidon,
VarBaseMul, CompleteAdd, EndosclMul, EndomulScalar and (feature-flagged)
RangeCheck0/1, ForeignFieldAdd/Mul, Xor, Rot, plus the generic gate
(`linearization.rs:64-68` and following; generic gate coefficients layout
`l, r, o, m, c` at `generic.rs:163-195`, constraint
`l·w₀ + r·w₁ + o·w₂ + m·w₀w₁ + c = 0`).

The verifier evaluates each token stream at ζ using the proof's claimed
evaluations (`PolishToken::evaluate`, called at `verifier.rs:479-487` for the
constant term and `verifier.rs:933-942` per index term). **What is compared:**
nothing directly — the constant term is subtracted inside ft(ζ) (C5) and the
index-term scalars multiply commitments in f_comm (C7); the equality is
ultimately `ft_comm == f_comm − t_comm·(ζⁿ−1)` enforced by the IPA opening
(C8/C9). This is the PLONK identity `f(X) = t(X)·Z_H(X)` checked at X = ζ
via the evaluation `ft(ζ)`.

*Gadget:* K1 — the PolishToken evaluator is a small stack machine over **Fp** ops;
its per-gate token streams are *verifier-index constants* baked into the circuit.
*Cost:* dominated by the Poseidon-gate constraint term (the only term involving
MDS/5-round unrolling): **10³–10⁴** gates total. **[R-est]**

### C7 — f_comm: the linearization commitment MSM [S] — K2

`verifier.rs:889-956`. The verifier computes

```
f_comm = perm_scalars · σ₆_comm  +  Σ_{(col, tokens) ∈ index_terms} PolishToken::evaluate(tokens, ζ, evals) · comm(col)
```

where `comm(col)` is resolved from proof/index via `Context::get_column`
(`verifier.rs:67-108`): witness/coefficient/sigma/z commitments, generic
selector, poseidon selector, the custom-gate commitments, and (feature-flagged)
optional gates + lookup columns. Final `PolyComm::multi_scalar_mul` at
`verifier.rs:954-955` — ~40–50 Vesta points, **Fp** scalars.

Then **Maller's optimization** gives the ft commitment (`verifier.rs:958-965`):

```
ft_comm = chunk(f_comm) − chunk(t_comm)·(ζⁿ − 1)
```

with chunking by ζ^{max_poly_size} (`verifier.rs:961-963`).

*Gadget:* K2 (Vesta MSM; non-native **Fp** scalars). *Cost:* ~45 non-native scalar
muls, endo-accelerated ⇒ **10⁵–10⁶** gates. **[R-est]** Second-most-expensive
check after the IPA.

### C8 — Combined evaluation & the batch assembly [S] — K1 (+K2 plumbing)

The scalar `combined_inner_product` (`commitment.rs:622-657`, formula at
`617-619`; call site `verifier.rs:492-606`):

```
cip = Σ_k polyscale^{k·n+i} · ( Σ_j evals[k][j][i] · evalscale^j )
```

over the ordered polynomial list: prev-challenge polys, public, ft (= [ft(ζ),
ft_eval1]), z, generic/poseidon/complete-add/varbasemul/endomul/endomul-scalar
selectors, w[0..15], coefficients[0..15], σ[0..6], optional gates, lookup
columns (`verifier.rs:502-603`). Chunked evaluations are first combined with
powers of ζ^{max_poly_size} (`evals.combine`, `verifier.rs:409`, `878-881`).

**This is the "all-evaluations consistency" check.** The proof supplies raw
scalars as evaluations; the verifier never re-evaluates any polynomial. The
claimed evals are bound to the commitments because (a) they are all absorbed
into the transcript before v, u are squeezed (C3), and (b) `to_batch` assembles
`evaluations: Vec<Evaluation>` pairing each commitment (chunked) with its
claimed [ζ, ζω] evaluations (`verifier.rs:967-1181`, including `ft_comm` paired
with `[ft_eval0, ft_eval1]` at `verifier.rs:984-987`), and the IPA opening
proves `Σ polyscaleⁱ·fᵢ(xⱼ)` aggregated by evalscale equals `cip`. If any
claimed eval were inconsistent with its commitment, the final MSM (C9) fails.

*Gadget:* K1 for the scalar combination (pure **Fp**: ~10³ muls ⇒ **10³–10⁴**
gates **[R-est]**); the commitment pairing is data plumbing for K4.

### C9 — The IPA opening check [S] — K4 (the big one)

`SRS::verify` (`ipa.rs:301-502`; the check equation is documented at
`ipa.rs:317-336`). Per proof in the batch:

1. Absorb `shift_scalar(cip)` into the fq-sponge; squeeze field element t and
   map to a group element **U** via `group_map` (`ipa.rs:372-378`).
2. Per round i = 0..k−1 (k = log₂(SRS depth)): absorb Lᵢ, Rᵢ; squeeze
   challenge uᵢ via endo (`ipa.rs:1261-1283`, `squeeze_challenge`
   `commitment.rs:490-501`). Compute all uᵢ⁻¹ by batch inversion
   (`ipa.rs:1276-1280`).
3. Absorb `delta`; squeeze **c** via endo (`ipa.rs:382-383`).
4. `b0 = Σ_j evalscale^j · b(x_j)` over the evaluation points [ζ, ζω], where
   `b(X) = Π_{i<k} (1 + u_{k−1−i}·X^{2^i})` (`b_poly`,
   `commitment.rs:426-436`; call `ipa.rs:389-398`).
5. `s = b_poly_coefficients(chal)` — the 2^k coefficients, sᵢ = Π_{j: bit j
   of i set} u_{k−j} (`commitment.rs:464-476`; call `ipa.rs:402`).
6. Assemble one giant MSM and check it equals the identity (`ipa.rs:404-501`):

```
0 ==  (−z₁·rand)·sg  −  sg_rand·sg  +  ⟨sg_rand·s, G_SRS⟩        [sg correctness]
    − (rand·z₂)·H
    − (rand·z₁·b0)·U
    + Σᵢ rand·c·(uᵢ⁻¹·Lᵢ + uᵢ·Rᵢ)                                [round folding]
    + Σⱼ rand·c·polyscaleʲ·commⱼ                                 [combine_commitments,
                                                                    commitment.rs:724-744]
    + (rand·c·cip)·U
    + rand·delta
```

Final check: `msm(points, scalars) == G::zero()` (`ipa.rs:501`). The two
randomizers `rand_base`, `sg_rand_base` are sampled from RNG after everything
else is fixed (`ipa.rs:355-360`) — they bind the per-proof sub-equations so a
cheater cannot trade error between them.

*Gadget:* **K4** (PastaIPA / ScalarMul). Contains:
- k·2 challenge-derived scalar muls on (Lᵢ, Rᵢ) — k = log₂(SRS size);
- the **s-vector MSM `⟨s, G⟩` with 2^k terms** — computing `s` itself
  is 2^k Fp muls, and the MSM is 2^k non-native scalar muls;
- ~50 commitment terms (C8 list) + constant overhead.

> **[CORRECTED 2026-07-27 — a Step figure was attached to the Wrap side.]** The earlier text read
> *"**k = 16** for Mina's **wrap** SRS ⇒ 32 terms."* **Wrap is k = 15; k = 16 is Step.** Sourced, all
> re-read this pass:
> - `~/dev/mina/src/lib/crypto/kimchi_backend/pasta/basic/kimchi_pasta_basic.ml:16-17` — `module Wrap = Nat.N15` / `module Step = Nat.N16` (these are the `Rounds` modules).
> - `~/dev/mina-rust/crates/ledger/src/proofs/mod.rs:33-34` — `BACKEND_TICK_ROUNDS_N = 16` (Step/tick), `BACKEND_TOCK_ROUNDS_N = 15` (Wrap/tock); wired at `field.rs:105,124`.
> - `field.rs:106,127` — `Fp::SRS_DEPTH = 32768`, `Fq::SRS_DEPTH = 65536`, consumed generically as `SRS::<F::OtherCurve>::create(F::Scalar::SRS_DEPTH)` (`~/dev/mina-rust/crates/ledger/src/verifier/mod.rs:42`).
> - `proof-systems kimchi/src/proof.rs:437-438` — *"`k = 15` for a domain of size `2^15`, giving an MSM of 32768 points."*
>
> Resolving those together: **Step is Fp-native ⇒ its proof is committed on Vesta ⇒ k = 16, SRS 2^16 = 65536,
> 32 (L,R) terms. Wrap is Fq-native ⇒ committed on Pallas ⇒ k = 15, SRS 2^15 = 32768, 30 terms.**
> Since this document's subject is the **Vesta** side, its **numbers (k = 16, 65536) were right and only
> the word "wrap" was wrong** — but the mislabel is exactly the kind that propagates, and
> `MINA-DREGG-ZKAPP-BRIDGE.md` already stated Step 2^16 / Wrap 2^15 correctly, so the two docs
> disagreed and this one was the outlier. **No gate-count band below changes.**

*Cost:* naive **10⁸–10⁹** gates; with endo split + windowing + batching,
**10⁷–10⁸**. **[R-est]** **This is the hardest and most expensive check by two
orders of magnitude** — it is exactly what Pickles defers into the next
recursion step (the `sg`/`⟨s,G⟩` split exists so the 2^k MSM can be deferred;
see the comments at `ipa.rs:335-336` and `commitment.rs:457-460`).

### C10 (optional) — Plookup [S, present but feature-gated]

Lookups are **off** when `verifier_index.lookup_index` is `None`; every lookup
step above is behind that flag (transcript: `verifier.rs:179-247`; eval list:
`verifier.rs:1044-1181`; table commitment recombination via `combine_table` at
`verifier.rs:1087-1108`). The lookup argument contributes additional terms to
the linearization (aggreg/sorted/table identities, joint combiner j).
**Recommendation: out of scope for K5 v1** — a circuit whose verifier index has
no lookup features needs none of this. Flag as advanced/follow-up.

---

## Check → gadget summary

| # | Check | Source | Gadget | OOM gates [R-est] |
|---|-------|--------|--------|-------------------|
| C1 | Shape/length checks | verifier.rs:640-779, 810-831 | K1 | O(1) |
| C2 | Public-input commitment | verifier.rs:833-858 | K2 | 10⁴–10⁵ |
| C3 | Fiat-Shamir transcript (β γ α ζ v u) | verifier.rs:126-405; plonk_sponge.rs:56-156 | K3 | 10⁴–10⁵ |
| C4 | Public eval at ζ, ζω | verifier.rs:332-379 | K1 | 10³–10⁴ |
| C5 | Permutation terms of ft(ζ) + perm_scalars | verifier.rs:411-462; permutation.rs:392-430 | K1 | 10²–10³ |
| C6 | Linearization constant+index terms at ζ | verifier.rs:464-487, 933-942; linearization.rs | K1 | 10³–10⁴ |
| C7 | f_comm MSM + ft_comm (Maller) | verifier.rs:889-965 | K2 | 10⁵–10⁶ |
| C8 | combined_inner_product + eval pairing | verifier.rs:492-606, 967-1181; commitment.rs:622-657 | K1 | 10³–10⁴ |
| C9 | IPA opening (rounds + ⟨s,G⟩ + b_poly + MSM=0) | ipa.rs:301-502; commitment.rs:426-476 | K4 | 10⁷–10⁸ (2^k-MSM dominates) |
| C10 | Plookup (optional) | verifier.rs:179-247, 1044-1181 | — | defer |

---

## K5 build plan (v1: one Kimchi proof, no Pickles recursion) [R-design]

**Freeze for v1:** single proof (no batching); ~~`prev_challenges = 0`~~ **[RETIRED 2026-07-28 —
`prev_challenges` is now a PARAMETER checked against the verifier index (`shapeOkRec`), its
commitments are in the phase-1 transcript, its digest is in the phase-2 one, and its b-poly
evaluations at the head of the C8 list are RECOMPUTED (`prevChalFoldOk`); run on a real
`prev_challenges = 2` proof in `KimchiRecursionGate`]**; no lookups
(`lookup_index = None`); `chunk_size = 1` (domain ≤ SRS, the common Mina case);
`zk_rows = 3`; public input present and small. Proof side: Vesta (**Fp** scalars);
circuit side: **Fq**-native with non-native **Fp** (K1).

**Build order** (each stage testable against the Rust verifier's intermediate
values):

1. **Transcript replay (C3)** — K3. Everything downstream consumes β, γ, α, ζ,
   v, u. First milestone: reproduce all challenges + `public_evals` + the
   fq-sponge state handoff to the IPA from a real proof fixture. Cheap and
   catches 90% of encoding bugs (absorb order, ζ-before-ζω, endo map).
2. **Scalar checks (C4, C5, C6, C8-scalar)** — K1. Pure **Fp** arithmetic:
   public evals, ft_eval0, PolishToken evaluation, combined_inner_product.
   No curve ops; KAT against Rust intermediates.
3. **Commitment geometry (C2, C7, C8-pairing)** — K2. public_comm, f_comm MSM,
   ft_comm; assemble the `Evaluation` list. Second milestone: the assembled
   `BatchEvaluationProof` matches Rust's, field-for-field.
4. **IPA (C9)** — K4, in this order: per-round challenges uᵢ, uᵢ⁻¹ →
   `b_poly`/`b0` → `b_poly_coefficients`/s-vector (2^k **Fp** muls) → the final
   batched MSM == 0. Third milestone: accept/reject matches
   `OpeningProof::verify` on positive and negative fixtures.

**Randomizers [R-design]:** `rand_base`/`sg_rand_base` come from an RNG in Rust
(`ipa.rs:355-360`). In-circuit there is no RNG; for a deterministic verifier
derive them by Fiat-Shamir (squeeze the fq-sponge after `delta` is absorbed).
This preserves the binding property (sampled after all proof data is fixed) and
must be documented as a deliberate deviation from `ipa.rs`.

**Hardest / most expensive:** **C9's `⟨s, G⟩` MSM — 2^k = 65536 non-native
Vesta scalar muls** (plus the 2^k-mul s-vector computation). **[CORRECTED 2026-07-27 — the figure
stands, its label did not: 65536 is the Vesta/**Step** SRS, not the Wrap SRS, which is 32768. See
§C9.]** Nothing else is
within two orders of magnitude. If v1 must shrink, the honest lever is the
Pickles one: defer the s-vector MSM out of the circuit (the protocol already
isolates it as the `sg` term) — but that *is* recursion, so for v1 budget for
the full MSM with endo+windowing and measure before optimizing further.
