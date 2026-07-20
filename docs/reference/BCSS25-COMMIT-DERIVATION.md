# BCSS25 into the BCIKS20 FRI commit analysis: a public derivation and constant audit

Date: 2026-07-16

> **Provenance & check.** This derivation was drafted by codex and then CHECKED line-by-line against
> the primary sources by the driving lane. Verified independently: (a) BCSS25 Lemma 3.1's degree
> formulas `D_X=(m+½)√(nk)`, `D_Y=(m+½)√(n/k)`, `D_Z=⅓(m+½)²(n/k)` (§2.2 matches, and `D_Z` is
> `n`-independent — the improvement); (b) the §2.4 self-consistency check — plugging the reconstructed
> bookkeeping into the unweighted target `T=d(γn+1)` reproduces BCSS25 Theorem 4.2's published bound
> EXACTLY, pinning all factors; (c) BCIKS20 §7.1–7.2 (Lemmas 7.5/7.6) and Lemma 8.2's weight recursion,
> read in full — the weighting is intrinsic (`ε_Q = E[µ⁽ʳ⁾]`) and the transfer needs only
> co-curvilinearity, which BCSS25 §3.2 Step 4 supplies. The load-bearing half (Lemma 7.5) is mechanized
> in `metatheory/Dregg2/Circuit/FriWeightingTransfer.lean`. The one soft spot in this document is §6.4's
> reconciliation of the repository's "61" anchor (the ledger uses a FIXED `bciksM` where this document
> optimizes over `m`, so its "63.976 at the wrap / 61 at a ρ=1/8 row" attribution should be read as
> approximate); it does not affect the qualitative verdict. Companion:
> `FRI-SOUNDNESS-FRONTIER-RESEARCH.md` §8.
>
> ⚑ **These ε_C figures (61, 61.779, 63.976, …) are INFORMAL analytical outputs of the BCIKS20
> formula, NOT proven soundness bounds against an adversary.** The theorem-backed deployed
> commit-phase reading is **51 bits** at the deployed `2²²` domain
> (`FriDeployedHeightPairing.deployed_wrap_commitBits`); the "61" anchor this section reconciles is
> a config/height MISPAIRING and is refuted (`deployed_wrap_is_not_61` — it is a true reading of
> `recursionConfig` at `2^19`, not of the deployed wrap). Use `51` as the deployed number; read
> everything below as the derivation of the FORMULA those readings come from, not as a bound.

## Executive verdict

There are two different claims that must not be conflated.

1. **BCSS25 Corollary 4.4 as stated, with unrestricted real weights, does not follow from BCSS25's public co-curvilinearity argument plus BCIKS20 Lemmas 7.5--7.6 alone.** Lemma 7.5 loses a positive amount, and Lemma 7.6 removes that loss only when the weights lie on a known rational grid. The unpublished-set theorem, BCSS25 Theorem 4.3, is genuinely doing extra work for the unrestricted-weight corollary.

2. **The weighted statement needed in BCIKS20's FRI proof does follow from the public ingredients.** The FRI weights have exactly the common-denominator structure required by BCIKS20 Lemma 7.6. Feeding the *same chosen proximate codewords* into BCSS25 Section 3.2's public co-curvilinearity argument, and then applying Lemmas 7.5--7.6, gives a linear-in-domain exceptional-set bound. No arbitrary family of prescribed agreement sets is needed in Lemma 8.2. Thus the `[Sta25]` dependency is eliminable for the FRI application, though not for Corollary 4.4 in its full stated generality.

The quantitative result for a degree-`d` curve on a local domain of size `n`, with weight denominator `W`, is the following. Put

\[
 a=b+\tfrac12,\qquad
 C_b=\frac{2a^5}{3\rho^{3/2}},\qquad
 Y_b=\frac{a}{\sqrt\rho}.
\]

If `S` is the set of challenges having weighted agreement at least `alpha`, and the BCSS interpolation parameter `b` is valid for `gamma=1-alpha`, then the public proof gives the sufficient bound

\[
 \boxed{
 |S|>d\left(C_b n+Y_b(Wn+1)\right).
 }
 \tag{WCA}
\]

Under this condition there are codewords `v_0,...,v_d` whose joint agreement domain with the input words has weight at least `alpha`. The exact coefficient of `n` is

\[
 \boxed{
 d\left(\frac{2(b+1/2)^5}{3\rho^{3/2}}
       +\frac{(b+1/2)W}{\sqrt\rho}\right),
 }
\]

with additive constant `d(b+1/2)/sqrt(rho)`.

For the FRI round from `D^(i)` to `D^(i+1)`, `W |D^(i+1)|=|D^(0)|=:N`. Hence (WCA) becomes

\[
 |S_i|>d_i\left(C_{b_i}|D^{(i+1)}|+Y_{b_i}(N+1)\right),
 \]

which is linear in the initial domain size `N`. Both the former proximity-gap contribution and the denominator/weighting contribution are linear.

With the public constants, the BCIKS20 round structure, the exact fold schedules described below, and the problem's field/rate convention, the optimized ethSTARK-equation-(20) lower bounds are:

| configuration | new `-log2 eps_C` | query/PoW column | new composed `lambda` | optimized BCIKS20 `lambda` | gain |
|---|---:|---:|---:|---:|---:|
| wrap: `N=2^19`, `rho=1/64`, arity 8 | 72.00005 | 72.03810 | **71.00005** | 63.97608 | **+7.02397** |
| leaf: `N=2^12`, `rho=1/64`, arity 2 | 72.87202 | 72.76471 | **71.76471** | 70.10882 | **+1.65589** |
| outer: `N=2^18`, `rho=1/8`, arity 2 | 72.56576 | 72.44342 | **71.44342** | 65.91154 | **+5.53188** |

Here `lambda=min{-log2 eps_C, zeta-s log2(alpha)}-1`. The low-rate linear improvement survives, but the *composed* gain is much smaller than 17 bits: the query/PoW column caps the result near 72 bits, and the arity-8 public curve theorem uses a larger interpolation parameter than the binary-line theorem. The `rho^{-3/2}` factor is large, but it is not by itself the explanation: it occurs in both the old and new leading constants.

There is also a configuration-label mismatch in the premise that must be recorded rather than hidden. The supplied row `N=2^19, rho=1/64, s=19, zeta=16` does **not** evaluate to 61 bits under the displayed BCIKS20 formula; optimized over the analysis parameter it gives 63.976 bits after equation (20). The repository's current “61” anchor comes from a different row: the arity-2 recursion configuration at `rho=1/8`, `s=38`, `zeta=14`, evaluated at the fixed ledger parameter `m=7`, has `-log2 eps_C=61.779`. Section 7 below gives both comparisons.

## 1. Sources and notation

The public sources used here are:

- Ben-Sasson, Carmon, Haboeck, Kopparty, Saraf, *On Proximity Gaps for Reed--Solomon Codes*, ECCC TR25-169, especially Lemma 3.1, Section 3.2, Theorem 4.2, Theorem 4.3, and Corollary 4.4: [report page](https://eccc.weizmann.ac.il/report/2025/169/) and [PDF](https://eccc.weizmann.ac.il/report/2025/169/download).
- Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed--Solomon Codes*, revision 3 of ECCC TR20-083 / eprint 2020/654, especially Section 7.2, Lemmas 7.5--7.6, Lemma 8.2, and Theorem 8.3: [revision-3 PDF](https://eccc.weizmann.ac.il/report/2020/083/revision/3/download).
- StarkWare, *ethSTARK Documentation, Version 1.2*, equation (20): [eprint 2021/582](https://eprint.iacr.org/2021/582.pdf).

I use distinct letters because both papers overload `m`, `M`, and `l`.

- `n=|D|` is the local RS block length.
- `rho` is BCSS25's slightly reduced rate, as stipulated in the problem.
- `d` is the degree of the challenge curve. An FRI fold of ratio `L` produces `d=L-1`.
- `b` is the integer interpolation/multiplicity parameter called `m` in BCSS25.
- `h` is the BCIKS20/FRI analysis parameter in
  \[
  \alpha_h=\sqrt\rho\left(1+\frac1{2h}\right).
  \]
- `W` is the common denominator of the weight values in BCIKS20 Lemma 7.6.
- `N=|D^(0)|` is the first, largest FRI domain.
- `L_i=|D^(i)|/|D^(i+1)|`, `d_i=L_i-1`, and
  \[
  P_i=\prod_{j=0}^i L_j,\qquad |D^{(i+1)}|=N/P_i.
  \]

All weights use BCIKS20's normalization

\[
 \mu(A)=\frac1n\sum_{x\in A}\mu(x),\qquad 0\leq \mu(x)\leq1.
\]

Equivalently, BCSS25 writes the atom mass as `w(x)/n`. Thus `mu` is dominated pointwise by uniform counting measure:

\[
 \mu(A)\leq |A|/n.
 \tag{1.1}
\]

## 2. What the public BCSS proof actually supplies

### 2.1 Choosing the proximate codewords

Let

\[
 u_z=u_0+zu_1+\cdots+z^d u_d.
\]

Suppose that for every `z` in a challenge set `S` we have chosen a codeword `P_z in C` with

\[
 \operatorname{agree}_\mu(u_z,P_z)\geq\alpha=1-\gamma.
 \tag{2.1}
\]

By (1.1), the *same* chosen codeword satisfies ordinary agreement at least `alpha`:

\[
 \frac{|\{x:u_z(x)=P_z(x)\}|}{n}
 \geq \operatorname{agree}_\mu(u_z,P_z)
 \geq 1-\gamma.
 \tag{2.2}
\]

Consequently `Delta(u_z,P_z)<=gamma`, so the chosen family `(P_z)_{z in S}` is a valid input to the Guruswami--Sudan argument in BCSS25 Section 3.

The word “chosen” is load-bearing. Applying only the *statement* of Theorem 4.2 would give some correlated codeword tuple, but would not say that its curve passes through the particular codewords witnessing (2.1). Section 3.2, Step 4 is stronger: its proof starts with an arbitrary selected proximate `P_z` for every `z`, and produces a subset `S'` on which those same `P_z` are co-curvilinear.

### 2.2 Interpolant degrees

Put `a=b+1/2`. BCSS25 Lemma 3.1 gives, for a line,

\[
 \begin{aligned}
 D_X&=a\sqrt{nk}=a n\sqrt\rho,\\
 D_Y&=a\sqrt{n/k}=\frac{a}{\sqrt\rho},\\
 D_Z&=\frac13a^2\frac nk=\frac{a^2}{3\rho}.
 \end{aligned}
 \tag{2.3}
\]

The key improvement is visible here: `D_Z` is independent of `n`. In BCIKS20 the effective `Z`-degree was linear in `n`, and it is that factor that made the exception count quadratic.

For a degree-`d` curve, BCSS25 Section 4.1 gives the same construction with `(0,d,1)`-weighted `Z`-degree. The required bound scales by `d`; equivalently, for the bookkeeping below one may take

\[
 D_Z^{\mathrm{curve}}=dD_Z=\frac{d a^2}{3\rho}.
 \tag{2.4}
\]

For the binary case `d=1`, BCSS25 Theorem 1.5 permits

\[
 b\geq \left\lceil\frac{\sqrt\rho}{2(1-\sqrt\rho-\gamma)}\right\rceil.
 \tag{2.5}
\]

The general curve theorem, Theorem 4.2, is stated with the more conservative condition

\[
 b\geq \left\lceil\frac{\sqrt\rho}{1-\sqrt\rho-\gamma}\right\rceil.
 \tag{2.6}
\]

This factor of two matters numerically. Retaining BCIKS20's

\[
 \alpha_h=\sqrt\rho(1+1/(2h)),\qquad
 1-\sqrt\rho-\gamma=\alpha_h-\sqrt\rho=\frac{\sqrt\rho}{2h},
 \tag{2.7}
\]

allows `b=h` for a line by (2.5), but requires `b=2h` for a general curve by (2.6). A calculation that uses `b=h` for the degree-7 wrap is not an instantiation of the public Theorem 4.2.

### 2.3 Factor bookkeeping and the size of the co-curvilinear subset

BCSS25 factors the interpolant and focuses on pairs `(R_i,H_ij)`. Write

\[
 q_{ij}=D^{(R)}_{Y,i}D^{(H)}_{Y,ij}D^{(R)}_{Z,i}
 \]

and let `S_ij` be the challenges assigned to that pair. Section 3.2, Step 4 says that if

\[
 |S_{ij}|>2D_Xq_{ij},
 \tag{2.8}
\]

then the Hensel-lift argument produces a polynomial curve

\[
 P(X,Z)=v_0(X)+Zv_1(X)+\cdots+Z^d v_d(X)
 \]

and a subset `S' subseteq S_ij` such that

\[
 P_z(X)=P(X,z)\quad\text{for all }z\in S',
 \tag{2.9}
\]

with

\[
 |S'|\geq |S_{ij}|-q_{ij}.
 \tag{2.10}
\]

The displayed lower bound `(2D_X-1)q_ij` in BCSS25 is obtained by combining (2.8) and (2.10). For weighting, however, it is better to keep the unsimplified form (2.10), because it lets us demand an arbitrary target size `T` for `S'`.

The factor degrees obey the identities used explicitly in BCSS25 Section 3.2:

\[
 \sum_jD^{(H)}_{Y,ij}=D^{(R)}_{Y,i},\qquad
 \sum_iD^{(R)}_{Y,i}=D_Y,
 \tag{2.11}
\]

and, after separating content roots,

\[
 \sum_{i,j}q_{ij}\leq D_Y^2D_Z^{\mathrm{curve}}.
 \tag{2.12}
\]

The number of nonconstant factor pairs is at most `D_Y`. Content roots contribute at most their `Z`-degree and are absorbed by the same final upper bound, exactly as in the last display of BCSS25 Section 3.2.

Fix a desired lower bound `T` on `|S'|`. If no pair simultaneously satisfies (2.8) and

\[
 |S_{ij}|-q_{ij}\geq T,
 \tag{2.13}
\]

then every pair satisfies

\[
 |S_{ij}|\leq 2D_Xq_{ij}+T.
\]

Summing this inequality and using (2.11)--(2.12) gives

\[
 |S|\leq 2D_XD_Y^2D_Z^{\mathrm{curve}}+TD_Y.
 \tag{2.14}
\]

Taking the contrapositive, a sufficient condition for a co-curvilinear subset of size at least `T` is

\[
 |S|>2D_XD_Y^2D_Z^{\mathrm{curve}}+TD_Y.
 \tag{2.15}
\]

Substituting (2.3)--(2.4),

\[
 2D_XD_Y^2D_Z^{\mathrm{curve}}
 =d\,\frac{2a^5}{3\rho^{3/2}}n=dC_b n.
 \tag{2.16}
\]

This is the exact linear replacement for the former quadratic term.

### 2.4 Check against BCSS25 Theorem 4.2

For ordinary correlated agreement of a degree-`d` curve, the final collinearity/curvilinearity step needs

\[
 T=d(\gamma n+1).
\]

Putting this target into (2.15) yields

\[
 \begin{aligned}
 |S|&>d\left(
 \frac{2a^5}{3\rho^{3/2}}n
 +\frac a{\sqrt\rho}(\gamma n+1)
 \right)\\
 &=d\left(
 \frac{2a^5+3a\gamma\rho}{3\rho^{3/2}}n
 +\frac a{\sqrt\rho}
 \right),
 \end{aligned}
 \tag{2.17}
\]

which is exactly BCSS25 Theorem 4.2. This check pins all factors `2`, `3`, `d`, and `rho` in the weighted generalization below.

## 3. Weighting transfer: what closes and what does not

### 3.1 BCIKS20 Lemma 7.5 applies to the selected proximates

From (2.9), define

\[
 w(x,z)=\sum_{j=0}^d z^ju_j(x),\qquad
 \widetilde w(x,z)=\sum_{j=0}^d z^jv_j(x).
\]

For every `z in S'`, `widetilde w(.,z)=P_z`, not merely some other nearby codeword. Therefore (2.1) gives

\[
 \operatorname{agree}_\mu(w(\cdot,z),\widetilde w(\cdot,z))\geq\alpha
 \quad(z\in S').
 \tag{3.1}
\]

Let

\[
 D'=\{x:(u_0(x),\ldots,u_d(x))=(v_0(x),\ldots,v_d(x))\}.
\]

For a fixed `x`, the difference `w(x,Z)-widetilde w(x,Z)` has degree at most `d`. If it vanishes on more than `d` points, it vanishes identically. Double counting the pairs `(x,z)` satisfying equality is exactly BCIKS20 Lemma 7.5 and yields

\[
 \mu(D')>\alpha-\frac d{|S'|-d}.
 \tag{3.2}
\]

This step needs no prescribed family of agreement sets and no `[Sta25]` result.

### 3.2 Denominator rounding removes the loss for FRI

Assume each weight value has denominator dividing `W`. Because of the outer `1/n` normalization, every possible weighted set size lies on the grid

\[
 \frac1{Wn}\mathbb Z.
\]

BCIKS20 Lemma 7.6 observes that if

\[
 |S'|\geq Wnd+d=d(Wn+1),
 \tag{3.3}
\]

then

\[
 \frac d{|S'|-d}\leq\frac1{Wn}.
\]

After rounding `alpha` up to the next grid point, (3.2) forces

\[
 \mu(D')\geq\alpha.
 \tag{3.4}
\]

Set `T=d(Wn+1)` in (2.15). Equations (2.16) and (3.3) give the promised weighted exceptional-set bound

\[
 \boxed{
 |S|>d\left(
 \frac{2(b+1/2)^5}{3\rho^{3/2}}n
 +\frac{b+1/2}{\sqrt\rho}(Wn+1)
 \right).
 }
 \tag{3.5}
\]

Expanding the right-hand side, the exact coefficient in front of `n` is

\[
 \boxed{
 d\left(
 \frac{2(b+1/2)^5}{3\rho^{3/2}}
 +\frac{(b+1/2)W}{\sqrt\rho}
 \right),
 }
 \tag{3.6}
\]

and the additive constant is `d(b+1/2)/sqrt(rho)`.

This is a slightly sharper use of the public Section 3.2 bookkeeping than the older “first obtain `|S'|>|S|/(2D_Y)`, then demand it be large” route. The latter would insert `2D_Y` in the weighting term. Equation (3.5) follows directly from the same summed-factor argument BCSS25 uses to save its extra `D_Y`, with the final target `gamma n+1` replaced by `Wnd+d`.

### 3.3 Why this does not prove unrestricted Corollary 4.4

BCSS25 Corollary 4.4 allows arbitrary real `w(x) in [0,1]`. For such weights, the set of possible values `mu(A)` need not have any positive grid spacing. Lemma 7.5 gives only (3.2), whose loss is strictly positive for every finite `S'`. Lemma 7.6 cannot be invoked with a finite common denominator.

Uniform domination does not fix this. It gives ordinary density of each chosen agreement set, but a set of large cardinality can carry small `mu`-mass when the weight is concentrated elsewhere. Nor can one take a limit in the denominator while keeping (3.3): the required number of challenges grows with `W`, while the field and `S'` are fixed.

Thus the public ingredients prove:

- a lossy arbitrary-real-weight statement with conclusion (3.2); and
- an exact denominator-bounded statement with conclusion (3.4) and exception bound (3.5).

They do **not** prove Corollary 4.4 verbatim for all real weights. Theorem 4.3's stronger “one of the prescribed agreement sets itself supports the correlated tuple” conclusion removes the loss without a denominator, which is genuinely stronger.

For FRI this distinction is harmless, because its weights are on precisely the denominator grid used in (3.3).

## 4. The FRI denominator check

In BCIKS20 Lemma 8.2, at round `i` the weight on `D^(i+1)` is the accumulated acceptance probability of a uniformly selected descendant in `D^(0)`. Therefore its values have denominator

\[
 W_i=\frac{N}{|D^{(i+1)}|}.
 \tag{4.1}
\]

Consequently

\[
 W_i|D^{(i+1)}|=N,
 \]

and the Lemma 7.6 target is

\[
 |S'_i|\geq d_i(N+1).
 \tag{4.2}
\]

Equation (3.5) becomes

\[
 \boxed{
 |S_i|>d_i\left(
 C_{b_i}|D^{(i+1)}|+Y_{b_i}(N+1)
 \right).
 }
 \tag{4.3}
\]

This answers the quantitative bookkeeping question directly. The improved `Z`-degree remains `O(1)` in the local block length, and the factor-sum argument produces a co-curvilinear subset large enough for Lemma 7.6 after adding only the second, linear term in (4.3). Since `|D^(i+1)|<=N`, every round's exception count is `O(N)`. The field-size hypothesis is useful, not vacuous, at the deployed parameters: the largest optimized per-event thresholds below are about `10^15`, while

\[
 |F|=p^4=16428751811598850197311699254593454081\approx2^{123.62756}.
\]

## 5. Reassembling BCIKS20 Lemma 8.2

### 5.1 Initial affine-combination event

BCIKS20's event `E^(0)` concerns the random affine combination of the batched input words and uses uniform weights. The standard public line-to-affine-space reduction in BCIKS20 Section 6.3 gives the same exception probability as a line. With

\[
 \alpha_h=\sqrt\rho(1+1/(2h)),\qquad \gamma_h=1-\alpha_h,
\]

the sharper line parameter is `b=h`, and the public BCSS bound is

\[
 B_0=C_hN+Y_h(\gamma_hN+1).
 \tag{5.1}
\]

This line-to-affine reduction is elementary and public; it is not the `[Sta25]` arbitrary-agreement-set theorem.

### 5.2 Per-round weighted events

For round `i`, use (4.3). To retain BCIKS20's `alpha_h`:

- if `d_i=1` (a binary fold), the public line theorem permits `b_i=h`;
- for a general curve, BCSS25 Theorem 4.2 as publicly stated requires `b_i=2h` by (2.6)--(2.7).

The exact public commit-phase error obtained by the BCIKS20 union bound is therefore

\[
 \boxed{
 \varepsilon_C^{\rm lin}(h)=\frac1{|F|}\left[
 C_hN+Y_h(\gamma_hN+1)
 +\sum_{i=0}^{r-1}d_i
 \left(C_{b_i}\frac N{P_i}+Y_{b_i}(N+1)\right)
 \right].
 }
 \tag{5.2}
\]

This is not a heuristic substitution into the displayed BCIKS20 theorem. It is the result of repeating the probability union in Lemma 8.2 with the newly proved per-round threshold.

The exact coefficient of `N` in (5.2) is

\[
 C_h+\gamma_hY_h+
 \sum_i d_i\left(\frac{C_{b_i}}{P_i}+Y_{b_i}\right),
 \tag{5.3}
\]

and the additive constant is

\[
 Y_h+\sum_i d_iY_{b_i}.
\]

Thus the whole commit error is linear in `N`.

When all folds are binary, every `b_i=h`, and

\[
 \sum_i\frac{L_i-1}{P_i}=1-\frac1{P_{r-1}}.
\]

So (5.2) simplifies to

\[
 \varepsilon_C^{\rm lin}(h)=\frac1{|F|}\left[
 C_hN\left(2-\frac1{P_{r-1}}\right)
 +Y_h\left(\gamma_hN+1+(N+1)\sum_i d_i\right)
 \right].
 \tag{5.4}
\]

This telescoping factor is the linear analogue of BCIKS20's quadratic geometric-series factor. In the old proof,

\[
 1+\sum_i\frac{L_i-1}{P_i^2}<\frac32,
\]

which turns the per-event coefficient `1/3` into the theorem's `1/2`. For a linear local-domain term, the corresponding factor is less than `2`, not `3/2`. Simply replacing `N^2` by `N` inside the final BCIKS20 formula without recomputing this sum misses that change.

### 5.3 Soundness composition

The FRI error is now bounded by

\[
 \varepsilon_{\rm FRI}\leq \varepsilon_C^{\rm lin}(h)+\alpha_h^s.
\]

Including the query grinding parameter `zeta`, ethSTARK equation (20) gives

\[
 \boxed{
 \lambda(h)\geq
 \min\{-\log_2\varepsilon_C^{\rm lin}(h),
       \zeta-s\log_2\alpha_h\}-1.
 }
 \tag{5.5}
\]

The analysis parameter `h` is not a prover knob. It is optimized over integers `h>=3` separately for each row.

## 6. Numerical instantiation

### 6.1 Field and schedules

For BabyBear,

\[
 p=2^{31}-2^{27}+1=2013265921,
\]

so

\[
 \log_2p=30.9068905963251129,
 \qquad
 \log_2|F|=4\log_2p=123.627562385300452.
\]

The rows use the deployed query knobs associated with the supplied rates:

- `rho=1/64`: `s=19`, `zeta=16`;
- gnark outer at `rho=1/8`: `s=38`, `zeta=16`.

The fold schedules reduce the degree by the inverse rate:

- arity-8 wrap: `(L_i)=(8,8,8,8,2)`, so `sum L_i=34` and `(d_i)=(7,7,7,7,1)`;
- binary leaf at rate `1/64`: six folds, `sum L_i=12`;
- binary outer at rate `1/8`: fifteen folds, `sum L_i=30`.

Using the coarser repository ledger convention `5*8=40` instead of the exact wrap sum changes the final new wrap result by only about `0.0012` bits; the table uses the exact schedule.

The numerical convention in this section follows the problem statement and treats the supplied `rho` as BCSS25's reduced rate. If an implementation instead names `(k+1)/n` as its rate, it must translate to BCSS25's `k/n` round by round before claiming the last decimals.

### 6.2 New public-bound results

The optimized results from (5.2)--(5.5) are:

| row | optimizing `h` | BCSS `b` used in rounds | `alpha_h` | `-log2 eps_C^lin` | `zeta-s log2 alpha_h` | composed lower bound |
|---|---:|---|---:|---:|---:|---:|
| wrap `2^19`, `1/64`, arity 8 | 14 | 28 for degree 7; 14 for the last binary fold | 0.129464285714 | 72.000047706 | 72.038104612 | **71.000047706** |
| leaf `2^12`, `1/64`, binary | 58 | 58 | 0.126077586207 | 72.872016591 | 72.764709235 | **71.764709235** |
| outer `2^18`, `1/8`, binary | 49 | 49 | 0.357161078252 | 72.565763447 | 72.443422513 | **71.443422513** |

For reproducibility, the corresponding commit errors are

\[
 \begin{array}{rcl}
 \text{wrap:}&\varepsilon_C^{\rm lin}&=2.1175123469049322\cdot10^{-22},\\
 \text{leaf:}&\varepsilon_C^{\rm lin}&=1.1570101303432654\cdot10^{-22},\\
 \text{outer:}&\varepsilon_C^{\rm lin}&=1.4306340066213249\cdot10^{-22}.
 \end{array}
\]

At the wrap optimum, the union-bound numerator before division by `|F|` is

\[
 3.4788084805297337\cdot10^{15}.
\]

The initial affine event contributes about `1.147067120042364e14`; the five fold events contribute about `3.364101768525497e15`. These numbers are far below the challenge-field cardinality.

### 6.3 Comparison with the displayed BCIKS20 formula

For a fair comparison, optimize the original formula over integer `h>=3` using the same `s`, `zeta`, and exact `sum L_i`:

\[
 \varepsilon_C^{\rm old}(h)=
 \frac{(h+1/2)^7N^2}{2\rho^{3/2}|F|}
 +\frac{(2h+1)(N+1)}{\sqrt\rho|F|}\sum_iL_i.
\]

This gives:

| row | old optimum `h` | old commit column | old query column | old composed | new composed | gain |
|---|---:|---:|---:|---:|---:|---:|
| wrap `2^19`, `1/64`, arity 8 | 3 | 64.976077928 | 68.774543995 | 63.976077928 | 71.000047706 | **+7.023969778** |
| leaf `2^12`, `1/64`, binary | 7 | 71.279328215 | 71.108822203 | 70.108822203 | 71.764709235 | **+1.655887033** |
| outer `2^18`, `1/8`, binary | 5 | 66.911541052 | 67.774866098 | 65.911541052 | 71.443422513 | **+5.531881461** |

The tall low-rate wrap does improve substantially, but not by 17 bits after composition. There are three reasons.

1. The query/PoW column is near 72 bits and cannot benefit from the commit improvement.
2. For the degree-7 rounds, the public curve theorem requires `b=2h`, making the fifth-power constant larger than a line-only substitution suggests.
3. Reassembling a linear per-round error changes the geometric-series factor and retains the denominator-weighting contribution.

At a fixed line parameter, the asymptotic raw leading-term improvement can indeed be on the order of `log2 N`. For example, comparing the old leading term with the twice-summed new line leading term gives the ratio

\[
 \frac38(h+1/2)^2N.
\]

At `N=2^19` this ratio is over 21 bits already at `h=3`. But a raw leading-term ratio is not the optimized equation-(20) gain. Optimization changes `h`, arity-8 changes the BCSS parameter, and then the query column takes the minimum.

Thus the warning requested in the problem is affirmative: **the proven composed gain is smaller than +17 bits at `rho=1/64`**. The linear win survives; the headline gain is capped elsewhere.

### 6.4 Reconciling the “61 bits at `2^19`” anchor

The problem's stated wrap row combines `N=2^19`, `rho=1/64`, and the wrap query knobs. The displayed BCIKS20 formula evaluates there to 63.976 composed bits when optimized, not 61.

The current repository's 61-bit commit anchor is the separate recursion configuration:

\[
 N=2^{19},\quad \rho=1/8,\quad s=38,\quad \zeta=14,
\]

with binary folds and the ledger's fixed `h=7`. For that row,

\[
 -\log_2\varepsilon_C^{\rm old}(7)=61.779328216,
\]

whose integer floor is 61. Equation (20) at that fixed `h` gives 60.779 bits after the final `-1`. If the old row is optimized, `h=5` gives 63.9115 composed bits.

For reference, applying the public linear binary bound to that *actual recursion row* and optimizing gives

\[
 h=56,\quad
 -\log_2\varepsilon_C^{\rm lin}=70.61164,\quad
 \zeta-s\log_2\alpha_h=70.51269,
\]

and hence

\[
 \lambda\geq69.51269.
\]

This extra row is not substituted for any of the three rows requested above; it is included solely to explain where the repository's “61” comes from.

## 7. Adversarial self-check: try to break the public route

### 7.1 Does Lemma 8.2 supply arbitrary prescribed agreement sets?

No. At a fixed round, after fixing the transcript prefix, the bad event is

\[
 \operatorname{agree}_{\nu^{(i+1)}}(u_z,V^{(i+1)})>\alpha_i.
\]

For every bad `z`, choose a codeword `P_z` attaining that weighted agreement. The code is finite, so a maximizer exists. These are not externally prescribed sets that the proof must preserve for an adversary; they are witnesses selected for the event itself.

The public BCSS Section 3 proof accepts these selected `P_z`, and Step 4 returns a subset on which the *same* `P_z` lie on one polynomial curve. Therefore (3.1) holds and BCIKS20 Lemmas 7.5--7.6 apply verbatim. The proof never asks for a tuple that agrees on one particular adversarially fixed `A_z`.

### 7.2 Are the FRI weights really denominator-bounded?

Yes. `mu^(0)` has values in `{0,1}`. Each transition to the next domain averages uniformly over a fold coset. Inductively, on `D^(i+1)` the denominator divides

\[
 \prod_{j=0}^iL_j=\frac N{|D^{(i+1)}|}.
\]

Zeroing a weight when a consistency condition fails does not enlarge the denominator. This is exactly the `W_i` in (4.1).

### 7.3 Does the strict `>` in Lemma 8.2 cause a boundary gap?

No. The bad event uses weighted agreement strictly greater than the running threshold. Since the weights lie on a finite grid, one may raise the threshold to the next grid value actually attained by the event and then apply Lemma 7.6. The resulting joint agreement is strictly above the old threshold, which is what the contradiction in Lemma 8.2 needs. This is the same discretization used in BCIKS20's proof.

### 7.4 Does the inverse FRI interpolation need more than joint weighted agreement?

No. Once `u_0,...,u_d` jointly agree with codewords `v_0,...,v_d` on a set of `nu^(i+1)`-weight above the running threshold, BCIKS20 applies the inverse fold interpolation pointwise to obtain a codeword in `V^(i)` agreeing with `f^(i)` with at least that weight. This step depends on the FRI interpolation map and code closure, not on how the joint set was obtained. Equation (3.4) supplies exactly the premise it consumes.

### 7.5 What still relies on something beyond (A)--(C)?

Three scope qualifications remain.

1. **Unrestricted real weights:** as proved in Section 3.3, Lemmas 7.5--7.6 do not recover full Corollary 4.4. Theorem 4.3 or another exact arbitrary-weight argument is needed there.
2. **The initial batched affine event:** Lemma 8.2 uses the standard line-to-affine reduction. That reduction is public in BCIKS20 Section 6.3 and does not use `[Sta25]`, but it is an additional elementary ingredient beyond the three items if “(A)--(C) only” is read literally for the entire FRI theorem rather than for the weighted curve step.
3. **Degree-`d` curve scaling:** BCSS25 Section 4.1 states the extension and explains the `d`-fold `Z`-degree and final bound. The detailed Section 3 proof is written for a line. The extension is reconstructible by replacing `(0,1,1)` with `(0,d,1)` and carrying the factor `d`, as done in (2.4)--(2.17); no personal communication is used. Nevertheless, a citation should say that this reconstruction is part of our assembly, not that BCSS25 states a full FRI theorem.

None of these qualifications creates an arbitrary-set gap in the FRI round-by-round use.

## 8. Final conclusion

The strongest correct conclusion from the public record is:

- **Refuted in full generality:** BCSS25 Corollary 4.4 for arbitrary real weights is not derivable from the public co-curvilinearity result plus BCIKS20 Lemmas 7.5--7.6 alone. The denominator-free last step is precisely where the stronger Theorem 4.3 matters.
- **Confirmed for FRI:** BCIKS20 Lemma 8.2 uses rational subtree-acceptance weights with a known common denominator. For those weights, the BCSS25 co-curvilinear subset and BCIKS20's elementary double counting give exact weighted correlated agreement with the linear exceptional bound (3.5). The full adversarial “given sets” theorem is not consumed.
- **Bookkeeping closes:** the improved `D_Z=O(1)` gives the exact former-quadratic coefficient `2(b+1/2)^5/(3rho^(3/2))`; demanding `|S'|>=d(Wn+1)` adds `d(b+1/2)(Wn+1)/sqrt(rho)`. At FRI round `i`, `Wn=N`, so both contributions are linear in `N`.
- **The numerical gain is real but capped:** the requested rows yield about 71.00, 71.76, and 71.44 composed bits. At low rate the gain is not +17 bits after composition; the query/PoW column and the degree-7 parameter mapping absorb most of the raw asymptotic improvement.

Accordingly, `[Sta25]` is eliminable from a carefully stated FRI-specific security derivation, but it is not honest to say that the public ingredients reproduce BCSS25 Corollary 4.4 verbatim. Any mechanized or deployed ledger should encode the denominator-bounded theorem (3.5) and the reassembled error (5.2), with the binary/general-curve parameter distinction explicit.
