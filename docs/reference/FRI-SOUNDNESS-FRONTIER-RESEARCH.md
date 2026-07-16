# FRI-SOUNDNESS-FRONTIER-RESEARCH — what the capacity refutation actually killed, and what buys PROVEN bits

**What this is.** A four-lane literature + code synthesis answering one question: *given that the FRI
capacity conjecture is refuted, what is dregg's best PROVEN (not conjectured) soundness posture, and
what would raise it?* Companion to [`FRI-PARAM-FRONTIER.md`](./FRI-PARAM-FRONTIER.md) (the knob→cost
map). This doc changes no parameter and no Lean; it is the research record and a corrections list.

**The two-column law is preserved throughout.** FRI soundness is a product of (1) the **per-fold**
proximity-gap error and (2) the **query** ledger. This doc never multiplies them into a headline —
`FriLedgerSound.query_ledger_does_not_determine_perFold` is a theorem, not a caveat. Every number
below is labeled with its column.

---

## 0. Headline

Four findings, in descending order of how much they should change what we do.

1. **The capacity refutation does NOT reach BabyBear — but the posture stands anyway, for a better
   reason than the tree gives.** No published counterexample instantiates at our field: the one that
   hits our rate exactly (ρ = 1/64) needs **characteristic 2**; the one that hits our *domain shape*
   (a smooth multiplicative subgroup) needs a **~2^1024-bit prime chosen per block length**. Neither
   is BabyBear. But this is **not** a rescue of the capacity column, because a conjecture refuted in
   general cannot be priced against on a technicality of field cardinality. Demoting capacity to a
   drift canary and standing on Johnson was the right call, and is now **externally confirmed** — the
   Nov-2025 SoK's verbatim verdict is *"Soundness up to the Johnson bound is unaffected."*
   → ember: the refutation is real, but it does **not** mean "they broke the coset RS we run."

2. **⚑ The proven column is missing a term, and it is the term that binds.** Our ledger's
   `q·lb/2 + pow` is the `m → ∞` idealisation of BCIKS20 Thm 8.3 and **silently drops the commit-phase
   error ε_C**. Two lanes and my own independent recomputation agree: the deployed wrap proves
   **~70**, not 73. Worse, ε_C ∝ |D⁽⁰⁾|²/|F| means the proven posture is **not trace-invariant** — at a
   2^20-row trace the same config falls to **~62**. This is a *measurement* gap in our ledger, not a
   break: the number was never load-bearing against an attack, and BCHKS25 (below) buys most of it back.
   ⚑ **UPDATE 2026-07-15 (§3.2a): the heights are now MEASURED, and ~70 was the FIXTURE's number.** The
   deployed worst case is `|D⁽⁰⁾| = 2^19` — the `WRAP_LOG_CEIL = 16` recursion ceiling, forced on every
   fold, already shipping — which proves **~64**, i.e. **~7 bits BELOW the gate's own
   `JOHNSON_FLOOR_BITS = 71`**. The `2^6`-row "fixture" turns out to be `MIN_TRACE_HEIGHT`, the system's
   *smallest* real trace. **This does not become a break** (same reason as above — the column is not what
   stands between us and an attacker; the per-fold and Johnson columns are), but the honest deployed
   proven number is ~64, and **the pow lever cannot reach 71 at that height** (item 8, refuted).

3. **⚑ There is a CEILING at ~78 proven bits at ext-degree 4, and no query or PoW bump can pass it.**
   Because ε_C ∝ 1/|F| and grows as m⁷, the `min` in ethSTARK eq. (20) saturates: q = 25 and q = 200
   prove the *same* 77.98 bits. **Extension degree is the only lever that raises the ceiling** (+30.91
   bits per degree = exactly log₂ p). ⚑ **This makes `FRI-PARAM-FRONTIER.md`'s Frontier B — "proven
   Johnson 128 at (lb=8, q=28), +50% wire, no new crypto" — unreachable at ext-degree 4.** That row
   should be withdrawn or re-labeled.

4. **The cheap lever is real but smaller than one lane claimed, and it is NOT free.** PoW bits are
   free on **wire** (one field element) and free on **verify** — but the grind is `challenger.grind()`
   at `fri/src/prover.rs:98`, **inside `prove`, per proof**, Fiat-Shamir-bound to the transcript. It
   is not a one-time cost. `pow 16→20` is genuinely near-free (+3.3 bits, 16× a microsecond grind);
   `pow→27` reaches the ceiling but costs 2048× the grind on a 58 ms prove.

**What did NOT move.** The per-fold column's Kambiré defence is *correct*, and for a stronger reason
than the tree states (§1.4). Johnson remains the sharpest proven per-query rate at our rates, and
that is now backed by a **proven barrier**, not merely an absence of results (§2.3).

---

## 1. What Kambiré actually killed

### 1.1 ⚑ Citation error — `2025/2046` is not Kambiré

All four lanes independently found this; it is **certain**.

`FRI-PARAM-FRONTIER.md` (lines 11-13, 122-124, 262-263), `HORIZONLOG.md`,
`docs/deos/CRATE-EXCELLENCE-PLAN.md`, `GOAL-MULTICHAIN-SETTLEMENT.md`, and the memory file
`project-linking-tower-forgery-closure.md` all cite *"Kambiré (arXiv 2604.09724 + eprint 2025/2046)"*
as one work. **They are two papers by different authors, with different methods.**

| cite | actually is | what it does |
|---|---|---|
| arXiv **2604.09724** | Antonio Kambiré, *Proximity Gaps Conjecture Fails Near Capacity over Prime Fields*, 9 Apr 2026, sole author, 2pp | **counterexample** over prime fields, fleshing out a sketch by Krachun & Kazanin (his ref [4], personal communication, unpublished) |
| eprint **2025/2046** | **Elizabeth Crites & Alistair Stewart** (Web3 Foundation), *On Reed–Solomon Proximity Gaps Conjectures*, rec. 2025-11-05, rev. 2025-12-19 | **impossibility via reduction**, *not* a counterexample — disproves three up-to-capacity conjectures (BCIKS correlated agreement; WHIR's mutual correlated agreement; DEEP-FRI list-decodability) |

So the parenthetical also **mis-describes Crites–Stewart**: it constructs no counterexample at all.
Kambiré's own bibliography does not cite Crites–Stewart. The *refutation claim survives and is in fact
doubly sourced* — only the attribution is wrong.

### 1.2 The four refuting results, and exactly what each needs

The conjecture refuted is BCHKS **Conjecture 1.2** (`n^τ`-bounded proximity gaps), verbatim:

> *Let δ ∈ (0,1) be a constant. For every Reed–Solomon code C = RS[F_q, D, k] with length |D| = n and
> distance δ, and for every η > 0, C has proximity gaps up to radius γ = δ − η, with proximity loss
> ε\* = o_η(1) and a = O_η(n^τ).*

| paper | kind | rate reached | field / domain needed | hits BabyBear? |
|---|---|---|---|---|
| **Diamond–Gruen** eprint 2025/2010 | counterexample | **rate → 0 only** | — | **NO** — our rates are fixed constants |
| **Crites–Stewart** eprint 2025/2046 | impossibility (reduction to list-decoding) | up-to-capacity forms | "large fields" | **NO** (but see §6) |
| **BCHKS** ECCC TR25-169 Thm 1.6 | counterexample | **ρ = 2^−(τ+2) — exactly 1/64 at τ=4** | **characteristic 2** + domain = random **F₂-subspace** | **NO** — BabyBear is odd char; our domain is a multiplicative coset |
| **Kambiré** arXiv 2604.09724 | counterexample | ρ ∈ (0, ½) — formally covers 1/64 | **prime p chosen per n**, p ≡ 1 (mod n), p ∈ [4^s, 8^s] | **NO** — ~2^1024, vs our fixed 2^31 |

**Diamond–Gruen explicitly nominate our regime as still-plausible**, verbatim from their abstract:
*"Our code families' relative rates converge to 0 and their relative radii converge to 1"*, and they
suggest *"that conjecture be restricted to the case of families whose relative rates are bounded from
below by a positive constant."* dregg's rates (1/64, 1/8) are exactly that case.

**Kambiré's decisive qualifier, the one the tree omits.** His Thm 1 selects the prime *as a function
of n* via a quantitative Linnik theorem, from `[4^s, 8^s]` with `s = K·log₂ n`. Instantiated at our
rate (ρ = 1/64, C = 1 — *this arithmetic is lane-1's, not Kambiré's*): K = 32, s = 512, n = 2^16, so
**p ∈ [2^1024, 2^1536]**. dregg runs BabyBear p = 2^31 − 2^27 + 1, |F| = p⁴ ≈ 2^123.6. The gap is
~900 bits. It is an asymptotic existence statement over a family with p growing per n; it says nothing
about a fixed 31-bit prime.

**Kambiré's second qualifier: the radius.** He fails at δ = (1−ρ) − Ω(1/log n) — a *vanishing* distance
below capacity. At ρ = 1/64 that is δ ≈ 0.980 vs capacity 0.984 — and vs **Johnson 1−√ρ = 0.875**.
**The counterexample lives ~0.105 above the radius dregg operates at.**

**BCHKS Thm 1.6 is the near miss worth knowing.** At τ = 4 it lands at **ρ = 1/64 exactly** — our
deployed wrap rate, constant not vanishing — with γ = 15/16 = 0.9375, strictly between Johnson (0.875)
and capacity (0.984). It misses us on two independent grounds: characteristic 2, and a domain that is
*"essentially a uniformly random F₂-subspace of F_q"* (verbatim) rather than a multiplicative coset.
BCHKS flag both escapes themselves, verbatim:

> *"Versions of Conjecture 1.2 may still be true. For example, the conjecture may hold, even with
> τ = 1, for fields of prime cardinality, or for well chosen evaluation domains D over fields of
> characteristic 2. We think this is a very exciting direction for future research."*

Kambiré's paper is precisely the closure of the *prime cardinality* escape — hence its title. ⚑ Note
**BabyBear⁴ has prime-power cardinality p⁴ with odd characteristic — literally in neither
counterexample family.** Do **not** lean on this; see §1.3.

### 1.3 ⚑ The coset/plain axis is NOT where the defence lives

The tree's *"counterexamples for coset Reed–Solomon"* framing is half-right in a way worth fixing.
Kambiré's domain is `D = ⟨ω⟩`, the multiplicative subgroup generated by a primitive n-th root of unity
— **exactly the smooth FRI-shaped domain**. And since RS on a coset `gH` is equivalent to RS on `H` by
the degree-preserving rescaling `f(X) ↦ f(gX)`, **plonky3's coset offset buys nothing**. The tree is
right not to lean on "coset"; it should also stop implying "coset" is what is under attack.

**The honest defence is not "they missed us."** It is: *a conjecture refuted for all τ in char 2 and
near-capacity over prime fields cannot be a security basis for anyone.* The capacity column is dead as
a target regardless of whether any counterexample reaches BabyBear — which is exactly why carrying it
as a drift canary, and standing on Johnson, is correct. **The posture does not depend on the escape.**

### 1.4 ⚑ The refutations do not even speak to our per-fold column — a stronger position than we claim

Every one of these results (DG, CS, BCHKS, Kambiré) is about the **affine line** `f + z·g` over a code
family with `k → ∞`. dregg's `wrap_perFold_soundness_capacity` (112.6 at arity 2 / lb 6; 109.84 at the
deployed arity 8) is a **field-independent counting bound over a fixed dim-2 constant-fold recursion
code** (|κ| = 64, C(64,2) = 2016). Two structural reasons it is **out of scope entirely**:

1. **k = 2 is fixed** — asymptotic family counterexamples cannot instantiate at a fixed small dimension.
   (Lane 3 confirmed from Kambiré's text that his construction *"does NOT apply to fixed small
   dimension codes; it requires n to grow arbitrarily large."*)
2. **The arity-8 fold is a degree-7 moment curve**, not the affine 2-to-1 line these theorems analyze.

So `FriCorrelatedAgreementSharp.lean` §8's comment *"SOUND against Kambiré's capacity refutation"* is
**correct, and for a sharper reason than proximity**: the object is different. ⚑ **But the name
`wrap_perFold_soundness_capacity` invites exactly the misreading that produced the bad headline** — it
is a bespoke dim-2 count, *not* an instance of the refuted capacity conjecture. Recommend a rename or
a clarifying comment.

⚠ **One unwritten check.** Our dim-2 defence is checked against **Kambiré only**. Crites–Stewart is an
*independent* refutation (impossibility via list-decoding, over large fields) whose regime we have
**never tested the dim-2 counting bound against**. Per `feedback-prove-the-floor-false`, that check
should be written before 109.84/112.6/118 is quoted again. This is per-fold and does not touch the 73.

---

## 2. The best PROVEN posture available today

### 2.1 ⚑ The lb/2 ledger IS BCIKS20 — but our number drops ε_C

`numQueries·logBlowup/2 + powBits` is exactly the `α^s` term of **BCIKS20 Thm 8.3** (eprint 2020/654,
JACM 10.1145/3614423), read verbatim from the local mirror at
`~/dev/gh/forks/IACR-eprint-mirror/2020/654.pdf` (Thm 8.3, pp. 40-41):

```
ε_FRI = ε_C + α^s ,   α = √ρ·(1 + 1/2m) ,   m ≥ 3
ε_C   = (m+½)⁷·|D⁽⁰⁾|² / (2ρ^{3/2}|F|)  +  (2m+1)(|D⁽⁰⁾|+1)·Σᵢ l⁽ⁱ⁾ / (√ρ·|F|)
```

`−log₂ α → (1/2)log₂(1/ρ) = lb/2` as `m → ∞`. **So our ledger is the bottom row at m → ∞ and omits
ε_C entirely.** ethSTARK (eprint 2021/582) eq. (20) composes them: `λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1`.

The catch: **ε_C grows as m⁷ while the query term improves only as `−log₂(√ρ(1+1/2m))`.** Buying query
bits needs large m, which detonates ε_C. Optimising over m at the deployed wrap gives **~70, not 73**.

**Independently reproduced three times.** Lane 2 got 70.47, lane 4 got 70.11, and my own from-scratch
implementation (`scratchpad/eps_c.py`) reproduces **70.11 at m = 7** exactly. Three implementations of
a formula read verbatim from the paper, agreeing to <0.4 bits, is strong evidence the shape is right.

⚑ **And plonky3's own conjectured number drops two terms.** `fri/src/config.rs:42-44` (rev `82cfad73`,
verified verbatim):
```rust
pub const fn conjectured_soundness_bits(&self) -> usize {
    self.log_blowup * self.num_queries + self.query_proof_of_work_bits
}
```
It cites ethSTARK, but eq. **(19)** is `λ ≥ min{ζ + R·s, log₂|K|} − 1` — plonky3 drops **both** the
`min{·, log₂|K|}` field cap **and** the `−1`. At our deployed wrap: our ledger reads 130; eq. (19)
reads `min{130, 123.63} − 1 = 122.63`. **The field cap is already binding on the conjectured column**
— 7 of the "130 capacity bits" do not exist. (plonky3's own doc-comment at `:40-41` concedes *"proven
soundness … isn't currently supported by this crate."*) Our `FRI-PARAM-FRONTIER.md` already notes a
`~124` cap; the ledger arithmetic does not apply it.

### 2.2 ⚑ SOTA is BCHKS25, and it buys most of the shortfall back

**Ben-Sasson, Carmon, Haböck, Kopparty, Saraf**, *On Proximity Gaps for Reed–Solomon Codes*,
**ECCC Report TR25-169**, 11 Nov 2025 (fetched in full from Kopparty's faculty page; confirmed as ref
[1] of Kambiré's bibliography). Verbatim from the abstract:

> *"For proximity gaps up to the Johnson radius J(δ), we show that proximity loss ε\* = 0 can be
> achieved with only O(n) exceptional z's (improving the previous bound of O(n²) exceptions). This
> significantly reduces the soundness error in the aforementioned arguments systems."*

This is a **live upgrade to our proven column**: the O(n²)→O(n) improvement attacks exactly the
`|D⁽⁰⁾|²` factor that makes ε_C bind. Lane 2's assembly of BCHKS25's Thm 4.2 bad-set bound into
BCIKS20's round structure recovers ~2 bits and lands the deployed wrap at **~72.45**, i.e. within
~0.55 bits of our quoted 73 — **making 73 defensible, but only by citing BCHKS25, not BCIKS20.**

⚠ **Flagged: BCHKS25 does not restate a full FRI soundness theorem.** It explicitly defers to the
existing analyses ([BCIKS20], [HLP24 = Circle STARKs], [Sta25 = S-two]). The assembly is *lane 2's*,
not the paper's; the shape is solid, the constant could move ~1 bit.

⚠ **The constants are brutal at ρ = 1/64.** Thm 1.5's bound carries `ρ^{-3/2} = 512` and `η^{-5}`, so
the asymptotic O(n²)→O(n) win is *largely eaten* at our very low rate. Lane 1's instantiation
(ρ=1/64, γ=0.85) gives ≈2^-86 vs a naive O(n²) ≈2^-83.6 — a real but modest win, and the comparison
uses a naive incumbent constant. **The win is likely larger at ρ = 1/8** (the gnark outer/recursion
configs) where `ρ^{-3/2} = 22.6` rather than 512. This needs a careful instantiation before claiming bits.

### 2.3 ⚑ Johnson is the ceiling of the unconditional — and that is now a PROVEN barrier

The answer to *"is there something sharper than Johnson?"* is **no, and there provably cannot be
without first improving RS list-decoding.** Four independent obstructions:

- **BCHKS25 Cor 1.7** — proximity gaps *at* J(δ) with even o(1) loss require `a ≥ n^{2−ε}` exceptions.
  Constructed at δ = 15/16, γ = 3/4 = J(δ) exactly; the paper says this *"shows that Theorem 1.5, on
  proximity gaps up to the Johnson radius, is tight for a particular value of δ."*
- **BCHKS25 Thm 1.9 — the one result with NO escape hatch** (no characteristic, rate, or family
  restriction): beyond the list-decoding radius for list size q, soundness error is `≥ 1/(2n)`, and
  *"thus cannot be reduced by increasing q"* (verbatim). **A bigger field cannot buy back radius.**
- **BCHKS25 abstract**, verbatim: *"improved bounds on the list-decoding radius of Reed–Solomon codes
  is a prerequisite for any new proximity gaps results beyond the Johnson radius."*
- **Crites–Stewart 2025/2046** independently: correlated agreement with small enough error implies
  list-decoding of RS.

Guruswami–Sudan decodes exactly *to* 1−√ρ = Johnson (it is what BCIKS20 uses non-algorithmically);
Koetter–Vardy is soft-decision and buys no worst-case radius for RS.

⚑ **And the "randomly punctured RS achieves list-decoding capacity" line does not rescue us.** BCHKS25
cites [RW13, ST20, GLS+24, BGM23, GZ23, AGL24] for RS with **randomly chosen evaluation domains**
being list-decodable near δ. Our domain is a coset of a 2-smooth multiplicative subgroup — mandatory
for the FFT, maximally structured, and precisely the family Kambiré builds on. **This capacity-achieving
line is unavailable to dregg and to every FFT-based STARK.** Worth stating in the frontier doc: it is
the most natural "but surely capacity is fine" objection, and it has a clean refusal.

**So `FRI-PARAM-FRONTIER.md:298-317` — *"there is no capacity-rate upside to chase — that door is
closed by the refutation"* — is CORRECT, and is now backed by a proven barrier rather than an absent proof.**

### 2.4 The one paper claiming "above Johnson" is strictly worse for us

**eprint 2026/858**, Chai & Fan (IoTeX Network), *FRI Soundness Above the Johnson Bound via Threshold
Halving*, approved 2026-05-05. Claims *"the first unconditional soundness theorem above the Johnson
bound for FRI, STIR, and WHIR"*, via Rothblum–Vadhan–Wigderson threshold halving, changing no prover
message — only recalibrating the query parameter:

```
ε_FRI ≤ nR/|F| + (1 − δ/2)^q ,  for every δ ∈ (δ_J, 1−ρ)
```

**Lane 3 derived that it is dominated at every rate.** The base beats Johnson only if `1 − δ/2 < √ρ`,
i.e. `δ > 2(1−√ρ) = 2δ_J`. But with `x = √ρ`: `1−ρ ≤ 2(1−√ρ) ⟺ (1−x)(1+x) ≤ 2(1−x) ⟺ 1+x ≤ 2`, true
for all ρ < 1. **So the reachable radius δ ≤ 1−ρ is always strictly below 2δ_J — the bound is never
the argmax.** "Above the Johnson bound" refers to the **radius δ**, not to soundness **bits**.

At our params: deployed wrap **73 → 34.6** (a 38-bit loss); outer at rate 1/8 **73 → 47.5**. The gap
*widens as rate falls*, so our deliberate low-rate posture is exactly where this bound is worst. It is
a genuine advance for the *radius* gap left open by the refutation; it is **not a lever for dregg**.
⚑ Beware: it is being summarised online as *"every deployed FRI system now has a positive proven
floor"* — true, but it reads as an upgrade and is not one.

Its sibling **eprint 2026/861** (same authors) titles itself *"A Rigorous O(1)/|F| Bound on Plain
Reed–Solomon, with 2× Smaller STARK Proofs"* but the abstract concedes it *"reduces to a single
sparse-worst-case dominance conjecture (Q2)"* — **not unconditional**; a reduction to a new, unvetted
conjecture, i.e. exactly the named-carrier pattern we refuse. No independent citation or replication
of either paper was found.

---

## 3. ⚑ THE LEVER TABLE

**Column: QUERY ledger, PROVEN (BCIKS20 Thm 8.3 + ethSTARK eq. (20), optimised over m ≥ 3).**
Baseline = deployed wrap (BabyBear, ext 4, |F| = 2^123.63, lb 6, arity 8, q 19, pow 16, |D⁽⁰⁾| = 2^12).
**Baseline 70.11 proven bits. Ceiling at ext-degree 4: 77.98 — unreachable-past by any q or pow.**

| # | lever | proven bits | cost | plonky3 today? |
|---|---|---|---|---|
| **1** | **ext degree 4→5** | **+30.91 on the CEILING** (77.98 → 108.88); +1.79 at q=19 alone | quintic EF mul (cheap); **gnark wrap rewrite + VK re-key** (expensive) | **YES for 5 and 8; degree 6 PANICS** |
| **2** | **powBits 16→20** | **+3.29** (70.11 → 73.39) | **0 wire, 0 verify**; 16× grind (still µs) — **per proof** | **YES** (hard cap 30; practical 27) |
| **3** | **powBits 16→27** | **+7.87** (70.11 → **77.98 = the ceiling**) | **0 wire, 0 verify**; **2048× grind, per proof** (~0.2–1.7 s est.) | **YES** |
| 4 | numQueries 19→25 | +7.87 (→ 77.98 = ceiling) | **5.28 KiB/query** → +32 KiB; +0.14 ms verify/query | YES |
| 5 | numQueries 25→200 | **+0.00** | pure proof size | YES |
| 6 | logBlowup 6→7 | +6.37 (→ 76.48) — **the proven optimum** | +4.4 KiB; **~2× prover** (58→101 ms measured) | YES |
| 7 | logBlowup 6→8 | **+4.87 only** (→ 74.98) — **WORSE than lb=7** | ~4× prover (183 ms) | YES |
| 8 | arity 8→2 | **+0.00** | ~+16–20% proof size at deployed | YES |

**Verified verbatim in the pinned source (rev `82cfad73`):**
- `impl BinomialExtensionData<4|5|8> for BabyBearParameters` — `baby-bear/src/baby_bear.rs:65,76,92`.
  **Degree 6 is absent AND unreachable**: `monty-31/src/extension.rs:27-32` `binomial_mul` matches
  `4 => quartic_mul_packed, 5 => quintic_mul_packed, 8 => octic_mul_packed, _ => panic!("Unsupported
  binomial extension degree: {}")`.
- ⚑ **Degree-5 caveat:** `EXT_TWO_ADICITY = 27` (`baby_bear.rs:86`) — **zero** two-adicity over
  BabyBear's own 27, vs 29 (deg 4) and 30 (deg 8). Independently re-derived: v₂(p⁴−1)=29,
  v₂(p⁵−1)=27, v₂(p⁸−1)=30 (the quintic is odd-index, so (p⁵−1)/(p−1) is odd). Harmless for challenge
  sampling; **prefer degree 8 over 5** if any path needs a smooth subgroup *in* the extension.
- PoW cap: `challenger/src/grinding_challenger.rs:113` `assert!((1u64 << bits) < F::ORDER_U64)`.
  BabyBear order = 2013265921 = 2^30.907 ⟹ **bits ≤ 30 or the prover panics**. Worse,
  `type Witness = F` (a *single* field element) and the search is exhaustive over the field with
  `.expect(...)`, so P(no witness) = exp(−p/2^bits) is a **prover panic, not a retry**: 3.1e-7 @ 27,
  5.5e-4 @ 28, 2.3% @ 29, **15.3% @ 30**. ⟹ **practical ceiling 27.**
- Why is pow 16? It is **plonky3's own default** (`fri/src/config.rs:83,97,111`) — inherited, not derived.

**⚑ CORRECTION to a lane's claim: the PoW grind is PER PROOF, not one-time.** `fri/src/prover.rs:98`,
`let pow_witness = challenger.grind(params.query_proof_of_work_bits);` — **inside `prove`**, and it
must be, since the witness is Fiat-Shamir-bound to the transcript. The grind *is* rayon-parallel and
SIMD-packed (`(0..num_batches).into_par_iter().find_map_any(...)`, lanes = `F::Packing::WIDTH`), so
expected work is `2^pow / lanes` packed permutations. At pow 16 that is ~8k perms — invisible inside a
58 ms prove. At pow 27 it is ~16.8M packed perms ≈ **0.2–1.7 s**, a 4–30× prover regression on every
proof. **So "pow → 27 is free" is wrong; "pow → 20 is nearly free" is right.**

**⚑ A second PoW knob nobody's lever table mentions:** `commit_proof_of_work_bits`
(`fri/src/config.rs:18`, defaulted `1`/`0` at `:54,68,82,96,110`), ground **per commit round** at
`prover.rs:224`. It does not enter `conjectured_soundness_bits` at all. Unexamined.

### 3.1 ⚑ The ceiling, and why it reorders everything

Sweeping **all** (q ≤ 200, pow ≤ 27) at the deployed trace/lb/arity, the maximum achievable proven
soundness at ext-degree 4 is **77.98 bits** — reached at q = 19 / pow = 27, and **not improved by
q = 200**. The gaps between degrees are exactly **log₂ p = 30.91**, because ε_C ∝ 1/|F| = 1/p^d:

| ext degree | proven ceiling | plonky3 |
|---:|---:|---|
| 4 (deployed) | **77.98** | YES |
| 5 | 108.88 | YES (but two-adicity 27) |
| 6 | 139.79 | **NO — panics** |
| 8 | 201.60 | YES |

⚑ **This withdraws Frontier B.** `FRI-PARAM-FRONTIER.md` §2 prices *"proven Johnson 128 at (lb=8,
q=28) → 180.9 KiB, +50% wire"*. Under BCIKS20's real ε_C **that is unreachable at ext-degree 4 at any
q** — the naive ledger's monotone `q·lb/2` reading is what makes 128 look purchasable. Reaching proven
128 needs **ext ≥ 6** (a plonky3 change we do not have) — lane 4 prices ext 6 + lb 3 + q 70 + pow 27 at
~340 KiB. ⚠ Under **BCHKS25** the ceiling rises (ε_C linear in n, not quadratic — worth roughly the
12–20 bits of `log|D⁽⁰⁾|`), so Frontier B may be *partially* recoverable; **nobody has computed the
BCHKS25 ceiling.** That is the single most valuable missing number in this doc.

### 3.2 ⚑ The proven posture is NOT trace-invariant — the finding no lane reported

ε_C ∝ |D⁽⁰⁾|², so **proven bits fall ~2 per trace doubling.** My sweep, same deployed config:

| trace | \|D⁽⁰⁾\| | proven |
|---:|---:|---:|
| 2^6 rows (the measured fixture) | 2^12 | **70.11** |
| 2^14 rows | 2^20 | **61.98** |

The measured cost grid is a **2^6-row trace** (`degree_bits [6,3,4]`, PROOF-ECONOMICS §2b) — smaller
than a production turn. ⚑ This *reconciles the two analyses*: the tree's
own counting bound also degrades ~2 bits/doubling once evaluated at the **first** fold rather than the
terminal one (§4.2) — the two agree on the shape. Under BCHKS25's O(n) the sensitivity halves to
~1 bit/doubling, which is a second reason to re-point the citation.

#### 3.2a ⚑ MEASURED 2026-07-15 — item 6 is CLOSED, and the real worst case is 2^19, not 2^12

The distribution above was **assumed**. It is now measured, off real proofs' `BatchProof::degree_bits`
(`circuit-prove/tests/fri_trace_height_measure.rs`, the non-rotting gate). Three of this section's
premises were wrong, and **all three in the same direction**:

1. **The tall trace is not hypothetical — it is DEPLOYED, on every fold, by construction.**
   `accumulator.rs:238` pins `WRAP_LOG_CEIL = 16` and `wrap_params()` applies it as a
   `min_trace_height` FLOOR (live, ON BY DEFAULT — `accumulator.rs:660`, `:427`) so the running fold's
   FRI shape is depth-invariant. At `log_blowup = 3` that is **|D⁽⁰⁾| = 2^19 on every fold** — the
   worst case is also the *typical* case. Measured natural fold heights are `degree_bits
   [9,9,15,14,15]` (re-measured via `apex_shrink_trace_anatomy`; recorded at `accumulator.rs:227`), so
   the ceiling pads 2^15 → 2^16. **The VK-depth-invariance knob is silently buying its constancy with
   ~7 proven bits.** Nobody priced that trade, because the ledger cannot see height.
2. **The leaf height is not the effect-VM trace — it is the Poseidon2 CHIP table, and it overtakes.**
   `MIN_TRACE_HEIGHT = 64` (`trace.rs:508`) floors the MAIN table at 2^6 (whence `[6,3,4]`), but FRI
   batches all five IR-v2 tables onto the largest domain, and the chip table runs ~4 rows/transfer —
   passing the main table at **32 effects**. Measured: 1 effect → `[6,3,4]` = 2^12; 32 → `[6,7,4]` =
   2^13; 64 → `[6,8,4]` = 2^14; 128 → `[7,9,4]` = 2^15; 512 → `[9,11,4]` = 2^17. A gate reading the
   *witness* height reports 2^6 for the 32-effect turn and is wrong by ~2 proven bits.
3. **Nothing caps effects-per-turn**, so the leaf |D⁽⁰⁾| is **unbounded above** (no `MAX_EFFECTS`-class
   bound exists in `turn/`, `intent/`, or `circuit/src/effect_vm/`). Small in practice — a real
   multi-verb turn measures `[3,4,3,3]` = 2^4 — but structurally open.

**The honest proven table at MEASURED heights** (this doc's own ε_C arithmetic, independently
reproduced a 4th time — 70.11 @ m=7 and 61.98 @ 2^20 both reproduce exactly):

| config | measured \|D⁽⁰⁾\| | proven | ledger asserts |
|---|---:|---:|---:|
| leaf ir2, 1-16 effects (**the fixture**) | 2^12 | 70.11 | 73 |
| leaf ir2, 64 effects | 2^14 | 69.39 | 73 |
| leaf ir2, 512 effects | 2^17 | 67.77 | 73 |
| outer/gnark shrink (2^15 tables) | 2^18 | 65.91 | 73 |
| **recursion WRAP (every fold)** | **2^19** | **63.91** | **71** |

⚑ **The deployed proven posture is ~64 bits, not ~70 and not 73** — the ~70 is the *fixture's* number,
and the fixture is the system's *smallest* real trace. The gate's `JOHNSON_FLOOR_BITS = 71` is
**~7 bits above** what the weakest config actually proves once ε_C is priced at its real |D⁽⁰⁾|. Note
`create_recursion_config` is now the weakest link on **both** columns at once (pow 14 *and* the tallest
trace), and the query ledger can see only the first. ⚠ These remain **optimistic upper bounds** — they
omit ethSTARK eq. (20)'s DEEP/ALI top row, as everything else in this doc does. BCHKS25's O(n) would
halve the trace sensitivity, which raises the stakes on re-pointing the citation (§2.2).

### 3.3 Why arity is not a security lever in either direction

Two independent routes agree it buys **0.00 bits**:
- On BCIKS20's ledger, arity enters ε_C **only** through `Σᵢ l⁽ⁱ⁾` in the second term (arity 8 = 2
  rounds × 8 = 16; arity 2 = 6 × 2 = 12 — worth log₂(16/12) = 0.415 bits on a term already ~23 bits
  below the dominant one). My sweep: **arity 2, 4, 8, 16 all give 70.11.**
- `α = √ρ(1 + 1/2m)` contains **no arity term at all** ⟹ **the Johnson query column is
  arity-independent and our ledger is correct as written.**

⚑ **The two analyses price arity differently and both are right** — they bound different objects.
BCIKS20's `Σl⁽ⁱ⁾` → 0.415 bits (a query-ledger effect); the tree's moment-curve count → 2.807 bits (a
per-fold effect). **There is no single "arity price."**

⚑ **So `FRI-PARAM-FRONTIER.md:163`'s framing — "arity costs 2.807 bits, moving it is ember's call" —
prices arity ~19× too high as a system-soundness trade.** The 2.807 is a true statement about the
per-fold column and a false one about system soundness; the per-fold column sits ~16 bits of slack away
from binding. Lane 2's end-to-end BCHKS25 computation makes the same point: arity 2 → 72.60 vs arity 8
→ 72.45, i.e. **arity 8 costs ~0.15 end-to-end bits, not 2.807.** This materially changes the arity
decision — and it is a *quantitative vindication* of the doc's own law never to multiply the columns.

⚑ **And the "+9%" cost is a real number quoted about the wrong object.** `FRI-PARAM-FRONTIER.md:162`
prices arity 8→2 at "+9% size — PROOF-ECONOMICS §1", but §1's row is measured at **v1's lb=3, q=50,
451.7 KiB** — a config nobody deploys. Lane 4's first-principles Merkle-path model (calibrated to 81%
against that one measured point) projects **≈+16–20% at the deployed lb=6/q=19/120.4 KiB**, because the
deployed proof is 3.75× smaller while its domain is 8× deeper (2^12 vs 2^9 ⟹ longer paths). Needs a
real measurement at `ir2_config`.

### 3.4 FriArityTransfer is vindicated by the literature

`FriArityTransfer.lean`'s `14112 = 7·2016` and `log₂ 7 = 2.807` are **exactly** BCIKS20 **Thm 1.5**
("correlated agreement for low-degree parameterized curves", error `l·ε`) and BCHKS25 **Thm 4.2**
("correlated agreement for curves, up to Johnson bound", bad set > `M·[O_ρ(n/η⁵)]`), at `l = M = arity
− 1 = 7`. Because Haböck (eprint 2022/1216, §3.1 eq. (3)-(4)) shows the arity-a FRI fold **is**
`p_i(Y) = F_0(Y) + λF_1(Y) + … + λ^{a-1}F_{a-1}(Y)` — verbatim plonky3's `lagrange_interpolate_at`
(`fri/src/two_adic_pcs.rs:109-131`), a degree-(a−1) curve, exactly these theorems' hypothesis.

**The tree independently rederived a published bound.** The *"the transfer was never mechanized /
degree-7 moment curve"* worry at `FRI-PARAM-FRONTIER.md:19-26` is real mathematics but **not
unexplored territory** — it is covered by a 2020 theorem and sharpened by a 2025 one. `FriArityTransfer.lean`
is **correct and is not a novelty risk.**

---

## 4. ⚑ Per-fold column — two statement-level residuals

**Column: PER-FOLD.** These do not touch the 73/71. Reported as flags for a metatheory lane, **not**
asserted as refutations: I read the *statements* and the composition, not every proof.

### 4.1 ⚑ The M=1 discharge may not fire at the radius FRI needs

The last commit (`0aacd6a6e`) discharges `hΦ` at the deployed arity 8. Read verbatim,
`FriArityFiberDischarge.lean:509-515`:

```lean
theorem arity8_phase_injective {f : Fin (2 ^ (3 + 6)) → BabyBear} {dOut : ℕ}
    (hfar : farN friSetupK8Wrap.C dOut f) (hdOut : 496 ≤ dOut) : …
```

On the 512-point domain (`friSetupK8Wrap_domain : … = 512`) that is a required relative distance of
**496/512 = 96.9%**. But **FRI soundness must reject words at the Johnson radius δ = 1 − √ρ = 0.875**
(= 448/512). **Words in the band [448, 496) — precisely where a cheating prover lives — appear not to
be covered**, so `hΦ` may be discharged only *outside* the regime that needs it.

The requirement is **intrinsic to the proof method**, not an artifact: `phase_injective_of_far` needs
`Fintype.card ι ≤ 2*n + dOut`, i.e. `dOut ≥ |ι| − 2n = 512 − 16 = 496`. The argument only bites when
the word is *almost maximally* far.

⚑ **The non-vacuity witness sits in the same band and therefore does not answer the question.**
`phase_injective_fires` exhibits a **503**-far word (98.2%) against the ≥496 requirement — genuinely
non-vacuous, but well above Johnson. This is the `feedback-prove-the-floor-false` shape exactly: the
floor was checked for non-vacuity at a radius that does not test it. **The deployed per-fold posture
(109) still looks hypothesis-carrying in the FRI-relevant band.**

### 4.2 The ledger's `|κ| = 2^logBlowup` models only the TERMINAL fold

`friSetupK8Wrap : FriSetupK BabyBear (Fin (2^(3+6))) (Fin (2^6)) (2^3)` — |L| = 512, |κ| = 64. But the
deployed prover folds **2^12 → 2^9 → 2^6** (two arity-8 rounds; `fri/src/prover.rs:198-200` runs
`while folded.len() > blowup * final_poly_len`, terminating at 2^lb = 64). **The modeled setup is round
1 of 2.** Round 0 has |κ| = 2^9, so by the tree's *own* count `|Good| ≤ 7·C(512,2) = 915712 = 2^19.80`
⟹ **103.82 bits, not 109.84** — and it degrades 2 bits per trace doubling (75.82 at a 2^20-row trace),
exactly as ε_C's |D⁽⁰⁾|² predicts. Still far above the binding column, so **the posture does not move**
— but `PER_FOLD_FLOOR_BITS = 109` is documented (`fri_params_soundness_budget.rs:149-153`) as *"the
deployed reading of the WEAKEST shipped config"*, and 109 is the **strongest** of the deployed rounds.

### 4.3 One thing in our favour that no lane noticed

`arity8_good_card_le` instantiates `good_card_le_of_phase_injective` at **s = 2** (`dIn = 62` ⟹
`|S β| ≥ 64 − 62 = 2`). Since the bound is `|Good|·C(s,2) ≤ (m−1)·C(|κ|,2)`, **smaller s = larger Good
set = weaker bound**: s = 2 gives 14112, while the Johnson-radius agreement (s ≈ 8) would give
`7·2016/28 = 504` ⟹ **~114.6 bits**. **The tree took the most conservative instantiation available.**
That is the right instinct, and it means §4.1's radius mismatch, if real, is the *only* thing standing
between the deployed per-fold number and a better one.

---

## 5. The construction question — STIR / WHIR / BaseFold / Ligero

**Blunt answer: no. Nothing here gives a stronger PROVEN posture at our rates, and the maturity gap is
disqualifying on its own.**

**The load-bearing fact: the whole RS line bottoms out at the SAME proven radius.** The SoK
(eprint 2026/1367, *SoK: Hash-Based Polynomial Commitments and Low-Degree Tests*, approved 2026-07-06)
states the primary sources *"report their guarantees under different, and frequently conflated,
soundness regimes: unique decoding, the Johnson list-decoding bound, and (conjecturally) capacity"*,
and places the proven cells at *"the Johnson bound for DEEP-FRI, STIR, and Basefold-over-RS."*
**STIR/WHIR/BaseFold do not escape the capacity conjecture — they rest on it exactly as FRI does, and
their proven fallback is the same 1−√ρ we already stand on.** Adopting them changes query **count**,
never the proven **bits per query**.

| scheme | proven radius | why not for dregg |
|---|---|---|
| **STIR** (2024/390, CRYPTO'24 best paper) | **Johnson** | win is `O(log d + λ log log d)` vs `O(λ log d)` — **asymptotic in degree**; our tables are **2^3–2^8 rows**, STIR's headline is at **d = 2^26** |
| **WHIR** (2024/1586) | **Johnson** | its headline rests on **mutual correlated agreement up-to-capacity — the conjecture Crites–Stewart disproved** |
| **BaseFold** (2023/1705) | Johnson (only via Haböck 2024/1571) | native codes are **random foldable** (punctured Reed–Muller), not RS; **multilinear** vs our univariate AIRs |
| **Blaze** (2024/1609, EUROCRYPT'25) | inherits BaseFold-over-RS ⟹ **Johnson** | **binary fields**; sells prover speed, not proven bits |
| **Ligero / Brakedown** | **unconditional** (code distance directly) | **O(√n) proofs — megabytes**; cannot be BN254-wrapped at our budget |

**STIR's strongest honest claim**, verbatim from its abstract: *"For λ bits of security, STIR has query
complexity O(log d + λ·log log d), while FRI … has query complexity O(λ·log d) (including variants of
FRI based on conjectured security assumptions)."* — STIR's **proven** query complexity beats FRI's
**conjectured** one, *asymptotically*. At d = 2^8: log d = 8, log log d = 3 — the two are within a
small constant, and STIR's added machinery (per-round OOD, degree corrections) plausibly eats it.

⚑ **We already banked STIR's core idea by a cheaper route.** STIR = "Shift To Improve Rate": recursively
improve the rate so later rounds are worth more Johnson bits. **IR-v2 already trades blowup UP /
queries DOWN to lb = 6 (rate 1/64)** — a static version of the same move. That is why we sit at 3
Johnson bits/query where a rate-1/4 system sits at 1.

**⚑ Corroborating that the regimes are first-class:** WHIR's reference implementation CLI exposes
`--sec {UniqueDecoding | ProvableList | ConjectureList}` — **the code itself admits its headline
numbers are the ConjectureList setting.**

**Maturity — disqualifying on its own.** STIR (`github.com/WizardOfMenlo/stir`): arkworks, self-described
academic prototype, explicitly not production. WHIR (`github.com/WizardOfMenlo/whir`): README states it
*"has not received careful code review"*. The plonky3 port that would matter (`tcoratger/whir-p3`): 838
commits, 68 stars, one maintainer, **no releases published**. **No gnark BN254 verifier exists for STIR
or WHIR at all** — which for us is the load-bearing gap, since our outer wrap *is* a gnark FRI verifier
and that circuit would have to be rewritten and re-audited from zero. **Trading a proven, mechanized,
`@[export]`-ed ledger across 7 shipped configs for an unmechanized number in unaudited one-maintainer
code is a downgrade in assurance whatever the paper says.**

### 5.1 ⚑ The one genuine prize — a research question, NOT a result

**Goyal & Guruswami**, eprint 2025/2054, *Optimal Proximity Gaps for Subspace-Design Codes and (Random)
Reed–Solomon Codes* (MIT / UC Berkeley; rec. 2025-11-06, rev. 2026-03-24). Verbatim: *"we prove that
variants of RS codes, such as folded RS codes and univariate multiplicity codes, indeed have proximity
gaps for δ approaching 1−R."* Field requirement: *"only linear in the block length"* — trivially met by
2^123.6. **This is the only door to proven-capacity, and it is a CODE change, not an IOPP change.**
(Corroboration: arXiv 2601.10047 was **withdrawn 2026-06-10** as *"subsumed by the prior work of Goyal
and Guruswami"*.)

**The suggestive part:** GG proves capacity gaps for **folded RS**, and *we already fold at arity 8* —
our fold opens a size-8 coset per query via `lagrange_interpolate_at`, and a folded-RS alphabet is
exactly a bundle of s consecutive evaluations.

⚠ **These are NOT the same object, and that is why this is a question and not a plan.** FRS folding is
a property of the **code's alphabet**; our arity-8 fold is a **protocol step** over a code that remains
plain RS on a smooth coset — and GG give plain RS only 1−√R. **Open question, which lane 3 found nobody
asking:** *does the GG curve-decodability / LCL machinery transfer to a coset-RS code whose queries
already reveal size-8 cosets?* Highest expected value in this survey; also plausibly very hard (the
Ethereum Foundation has a seven-figure bounty on the neighbouring MCA conjecture — the market's estimate,
and a fair one).

**2026 successor watch (fetched, negative).** arXiv 2607.08516 (Goyal, Guruswami, Sun, Wootters, 9 Jul
2026) improves gaps for **random** ensembles (random linear, RS with **random** evaluation points,
Gallager LDPC) with *"a black-box transference from subspace design codes"*. Still nothing for
deterministic RS on a smooth coset. **The direction of all 2025–2026 progress is uniform: capacity gaps
are being proven for codes with random or subspace-design structure, and plain coset RS is being left
at Johnson.** No sign of anyone closing it for our code.

---

## 6. ⚑ THE HONEST RECOMMENDATION

Ranked. **Nothing here is urgent** — no published result attacks any dregg config, and per
`feedback-iterative-approximative-method` these are scheduled sharpenings on a chosen trajectory, not
surprises. The single highest-value item is a **measurement**, not a knob.

### Tier 0 — free, do now (corrections; no parameter moves)

1. **Fix the citation** everywhere it appears (`FRI-PARAM-FRONTIER.md:11-13,122-124,262-263`;
   `HORIZONLOG.md`; `docs/deos/CRATE-EXCELLENCE-PLAN.md`; `GOAL-MULTICHAIN-SETTLEMENT.md`; memory
   `project-linking-tower-forgery-closure.md`). Suggested replacement:
   > The up-to-capacity correlated-agreement conjecture is refuted (Crites–Stewart eprint 2025/2046,
   > impossibility via list-decoding; Diamond–Gruen eprint 2025/2010, counterexample at rate→0; BCHKS
   > ECCC TR25-169 Thm 1.6, counterexample at constant rate in char 2; Kambiré arXiv 2604.09724,
   > counterexample over prime fields at ρ∈(0,½) within Ω(1/log n) of capacity). **None instantiates at
   > BabyBear**: DG needs rate→0, BCHKS needs characteristic 2 and a random F₂-subspace domain, Kambiré
   > needs a ~2^1024-bit prime chosen per n. The capacity ledger is dead as a security target
   > regardless — a refuted conjecture cannot be a basis — which is why it is carried only as a drift canary.
2. **Re-point the proven citation from BCIKS20 to BCHKS25** (ECCC TR25-169) in
   `fri_params_soundness_budget.rs` and `FRI-PARAM-FRONTIER.md` §1a. **Under BCIKS20 — the paper we
   actually name — the deployed wrap proves ~70, not 73.** BCHKS25 is what makes 73 defensible.
3. **Withdraw or re-label Frontier B** (§3.1): "proven Johnson 128 at (lb=8, q=28)" is unreachable at
   ext-degree 4 under the real ε_C.
4. **Re-price arity in the doc** (§3.3): ~0.15 end-to-end bits, not 2.807; and the "+9%" is measured at
   v1's config, ≈+16–20% at deployed.
5. **Rename or comment `wrap_perFold_soundness_capacity`** (§1.4) — it is a bespoke dim-2 count, not an
   instance of the refuted capacity conjecture, and its name invited the bad headline.

### Tier 1 — cheap engineering, high value

6. ~~**⚑ MEASURE the deployed trace-height distribution.**~~ **DONE 2026-07-15 — see §3.2a.** The
   answer is worse than this item assumed: the deployed worst case is **|D⁽⁰⁾| = 2^19** (the
   `WRAP_LOG_CEIL = 16` recursion ceiling, forced on every fold), not the 2^12 fixture — so the real
   proven posture is **~64 bits**, ~7 below the gate's own `JOHNSON_FLOOR_BITS = 71`. Gated
   non-rottingly by `circuit-prove/tests/fri_trace_height_measure.rs`.
7. **⚑ Mechanize ε_C as a real column in `Dregg2.Circuit.FriLedger.friLedger`**, beside the naive
   `q·lb/2 + pow`, so the gate reports it rather than a scratch script. Three independent
   implementations agreeing at ~70 (§2.1) is exactly the point at which this should stop living in Python.
8. **`pow 16 → 20` on every shipped config.** **+3.29 proven bits, 0 wire, 0 verify**, 16× a
   microsecond grind.
   ⚠ Unlike the earlier lane claim, **the grind is per-proof** — so stop at 20 (or measure before 24).
   ⚑ **REFUTED as a FIX for `create_recursion_config`, by §3.2a's measurement.** This item claimed pow
   20 "fixes" the weakest link. At that config's **measured** |D⁽⁰⁾| = 2^19 it does not: pow 14 → 63.91,
   pow 16 → 65.54, pow 20 → **67.55**, and the lever then **saturates** — pow 24 → 68.48, pow 27 →
   68.48, *the same number*. **No pow value reaches the gate's own 71 floor at the real height**, because
   ε_C's commit column binds and the `min` in eq. (20) stops moving (§3.1's ceiling, now biting a shipped
   config rather than a hypothetical). The +3.29 is real and still worth taking (0 wire), but it is a
   *mitigation*, not a fix. Reaching 71 at the recursion needs the **height** (lower `WRAP_LOG_CEIL`, at
   the cost of the depth-invariant VK — see §3.2a) or **BCHKS25**'s O(n) (§2.2), not the pow knob.
   The lane 2 figure of 70.49 for this config is a **2^12-height** reading; at 2^19 it is 63.91.
9. **Instantiate BCHKS25 Thm 1.5 in Lean at the 7 shipped configs** and compute **the BCHKS25 ceiling**
   (§3.1) — the most valuable missing number here. Likely a larger win at ρ = 1/8 (`ρ^{-3/2} = 22.6`)
   than at ρ = 1/64 (512).
10. **Write the Crites–Stewart check against the dim-2 counting bound** (§1.4). Our defence is checked
    against Kambiré only.

### Tier 2 — real engineering

11. **⚑ Close the M=1 fiber-discharge radius gap** (§4.1) — the sharpest open item. The discharge needs
    96.9% farness; FRI needs 87.5%. If it is real, the deployed per-fold 109 is still hypothesis-carrying
    in the band that matters. Note §4.3: the s=2 instantiation is conservative, so there is room.
12. **Extension degree 4 → 8** is the **only** lever that raises the ceiling (77.98 → 201.60), and
    plonky3 supports it **today** (prefer 8 over 5: two-adicity 30 vs 27). The cost is the wrap:
    degree 4 is hardcoded at `dregg_outer_config.rs:125` (`pub const OUTER_EXT_DEGREE: usize = 4`) **and**
    `chain/gnark/babybear_ext_ref.go:7` (`type bbExtRef [4]uint32`) — a gnark-circuit rewrite + full VK
    re-key across every consumer. **Do not start this before item 6**: if real traces are tall, the
    ceiling matters much more than it looks; if short, less.
13. **`lb 6 → 7`** is the proven optimum at q = 19 (+6.37 bits, +4.4 KiB, ~2× prover). **`lb = 8` is
    worse than `lb = 7`** — the naive ledger's monotone reading is wrong by ~17 bits there.

### Tier 3 — research frontier

14. **The GG folded-RS question** (§5.1): does GG's capacity gap transfer to a coset-RS code whose
    queries already reveal size-8 cosets? If yes, it is the only path past Johnson at zero proof-size
    and zero prover cost. Plausibly very hard.
15. **Track BCHKS25 Thm 1.9** — the only universal, escape-hatch-free barrier: gaps stop at the
    list-decoding radius with error ≥ 1/(2n) that *"cannot be reduced by increasing q"*. **It means the
    Johnson→capacity window can never be generically reclaimed — so the 73/71 Johnson floors are
    structurally the right thing to stand on, not a temporary posture.** `HORIZONLOG.md:504`'s
    TERMINAL-FLOORS entry still frames "FRI capacity conjecture" as a floor in good standing; it is a
    **refuted** one that we correctly do not rely on, and the entry could say so.

### What NOT to do

- **Do not adopt eprint 2026/858** ("above the Johnson bound"): **73 → 34.6** at our deployed config
  (§2.4). It is above Johnson in *radius*, not in *bits*, and is worst exactly at low rates.
- **Do not adopt 2026/861**: self-described "Rigorous" but reduces to an unvetted conjecture (Q2).
- **Do not adopt STIR/WHIR/BaseFold** for soundness: same Johnson ceiling, asymptotic-in-degree win we
  are too small to collect, no gnark verifier, prototype-grade code (§5).
- **Do not buy queries alone**: q saturates at ~25; q = 200 proves the same 77.98 as q = 25 (§3).
- **Do not treat arity as a security lever** in either direction (§3.3).
- **Do not lean on "BabyBear⁴ is a prime power, so it is in neither counterexample family"** (§1.2).
  It is true and it is not a defence. The Johnson posture makes it moot.

**If the one-line answer is wanted:** *fix the citations, mechanize ε_C, measure the trace heights,
grind pow to 20 — and keep standing on Johnson, which the literature now proves is where the floor is.*

---

## 7. ⚠ Uncertain / unfetched — every gap, flagged

**Blocked by infrastructure.** `eprint.iacr.org` serves a Cloudflare interstitial/403 to curl and
WebFetch for **every** `/YYYY/NNN.pdf`; abstract landing pages render fine. So for **Crites–Stewart
2025/2046**, **S-two 2026/532**, **SoK 2026/1367**, **Chai–Fan 2026/858 & 2026/861**, **Goyal–Guruswami
2025/2054**, **Haböck 2024/1571 & 2025/2110**, **STIR 2024/390**, **WHIR 2024/1586**, and **Diamond–Gruen
2025/2010** we have **abstracts only**. Fetched in full: **Kambiré** (arXiv, both pages), **BCHKS ECCC
TR25-169** (Kopparty's faculty page), **BCIKS20** and **Haböck 2022/1216** and **BaseFold 2023/1705**
(local IACR mirror `~/dev/gh/forks/IACR-eprint-mirror/`), **DG25b** (cic.iacr.org).

**Highest-value remaining fetches, in order:**
1. **⚑ S-two whitepaper eprint 2026/532, Appendix A.5** — StarkWare's *current post-Kambiré replacement
   posture*, and explicitly about **curve-decodability**, which is exactly our arity-8 question. Known
   only via Kambiré's one-sentence description of his ref [3]. **Fetch by hand in a browser.**
2. **SoK 2026/1367 body** — its production-systems survey is exactly what would settle whether
   plonky3/Risc0/SP1/Plonky2/Winterfell changed parameters.
3. **Crites–Stewart 2025/2046 body** — no theorem-level detail at all; its "minimal modifications" are
   the candidate **replacement assumption** and are unread. Needed for the §1.4 check (item 10).
4. **Goyal–Guruswami 2025/2054** — the **folding parameter** requirement for FRS is not in the abstract.
   Whether their capacity gap holds at s = 8 could kill §5.1 outright.

**Numbers that are ours, not the papers':**
- The ε_C recomputation (**70.11 / 77.98 / ceilings / lb turnover / trace sensitivity**) uses BCIKS20's
  verbatim formula but **my** arithmetic, **unmechanized** (`scratchpad/eps_c.py`). ⚠ It **omits
  ethSTARK eq. (20)'s DEEP/ALI top-row terms**, so every proven figure here is an **optimistic upper
  bound**; the true posture is somewhat lower. The **ranking and the ceiling's existence are robust**
  (they follow from ε_C's m⁷ and 1/|F| structure). Lanes 2 and 4 got 70.47 and 70.11 by independent
  implementations; my lb=7/lb=8 constants (76.48/74.98) differ from lane 4's (74.48/70.98) — **the
  turnover shape is robust, the constants are not.**
- ~~**|D⁽⁰⁾| is assumed**, not measured~~ — **now MEASURED (§3.2a)**, off real proofs' `degree_bits`.
  The assumed anchors were both wrong: the 2^12 "fixture" is the system's *smallest* real trace (it is
  `MIN_TRACE_HEIGHT`, not a fixture), and the 2^20 "tall anchor" was hypothetical while the **real**
  deployed worst case — 2^19, the `WRAP_LOG_CEIL` recursion ceiling — was already shipping on every
  fold. The ε_C *formula* is now also verified verbatim against BCIKS20 Lemma 8.2/Thm 8.3 and the
  composition against ethSTARK eq. (20), and this doc's arithmetic reproduced a 4th time (70.11 @ m=7,
  61.98 @ 2^20, both exact). What remains ours-not-the-papers' is unchanged: the DEEP/ALI omission
  (so every figure stays an **optimistic upper bound**) and the unmechanized arithmetic (item 7).
- Lane 1's Kambiré instantiation (ρ=1/64, C=1 → p ∈ [2^1024, 2^1536]) and BCHKS25 Thm 1.5 constant
  (≈2^-86 at ρ=1/64) follow the papers' formulas but **appear in neither paper**; the 2^-86 vs 2^-83.6
  comparison uses a **naive** O(n²) incumbent without BCIKS20's actual constant, so **the net-gain
  question is genuinely open**.
- The **pow-27 grind estimate (0.2–1.7 s)** is extrapolated from packed-Poseidon2 throughput, **not
  measured**. The *per-proof* fact is verified (`prover.rs:98`); the magnitude is not.
- The **arity +16–20%** projection is a Merkle-path model calibrated against **one** measured point (81%
  agreement). Directionally solid; needs a real measurement at `ir2_config`.

**Read but not proved:**
- §4.1 (fiber radius) and §4.2 (terminal-fold modeling) are reads of **statements** plus the composition
  through `arity8_good_card_le`. I did not read the proofs or trace every consumer, and may be
  misreading what `dOut` measures (input vs output word). **Flagged for a metatheory lane, not asserted.**

**Unresolved / not chased:**
- **BCHKS25 Thm 1.6 at τ = 1** gives γ = 1/2, *below* the Johnson radius where Thm 1.5 guarantees the
  opposite — an apparent contradiction. Most likely a misreading of a constraint (the paper highlights
  τ=2 as the tight case). **Only the unambiguous τ=2 (ρ=1/16) and τ=4 (ρ=1/64) instances are used here;
  no conclusion rests on τ=1.**
- **BCHKS25's venue**: search surfaced STOC 2026 (DOI 10.1145/3798129.3800827, "of" vs the preprint's
  "for"); dl.acm.org 403'd. **Cite the ECCC report, not STOC.**
- **[GGM25] Garreta, Gruen, Manzur, *Attacking FRI and the STARK toy problem*** — in BCHKS25's
  bibliography as a **personal communication**, no URL. It is an **attack paper on FRI**, directly
  adversarial to our posture. Not located. **Worth a search.**
- **[Hab25] Haböck, *A note on mutual correlated agreement*** — also a personal communication, no URL.
- **[Krachun & Kazanin]** — Kambiré's ref [4], unpublished personal communication; **his paper is the
  public record of that sketch.**
- **eprint 2024/1512** (Gao, Kan, Li — improved FRI soundness, linear proximity gaps) was **WITHDRAWN**
  2024-10-02, six days after receipt. **Not citable; must not enter the ledger.** Its headline claim was
  later achieved properly by BCHKS25 — the result is real, the citation must be BCHKS25.
- **NOT ESTABLISHED**: whether plonky3 (rev `82cfad73`), Risc0, SP1, Plonky2, or Winterfell changed FRI
  parameters in response. **No primary evidence either way.** The only citable practitioner response is
  StarkWare's (BCHKS authorship + S-two Appendix A.5, unfetched). Two lanes explicitly **discarded Kagi
  FastGPT output** asserting ecosystem parameter changes — unsourced, uncorroborated.
- **EF "Proximity Prize"** (~seven figures, judges said to include Boneh and Fenzi): from a search
  summary only; the one page fetched predates the disproofs and is stale. **Do not cite without verification.**
- **Not investigated at all**: circle-STARK / Mersenne31 / Stwo-line proximity results (2026/858
  mentions "the unit circle via the Stwo coupling"); Binius/binary-tower; arXiv 2605.07595
  (syndrome-space, random linear codes); eprint 2026/310 (*Bolt: Faster SNARKs from Sketched Codes*).
- **Confabulation warning**: a search summary asserted a "Bordage et al. result … shows that pushing
  STIR beyond Johnson bound is provably impossible." **Could not locate or verify**, and the second half
  contradicts 2026/858 existing at all. **Not relied on anywhere above**; flagged because it will
  resurface if these queries are re-run.

---

## 8. ⚑ THE `[Sta25]` DEPENDENCY IS ELIMINABLE FOR FRI — the bits are PARTIALLY EARNED (2026-07-16)

Item 2 of §6 ("re-point the proven citation to BCHKS25") and §3.1's missing BCHKS25 ceiling were
BLOCKED on the same worry the tree records verbatim: BCSS25's improved `O(n)` bound enters FRI only
through a WEIGHTED correlated-agreement theorem (its Corollary 4.4) whose proof it defers to
**`[Sta25, Theorem 22]` — the StarkWare S-two whitepaper, a personal communication we cannot read**.
`FriLedger.lean` refuses to bank a security number on an unreadable citation, correctly.

**This section retires that block by PROVING the underlying transfer instead of citing it.** The full
line-by-line derivation, cross-checked against the primary sources, is
[`BCSS25-COMMIT-DERIVATION.md`](./BCSS25-COMMIT-DERIVATION.md) (codex-drafted, checked here against
BCSS25 Lemma 3.1 / §3.2 / Thm 4.2 and BCIKS20 §7.1–7.2). The load-bearing half is mechanized in
`metatheory/Dregg2/Circuit/FriWeightingTransfer.lean` (kernel-clean, `#assert_axioms`-clean).

**The finding (both halves verified independently, by hand-reading the PDFs and by a codex constant
reconstruction that reproduces BCSS25 Thm 4.2 exactly):**

* **The weighting transfer is `[Sta25]`-free.** BCIKS20 §7.1 derives its weighted curve theorem
  (Thm 7.2) from the UNWEIGHTED one plus a single structural fact — **co-curvilinearity on a large set
  `S′`** (the found codewords `v₀…v_l` satisfy `∑ zʲ vⱼ = P_z` for every `z ∈ S′`, its Prop 5.5) — via
  **Lemmas 7.5/7.6, elementary double-counting** (BCIKS20 §7.2, fully public, mechanized here as
  `weighting_transfer_double_count` / `weighting_transfer_bound`). BCSS25 §3.2 **Step 4** PROVES exactly
  that co-curvilinear `S′` with the IMPROVED `O(1)`-`Z`-degree interpolant — making `S′` only larger.
  So the weighted bound FRI's round analysis consumes is reachable by feeding BCSS25's improved `S′`
  into BCIKS20's public transfer. The `[Sta25]`-backed **Theorem 4.3** (arbitrary prescribed agreement
  sets `{A_z}`) is a STRONGER statement the FRI application does **not** need.

* **Scope, audited against over-claiming.** The public route closes for the **denominator-bounded**
  weights FRI uses (`µ⁽ⁱ⁾` = subtree-acceptance probability, denominator `M = |D⁽⁰⁾|/|D⁽ⁱ⁺¹⁾|` — on the
  rational grid `1/(M|D|)ℤ`, so Lemma 7.6's rounding removes the loss) — **NOT** for BCSS25 Cor 4.4 in
  its full stated generality (arbitrary real weights, no grid, where Thm 4.3 is genuinely doing extra
  work). The honest claim is *"`[Sta25]` is eliminable for the FRI application"*, not *"the public
  ingredients reproduce Corollary 4.4"*. `FriWeightingTransfer` mechanizes the general (lossy) Lemma
  7.5 **and, as of 07-16, the denominator-rounding Lemma 7.6** that removes its loss
  (`weighting_transfer_rounded`); the remaining residual is `CoCurvilinearity` (see below — the `Prop`
  was vacuous as first stated and has been corrected).

* **The improved `ε_C` is genuinely LINEAR in `|D⁽⁰⁾|`.** The constant reconstruction pins it to
  `|S| > d·( 2(m+½)⁵/(3ρ^{3/2})·n + (m+½)/√ρ·(W·n+1) )` — reproducing Thm 4.2 at the unweighted target
  `W=1, T=d(γn+1)`, so all factors `2, 3, d, ρ` are checked. The former-quadratic term
  `(m+½)⁷|D⁰|²/(2ρ^{3/2}|F|)` becomes linear; the weighting term was already linear.

* **⚑ THE BITS, HONESTLY — `+1.7 … +7`, NOT `+17 … +31`.** §3.1 estimated the win at `~log₂|D⁽⁰⁾|`.
  Recomputed with the linear `ε_C`, composed through ethSTARK eq. (20), optimized over `m ≥ 3`:

  | config | old (BCIKS20, optimized) | new (public linear `ε_C`) | gain |
  |---|---:|---:|---:|
  | wrap `|D⁰|=2^19`, `ρ=1/64`, arity 8 | 63.98 | **71.00** | **+7.02** |
  | leaf `|D⁰|=2^12`, `ρ=1/64`, arity 2 | 70.11 | **71.76** | **+1.66** |
  | outer `|D⁰|=2^18`, `ρ=1/8`, arity 2 | 65.91 | **71.44** | **+5.53** |

  Two reasons the raw `~+21`-bit leading-term improvement collapses to `~+7` after composition: (i)
  once `ε_C` clears the query column, the `min` in eq. (20) is set by `ζ − s·log₂ α ≈ 72`, so the
  composed bits **saturate at the query ceiling** — the commit term is no longer what binds; (ii) the
  arity-8 fold is a degree-`7` CURVE, and BCSS25's public curve theorem (Thm 4.2) requires the
  multiplicity parameter `m = 2h` where the binary line (Thm 1.5) allows `m = h`, inflating the
  `(m+½)⁵` constant. The win is real, robust at low rate, and modest.

**Residual (public, names no personal communication) — RE-SCOPED 2026-07-16, and it is LARGE.** The
earlier text here said the residual was "`~15` pages of Guruswami–Sudan analysis over `𝔽_q(Z)`, PROVED
in BCSS25 §3". Read against the primary source, that is **wrong in a way that matters**: BCSS25 §3.2
does not prove Step 4. It opens by calling itself *"a brief summary of the steps from **[BCI⁺20,
Section 5]**… the underlying field is the field of rational functions `K = 𝔽_q(Z)`, and the required
finite extension is an **algebraic function field**, which makes concrete computations **quite
technical**"*, and Step 4 says outright: *"Reaching this conclusion is **the major part of the proof,
comprising sections 5.2.5 – 5.2.7 as well as Appendix A of [BCI⁺20]**."* BCSS25 §3.2's own contribution
is the BOOKKEEPING (`2D_X D_Y³ D_Z` → `2D_X D_Y² D_Z + (γn+1)D_Y`). **The `[Sta25]`-free headline
survives** — BCI⁺20 is public (eprint 2020/654) — but the obligation is a Hensel lift over an algebraic
function field, not 15 pages of bookkeeping.

**⚑ And the named residual `Prop` was VACUOUS.** `FriWeightingTransfer.CoCurvilinearity` quantified
`∃ v` over ARBITRARY words, with the codeword constraint only in a docstring aside ("tracked by the
caller" — nothing tracked it). `v := u` proves it outright; the advertised "concrete falsifier" refuted
the matrix of an existential, not the existential. Discharging it as stated would have earned **zero
bits**. Fixed 07-16: it now carries `∀ j ≤ l, IsRSCodeword pt k (v j)`, and non-vacuity is PROVED by a
falsifier theorem, with the unconstrained shape retained as a tooth proving it *was* a theorem.

**Mathlib gap, scoped (the feasibility answer).** No coding theory whatsoever (no RS, no linear codes,
no minimum distance, no Johnson, no list decoding). `MvPolynomial.weightedTotalDegree` has a definition
and four lemmas — no `_mul_le`, and the GS degree bound *is* a statement about weighted degree of
products. **No bivariate multiplicity** (no multivariate Hasse derivative, no MvPolynomial Taylor
shift) — the deepest hole. No bivariate root extraction. What IS free: the interpolation-by-counting
step (`LinearMap.ker_ne_bot_of_finrank_lt` + `MvPolynomial.basisMonomials`), bivariate polys, and
`RatFunc F` for `K = 𝔽_q(Z)`. **GS layer alone ≈ 3000–6000 lines; the Hensel lift sits on top. This is
multi-month-to-paper, not a week.**

**Banked instead (07-16): BCIKS20 Lemma 7.6 is now mechanized** (`OnGrid`, `grid_round`,
`weighting_transfer_rounded`) — the grid rounding that removes Lemma 7.5's loss, previously asserted in
prose while only the lossy 7.5 was proved. Given `CoCurvilinearity`, FRI's denominator-bounded weights
now yield `µ(D′) ≥ α` EXACTLY (`exact_weighted_agreement_of_coCurvilinear`), the shape Lemma 8.2
consumes. **The verdict: `61` stands, and the `+7` is NOT banked. It is not "what we can prove until
StarkWare publishes [Sta25]" — it is "what we can prove until someone mechanizes BCI⁺20 §5's Hensel
lift, all of whose ingredients are public."**

---

*Sources fetched in full: Kambiré arXiv:2604.09724; BCHKS ECCC TR25-169; BCIKS20 eprint 2020/654;
Haböck eprint 2022/1216; BaseFold eprint 2023/1705; DG25b cic.iacr.org 1/4/8; zksecurity (Mohnblatt,
2025-11-14). §8 (2026-07-16): BCSS25 = ECCC TR25-169 read in full (Lemma 3.1, §3.2, Thm 4.2/4.3, Cor
4.4); BCIKS20 §7.1–7.2 + Lemma 8.2 read in full; the weighting transfer (Lemma 7.5) mechanized in
`Dregg2/Circuit/FriWeightingTransfer.lean`; constant audit in `BCSS25-COMMIT-DERIVATION.md`. Code
verified verbatim at plonky3 rev `82cfad73`. Recomputation: `scratchpad/eps_c.py`. This document's
§0–§7 change no deployed parameter and no Lean; §8 adds one Lean module (the `[Sta25]`-free transfer)
and changes no deployed parameter.*
