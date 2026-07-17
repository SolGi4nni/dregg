# FRI-BOTH-WIN-LEVERS — where security and speed move the SAME direction

**What this is.** ember's question: *most FRI levers trade off (queries and PoW buy bits, and cost size
and time) — but do any buy **both**? And if plonky3 will not do what we want, are there **good reasons**,
or is it an arbitrary gap?* This doc answers both, from primary sources and from the pinned prover source.
It succeeds [`FRI-SOUNDNESS-FRONTIER-RESEARCH.md`](./FRI-SOUNDNESS-FRONTIER-RESEARCH.md) (**the
baseline**) — which corrected us, and which this doc **corrects in turn, at five places**.

**This document changes no parameter, no Lean, and no deployed config.** It is a research record.

**The two-column law holds throughout.** FRI soundness is a product of the **per-fold** proximity error
and the **query** ledger; `FriLedgerSound.query_ledger_does_not_determine_perFold` is a theorem. Nothing
below multiplies them. Every number is labeled with its column and its paper.

---

## 0. Headline

**Yes, both-wins exist, and they have a mechanism rather than being a coincidence. But the biggest one is
an artifact of the paper we cite — and the SOTA that dissolves it is already implemented inside the
plonky3 rev we pin.**

1. **⚑ The mechanism.** `|D⁽⁰⁾| = trace_height × 2^lb` is **simultaneously** the prover's LDE work unit
   (prover ≈ `O(width · |D⁽⁰⁾| · log)`) and the numerator of the FRI commit-phase error
   (`ε_C ∝ |D⁽⁰⁾|²/|F|`). **Anything that shrinks the evaluation domain buys prover time AND proven
   bits.** The wire pays, because a smaller domain means fewer bits per query. That is the answer to
   ember's question in one line — and it is why the both-wins are *exactly* the two knobs inside `|D⁽⁰⁾|`.

2. **⚑ We have been pricing the wrong artifact — by 12 bits.** The baseline headlines **70.11 proven
   bits**. That is a **2^6-row leaf**. The artifact that travels to a light client is the **recursion
   apex**: tables floored at `WRAP_LOG_CEIL = 16` (`circuit-prove/src/accumulator.rs:238`), running at
   `log_blowup 6` (`circuit-prove/src/joint_turn_recursive.rs:435`) ⟹ `|D⁽⁰⁾| = 2^22` ⟹ **57.98 proven
   bits under BCIKS20**, not 70.11.

3. **⚑ At the apex, the cheap levers buy EXACTLY ZERO.** `ε_C` and the query ledger compose as a `min`
   (ethSTARK eq. 20). Below trace ≈ **2^11.1** the query term binds and trace height is worth ~0; above
   it `ε_C` binds and **queries and PoW are worth 0.00**. The apex is 5 doublings above. **So the
   baseline's single Tier-1 "do this now" item — "`pow 16→20`, +3.29 bits, 0 wire, 0 verify" — is worth
   `+0.00` on the proof anyone actually verifies.** It is a real lever, on the leaf only.

4. **⚑ plonky3's degree-6 gap is ARBITRARY — and degree 6 does not panic, it does not compile.** No
   mathematical and no SIMD reason. **X⁶ − 22 is irreducible over BabyBear** (Rabin-verified;
   `W₆ = 22 = 11 × 2`, literally plonky3's own d=4 and d=8 constants multiplied), all five required
   constants are computable **and were computed** (§3), a generic schoolbook fallback **already ships**
   for Mersenne31 and Goldilocks, and 4-lane NEON **already runs degree 5**. When math genuinely blocks
   plonky3 it builds a workaround (KoalaBear's `TrinomialQuinticData`). For BabyBear degree 6 nothing
   blocks. **Nobody needed it.**

5. **⚑ A better code is a dead end, and the repo's open question is now CLOSED with a counterexample.**
   Goyal–Guruswami needs folding parameter `s ≳ 16/η²` — **an alphabet of ~1764 field elements just to
   break even with what BCIKS20 proves for free at s=1**, and at our trace sizes the alphabet **exceeds
   the entire codeword** (the code does not exist). And FRI's coset is **provably not** a folded-RS
   bundle: the structure that makes FRI foldable is the structure that destroys the capacity gap (§5).

**⚑ THE FINDING THAT DECIDES WHAT WE DO.** The `|D⁽⁰⁾|` both-wins exist **only under BCIKS20**. Under
**BCSS25** — same authors, *the SOTA* — `ε_C` is **linear in n, not quadratic**, and:

| | BCIKS20 (what our code cites) | BCSS25 (SOTA) |
|---|---|---|
| apex proven | **57.98** | **~70.9** |
| trace-height slope | **−2.000/doubling** | ~−0.2 to −0.4/doubling |
| **best `lb` @ q=19** | **7** (74.48) — *lower `lb` raises the ceiling* | **8** (85.37) — *higher `lb` is better* |

> **The paper we cite decides the SIGN of both `|D⁽⁰⁾|` levers.** Under BCIKS20, shrink the domain
> (both-win). Under BCSS25, the domain barely matters, the classic trades return — and **our deployed
> "raise blowup, cut queries" design is vindicated rather than backwards.**

**And the SOTA is already in our dependency tree.** `p3-whir` transcribes BCSS25 Thm 1.5 verbatim
(`whir/src/parameters/soundness.rs:99-123`); **`p3-fri` still cites BCIKS20** (`fri/src/prover.rs:25-31`)
and offers only `rate^q` / `rate^{q/2}`. **The improved theorem exists in Rust, in the rev we pin, in the
wrong module.** ⚠ It is a *proximity-gaps* bound, not a FRI composition — that composition is still ours
to write (§1.4).

**So the one-line answer:** *the both-win is real and it is `|D⁽⁰⁾|`; but before spending engineering on
it, settle §1.4 — because under the better paper it mostly evaporates, and that paper is sitting in
`whir/src/parameters/soundness.rs`.*

---

## 1. ⚑ Trace height as a security lever — the ε_C form, VERIFIED

### 1.1 The theorem, verbatim (the baseline's formula is CORRECT)

Transcribed independently from the local mirror `~/dev/gh/forks/IACR-eprint-mirror/2020/654.pdf`,
**BCIKS20 Thm 8.3, p. 41** (Lemma 8.2, p. 40) — Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity
Gaps for Reed–Solomon Codes*, JACM 10.1145/3614423:

> **Theorem 8.3 (Batched FRI Soundness).** … Let `α = √ρ(1 + 1/2m)` for integer `m ≥ 3` … Let
> `l⁽ⁱ⁾ = |D⁽ⁱ⁾|/|D⁽ⁱ⁺¹⁾|` … `s` is the number of invocations of the FRI QUERY step. … accept with
> probability greater than
>
> `ε_FRI := ε_C + αˢ = (m+½)⁷·|D⁽⁰⁾|²/(2ρ^{3/2}|F|) + (2m+1)(|D⁽⁰⁾|+1)/√ρ · (Σ_{i=0}^{r−1} l⁽ⁱ⁾)/|F| + (√ρ(1+1/2m))ˢ`

**The baseline's transcription is correct, character-for-character.** Two independent transcriptions
agree, and the implementation **reproduces the paper's own worked example on p. 41** (q ≥ 2^256, n = 2^20,
ρ = 2^-4, m = 2^11−1, s = 65): ε_C = 2^-134.00 vs the paper's *"< 2^-133"*; α^65 = 2^-129.98 vs their
*"≈ 2^-129.97"*. A second implementation independently reproduces **ethSTARK's** own worked example
(eq. 21, p. 40): λ = 80.43 vs the paper's 80. **The formula is settled.**

The five questions put to the source:

1. **The leading term is genuinely `|D⁽⁰⁾|²/(2ρ^{3/2}|F|)`** — quadratic, and `D⁽⁰⁾` is the **first and
   largest** domain (`D⁽⁰⁾ ⊋ … ⊋ D⁽ʳ⁾`, p. 39; `ρ = (k⁽⁰⁾+1)/n⁽⁰⁾`), i.e. **`trace_height × 2^lb`**. The
   round-sum lives **only in term 2**, because per-round errors decay geometrically (the proof, p. 44,
   bounds `Σ(l⁽ⁱ⁾−1)/(l⁽⁰⁾···l⁽ⁱ⁾)² ≤ ½`; `3/2 · 1/3` is where the `2` in `2ρ^{3/2}` comes from). **Term 2
   never matters at our params** — 23–37 bits below term 1.
2. **The exponent is 7**, `m ≥ 3` **integer**. `m` is the Johnson-tightness knob: `m → ∞` drives `α → √ρ`
   (the best query rate) but `ε_C ∝ m⁷`. That tension is the whole story — **and the naive `q·lb/2` ledger
   silently assumes `m → ∞`.**
3. `s` = query count; `l⁽ⁱ⁾` = the folding arity.
4. **Only two terms**, and Thm 8.3 **is already** the batched/correlated-agreement variant. Its conclusion
   is a *correlated agreement* statement, not soundness — **ethSTARK eq. (20) composes**:
   `λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1`.
5. **Yes — genuinely quadratic.** But the `min` decides whether that matters (§1.3).

### 1.2 ⚑ THE MASTER EQUATION — every ε_C lever in one line

Once `ε_C` binds the `min`, it is maximized at `m = 3` (it grows as `m⁷`):

```
−log₂ ε_C = log₂(2|F|) − 7·log₂(m+½) − 2·log₂(T) − 3.5·lb        [T = trace height]
```

because `|D⁽⁰⁾|²/ρ^{3/2} = T²·2^{2lb}·2^{1.5lb} = T²·2^{3.5·lb}`. At `m = 3`, `7·log₂(3.5) = 12.651`; eq.
(20) subtracts 1. So at extension degree `d` over BabyBear (`log₂ p = 30.907`):

> ### **PROVEN CEILING = 30.907·d − 12.65 − 2·log₂(T) − 3.5·lb**

**Derived, not fitted** — it reproduces every ceiling in the baseline exactly (77.98 at d=4/T=2^6/lb=6;
201.60 at d=8). It is the whole lever map:

| lever | effect on the ceiling | effect on the prover |
|---|---|---|
| **extension degree `d`** | **+30.91 bits per degree** | ~1.3–1.6× slower at 4→8 (§3.5) |
| **trace height `T`** | **+2 bits per halving** | **~2× faster per halving** ⟸ **BOTH-WIN** |
| **log_blowup `lb`** | **+3.5 bits per decrement** | **~2× faster per decrement** ⟸ **BOTH-WIN** |

**The two both-wins are exactly the two knobs inside `|D⁽⁰⁾|`** — not a coincidence: `|D⁽⁰⁾|` is what the
prover does FFT work over and what `ε_C` is quadratic in. `d` is the odd one out — a pure trade (buys
ceiling, costs arithmetic), which is why it is *not* a both-win despite being the largest number here.

⚠ **This equation is BCIKS20's. Under BCSS25 the `2·log₂(T)` becomes `1·log₂(T)` and the `3.5·lb` becomes
`2.5·lb`** — which is exactly why the levers change sign (§1.4).

### 1.3 ⚑ The `min` gates everything: two regimes, and we sit on the boundary

`λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1` means **only the binding column has levers**:

| regime | binds | trace height | lower lb | more queries | more PoW |
|---|---|---|---|---|---|
| **ε_C-bound** (tall trace / high lb / low `d`) | `ε_C` | **+2.00/halving** | **+3.5/step** | **ZERO** | **ZERO** |
| **query-bound** (short trace / low lb / high `d`) | query | **ZERO** | −`lb/2` per query | works | works |

**Crossover: trace ≈ 2^11.10** at the deployed `lb=6, q=19, pow=16`. Verified by two independent
implementations.

- **The deployed leaf (T = 2^6) sits 0.17 bits from the boundary** (`ε_C` 71.28 vs query 71.11) — which
  is why the baseline, which only ever priced the leaf, saw the query column and concluded PoW was the
  cheap lever. **At the leaf, it is.**
- **The apex (T = 2^16) is 5 doublings past the crossover.** There, PoW and queries are worth **exactly
  0.00**, and only `|D⁽⁰⁾|` moves the number.

⚑ **This resolves the baseline's internal contradiction.** Its §3.2 asserts *"proven bits fall ~2 per
trace doubling"*, but its own two anchors (70.11, 61.98) span 8.13 bits over 8 doublings ≈ **1.02**.
Neither is the slope. **The slope is piecewise:** ~0 below the crossover, **exactly 2.000** above. The
baseline quoted the asymptotic slope as if it were the local one at its fixture.

### 1.4 ⚑ THE FORK — the levers exist only under the paper we cite

**BCSS25** = **BCHKS25**: *the same paper in two venues* — **eprint 2025/2055** / **ECCC TR25-169**,
*On Proximity Gaps for Reed–Solomon Codes*, Ben-Sasson, Carmon, Haböck, Kopparty, Saraf, Nov 2025. It
improves the exception bound from `O(n²/η⁷)` to `O(n/η⁵)`. **Thm 1.5 / Thm 4.2 / Cor 4.4 (ECCC p. 27):**

```
a > (2(m+½)⁵ + 3(m+½)·γ·ρ)/(3ρ^{3/2}) · n  +  (m+½)/√ρ        [m = max(⌈√ρ/(2η)⌉, 3)]
```

— **linear in `n`, and `(m+½)⁵` not `⁷`**. ⚑ **Cross-validated by two fully independent routes**: read
verbatim off the ECCC PDF (p. 27), *and* transcribed by the plonky3 team into
**`whir/src/parameters/soundness.rs:99-123`** of the rev we pin — **character-for-character identical.**

plonky3's own table, verbatim from that file:

| Reference | Bound on exceptional z's | Proximity loss |
|---|---|---|
| `[BCI+20]` | `O(n^2/eta^7)` | 0 |
| `[BCSS25]` | `O(n/eta^5)` | 0 |

> *"The improvement factor of `n*eta^2` translates to approximately `log_2(n)` additional bits of provable
> security, **enabling 128-bit security with degree-5 extensions of KoalaBear**."* — `soundness.rs:120-121`

**⚑ And `p3-fri` does not have it.** `fri/src/prover.rs:25-31` still cites *"Proximity Gaps for
Reed-Solomon Codes (https://eprint.iacr.org/2020/654)"* and offers only `rate^{num_queries}` or
`rate^{num_queries/2}`. **The SOTA theorem is implemented in Rust, in the rev we pin, in the wrong
module.**

Composed into eq. (20) (my implementation, agreeing with a lane's to ~0.1 bits):

| trace | \|D⁽⁰⁾\| | **BCIKS20** (cited) | **BCSS25** (SOTA) |
|---:|---:|---:|---:|
| 2^6 (leaf) | 2^12 | **70.11** | 71.70 |
| 2^12 | 2^18 | 65.98 | 71.32 |
| 2^16 (**apex**) | 2^22 | **57.98** | **70.88** |
| 2^20 | 2^26 | 49.98 | 70.11 |
| **slope** | | **−2.000/doubling** | **~−0.2 to −0.4/doubling** |

And the sign flip on `lb` (trace 2^6, q=19, pow=16):

| lb | 3 | 4 | 5 | 6 | **7** | **8** | 9 | 10 |
|---|---|---|---|---|---|---|---|---|
| **BCIKS20** | 43.45 | 52.84 | 61.91 | 70.11 | **74.48** ⭐ | 70.98 | 67.48 | 63.98 |
| **BCSS25** | 43.48 | 52.98 | 62.44 | 71.70 | 80.02 | **85.37** ⭐ | 82.87 | 80.37 |

`ε_C^BCIKS ∝ T²·2^{3.5lb}` (cap falls 3.5/step) vs `ε_C^BCSS ∝ T·2^{2.5lb}` (cap falls 2.5/step), while
the query row rises 9.5/step either way. **The optimum moves 7 → 8, and the trace lever flattens.**

⚑ **And the baseline's diagnosis of this paper is REFUTED.** Its §2.2 claims *"the constants are brutal
at ρ = 1/64 … the O(n²)→O(n) win is largely eaten at our very low rate"*, reasoning from `ρ^{-3/2} = 512`.
**`ρ^{-3/2}` appears in BOTH bounds and cancels exactly.** The ratio is `(3/8)(m+½)²·n` = **14.2 bits at
|D⁽⁰⁾| = 2^12, 28.2 bits at 2^26** — the win is large and **grows with n**, i.e. it is *biggest exactly at
the apex*. BCSS25 looked like "+2 bits" only because **the query term caps at ~72** — the query ledger
eats the benefit, not the constants.

**So the fork is:**
- **Stand on BCIKS20** (verbatim-citable end-to-end, no assembly): apex = 57.98; shrink `|D⁽⁰⁾|`; `lb` down.
- **Stand on BCSS25** (SOTA; win biggest at the apex; transcribed in `p3-whir`): apex ≈ 70.9; trace height
  stops mattering; `lb` **up**; our deployed design vindicated.
  ⚠ **But BCSS25 does not restate a FRI soundness theorem.** It defers to [BCIKS20], [HLP24], [Sta25];
  "FRI" does not appear in its abstract, and `p3-whir`'s transcription is a *proximity-gaps* error for
  WHIR, not a FRI `ε_C`. **The composition is ours — unpublished, unrefereed (ECCC preprint), unmechanized.**

**The honest position: the apex is between 58 and 71 proven bits, and which it is depends on a
composition nobody has published.** That is the most consequential open item in this doc, and it is a
**mechanization** task, not a knob.

### 1.5 ⚑ Two structural facts about our own ledger

- **`ε_C` appears NOWHERE in the codebase.** `FriKnobs`
  (`circuit-prove/tests/fri_params_soundness_budget.rs:184-200`) carries `log_blowup, num_queries,
  query_pow_bits, max_log_arity, log_final_poly_len, ext_deg` — and **no trace-height field at all**
  (verified). **The deployed ledger is structurally incapable of expressing ε_C**, so it cannot see the
  strongest lever in this doc even in principle. Its `johnsonBits = 73` for the deployed config; the true
  eq-(20) number is **70.11**, and the cap (71.28) is within **0.2 bits** of binding. **The ledger is ~3
  bits optimistic *and* blind to the term about to bind** — exactly what commit `7e09d84a4` suspected.
- **⚠ The baseline's reproduction artifact does not exist.** It cites `scratchpad/eps_c.py`; the file is
  **absent from the tree and from `git log --all`** (verified). Two of its three "independent
  reproductions" of 70.11 are unreproducible. *(The number is fine — this doc reproduces it a fourth time,
  from the paper. But the citation was to nothing.)*
- Bonus: `conjectured_soundness_bits` (`fri/src/config.rs:42-44`) has **zero callers** and is `|F|`-blind.

---

## 2. Trace height in dregg: what drives it, and what it buys

### 2.1 ⚑ Two tiers, and the baseline priced the small one

| tier | artifact | max table | `\|D⁽⁰⁾\|` | proven (BCIKS20) |
|---|---|---|---|---|
| **leaf** (`ir2_config`, `descriptor_ir2.rs:5405`) | per-turn | chip ≈ 2^8 | 2^14 | ~66 |
| **apex** (`ir2_leaf_wrap_config`, lb 6 / q 19) | **travels to a light client** | **2^16** (floored) | **2^22** | **57.98** |

- **Leaf.** `main` is pinned at `MIN_TRACE_HEIGHT = 64` (`circuit/src/effect_vm/trace.rs:508`); `byte` at
  `2^4` (verify-side pinned, `descriptor_ir2.rs:337`); `chip` (Poseidon2) is one row per permutation and
  is **the max** — the deployed *rotated* leg has 130 sites
  (`metatheory/…/EffectVmEmitRotationV3.lean:394`, `#guard … == 130`) ⟹ `next_pow2(130) = 2^8`. So the
  leaf's `|D⁽⁰⁾|` is likely **2^14, not the baseline's 2^12**. ⚠ **Unmeasured** — no test pins the rotated
  leg's `degree_bits`. The `degree_bits [6,3,4]` the baseline used is a **real release measurement of the
  graduated v1 transfer**, not a fixture — but not of what we deploy.
- **Apex.** `degree_bits [9, 9, 15, 14, 15]`, **measured** and recorded in code at depth 2 *and* 3
  (`circuit-prove/src/accumulator.rs:225-227`). Then `WRAP_LOG_CEIL = 16` floors every running-proof
  table. **The code's own comment concedes the natural max is `2^15` and `2^16` is "a safe pad".**

### 2.2 ⚑ What does NOT drive it (two hypotheses from the brief, killed)

- **Constraint degree does not grow `|D⁽⁰⁾|` at all.** plonky3 blows each matrix up to *its own* height
  and rolls short ones into FRI later by bucket (`fri/src/two_adic_pcs.rs:607-613, 658`;
  `fri/src/prover.rs:238-245`); **only the max binds** (`two_adic_pcs.rs:475-480`), and quotient chunks
  land in the **same bucket as their trace** (`batch-stark/src/prover.rs:326-327`). **So the
  degree-vs-columns tradeoff is a prover-work tradeoff, NOT a proven-bits one — "pack rows, raise degree"
  buys ZERO bits.**
- **A narrower trace is NOT a soundness lever.** The DEEP/ALI term is `k/|EF|`
  (`two_adic_pcs.rs:557-564`, `k ≈ 2·width + quotients`) ≈ **2^-115 — 37 bits below binding.** Pure perf.
- **Padding across tables is free of `|D⁽⁰⁾|` risk** for the same reason. A 1-effect transfer pads 1 real
  row to 64 (**98.4% padding**) — real prover waste, **zero** proven bits, because `chip` is taller anyway.

⚑ **But `MIN_TRACE_HEIGHT = 64`'s justification is stale.** Its comment (`trace.rs:494-508`) reasons at
*"domain_size = 256 at blowup-4, 6 FRI rounds"* and *"80 queries"* — the deployed config is **blowup-64,
19 queries** (verified). A single-row-tamper heuristic, **never reconciled with ε_C**. Not a bug; an
unpriced constant.

### 2.3 ⚑ The padding cliff — a real, unnoticed both-win

`log2_strict_usize` panics on non-powers-of-two (`util/src/lib.rs:78-87`); heights round **up**. So a
table at `2^k + 1` rows pads to `2^{k+1}`: **2 proven bits and 2× the prover, for one extra row.**
**Keeping the tallest table just under a power of two is faster *and* more sound.** Width has no such
cliff. This is the cheapest both-win in the doc and nobody has looked for it in our tables.

### 2.4 What would actually shrink it, ranked

| # | move | bits (BCIKS20) | bits (BCSS25) | prover | status |
|---|---|---|---|---|---|
| 1 | **`WRAP_LOG_CEIL` 16 → 15** | **+2.00** | ~+0.3 | **~2× less apex work** | **free — the code says 2^15 IS the natural max** |
| 2 | `WRAP_LOG_CEIL` 16 → 14 | +4.00 | ~+0.6 | ~4× less | needs the 2^15 tables to fall first |
| 3 | **Narrow the inner proof** (~752 opened cols → apex ALU height, `apex_shrink.rs:141`) | **+2 to +4** | ~+0.6 | large (18 min → ~4.5 min) | **this is the layout optimizer** (§2.5) |
| 4 | **Cut the leaf's 130 Poseidon2 sites** — the chip **already supports arity 11 and 16** (`CHIP_RATE = 16`, `descriptor_ir2.rs:299-322`) | +2–4 leaf | ~0 | leaf + apex `path_depth` | plausible, unattempted |
| 5 | `MIN_TRACE_HEIGHT` 64 → 16 | **0** | 0 | leaf only | **buys nothing** until chip falls; floored at 2^4 by the byte table |

### 2.5 ⚑ The layout optimizer: it is ALREADY a soundness project — through the apex

Status is better than memory records: **the allocator LANDED green** (Phase 1–2,
`docs/RECOVERED-THREADS.md:73-85`); **only Phase 3, the optimizer, is designed-but-unbuilt**
(`docs/DESIGN-verified-layout-optimizer.md`).

Its objective is explicitly **width-only**: *"minimize Σ(committed table widths) (queries pinned)"* —
*"the only lever is committed width"*. **Height never enters.** And yet:

> **The apex's ALU table height IS the inner proof's opened-column count.** So **inner width becomes apex
> height becomes proven bits.** The optimizer's existing width objective is *already* a soundness
> objective — nobody noticed, because nobody priced the apex.

Two teeth this earns:
- ⚑ **Its headline pass is backwards.** Pass 1 ("table-ize the rotated hash sites onto the chip bus")
  moves work **onto** the chip table, making it **taller** — the design concedes it buys "chip height". It
  wins wire bytes and **loses leaf proven bits**. Unpriced.
- To be a soundness project *on purpose* it needs the cost model to become **`max_table_height`** (a
  **min-max**, not a sum) alongside width, plus a **row-packing** transform class the four designed passes
  do not contain.

### 2.6 Blunt verdict on ember's #1 hypothesis

**Trace height IS a security lever — at exactly 2.000 bits/doubling, uncapped by q or pow — and
simultaneously a ~2×/doubling prover lever. The both-win is real, and its mechanism is `|D⁽⁰⁾|`.** Three
honest deflations:

1. **It is a lever *downward*, not upward** — really a **tax**: growing the trace costs 2 bits/doubling
   and *no amount of queries or grinding buys them back*.
2. **The achievable reduction is 2–4 bits, not 20.** Realistic apex `2^16 → 2^14` = **+4.00 bits**. *(The
   lane that investigated our heights priced this at "+2" by inheriting the baseline's refuted 1.02 slope;
   corrected here to +4.00.)*
3. **⚑ Under BCSS25 it is worth ~0.6 bits and the case evaporates.** The bits argument for shrinking
   traces **survives only while we stand on BCIKS20**.

**So the time lever is the real prize**: the apex fold is an **18-minute prove**; a 4× height cut is ~4.5
minutes and compounds with the GPU path. **This is a perf project that pays a 2–4 bit soundness dividend
under one paper and ~0.6 under the other — not a soundness rescue.** The ~78-bit ext-degree-4 ceiling
still dominates, and extension degree remains the only lever that moves it.

---

## 3. ⚑ Why plonky3 has no BabyBear extension degree 6 — the factual answer

**Verdict: an arbitrary implementation gap. Not mathematics, not SIMD.** All from the pinned source
(`~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7`, rev `82cfad73`).

### 3.0 A correction to the premise: degree 6 does not panic — it does not COMPILE

Tested empirically against the pinned rev. `BinomialExtensionField<BabyBear, 6>` fails at **compile time**:

```
the trait bound `MontyField31<BabyBearParameters>: BinomiallyExtendable<6>` is not satisfied
```

because no `impl BinomialExtensionData<6> for BabyBearParameters` exists. The `panic!` at
`monty-31/src/extension.rs:31` is a **second, deeper gate** that only fires if someone writes that impl.
**Both are gaps; neither is a reason.**

### 3.1 The math: X⁶ − 22 IS irreducible over BabyBear

`p − 1 = 2^27 · 3 · 5`, so `2 | p−1` and `3 | p−1`; degree 6 = 2·3 needs `W` a **non-square and a
non-cube** (the `4 | d ⟹ p ≡ 1 mod 4` clause does not apply, since `4 ∤ 6`). Verified by **Rabin's test
with real polynomial arithmetic**, not by citing Lidl–Niederreiter:

> **11 is a non-square but IS a cube; 2 is a non-cube but IS a square. Their product is both — so
> `W₆ = 11 × 2 = 22`**, literally plonky3's own d=4 and d=8 constants multiplied. (`X⁶−31`, `X⁶−33` also
> work.)

**Model validation:** the method **reproduces every published plonky3 constant exactly** — `DTH_ROOT` for
d=4/5/8 (1728404513, 815036133, 420899707) and `EXT_TWO_ADICITY` 29/27/30 (`baby_bear.rs:68,86,96`). It is
not guessing. The complete, verified `BinomialExtensionData<6>`:

| const | value |
|---|---|
| `W` | **22** |
| `DTH_ROOT` | 1314723124 |
| `EXT_GENERATOR` | `[6, 1, 0, 0, 0, 0]` |
| `EXT_TWO_ADICITY` | **28** (≥ 27, passes the const assert at `monty-31/src/extension.rs:90`) |
| `TWO_ADIC_EXTENSION_GENERATORS` | `[[0,0,0,1347018028,0,0]]` (order verified exactly 2^28) |

**Every required const is computable, and all were computed.** Nothing needs a table nobody can build.

### 3.2 SIMD is not the reason — degree 5 on 4-lane NEON refutes it

NEON is **4-lane** (`aarch64_neon/packing.rs:30`) yet implements **degree 5**: `quintic_mul_packed`
(`:1113`, `assert_eq!(WIDTH, 5)`) does 4 coefficients in-vector and `res[4]` on the scalar ALU. AVX2 is
8-lane and runs degree 4 with **half the lanes idle** (`x86_64_avx2/packing.rs:1033`). **Degree need not
divide or tile the SIMD width.** Degree 6 (4+2) would be no more awkward than the 5 that already ships.

### 3.3 A generic fallback exists, ships in production — and Monty31 replaced it with a panic

`field/src/extension/binomial_extension.rs` is degree-agnostic **everywhere**: `binomial_mul` (`:677`,
`_ =>` schoolbook loop, any D), `binomial_square` (`:726`), `try_inverse` (`:366`, generic Frobenius). And
it is **used**: Mersenne31 `BinomiallyExtendable<3>` (`mersenne-31/src/extension.rs:11`), Goldilocks `<2>`
and `<5>` (`goldilocks/src/extension.rs:11,91`). **The Monty31 impl is a performance specialization that
swapped a working fallback for `panic!`.**

### 3.4 The clincher: plonky3 handles REAL obstructions differently

KoalaBear has `p − 1 = 2^24 · 127` — `3 ∤ p−1` and `5 ∤ p−1`, so `X⁵−W` and `X⁶−W` are **genuinely
impossible** there. plonky3 knew, and built a workaround: `TrinomialQuinticData` (`X⁵+X²−1`), documented
at `monty-31/src/data_traits.rs:143-145` as *"required for fields where 5 does not divide (P−1), making
simple binomial extensions impossible."*

> **When the math blocks them, they build a trinomial. For BabyBear degree 6 the math blocks nothing.**

The degree sets are per-field ad hoc (BabyBear {4,5,8}, KoalaBear {4,8}), the trait is marked *"TODO: This
should be deleted long term"* (`data_traits.rs:114`), and the CHANGELOG shows degrees landing **on demand**
(#846 quartic inverse, #847 quintic). **Zero mentions of degree 6 anywhere.** The only ceiling is
`debug_assert!(d <= 8)` (`matrix/src/lib.rs:537`) — 6 is under it.

⚑ **And plonky3's own in-repo argument is for `d ≥ 5`:** `uni-stark/src/security.rs:157-158` caps
conjectured security by `num_modulus_bits`. **D=4 → 123.6 bits, below 128.** D=5 → 154.5, D=6 → 185.4,
D=8 → 247.3. *plonky3 itself documents that our extension degree is too small for a 128-bit target* — and
`whir/src/parameters/soundness.rs:121` says BCSS25 *"enabl[es] 128-bit security with degree-5 extensions"*.

### 3.5 What degree 5 vs 8 costs — MEASURED

Microbench on the pinned rev (aarch64 NEON):

| D | throughput | vs d=4 | naive `O(d²)` predicts |
|---|---|---|---|
| 4 | 3.58 ns/mul | 1.00× | 1.00× |
| 5 | 4.19 ns/mul | **1.17×** | 1.56× |
| 8 | 10.91 ns/mul | **3.05×** | 4.00× |

**SIMD beats the naive model.** (Latency 16.6/16.9/20.2 ns — dependency-bound, nearly flat.) A criterion
bench comparing exactly 4/5/8 exists at `baby-bear/benches/extension.rs:14-63`.

**End-to-end, extension mul is not the prover.** Trace LDE + Merkle dominate (~70–85%) and are base-field,
D-independent (`two_adic_pcs.rs:316-324`). Quotient eval is **packed base, not ext** — `folder.rs:103-105`
decomposes the α-fold into D base dot products. Only the FRI fold (`two_adic_pcs.rs:156-162`) and DEEP
reduce (`:648-650`) are `O(D²)`, ~10–20%. **Estimated 4→8 slowdown ≈ 1.3–1.6×** — *an estimate, not a
measurement.*

⚑ **But degree alone buys nothing where we sit.** At the deployed `lb=6, q=19`, the **query column binds**
— so ext 4→5 buys **exactly 0 bits**. Extension degree raises the *ceiling*; it only pays **stacked with
higher `q`/`lb`** (§4.2). It is not a standalone move.

### 3.6 What the wrap costs us, and the one real hazard

Degree 4 is baked at **~30 Rust sites** (mechanical), **1 Lean config** (`ExtFieldChallenge.lean:218`,
`deployed_extDeg_four := rfl` — self-catching), and **~16 gnark files / 136 `BBExt` sites** with four
hand-unrolled degree-4 kernels. Verified:

- `circuit-prove/src/dregg_outer_config.rs:125` — `pub const OUTER_EXT_DEGREE: usize = 4;`
- `chain/gnark/babybear_ext_ref.go:7` — `type bbExtRef [4]uint32`
- `chain/gnark/babybear_ext.go:19,23` — `const BBExtW = uint32(11)`, `type BBExt [4]frontend.Variable`,
  schoolbook mult with the wraparound `X⁴ = 11`

⚑ **The one hazard worth flagging.** `babybear_ext.go:64-83` derives `ReduceBounded(c0, 68)` from the
degree-4 unrolled arithmetic. **That `68` is a soundness constant, not a type.** The Go compiler catches
array-shape breaks; it will **not** catch a stale bound. **That is the only place a degree change buys a
silent soundness bug** — exactly the shape of [[feedback-a-doc-comment-is-a-name-not-a-proof]].

### 3.7 So: is "bump the degree" free-ish, or a landmine?

**Neither. It is ordinary, bounded work with one sharp edge.** There is no good reason degree 6 is absent
— the constants above are ready to paste. But **degree 6 buys nothing degree 8 does not** (both clear 128;
§4.2), and **degree 8 ships today with better two-adicity (30 vs 27/28)**. The cost is not plonky3 —
*plonky3 is ready*. **The cost is our gnark wrap**: ~136 `BBExt` sites, four hand-unrolled kernels, a
`ReduceBounded` constant that fails silently, and a **full VK re-key across every consumer**.

---

## 4. Other both-wins — and the tradeoffs that pretend to be both-wins

### 4.1 ⚑ `log_blowup` — the baseline's numbers are an ARTIFACT; the sign depends on the paper

**The baseline's §3 lever table rows 6–7** (*"lb 6→7: +6.37 → 76.48, the proven optimum"*; *"lb=8: +4.87 →
74.98"*) **are wrong.** They pinned `|D⁽⁰⁾|` at 2^12 **while raising the blowup** — forgetting that
`|D⁽⁰⁾| = T·2^lb` **grows with lb**. Reproduced exactly: computing with `D⁽⁰⁾` pinned returns the
baseline's **76.48 / 74.98**; computing it correctly returns **74.48 / 70.98**. The discrepancies are
exactly **2.00 and 4.00 bits** = `log₂(4)` and `log₂(16)` = the `(2^lb ratio)²` factor. ⚑ **Two
independent lanes reached this same diagnosis**: *"one lane has a locatable bug"* — it decayed the cap at
1.5 bits/lb instead of 3.5, varying only `ρ^{3/2}`. The baseline's *"the turnover shape is robust, the
constants are not"* was too charitable: **the constants have a locatable bug, and the shape is wrong too.**

⚑ **A second baseline error: "lb=8 is WORSE than lb=6" is FALSE at our trace** — 70.98 > 70.11 at T=2^6.
(It is true at T=2^14: 54.98 < 61.98.) And the baseline's *own* numbers (+6.37, +4.87) both say lb=8 beats
lb=6 — **the claim misreads the table it cites.** What is true is **lb=8 < lb=7**.

**At FIXED q=19 the optimum IS lb=7 (74.48)** — and the mechanism is not a slope race (the query row rises
9.5/step, the cap falls 3.5/step; 9.5 > 3.5 always). **It is the `min{}` switching:** below the crossover λ
*follows the query row up*; above it λ *follows the cap down*. The peak sits at the crossover, `lb ≈ 6.46`
⟹ best integer **7**.

**But once `q` is optimized per `lb`, the ceiling is `110.98 − 3.5·lb − 2·log₂T` — monotone decreasing:**

| lb | q\* | **proven** | proof KiB | prove ms | **bits per prover-ms** |
|---:|---:|---:|---:|---:|---:|
| 3 | 58 | **88.48** | 285.6 | 29 | 3.05 |
| **4** | 40 | **84.98** | 212.5 | **20** | **4.25** ⟸ best |
| 5 | 30 | 81.48 | 171.4 | 32 | 2.55 |
| **6 (deployed)** | 23 | 77.98 | 141.5 | 58 | 1.34 |
| 7 | 19 | 74.48 | 124.8 | 101 | 0.74 |
| 8 | 15 | 70.98 | 106.3 | 183 | 0.39 |

*(proof size from the baseline's fitted model `20561 + q·(3971+239·lb)`, which reproduces 6 measured points
to <0.25 KiB; prove ms from the measured grid, `FRI-PARAM-FRONTIER.md:174-180`.)*

> **⚑ `lb 6 → 4` **with `q 19 → 40`** buys +14.87 proven bits AND a 2.9× faster prover** — paid entirely
> in wire (+92 KiB) and verify (+2.1 ms). **A genuine both-win on security and prover time.**
> ⚠ **At FIXED q it is a loss** (lb=4/q=19 → 52.84). The extra queries are not optional; they are the price.

**And it is legal.** `log_blowup ≥ log₂⌈max_degree − 1⌉`; the whole-batch degree ceiling is **8**
(`descriptor_ir2.rs:5418-5420`, guarded by `ir2_degree_budget`) ⟹ **`lb ≥ 3`**. **lb=6 is not forced by our
AIRs.** *(⚠ The recursion AIR is stricter — `log_blowup must be >= 3 because our AIR has degree-7
constraints (x^7 S-box)`, `plonky3_recursion_impl.rs:330`. Still ≥ 3.)*

⚑ **Under BCIKS20, the deployed config's design rationale is backwards for the proven column.**
`ir2_config`'s doc-comment (`descriptor_ir2.rs:5409-5414`) says: *"queries dominate IR-v2 proof size … so
RAISING blowup and CUTTING queries shrinks the wire"*. **That optimization was made against a ledger
(`q·lb/2 + pow`) monotone in lb — so raising blowup looked free on security. Under BCIKS20's real ε_C it
costs 3.5 ceiling bits per step and doubles the prover.** We tuned a knob against a ledger that omits the
term penalizing exactly that knob.

⚑ **⚠ But under BCSS25 the design is VINDICATED** — the optimum moves to lb=8 (85.37) and raising blowup
*buys* proven bits. **§1.4 decides this, and it decides it for the whole section.**

⚑ **The baseline's Tier-2 item 13 ("`lb 6→7` is the proven optimum") is dominated either way:** at fixed q
it is **+4.37 bits for 2× prover**, while **`lb=6, q 19→23` is +7.87 bits for ~0 prover** and +17 KiB.
**Raising queries at lb=6 strictly dominates raising lb.**

### 4.2 Extension degree — a TRADE, but the one that restores the frontier

Not a both-win: it costs ~1.3–1.6× prover and a gnark rewrite. But it is the only lever on the ceiling:

| ext | ceiling (T=2^6, best lb) | reaches proven **128**? |
|---|---|---|
| 4 (deployed) | 88.48 | **NO — unreachable at any q** |
| 5 | 119.38 | **NO** |
| 6 | 150.29 | **yes** — (lb 6, q 38, pow 20) → 129.71, 220.7 KiB |
| 8 | 212.10 | **yes** — (lb 6, q 37, pow 20) → 129.93, 215.4 KiB |

**The baseline's "Frontier B is unreachable at ext-degree 4" is CONFIRMED**, and its "needs ext ≥ 6" is
confirmed too (ext 5's ceiling is 119.38, still short of 128). But the sharper statement:

> **Frontier B is recoverable at ext ≥ 6 at exactly the wire cost it always quoted** (lb=6, q=38,
> 220.7 KiB — the baseline's own Frontier B row). Its *shape* was right; only its proven column was wrong.
> **Withdraw it at ext 4; it returns at ext 8.**

⚑ **This is why ext degree matters more than its bit count suggests: at ext 8 the query column binds again
everywhere up to lb=8, so proven bits RISE monotonically with lb — exactly as the naive ledger says. The
classic frontier is RESTORED, and our size-optimal high-blowup design becomes security-optimal too.** The
tension in §4.1 exists **only** because ext 4 pins us at the ε_C boundary. **Raising the extension degree
does not just buy bits; it makes the other levers behave again.** *(BCSS25 does much the same, for free.)*

### 4.3 PoW and queries — real, cheap, and worth ZERO where it counts

**The baseline's `pow 16→20 = +3.29` is CONFIRMED at the leaf**, and its mechanism is prettier than stated:
raising `pow` lets the optimiser **drop m** (7 → 5), cutting the `(m+½)⁷` damage to ε_C — so **both columns
improve together**. PoW is not purely a query-column lever; it buys ε_C room.

**But at the apex (T = 2^16, ε_C-bound at m=3) there is no m left to trade:**

| lever @ **apex** | proven | Δ |
|---|---|---|
| deployed (lb6, q19, pow16, T=2^16) | 57.98 | — |
| `pow 16 → 20` | 57.98 | **+0.00** |
| `q 19 → 25` | 57.98 | **+0.00** |
| `WRAP_LOG_CEIL 16 → 15` | 59.98 | **+2.00** |

> **⚑ The baseline's single Tier-1 "do this now" knob is worth +0.00 bits on the artifact that reaches a
> light client.** +3.29 on the leaf. Both true; only one is about the proof anyone verifies.

**Caps CONFIRMED in the pinned source:** `challenger/src/grinding_challenger.rs:113`
`assert!((1u64 << bits) < F::ORDER_U64)` ⟹ **bits ≤ 30**; `type Witness = F` (a *single* field element)
with an exhaustive `.expect("failed to find proof-of-work witness")` (`:221`) ⟹ **a prover panic, not a
retry** (2.3% @ 29, 15.3% @ 30) ⟹ **practical ceiling 27**. The grind is **per proof**
(`fri/src/prover.rs:98`, inside `prove` — it must be; the witness is Fiat-Shamir-bound).

### 4.4 ⚑ `commit_proof_of_work_bits` — genuinely uncounted, and it breaks the "ceiling"

Confirmed real: ground **per fold round** at `fri/src/prover.rs:224`, immediately before `beta` at `:228`;
checked at `verifier.rs:222`; **omitted from `conjectured_soundness_bits`** (`config.rs:42-44`); and **0 in
all 7 shipped dregg configs**. It suppresses the ε_C-side terms, so:

- at the deployed `lb=6/q=19` (**query-bound**) it buys **+1.45 bits** — small;
- at `lb=7` (**cap-bound**) it buys **+5.5 bits** (74.48 → 80.02) — **which breaks the 78-bit "ceiling"
  §1.2 derives.**

⚑ **So the ceiling is a ceiling only at `commit_pow = 0`.** It is complementary to the ε_C-bound regime,
not a standalone win — precisely where the trace-height lever lives. **Nobody has priced this.**

Two real defects found on the way: `config.rs:18` claims PoW before *"each batching challenge"* but the
DEEP/ALI `alpha` is **un-ground** (`two_adic_pcs.rs:564` — zero grinds in that file); and **`CirclePcs`
silently ignores `commit_proof_of_work_bits` entirely** (`circle/src/prover.rs:84-156`).

### 4.5 Batching — NOT the reverse of a both-win; it is nearly free

⚑ **A hypothesis in the brief (and in my own first pass) is REFUTED.** `two_adic_pcs.rs:475-480`:
**`|D⁽⁰⁾| = MAX height × 2^lb`, never the sum.** So batching N AIRs of **equal height** costs **~0 proven
bits** (only the `k/|EF|` term, ~37 bits of slack) and amortizes prover overhead. `p3-batch-stark` keeps
each AIR at its own height in one FRI instance (`batch-stark/prover.rs:214-219`); `lookup/` makes them
talk. **A real both-win, and we already have it.**

*(The apex's 12-bit deficit is therefore NOT "the cost of batching" — it is the cost of the recursion
verifier's own tables being tall, plus a `WRAP_LOG_CEIL` pad. Batching more turns per apex is ~free;
making the apex's verifier circuit smaller is the lever.)*

### 4.6 A different field — honest verdict: no

| field | verdict |
|---|---|
| **Goldilocks²** (\|K\| = 2^128, ceiling 85.85 vs 77.98) | **Loss/wash.** The +4.4 bits of \|K\| costs **half the SIMD lanes on the base-field LDE** (4 vs 8 AVX2, 8 vs 16 AVX512 — `goldilocks/src/x86_64_avx2/packing.rs:26`) — which is where the work is. And the gnark wrap is structurally BabyBear-specific (nonnative BabyBear+EF4, radix-2^31 challenger packing, hardcoded arity-2 fold). |
| **M31 / circle STARKs** | **Loss.** Shipped circle configs run **D=3 over bare 𝔽ₚ = 93 bits** — *worse* than BabyBear⁴'s 123.6. Max M31 is 186 (D=3 over 𝔽ₚ²), but `CirclePcs` is **arity-2-only** (`circle/src/folding.rs:103`), ignores `log_final_poly_len`, and ignores commit-PoW. |
| **KoalaBear** | **No reason.** Same \|K\|; no soundness difference. (Poseidon2 S-box degree 3 vs 7 — pure perf.) |
| **A bigger base prime** | A **trade** (ceiling for per-op speed), not a both-win. |

*(Bonus defect: `circle/src/verifier.rs:259-266` lets a malicious proof **panic** the verifier — a DoS,
unreachable at shipped configs.)*

### 4.7 Rejected as levers — plainly

| lever | verdict |
|---|---|
| **Constraint degree / row packing** | **0 bits.** Quotient chunks share their trace's FRI bucket; only the max table binds (§2.2). |
| **Narrower trace** | **0 bits.** DEEP/ALI term ≈ 2^-115, **37 bits below binding** — pure perf. |
| **Merkle digest size** | **Not a cap.** 8 BabyBear = 248 bits ⟹ ~124-bit collision; outer = 1 BN254 ⟹ ~127. Both far above the ~78 cap (ethSTARK wants digest ≥ 2λ = 156 ✓). **Nobody is missing a cap here.** |
| **Arity** | **~0.15 end-to-end bits** (it enters only the negligible term 2), vs the per-fold column's 2.807. The baseline's §3.3 is **correct**. |
| **`log_final_poly_len`** | Inert; no material soundness term. |
| **dregg's query balance** | **Already right** — deployed sits at cap 71.28 vs query 71.11. **No wasted queries to harvest.** |

---

## 5. ⚑ A better code — verdict: NO, and the repo's open question is CLOSED

**The hypothesis's logic is sound. Its premise is false for dregg.** *(Read in full: **ECCC TR25-166**,
Oct 2025, 34pp — the eprint 2025/2054 PDF 403s, but the same paper is on ECCC. ⚠ ECCC is the Oct 2025
version; eprint was revised 2026-03-24, so parameter drift is possible — but the crux is corroborated
independently, below.)*

### 5.1 What Goyal–Guruswami actually proves — verbatim

> **Theorem 1.2 (Optimal proximity gaps for folded RS code).** For all R, η, err ∈ (0,1), a rate R folded
> Reed–Solomon code over alphabet **Fˢ** and block length n has (1−R−η, err)-proximity gap (in fact,
> mutual correlated agreement) for lines, **if s ≳ 1/η²** and err·|F| ≳ n/η + 1/η³. The same holds for
> order-s univariate multiplicity codes.

**Corollary 4.11** gives the constant: for **s > 4t²**, radius **1−R−2/t** ⟹ **η = 2/t ⟹ s > 16/η²**.
**The folding parameter grows as the SQUARE of the inverse gap** — the crux, and worse than feared.
Corroborated independently by the withdrawn arXiv 2601.10047 (Jeronimo–Liu–Rajpal, Thm 6.2: `m ≥ c/η²`)
and by the classical GR08 fact that FRS needs `m ≈ 1/ε²`.

- **Codes covered:** folded RS, univariate multiplicity, random linear, **random-evaluation-point** RS,
  AEL/expander. **Plain RS on a 2-smooth multiplicative coset: NOT COVERED** — GG give it only `1−√R`.
- **Rates:** general; formally covers 1/64 and 1/8 — but see the block-length wall.
- **Field size:** *"only linear in the block length"* — **verified true, and not the binding constraint**
  (err ≥ 2^-101 even at t=256 against |F| = 2^123.6).
- **GG build no protocol.** *"IOPP" appears **exactly once** in 34 pages* — in the motivation. Their §6
  open questions are internal parameter cleanups; constructing a protocol is not even listed.

### 5.2 Is "halve the queries" valid? — **logic yes; arithmetic catastrophic**

Each FRS symbol is `s` field elements, so each query downloads `s`. At our wrap rate 1/64 (our arithmetic,
from Cor 4.11):

| t | η=2/t | bits/query | **s > 4t²** | q@100b | **field elts/query** |
|---|---|---|---|---|---|
| 16 | 0.125 | 2.83 | 1024 | 36 | 36,864 |
| **21** | 0.095 | **3.17** | **1764** | 32 | 56,448 |
| 128 | 0.016 | 5.00 | 65536 | 20 | 1,310,720 |

*Baselines: **Johnson (proven, plain RS) = 3.00 bits/query at s = 1**. Capacity = 6.00.*

> **You need an alphabet of ~1764 field elements just to BREAK EVEN with what BCIKS20 already proves for
> free at s = 1.** Query count shrinks ≤2×; per-query cost grows by `s ≥ 10³`. **Net ~1000–8000× worse.
> The win does not evaporate — it inverts.**

**The kill shot: the alphabet exceeds our entire codeword.** Traces are 2^3–2^8 rows; at rate 1/64 the
whole codeword is N = 512…16384 field elements, and block length is `n = N/s` **symbols**:

- 2^8-row trace, s=4096 ⟹ **n = 4 symbols** (δ granularity 1/4 — a "1−R−η" radius is meaningless)
- 2^8-row trace, s=65536 ⟹ **n = 0.25 — the code does not exist**
- 2^3-row trace, s=1024 ⟹ **n = 0.5 — does not exist**

**We are far below the asymptotic regime. The win is uncollectable.**

### 5.3 ⚑ Is folded-RS latent in FRI? — NO, and here is the counterexample

The baseline flags this as *"the open question nobody is asking"* (its §5.1). **Its verdict is right; its
reason is soft. The hard one:**

Both objects have shape `{x·gᵗ : t<s}`. The difference is the **generator's order**:
- **FRI:** `g = w`, `ord(w) = 8` exactly — a coset of the order-8 **subgroup**; exponent step `N/s`.
- **FRS:** `g = γ`, **primitive** (order `q−1`); the first `s` powers — **not** a subgroup; exponent step 1.

They are **not the same set** (verified numerically), and the order is load-bearing.

> **Counterexample (ours, verified in 𝔽₉₇).** Take GG's Def 2.20 with `γ` of order exactly `s` — i.e.
> FRI's coset read as an FRS bundle. It satisfies Def 2.20's literal conditions (`q > sn` ✓,
> `αᵢγᵗ ≠ αⱼ` ✓). Now take **A = span{1, x⁸, …}** — the polynomials in `x⁸`. Since `(αᵢwᵗ)⁸ = αᵢ⁸`,
> *every* symbol is constant on its coset, so `dim Aᵢ = r−1` for **every** i. GG Def 2.17 then forces
> **τ(r) ≥ (r−1)/r = 0.5**, while Thm 2.21 [GK16] claims **τ(2) = sR/(s−r+1) = 0.286**. **Contradiction —
> the FRI-coset-grouped code is NOT a subspace design.** GG's entire engine fails on it.

**The deep reason is a genuine tension, and it is fatal:**

> **FRI's foldability and FRS's subspace-design property are mutually exclusive.** FRI *needs*
> `ord(w) = arity` so `x ↦ x^arity` collapses the coset — that is what makes recursion possible. FRS
> *needs* `ord(γ) ≫ s` so no low-degree relation ties the bundle. **The counterexample subspace
> `span{1, x⁸}` is literally the set of polynomials FRI's fold map makes constant on each coset. The
> structure that makes FRI work is the structure that destroys the capacity gap.**

A second, independent consistency argument reaches the same place: plain-RS-at-capacity is *refuted* while
FRS-at-capacity is *proven*, so any bridge letting FRI inherit FRS's capacity would prove something known
false. *(Side note: GG's Def 2.20 as printed omits the `ord(γ)` hypothesis GR08/GK16 assume — a writeup
gap, not an error in the result.)*

**⟹ The repo's open question (baseline §5.1, "highest expected value in this survey") can be closed: the
answer is NO, with a counterexample.**

### 5.4 Is there an IOPP built on it? — nothing, anywhere

| scheme | code | **proven** radius | FRS as a code? |
|---|---|---|---|
| **Bolt** (2026/310) | sketched LDPC+RS | **unique decoding only** | **No** |
| Blaze (2024/1609) | interleaved RAA | unique decoding | No |
| BaseFold (2023/1705) | foldable linear | double-Johnson (*below* Johnson) | No |
| STIR (2024/390) | plain RS | Johnson (Thm 3.4); capacity = **Conjecture 5.6** | No |
| WHIR (2024/1586) | constrained RS | MCA only at unique decoding; capacity = **Conj. 4.12** | No |

**Bolt kills it outright** — Remark 1.4: *"Throughout this work we focus exclusively on the unique decoding
regime."* Zero occurrences of "folded Reed-Solomon". Its Open Question 3 *wants* GG's capacity gaps and
notes it *"requires a larger sparsity than what we can afford."* **`bolt-rs`: 5 stars, ONE COMMIT TOTAL, 0
releases**, and its headline benchmark includes an *estimate* for an unimplemented component against a
self-reimplemented baseline.

> **A capacity-radius IOPP over folded RS or multiplicity codes: no paper, therefore no prover.** GG and
> JLR ship zero code. The gap between "gap proven at 1−R" and "working IOPP" is an open **construction**
> problem, not an engineering pickup. **A paper is not a prover; here there is not even a paper.**

### 5.5 What adoption would cost

Both of GG's doors are bricked before engineering starts:
- **Thm 1.2 (FRS):** needs an alphabet larger than our whole codeword. **Dead on arithmetic.**
- **Thm 1.3 (random RS):** needs **random evaluation points** ⟹ deletes `Radix2DitParallel` and
  `TwoAdicFriPcs` (`circuit/src/plonky3_prover.rs:31,34,61,81`) — the NTT *and* FRI's recursion. **Dead.**

If both were ignored: a new code + **an IOPP that does not exist in the literature** (open research, not a
port); a plonky3 prover rewrite; the **gnark BN254 FRI verifier rewritten and re-audited from zero**; and
the Lean ledger — which currently *proves* per-fold discharge at all six shipped configs
(`FriArityFiberDischarge.phase_injective_of_far`) — thrown away for an unmechanized number. **Trading a
proven, mechanized ledger for a paper with no protocol is a downgrade in assurance whatever the theorem
says.**

---

## 6. ⚑ THE RANKED BOTH-WIN TABLE

**Column: QUERY ledger, PROVEN.** Baseline artifact = **the recursion apex** (`ir2_leaf_wrap_config`:
lb 6, arity 2, q 19, pow 16, T = 2^16 ⟹ `|D⁽⁰⁾| = 2^22`) = **57.98 bits under BCIKS20**, **~70.9 under
BCSS25**. Bits are BCIKS20 unless noted.

| # | lever | bits gained | speed effect | cost | today? |
|---|---|---|---|---|---|
| **1** | **Mechanize ε_C** — add trace height to `FriKnobs`, port `whir/…/soundness.rs`'s BCSS25 bound into the FRI ledger | **0 — but it decides whether 2/3/4/5 are worth 4 bits or 0.6** | none | Lean + Rust | **YES — and it GATES the rest** |
| **2** | **`WRAP_LOG_CEIL` 16 → 15** | **+2.00** (BCSS25 ~+0.3) | **~2× less apex work** | ~none — the code calls 2^16 *"a safe pad"* over a measured 2^15 max | **YES — one const** |
| **3** | **Padding-cliff audit** — keep the tallest table just under `2^k` | **up to +2.00** per table that is barely over | **up to 2× less work** | an audit | **YES** |
| **4** | **`lb 6 → 4` with `q 19 → 40`** (leaf) | **+14.87** ⚠ **BCSS25: this REVERSES — lb should go UP** | **2.9× faster prover** | +92 KiB wire, +2.1 ms verify, bigger gnark wrap | **YES — config only** |
| **5** | **Narrow the inner proof** (~752 opened cols → apex ALU height) | **+2 to +4** (BCSS25 ~+0.6) | **large — 18 min → ~4.5 min** | **build Phase 3 of the layout optimizer** | designed, unbuilt |
| **6** | **Cut the leaf's 130 Poseidon2 sites** (chip already has arity 11/16) | +2–4 leaf | leaf + apex | real work | plausible, unattempted |
| 7 | **`commit_proof_of_work_bits` 0 → 16** | **+1.45 deployed; +5.5 at lb=7 — breaks the "ceiling"** | per-round grind | 0 wire | **YES — uncounted today** |
| 8 | Batching more turns per apex | **~0** (only the max height binds) | **amortizes overhead** | none | **YES — already have it** |
| 9 | `q 19 → 23` (leaf) | +7.87 | ~0 prover | +17 KiB | YES |
| 10 | `pow 16 → 20` | **+3.29 leaf / +0.00 apex** | 16× a µs grind, per proof | 0 wire, 0 verify | YES |
| 11 | **ext degree 4 → 8** | **+50.6** (to 128.93 @ lb6/q38) — **the only ceiling lever** | **~1.3–1.6× SLOWER** | **gnark rewrite (~136 sites) + full VK re-key**; `ReduceBounded(c0,68)` fails silently | plonky3 **YES**; our wrap **NO** |
| — | constraint degree / row packing | **0.00** | — | — | not a lever (§2.2) |
| — | narrower trace | **0.00** (37 bits of slack) | pure perf | — | not a lever (§4.7) |
| — | arity | ~0.15 | — | — | not a lever (§4.7) |
| — | Merkle digest | not a cap (~124 vs ~78) | — | — | not a lever (§4.7) |
| — | Goldilocks² / M31 / KoalaBear | wash or **loss** | — | — | **no** (§4.6) |
| — | a better code (GG folded-RS) | **inverts ~1000×**; no IOPP exists | — | total rewrite | **NO** (§5) |

**Reading it honestly.** Rows 2–6 and 8 are the both-wins, and **every one is a `|D⁽⁰⁾|` move** — because
`|D⁽⁰⁾|` is the one quantity that is both the prover's work and ε_C's numerator. Rows 9–11 are the classic
trades. **Row 1 must come first**: the deployed ledger has no trace-height field, so it cannot express —
let alone enforce — rows 2, 3, 5, or 6, and it cannot tell us whether they are worth 4 bits or 0.6.

**⚠ The caveat over the whole table: rows 2, 3, 5, 6 shrink ~5× under BCSS25, and row 4 REVERSES SIGN.**
The both-win column is largest under the paper we cite and smallest under the paper we should cite.
**Resolve §1.4 before spending engineering on rows 4–6.**

**If the one-line answer is wanted:** *the both-win is real and it is `|D⁽⁰⁾|` — but do row 1 first, take
rows 2 and 3 (free either way), and do not touch `lb` until we know which paper we stand on.*

---

## 7. ⚠ Uncertain / unfetched — every gap, flagged

**Numbers that are OURS, not the papers':**
- The **master equation** (§1.2) is *derived* from BCIKS20's verbatim formula but appears in no paper.
- The **BCSS25 → FRI composition** (§1.4) is ours. **BCSS25 does not restate a FRI soundness theorem** —
  it defers to [BCIKS20], [HLP24], [Sta25]; "FRI" does not appear in its abstract; and `p3-whir`'s
  transcription is a *proximity-gaps* error for WHIR, not a FRI `ε_C`. Shape solid; the constant could
  move ~1 bit. ECCC preprint = **unrefereed**.
- ⚠ **All proven figures OMIT ethSTARK eq. (20)'s DEEP/ALI top-row terms**, so every number here is an
  **optimistic upper bound**; the true posture is somewhat lower. **The ranking is robust** (all rows share
  the omission; it follows from ε_C's `m⁷`/`1/|F|` structure).
- The **ext 4→8 end-to-end slowdown (1.3–1.6×)** is an **estimate** from a component microbench. The
  **microbench itself is measured** (aarch64 NEON, pinned rev).
- **Proof sizes** come from the baseline's fitted model, calibrated to 6 measured points **at the leaf**;
  **no apex proof size is measured**, and the apex's wire is what travels.
- The **GG rate/alphabet arithmetic** (§5.2) follows Cor 4.11's formula but appears in no paper.

**Measured vs assumed:**
- The apex `degree_bits [9,9,15,14,15]` is **code-recorded from a real 2026-07-12 run**
  (`accumulator.rs:225-227`), **not re-measured here** (release binaries lack the `prover` feature; a real
  build is 20+ min). Labeled **unmeasured-fresh, code-recorded**.
- **The deployed rotated leaf's `degree_bits` are UNMEASURED** — no test pins them. The chip ≈ 2^8 figure
  is inferred from the 130-site `#guard` plus the code's own *"2³–2⁸ rows"* comment.
- ⚑ **The cheapest next action settles both.** `cargo test -p dregg-circuit-prove --release --test
  apex_shrink_trace_anatomy -- --ignored --nocapture` prints `degree_bits` **with table names**, no proving
  (~4 min after build). It also resolves a live contradiction: `apex_shrink.rs:145` claims poseidon2-W16 is
  the 2^15 table, but the registration order (`common.rs:404-433`) puts poseidon2 at 2^14 and **recompose**
  at 2^15, and `docs/deos/APEX-VERIFIER-AIR-REDUCTION.md:35-36` hedges. **Someone guessed.**
- **GG source drift**: read from **ECCC TR25-166 (Oct 2025)**; eprint 2025/2054 was revised 2026-03-24 and
  could not be fetched. The crux (`s ∝ 1/η²`) is corroborated by two independent sources.

**Read but not proved:** §2.5's "inner width → apex height" chain is read from `apex_shrink.rs:141-143`
and the registration order; the *quantitative* map from opened-column count to ALU rows is not derived.

**Found on the way, not chased (all in the pinned plonky3):** the DEEP/ALI `alpha` is **un-ground**
despite `config.rs:18`'s claim (`two_adic_pcs.rs:564`); `CirclePcs` **silently ignores**
`commit_proof_of_work_bits` (`circle/src/prover.rs:84-156`); `circle/src/verifier.rs:259-266` lets a
malicious proof **panic** the verifier (DoS; unreachable at shipped configs);
`conjectured_soundness_bits` has **zero callers** and is `|F|`-blind.

**And in dregg — the baseline's Tier-0 item 1 is PARTLY done, and I re-located the remnant.** A lane
reported `circuit/src/lib.rs:83` as miscrediting eprint 2025/2046 to *"Kambiré"*. **That is wrong and I
verified it:** `circuit/src/lib.rs:100-103` **already correctly** attributes 2025/2046 to
*"Crites–Stewart … disprove it by reduction"* and names Kambiré separately for arXiv 2604.09724. The
**real** surviving miscitation is **`circuit-prove/tests/fri_params_soundness_budget.rs:130-131`** —
*"the capacity conjecture is REFUTED … (Kambiré, eprint 2025/2046)"* — and
`circuit-prove/src/plonky3_recursion_impl.rs:306` and `circuit/src/plonky3_prover.rs:116` carry the same
pairing. *(Flagged as an instance of [[feedback-verify-agent-claims]]: the finding was real, the address
was not.)* **⚑ UPDATE (2026-07-15): the two Rust sites are repaired** — `plonky3_recursion_impl.rs` and
`plonky3_prover.rs` now attribute 2025/2046 to Crites–Stewart and Kambiré to arXiv 2604.09724
separately, and the recursion config's `128` is labeled as the refuted capacity column it is.
`fri_params_soundness_budget.rs:130-131` is owned by another lane and is not repaired here.

**Also found, and it retires a baseline flag:** the baseline's §4.1 worries that the `M = 1` fiber
discharge fires only at 96.9% farness while FRI needs 87.5%, and reports it as an open metatheory
residual. **The tree has since answered it honestly and in the open** — `circuit/src/lib.rs:78-87` cites
`Dregg2.Circuit.FriJohnsonRadiusGap.deployed_M1_false_at_johnson` (a `448`-far word with a non-injective
phase map — so `M = 1` is **FALSE** in `[448, 496)`, confirming the baseline's suspicion) and
`deployed_discharge_threshold_tight` (496 cannot be weakened by one). The honest count at the Johnson
radius is `arity8_johnson_good_card_le`'s `3528` ⟹ ~111 bits, **higher only because it is a weaker
claim**. **The baseline's §4.1 is resolved, not open** — not re-derived here, but the flag should not be
carried forward as if nobody had looked.

**Inherited from the baseline, NOT re-verified here:** the Kambiré / Crites–Stewart / Diamond–Gruen
citation corrections (its §1), the per-fold column's residuals (its §4), and the STIR/WHIR/BaseFold
maturity survey (its §5). This doc re-verified the **ε_C column**, the **plonky3 source claims**, and the
**better-code question**, and corrected five things; it did not re-audit the rest.

---

*Primary sources read in full: **BCIKS20** eprint 2020/654 Thm 8.3 (local mirror, p. 41, transcribed
twice, validated against the paper's own p. 41 worked example, and against **ethSTARK** eprint 2021/582
eq. 21 p. 40); **BCSS25 / BCHKS25** eprint 2025/2055 = ECCC TR25-169 Thm 4.2 / Cor 4.4 (p. 27,
cross-validated against `p3-whir`'s verbatim transcription); **Goyal–Guruswami** ECCC TR25-166 (34pp, =
eprint 2025/2054). Code verified verbatim at plonky3 rev `82cfad73` and at dregg HEAD. Recomputation:
`scratchpad/eps_c_integrator.py`, `lb_curve.py`, `eps_c_verify.py` (each self-validating against a
published worked example; independent of the baseline's cited-but-nonexistent `eps_c.py`).*

*This document changes no deployed parameter and no Lean. It is the research record.*
