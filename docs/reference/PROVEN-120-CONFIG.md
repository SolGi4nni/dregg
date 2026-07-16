# PROVEN-120-CONFIG — what a genuine, proven 120-bit dregg actually costs

**ember's question, verbatim:** *what would we do to have a genuine, proven 120-bit configuration of our
system?*

**What this is.** A design. Every input is now measured or mechanized, so this is an optimization
problem rather than a research question. It succeeds
[`FRI-BOTH-WIN-LEVERS.md`](./FRI-BOTH-WIN-LEVERS.md) (the lever map) and
[`EXT-DEGREE-COST.md`](./EXT-DEGREE-COST.md) (the cost column), and **corrects both, at three places**:
their shared *"`WRAP_LOG_CEIL` 16 → 14 buys +4.00 bits"* row (**the knob is a FLOOR — it buys 0**, §3.5);
the derived ceiling formula both stand on (**0.6–1.5 bits optimistic** vs the mechanized ledger, §1.3);
and `EXT-DEGREE-COST.md`'s **d=5 recommendation** (**d=5 cannot reach 120 anywhere**, §3.2).

**This document changes no parameter, no config, no Lean, and nothing deployed.** It is a decision
input. The deployed `d = 4` stands.

**⚑ The numbers here are the MECHANIZED ledger's, not a formula's.** Every proven-bit figure below is
computed by an exact transcription of `metatheory/Dregg2/Circuit/FriLedger.lean`'s `friCommitLedger`
(pure `Nat` arithmetic, every rounding conservative), **validated against all 14 numbers
`FriLedgerSound.lean` PROVES** — `wrap_ledger_commitBits = 71`, `= 55` at `logD0 = 20`,
`johnsonBits = 73`, `goodCount = 14112`, `perFoldBits = 109`, `ethWrap` `28`/`118`, `prodV1`
`196`/`116`, `recursion_johnsonBits = 71`, and all four rows of
`ledger_commitBits_at_measured_heights` (`81`/`67`/`63`/`61`). **All 14 reproduce exactly.**

---

## 0. Headline

1. **⚑ Proven-120 is NOT reachable today, and no knob reaches it. It needs the extension-degree wrap
   rewrite — and only `d = 8`.** The deployed ceiling at `d = 4` is **57** at the apex. `d = 5`
   **cannot reach 120 anywhere**, at any `(lb, q, pow)`, at any trace height a shipped config has — its
   best ceiling is **118**, at `T = 2^6, lb = 3`, which is *exactly* the v1 leaf's shape. It misses by
   2 bits everywhere. **`d = 6` FAILS at the deployed apex** (ceiling **119**) and is **orphan-blocked**
   — it needs a permanent **fork of 18 plonky3 crates** that `d = 8` does not. **The answer is `d = 8`, and it is the only answer.**

2. **⚑ The good news is that `d = 8` gives ONE knob-set for the whole system.**
   **`d = 8, lb = 6, q = 36, pow = 16`** reads **λ = 122.60 on every shipped config** — leaf, apex,
   outer, v1, zk, rotated — with **2.6 bits of margin**. At `d = 8` the *query* column binds
   everywhere, and the query column is **trace-height-invariant**, so one config yields one number for
   every artifact. The six-config table collapses to one row. **This is the design.**

3. **⚑ The apex-height discrepancy is RESOLVED, and it resolves AGAINST the mechanized ledger.** The
   apex is **`|D⁰| = 2^22`**, not `2^19`. `accumulator.rs:646` binds `ir2_leaf_wrap_config()`
   (`log_blowup = 6`) and `:654` binds `wrap_params()` (the `2^16` floor); **both are passed to the
   same prove call at `:783`**. So `WRAP_LOG_CEIL` floors tables that are minted at **lb = 6** ⟹
   `2^16 · 2^6 = 2^22`. `create_recursion_config` (lb = 3) **is not called on that path at all**.
   ⚠ **So `FriLedgerSound.ledger_commitBits_at_measured_heights` row 4 is wrong**: it pairs
   `recursionConfig` (lb = 3) with a height sourced from a floor applied only to the lb = 6 path —
   **precisely the error its own docstring says a parametric ledger exists to prevent.** **The deployed
   posture is 57, not the 61 the tree currently believes.**

4. **⚑ ember's ceiling equation is CONFIRMED in shape and is 0.6–1.5 bits OPTIMISTIC.**
   `CEILING = 30.907·d − 12.65 − 2·log₂(T) − 3.5·lb` reproduces the mechanized ledger's every entry to
   within `−0.6 … −1.5` bits — always with the ledger **below** the formula, because the ledger floors
   to `Nat` and over-estimates `ε_C` on purpose. **Do not design to the formula at a 120 boundary**;
   the formula says 120.29 where the ledger says 119.

5. **⚑ Two of ember's three rough solves are refuted, and the third is the one that matters.**
   - `d=8, lb=6, q≈35, pow≈15, T=2^19` reads **118.61 — SHORT by 1.39.** The fix is one query and one
     grind bit: `q=36, pow=16` ⟹ **122.60**.
   - *"`d=6` would give ~124 at the current height"* — that is `d=6` at `lb=3`. **At the apex's actual
     `lb = 6` the `d=6` ceiling is 119 and 120 is UNREACHABLE at any `(q, pow)`.** The free trace lever
     (`WRAP_LOG_CEIL 16→15`) is *exactly* what rescues it, to 121 — a 1-bit margin, which is not a
     margin.
   - *"`d=5` tops out ~93 and cannot reach 120 at `T=2^19`"* — **correct, and it generalizes: `d=5`
     cannot reach 120 at ANY height ≥ 2^6.** There is **no cheaper corner**; the answer to *"lower `T`
     + d=5"* is **no**.

6. **⚑ The cheapest genuine proven-120 config costs LESS at the wrap than the published estimate — if
   one non-obvious knob moves with it.** A naive `d=8` 120-config needs the gnark-verified outer to go
   `q: 38 → 71` (**1.87× the wrap's query loop**, on top of `d=8`'s 2.35× ExtMul). But **raising the
   outer's `lb` 3 → 6 takes `q` to 36 — *fewer* queries than today's 38 — while leaving the gnark fold
   depth EXACTLY unchanged** (`R = logD₀ − lb = log₂T = 15` either way). **So the wrap pays for the
   degree only, and `EXT-DEGREE-COST.md`'s ~7.5–12M R1CS estimate survives.** Without that knob it does
   not.

> **The one-line answer to ember:** *Proven-120 is not reachable today and no knob gets there — it
> needs the ext-degree wrap rewrite, at `d = 8`, full stop. But it is ONE knob-set for the whole system
> (`d=8, lb=6, q=36, pow=16`, λ = 122.60 everywhere, 2.6 bits of margin), it costs a measured +25%
> prover / +20% wire, and — if the outer's blowup rises with the degree — the gnark wrap pays only the
> degree, not a doubled query loop. The gate is, as ever, Groth16 setup memory: ESTIMATED, and the one
> number in this document that a small lane could turn into a measurement before anyone commits.*

---

## 1. The method — what "proven" means here, and why not the formula

### 1.1 The composition

FRI soundness is **two columns**, never a product (`FriLedgerSound.query_ledger_does_not_determine_perFold`
is a theorem). ethSTARK (eprint 2021/582) eq. (20) composes them:

```
λ ≥ min{ −log₂ ε_C ,  ζ − s·log₂ α } − 1        α = √ρ·(1 + 1/2m),  m ≥ 3 integer
```

- **The commit column** `−log₂ ε_C` — BCIKS20 Thm 8.3, transcribed verbatim into
  `FriLedger.friCommitLedger`, parametric in `logD0` and `m`. **This document computes it, never
  approximates it.**
- **The query column** `ζ − s·log₂ α` = `pow + q·(lb/2 − log₂(1 + 1/2m))`.

⚠ **The ledger's `johnsonBits = q·lb/2 + pow` is the `m → ∞` IDEALISATION** — the Lean says so in its
own field doc. It is **optimistic**: at `d=8, lb=6, q=35, pow=16` it reads **121** (pass) where the
honest finite-`m` column reads **119.61** (fail). **Every number in this document uses the honest
finite-`m` column, and `m` is optimized as BCIKS20 permits.**

⚑ **`capacityBits` appears nowhere below.** The conjecture beneath it is **refuted** (Crites–Stewart
eprint 2025/2046). It is a **drift canary, never a security number**, and this design does not touch it.

### 1.2 The `m` tension — a third knob, and it is real

`m` is BCIKS20's Johnson-tightness parameter and it moves **both** columns in **opposite** directions:
`ε_C ∝ (m+½)⁷` (raising `m` **hurts** the ceiling) while `α → √ρ` (raising `m` **helps** the query
column). So `λ = max over m ≥ 3 of min{…}`. **This is why the ceiling is quoted at `m = 3`** (where
`ε_C` is smallest) but the *achieved* λ is usually at much larger `m`.

⚑ **A wire-window note, in our favour to know:** `FriLedger.epsCInWindow` caps `bciksM ≤ 64` — a **wire
guard, not BCIKS20's hypothesis** (which is only `m ≥ 3` integer). At `d = 8` the optimizer wants
`m > 64`. **The window costs exactly one query** (`q = 36` rather than 35). Every number below respects
the window, i.e. is conservative. Widening it is a one-line change worth one query.

### 1.3 ⚑ ember's ceiling equation, CHECKED against the mechanized ledger

`CEILING = 30.907·d − 12.65 − 2·log₂(T) − 3.5·lb` (which already folds in `log₂(2|F|)`'s `+1` and
eq. (20)'s `−1`; they cancel). Checked at 60 points across `d ∈ {4,5,6,8}`, `lb ∈ {3,6,7}`,
`log₂T ∈ {6,8,13,16,19}`:

| | analytic | mechanized ledger | delta |
|---|---:|---:|---:|
| d=4, T=2^6, lb=6 (the leaf anchor) | 77.98 | **77** | −0.98 |
| d=4, T=2^16, lb=6 (**the apex**) | 57.98 | **57** | −0.98 |
| d=8, T=2^16, lb=6 | 181.61 | **181** | −0.61 |
| d=6, T=2^16, lb=6 | 119.79 | **119** | −0.79 |
| d=5, T=2^19, lb=3 | 93.38 | **92** | −1.38 |

> ⚑ **The formula is CONFIRMED in shape and is uniformly 0.6–1.5 bits OPTIMISTIC.** The gap is the
> ledger's deliberate conservatism (`Nat` floor + an `ε_C` numerator that rounds **up**). **At a 120
> boundary that gap decides configs**: the formula says `d=6, lb=6, T=2^15` = **121.79**; the ledger
> says **121**. Design to the ledger.

---

## 2. ⚑ The apex-height discrepancy — RESOLVED

ember: *"One lane says the apex is 2^22 → 57.98; the height census tops at 2^19 → 61 — resolve or
flag."*

**RESOLVED: the apex is `2^22`. The census is wrong, and so is the Lean theorem.**

The wrap step binds its config and its params eight lines apart, and they are **not** the pair the
census assumes:

| line | binding |
|---|---|
| `circuit-prove/src/accumulator.rs:646` | `let config = ir2_leaf_wrap_config();` — **log_blowup = 6** |
| `circuit-prove/src/accumulator.rs:654` | `let fold_params = if self.wrap_enabled { wrap_params() }` — the `2^16` floor, **default on** (`:425-430`) |
| `circuit-prove/src/accumulator.rs:783` | **both** passed to `build_and_prove_aggregation_layer_with_expose(…, &config, …, &fold_params, …)` |

`IR2_INNER_LOG_BLOWUP = 6` (`ivc_turn_chain.rs:869`) is minted into the **output** proof, not merely
verified: `create_recursion_config_for_inner_fri` sets **both** the StarkConfig PCS (which mints) and
the `FriVerifierParams` (`plonky3_recursion_impl.rs:419-467`, whose own docstring says so).

⟹ **`|D⁰| = 2^16 · 2^6 = 2^22`**, and `create_recursion_config` (lb = 3) **is never called on this
path**.

**Three artifacts are wrong and should be corrected (not by this document):**

| artifact | error |
|---|---|
| `FriLedgerSound.lean:692` row 4 | pairs `recursionConfig` (lb=3) with `logD0 = 19`, a height sourced from a floor applied only to lb=6-minted tables. **The docstring at `:670-672` names this exact error as the one a parametric ledger exists to prevent.** |
| `fri_trace_height_measure.rs:133` | `DEPLOYED_WORST_LOG_D0 = WRAP_LOG_CEIL + RECURSION_FRI_LOG_BLOWUP = 19` — same mispairing, and `:293-299` **asserts** it |
| `plonky3_recursion_impl.rs:385-392` | stale comment: *"the recursion PROVER side is unchanged from `create_recursion_config` (log_blowup=3)"* — **false of the code beneath it** |

⚑ **Consequence: the deployed posture is 57, not 61.** The tree is **4 bits optimistic** about its own
worst case, and the census's warning about *"~2 bits per doubling"* guards a number two doublings
stale.

⚑ **A second, unmeasured config falls out.** `ir2LeafWrapRotatedConfig` (lb=6, arity 2 —
`FriLedgerSound.lean:277`) has **no row at any recursion height** in
`ledger_commitBits_at_measured_heights`; its only lb=6 rows are the *leaf* at `logD0 = 14` and the
fixture at `12`. The rotated aggregation **root** runs at natural heights (`joint_turn_recursive.rs`
uses `ProveNextLayerParams::default()` at every node — `:284, :536, :648, :771, :858, :959`; no floor)
over measured `degree_bits [9,9,15,14,15]` ⟹ **`|D⁰| = 2^21`**. **Two shipped `|D⁰|` (2^22, 2^21)
exceed the "deployed worst case" the tree pins.**

---

## 3. ⚑ THE SOLVE — both columns ≥ 120, per shipped config

### 3.1 Where every shipped config stands TODAY (d = 4)

Honest eq. (20), on the mechanized ledger, each config at **its own** measured height:

| config | lb | q | pow | T | \|D⁰\| | ceiling | **λ** |
|---|---:|---:|---:|---:|---:|---:|---:|
| `prodV1Config` (v1 per-turn) | 3 | 38 | 16 | 2^6 | 2^9 | 87 | **70.50** |
| `zkConfig` (shielded lane) | 3 | 38 | 16 | 2^6 | 2^9 | 87 | **70.50** |
| `ir2_config` (leaf, arity 8) | 6 | 19 | 16 | 2^8 | 2^14 | 73 | **69.00** |
| `ethWrapOuterConfig` (gnark outer) | 3 | 38 | 16 | 2^15 | 2^18 | 69 | **65.54** |
| `recursionConfig` | 3 | 38 | 14 | 2^16 | 2^19 | 67 | **63.54** |
| **`ir2_leaf_wrap` (THE APEX)** | 6 | 19 | 16 | **2^16** | **2^22** | **57** | **57.00** |

**Nothing ships above 71. The artifact a light client verifies reads 57.** Proven-120 is **63 bits
away** on the binding config.

### 3.2 The ceiling map — the only question that matters first

`ceiling = max λ at ANY (q, pow)` = mechanized `commitBits(m=3) − 1`. **If the ceiling is below 120, no
query budget and no grind reaches 120.** MECHANIZED:

| d | lb=3 | lb=4 | lb=5 | lb=6 | lb=7 | lb=8 |
|---|---:|---:|---:|---:|---:|---:|
| **4** @ apex T=2^16 | 67 | 64 | 60 | **57** | 53 | 50 |
| **5** @ apex T=2^16 | 98 | 95 | 91 | 88 | 84 | 81 |
| **5** @ **T=2^6** (its best case anywhere) | **118** ⚠ | 115 | 111 | 108 | 104 | 101 |
| **6** @ apex T=2^16 | 129 | 126 | 122 | **119** ⚠ | 115 | 112 |
| **6** @ apex T=2^15 (free lever) | 131 | 128 | 124 | **121** | 117 | 114 |
| **8** @ apex T=2^16 | 191 | 188 | 184 | **181** | 177 | 174 |

> ⚑ **`d = 5` IS DEAD.** Its ceiling **anywhere a shipped config lives** tops out at **118** — at
> `T = 2^6, lb = 3`, which is exactly `prodV1Config`'s shape. It misses 120 **at the smallest trace in
> the system**, by 2 bits, before a single query is bought. `MIN_TRACE_HEIGHT = 64 = 2^6`
> (`circuit/src/effect_vm/trace.rs:508`) pins the v1 main table and **no shipped config has `T < 2^6`**.
> **There is no cheaper corner. The answer to ember's "lower T + d=5" is NO** — it would need `T ≤ 2^5`,
> which does not exist here, and it would still have to hold at the 2^16 apex, where d=5's ceiling is 88.

> ⚑ **`d = 6` FAILS at the deployed apex.** `lb = 6, T = 2^16` ⟹ ceiling **119**. ember's "~124" is
> `d=6` at **lb=3**; the apex is lb=6. **120 is unreachable at any `(q, pow)`.** It is rescued only by
> the free trace lever (→ **121**, `q = 38 @ pow 16`) or by dropping `lb` to 5 (→ 122, `q = 41 @ pow 26`).
> **A 1–2 bit margin bought with a near-cap grind is not a margin.**

### 3.3 ⚑ THE lb TENSION, characterized

ember: *"raising `lb` helps the query column (`+q·lb/2`) but hurts the commit ceiling (`−3.5·lb`) —
find the real optimum, do not assume mine."*

**The tension is real but it is CONDITIONAL: it exists only while `ε_C` binds.** The `min{}` decides.

At **d = 8, apex T = 2^16**, cheapest `(q, pow)` clearing 120 at each `lb`. ⚠ *This table minimizes
`q`, so it pushes `pow` to its practical cap (26–27) — it is the **shape** of the lb lever, not the
recommendation. §3.4 deliberately keeps `pow` at the deployed **16** and pays the difference in
queries (32 → 36), because grinding has been refuted as cheap twice and the cap is hard.*

| lb | ceiling | q | pow | m* | λ |
|---:|---:|---:|---:|---:|---:|
| 3 | 191 | 64 | 26 | 46 | 120.28 |
| 4 | 188 | 48 | 26 | 35 | 120.46 |
| 5 | 184 | 38 | 27 | 28 | 120.57 |
| **6** | **181** | **32** | 26 | 23 | 120.64 |
| 7 | 177 | 27 | 27 | 39 | 120.20 |
| 8 | 174 | 24 | 26 | 18 | 120.73 |
| 10 | 167 | 19 | 27 | 14 | 120.79 |

> ⚑ **At `d = 8` there is NO tension.** The ceiling (191 → 167) never comes within **45 bits** of the
> target, so the `−3.5·lb` cost is invisible and **higher `lb` is monotonically better** — the query
> bill falls 64 → 19. **The classic frontier is restored and the deployed high-blowup design is
> VINDICATED.** The tension in `FRI-BOTH-WIN-LEVERS.md` §4.1 exists **only** because `d = 4` pins us
> against the ceiling.
>
> ⚑ **At `d = 6` the tension BITES** — the ceiling *is* the binding constraint at lb=6 (119 < 120), so
> `lb` must come **down** (5 → 122, 3 → 129) and the query bill goes **up** (41 → 67). **d=6 is the only
> degree where ember's tension is the real design problem.** That is a reason to avoid it, not to
> pursue it.
>
> **So: do not optimize `lb` against the ceiling. Pick the degree that makes the ceiling irrelevant,
> then `lb` is a pure wire/prover trade — which is the knob we already know how to tune.**

### 3.4 ⚑ THE ANSWER — one knob-set, every shipped config

Because at `d = 8` the **query column binds everywhere**, and the query column contains **no trace
height**, every config reads the **same** number:

> ### **`d = 8, lb = 6, q = 36, pow = 16` ⟹ λ = 122.60 on EVERY shipped config**

| config | T | \|D⁰\| | ceiling | **λ** | |
|---|---:|---:|---:|---:|---|
| `prodV1Config` | 2^6 | 2^12 | 201 | **122.60** | PASS |
| `zkConfig` | 2^6 | 2^12 | 201 | **122.60** | PASS |
| `ir2_config` (leaf) | 2^8 | 2^14 | 197 | **122.60** | PASS |
| `ethWrapOuterConfig` | 2^15 | 2^21 | 183 | **122.60** | PASS |
| `recursionConfig` | 2^15 | 2^21 | 183 | **122.60** | PASS |
| **`ir2_leaf_wrap` (apex)** | 2^15 | 2^21 | 183 | **122.60** | PASS |

**2.6 bits of margin, uniformly.** `pow` stays at the **deployed 16** — no grind escalation, which
matters because *"pow grinding is nearly free"* has been refuted twice and the practical cap is 27
(`grinding_challenger.rs:113` asserts `bits ≤ 30`; the witness search is an exhaustive
`.expect(…)` ⟹ a prover **panic**, not a retry, at 15.3% incidence by 30).

⚑ **The one knob that must move besides the degree: `lb` 3 → 6 at the v1/outer/recursion configs.**
Keeping `lb = 3` also clears 120 — but at **`q = 71`**, and that query count is what the gnark wrap
pays for (§4.2). **Unifying at lb = 6 is what makes the wrap affordable.**

⚑ **`λ` is identical at T=2^15 and T=2^16.** At `d=8` the trace-height lever buys **exactly 0 proven
bits** (§3.5). It is in the recommendation for its **prover time**, not its bits.

---

## 3.5 ⚑ The trace-height lever — how far can T go, and is it a cheaper route to 120?

**Answer: it is not a route to 120 at all. It is worth +2 bits, once, and then it stops — and at the
recommended `d = 8` it is worth ZERO bits. Take it anyway, for the ~2× prover.**

⚑ **The finding that bounds it, and it corrects `EXT-DEGREE-COST.md` §4:** `WRAP_LOG_CEIL` is applied
as **`with_min_trace_height`** (`accumulator.rs:247`) — **a FLOOR, not a cap.** It cannot pull a table
below its natural height. The measured natural heights are `[9, 9, 15, 14, 15]` (`accumulator.rs:227`,
recorded at depth 2 **and** 3) ⟹ **natural max = 2^15**. So `|D⁰| = max(natural, floor) · 2^lb`:

| `WRAP_LOG_CEIL` | max table | \|D⁰\| | Δ proven (d=4) | Δ proven (**d=8**) |
|---:|---:|---:|---:|---:|
| **16 (deployed)** | 2^16 | 2^22 | — | — |
| **15** | 2^15 | 2^21 | **+2.00** | **+0.00** |
| 14 | **still 2^15** | **still 2^21** | **+0.00** | **+0.00** |
| ≤ 14 | still 2^15 | still 2^21 | **+0.00** | **+0.00** |

> ⚑ **`EXT-DEGREE-COST.md` §4's *"`WRAP_LOG_CEIL` 16 → 14: +4.00 bits"* is NOT PURCHASABLE BY THE
> KNOB.** Lowering a floor below the natural max does nothing at all. To go below `2^15` the **tables
> must shrink** — that is `apex_shrink`'s ~752 opened columns (`apex_shrink.rs:141`) and the
> **layout optimizer**, a real project, not a constant.

**What the ceiling buys, and what breaks if it drops.** The floor exists so the FRI shape
(`num_phases = log_max_height − log_blowup`) is **constant across depth**, so the next layer's verifier
op-list — its VK core — does not drift. At floor `2^16` that holds even if the natural max grows to
`2^16`; at floor `2^15` it holds **only while the natural max stays ≤ 2^15**. **The pad is one doubling
of safety margin, and dropping it spends that margin.** Two honest mitigations: the natural max is
**measured constant at depths 2 and 3**, and the depth-invariance test (`accumulator.rs:470`) is the
gate that would catch a regression. **And the ceiling already fails to deliver constant VK anyway** —
`accumulator.rs:219-234` concedes the op-list and the preprocessed commitment **still drift with
depth**; the floor closes the height half only. So the margin being spent is protecting a property that
is **not currently achieved**.

**Verdict.** `16 → 15` is a genuine free both-win — **+2 proven bits at d=4, and ~2× less apex prover
work** (the apex fold is an 18-minute prove) — and it is **degree-independent, zero wire, zero wrap
cost**. **Do it regardless.** But **it is not a route to 120**: at `d = 4` it takes the apex 57 → 59,
and the target is 120. **Only degree moves the ceiling.**

---

## 4. ⚑ THE CANDIDATE TABLE — cost, with every label

### 4.1 The candidates

| # | (d, lb, q, pow, T) | **proven λ** | reaches 120? | prover | proof | wrap | engineering |
|---|---|---:|---|---|---|---|---|
| **0** | **d=4, lb=6, q=19, pow=16, T=2^16** — *deployed* | **57.00** | **no** — ceiling 57 | 1.00× | 120 KiB | 4.98M | — |
| 1 | d=4, lb=6, q=19, pow=16, **T=2^15** | 59.00 | **no** — ceiling 59 | **~0.5×** apex | 120 KiB | 4.98M | **free** (`WRAP_LOG_CEIL`) |
| 2 | **d=5**, any lb, any q, any pow, **any T ≥ 2^6** | **≤ 118** | **NO — ANYWHERE** | +7% | +4.6% | ~6–7M | wrap rewrite **+ W: 11→2** |
| 3 | **d=6**, lb=6, T=2^16 | **≤ 119** | **NO** | ~+15% (EST) | ~+12% (EST) | ~6.5–9M (EST) | wrap rewrite **+ FORK of 18 crates** (orphan-blocked) |
| 4 | d=6, lb=6, q=38, pow=16, **T=2^15** | **121.00** | yes — **1 bit** | ~+15% (EST) | ~250 KiB (EST) | ~6.5–9M (EST) | wrap rewrite **+ FORK of 18 crates** (orphan-blocked) |
| 5 | d=6, lb=5, q=41, pow=26, T=2^16 | 120.00 | yes — **0 bits** | ~+15% (EST) | ~245 KiB (EST) | ~6.5–9M (EST) | as #4, **+ near-cap grind** |
| **6** | **d=8, lb=6, q=36, pow=16, T=2^15** ⭐ | **122.60** | **YES — 2.6 bits** | **+25%** | **252 KiB** | **~7.5–12M** (EST) | wrap rewrite + p3-recursion `8 =>` arm; **no fork, no W change** |
| 7 | d=8, lb=6, q=34, pow=20, T=2^15 | 120.6 | yes | +25% | 240 KiB | ~7.5–12M (EST) | as #6 + 4 grind bits |
| 8 | d=8, lb=3, q=71, pow=16, T=2^15 | 120.70 | yes | +25% | **~350 KiB** | **~14–22M** (EST) | as #6, **1.87× wrap query loop** |

**Labels.** Prover / proof deltas at d=5 and d=8 are **MEASURED** (`EXT-DEGREE-COST.md` §1.2/§1.4,
`circuit-prove/tests/ext_degree_cost_measure.rs`, min-of-3, deployed-realistic width 128). **d=6 is
ESTIMATED by interpolation and has never been measured — nothing can run it** (§5). Proof sizes are the
fitted model `20561 + q·(3971 + 239·lb)` (reproduces 6 measured points to <0.25 KiB) × the **measured**
d-scaling. Wrap R1CS at d≠4 is **ESTIMATED**; at d=4 it is **MEASURED** (4,980,767).

### 4.2 ⚑ The gnark wrap — the real gate, and the knob that saves it

**The gate is Groth16 SETUP MEMORY, not prove time**: 23 GB / 13m11s at 12.2M R1CS
(`HORIZONLOG.md:8375`, `docs/deos/ETH-NATIVE-WRAP.md:6`); prove is 16.7 s — a rounding error. **VK size
is d-independent** (2,576 B — a function of the 26 public inputs only, all base-field).

⚑ **The coupling nobody has priced: a 120-config raises `q`, and the wrap's cost is `q`-proportional.**
The wrap loops Poseidon2Bn254 (240 R1CS) × Merkle levels × **queries**; FRI core (1.86M, 37.3%) and
`open_input` (2.47M, 49.6%) are both largely per-query. **`EXT-DEGREE-COST.md`'s ~7.5–12M estimate
holds `q` at 38.** A 120-config at the outer's deployed `lb = 3` needs **`q = 71`** ⟹ **1.87× the query
loop, on top of d=8's 2.35× ExtMul** ⟹ **ESTIMATED ~14–22M R1CS and ~35–50 GB setup** — which would
likely break the box.

> ### ⚑ **The knob that saves it: raise the OUTER's `lb` 3 → 6 with the degree.**
> | outer config | q to clear 120 @ pow 16 | wrap query loop vs today |
> |---|---:|---:|
> | lb=3 (deployed) | **71** | **1.87×** |
> | lb=4 | 53 | 1.39× |
> | lb=5 | 43 | 1.13× |
> | **lb=6** | **36** | **0.95× — FEWER than today's 38** |
>
> **And the gnark fold depth does not move at all:** `R = log₂|D⁰| − lb = log₂T = 15` at **both** lb=3
> (2^18) and lb=6 (2^21). **The wrap circuit's structure is unchanged; only the d² parts grow.** ⟹
> **`EXT-DEGREE-COST.md`'s ~7.5–12M / ~15–25 GB estimate survives, and candidate #6 is the affordable
> one.**
>
> ⚠ **The price, named and UNMEASURED:** the outer's LDE domain goes `2^18 → 2^21` — **8× the outer
> shrink prove's FFT/Merkle work**, which is the base-field 85% that degree cannot touch. **This is a
> real prover cost on the apex path and this document does not measure it.** It is the one new cost the
> recommendation introduces, and it is the next thing to measure after the wrap.

⚑ **Two `ReduceBounded` bound comments are ALREADY WRONG at d=4**, before anyone touches the degree
(`babybear.go:11-12` says *"qBits ≤ 38"* and `:84-85` says *"widest accumulation is < 2^68"*; the widest
is **2^77**, `stark_open_input.go:292`). These are **soundness constants that fail silently** — the Go
compiler catches array shapes, never a stale bound. **Fix them before the degree work, not during.** At
d=8 the derived bounds are `extMulRawInto` 69, `S_z` 78, `S_x` 71, `ExtFromBasis` 38 (**COMPUTED** from
`boundBits(d) = 62 + ceil(log₂(1 + W·(d−1)))`, which reproduces the deployed 68 exactly).

### 4.3 ⚑ The estimate that should be a measurement — and it is a small lane

`TestSettlementGadgetMarginalCosts` (`chain/gnark/settlement_profile_test.go:396-412`) already isolates
the `ExtMul`/`ExtAdd` marginals and **reproduced the measured 92 R1CS exactly**. **It has never been run
at `d ≠ 4`.** Parameterizing `BBExt` by degree and re-running it — plus a phase-stripped compile at the
recommended `(d=8, lb=6, q=36)` — **replaces this document's last estimate with a measurement, for a
fraction of the rewrite's cost, before committing to it.**

⚠ **And the surface is unguarded:** `settlement_profile_test.go` asserts **no absolute R1CS count**
(`:209-214` compares twin-vs-real, not a golden), both heavy tests are env-gated, **gnark never runs in
CI** (`.github/workflows/armed-teeth.yml:90`), and `chain/gnark/README.md:42` still says "~12.2M R1CS",
two generations stale. **A 2× regression passes silently today.** Put a golden count on it **first**.

---

## 5. ⚑ The d=6 question — scoped honestly

ember: *"d=6 is exactly the arbitrary-gap degree — tantalizing. If it is the sweet spot, what would
implementing it take? Days or months?"*

**It is not the sweet spot, and the reason is arithmetic, not effort: `d = 6` FAILS at the deployed
apex** (ceiling **119** at lb=6, T=2^16). It clears 120 only *with* the free trace lever (**121**, a
1-bit margin) or by dropping `lb` to 5 and grinding at **pow = 26** against a practical cap of 27
(**0-bit margin**). Meanwhile `d = 8` reads **181** at the same shape — **60 bits of margin** — and
**ships in plonky3 today**.

The mathematics is genuinely ready, and `FRI-BOTH-WIN-LEVERS.md` §3 is confirmed: **X⁶ − 22 is
irreducible over BabyBear** (Rabin-verified; `W₆ = 22 = 11 × 2`, literally plonky3's own d=4 and d=8
constants multiplied), all five constants are **computed**, and the trait needs **exactly those five
plus one associated type** (`monty-31/src/data_traits.rs:116-142`) — `type ArrayLike = [[BabyBear; 6]; 1]`
(EXT_TWO_ADICITY 28 − TWO_ADICITY 27 = one generator, which matches). **The impl is ~10 lines and is the
easy part.** But three things kill it:

1. **⚑⚑ ORPHAN-BLOCKED — `d = 6` REQUIRES FORKING PLONKY3.** `BinomialExtensionData<6>` is defined in
   **p3-monty-31** (`monty-31/src/data_traits.rs:116`) and `BabyBearParameters` in **p3-baby-bear**
   (`baby-bear/src/baby_bear.rs:13`). Both foreign; the const-generic `6` is not a local type and does
   not cover the impl. **Rust forbids it.** *This is exactly why d=5 and d=8 need no fork: their impls
   already exist upstream* (`baby_bear.rs:76`, `:92`). ⚑ **The newtype escape hatch fails too** — a
   local `BabyBearParams6` is orphan-legal but yields a **distinct type** from `BabyBear`, breaking
   every `ExtensionField<BabyBear>` bound in the tree, **and it still hits the panic below.** dregg
   consumes `Plonky3/Plonky3` at upstream rev `82cfad7` across **18 crates** (`Cargo.toml:213-230`);
   d=6 converts all 18 to a fork we own and must rebase **forever**.
2. **⚑ The panic gate is real and is not patchable from outside.** `monty-31/src/extension.rs:21-33` is
   a **blanket impl** that overrides the D-generic default with `match WIDTH { 4|5|8 => …, _ => panic!
   }` at `:31`. So `BinomialExtensionField<BabyBear,6>` **compiles and then dies on the first scalar
   multiply.** The `*_mul_packed` helpers are `pub(crate)` ⟹ **the `6 =>` arm must live inside
   p3-monty-31.** *(The const assert at `:88-90`, `EXT_TWO_ADICITY ≥ TWO_ADICITY`, passes: 28 ≥ 27.
   Not a gate. And SIMD really is **optional** — `binomial_mul` `:677`, `binomial_square` `:712`,
   `try_inverse` `:353` are all D-generic, and the *packed* path bypasses the panic entirely, so the
   `6 =>` arm can simply route to the generic schoolbook.)*
3. **`W` changes 11 → 22**, so its gnark rewrite touches **every `BBExtW` site on both sides** — work
   `d = 8` skips entirely, because **d=8 keeps `W = 11`**. And **d=6 LOSES two-adicity relative to
   deployed d=4** (28 vs 29) — the same tooth that counts against d=5. **d=8 gains one (30).**

**Scope, honestly: WEEKS — call it 4–8 — and the tail is the wrap, not the field.** Hours for the
constants; 1–2 days for the `6 =>` arm + differential tests; days *plus a permanent rebase tax* for the
fork mechanics; ~1 week for the p3-recursion arm (§6); 2–3 days for dregg's 24 `const D` sites; **2–4
weeks for the gnark wrap** (85 `[4]`/`BBExt{…}` literal sites across 10 Go files); 1–2 weeks for
Groth16 re-setup + VK re-freeze + re-audit. **"Days" is only the field layer. "Months" overstates it
absent a wrap-memory surprise.**

> **Verdict: `d = 6` is strictly dominated by `d = 8`.** It **fails outright at the deployed apex**
> (119), it buys 121 where d=8 buys 183, and it costs a **permanent fork of 18 crates** plus a `W`
> change that d=8 does not need. **The tantalizing gap should stay closed.**
>
> ⚑ **Its real value is a finding, not a lane.** The d=6 impl + `6 =>` arm is a small, well-formed
> **upstream PR to Plonky3** (~30 lines, mirroring the existing d=5/d=8 shape, constants ready). If
> upstream took it, the fork tax would vanish. **That is worth doing on its own merits someday — it is
> not on dregg's critical path, and it should not be put there.**

---

## 6. ⚑ THE RECOMMENDATION, AND THE ORDER

### Is proven-120 reachable today? — **No. Plainly: it needs the ext-degree wrap rewrite.**

**No knob reaches it.** The deployed ceiling at the apex is **57**; the target is 120. Queries cannot
pass `ε_C` (it contains neither `q` nor `pow` — `query_and_pow_cannot_pass_epsC` is a theorem), the
trace-height lever is worth **+2 bits once and then nothing**, and `lb` is worth 3.5 bits a step in the
wrong direction. **`d = 4` is 63 bits short and the gap is not closable by tuning.** `d = 5` is short
**everywhere** and `d = 6` fails at the apex. **The recommendation is `d = 8`, and it is the only
configuration that clears 120 on every shipped config with margin.**

### The cheapest genuine proven-120 config

> ## **`d = 8, lb = 6, q = 36, pow = 16, WRAP_LOG_CEIL = 15`**
> **λ = 122.60 on every shipped config** (2.6 bits of margin) — one knob-set, one number, every
> artifact.
>
> **Cost:** **+25% prover** (MEASURED), **+20% proof** ⟹ apex ~120 → **252 KiB** (MEASURED d-scaling ×
> fitted size model), **verify +0.5–0.9 ms** (MEASURED, a non-event), **VK size unchanged** (2,576 B,
> d-independent). **Wrap: ESTIMATED ~7.5–12M R1CS / ~15–25 GB setup** — affordable *only because* the
> outer's `lb` rises with the degree, which holds its query loop at 36 vs today's 38.
>
> **Engineering:**
> - **The field: FREE.** `BinomialExtensionField<BabyBear, 8>` ships upstream (`baby_bear.rs:92`),
>   `octic_mul_packed` is a real SIMD arm at `monty-31/src/extension.rs:29` (**not** the `_ => panic!`),
>   `W` stays **11**, two-adicity **gains** one (29 → 30). **No plonky3 fork.**
> - **⚑ The recursion backend: a new arm, and this is the "backend enumeration" — it bites d=8 too.**
>   `recursion/src/backend/fri.rs:405-489` (our **already-forked** `emberian/plonky3-recursion`, rev
>   `0a4a554`) matches `proof.ext_degree` over **`1 | 2 | 4 | 5`** and errors on everything else —
>   **`8` is not in it.** Each arm is a monomorphized turbofish ⟹ **~20 new lines.** And
>   `poseidon2_config_for_air_builder<D>` (`circuit-prover/src/batch_stark_prover/poseidon2.rs:1611`)
>   returns `None` at d=8: there is no `BABY_BEAR_D8_W16` (`circuit/src/ops/poseidon2_perm/config.rs:56-78`
>   has only D1_W16, D4_W16, D4_W24), so d=8 follows the **d=5 precedent** — route through the
>   base-field `BABY_BEAR_D1_W16` challenger (`fri.rs:192`, `new_d5`). **~1 week. Because the crate is
>   already ours, this is an edit, not a fork.**
> - **dregg: 24 `const D: usize = 4` code sites** (21 in `circuit-prove/src/`, 5 in tests) — 13 leaf
>   adapters, 2 AIRs, 3 apex/accumulator, **2 named consts that are the real knobs and that nothing
>   links** (`dregg_outer_config.rs:125` `OUTER_EXT_DEGREE`, `plonky3_recursion_impl.rs:90`
>   `RECURSION_EXT_DEGREE`), 1 GPU (`gpu_backend.rs:3702`). **2–3 days**, mechanical.
> - **The gnark wrap — the tail: 2–4 weeks.** `type BBExt [4]frontend.Variable`
>   (`babybear_ext.go:23`) is a **type-level arity**, not a constant: **85 `[4]`/`BBExt{…}` literal
>   sites across 10 Go files**, 3 unrolled kernels, 7 d-hardcoded circuit sites, 4 host twins,
>   `ExtInv`'s Fermat exponent, a `DTH_ROOT`/generator re-pin, **4 bound constants that fail silently**,
>   and **a full VK re-key across every consumer** (`DreggGroth16Verifier25.sol`, the pinned
>   `DreggApexRecursionVk` fingerprint at `apex_shrink_gnark_export.rs:192-233`). **No `W` change.**
> - **Groth16 re-setup + VK re-freeze + descriptor regen + re-audit: 1–2 weeks.**
>
> **⟹ WEEKS, not days — call it 4–8, dominated by the wrap.** Same order as d=6, **minus the permanent
> fork tax and the `W` change, and for 60 more bits of margin.**

### The order — free both-wins first, the deciding measurement second, the rewrite last

1. **`WRAP_LOG_CEIL` 16 → 15.** **+2 proven bits at today's d=4 (57 → 59) and ~2× less apex prover
   work.** Free, zero wire, zero wrap, degree-independent. Gate it on the depth-invariance test; the
   margin it spends protects a property (constant VK) the tree **does not currently achieve** anyway.
   **Do it regardless of everything below.**
2. **Correct the three wrong artifacts** (§2): `FriLedgerSound.lean:692` row 4, `fri_trace_height_measure.rs:133`,
   `plonky3_recursion_impl.rs:385-392` — **and add the missing `ir2LeafWrapRotatedConfig` rows.** The
   tree currently believes it is 4 bits sounder than it is. **This is free and it is a correctness fix
   to the ledger that every later decision reads.**
3. **Fix the two stale `ReduceBounded` comments and put a golden absolute R1CS count on
   `settlement_profile_test.go`.** Small; retires the silent-failure class **before** the degree work
   can land inside it.
4. **⚑ Parameterize `BBExt` by degree; run `TestSettlementGadgetMarginalCosts` + a phase-stripped
   compile at `(d=8, lb=6, q=36)`.** **This is the lane that actually decides**, and it is small: it
   replaces this document's last estimate — **the setup-memory gate** — with a measurement, for a
   fraction of the rewrite's cost.
5. **Measure the outer `lb` 3 → 6 prover cost** (`|D⁰|: 2^18 → 2^21`, 8× the outer shrink's base-field
   work). It is the one cost this design introduces that nobody has priced.
6. **Then, and only then, the d=8 rewrite** — against a measured wrap cost and a measured prover cost.

⚑ **Steps 1–3 are free, land today, and are worth doing whatever ember decides about the degree.**
Steps 4–5 cost a lane each and turn the last two estimates into measurements. **Step 6 is the only
expensive thing here, and it should not start until 4 and 5 have reported.**

---

## 7. What could still be wrong with this design

Stated so it can be attacked:

- **The wrap R1CS and setup memory at d=8 are ESTIMATED.** They are the **gate**, and they are the one
  thing here that decides feasibility. §4.3 is how to settle it. **Named, not closed.**
- **The outer `lb` 3 → 6 prover cost is UNMEASURED** (8× the outer LDE). It is what makes the wrap
  affordable, so it must be priced before the rewrite.
- **The ext-cost harness's AIR is a proxy** (`EXT-DEGREE-COST.md` §1.5): single-table uni-stark, where
  deployed is multi-table batch-STARK with LogUp. LogUp fractions are EF-valued, so the deployed
  extension fraction is plausibly **above** the measured 14–18% ⟹ d=8 plausibly **above** +25%.
- **The GPU prover path is not measured at any degree** (`gpu_backend.rs`, `const D: usize = 4`).
- **This design stands on BCIKS20.** Under **BCSS25** (SOTA, `ε_C` linear in `n`) every ceiling here
  rises by ~17–31 bits and `d = 5` or even `d = 4` might reach 120 — **but BCSS25 states no FRI
  soundness theorem at all**; it defers to [BCIKS20]/[HLP24]/[Sta25], and **[Sta25] is a personal
  communication**. `p3-whir` transcribes it for WHIR, not FRI, and is not a dependency.
  `FriLedger.lean`'s citation block is explicit that composing it would be **our** unpublished
  assembly. ⚑ **If someone proves that composition, this entire document should be recomputed — it is
  the single highest-leverage alternative to the d=8 rewrite, and it is a mechanization task, not a
  knob.** It is also the only route by which proven-120 becomes reachable **without** touching the wrap.

---

## Provenance

| claim | label | source |
|---|---|---|
| every proven-bit figure, all configs | **MECHANIZED** — exact transcription of `friCommitLedger`, validated against **all 14** numbers `FriLedgerSound.lean` proves | `metatheory/Dregg2/Circuit/FriLedger.lean:322-339`; `FriLedgerSound.lean:647,657,692,714` |
| eq. (20) composition, finite-`m` query column | **DERIVED** — ethSTARK eprint 2021/582 eq. (20); BCIKS20 Thm 8.3 | `FriLedger.lean:206-288` (verbatim transcription) |
| ember's ceiling formula is 0.6–1.5 bits optimistic | **COMPUTED** — 60-point comparison vs the mechanized ledger | §1.3 |
| **apex = 2^22**, `create_recursion_config` unused on that path | **VERIFIED AT SOURCE** | `accumulator.rs:646,654,783`; `ivc_turn_chain.rs:869`; `plonky3_recursion_impl.rs:419-467` |
| rotated root = 2^21, natural heights, no floor | **VERIFIED AT SOURCE** | `joint_turn_recursive.rs:284,536,648,771,858,959`; `accumulator.rs:225-227` |
| `WRAP_LOG_CEIL` is a **floor**, so ≤14 buys 0 | **VERIFIED AT SOURCE** | `accumulator.rs:247` (`with_min_trace_height`), `:225-227` (natural max 2^15) |
| prover +25% (d=8) / +7% (d=5), proof +20% / +4.6%, verify | **MEASURED** | `circuit-prove/tests/ext_degree_cost_measure.rs`; `EXT-DEGREE-COST.md` §1.2/§1.4 |
| gnark ExtMul = 92 R1CS, circuit = 4.98M, phases, 23 GB setup | **MEASURED (in-repo)** | `HORIZONLOG.md:8465-8475`; `docs/deos/CROSS-CHAIN-SETTLEMENT-REALNESS.md:22` |
| `boundBits(d)` at d=5/6/8; ExtMul R1CS at d≠4 | **COMPUTED** — reproduces the deployed 68 / 92 exactly | `EXT-DEGREE-COST.md` §3.1/§3.6 |
| proof sizes at new (q, lb) | **MODEL** — `20561 + q·(3971+239·lb)`, fitted, <0.25 KiB on 6 measured points, × **measured** d-scaling | `FRI-BOTH-WIN-LEVERS.md` §4.1 |
| **gnark whole-circuit R1CS / setup peak at d=8** | **⚠ ESTIMATED — the gate** | §4.2; settle via §4.3 |
| **outer `lb` 3→6 prover cost** | **⚠ UNMEASURED** | §4.2 |
| d=6 prover/proof/wrap figures | **⚠ ESTIMATED** — d=6 cannot be run; nothing compiles it | §4.1 |
| X⁶−22 irreducible; the five d=6 constants | **COMPUTED** (Rabin; reproduces every published plonky3 constant) | `FRI-BOTH-WIN-LEVERS.md` §3.1 |
| `capacityBits` | **REFUTED conjecture — drift canary, never a security number** | `FriLedger.lean:60-88` (Crites–Stewart eprint 2025/2046) |
