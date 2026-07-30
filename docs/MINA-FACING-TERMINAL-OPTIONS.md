# The Mina-facing terminal: what ~460 Pickles slices actually buys, and the two levers that move it

**2026-07-30.** Companion to `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md`, which measures the cost of a
Kimchi circuit verifying dregg's **root** proof at deployed geometry. This document answers a
different question: *is that cost necessary?*

The answer is **no**, and the reason is not a FRI knob.

---

## 0. The finding, up front

| what Mina verifies | hash the FRI/MMCS uses | rows | slices @ 54,300 | trusted setup |
|---|---|---:|---:|---|
| **the ROOT — deployed today** | Poseidon2-BabyBear (foreign, 31-bit) | 2.46 × 10⁷ | **453** | none |
| the root, `arity 8` + `cap_height 8` + `q 16` | Poseidon2-BabyBear | 1.39 × 10⁷ | **255** | none |
| a plonky3-native SHRINK of the root ⚠ *re-knobbed; 390 at its current knobs, see §2* | Poseidon2-BabyBear | 9.8 × 10⁶ | **180** | none |
| **the ROOT, hashed with Mina-Poseidon over Pasta** | **Mina-Poseidon (NATIVE)** | **2.9 × 10⁶** | **54** | **none** |
| **a plonky3-native SHRINK, Pasta-hashed** ⚠ *re-knobbed; 67 at its current knobs* | **Mina-Poseidon (NATIVE)** | **1.6 × 10⁶** | **30** | **none** |

**The single biggest lever is not the FRI parameters and not the shrink. It is which hash the
Mina-facing proof commits with.** `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §0 already states the
fact this rests on and does not draw the conclusion:

> Kimchi's native Poseidon costs **11 rows** per permutation; this shape over a foreign 31-bit
> prime costs **2,600**. The ~236× is the reduction, not the hash.

Roughly **76% of the deployed budget is hashing** — Merkle paths 50%, leaf sponges 26% (my
decomposition below; the live leg-18 model independently puts hashing at ~84%). All of it is paid
in the expensive currency because the proof commits with Poseidon2-over-BabyBear, which a Pasta
circuit must emulate. Nothing forces that choice for a *Mina-facing* proof.

**dregg already does exactly this for Ethereum.** `DreggOuterConfig` exists so that the ETH-facing
proof commits with Poseidon2-**BN254**, turning a ~16,837-R1CS emulated BabyBear permutation into a
~243-R1CS native one — a measured 40.9M → 1.0M collapse (`circuit-prove/src/apex_shrink.rs:10-13`).
**Mina has no analogous config, and that is the whole gap.** The pattern is one foreign-hash
terminal per destination chain; Mina is missing its own.

⚠ **The Pasta rows are a PROJECTION from measured units, not a measurement.** See §4 for exactly
which inputs are measured and which are derived, and for the one probe that would settle it. The
projection is unusually robust in one specific way: after the swap, hashing is 0.6% of the budget,
so tripling the hash price moves the answer by under 2%.

---

## 0.1 ⚑ MEASURED SINCE — the probe ran, the config exists, and the headline held

**2026-07-30, later the same day.** §7's ordered plan was executed through step
3. Everything below is a measurement or a landed artifact; the paragraphs above
it are left as written so the projection and its check can be read against each
other.

### The probe (§4's named probe, §7 step 1) — `bridge/mina-zkapp/scripts/mina-poseidon-merkle-rows.ts`, `npm run mina-merkle`

| | this document ASSUMED | MEASURED (o1js 2.15.0) | vs deployed BabyBear |
|---|---:|---:|---:|
| one native Poseidon permutation | 11 (cited `POS_ROWS_PER_HASH`) | **13** | 2,600.5 → **200×** |
| one Merkle level (swap + hash) | ~15 (derived) | **15.5** | 2,677 → **173×** |
| one depth-22 opening | — | **342** | 58,971 → **172×** |
| one leaf-sponge BabyBear LANE | — | **3.69** | 329 → **89×** |

The cited **11** is kimchi's Poseidon *gate chain*; o1js charges 2 more rows for
the generic rows around it. The derived **15 rows/level** was right to 3% for
the wrong reason — the conditional swap is ~2.5 rows, not ~4.

The lane figure was never estimated here at all, and it is the second-biggest
hash term: the Pasta MMCS packs **16 BabyBear lanes per permutation** (8 shifted
radix-2^31 limbs × rate 2) against the deployed sponge's **8**. Half the
permutations *and* each 200× cheaper. Most of the residual 3.69 is the per-lane
range check, which is hash-independent and does not shrink.

### The re-measurement (§7 step 4's deliverable)

Each hash term scaled by its own measured unit ratio; the non-hash terms
unchanged (they are BabyBear extension arithmetic, which no hash choice touches):

| term | deployed | Pasta | ratio |
|---|---:|---:|---:|
| Merkle paths | 1.23 × 10⁷ | 7.12 × 10⁴ | 0.0058 |
| leaf hash + lane range checks | 6.50 × 10⁶ | 7.29 × 10⁴ | 0.0112 |
| challenger observe | 2.50 × 10⁶ | 1.25 × 10⁴ | 0.0050 |
| DEEP quotient | 2.50 × 10⁶ | 2.50 × 10⁶ | unchanged |
| AIR evaluation at ζ | 1.90 × 10⁵ | 1.90 × 10⁵ | unchanged |
| **total** | **2.40 × 10⁷** | **2.85 × 10⁶** | |
| **slices @ 54,300** | **442** | **53** | |

**53 against §0's projected 54 — 2.6% under. The projection held.** The Merkle
term is computed two independent ways (scaled, and directly from 238 levels ×
19 queries × 15.5) and the two land 1.6% apart; the script fails if they ever
diverge by more than 10%.

§3's prediction that the *shape* flips is confirmed and is sharper than written:
hashing was **89%** of the deployed budget and is **5.5%** of this one, and the
DEEP quotient is now **88%**. A 3× error in every measured Pasta hash price
moves the answer 53 → 58 slices. **The answer is no longer sensitive to the hash
at all**, which retires the hash as a lever and promotes column narrowing
(§7 step 6) to the next one.

### The artifacts (§7 steps 2 and 3)

- **`circuit-prove/p3-pasta`** (package `dregg-p3-pasta`) — Pasta `Fp` as a p3
  `PrimeField` plus kimchi's Poseidon as a p3 `CryptographicPermutation`.
  `p3-bn254` was the template. It delegates arithmetic to
  `mina_curves::pasta::Fp` rather than re-rolling Montgomery, because the Mina
  side of the bridge is *defined* over that type.
- **`circuit-prove/src/dregg_mina_config.rs`** — `DreggMinaConfig`, the twin of
  `dregg_outer_config.rs`. ⚑ Its FRI knobs are the ETH wrap's **element for
  element**, deliberately: the ledger reading is then the already-modeled
  `FriLedgerSound.ethWrapOuterConfig` and **the hash field is the only change**.
  It is an eighth row in `circuit-prove/tests/fri_params_soundness_budget.rs`.
- **`circuit-prove/src/apex_shrink.rs`** — the outer role is now generic over
  `OuterShrinkConfig`, a trait bound that *is* §2's soundness paragraph: a
  config not sharing `Val = BabyBear` / `Challenge = EF4` cannot be named in
  that position. A third destination chain is a config, not a change there.

### One real terminal proof, and the dregg-side price MEASURED

`circuit-prove/tests/mina_terminal_tooth.rs` folds the real 2-turn rotated
chain, terminates the apex under `DreggMinaConfig`, verifies it, refuses a
tampered opening, and shrinks the **same apex** under `DreggOuterConfig`
alongside for the comparison:

| | Mina-Poseidon terminal | Poseidon2-BN254 shrink | ratio |
|---|---:|---:|---:|
| prove | **280.0 s** | 179.7 s | **1.56×** |
| verify | 243.9 ms | 234.6 ms | 1.04× |
| proof bytes | 430,510 | 430,566 | 1.000× |
| `degree_bits` | `[9, 9, 15, 14, 15]` | `[9, 9, 15, 14, 15]` | identical |

§3's estimate — "~2× the S-boxes … expect ~150–200 s against the BN254 shrink's
~95 s" — was right about the *ratio* and this box is slower than the one that
measured 95 s. **1.56×, not 2×**: the prove is dominated by the blowup LDE, so
kimchi's 55 full rounds are diluted rather than doubling anything.

⚑ The two terminals share `degree_bits`, instance count and extension degree,
and the proof sizes agree to four digits — the hash swap really does change only
*what the commitment is computed in*. The test asserts that, and separately
asserts the two committed roots **differ**, which is the thing types cannot say:
that the swap reached the commitment instead of silently no-opping.

### The soundness answer, and one correction

The commitment-collision bar, by `RomQueryFloor.birthday_bound` at the real
field orders (`circuit-prove/p3-pasta/tests/commitment_birthday_bar.rs`):

| | digest space | bar |
|---|---:|---:|
| deployed BabyBear MMCS `[BabyBear; 8]` | 2^247.26 | Q ≈ **2^123.63** |
| ETH terminal `[Bn254; 1]` | 2^253.60 | Q ≈ **2^126.80** |
| **Mina terminal `[PastaFp; 1]`** | **2^254.00** | Q ≈ **2^127.00** |

The swap **raises** the bar: +3.37 bits on the deployed MMCS, +0.20 on the ETH
terminal. The sponge capacity moves the same way (2^247.26 → 2^254.00) and the
Mina digest is exactly the capacity, not a truncation. What does **not** move:
every FRI/DEEP bound is denominated in `EF4 = 2^123.63`, which the hash swap
does not touch — so the challenge field is still the binding constraint.

⚠ **§3 says "Pasta Fp is 254.6 bits". It is 254.000** — `p` is `2^254` plus a
190-bit tail, so `log2(p)` is 254 to seventeen places; BN254 is 2^253.60 for the
same reason read the other way. The ~127-bit conclusion §3 drew is right; the
input was not.

⚠ **What is not done, and it is the reason none of the row counts above are
deployed numbers:** the o1js verifier still hashes Poseidon2-BabyBear
(`Poseidon2Merkle.ts`). §7 step 5 is untouched. dregg can now MINT a Mina-native
proof; nothing on Mina consumes one. **A config that nothing consumes is a lever
built, not pulled.**

⚠ And one residual the soundness section names rather than buries: the Pasta ROM
idealization is named in-tree on the **Pickles** side
(`PicklesTranscriptBinding`'s `SpongeKeyedROFaithful`). Nothing points it at the
FRI/MMCS carrier sites the way `Poseidon2RomInstantiation` is pointed at the
BabyBear ones. An unconnected leg, not a hole.

---

## 1. Why the existing BN254 shrink is not the answer

`circuit-prove/src/apex_shrink_gnark_export.rs` is the shrink that exists. **Pointing Mina at it
would be strictly worse than pointing Mina at the root**, and it carries a cost ember has ruled out.

- Its FRI/MMCS commits with **Poseidon2-BN254** — a **254-bit** foreign modulus on Pasta. The root's
  BabyBear is a **31-bit** foreign modulus, which is the cheap case and the only reason a Kimchi
  verify is expressible at all (`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md:66-71`). Verifying the BN254
  shrink on Pasta moves *every* hash from the cheap foreign case to the expensive one, in exchange
  for a 16× smaller domain — a bad trade.
- The **Groth16 layer above it needs a trusted setup**, currently a single-party dev ceremony
  (`chain/gnark/settlement_snark_test.go:7-11`: *"whoever runs it knows the toxic waste and can
  forge proofs for this VK"*). Ember has ruled this out as a Mina lever, and correctly: a Mina
  bridge should not inherit a ceremony the STARK stack does not otherwise need.
- Verifying the **Groth16 proof itself** on Mina is not merely expensive, it is **blocked**: Kimchi
  has no Fp12/Fp6/Fp2, no Miller loop, no G2 (`docs/MINA-DREGG-ZKAPP-BRIDGE.md:110-129`, Route C).

**None of this is an argument against a shrink.** It is an argument against *that* shrink's outer
config. Which is the next section.

---

## 2. The plonky3-native shrink — it is already built, and the outer config is a monomorphisation

`circuit-prove/src/apex_shrink.rs` recursively verifies a real apex/root proof in-circuit and proves
that circuit under a second config. **The recursion is not BN254-specific; only the instantiation
is.** The module's own doc states the seam precisely (`apex_shrink.rs:34-40`):

> The split is sound because the two configs share `Val = BabyBear` and `Challenge = EF4`: the
> verifier circuit is a field-level object (`Circuit<EF4>`), its table AIRs depend only on
> `Val`/`Challenge`, and only the PCS/challenger — swapped wholesale via the outer config — touch
> the hash field.

### ⚑ Can dregg shrink its own root TODAY, with what exists? **Yes — and with no new code.**

There are two entrypoints, and only one of them is BN254-shaped:

- **One config for both roles** — `build_and_prove_next_layer_with_expose::<DreggRecursionConfig,
  ..>`. This is the ordinary BabyBear recursion layer, and it is exercised at **eight leaf adapters
  plus the GPU backend** (`membership`, `sovereign`, `factory`, `hatchery`, `presentation`,
  `custom`, `caveat_admission`, `blinded_membership`, `gpu_backend.rs:5320`). Pointed at the root's
  `RecursionOutput`, **this produces a BabyBear-hashed shrink of the root today.** No trusted setup,
  no new config, no generalisation. It is the same operation `RecursiveAggregation` performs at
  every turn-chain fold — the root is just the last thing that has not had it applied to it.
- **Split configs** — `apex_shrink.rs`, needed only when the *output* must be hashed differently
  from the *input*. That is the Pasta case, and the BN254 instantiation is the worked example.

So the plonky3-native shrink is not a thing to build; it is a thing to *call*. What has to be built
is only the Pasta variant of the second entrypoint.

`shrink_apex_to_outer(apex, inner_config, outer_config: &DreggOuterConfig)` names a concrete type,
but every step it re-plays is generic over `StarkGenericConfig` (`build_next_layer_circuit`,
`get_airs_and_degrees_with_prep`, `ProverData::from_airs_and_degrees`,
`BatchStarkProver::<SC>::prove_all_tables`). **Generalising the signature over
`SC: StarkGenericConfig<Val = BabyBear, Challenge = EF4>` is a mechanical change**, and it yields:

- **`DreggRecursionConfig` as the outer** → a pure-BabyBear shrink. No BN254, no ceremony.
- **A `DreggPastaConfig` as the outer** → the Mina-native-hash shrink, which is the recommendation.

### The shrunk geometry — MEASURED, from the real fixture

The shrink circuit's **trace shape is set by the INNER config** (the apex's knobs it re-verifies),
not by the outer hash. So the geometry below, read off the committed BN254 fixture
`chain/gnark/fixtures/apex_shrink_fri_real.json`, is **the same shape a Pasta- or BabyBear-hashed
shrink produces**:

| | ROOT (what Mina targets today) | SHRINK (measured) |
|---|---|---|
| `degree_bits` | `[10, 10, 16, 15, 3, 16, 0]` — 7 tables | `[9, 9, 15, 14, 15, 0]` — 6 tables |
| max trace | **2^16** | **2^15** |
| main columns | **940** (+175 prep, +56 quotient, +256 permutation) | **520** (+155 prep) |
| opened (matrix, point, column) DEEP terms / query | **2,630** (measured, `root-fri-braid.ts:844`) | **1,670** |
| `\|D⁰\|` | 2^22 (`lb 6`) | 2^21 at `lb 6`; 2^18 at the BN254 config's `lb 3` |
| fold rounds | 16 (arity 2) | 15 at `lb 3` arity 2; 5 at `lb 6` arity 8 |
| prove time | — | **~95 s** at blowup 8 (measured) |

So one recursion pass takes the trace **2^16 → 2^15** and the column census **940 → 520**. That is
where the shrink's ~1.8× Mina-side win comes from, and it is the *smaller* of the two levers.

### ⚠⚠ THE SHRINK'S BENEFIT IS CONTINGENT ON RE-CHOOSING ITS OUTER KNOBS, and I nearly quoted it without saying so

`DreggOuterConfig` runs at **`log_blowup 3`, arity 2, and 38 queries** — forced by its own soundness
gate, `3 × 38 + 16 = 130` (`dregg_outer_config.rs:135-138`). The blowup 64 → 8 rebalance that made
the shrink prove ~8× faster bought that **by doubling the query count**, and **Mina's cost is linear
in queries.** So:

| shrink, Pasta-hashed | slices | composite |
|---|---:|---:|
| at the **current** outer knobs (`lb 3`, arity 2, **q 38**) | **67** | 65 |
| re-knobbed (`lb 6`, arity 8, q 19) | 35 | 59 |
| re-knobbed (`lb 6`, arity 8, q 16) | **30** | 59 |

and at BabyBear hashing the same contingency is brutal: the shrink at its **current** knobs is
**390 slices** against the root's 453 — **essentially no win at all**. My §0 row quoting 180 assumes
the re-knobbed shape, and that assumption is load-bearing.

⚑ **Re-knobbing is free on the security side, but not for the reason it looks.** The shrink's own
composite falls 65 → 59, which sounds like a loss and is not: **the chain's composite is
`min(root, shrink)`**, because forging a root that genuinely satisfies the shrink's circuit is a
57-bit attack either way. The root binds at **57** in every row of that table. What re-knobbing
actually spends is the shrink's *prover* time (a larger blowup), which is dregg-side and cheap.

⚑ And the outer config's knobs are **pinned by gnark**, not free: `OUTER_FRI_MAX_LOG_ARITY = 1`
because *"`friFoldRowArity2` hardcodes the arity-2 fold; the gnark `FriConfig` carries no arity
field at all"*, and `OUTER_FRI_COMMIT_POW_BITS = 0` by a hardcoded gnark witness
(`dregg_outer_config.rs:139-158`). **A Mina-facing config is not subject to either** — which is one
more reason it should be its own config rather than a re-use of the ETH one.

### ⚠ Is there a fixed point? Not at the BN254 config's knobs — it GROWS

⚑ **First, the honest status: the question has never been run, and the repo forbids it by
construction.** `dregg_outer_config.rs:200-203` — *"It deliberately does NOT implement
`FriRecursionConfig`: … **no layer ever verifies an outer proof in-circuit** (gnark verifies it
natively)."* There is no code path that recursively verifies a shrink proof. What follows is a
structural computation from the repo's own per-query counts, not a measurement.

The verifier circuit's Poseidon2 term is `Q × (input levels + commit levels + leaf sponges)`:

| per query | root (\|D⁰\|=2^22, F=16, 19q, 940 cols) | shrink (\|D⁰\|=2^18, F=15, **38q**, 520 cols) |
|---|---:|---:|
| input Merkle levels | 4 × 22 = 88 | 4 × 18 = 72 |
| commit Merkle levels | Σ(21…6) = 216 | Σ(17…3) = 150 |
| leaf sponge perms | ~151 | ~84 |
| **subtotal** | **455** | **306** (0.67×) |
| **× queries** | × 19 = **8,645** | × 38 = **11,628** |

**⇒ 1.35× MORE permutations. The verifier circuit GROWS.** The per-query work does fall to 0.67×,
and doubling the query count more than cancels it. The Horner/ALU term moves the same way
(~0.55× columns × 2× queries ≈ 1.1×).

At `lb 6` / 19 queries it would instead contract to ~0.68×, with diminishing returns toward a floor
set by the verifier circuit's own irreducible content (the Poseidon2-W16 table alone is 300 columns).

**So "shrink twice" is not free and is not obviously worth it.** The query count of the *outer*
config is what decides whether recursion contracts, and `DreggOuterConfig`'s 38 were chosen for the
gnark path. Anything past one pass should be measured, not assumed.

⚠ **And the repo's own size model does not reproduce the one measurement it has.** Both terms above
predict ~2^13.3 where the measured shrink is **2^15** — short by ~2 bits on each. The `perm_model`
in `apex_shrink_trace_anatomy.rs:230-253` is a *prover*-cost model (it takes trace heights as input
and counts outer leaf-sponge permutations; its `LOG_BLOWUP = 6` is also stale against the deployed
`OUTER_FRI_LOG_BLOWUP = 3`), and `APEX-VERIFIER-AIR-REDUCTION.md:29-71`'s attribution asserts
"one permutation ≈ one W16-AIR row" while its own permutation count says otherwise. **There is no
validated circuit-size model in the tree**, so treat every projection in this subsection as
directional only. The measured `degree_bits` vector is the only thing here that is solid.

---

## 3. The lever that actually matters: hash the Mina-facing proof with Mina-Poseidon

`circuit-prove/sketches/mina-pasta-hash-probe` exists for exactly this and states it as a GO/NO-GO:

> can a Pasta-instantiated `DreggOuterConfig` hash its FRI MMCS with Mina-Poseidon so an o1js/Kimchi
> verifier hashes **natively**?

**Part A is landed and CI-gated.** `mina_poseidon_hash` (kimchi's own `ArithmeticSponge<Fp,
PlonkSpongeConstantsKimchi, 55>`) is pinned bit-for-bit to o1js `Poseidon.hash` gold vectors,
mirrored at `bridge/mina-zkapp/src/rust-gold-vectors.ts`, and `scripts/check-mina-attestation.sh`
fails if the two disagree. The probe also supplies the two MMCS primitives:

- `compress(l, r)` — the Pasta twin of `TruncatedPermutation`, **one permutation, digest = one
  native Fp**. On the o1js side this is *literally* `Poseidon.hash([left, right])` — one Poseidon
  gate chain, **11 rows** (`kimchi/.../poseidon.rs: POS_ROWS_PER_HASH = 11`), against **2,677
  measured rows** for a BabyBear-hashed Merkle level.
- `leaf_hash(row)` — the Pasta twin of `MultiField32PaddingFreeSponge`, packing 8 canonical BabyBear
  limbs per Fp (Pasta Fp is 254.6 bits — the same 8-limb budget BN254 already uses).

### What it does to the budget

Unit prices are named in §4. Per-query terms scale with `q`; once-terms do not.

| term | deployed (BabyBear-hashed) | Pasta-hashed, `arity 8` + `cap 8` + `q 16` |
|---|---:|---:|
| Merkle paths | 1.23 × 10⁷ (49.9%) | 1.4 × 10⁴ (0.6%) |
| leaf hash + lane range checks | 6.5 × 10⁶ (26.4%) | 1.3 × 10⁵ (5.2%) |
| DEEP quotient | 2.5 × 10⁶ (10.1%) | **2.1 × 10⁶ (84.8%)** |
| challenger observe of the opened values | 2.5 × 10⁶ (10.2%) | 1.3 × 10³ (0.1%) |
| AIR constraint evaluation at ζ | 1.9 × 10⁵ (0.8%) | 1.9 × 10⁵ (7.6%) |
| **total** | **2.46 × 10⁷ ⇒ 453 slices** | **2.5 × 10⁶ ⇒ 45 slices** |

⚑ **After the swap the problem changes shape entirely.** Hashing stops being the cost and the
**DEEP quotient becomes 85%** of it — and the DEEP quotient is BabyBear *extension arithmetic*,
which no hash choice and no FRI knob touches. It is priced per **(matrix, point, column)** term, so
the next lever after this one is `APEX-VERIFIER-AIR-REDUCTION.md`'s **column narrowing**, exactly as
`MINA-VERIFIES-DREGG-FRI-SIZE.md` §5.2 predicted — but arriving three levers earlier than expected.

⚑ **And the FRI knobs stop mattering almost entirely.** Isolated from the query count, `arity 8` +
`cap_height 8` together are worth:

| | BabyBear-hashed | Pasta-hashed |
|---|---:|---:|
| `q 19`, arity 2, `cap 0` | 24,574,325 (453 slices) | 2,923,071 (54) |
| `q 19`, **arity 8 + cap 8** | 15,935,540 (293) | 2,893,934 (53) |
| worth | **−35.2%** | **−1.0%** |

Both knobs exist to shorten Merkle paths, and after the hash swap Merkle paths are 0.6% of the
budget. **The single most-recommended FRI change in `MINA-VERIFIES-DREGG-FRI-SIZE.md` §5.1 — the
arity flip, called there *"the single largest avoidable cost in this whole document"* — is worth one
percent once the hash is native.** It is still worth taking on the dregg side for its own reasons;
it is no longer a Mina argument.

### What it costs to build

- A `DreggPastaConfig` — the direct twin of `dregg_outer_config.rs`, with `mina-poseidon` in place of
  `Poseidon2Bn254`. `mina-poseidon` and `mina-curves` are already pinned in the root `Cargo.toml`,
  and the probe already has the hash and both MMCS primitives.

  ⚑ **The one piece that does NOT exist, and it is the real cost of this lever: there is no
  `p3-pasta`.** `DreggOuterConfig` gets `Bn254` (a `p3_field::PrimeField`) for free from upstream
  `p3-bn254`; the Pasta side needs that written — a newtype over `mina_curves::pasta::Fp` (ark-ff)
  implementing p3's `Field`/`PrimeField`, plus a `CryptographicPermutation<[Fp; 3]>` adapter over
  `mina-poseidon`'s `ArithmeticSponge`. **`p3-bn254` is the template and it is a small crate.** With
  those two, everything above them drops in unchanged and generically:
  `MultiField32PaddingFreeSponge<BabyBear, Fp, Perm, 3, 2, 1>`,
  `TruncatedPermutation<Perm, 2, 1, 3>`, `MultiField32Challenger<BabyBear, Fp, Perm, 3, 2>` — the
  exact type shapes `dregg_outer_config.rs:166-189` already instantiates.

  The `TruncatedPermutation`/`Poseidon.hash` equivalence is not an assumption: permuting `[l, r, 0]`
  and truncating to one element **is** absorbing two lanes at rate 2 into a zero state and squeezing
  `state[0]`. The probe writes `compress` as `mina_poseidon_hash(&[left, right])` for that reason.

  ⚠ **Prover-side cost, not free:** kimchi's Poseidon is **55 full rounds** at width 3 (α = 7)
  against `Poseidon2Bn254`'s 8 full + 56 partial — roughly **2× the S-boxes per permutation**. The
  BN254 shrink proves in ~95 s, so expect a Pasta-hashed one nearer ~150–200 s. That is prover time
  on dregg's side, traded against ~15× fewer Kimchi rows on Mina's. Estimate, not measured.
- Generalising `shrink_apex_to_outer` over `SC` (§2) — or, since the root's own outer config is a
  choice too, minting the Mina-facing proof directly at `DreggPastaConfig` with no shrink at all.
  **That variant alone is 453 → 54 slices with no other change.**
- o1js-side: `Poseidon2Merkle.ts`'s permutation is replaced by native `Poseidon.hash`. The FRI walk,
  the coset descent, the fold arithmetic and the DEEP quotient are **unchanged** — they are BabyBear
  arithmetic and stay exactly as built and KAT'd.

### What it costs in trust

- **No trusted setup.** It is a STARK end to end. This is the property the Groth16 shrink lacks.
- **One carrier swap, and it must be named:** Mina-Poseidon (kimchi params, Pasta Fp) replaces
  Poseidon2-BabyBear as the MMCS/transcript hash. Digest is one Fp = 254.6 bits ⇒ ~127-bit collision
  resistance, against the BabyBear digest's 8 × 31 = 248 bits ⇒ ~124-bit. Comparable, and it is the
  hash Mina's own security already rests on.
- The FRI ledger arithmetic is **untouched** — `Val = BabyBear`, `Challenge = EF4` on both sides, so
  every number in `FriCommitPow.lean` reads the same. A Pasta-hashed shrink at `lb 6` over a 2^15
  trace sits at `|D⁰| = 2^21` rather than 2^22, which the ledger reads **2 bits higher**, not lower.

---

## 4. MEASURED vs DERIVED — read before quoting anything above

**MEASURED** (`getRows()` on committed, KAT'd, 2%-ratcheted o1js circuits):

| | value | authority |
|---|---:|---|
| Poseidon2-w16-BabyBear permutation | 2,600.5 rows | §3.8 |
| Merkle level, BabyBear-hashed | 2,677 rows | §3.9 |
| one whole FRI query, 16 layers | 684,726 rows | §3.10, `fri-query-rows.ts:333` |
| one query's commit phase | 623,310 rows | §3.13 |
| DEEP quotient, one query | 154,523 rows at 2,286 terms ⇒ **67.6 rows/term** | §3.15 |
| DEEP terms at the root | **2,630** — off the real proof | `root-fri-braid.ts:844` |
| emitted total, deployed root verify | **24,574,325** | `emitted-schedule.ts:349` |
| usable rows per Pickles step, `mpv = 1` | **54,300** | `PartitionSchedule.ts:105` |
| shrink `degree_bits` / columns / prove time | `[9,9,15,14,15,0]` / 520 / ~95 s | `apex_shrink_fri_real.json` |

**CITED UPSTREAM, not measured here:** Kimchi's native Poseidon at **11 rows/permutation**
(`POS_ROWS_PER_HASH`). I add ~4 rows for the conditional swap ⇒ **15 rows/Merkle level**.

**DERIVED:** the lane range check at **~7 rows** (§3.8 puts range gates at 38% of 2,600.5 across
~141 reductions). The packing of 8 lanes into one Fp is charged inside it.

**The whole Pasta column is therefore a PROJECTION.** Its robustness: Merkle paths are 0.6% of the
Pasta total, so a 3× error in the 15-row estimate moves the answer by **under 2%**. The dominant
term is the DEEP quotient at a **measured** 67.6 rows/term. The projection is sensitive to that
number and almost nothing else.

**The one probe that would settle it**, and it is small: an o1js circuit that walks a depth-20
Merkle path with native `Poseidon.hash`, KAT'd against the probe crate's `compress`, and reports
`getRows()`. That is the Pasta analogue of §3.9, and it converts this document's headline from a
projection to a measurement.

---

## 5. ⚑ ~460 slices is NOT infeasible, and that changes the argument

Seven slices of the root-AIR chain ran in **29 minutes wall** across seven processes (171 s compile
+ 63 s prove per slice). At that rate 460 slices is **~4 hours at 7-way parallelism and under two at
16-way** — one long run, not a wall. So none of the above is *required*; it is a question of what a
Mina settlement should cost per dregg root, not whether it can happen at all.

That said, the gap between **453 slices** and **30** is the difference between "a batch job" and
"a thing a relayer runs on every root", and the lever costs no trusted setup and no soundness.

### ⚑ Which slice currency this document is in

There are two, and they are not interchangeable. **Every slice figure above is `rows / 54,300`** — the
same currency as §3.23's emitted schedule, which reads **448 steps at `mpv = 1`** against my 453, so
the two agree. The *other* currency is the live leg-18 planner (`fri-walk-plan`), which models
30,363,795 rows and places real cuts at a 50,000-row budget with measured carry:
**839 FRI slices + 7 AIR slices = 846**, 23.4% of it carry. That number is larger because it
schedules rather than divides and because it prices the AIR braid.

**The ratios in this document hold in either currency** — they are ratios of row counts, and the
hash swap does not change how cuts are placed. Read "453" as "the deployed root, in the currency the
prompt's ~460 came from", not as a scheduling result.

### Wall clock — and the provenance correction

⚠ The often-quoted **171 s compile + 63 s prove** is §3.27's per-**process** average for the seven
**AIR** slices (1,200 s / 7, 442 s / 7) and includes node boot, o1js load and `analyzeMethods`. The
**FRI** slices' own artifacts (`.fullchain/fri-meta-{0..24}.json`, 25 slices, all `verified: true`)
measure **53.6 s compile / 19.7 s prove** mean — the `compile()`/`prove()` calls themselves. Using
the FRI figures, at ~73 s per slice:

| | slices | serial | 7-way | 16-way |
|---|---:|---:|---:|---:|
| root, deployed | 453 | 9.2 h | **1.3 h** | 35 min |
| root + `arity 8` + `cap 8` + `q 16` | 255 | 5.2 h | 44 min | 19 min |
| BabyBear-hashed shrink | 180 | 3.7 h | 31 min | 14 min |
| **Pasta-hashed root** | **54** | 1.1 h | **9 min** | 4 min |
| **Pasta-hashed shrink** | **30** | 37 min | **5 min** | 2 min |

⚑ **Compile is 73% of that, and §5.1 below shows it should be ~zero.**

### 5.1 ⚑ THE SECOND LEVER, and it is orthogonal to the hash: the 19 query walks are the SAME SHAPE, and the walk compiles 839 distinct circuits anyway

The hash swap cuts **rows**. This cuts **compiles**, and it is a bigger factor.

The deployed FRI walk builds **one `ZkProgram` per slice index**: `friSliceProgramName(si, …)` bakes
`si` into the program name (`RootFriSlice.ts:832-838`), `friSliceShape(si)` makes the private-input
widths a function of `si` (`:841-856`), and `AIR_SLICES + si` enters the boundary as a
**compile-time constant** rather than a witness (`:955-957`, `:967-971`). So **839 slices means 839
compiles and 839 verification keys.**

But the planner's own output shows the object is homogeneous. Live run of the committed
`fri-walk-plan`, slices per query:

```
[45,45,45,45,44,45,44,43,44,44,44,44,44,43,44,44,43,43,43]   + 3 for the transcript
```

**Nineteen structurally identical query walks, 43–45 slices each.** The ~15× redundancy is thrown
away by a planner that cuts greedily and *globally*, so each query's cut list drifts by a slice or
two and no two slices end up the same shape.

**The mechanism to fix it is already built and already proved, one section over.** §3.20's
`DreggProofPartition.makeChainedProofVerify` is exactly a uniform circuit that *cannot* bake in its
own position: the step index `k` and the terminal bit are **witnesses**, pinned three ways (constant
`k = 1` on `first`; `Poseidon(rcd, cd, k) == publicInput` **and**
`predecessor.publicOutput == publicInput` on `step`; `k+1` in the closing seal). Measured there:
the whole chain is **two verification keys — one transcript step, one walk step reused N times** —
and the uniformity costs **11 rows** (`walk.first` 23,623 vs `walk.step` 23,612).

⚑ **Nothing applied this to the deployed FRI walk, and nothing in the repo discussed doing so** —
until §5.1a below, which does. The only place the homogeneity was named at all is
`root-air-chain.ts:33-40`, and it is named there as a *contrast* — explaining why the **AIR**
slices legitimately need one VK each (*"the AIR's slices are
DIFFERENT programs … their chains are ONE circuit invoked N times, **because 19 query walks are the
same shape**"*). The observation is written down and the consequence is not drawn.

And the win is bigger than 15×, because **a VK for a fixed program is a protocol constant emitted
once** — the exact argument §3.24/§3.27 already makes for the AIR slice keys. Compile leaves the
per-proof path entirely and the marginal cost of verifying a root becomes **prove-only**, fully
parallel across the 19 queries.

**This composes with the hash swap rather than competing with it.** At the Pasta-hashed shrink's
~30 slices over 19 queries the walk is ~1.5 slices per query, so the distinct-shape count falls to a
handful and compile stops being a line item at all.

### 5.1a ⚑ DRAWN — and the estimates above were close but wrong in three places

`bridge/mina-zkapp/src/RootFriUniform.ts` + `bridge/mina-zkapp/scripts/root-fri-uniform.ts`
(leg 19, `npm run root-fri-uniform`) build it. Everything in this
subsection is **measured on the root's real geometry**, not projected.

**First, the homogeneity is EXACT, and it is now a check rather than an observation.** The walk is
**36 head segments** (22 `duplex` + 14 `permBind`, 78,621 modelled rows) followed by **19 query
blocks of 593 segments each**. `assertHomogeneous` compares every block against query 0 field by
field, compares modelled rows exactly (**1,593,956.5 each, identical**), and compares committed lane
reads after the 1,427-lane per-query shift. **Zero mismatches**, and it *throws* — a geometry change
that broke the homogeneity fails loudly instead of quietly producing a wrong chain.

| | deployed | query-aligned, measured |
|---|---:|---:|
| slice instances, FRI | 839 | **820** |
| **distinct programs / compiles / VKs, FRI** | **839** | **46** (3 head + 43 block) |
| with the AIR half | 846 instances / 846 VKs | **827 instances / 53 VKs** |
| compile, serial | 839 × 53.6 s = **12.5 h** | **46 compiles, 55.9 min MEASURED** (mean 72.9 s/program) |
| prove, serial @ 19.7 s | 4.6 h | 4.5 h — **unchanged, as predicted** |

**Second, §5.1's ⚠ was wrong about the direction of the cost.** It expected forcing the cuts onto a
repeated grid to *waste* slack. Priced apart, and both halves matter:

- **the alignment alone costs +38 instances (+4.5%)** — 877 against 839, at the deployed one-level
  commitment. That is the real price of the grid, and §5.1 was right that it is not free.
- **the commitment shape it ENABLES gives 57 back.** Chunk-aligning each query's opened rows
  (33,062 lanes → 35,328; 130 chunks → 138) lets `friDigest` become two-level —
  `H(g_0…g_23, qd_0…qd_18)` with `qd_q = H(6 chunks)` — so a slice witnesses **75 chunk digests
  instead of 156**. At 26 modelled rows a digest that is ~2,100 rows of carry returned per slice.
- **net: 820 against 839, −2.3%.** The alignment slack is real and is more than paid for.

**Third, "witness `si`" is not the whole change, and the part that was invisible is a RING.** The
deployed chain pins `vk.hash.assertEquals(Field(prevKeyHash))` — a compile-time constant, which
works because slice *i* is compiled after slice *i−1*: a **path**. A uniform block is a **ring**:
position 0's predecessor is the head's last slice at `q = 0` and the block's **last** position after
that. A ring of compile-time constants has no fixed point — position 0 would need the last
position's key, which needs position 0's. So the key list becomes a **Merkle root carried in the
chain**, each slice proves its predecessor's `vk.hash` at a **fixed leaf index** under it, and the
root is anchored where the verifier already looks: **the terminal seal carries it**, and the verifier
recomputes the seal from the protocol's own key list. The admissible key at each position is still
**exactly one**, and side-loading's named hole stays closed — shown by a control, below.

**What is witnessed, and what forces it.** Three things, and the third is strictly stronger than
§3.20's:

- **`k`, the step index.** Constant on the head slices (the induction base); a private input on a
  block slice, which asserts `stepBoundary(friCommit, carry, k) == publicInput` **and**
  `predecessor.publicOutput == publicInput` while the predecessor emitted `…, k_prev + 1`. So
  `k = k_prev + 1` by collision resistance, inductively. `makeChainedProofVerify`'s argument verbatim.
- **`q`, the query.** Not independently witnessed-and-hoped: the program at position `pos` asserts
  `k == 10 + q·43 + pos` with `pos` a compile-time constant, and a one-hot over the 19 queries
  range-checks `q ∈ [0, 19)`. So **`q` is a function of `k`** — and so is `pos`: if the program at
  `pos'` were used at a step whose true position is `pos`, then `43 | (pos − pos')` with
  `|pos − pos'| < 43`, hence `pos = pos'`. **The program admissible at step `k` is unique.** The
  key-tree leaf check then forces the predecessor to be position `pos − 1`, so the program *sequence*
  is forced too.

  ⚑ **Double-count and skip are therefore impossible for exactly the reason they are in the deployed
  chain, and one more.** `k` starts at the head's compile-time constant, increases by exactly one per
  step (the successor's boundary hash carries `k+1` and the successor asserts its own `k` against
  it), and the terminal seal fixes the last one at **827** — so the chain visits `7 … 826` once each,
  and each `k` names exactly one `(q, pos)`. What is *new* is a splice the deployed chain cannot
  express: **`k + 43` together with `q + 1` satisfies the tie**. It is this slice replayed a whole
  query later, and only the boundary refuses it — which is why the splice table has it and the
  unbound control shows that control *accepting* it.
- **the terminal bit is not a witness at all.** The block's last position seals exactly when
  `q == 18`, and `q` is pinned by `k`. §3.20 had to witness `isLast` and argue that neither setting
  passes; here there is nothing to set.

**And the current-query register, which §5.1 did not anticipate needing.** One circuit reads slot
`qidx[0]`; a block opens by selecting **its own** transcript index out of the 19 carried ones on the
same one-hot. Without it a uniform chain would walk the same query nineteen times while every
boundary matched.

**The uniformity cost, measured by building the same cut three times in one process:**

| position | deployed shape | + carried key tree | + witnessed `k`, `q` | total |
|---|---:|---:|---:|---:|
| `head1` | 50,026 | +84 | +75 | 50,185 (**0.32%**) |
| `block0` | 46,206 | +84 | +120 | 46,410 (**0.44%**) |
| `block1` | 46,434 | +84 | +75 | 46,593 (**0.34%**) |
| `block42` | 11,951 | +84 | +77 | 12,112 (**1.35%**) |

**≤ 204 rows a slice.** §3.20's 11 rows does not transfer and was not assumed to: that construction
had no 19-way one-hot, no register multiplexer and no ring to break. The three components are
reported separately so the ring-breaking and the index-witnessing are never quoted as each other.

⚑ **The instrument that made this safe to build, and it found a real defect on its first run.**
`[3b]` walks **all 820 instances out of circuit** and asserts each enters exactly the boundary its
predecessor emits, then that the last emits the terminal seal. It costs seconds. It immediately
failed at `block0 q=1`, chain step 53 — a block's two ends carried *different slot lists*, because
the walk's own liveness kills `qidx[0..q]` at the start of query `q+1`, so `liveIn[headSegs +
blockSegs]` is 19 slots shorter than `liveIn[headSegs]`. **Every one of the 19 block-to-block joins
was broken.** Those joins first occur at instance 46 and the seal at instance 820, so a proof run of
any affordable length would have been green and wrong.

⚑ **The compile figure is measured, and the absolute is contaminated while the ratio is not.** All
46 programs were compiled one process each: **46 distinct verification keys** (checked distinct),
**55.9 min** of compile in total, mean **72.9 s** — against the FRI legs' uncontended **53.6 s**,
because this box was at load ~47 with two sibling lanes compiling throughout. The comparison is
taken at *one* rate applied to both sides, so contention cancels: at the measured 72.9 s the deployed
839-key walk is **17.0 h**; at the uncontended 53.6 s it is 12.5 h and this walk is 41 min. **18.2×
either way**, and it is a one-time protocol-constant cost rather than a per-proof one.

**Proved, against dregg's committed root proof, one process per slice:**

| slice | step index | what it establishes |
|---|---|---|
| `head0` | k = **7** (constant) | predecessor **AIR slice 6** under its own key, pinned by the compile-time constant, entering AIR slice 6's own terminal seal |
| `head1` | k = 8 (constant) | `publicInput` **is** head0's `publicOutput`; predecessor's key proved at **leaf 0 of the carried key tree** |
| `head2` | k = 9 (constant) | — |
| **`block0`** | **k = 10, WITNESSED** | **q witnessed and tied to k; the current-query register muxed out of the 19 carried transcript indices; the two-level per-query commitment; the key tree at leaf 2** |

`head0`'s verification key hash is bit-identical across three independent processes and two working
directories, so the list the tree is built over is a constant and not an accident of one run.

⚑ **What re-emits.** The FRI lane table is chunk-aligned per query and `friDigest` is two-level, so
**every boundary in this chain is a different field element from the deployed one's**. Nothing holds
the old shape — the deployed FRI slice artifacts are a leg's measurements, not state — but the two
chains cannot be mixed, and `RootFriSlice.makeFriSliceProgram` is now the **superseded** path.

### ⚑ And the boundary carry stops mattering too

A step boundary was measured at **34,566 rows** under a flat `rootCommitDigest` and **1,402** under
the chunked one (§3.20/§3.21) — the 2.00× the scheduler found. At 453 slices that chunked carry is
453 × 1,402 ≈ 6.4 × 10⁵ rows ≈ **12 extra slices**, which is exactly why the honest deployed figure
is "~460" and not 453. At 30 slices it is 4.2 × 10⁴ ≈ **0.8 of one slice**.

So the chunked-commitment win — a genuinely clever structural fix, and the largest one found so far
— is worth 12 slices in the regime it was built for and **under one** in the Pasta regime. Both of
the scheduler's levers (placement 1.66×, commitment shape 2.00×) are optimisations *within* a
decomposition whose unit cost is set by the hash. Changing the hash is the re-slicing.

---

## 6. Ember-gated — named, not done

| step | why it is yours |
|---|---|
| **Changing the ROOT's FRI knobs** (`max_log_arity`, `cap_height`, `num_queries`) | re-emits every descriptor, **rotates the apex VK** (`DREGG_APEX_RECURSION_VK`, governance-pinned and mirrored in `chain/gnark/settlement_circuit.go`), and changes the shape the gnark shrink verifies in-circuit ⇒ **a fresh Groth16 setup for the ETH path**. `fri_hundred_bit_cutover.rs:62-63` already flags this as yours. ⚑ This entanglement is itself an argument for a **separate Mina-facing terminal**: it decouples Mina's geometry from the ETH path entirely. |
| **Deploying the zkApp / pinning a new VK on chain** | outward-facing and irreversible. |
| **`commit_proof_of_work_bits 0 → k` on the root** | a knob turn natively, but the gnark circuit hardcodes a `0` witness and fails closed ⇒ same Groth16 flag day. Free on a Mina-only terminal. |

**Not ember-gated, and buildable now:** `DreggPastaConfig`, the `SC`-generalisation of
`shrink_apex_to_outer`, and the o1js native-Poseidon Merkle probe of §4.

---

## 7. What to do next, in order

1. **The o1js native-Poseidon Merkle probe** (§4). Small, and it converts the headline from a
   projection to a measurement. Nothing below is worth starting until this reads.
2. **`p3-pasta`** — a `PrimeField` newtype over `mina_curves::pasta::Fp` plus a
   `CryptographicPermutation<[Fp; 3]>` over `mina-poseidon`. `p3-bn254` is the template.
3. **`DreggPastaConfig`** — the mechanical twin of `dregg_outer_config.rs` once (2) exists.
4. **Generalise `shrink_apex_to_outer` over `SC`** — only needed for the shrink variant; the
   Pasta-hashed *root* (54 slices) needs only (2) and (3).
5. **Re-point the o1js verifier's hash.** `Poseidon2Merkle.ts`'s permutation becomes native
   `Poseidon.hash`; the FRI walk, coset descent, fold arithmetic and DEEP quotient are unchanged.
6. **Then, and only then, the column narrowing** (`APEX-VERIFIER-AIR-REDUCTION.md`) — because at
   that point the DEEP quotient is 85% of what is left and it is priced per column.

**Do not start with the FRI knobs.** They are worth 35% today and 1% after step 5, and changing them
on the root rotates the apex VK and forces a fresh Groth16 setup for the ETH path (§6).

**In parallel, and independent of all six** — the compile lever (§5.1), which needs nothing from the
hash work and pays off in the current regime too:

- ~~**A. Price the alignment slack.**~~ **DONE — §5.1a.** +4.5% on its own, and the commitment shape
  it enables gives more than that back: **820 instances against 839.**
- ~~**B. Make the walk slice uniform.**~~ **DONE — §5.1a.** `src/RootFriUniform.ts`,
  `bridge/mina-zkapp/scripts/root-fri-uniform.ts`. **839 FRI verification keys → 46**, uniformity cost ≤ 204 rows a
  slice, and the ring that a compile-time key pin cannot close is closed by a carried key tree
  anchored in the terminal seal.

A and B were the cheapest real wins in this document and the only ones that needed no new field, no
new config, and no decision from ember. **The next one on that list is the o1js native-Poseidon
Merkle probe of §4**, which is still the thing that converts the headline from a projection to a
measurement.

---

## 8. One line on the query count, deliberately not a derivation

The deployed 19 queries sit well above what the FRI ledger's binding term needs, so a lower count is
arithmetically available. **I am not proposing it.** The ledger is an informal reading that is
**not attached to `verifyAlgo`** — no machine-checked theorem ties the deployed verifier's
acceptance to the BCIKS bound against an adversary object — so "we could drop to N queries" is
reasoning inside a model nobody has connected to the thing that runs. Flagged as a protocol question
for ember, not as a result. Every row figure above at `q 16` is shown *because the comparison is
useful*, not because the drop is recommended.
