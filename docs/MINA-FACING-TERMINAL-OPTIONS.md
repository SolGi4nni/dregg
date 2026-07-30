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
| a plonky3-native SHRINK of the root | Poseidon2-BabyBear | 9.8 × 10⁶ | **180** | none |
| **the ROOT, hashed with Mina-Poseidon over Pasta** | **Mina-Poseidon (NATIVE)** | **2.9 × 10⁶** | **54** | **none** |
| **a plonky3-native SHRINK, Pasta-hashed** | **Mina-Poseidon (NATIVE)** | **1.6 × 10⁶** | **30** | **none** |

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

### ⚠ Is there a fixed point? Not at the BN254 config's knobs — it GROWS

The recursion circuit's dominant table is the ALU carrying the reduced-opening Horner arithmetic,
which `apex_shrink.rs:137-140` describes as *"~752 opened columns × 19 FRI queries"*. So the
verifier circuit's size scales roughly as **(queries × opened columns)** of the proof being verified:

- verifying the **root**: 19 queries × ~1,427 lanes ≈ 2.7 × 10⁴ lane-openings ⇒ a 2^15 circuit.
- verifying the **shrink at `DreggOuterConfig`'s knobs** (38 queries, `lb 3`): 38 × ~967 ≈ 3.7 × 10⁴
  — **larger than the root**. Recursion at those knobs diverges.
- verifying a shrink minted at **`lb 6`, 19 queries**: 19 × ~967 ≈ 1.8 × 10⁴ ⇒ ~0.68×, so it does
  contract, with diminishing returns toward a floor set by the verifier circuit's own irreducible
  content (the Poseidon2-W16 table alone is 300 columns).

**So "shrink twice" is not free and is not obviously worth it.** The query count of the *outer*
config is what decides whether recursion contracts, and `DreggOuterConfig`'s 38 queries were chosen
for the gnark path, not this one. Anything past one pass should be measured, not assumed.

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

This also means the FRI knobs stop mattering: at Pasta hashing, `arity 8` + `cap_height 8` together
are worth only 16% (2.92 × 10⁶ → 2.47 × 10⁶), where at BabyBear hashing they are worth 35%.

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

## 7. One line on the query count, deliberately not a derivation

The deployed 19 queries sit well above what the FRI ledger's binding term needs, so a lower count is
arithmetically available. **I am not proposing it.** The ledger is an informal reading that is
**not attached to `verifyAlgo`** — no machine-checked theorem ties the deployed verifier's
acceptance to the BCIKS bound against an adversary object — so "we could drop to N queries" is
reasoning inside a model nobody has connected to the thing that runs. Flagged as a protocol question
for ember, not as a result. Every row figure above at `q 16` is shown *because the comparison is
useful*, not because the drop is recommended.
