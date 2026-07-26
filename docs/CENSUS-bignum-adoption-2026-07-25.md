# Census — bignum adoption gap (2026-07-25)

Lane C. Read-only analysis; nothing in this census was refactored.

**Substrate statement:** every item below is Lean-authored AIR under `metatheory/`. The
adoption target, `Dregg2.Bignum`, emits into `Dregg2.Circuit.Expr` / `Constraint` +
`Dregg2.Circuit.Lookup.rangeCheck`, which `circuit/src/lean_descriptor_air.rs` ingests as a
generic IR (`EmittedExpr = var | const | add | mul`). No Rust hand-authored AIR is proposed,
recommended, or implied anywhere in this document.

Foundation build, on the assigned lane:

```
scripts/hbuild pq-bfv-native 'cd metatheory && lake build Dregg2.Bignum'
pbuild: VERDICT outcome=PASS status=0 lane=pq-bfv-native host=hbox
✔ [1397/1397] Built Dregg2.Bignum (2.3s)
```

---

## 0. The denominator was measuring the wrong population

The brief states *197 Lean files mention limbs, 6 import `Dregg2.Bignum`, about 3 percent*.
Two corrections, both of which change what the number means.

**(i) The limb corpus is 314 files, not 197.** Measured over 2,070 non-vendored `.lean` files:

| population | count |
|---|---|
| files containing a real `limb` token | **314** |
| files matching `grep -i limb` (includes `climb`/`climbs`) | 341 |
| of those, `climb`-only false positives | 27 |
| import `Dregg2.Bignum` | 6 |
| reference the `CaveatBignum` denotation | 5 |

Beware `grep -riE '[a-z]Limb'` — under `-i` the `[a-z]` class matches the `c` in `climb`, so
that pattern silently returns the whole contaminated set. That is how I first got 341 = 314.

**(ii) The limb corpus is the wrong population, and it undercounts the gap.**
A hand-rolled pack is precisely the code that does *not* say "limb" — it says `pack`, `code`,
`digit`, `score`, `ballot`. Of the six strongest class-(a) sites found below, **four are not in
the limb corpus at all**:

| site | in `limb` corpus? |
|---|---|
| `Market/DarkBazaarPrivateDescriptor.lean` | yes |
| `Dregg2/Circuit/DeployedCapTree.lean` | yes |
| `Dregg2/Games/PrivatePreferenceDescriptor.lean` | **no** |
| `Dregg2/Games/PrivateRaidAssignmentDescriptor.lean` | **no** |
| `Market/DarkBazaarSameOpeningPoly.lean` | **no** |
| `Dregg2/Circuit/Emit/AutomataflCommit.lean` | **no** |

So "3% of limb-mentioning files import Bignum" is not the adoption gap. Measuring by *narrowing
signal* instead of by vocabulary: **268 weighted-digit-sum pack sites across ~60 files**, of
which the ranked class-(a) list below is the load-bearing part.

The honest one-line summary is not "197 files should adopt Bignum." It is: **the bignum library
has ~11 genuine adopt-sites, 2 of them security-load-bearing, and the reason adoption looks like
3% is that most files saying "limb" mean a digest lane, which correctly needs no bignum at all.**

---

## Class (a) — GENUINE NARROW PACKING that should adopt `Dregg2.Bignum`

Ranked by blast radius. "Reverse deps" = files importing the module (measured, non-vendored).

### A1. `Dregg2/Circuit/Emit/PqIdentityAuthorityEmit.lean` — hand-rolled schoolbook carry-add
**Reverse deps: 1 direct** (but see load-bearing note). **Rank #1 on security, not on fan-out.**

- `PqIdentityAuthorityEmit.lean:78-97` emits a four-limb base-2^16 increment with explicit
  binary carry witnesses:
  - `succBody0`: `new0 + 65536*c0 = old0 + 1`
  - `succBody1`: `new1 + 65536*c1 = old1 + c0`
  - `succBody2`: `new2 + 65536*c2 = old2 + c1`
  - `succBody3`: `new3 = old3 + c2` — top limb, **no carry-out witness**
  - `carryBoolBody i`: `c_i(c_i - 1) = 0`
- **What it commits:** the PQ-identity *epoch* increment — VK-epoch freshness.
- **Width:** 4 limbs x 16 bits = exact u64. Width is **SUFFICIENT**; this is not a domain bound.
- **Why it is class (a):** this is `Dregg2.Bignum.AddValid` re-derived by hand at fixed arity 4.
  `AddValid` (Bignum.lean:195) is the same object generically, and the file's own comment
  ("absence of a fourth carry is the no-overflow tooth", line 94-95) is *literally*
  `Bignum.add_overflow_unsat` (Bignum.lean:299) and `add_result_fits` (:307), which are proven
  theorems rather than a comment. `CARRY := 108` with three columns is Bignum's boolean carry
  chain, and `carryBoolBody` is its `(c = 0 ∨ c = 1)` clause.
- **Load-bearing:** yes. Per the project record, VK-epoch freshness is *forced in-circuit*; an
  epoch that could wrap is a replay surface. The no-wrap argument currently rests on the
  *absence* of a column, which is a real argument but an unproven-in-place one — Bignum states
  and proves it.

### A2. `Dregg2/Circuit/DeployedCapTree.lean` — capability mask limb recombination
**Reverse deps: 10** (`DeployedCapTree`) **+ 14** (`CapOpenEmit`, which emits its range gate).

- `DeployedCapTree.lean:357` — `def maskOfLimbs (lo hi : ℤ) : ℤ := lo + hi * 65536`
- `:373` — `facetOfLeaf l : Option EffectMask := some (maskOfLimbs l.mask_lo l.mask_hi).toNat`
- `:565-566` — canonical build: `mask_lo := canonMask c.facet % 65536`, `mask_hi := ... / 65536`
- Range gate lives in `Emit/CapOpenEmit.lean:143-146`: per-16-bit-limb decomposition
  `mask_lo = Σ_{i<16} bit_i·2^i` with boolean pins, replacing an older single 32-bit
  `maskReconGate`.
- **What it commits:** the deployed `EffectMask` u32 on a capability leaf — the facet half of
  the two-axis authority gate (`confersLeaf`, `:387-393`).
- **Width:** `mask = lo + 2^16·hi`, u32. **This width IS a real bound on the domain** — see A2b.
- **Why it is class (a):** `maskOfLimbs` is `bignumVal 65536 [lo, hi]`; the `maskReconLo/Hi` bit
  gates are `Bignum.range_bits_bound` (Bignum.lean:463) + `rangeClause_is_lookup` (:568)
  re-derived by hand. The recomposition-is-a-gate step is `addLimbEqn_is_gate` (:534).
- **NOT a hole.** I checked the accept path specifically: the 16-bit range gate genuinely
  exists and was a documented prior fix, and `.toNat` of a negative decodes to mask `0`, which
  `isEffectPermitted (some 0) _ = false` (`Exec/FacetAuthority.lean:166`) fails **closed**. My
  initial suspicion of an ungated limb was wrong and is retracted here. This is a *duplicate
  implementation*, not a wound.

#### A2b. The u32 effect mask is 28/32 full — a real, measurable domain bound
Adjacent to the bignum question but the most concrete width finding in this census.

- `cell/src/facet.rs:31` — `pub type EffectMask = u32`
- Deployed bits: **28 constants, bits 0..27**, highest `EFFECT_ROTATE_PQ_IDENTITY = 1 << 27`.
- **Four bits remain.** Every capability, facet attenuation (`isFacetAttenuation`), and
  authority theorem rides this 32-bit mask. This is a hard ceiling on the number of expressible
  effect classes, and it is 87.5% consumed.

#### A2c. Lean/Rust effect-bit parity gap (reported, not inflated)
`Dregg2/Exec/FacetAuthority.lean:148-156` defines **9** named `EFFECT_*` constants (bits 0-8)
plus `EFFECT_ALL`. Rust deploys **28**. Bits 13, 16, 23 appear in Lean only as inline literals
(`Emit/CapOpenEmit.lean:709,713`; `Circuit/DeployedCapOpen.lean:256`). **16 deployed effect bits
have no Lean constant at all.** This is a coverage gap in the Lean facet model, not a bignum
item; it is recorded here because it was found on the same accept path and bounds what the
authority theorems can be *about*.

### A3. `Market/DarkBazaarPrivateDescriptor.lean` — THE EXEMPLAR (Lane D owns this file)
**Reverse deps: 7.** Read-only here; coordinated by reading, not edited.

- `:99-100` — `orderCode o = o.kind.val + 8 * o.qty.val`, seven-bit, `∈ [0,127]`
- `:120-122` — `packedBook w = Σ_{i<4} 128^i · orderCode (w.orders i)`, `< 128^4 = 2^28`
- `:125-160` — `packedBook_injective_on_orders`, proven by a **hand-expanded four-term omega
  argument** with the digit weights written out literally (`128`, `16384`, `2097152` at
  `:134-137`) and four separate `omega` blocks (`:139-154`), each re-deriving digit bounds.
- **What it commits:** four private limit orders, into **one** BabyBear felt, absorbed at
  `rootPreimage` (`:165-166`) lane 3.
- **Width:** 2^28 < BabyBear 2^31. **SUFFICIENT for the stated family** (4 orders, qty<16,
  8 kinds) but it is a **real bound on the domain**: the pack cannot carry a fifth order or a
  wider quantity without exceeding the felt. The family shape is load-bearing for the width.
- **Why it is class (a):** `packedBook` is `bignumVal 128` over a 4-digit list, and
  `packedBook_injective_on_orders` is Bignum's digit-uniqueness at fixed arity. Imports none of
  the bignum stack (verified: no `import Dregg2.Bignum`, no `CaveatBignum`).

### A4. `Dregg2/Games/PrivatePreferenceDescriptor.lean` — same pattern, two felts
**Reverse deps: 3.** Not in the limb corpus.

- `:75-77` — `ballotPackOf`: four base-4 digits into a byte
  (`b0 + 4·b1 + 16·b2 + 64·b3`)
- `:88` — `ballotPackOf_injective`, hand omega
- `:113` / `:116` — `packedLow = ballotPack 0 + 256 * ballotPack 1`,
  `packedHigh = ballotPack 2 + 256 * ballotPack 3`
- `:119-121` — `packedScores_injective`, hand-expanded across both felts
- **What it commits:** sixteen two-bit preference scores.
- **Width:** two 16-bit felts. **SUFFICIENT**; the header states "faithfully packed into two
  16-bit felts" and 16 scores x 2 bits = 32 bits = the two felts exactly. Domain-bounding for
  the fixed 16-participant family.

### A5. `Dregg2/Games/PrivateRaidAssignmentDescriptor.lean` — base-4096, two felts
**Reverse deps: 2.** Not in the limb corpus.

- `:84-85` — `participantPack`: mixed-radix pack of scores and admissibility
  (`16·s2 + 64·s3 + 256·a0 + 512·a1 + ...`)
- `:97` — `participantPack_injective`, hand omega
- `:138-142` — `packedLow/High = participantPack i0 + 4096 * participantPack i1`
- `:144-146` — `packedInputs_injective`, four inline `omega` calls (`:156-162`)
- **Width:** base-4096 x 2 per felt = 24 bits. **SUFFICIENT**, domain-bounding at 4 participants.

### A6. `Dregg2/Circuit/Emit/WideValueBindingEmit.lean` — hand bit-decomposition, `ranges := []`
**Reverse deps: 2.** The shielded value/asset width repair.

- `:105/:107` — `U64_LIMBS := 4`, `LIMB_BITS := 16`
- `:126` — `limbWeight i := (2 ^ (LIMB_BITS * i)) % P`, i.e. **mod-P reduced** place values
  (`#guard limbWeight 2 == 268435454`, `limbWeight 3 == 268295646`)
- `:198` — `limbRecomposeHead`: `limb_{k,i} − Σ_{b<16} 2^b·bit_{k,i,b}`
- `:203` — 16 boolean pins per limb; 128 distinct bit columns (`#guard` at `:362-365`)
- `:210` — `u64RecomposeHead`: `out − Σ_{i<4} limbWeight(i)·limb_{k,i}`
- `:292-300` — **`ranges := []`**, with the comment "the limb range check is an explicit bit
  decomposition exactly as the Rust one is"
- **What it commits:** full-u64 shielded value and asset, plus a narrow legacy compatibility
  felt `out`.
- **Width:** 4x16 = exact u64 on the wide carrier. The narrow `out` felt is a **mod-P lossy
  projection** (u64 domain 2^64 >> p ~ 2^31), but it is *derived from* the limbs and the wide
  carrier is what binds — so the narrowness is **not** load-bearing here. This is the felt-width
  repair working as designed.
- **Why it is class (a):** `ranges := []` means this descriptor does not ride
  `Lookup.rangeCheck` at all; it hand-rolls what `Bignum.range_bits_bound` and
  `rangeDecomp_field_faithful` (Bignum.lean:480) prove generically. The mod-P weight question
  is exactly `Bignum.antiExploit_field_vs_integer` (:645).

### A7. `Dregg2/Circuit/Emit/AutomataflCommit.lean` — correct, generic, still a duplicate
**Reverse deps: 4.** Feeds the whole-turn capstone. Not in the limb corpus.

- `:60-69` — `horner4` (base-4 Horner) and `packCell` (15 digits per felt)
- `:139` — `pack_injective`, **n-generic, by list induction** — not hand-expanded
- `:196` — `pack_injective_modp`, with a proven no-wrap bound (`4^15 < BABYBEAR_P`,
  `packCell_nonneg`)
- **What it commits:** Automatafl board cell codes, 15 base-4 cells per felt.
- **Width:** `4^15 = 2^30 < p`. **SUFFICIENT and proven so.**
- **Why it is class (a) anyway:** `horner4` *is* `bignumVal 4`; `horner4_inj` is Bignum's digit
  uniqueness; `packCell_nonneg` is `bignumVal_lt_base_pow` (Bignum.lean:71). This is the
  **highest-quality** duplicate in the tree — generic, both-polarity, no-wrap-proven — which
  makes it the best evidence that the library is genuinely re-derived rather than merely
  unused. Adopting here is a deduplication win, not a correctness fix.

### A8-A11. Lower-rank adopt candidates (same shape, smaller radius)

| # | file:line | what it packs | width | note |
|---|---|---|---|---|
| A8 | `Market/DarkBazaarSameOpeningPoly.lean:147-148` | 4 ciphertext phases, base-128 | 2^28 | `packCt`; mirrors A3 |
| A9 | `Market/DarkBazaarSameOpeningGadgetPoly.lean:158-160` | phase **and** noise, base-128 | 2^28 each | `packColumns` |
| A10 | `Dregg2/Circuit/PqIdentityAuthority.lean:34-42` | `Epoch4 = Fin 4 → Fin 65536`, `epochValue` | exact u64 | canonicity **free from the `Fin` type**; pure-Lean side of A1 |
| A11 | `Dregg2/Circuit/ExactFnspV3DurableAuthority.lean:43` | `count / 65536^i % 65536` | base-2^16 | limb *decomposition* direction |

---

## Class (b) — DIFFERENT BY DESIGN, do not adopt

These use "limb" for a representation that is not a base-B bignum. Adopting `Bignum` here would
be wrong, not merely unnecessary.

| group | files | why bignum does not apply |
|---|---|---|
| **ML-KEM / ML-DSA codecs** — `Crypto/MlKemCodec.lean`, `MlKemCodecSpec.lean`, `MlDsaCodec.lean`, `MlDsaKeygen.lean`, `MlDsaExpandA.lean`, `Fips204BitPack.lean`, `Fips203Kem.lean`, `MlKemDelta.lean`, `MlKemKeygenRefine.lean`, `VerifyCoreEqSpec.lean` | ~14 | Limbs are **polynomial coefficients mod q** (3329 / 8380417), not positional digits of one integer. `byteEncode`/`packBits`/`compress` are FIPS-mandated bit-packings whose *exact byte layout is the specification* — the spec is the authority, and any re-derivation must match FIPS byte-for-byte, not be "equivalent". `MlDsaExpandA.lean:86` (`b0 + 256·b1 + 65536·(b2 &&& 0x7F)`) looks like a base-256 pack but is FIPS 204 rejection sampling. |
| **NTT / RLWE / BFV** — `Bfv/*`, `Market/PrivateBookBfvNttFamily.lean`, `PrivateBookBfvBindingAir.lean`, `PrivateBookBfvButterflyAir.lean`, `Crypto/WgpuBfvNttSpec.lean`, `Circuit/TfhePbsRefinement.lean` | ~7 | Limbs are **RNS residues / NTT evaluation points**. Their value is a CRT tuple, not `Σ dᵢBⁱ`; there is no carry, and "the integer it denotes" is the wrong semantics entirely. |
| **Field-extension towers** — `Circuit/Emit/Bls12381Tower.lean`, `ExtFieldChallenge.lean`, `ExtChallengeOodSites.lean`, `Circuit/ChallengerFr.lean`, `Emit/GnarkVerifier/*` | ~9 | Limbs are **Fp2/Fp6/Fp12 extension coordinates** or a BN254 `Fr` embedding of BabyBear felts (`ChallengerFr.lean:269`, base-2^31 fold). Arithmetic is tower multiplication, not schoolbook. |
| **Byte/hash gadgets** — `Emit/Sha256Gadget.lean`, `Ed25519Gadget.lean`, `Sha256MerkleFold.lean`, `Crypto/Pedersen.lean` | ~4 | Word decomposition serving a fixed hash/curve spec. |

**Also class (b), and worth naming so it is not mistaken for a wound:**
`Dregg2/Bridge/LightClientTendermint.lean:439-445` — `demoSignBytes` (base-1000 field pack) and
`demoValSetEncode` (`foldl acc*97 + pubkey*7 + power`) look alarming but are **explicitly demo
fixtures** (`demoLeaf`, `demoHash`) built as non-vacuity discriminators, with an adjacent
theorem `demoCollapseLeaf_not_hashCR` proving the collapsing variant is refutable. Toy by
design, not deployed.

---

## Class (c) — ALREADY FINE

| group | count | why |
|---|---|---|
| Import `Dregg2.Bignum` | **6** — `Dregg2.lean`, `Deos/VaultSatDescriptor.lean`, `Shielded/RealCrypto.lean`, `Shielded/WideNativePqCommitment.lean`, `Market/ExactGapNoWrap.lean`, `Market/QuantizedConservation.lean` | already adopted |
| Use the `CaveatBignum` denotation | **5** (3 overlap the above) | `bignumVal` / `Ranged` directly |
| **Digest-lane "limbs"** — `Lanes16`, `commitmentToLanes16`, `recordDigestLimb`, `hcommitLimb`, `capRootLimb`, `restLimbs`, `preLimbsWide`, `RotatedLimbs`, `fieldLimbs` | **the large majority of the 314** | A 32-byte digest split into 16 canonical u16 lanes is a **lossless byte-carrier**, not an integer needing arithmetic. There is no add, no compare, no carry — nothing for `Bignum` to prove. `PqIdentityAuthority.lean:57` (`authorityImage_injective`) is the model: injectivity comes from the `Fin 65536` *type*, "no hash assumption and no field-collision assumption is needed". Correctly needs no width argument. |
| Comment-only mentions | 20 | the word `limb` appears only in prose |

The `restLimbs` / `preLimbsWide` / `RotatedLimbs` vocabulary (identifier frequency: `limb` 2,380,
`limbs` 898, `restLimbs` 158, `preLimbsWide` 74, `RotatedLimbs` 62) is one shared wide-carrier
idiom repeated across the ~97 `Circuit/Emit` files. **It is one design, counted many times.**
Treating those ~97 files as 97 adoption failures is exactly the inflation the brief warned
against.

---

## Ranked adopt list (the deliverable, one line each)

| rank | target | radius | load-bearing? | what adopting buys |
|---|---|---|---|---|
| 1 | `Emit/PqIdentityAuthorityEmit.lean:78-97` | 1 | **yes** — VK-epoch freshness | `AddValid` + `add_overflow_unsat`: the no-wrap tooth becomes a theorem instead of an absent column |
| 2 | `Circuit/DeployedCapTree.lean:357,373` + `Emit/CapOpenEmit.lean:143` | 10 + 14 | **yes** — capability authority | `bignumVal 65536` + `rangeClause_is_lookup`; retires a hand bit-decomposition on the authority path |
| 3 | `Market/DarkBazaarPrivateDescriptor.lean:120-160` | 7 | family-shape | **Lane D owns this** — replaces a 4-term hand omega with generic digit uniqueness |
| 4 | `Games/PrivatePreferenceDescriptor.lean:75-121` | 3 | no | same hand-omega collapse, two felts |
| 5 | `Games/PrivateRaidAssignmentDescriptor.lean:84-146` | 2 | no | same, base-4096 |
| 6 | `Emit/WideValueBindingEmit.lean:198-210,292` | 2 | no (wide carrier binds) | `ranges := []` → real `Lookup.rangeCheck`; 128 hand bit-columns retire |
| 7 | `Emit/AutomataflCommit.lean:60-196` | 4 | no (proven sufficient) | pure dedup; the *best* duplicate in the tree |
| 8-11 | A8-A11 above | 1-3 | no | mechanical |

---

## Residuals — work NOT done

1. **I did not build any file except `Dregg2.Bignum`.** The single VERDICT line above is the
   only build evidence in this census. No adopt-site was compiled, edited, or re-verified.
2. **No guard was made to fire.** This lane produced no red-then-green evidence because it
   changed no code. Every classification is from reading, not from execution.
3. **A2c (the 16 missing Lean effect-bit constants) is unverified as to impact.** I confirmed
   the constants are absent; I did **not** determine whether any authority theorem is thereby
   weaker, nor whether the missing bits are unreachable in the Lean turn model.
4. **A2b (28/32 mask bits) — I did not check whether any planned effect needs bit 28+.** The
   ceiling is measured; the runway is not.
5. **Class (b) counts are grep-bucketed, not read file-by-file.** The four group counts (~14,
   ~7, ~9, ~4) are pattern-matched. I read representatives, not all 34.
6. **I did not verify the Rust side of A1/A2** beyond `cell/src/facet.rs` bit constants. Whether
   the deployed prover emits the same carry/range columns the Lean descriptor declares is
   unchecked here.
7. **The ~60-file / 268-site narrowing-signal set is a superset of class (a).** I ranked the top
   11; the tail (`Emit/ExactNullifierAafiDescriptorPlan.lean`, `Emit/HeapOpenEmit.lean`,
   `Emit/FieldsOpenEmit.lean`, `Emit/AccumulatorOpenEmit.lean`,
   `Crypto/PrivateGraphRewriteDescriptor.lean`, `Market/DarkAmmPrivateDescriptor.lean:323-325`)
   is triaged by grep only and may contain a further genuine adopt-site.
8. **`Emit/AutomataflStepRefine.lean` (34 pack sites, the largest single count) is unclassified.**
   Its sites are `[ZMOD 2013265921]` congruences over 5-bit unary-ish spreads
   (`e.loc 69 + 2*e.loc 70 + 4*...`), which is a bit-spread not a bignum — but I did not read
   enough of it to place it in (a) or (c) with confidence.
