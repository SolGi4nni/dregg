# DESIGN — the canonical byte→felt codec

**Status:** design, pre-implementation. No code changed by this document.
**Date:** 2026-07-24.
**Supersedes as the *plan of record*** (not the evidence) for: `docs/WOUND-felt-width-boundaries-2026-07-19.md`
entries #5, #6, #9, #11, #18, #19, #20, #23, #24, #33, and `docs/FAITHFUL-COMMITMENT-LAW.md`'s
constructor discipline.
**Evidence:** six independent source-read census lanes, 2026-07-24. Every quantitative claim below
that is *not* attributed to a lane was re-derived here against the tree at `HEAD`; the arithmetic
facts in §2 are the ones the recommendation rests on and each was read from source, not inferred.

---

## 1. The root cause

**No canonical codec was ever designated.** Every author who needed to put 32 bytes into a BabyBear
trace invented the mapping at the point of need, from the same folk knowledge ("chop into 4-byte
chunks, reduce mod p"), and each invention lost information in a *different* way. Nobody was
reckless; each site is locally reasonable. The failure is architectural: **a byte→felt map is a
protocol primitive and it was treated as a local utility.**

Two consequences, and they explain the whole shape of the wound catalogue:

1. **33 wound entries look like 33 problems.** They are not. They are **4 arithmetic families**
   surfacing at ~52 places. Fix the 4 families and the 33 entries close together.
2. **Every doc-comment written at a call site describes a property the author *wanted*, not the
   property the arithmetic *has*** — because the author was reasoning about their own site, not
   about a designated primitive with a stated contract. Hence 30+ false injectivity /
   "~256-bit binding" comments (§6), several of which contradict a *correct* comment in the
   same file.

### 1.1 The four families

| # | Family | Arithmetic | Failure mode | Cost to break |
|---|---|---|---|---|
| **F1** | **MOD-P ALIAS** | 8 × (4-byte LE u32) `% p` | `v` and `v+p` collide for 53.1% of chunks | **O(1)** (add `p`), no grind |
| **F2** | **BIT-DISCARD** | 8 × (8+8+8+6 bits), drops bits 6–7 of every 4th byte | 16 of 256 source bits unbound | **O(1)** collision, but only ~2^120 for a *meaningful* second value |
| **F3** | **NON-CANONICAL SEED** | Poseidon2 sponge *over an F1 encoding*, squeezed to **1 felt** | inherits F1's O(1) collision **upstream of the hash**; plus ~2^15.45 birthday on the 1-felt image | **O(1)** where bytes are attacker-chosen; ~2^15.45 / ~2^31 where they are a hash image |
| **F4** | **LINEAR FOLD** | `Σ limbᵢ · MIX^i (mod p)` over an F1 encoding | an **onto F_p-linear form**: collisions *and* hits on a chosen target felt are one linear solve | **O(1) for both**, including *targeted* |

F3 and F4 both sit on top of F1, so **F1 is the seed of three of the four families.** F2 is
independent (the KEY_COMMIT lineage).

The critical structural point: **F3's Poseidon2 does not rescue it.** The reduction happens
*before* the sponge, so the sponge is fed identical inputs and cannot undo the collision. The
sponge does restore *preimage* hardness (aliasing yields no preimage), which is why F3 sites split
cleanly by whether the attacker chooses the bytes or receives them as a hash image. This split is
the single most useful triage axis in the whole catalogue.

### 1.2 Census totals

Raw symbol references, `grep` over `*.rs` excluding `target/`, at HEAD:

| Symbol | refs / files | | Symbol | refs / files |
|---|---|---|---|---|
| `fold_bytes32` (F3, incl. `_to_bb`) | 166 / 42 | | `canonical_32_to_felts_4` (F2) | 75 / 17 |
| `bytes32_to_8_limbs` (F1) | 135 / 31 | | `encode_hash` (F1 root) | 74 / 29 |
| `bytes_to_babybear` (F3) | 117 / 22 | | `hash_to_8` (F1, 8 refs are a name collision) | 63 / 10 |
| `fold_bytes32_to_bb` (F4) | 109 / 28 | | `field_limbs8` (F1 lane-reordered) | 62 / 17 |
| `hash_bytes` (F3, heavily name-polluted) | 218 / — | | `commitment_to_field` (F3) | 41 / 10 |
| `bytes32_to_felt8` (F1) | 28 / 10 | | `canonical_to_babybear_pi` (F2) | 21 / 5 |
| `canonical_32_to_felts_8` (F2) | 19 / 8 | | `from_bytes_packed` (F1, var-len) | 15 / 7 |
| `bytes32_to_limbs` (F1 clone) | 13 / 2 | | `encode_bytes_to_felts` (injective, 3-byte) | 10 / 3 |
| **`bytes32_to_u16_limbs` (F5 — correct)** | **7 / 1** | | **`bytes32_to_u16_le` (F5 — correct)** | **4 / 1** |
| **`bytes32_to_u16_be` (F5 — correct, BE)** | **2 / 1** | | | |

**After de-duplication across the six lanes** (≈8 site-groups were reported by two lanes each —
cap `target`/`breadstuff`, heap value, umem key/value, zkoracle leaves, `commitment_to_field`,
`revocation_hash_to_field`, `Faithful8::from_bytes32`):

| Bucket | Count | Meaning |
|---|---|---|
| **SECURITY site-groups** | **~52** | reaches a commitment, PI binding, authorizing equality, or a map/sort key |
| — of those, **O(1)-exploitable today** | **~20** | attacker chooses the bytes; a colliding pair is *constructed*, not searched |
| — of those, **~2^15.45–2^31** | **~24** | input is a hash image; needs a grind or a birthday search |
| — of those, **~2^120** | **~8** | F2 bit-discard; a colliding *string* is free, a colliding *meaningful value* is not |
| **STRUCTURAL** (width/geometry) | **~18** | a fix moves AIR columns, PI layout, or a committed root |
| **BENIGN** | **207** | tests, fixtures, benches, examples, doc lines, domain constants |
| **DEAD** | **11** | `#[allow(dead_code)]` / zero callers, grep-confirmed |
| **Distinct encoder implementations** | **~17 names** | across ~14 crates, realizing **4** distinct arithmetics |

**Honest sizing, since the ask invited it:** this is not 490 problems and it is not 12. It is
**~52 security site-groups generated by 4 arithmetics under ~17 names**, of which **~20 are
O(1)-exploitable**. The 207 benign references are real noise — most of the raw grep volume is
tests. And an important sobering note that every lane independently reached: **the census found no
demonstrated *soundness* break.** Nearly every site projects identically on the producer and
verifier sides, so a collision *over-includes* (an honest turn goes UNSAT, a distinct fresh
nullifier is refused) rather than authorizing a forgery. The realized class is
**availability/denial with occasionally global blast radius**, not theft. Two candidates for a
genuine soundness break are flagged as **unknowns** in §7 — they are the ones worth a falsifier
before anything else.

The ratio that names the disease: **~17 implementations, 4 intents.** An order of magnitude more
copies than distinct meanings.

---

## 2. The canonical codec

The brief asked whether `bytes32_to_u16_limbs` is right, and specifically whether an **injective
8-felt** encoding exists, since 16 felts is 2× the width and width costs columns. That is the
load-bearing question, so it gets a real answer rather than a preference.

### 2.1 There is no injective 8-felt encoding. This is a pigeonhole theorem, not an engineering gap.

`BABYBEAR_P = 2^31 − 2^27 + 1 = 2013265921` (`circuit/src/field.rs:12`, read).

```
log2(p) = 31 + log2(0.937500000465…) = 30.906891 bits
8 felts  →  p^8  ≈ 2^247.2551
domain   →  2^256
deficit  →  2^8.745  ≈  429×
```

A map `[u8;32] → F_p^8` has a codomain **8.75 bits too small**. At least `2^256 − p^8 ≈ 0.9977 ·
2^256` inputs — **99.77% of all 32-byte strings** — must participate in a collision. No choice of
limb geometry, range check, or gate changes this.

The two candidates named in the brief both die here:

* **"8 limbs of 31 bits with a canonicity range-check."** A 31-bit range is `[0, 2^31)`, and
  `p < 2^31`, so a 31-bit limb is not a canonical felt. Range-check to `< p` instead and you have
  `p^8 < 2^256`. Dead.
* **"8 × 32-bit limbs with an explicit alias-rejecting gate."** Rejecting aliases means constraining
  each limb to `[0, p)`. A uniformly random 4-byte chunk is canonical with probability
  `p / 2^32 = 0.46875`, so the gate **accepts `0.46875^8 = 0.233%` of 32-byte strings** — it would
  reject 99.77% of BLAKE3 digests. Dead as a general codec.

  *But this gate is exactly right in the other direction*, and we already have it — see §2.4.

**Minimum injective width is `ceil(256 / 30.906891) = 9 felts.**

### 2.2 The width worry is the wrong worry: `CHIP_RATE = 16`

The decisive measurement, read from source and confirmed on both sides:

```
circuit/src/descriptor_ir2.rs:308   pub const CHIP_RATE: usize = 16;
circuit/src/descriptor_ir2.rs:2242  pub const CHIP_OUT_LANES: usize = 8;
metatheory/Dregg2/Circuit/DescriptorIR2.lean:160  def CHIP_RATE : Nat := 16
metatheory/Dregg2/Circuit/DescriptorIR2.lean:175  def CHIP_OUT_LANES : Nat := 8
```

**The deployed Poseidon2 chip absorbs 16 lanes per permutation and squeezes 8.**

Therefore:

* Today's 8-limb encodings (F1, F2) consume **half the chip's absorb rate**. One 32-byte value
  occupies 8 of 16 available lanes.
* A 16 × u16 encoding consumes **exactly one full chip absorb** for one 32-byte value.
* **⇒ At every site where the encoder output is absorbed into a sponge — which is the large
  majority of the ~52 — migrating 8→16 limbs costs ZERO additional permutations.** The "2× width"
  penalty is paid out of rate the chip already has and currently wastes.

The width penalty is real only where limbs sit in **persistent columns** (PI slots, carrier octets,
trace param columns) rather than being absorbed. And for those sites the answer is not to store
limbs at all — see §2.3.

Pricing the alternatives on this basis:

| Codec | Felts | Absorbs | Range check | Byte-aligned | In tree | Verdict |
|---|---|---|---|---|---|---|
| 9 × base-`p` digits | 9 | 1 | big-int `< 2^256` borrow chain | **no** | no | minimum width, worst gadget; Lean model would be genuinely painful |
| 11 × u24 | 11 | 1 | 2^24 table (too large) or 16+8 split ⇒ **22** lookups | yes | no | **strictly dominated** — no absorb saving over u16, *more* range constraints, a 5th codec to prove |
| **16 × u16** | **16** | **1** | **16 lookups at the standard 2^16 width** | **yes** | **4× in Rust, 1× in Lean** | **recommended** |
| 8 × u32 mod p (today) | 8 | 1 | none | yes | everywhere | non-injective, O(1) collisions |

11 × u24 is the interesting near-miss and it loses cleanly: it saves 5 felts of *preimage* width,
which buys nothing because both fit in one absorb, and pays for it with a range-check story that
either needs a 16-million-row table or decomposes back into 16-bit lookups anyway.

### 2.3 The design: two layers, because injectivity and binding are different requirements

The zoo exists partly because one map was asked to do two jobs. Separate them:

**Layer L — `Limbs16`: the injective byte→felt map.**

```
Limbs16(b: [u8;32]) = [ BabyBear(u16::from_le_bytes([b[2i], b[2i+1]])) ; i in 0..16 ]
```

Injective by construction (`2^16 ≪ p`, so no reduction occurs and the inverse is a memcpy).
In-AIR canonicity is 16 range checks at 16 bits — the cheapest lookup width available.
Used wherever the value must be **recoverable, ordered, or range-checked**: sorted-map addresses,
AAFI brackets, lex comparators, hash preimages, witness columns.

**Layer D — `Digest8`: the binding fixed-width commitment.**

```
Digest8(domain, b) = chip_squeeze( domain ‖ Limbs16(b) )      // one permutation, 8 output lanes
```

Not injective — §2.1 proves nothing 8-wide can be — but **hard**: collision cost is the birthday
bound over `p^8`, i.e. **2^123.63**, versus the F1 encodings' **O(1)**. That is the entire point.
Used wherever a value must be **bound in a fixed-width committed slot**: PI octets, carrier
octets, state-commitment limbs, map values.

**The reframe this forces, and it is the substantive one:** the failing sites do not fail because
they are non-injective. `Digest8` is non-injective too and is fine. They fail because they are
**raw non-injective *projections* (free, constructible collisions) where a *hard* non-injective
*compression* was required.** "Injective" was never the security property; it is a *sufficient*
property that Layer L happens to have for free, and it is the *necessary* property only where the
felts must be inverted or ordered.

**Width consequence:** at PI/column sites, `Digest8` is **8 felts — the same width as today**, and
in several places *narrower* (`circuit/src/bridge_action_witness.rs` publishes 24 PI slots as
3 × 8 limbs; 3 × `Digest8` is also 24, but `effect_action_air`'s per-field 8-slot layouts and
`ci_assurance`'s `CI_PI_COUNT = 25` are unchanged). **The migration is width-neutral at the
committed boundary and rate-neutral at the hashed boundary.** The 2× cost ember was rightly
worried about does not materialize anywhere it would have mattered.

**Banned by construction:** `Digest1` — any 32-byte value compressed to a *single* felt. Birthday
cost is `2^15.45`. There is no security boundary where that is acceptable. Sites that structurally
need one felt (today's 1-felt map keys and the `iroot` MMR) migrate to `Limbs16` keys with a lex
comparator, or to `Digest8` — not to a better 1-felt fold.

### 2.4 We already own the hard part, in Lean, `#guard`-checked

`metatheory/Dregg2/Circuit/Emit/FaithfulNoteSpendDescriptorPlan.lean` already contains the full
canonical-codec machinery, authored on the correct substrate:

* `BYTES32_U16_LIMBS := 16`, `U64_U16_LIMBS := 4` (`:58`, `:59`) — Layer L, with the file's stated
  convention: *"Every multi-limb integer/byte string is little-endian."*
* `u16Ranges base count` (`:384`) building a `RangePlan` of 16-bit checks; `rangePlan.length == 132`
  is `#guard`-ed (`:399`) — the range-check discipline, already emitted.
* **`Pack8Plan` / `packBodiesAt` (`:339`–`:373`) — the canonical `Digest8 ↔ Limbs16` bridge**, and
  it is precisely the "alias-rejecting gate" from §2.1 applied in the direction where it works.
  Its own doc (`:326`–`:337`) states the problem exactly right:

  > *"An equality `digest = lo + 2^16 hi` alone is not enough over BabyBear: for small digest
  > values, `digest + p` also fits in 31 bits."*

  and closes it with `hi + slack = FIELD_HI_CANON_MAX (0x7800)`, both 15-bit; `z` an exact zero
  indicator of `slack`; and `slack = 0 ⇒ lo = 0` (since `p = 0x78000001`). Six constraints per
  lane, 48 per octet. Conclusion in the file: *"every eight-felt digest has one canonical 32-byte /
  sixteen-u16 image in the AIR."*

This means the codec is **not new work in the risky place.** The AIR-side gadget exists, is
Lean-authored, and is guard-checked. What is missing is a *designation* and the Rust side calling
it instead of re-inventing.

### 2.5 Endianness — decided, because three copies disagree

Four independent implementations of Layer L exist and they are **not** all the same map:

| Site | Order | Status |
|---|---|---|
| `circuit/src/exact_nullifier_aafi.rs:407` `raw_to_u16_le` (+ inverse `u16_le_to_raw:415`) | **LE** | **LIVE** — backs the deployed exact fields root |
| `cell/src/note.rs:201` `bytes32_to_u16_limbs` | LE | faithful-v2 note path, pre-cutover |
| `circuit/src/exact_cap_root.rs:61` `bytes32_to_u16_le` | LE | exact cap leaves, not yet the live cap root |
| `turn/src/umem.rs:1499` `bytes32_to_u16_be` | **BE** | umem V2, staged/unarmed |

**Decision: little-endian.** Three of four, the *deployed* one, and Lean's stated convention.

The BE choice in umem was **not** arbitrary and deserves an explicit answer: BE limbs make
lexicographic order on the limb vector agree with `memcmp` on the source bytes, which is what a
sorted map's bracket gadget wants. The resolution is that **order is a property of how a comparator
reads the columns, not of the codec**: a lex comparator over LE limbs reads indices `15..0` instead
of `0..15`. That is a column-index change in the Lean descriptor with **zero constraint cost**.
umem V2 is staged and unarmed, so flipping it is free — do it before it arms.

Integers keep place order (`u64 → 4 × u16` LE, `value = Σ limbᵢ · 2^16i`), which LE also gives.
One rule, no exceptions.

### 2.6 Recommendation

> **The canonical codec is `Limbs16` — 16 little-endian u16 limbs — promoted from
> `circuit/src/exact_nullifier_aafi.rs:407` (`raw_to_u16_le` / `u16_le_to_raw`) into a new
> leaf crate `dregg-codec`, together with `Digest8 = chip_squeeze(domain ‖ Limbs16(b))` as the
> only permitted fixed-width committed form. Single-felt projections of 32-byte values are
> banned at security boundaries.**

Justification, in the order the decision actually turns on:

1. **An injective 8-felt encoding is impossible** (§2.1, pigeonhole, `p^8 = 2^247.26 < 2^256`) — so
   the choice is not "8 injective vs 16 injective", it is "9+ injective, or 8 non-injective".
2. **At 16 lanes the width is free where it is spent** (§2.2, `CHIP_RATE = 16`) — the 2× objection
   dissolves against a measured constant.
3. **Where width is not free, we do not spend it** (§2.3) — committed slots carry `Digest8` at 8
   felts, the same width as today, at `2^123.63` instead of `O(1)`.
4. **16-bit is the range-check width the AIR already emits** (§2.4, `u16Ranges`, `rangePlan`).
5. **The hard in-circuit gadget already exists in Lean and is `#guard`-checked** (§2.4, `Pack8Plan`).
6. **It is already deployed** in the one place someone did this correctly (`exact_fields_root`), so
   the migration target is a *live, exercised* code path rather than a design sketch.
7. **9 × base-`p` and 11 × u24 are strictly dominated** (§2.2 table) — smaller by a width that
   costs nothing, larger by a gadget cost that does.

---

## 3. The migration

Grouped by **what a fix breaks**, which is the only grouping that determines ordering.

**The window argument, stated plainly:** nothing is deployed, the devnet ledger was already lost on
reboot, and no external party holds a receipt whose hash must remain valid. A consensus-affecting
change costs a **re-genesis, which today is free.** It will not be free later. **Every
consensus-affecting item below should land now, in one epoch, or it becomes permanent debt.** This
is the single highest-leverage scheduling fact in the document.

### Stage 0 — BYTE-SAFE. No arithmetic moves. (closes 0 wounds; unblocks all of them)

1. Create `dregg-codec` (leaf crate, no deps beyond the field): `Limbs16`, `Digest8`, `Bytes32`
   wrapper, inverse, domain-tag registry. **Additive; nothing calls it yet.**
2. Correct or delete the **~30 false doc-comments** in §6. Free, and it stops the disease
   propagating into the next author's file.
3. Delete the **11 dead encoders** (§5, grep-confirmed zero callers).
4. Rename `turn/src/rotation_witness.rs:174 fold_bytes32_to_bb_limbs` — it delegates to the
   *faithful* `bytes32_to_8_limbs`, and the name invites exactly the faithful-vs-degraded confusion
   this whole document is about. Pure naming hazard, zero behavior.
5. Land the new linter (§4) in **report-only** mode so the true site count is measured, not
   estimated.

### Stage 1 — BYTE-SAFE. Collapse duplicates without changing any byte. (closes the DRIFT class)

The ~17 implementations realize 4 arithmetics, and within each family the copies are
**byte-identical** (verified by lane 4 via `grep '0x3F) << 24'` finding 4 bit-identical F2 bodies;
by lane 6 for the ~16 F1 copies). So each family can be collapsed to **one** implementation with
**zero** value change — a pure de-duplication.

Re-point every copy at one definition per family, marked `#[deprecated]` and `#[doc(hidden)]`.
No root moves, no VK regenerates, no test fixture changes.

**This closes the reinvention class immediately**, before any risky work. After Stage 1 there are
4 encoder bodies in the tree, not 17, and Stage 2+ has 4 things to change instead of 17.

### Stage 2 — VK-AFFECTING, non-consensus. The preimage layer. (closes ~35 of ~52)

Sites where the encoder output is **absorbed into a hash** whose *committed* form is already an
8-felt root or digest. Swapping the preimage codec changes the **value** of the root — so every
KAT, differential pin, and descriptor regenerates — but **no width, no PI layout, and no state
commitment structure moves.**

Order within the stage, hardest-hit first:

| Order | Sites | Wounds |
|---|---|---|
| 2a | `cell/src/state.rs:583,1014,1054` heap leaf **value** — the only LIVE, DEPLOYED, attacker-DIRECT, O(1) site with **no** exact replacement (fields got one; heap did not) | #18/#19 class |
| 2b | `cell/src/commitment.rs:547,552` CapLeaf `target`/`breadstuff` → cut over to the **already-written** `exact_cap_root` | #24 |
| 2c | `cell/src/note.rs:315,316,443–447,573,574` note commitment/nullifier preimages → `faithful_nullifier_v2` (already in-file) | — |
| 2d | `commit/src/typed.rs:606` `compress_member` — the membership leaf for cap/adjacency/nullifier/sender-authority sets | F2 |
| 2e | `turn/src/bilateral_schedule.rs:116,483,551–591` — seven accumulator roots, PI-checked at `proof_verify.rs:2852` | F2 |
| 2f | `dregg-doc/src/ci_assurance.rs:260–262` (+ the adjacent `exit_code % p` fail→0 at `:265`) | #6 |
| 2g | `zkoracle-prove/src/{attestation.rs:48,render.rs:183,198}`, `circuit-prove/src/zkoracle_leaf_adapter.rs:176,252` | #18/#19 |
| 2h | `storage/src/bucket_commitment.rs:122`, `starbridge-apps/site-host/src/site.rs:187`, `sandstorm-bridge/src/cell.rs:60,72` — public-substrate content roots, all attacker-DIRECT O(1) | — |
| 2i | `cell/src/program/eval.rs:2822` `KeyRotationGate` — self-committed `hash_bytes(next_keys)` permits **pre-committing an alias pair**, i.e. O(1) rotation equivocation | — |
| 2j | `commit/src/poseidon2_tree.rs:632` `commitment_to_field` → `persist/note_tree`, `poseidon2_note_tree`, `intent/lib:295`, `intent/gossip` | — |
| 2k | `sel4/…/crypto-floor/src/lib.rs:159,224` — the keyed-MAC tag reduction pulls EUF-CMA to ~2^31 **inside the verified partition** | — |

### Stage 3 — VK-AFFECTING + PI GEOMETRY. The committed-slot layer. (closes ~10)

Sites where limbs sit in **PI slots or trace param columns**. Replace *limbs-in-PI* with
*`Digest8`-in-PI*. Width-neutral or narrowing; PI offsets move, descriptors regenerate.

* `circuit/src/bridge_action_witness.rs:159–161` — `nullifier[8] ‖ recipient[8] ‖
  destination_federation[8]`, attacker-DIRECT, and **the most consequential unknown in §7**.
* `circuit/src/effect_action_air.rs:190,231` — per-effect PI slots `[8i, 8i+8)`.
* `turn/src/executor/effect_vm_bridge.rs:104` (+24 call sites) and its byte-twin
  `sdk/src/cipherclerk.rs:6741` (+23) — the two deployed projectors. **They must move in exactly
  one commit**; a skew between them is worse than the wound.
* `turn/src/executor/effect_vm_bridge.rs:278–288` — the *third* inline clone (EmitEvent
  topic/payload). Deleted in Stage 1; called out here because its descriptor moves.
* `circuit/src/effect_vm/trace.rs:26` `canonical_id_to_felts_4` — the inline AIR twin binding
  `federation_id` / `owner_cell_id` into row-0 aux columns.
* `turn/src/executor/proof_verify.rs:626` custom-proof entry binding; `:3212` `KEY_COMMIT` teeth;
  `circuit/src/effect_vm/trace_rotated.rs:4615` the in-AIR `_4` rider.
* `dregg-doc/src/ci_assurance.rs:232,236` — `CI_PI_COUNT` / `COL_EXIT` move.
* `circuit/src/faithful8.rs` — the type wall is re-founded here (§4).

### Stage 4 — CONSENSUS-AFFECTING. One epoch, all of it, now. (closes #5/#9/#11/#20/#23/#24/#33)

Everything that moves `pre_state_hash` / `post_state_hash`, a receipt hash, or a `MapOp` key width.
**These cannot be staged relative to each other** — they share the rotated block and the descriptor
key type. One epoch, one re-genesis.

* **The `MapOp` key widening.** `metatheory/…/DescriptorIR2.lean:301–313` types `MapOp.key` as
  **one** `EmittedExpr`; `EffectVmEmitRotationV3.lean:2410` sets `key := .var col`. Widening to
  `Limbs16` changes `MapOp`, the sorted-bracket / AAFI comparators (extend `LexCompare8Emit`'s
  `lexLt8_refines` to 16), and the leaf schema. **This is Lean-authored AIR work and belongs in
  Lean** — the leaf-schema widening plus the kernel flip is the ember-gated part.
* The 1-felt accumulator **keys** that ride it: `cell/src/{nullifier_set.rs:592,
  commitment_set.rs:270, revoked_set.rs:282, shielded_note_set.rs:279}`,
  `turn/src/rotation_witness.rs:326` (`cells_root`, wound #23's *still-narrow* key — the file's own
  doc already flags it), `exec-lean/src/nullifier.rs:138`,
  `circuit/src/effect_vm/trace_rotated.rs:1459` (wound #20 — a public system-wide constant whose
  key domain is attacker-writable via `RevokeDelegation`; **the single worst site in the
  catalogue** by blast radius).
* `turn/src/umem.rs:1162,1193,1208` — V1 codec **deleted**, V2 `UAddrV2`/`UValV2` armed, endianness
  flipped to LE (§2.5). Free today because V1 is staged and `umem_witness_enabled` is unflipped.
* `turn/src/rotation_witness.rs:346` `iroot` — the receipt-log MMR leaf **and** its 1-felt root.
* `turn/src/executor/proof_verify.rs:3371,3401,3412` + `verifier/src/lib.rs:466,480` +
  `turn/src/conditional.rs:816` + `node/src/mcp/proof.rs:200,204` +
  `turn-prover/src/proven_receipt.rs:126` — the turn-identity / receipt-identity binding. **Producer
  and verifier halves must land together** or every receipt check breaks.
* `turn/src/rotation_witness.rs:549` `B_PUBKEY_OCTET`; `circuit/src/poseidon2.rs:596`
  `lifecycle_payload_felt` (limb 29); `cell/src/commitment.rs:737` `canonical_to_babybear_pi`.

### Ordering rationale

Stages 0 and 1 are free and make everything after them 4× smaller. Stage 2 carries the most
security value per unit of risk — it closes ~35 of ~52 including *every* O(1)-exploitable
public-substrate site — and touches no geometry. Stage 3 is mechanical once the codec exists.
Stage 4 is the only irreversible one, so it goes last **in sequence** but must not slip **in
calendar** — it is the stage the free-re-genesis window is open for.

---

## 4. The wall (kind F)

### 4.1 Why `Faithful8` worked and why it was not enough

The `Faithful8` newtype (`circuit/src/faithful8.rs`) is a **correct and effective** piece of
design and the precedent to build on. Read its evidence honestly:

* It works exactly where applied. Wound #23 — a 1-felt heap root inside the consensus anchor — sat,
  in the words of its own fix comment (`turn/src/rotation_witness.rs:302`), *"three fields away
  from three siblings (`nullifier_root`/`commitments_root`/`revoked_root`) that were already
  `Faithful8`."* Three correct uses, one bare `BabyBear`, same struct, ~2^31 grind on the
  consensus anchor. **The wall's absence is what made #23 possible, and its presence is what made
  the three siblings safe.** That is as clean a natural experiment as one gets.
* The private inner field, the named-constructor discipline, and the two `compile_fail` doctests
  are all right.

**But it guards the wrong axis.** `Faithful8` was built to catch the **width** class (1 felt vs 8),
and it does. It has **no opinion whatsoever about whether those 8 felts are a hard compression or a
free-alias projection.** Its own constructor list admits the failures:

* `from_bytes32` **is** `bytes32_to_8_limbs` — family **F1**, O(1) aliasable.
* `from_canonical_key` **is** `canonical_32_to_felts_8` — family **F2**, 16 source bits discarded.
* `from_lossy_31bit_DANGER` — an explicit, named escape hatch (correctly greppable, but open).

And the module doc asserts what the constructors do not deliver: *"possession of a `Faithful8` is
evidence the value came from a faithful encoder."* For a directly-chosen preimage that is **false**,
and the type wall then **launders** it — a sink cannot distinguish an aliased octet from a faithful
one. This is the anti-launder clause realized in our own code.

Second gap, and it is where most of the remaining wounds live: **the wall covers committed VALUES
and leaves map/sort KEYS bare.** Every kind-D wound (#5, #9, #11, #20, #23's residual, #24, #33) is
a **key**, and a key is a bare `BabyBear` that no type ever guarded.

### 4.2 The replacement wall

**Three types, one crate (`dregg-codec`), and the raw byte array cannot escape any of them.**

1. **`Bytes32`** — the only carrier of a 32-byte value that is allowed to produce felts. Its
   *entire* felt-producing surface is `.limbs() -> Limbs16` and `.digest8(Domain) -> Digest8`.
   There is no `impl From<[u8;32]> for BabyBear` and no way to obtain a felt from bytes without
   naming one of the two.
2. **`Digest8`** — replaces `Faithful8`, with the constructor set **narrowed**, which is the whole
   point: `from_limbs16` (chip squeeze), `from_root8` (crate-private tree folds),
   `from_wire_commit{,_chip}`, `ZERO`. **`from_bytes32`, `from_canonical_key`, and
   `from_lossy_31bit_DANGER` are deleted, not deprecated.** A wall with an escape hatch is a
   convention.
3. **`MapKey`** — **new, and the gap `Faithful8` never covered.** Every accumulator / sorted-map /
   heap / umem key parameter takes `MapKey` (a `Limbs16` newtype carrying its lex order), never a
   bare `BabyBear`. This is the type that would have made #20 and #23's residual unrepresentable.

Additionally: `BabyBear::{encode_hash, from_bytes_packed, decode_hash, from_bytes}` become
crate-private to `dregg-codec` or are deleted (§5). They are the raw material of family F1 and
there is no legitimate caller outside the codec.

### 4.3 What the linter must catch that no type can

A type wall cannot see **arithmetic**. Nothing stops an author writing
`BabyBear::new(u32::from_le_bytes([b[0],b[1],b[2],b[3]]))` inline — that is precisely how ~17
implementations came to exist, and it is a type-correct expression. So the linter's job is the
**shape**, not the name:

| # | Pattern | Catches |
|---|---|---|
| L1 | `BabyBear::new($X)` where `$X` derives from `u32::from_{le,be}_bytes` / `% BABYBEAR_P` on byte-derived data | **F1 reinvention** — the root of 3 of 4 families |
| L2 | `& 0x3F`, `& 0x7FFF_FFFF`, or any mask applied between bytes and a felt | **F2 reinvention** (bit-discard) |
| L3 | a loop or `array::from_fn` whose body indexes a `[u8; _]` and constructs a felt | **any** new byte→felt map, named or not |
| L4 | `.as_u32()` / `felt.0` narrowing back to bytes within a function that also touches a commitment/PI symbol | felt→byte laundering |
| L5 | a bare `BabyBear` in a struct field or fn parameter named `*_key`, `*_addr`, `*_root`, `*_commit`, `*_nullifier`, `*_id` | **the kind-D key class** the type wall is being added for — belt-and-braces during migration |
| L6 | the words `injective`, `bijection`, `collision-resistant`, `binds the full`, `~256-bit`, `measure-zero` within N lines of a felt-producing `fn` | **the false-doc class itself** (§6) — 30 instances say this is worth automating |

**Why `scripts/check-no-degraded-felt.sh` must be replaced, not extended.** Read against its own
text, three structural limits:

1. **It scans 3 files.** `SCOPED_PATHS = {cell/src/commitment.rs, turn/src/rotation_witness.rs,
   circuit/src/effect_vm/trace_rotated.rs}` — 3 of ~14 crates containing security sites.
2. **It matches one symbol name** (`fold_bytes32_to_bb`) — family **F4 only**, which is 109 of
   ~900 references. F1, F2, and F3 are entirely invisible to it, and **F1 is the seed of three
   families.**
3. **Its scoping rationale is itself the wound.** The rule declares the executor/SDK projectors and
   accumulator keys *"sound THERE"* — a judgment about the **root** position (faithful root8) that
   does **not** hold for the **key** the leaves fold. That is exactly the #5/#20 class, excluded by
   the gate's own comment.

It is a **symbol blocklist**. A blocklist cannot catch a *new name* for the *same arithmetic*,
which is the exact failure mode that produced ~17 implementations.

**The replacement is an allowlist gate:** *no byte→felt arithmetic may appear anywhere in the
repository outside `dregg-codec/src/limbs.rs`.* Repo-wide by default, matching on shape (L1–L3),
with a single-file allowlist and per-line `ast-grep-ignore` justification for genuine residuals —
the pattern the current script already gets right. Two properties worth keeping from the existing
script and one to add:

* **Keep:** it FATALs (exit 2) if a scoped path vanishes, refusing to report green having scanned
  nothing. That instinct is correct and should be preserved as *"FATAL if the allowlisted codec
  file is missing."*
* **Keep:** inline `ast-grep-ignore` with a mandatory human reason on the line above.
* **Add:** the gate must print **how many files it scanned and how many patterns matched**, so a
  green that scanned nothing is visibly distinguishable from a green that scanned everything.

Finally, the wall the linter cannot build either: **the Lean side must model the byte→felt step.**
Today the Lean AIRs model keys and targets as *abstract felts* (`CapRootBridge.edgeLeafOf`,
`DeployedCapOpen.targetBindGate`, `DescriptorIR2.MapOp.key`), so every binding theorem holds over
the **post-encoding felt** and the encoder's non-injectivity is **invisible to the proof**. Lean
does not currently disagree with Rust — both encode the same non-injective map, which is why the
census found no accept-divergence — but Lean also cannot *see* the wound. `Limbs16` +
`Pack8Plan` (§2.4) is what lets the Lean model finally quantify over the **bytes**.

---

## 5. The deletions

Standing rule: go unadditive. Each of these is **deleted and rewired**, not deprecated behind a
flag. Named with its last consumer so the rewire is a bounded task.

### Deleted immediately (Stage 0 — dead, grep-confirmed zero callers)

| Encoder | Last state |
|---|---|
| `turn/src/executor/proof_verify.rs:2678,2723` `expected_notespend_nullifier_bb` / `expected_notecreate_commitment_bb` | `#[allow(dead_code)]`, zero callers |
| `turn/src/executor/proof_verify.rs:2759,2777` `expected_burn_target_limbs` | `#[allow(dead_code)]`, zero callers |
| `commit/src/poseidon2_tree.rs:643` `hash_bytes_to_field` | test + re-export only |
| `turn/src/rotation_witness.rs:254` `root_felt` | production callers already on the wide path; only a shift-assertion references it |
| `bridge/src/present.rs:1027` `build_circuit_witness` (and its `:1058` fold) | `#[allow(dead_code)]` legacy linear path |
| `cell/src/state.rs:464` `fields_root_leaves` fold | superseded by the exact-u16 V2 path |

### Deleted in Stage 1 — duplicate bodies (byte-identical; collapse is value-preserving)

**Family F1 (~16 copies → 0).** `circuit/src/field.rs:212` `BabyBear::encode_hash`; `:194`
`from_bytes_packed`; `:222` `decode_hash` (lossy inverse — its existence invites round-tripping a
non-injective map); `circuit/src/effect_vm/helpers.rs:37` `bytes32_to_8_limbs`;
`circuit/src/bridge_action_witness.rs:125` and `circuit/src/effect_action_air.rs:151` `encode_hash`;
`cell/src/note.rs:176` `bytes32_to_limbs`; `circuit/src/note_spending_witness.rs:365`
`bytes32_to_limbs` + `key_to_field_elements`; `turn/src/action.rs`
`stark_delegation_bytes32_to_babybear` (this list said `action.rs:576` under `cell/src/`; the crate was wrong
and the body has since been collapsed into `circuit/src/effect_vm/helpers.rs`); the three nested `bytes32_to_8_felts` clones at
`turn/src/executor/effect_vm_bridge.rs:278`, `sdk/src/cipherclerk.rs:6750`,
`node/src/mcp/proof.rs:560`; `cell/src/commitment.rs:1447` `bytes32_to_felt8`;
`bridge/src/present.rs:1760` `bytes_to_babybear_vec`.
*Last consumers:* the two deployed projectors (`effect_vm_bridge.rs:104`, `cipherclerk.rs:6741`)
and `Faithful8::from_bytes32`.

**Family F2 (~5 copies → 0).** `commit/src/typed.rs:565` `canonical_32_to_felts_8` and `:618` `_4`;
`storage/src/commitment.rs:512` (byte-identical cross-crate duplicate);
`cell/src/commitment.rs:737` `canonical_to_babybear_pi`; `circuit/src/effect_vm/trace.rs:26`
`canonical_id_to_felts_4` (inline AIR twin).
*Last consumers:* `Faithful8::from_canonical_key`, `compress_member`, the turn-identity PI path.

**Family F3 (~10 copies → 0).** `circuit/src/cap_root.rs:254` `fold_bytes32` + `encode_breadstuff`;
`bridge/src/present.rs:1766` `bytes_to_babybear`; `sdk/src/cipherclerk.rs:4803` twin;
`commit/src/poseidon2_tree.rs:632` `commitment_to_field`; `sdk/src/privacy.rs:625`
`revocation_hash_to_field`; `turn/src/executor/apply.rs:2323` nested `compress`;
`dsl/deco_payment.rs:95` and `dsl/note_spending.rs:793` inline folds; `intent/src/lib.rs:554`
inline; `circuit/src/openable_fields_root.rs:556` `fold_value32` (legacy v1, superseded in-file by
`ExactFieldsLeaf`); `circuit/src/poseidon2.rs:566` `hash_bytes`.

**Family F4 (1 body, ~100 references).** `circuit/src/effect_vm/helpers.rs:167`
`fold_bytes32_to_bb` — **the worst arithmetic in the tree** (an onto F_p-linear form: *both* a
collision *and* a hit on any chosen target felt are one linear solve). The repo's own test
`circuit/tests/effects_hash_fold_and_burn_target_width.rs:95`
(`fold_bytes32_to_bb_collides_in_o1_because_it_is_linear`) already exhibits the constructor.
*Last consumers:* the 4 `accumulator_leaf` key sites, both projectors,
`node/src/turn_proving.rs:1079` `nullifier_to_field`, `trace_rotated.rs:1459`.

**Narrow-4-byte projectors (worse than F1 — 28 bytes discarded).**
`storage/src/commitment.rs:485` `fe_to_bb`; `turn/src/executor/mod.rs:182` `fe_to_bb`;
`node/src/mcp/proof.rs` inline `project_setfield_to_vm`.

**Redundant *correct* codecs (keep exactly one).** Delete `cell/src/note.rs:201`
`bytes32_to_u16_limbs`, `circuit/src/exact_cap_root.rs:61` `bytes32_to_u16_le`,
`turn/src/umem.rs:1499` `bytes32_to_u16_be`; **promote**
`circuit/src/exact_nullifier_aafi.rs:407` `raw_to_u16_le` / `:415` `u16_le_to_raw` into
`dregg-codec`. Also delete the injective-but-fifth-codec 3-byte `encode_bytes_to_felts`
(`commit/src/typed.rs:531` **and** `storage/src/commitment.rs:482` — even the correct answers were
duplicated).

**Kept, re-founded.** `circuit/src/effect_vm/helpers.rs:122` `field_limbs8` — its lane-0-first
order is deployed protocol ABI for the welded rotated limbs and its doc-comment correctly warns of
the lane-order hazard. It becomes a *view* over `Limbs16` in `dregg-codec`, not a separate encoder.

**Deletion tally: ~34 encoder bodies and 11 dead functions removed; 1 canonical codec remains.**

---

## 6. The false doc-comments

Every one of these asserts a property the code does not have, and each was written in good faith by
someone reasoning about their own site. They are listed for **correction or deletion in Stage 0**,
because a false comment is how the next author inherits the mistake.

**Asserted injectivity / bijection (flatly false):**

| Location | Claim | Reality |
|---|---|---|
| `storage/src/commitment.rs:429` | *"via the fixed `canonical_32_to_felts_4` **BIJECTION**"* | lossy fold over a 16-bit-discarded octet. **The same file at `:283–284` correctly says "NOT a bijection"** — it self-contradicts |
| `app-framework/src/blinded_endpoint.rs:260` | *"the fixed `canonical_32_to_felts_4` **BIJECTION**"* | same non-bijective fold |
| `cell/src/note.rs:164–174` | *"two 32-byte values differing in ANY byte produce a distinct limb vector … **measure-zero**"* | the alias set is **53.1%** of the chunk space — the exact opposite of measure-zero |
| `circuit/src/note_spending_witness.rs:358–363` | same distinctness claim, alias set mischaracterized | ditto |
| `cell/src/commitment.rs:729–737` | *"30-bit truncation … guarantee a **unique encoding**"* | true about mod-`p`, false overall: 16 bits are discarded |
| `circuit-prove/src/zkoracle_leaf_adapter.rs:62` | *"byte↔limb packing **injectivity**"* | `from_bytes_packed` is the mod-`p` alias map |

**Asserted ~256-bit / full-value binding (overstated):**

| Location | Claim | Reality |
|---|---|---|
| `circuit/src/faithful8.rs:3–5,22–24,77,81,92–95` | *"~124-bit binding"*, *"possession of a `Faithful8` is evidence the value came from a **faithful** encoder"* | `from_bytes32` **is** `bytes32_to_8_limbs` (F1). **The wall launders the alias** — §4.1 |
| `circuit/src/faithful8.rs:126–138` | *"240 bits, faithful"* for `from_canonical_key` | 240 is the **image** size; 16 **source** bits are unbound and second-preimage is O(1) for a direct input |
| `bridge/src/present.rs:1759–1760` | *"preserves **full 256-bit distinguishability**"* | mod-`p` alias; **this is the F1 root comment** for the whole `hash_bytes` family |
| `turn/src/executor/effect_vm_bridge.rs:95–103` + `sdk/src/cipherclerk.rs:6734–6743` | *"full 256-bit binding path"* | true only for hash-image inputs; O(1) for chosen bytes |
| `turn/src/executor/effect_vm_bridge.rs:72–75` + `sdk/src/cipherclerk.rs:6719–6721` | *"binds the **full 32-byte value**"* | binds a ~31-bit linear image. The 4-byte-truncation fix it describes was real; the framing overstates the result |
| `circuit/src/bridge_action_witness.rs:118–124` **and** `circuit/src/effect_action_air.rs:145–149` | *"the **canonical** bridge-action encoding"*, *"collision probability ~p⁻⁸ ≈ **2⁻²⁴⁸**, well above the 124-bit STARK soundness target"* | 2⁻²⁴⁸ is the **random** all-limbs-collide probability, not the adversarial cost, which is **O(1)**. Copy-pasted onto two deployed encoders |
| `circuit/src/effect_vm/helpers.rs:136–158` | *"**Collision-resistant** fold"*, *"collide only with ~2⁻³¹ probability for random inputs"* | an onto **linear** form: chosen-input collision **and** targeted hit are O(1). Contradicted by the repo's own test at `circuit/tests/effects_hash_fold_and_burn_target_width.rs:95` |
| `circuit/src/effect_vm/helpers.rs:181–190` | `refusal_reason_bytes` *"at ~256-bit strength"* | holds only because the input is a hash image, not by the encoder |
| `circuit/src/effect_vm/helpers.rs:31–33` | *"the **canonical** full-32-byte limb decomposition"* | "canonical" is precisely the word that invited the reinvention |
| `circuit/src/cap_root.rs:248–253` | *"**collision-resistant** under the Poseidon2 sponge (up to the per-limb mod-p wrap)"* | discloses the wrap but frames it as benign; the collision is **upstream** of the sponge. In-tree exhibit: `exact_cap_root.rs:505` |
| `commit/src/poseidon2_tree.rs:630–631` | *"a one-way **binding**"* | a single ~31-bit felt is not collision-binding (~2^15.45) |
| `sandstorm-bridge/src/cell.rs:70–71` | *"binding under **Poseidon2 collision-resistance**"* | one ~31-bit felt over attacker-direct bytes: the pair is constructed, not searched |
| `bridge/src/present.rs:1763–1765` | *"preserves collision resistance … while using all 256 input bits"* | ~2^15.45 birthday; the seed does not use 256 bits injectively |
| `turn/src/executor/proof_verify.rs:3205–3210` | *"the AIR-bound 4-felt commitment to a 32-byte Ed25519 owner pubkey"* | silently drops 16 pubkey bits |

**Names the wrong mechanism entirely (stale):**

| Location | Claim | Reality |
|---|---|---|
| `dregg-doc/src/substrate.rs:124–127` | *"the substrate's `fold_bytes32` is collision-resistant over the full 32 bytes"* | the function it documents (`Leaf::finish`, `:127`) returns `blake3::hash` — `fold_bytes32` is not even called there |
| `starbridge-v2/src/deos_desktop/chrome.rs:70–73` | *"`fields_root` binds all 32 via `fold_bytes32`"* | the live `fields_root` uses the **exact-u16 V2** path; names a mechanism that is both wrong and non-binding |
| `sdk/src/full_turn_proof.rs:289` | *"already `fold_bytes32_to_bb`-d"* | the v13 fields-octet campaign replaced those folds with `field_limbs8` (`cell/src/commitment.rs:1134–1138`, `circuit/src/faithful8.rs:138–142`) |
| `turn-prover/src/aggregate_bilateral_prover.rs:243–253` | *"mirrors `canonical_32_to_felts_4` … matches its truncation discipline"* | that function masks **1 bit per felt** (`& 0x7FFF_FFFF`), not the 2-bits-per-limb `0x3F` discard — a *different*, less lossy truncation wrongly equated |
| `starbridge-apps/site-host/src/site.rs:168` | *"~130-bit FRI soundness (not the ~31-bit floor a single felt would be)"* | true of the per-asset digest; the collection **key** at `:187` is still one attacker-direct ~31-bit felt |

**Naming hazard (comment honest, name misleading):** `turn/src/rotation_witness.rs:174`
`fold_bytes32_to_bb_limbs` delegates to the **faithful** `bytes32_to_8_limbs`. Rename in Stage 0.

**Correct comments worth preserving as the model** — these authors got it exactly right and the
new codec's doc should read like them: `commit/src/poseidon2_tree.rs:90–92` (*"identifies a raw
chunk `x` with `x+p`"*); `storage/src/commitment.rs:283–284` (*"NOT a bijection … one-way map"*)
and `:972` (the `0x3F` bits are *"unbound"*); `turn/src/rotation_witness.rs:302` (the `cells_root`
*"⚑ STILL NARROW"* note, which flags its own residual and names the wound class);
`circuit/src/effect_vm/helpers.rs:110–118` (the `field_limbs8` LANE-ORDER HAZARD warning);
`circuit/src/openable_fields_root.rs:458` (the concrete `0x0800_0000 + p = 0x8000_0001` alias
canary); and `metatheory/…/CommitFaithfulRegrounded.lean`, which explicitly **removed** an
injectivity assumption rather than carrying it.

---

## 7. Honest unknowns

Nothing below is settled by this document. Each is stated with the specific thing that would
settle it.

1. **Is `bridge_action_witness` a soundness break or an availability break?** The census's uniform
   finding is that collisions *over-include* (both sides project identically ⇒ an honest turn goes
   UNSAT), which is availability. But `circuit/src/bridge_action_witness.rs:159–161` PIs
   `recipient` and `destination_federation` alongside the nullifier, and a colliding **recipient**
   would mean one bridge proof authorizes payment to either of two addresses — that is a genuine
   soundness break, not denial. **Settle:** construct the `+p` alias pair, run the prover, and check
   whether both recipients verify against one PI vector. **This is the single highest-value
   falsifier in the plan and it should run before Stage 2 scheduling.**
2. **Which nullifier path the live executor commits** — `cell/src/note.rs:315` (single-felt) or
   `faithful_nullifier_v2` (8-felt, same file). Two lanes could not resolve it. **Settle:** read
   the executor commit path end-to-end, or run the note-spend differential and observe which value
   lands in limb 26.
3. **Deployment status of the public-substrate crates** — `sandstorm-bridge`, `storage`,
   `starbridge-apps/site-host`. They emit commitments a self-verifying reader trusts, but whether
   they sit on the ledger consensus path (Stage 4) or off it (Stage 2) is unconfirmed and changes
   their stage. **Settle:** trace their roots to a receipt or confirm they terminate at a served
   artifact.
4. **`wasm/src/lib.rs:609,1810+`** — the code says *"in a real system this would be a STARK"* and
   returns a size **estimate**, so the ring path is probably a JS demo, but `fact_hash =
   hash_bytes(attribute_key)` is attacker-direct and SECURITY-shaped if live. **Settle:** confirm
   whether any verifier consumes it.
5. **Which "exact-u16" paths are live vs staged.** `exact_fields_root` is live; `exact_cap_root`
   and umem V2 appear staged. The Stage 2b/Stage 4 split depends on this. **Settle:** check the
   arming flags (`umem_witness_enabled` and the cap-root selection) and the staged registry.
6. **In-AIR range-check cost at scale.** One descriptor's `rangePlan.length == 132`. Sixteen u16
   checks per 32-byte value across every migrated site is a real trace cost that this document has
   **not** measured — only argued is cheaper than the alternatives. **Settle:** emit the migrated
   descriptors and measure trace width and constraint degree against HEAD.
7. **Whether `Digest8`'s 2^123.63 is the right target.** The deployed FRI posture is
   [[project-fri-soundness-reality]]'s **57 calculator bits**, so after this migration the codec is
   emphatically **no longer the binding constraint** — which is the correct outcome, but it means
   "we fixed the encoder" must not be described as "we fixed the soundness." **Settle:** the FRI
   correlated-agreement campaign, not this one.
8. **Whether any deployed root is genuinely consensus-anchored vs merely KAT-pinned.** Stage 2's
   claim to be "non-consensus" rests on this distinction and it was not exhaustively enumerated.
   **Settle:** enumerate the differential pins and classify each as fixture vs anchor.
9. **The census is a source read.** Six lanes read arithmetic; **no exploit was executed and no
   build was run.** Every collision cost above is derived from source, corroborated by two in-tree
   canaries (`exact_cap_root.rs:505` for the mod-`p` alias, and
   `effects_hash_fold_and_burn_target_width.rs:95` for the linear fold). **Settle:** the Stage 0
   linter in report-only mode gives a measured site count, and unknown #1's falsifier gives a
   measured exploit.

Two lane-reported items that are **not** unknowns but are worth carrying forward as work:
`sdk/tests/sovereign_rotated_wide.rs:374` may be type-stale (`fields_root_leaves` returning
`Vec<HeapLeaf>` into a parameter now wanting `&[ExactFieldsLeaf]`) — compile-confirm during
Stage 0; and `dregg-doc/src/ci_assurance.rs:265`'s `exit_code % p` aliasing failure→0 (wound #6) is
adjacent to Stage 2f and should ride with it.

---

## Appendix — the one-paragraph version

There is no canonical byte→felt codec, so seventeen were written, realizing four arithmetics, each
non-injective in a different way; that is why thirty-three wound entries look like thirty-three
problems. An injective eight-felt encoding is impossible (`p^8 = 2^247.26 < 2^256`), so the codec
splits in two: **`Limbs16`**, sixteen little-endian u16 limbs, injective by construction, costing
exactly one chip absorb because `CHIP_RATE = 16`; and **`Digest8`**, the Poseidon2 squeeze over
those limbs, eight felts wide — the same width deployed today — at `2^123.63` instead of `O(1)`.
The Lean AIR already contains the limb layout, the 16-bit range plans, and the canonicity gate,
`#guard`-checked. Migration runs byte-safe → VK-affecting → consensus-affecting, and the
consensus-affecting stage should land **now**, while a re-genesis is free. The wall becomes three
types with `MapKey` covering the keys `Faithful8` never guarded, and the linter matches
**arithmetic shape repo-wide** instead of one symbol name in three files. Thirty-four encoder
bodies are deleted. Roughly twenty sites are O(1)-exploitable today; none is a *demonstrated*
soundness break — the realized class is availability with occasionally global blast radius — and
the one candidate that might be worse (`bridge_action_witness`'s recipient aliasing) has a
falsifier waiting in §7.
