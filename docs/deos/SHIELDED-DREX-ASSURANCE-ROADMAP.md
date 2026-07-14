# Shielded DrEX — Assurance Roadmap

The north star: a DrEX where a batch **clears over hidden commitments** and the **only public
output is a proof that a fair, conserving, valid batch happened** — nobody, not even the operator,
learns who traded, the amounts, or the allocations.

This document maps the Lean/AIR/assurance work between what exists today and that north star. For
each of the six components it gives the honest grade (PROVEN / BUILT / NEEDED), a difficulty
(S / M / L / RESEARCH), dependencies, and a citation. Then a sequence, and the single most-valuable
next step.

Grading legend:
- **PROVEN** — a machine-checked Lean theorem (its *statement* audited, not just `#assert_axioms`-clean).
- **BUILT** — a circuit/AIR or Rust artifact that runs, with tested teeth (both polarities).
- **NEEDED** — the gap, with difficulty and what it depends on.

The whole tree's soundness floor is `HashCR` (Poseidon2 sponge collision-resistance) +
`Poseidon2ChipArithSound`, with the BCIKS20 list-decoding core proved for the deployed code and the
deployed FRI provably ~112.6-bit (memory `project-linking-tower-forgery-closure`). Everything below
inherits that floor for its STARK soundness; component 6 states where the shielded objects sit on it.

> **⚑ PQ posture correction (2026-07-14).** The shielded pool's value-commitment is today a Pedersen
> commitment over Ristretto (`cell-crypto/src/value_commitment.rs`), with a Schnorr excess and a
> Bulletproof range — all **discrete-log**. Pedersen *hiding* is perfect/information-theoretic and the
> STARK privacy path is statistical-ZK (`HidingFriPcs`), so **privacy is quantum-safe**. But Pedersen
> *binding* IS discrete-log, and DLog is **Shor-broken**: a quantum adversary recovers the generators'
> DLog relations, re-opens a value-commitment to a larger value, and forges a conservation-satisfying
> batch that **mints** while privacy hides the theft. So the shielded **value-binding / no-mint
> soundness is NOT post-quantum** — a real hole that contradicts dregg's PQ posture (ML-DSA, quantum-safe
> finality, memory `project-pq-metatheory-connected`), and is **not** covered by the PQ metatheory (whose
> floor `MSIS·MLWESearchHard·SchnorrDLHard·HashCR` uses DLog only as the *classical leg of a hybrid
> signature* with an MSIS fallback — the shielded binding has **no** lattice fallback). Component 2 below
> is rewritten to the PQ-correct target (Poseidon2 hash-commitment + fully-in-AIR STARK conservation,
> retiring DLog); see `docs/deos/PQ-SHIELDED-COMMITMENT.md`. The previously-named "full Ristretto
> EC-in-AIR" item is **deleted** — it entrenches the Shor-broken DLog rather than retiring it.

---

## The six components at a glance

| # | Component | PROVEN | BUILT | NEEDED (gap) | Diff. | Depends on |
|---|-----------|--------|-------|--------------|-------|-----------|
| 1 | Ring-clearing AIR | 2-leg spec + fusion spec | 2-leg tight-cycle apex | N-leg variable cycle + partial-fill `offer ≥ want_min` in-AIR | **M**(N-leg) / **M**(inequality) | in-AIR range gadget (exists) |
| 2 | **PQ value-commitment** (Poseidon2 hash + in-AIR STARK conservation) | field⇒integer conservation (no-wrap); Poseidon2 value_binding hiding | `value_binding` hash-commitment, in-AIR conservation gate, `VALUE_BITS` range gadget | migrate note-commitment Poseidon2 (not Ristretto); asset-coord + split/merge equality in-AIR; 64-bit in-AIR range; **retire Pedersen/Schnorr/Bulletproof DLog** | **M** (cutover) / **M–L** (64-bit) | Poseidon2 CR + in-AIR range (exist) |
| 3 | **ZK / reveal-nothing (the crux)** | abstract perfect-ZK lemma; Pedersen/nullifier hiding carriers | hiding PCS path (ZK=true), minimal PIs, tested | **clearing-level ZK theorem** — transcript independent of trades; simulator/indistinguishability; statistical-ZK of FRI PCS | **RESEARCH** | 1, 2; HidingFriPcs ZK floor |
| 4 | Membership + nullifier in-clearing | `shielded_spend_claim_refines`; deployed nullifier flip | apex `connect` binds legs to spend leaves | bind ring legs to the **deployed** nullifier accumulator (not per-leg toy pre-state) | **M** | deployed accumulator (exists) |
| 5 | Shielded SetField-attestation | — | — | attested-but-hidden per-trader allocation commitment; resolve SetField cohort ambiguity | **L** | 3, 4 |
| 6 | Composition + deployed-assurance | STARK soundness on real floors; fusion spec-proven | 2-leg apex folds green | fold N-leg apex under deployed VK; retire named EC/range residuals | **M→L** | 1, 2, 4 |

---

## 1. The ring-clearing AIR

**PROVEN.** `Market/ShieldedClearing.lean::shielded_ring_clears` — a shielded ring whose matched
cycle is `CycleValid` and settles through the verified executor is simultaneously conserving (per
asset, real ledger), fair (`RingBalanced` + every leg within its committed offer/want), and
private + no-double-spend (each leg a fresh member spend). `LedgerRealizationExt.lean::
shielded_ring_fused_clears` adds the **fusion** clause `LegFused` (the matcher's `node.offerAsset`/
`offerAmount` ARE a spent note's `asset`/`value`), with the load-bearing tooth
`legA_not_fused` (the un-fused demo leg does NOT satisfy it) and `fusedRing` non-vacuity.

**BUILT.** `circuit-prove/src/shielded_ring_clearing_air.rs` — the 2-leg, tight-cycle
ring-clearing apex. Enforces in-AIR: fusion gates (`offer_asset==asset`, `offer_amount==value`),
the `CycleValid` 2-cycle edges, the tight amount match (`offer_amount[k]==want_min[(k+1)%2]`),
distinct nullifiers (`nf₀!=nf₁` via inverse witness), Pedersen conservation, and the value-binding
recompute anchoring fusion to the spent note under Poseidon2 CR. The apex `connect`s each leg to a
real `prove_shielded_spend_leaf_with_claim`. Teeth tested: non-conserving, wraparound-mint,
out-of-range, double-spend, mis-fusion, mismatched-fold — all UNSAT.

**NEEDED.**
- **N-leg (variable-length cycles).** The AIR hard-codes `RING_LEGS = 2` and a leg-major column
  layout. Generalizing to N legs is a parameterized descriptor + the fold shape (`bind_leg_node`
  already generalizes leg-by-leg). **Difficulty M.** No new crypto; a descriptor-scaling build.
  The Lean side is already N-general (`shielded_ring_clears`/`_fused_clears` quantify over the list).
- **Partial-fill `offer ≥ want_min` inequality in-AIR.** The AIR enforces the *tight* swap
  (`offer_amount == want_min`); a genuine partial fill needs the **inequality** `offer_amount ≥
  want_min` as an in-AIR range/compare gate. The Lean partial-fill lowering is already ledger-real
  and general (`partialFill_cycle_ledger_realized`, `pricedPartialFills_conserves`, no tightness).
  **Difficulty M** — the Bignum range bedrock exists (`Dregg2.Bignum.legs_noWrap_conservation`,
  and the AIR's own `VALUE_BITS` bit-decomposition gadget); this is a compare gadget reusing it.

**Sequence note:** N-leg unlocks the app-wiring (a real DEX batch is not 2 legs); the partial-fill
inequality unlocks interior clearing. Both are M and independent of the crux (3).

---

## 2. PQ value-commitment — Poseidon2 hash + fully-in-AIR STARK conservation (retire DLog)

**⚑ This component was rewritten (2026-07-14) from "value-commitments in-AIR / full Ristretto
EC-in-AIR" to the PQ-correct target.** The old direction entrenched the Shor-broken Pedersen/Ristretto
discrete-log binding; the right direction retires DLog and lands the shielded value-binding on dregg's
existing PQ floors (`HashCR` / Poseidon2 CR, `Poseidon2ChipArithSound`, `HidingFriPcs` statistical-ZK).
Full diagnosis + migration scope: `docs/deos/PQ-SHIELDED-COMMITMENT.md`. **Options:** A (recommended) =
Poseidon2 hash-commitment + in-AIR STARK conservation; B (fallback) = a Module-SIS lattice homomorphic
commitment (PQ + homomorphic, but kilobyte commitments + a second lattice proof system). A dominates —
it reuses machinery the tree already carries and adds no new cryptographic system.

**PROVEN.** `RealCrypto.lean::twoLeg_noWrap_conservation` + `inAir_conservation_refines_pedersen`
— a field conservation gate `Σ value_in ≡ Σ value_out (mod p)` **plus the range bound** upgrades to
integer conservation. (Today this is stated as refining the group-Pedersen `ring_conserves_pedersen_list`;
under Option A the *same* no-wrap conservation stands on the STARK soundness directly — the target is to
re-anchor this refinement onto the Poseidon2 value-commitment instead of `pedTwoGen`, dropping the DLog
`binding` carrier.)

**BUILT — Option A is largely already present.** The three pieces of the PQ path exist in the codebase:
- **Hash value-commitment.** The shielded-spend circuit already publishes a **hiding Poseidon2 commitment
  to the value**: `value_binding = hash_fact(value, [randomness, 0, 0])` (C7,
  `shielded/spend_circuit.rs:39–40, 111–125, 143`; PI `[nullifier, merkle_root, value_binding]`), binding
  = Poseidon2 CR, hiding = the randomness blinder. This *is* the Option-A note-value commitment.
- **In-AIR conservation.** `Σ value_in − Σ value_out = 0` is a BabyBear field gate
  (`shielded_ring_clearing_air.rs`, clause (c)).
- **In-AIR range gadget.** Every conservation value is bit-decomposed into `VALUE_BITS` boolean columns
  with a compile-time `RING_LEGS·2^VALUE_BITS ≤ p` no-wrap assertion
  (`shielded_ring_clearing_air.rs::VALUE_BITS`, `RANGE_TARGET_COLS`), tested by
  `wraparound_mint_ring_is_unsat` / `out_of_range_output_is_unsat`. The AIR header itself notes this
  *"moves the shielded pool's per-output Bulletproof range proof from ATTESTED off-AIR to a CIRCUIT
  constraint."* That is the Option-A range gadget, landed for the BabyBear-scale range.

So the AIR already proves value conservation over hash-committed, in-AIR-ranged STARK witnesses. What is
still DLog is the **redundant off-AIR Pedersen aggregate** (`pedTwoGen` coordinate excess + the off-AIR
Schnorr `prove_asset_conservation` + the off-AIR Bulletproof `pool.rs::output_range_proofs` + the
Ristretto `commit_hidden_asset` bytes). This component is the decision to make the in-AIR hash+STARK path
the *sole* value-binding and **delete the DLog aggregate** — not a from-scratch build.

**NEEDED (the Option-A migration).**
- **Note commitment: Poseidon2, not Ristretto.** Make the on-chain leg the Poseidon2 `value_binding`
  (already a PI) rather than the 32-byte compressed Ristretto `commitment_bytes`
  (`pool.rs::HiddenAssetLeg`, `value_commitment.rs::commit_hidden_asset`). Extend the hash preimage to
  also commit `asset_type` (e.g. `hash_fact(value, [asset_type, randomness, 0])`) so one hash binds
  `(value, asset_type)` jointly, as the three-generator Ristretto commitment did. **Difficulty S–M.**
- **Conservation + asset-tag + split/merge equality: fully in-AIR, not off-AIR Schnorr.** Delete
  `prove_asset_conservation`/`verify_asset_conservation` (the Schnorr DLog excess). The value conservation
  is already the in-AIR field gate (c); fold the **asset-tag conservation** in as a second in-AIR field
  sum over the witnessed `asset_type` cells (replacing the `H_asset`-component check), and turn the
  split/merge `AssetEqualityProof` (a Chaum-Pedersen equal-DLog proof) into an in-AIR equality constraint
  over the witnessed asset cells. **Difficulty M** — wiring the asset coordinate into the same in-AIR
  conservation the value coordinate already uses.
- **Range: in-AIR 64-bit, not Bulletproof.** Delete `output_range_proofs` (`bulletproofs`). Extend the
  `VALUE_BITS` gadget to the full 64-bit amount via a multi-limb (Bignum) in-AIR range — the N-leg /
  multi-limb keystone `Dregg2.Bignum.legs_noWrap_conservation` already generalizes the no-wrap proof.
  **Difficulty M–L** (the 64-bit widening is the only real depth).
- **Drop the DLog crates from the shielded path.** Once the above land, `curve25519-dalek`, `bulletproofs`,
  and the Schnorr excess leave the shielded value-commitment TCB. (`ed25519-dalek` stays only as the
  *classical leg of the hybrid signature* — that surface IS covered by the PQ metatheory's hybrid combiner
  with an MSIS fallback; the shielded binding is the one with no fallback, so it is the one to retire.)

**Honest framing:** the *value-minting* soundness hole (the one that lets a batch print money) is CLOSED
in-circuit for the deployed field range — but its *binding floor today is DLog* (the `pedTwoGen`/Pedersen
model), which is **Shor-broken**. Option A re-anchors that same closed no-mint property onto Poseidon2 CR
+ STARK soundness, retiring DLog entirely. Most of the machinery already exists; the residual is a cutover
(delete Pedersen/Schnorr/Bulletproof, promote `value_binding` to the on-chain commitment) plus the 64-bit
in-AIR range widening. The old "full Ristretto EC-in-AIR" item is **deleted** — realizing the DLog curve
point in-circuit would deepen the exact assumption Shor breaks.

---

## 3. ⚑ The privacy / zero-knowledge property — "nobody learns what settled" (THE CRUX)

This is the new thing and the differentiator. It must be scoped exactly, because the codebase today
proves *soundness* of the clearing (it conserves, it is fair, it cannot double-spend) but has **no
theorem stating the clearing proof is zero-knowledge over the trades**. Read the grades carefully.

**PROVEN (but abstract, not yet on the clearing object):**
- `Metatheory/Open/PerfectZK.lean` closes the **perfect/statistical** fragment of ZK
  indistinguishability *generically*: given a perfect-ZK law `hperf : ∀ s w, view s w = sim s` (the
  real verifier view equals a witness-free simulation), it proves `view_indep_of_witness : ∀ s w₁ w₂,
  view s w₁ = view s w₂` — the verifier extracts zero information about which witness was used — with
  a real teeth/non-teeth pair. **This is a template, not instantiated on the ring-clearing transcript.**
  It **deliberately does NOT touch the computational layer** (PPT adversary, negligible advantage,
  simulator against efficient distinguishers) — that stays a parameter the metatheory carries.
- `Dregg2/Privacy.lean` — the value tier (Pedersen hiding, additively homomorphic), the graph tier
  (`unlinkable` stealth, `nullifier_hides_identity`), each as an abstract hiding **carrier** bundled
  with its computational law. Again: carriers, not a clearing-level theorem.

**BUILT (mechanism present, statistical-ZK is a tested config not a proven theorem):**
- The shielded-spend circuit proves through the **hiding** uni-STARK path (`prove_dsl_zk`,
  `HidingFriPcs`, `ZK = true` — `shielded/spend_circuit.rs`, `shielded/mod.rs`). Value, owner, key,
  Merkle path, randomness, leaf commitment live **only in the witness** under the hiding PCS. The
  circuit exposes exactly **3 PIs**: `[nullifier, merkle_root, value_binding]`, where `value_binding`
  is a *hiding* Poseidon2 commitment to the value (blinded by the note randomness).
- The ring-clearing apex exposes `[nf₀, root₀, vb₀, nf₁, root₁, vb₁]` — nothing else. All plaintext
  (values, offer/want, out_val/out_blind, range bits) is witness-only.
- The shielded pool (`pool.rs`) hides value + owner + **asset type** jointly (`HiddenAssetLeg`,
  `commit_hidden_asset`), with a transcript (`pool_message`) that binds no cleartext asset type.

**NEEDED (the crux gap — state it precisely):**

A DrEX batch is fully private only when there is a **theorem that the public transcript of the
clearing is independent of the private trades** — i.e. an observer (including the operator) learns
only "a fair, conserving, valid batch of size *n* cleared," and nothing about who / amounts /
allocations. Concretely this decomposes into three obligations, none of which exists yet at the
clearing level:

1. **State the clearing-level hiding theorem.** Instantiate PerfectZK's `view`/`sim` on the actual
   ring-clearing transcript. Prove `view_indep_of_witness` for the *real* exposed transcript: the
   public output (the proof + `[nf, root, vb]` per leg) is a simulable function of only the public
   data (the committed tree roots, the fresh-nullifier set, the batch size) — **independent of the
   private trade content** (owner, value, offer/want, allocation). **Difficulty RESEARCH** — writing
   the honest statement is the hard part (what is `view`? what does `sim` get?), and it is the
   differentiator. Depends on components 1 and 2 (the transcript must be finalized first).

2. **Discharge the per-PI leakage.** The three exposed lanes must each be shown to leak nothing:
   - `nullifier` — revealed **by design** to gate double-spend. Must reduce to the
     `nullifier_hides_identity` / `unlinkable` carrier (a nullifier is unlinkable to the holder).
     Today that is an abstract `Prop`, not tied to the deployed nullifier derivation.
   - `merkle_root` — public tree state; leaks nothing beyond the anonymity set (which is the whole
     tree). Cheap once stated.
   - `value_binding` — a hiding Poseidon2 commitment; hiding rests on the randomness + `HashCR`.
     Must be stated as a hiding property, not merely "it's a hash."
   **Difficulty M** once (1) frames it; these are reductions to named carriers.

3. **The statistical-ZK of the FRI PCS itself.** `HidingFriPcs` / `ZK = true` gives statistical
   zero-knowledge of the STARK, but this is a **tested config choice, not a proven simulator theorem**
   in the tree — and PerfectZK explicitly keeps the computational/statistical simulator as a
   *parameter*. Making "the proof reveals nothing beyond its PIs" a first-class named floor (the
   HidingFriPcs statistical-ZK obligation) — or proving it — is a heavy crypto obligation.
   **Difficulty RESEARCH.** This is the floor the whole reveal-nothing claim rests on; it should be
   NAMED and graded (statistical-ZK of the deployed hiding FRI), the same way `HashCR` and the DLog
   `binding` are named, rather than left implicit in a config flag.

**Honest one-line grade for component 3:** the clearing is proved *sound and private-by-construction*
(the plaintext never leaves the witness; only `[nf, root, vb]` is exposed), and the abstract ZK
machinery exists — but **there is no theorem yet that the clearing transcript reveals nothing about
the trades.** That theorem (statement + simulator/indistinguishability + the named statistical-ZK
floor) is the crux, and it is the single highest-value differentiator to build. Do not claim
"nobody learns what settled" as *proved* until it lands; today the honest claim is "private by
construction, with the hiding property tested at the PCS layer and the reveal-nothing theorem named."

---

## 4. Membership + nullifier in-clearing

**PROVEN.** `ShieldedClearing.lean::ShieldedLeg.refines` (from `shielded_spend_claim_refines`) — a
valid shielded-spend claim `[nullifier, merkle_root, value_binding]` refines a sound VM step:
AUTHORIZED (spends a real committed member note) + NO-DOUBLE-SPEND (fresh → joins spent set → never
re-spendable). The deployed nullifier flip (memory `project-vk-epoch-nullifier-flip`) forces
membership + freshness at the deployed descriptor (`noteSpendVmDescriptor2R24`, sorted-Merkle
accumulator, `nf ∉ pre.nullifiers` via `absent` + `aafi_insert`).

**BUILT.** The apex binds each ring leg to a real spend leaf via in-circuit `connect`
(`bind_leg_node`); a leg claiming a tuple no verifying spend backs is a `connect` conflict ⇒ UNSAT
(`mismatched_fold_does_not_bind`, `forged_spend_leg_never_mints_a_leaf`).

**NEEDED.** Bind the ring's legs to the **deployed** nullifier accumulator inside the clearing AIR.
Today each leg's `pre`/`post` is a per-leg toy `ShieldedState`; the freshness is proved against that
local state, not against the one deployed sorted-Merkle accumulator that the rest of the system
advances. The fusion at the spend-leaf is real; the *accumulator threading* — the clearing apex
consuming and advancing the single canonical nullifier root — is the weld. **Difficulty M.** Depends
on the deployed accumulator (exists) + the observer-threading residual named in the nullifier-flip
memory (item-3: `ShadowNullifierAccumulator` into `WireState`). Also open there: in-STARK
non-membership bound to the committed limb (light-client attestation).

---

## 5. Shielded SetField-attestation

**Grade: NEEDED (design).** Neither Lean spec nor circuit exists for the shielded allocation.

The goal: settle the **per-trader allocation attested-but-hidden** — prove a valid allocation
happened (each trader received exactly its cleared amount of its wanted asset) **without revealing
the allocation**. Today the clearing proves the *aggregate* is fair and conserving; the individual
trader→allocation map is not itself committed-and-hidden as a first-class object.

**NEEDED.** A shielded allocation-commitment settlement: each trader's post-batch position as a
hidden commitment, with a proof it equals `receivedAmount`/`receivedAsset` from the cleared cycle
(the fair-clearing already proves those quantities — `clearing_respects_limits`,
`cycle_individuallyRational`). Plus resolving the **SetField cohort ambiguity** (named): which
cohort a SetField write attributes to, so an allocation cannot be silently reassigned. **Difficulty
L.** Depends on 3 (the hiding property must be stated before "attested-but-hidden allocation" is
meaningful) and 4 (allocations land as note-creates against the accumulator).

---

## 6. Composition + deployed-assurance

**PROVEN.** The AIRs are STARK-sound on the real floors (`HashCR` + `Poseidon2ChipArithSound`,
BCIKS20 proved for deployed code, FRI provably ~112.6-bit — memory
`project-linking-tower-forgery-closure`). The fusion is spec-proven end-to-end
(`shielded_ring_fused_clears`), and the in-AIR conservation refines the Lean group-Pedersen
conservation (`inAir_conservation_refines_pedersen`) — the deployed field gate forces what the Lean
proves for the value-mint hazard (no toy stand-in: the `refVC` additive toy and `refTreeRoot` linear
hash are *retired* by `RealCrypto.lean`).

**BUILT.** The 2-leg apex folds and verifies green (`honest_shielded_2ring_folds_and_verifies`), and
the cleared claim round-trips.

**NEEDED / named residuals (what is NOT yet clean):**
- The N-leg apex under the **deployed VK** (composition 1 + 6): the 2-leg apex is a leaf-wrap config,
  not the deployed epoch VK. **Difficulty M→L.**
- **⚑ PQ residual (real, not just resolution).** The shielded value-**binding** today rests on DLog
  (Pedersen/Ristretto + Schnorr excess + Bulletproof range, `cell-crypto/src/value_commitment.rs`,
  `pool.rs`), which is **Shor-broken** — a genuine hole in the PQ posture, NOT covered by the PQ
  metatheory (component 2, `PQ-SHIELDED-COMMITMENT.md`). The fix is the Option-A cutover to the Poseidon2
  hash-commitment + fully-in-AIR STARK conservation (`value_binding` + the in-AIR conservation gate + the
  `VALUE_BITS` range, most of which is built), retiring DLog. The 64-bit in-AIR range is the remaining
  depth. Privacy is already quantum-safe (perfect hiding + statistical ZK) and needs no change.
- The uniform-price/optimality layer is MODEL-proved, not ledger-realized (DREGGFI-VISION §7,
  ZK-AUCTION-SUITE §8) — individual-rationality fairness IS ledger-realized; say which.

---

## Sequence — what unlocks what

```
        ┌─────────────────────────────────────────────────────────────┐
        │  Component 3: ZK / reveal-nothing theorem  (THE CRUX)        │
        │  statement → per-PI leakage → statistical-ZK FRI floor       │
        └───────────────▲─────────────────────────────▲───────────────┘
                        │ (transcript must be final)   │ (named floor)
   ┌────────────────────┴───┐                  ┌───────┴──────────────┐
   │ 1. N-leg ring AIR (M)  │                  │ 6. deployed-VK fold  │
   │    + partial-fill ≥ (M)│──── app wiring   │    + retire residuals│
   └────────────────────────┘                  └──────────────────────┘
   ┌────────────────────────┐   ┌───────────────────────┐
   │ 4. accumulator bind (M)│   │ 2. PQ value-commitment │
   │    (deployed nullifier)│   │  hash+in-AIR (M), retire│
   │                        │   │  DLog; 64-bit range(M-L)│
   └────────────────────────┘   └───────────────────────┘
                                  └── 5. shielded allocation (L, after 3+4)
```

- **1 (N-leg AIR)** unlocks a real DEX batch (not 2 legs) → app wiring. Independent of the crux.
- **4 (accumulator bind)** makes the double-spend gate deployed-real, not per-leg toy. Independent, M.
- **2 (PQ value-commitment)** is a *posture-alignment* item, NOT a faithfulness upgrade: the shielded
  value-binding is DLog (Shor-broken) today, so this retires DLog onto Poseidon2 CR + in-AIR STARK
  conservation. Most is built (`value_binding`, in-AIR conservation, `VALUE_BITS` range); the residual is
  a cutover + the 64-bit in-AIR range. The old "Ristretto EC-in-AIR" item is deleted (it entrenched DLog).
- **3 (the ZK theorem)** depends on 1+2 finalizing the transcript, but its *statement* can be drafted
  now against the current 2-leg transcript and refined. It is the differentiator and gates the honest
  "nobody learns what settled" claim.
- **5 (shielded allocation)** waits on 3+4.

---

## The single most-valuable next step

**Two, in priority order — and they are the ones the task frame calls out:**

1. **The clearing-proof ZK / reveal-nothing theorem (component 3).** This is the crux and the
   differentiator: it is the *only* thing that turns "private by construction, tested at the PCS
   layer" into "proved that the operator learns nothing about who/amounts/allocations." Concretely,
   the first move is to **write the honest statement** — instantiate `PerfectZK.view`/`sim` on the
   ring-clearing transcript `[nf, root, vb]ⁿ` + the proof, prove `view_indep_of_witness` reducing the
   exposed lanes to the named carriers (`nullifier_hides_identity`, value-binding hiding, public
   root), and **name the HidingFriPcs statistical-ZK floor** explicitly (graded, both-pole teeth),
   the way `HashCR` and DLog `binding` are named. Difficulty RESEARCH; highest strategic value.

2. **The N-leg ring-clearing AIR (component 1).** Difficulty M, no new crypto, and it unlocks a real
   DEX batch + the app wiring. It also finalizes the transcript shape that (1) must quantify over, so
   the two are complementary: build N-leg to fix the transcript, then state the ZK theorem over it.

Everything else (the PQ value-commitment cutover, 64-bit range, shielded allocation) is real work but
either a posture-alignment cutover reusing built machinery or a downstream dependent. **Note the PQ
value-commitment (component 2) is a real security residual, not a mere faithfulness upgrade** — the
shielded binding is Shor-broken today; retiring DLog is on the posture-critical path even if off the
demonstrable-batch path.

---

## Honest 4-line summary

1. **PROVEN:** the private-matching *clearing spec* is machine-checked and non-vacuous — a shielded
   ring clears conserving + fair + no-double-spend + **fused** to real hidden notes
   (`shielded_ring_clears`, `shielded_ring_fused_clears`), over real Pedersen (DLog binding) and real
   Poseidon2 (sponge CR), toys retired; the value-mint / wraparound hole is closed *in-circuit*.
2. **BUILT:** the 2-leg tight-cycle ring-clearing apex AIR runs and folds green with tested teeth
   (non-conserving, wraparound, double-spend, mis-fusion, mismatched-fold all UNSAT), proving through
   the hiding PCS with only `[nf, root, vb]` exposed and all plaintext witness-only.
3. **THE FRONTIER is the reveal-nothing property (component 3):** the clearing is private *by
   construction* but there is **no theorem yet that its transcript is independent of the trades** — no
   simulator/indistinguishability at the clearing level and no named statistical-ZK floor for the
   deployed hiding FRI. That theorem is the differentiator and does not exist today.
4. **Also NEEDED:** N-leg variable cycles + the partial-fill inequality in-AIR (M), binding legs to
   the *deployed* nullifier accumulator (M), **the PQ value-commitment cutover — the shielded binding is
   discrete-log (Shor-broken) today; retire Pedersen/Schnorr/Bulletproof onto the Poseidon2
   hash-commitment + fully-in-AIR STARK conservation (M, mostly built) + a 64-bit in-AIR range (M–L)**,
   and the shielded attested-but-hidden allocation (L). Honest posture: the 2-leg AIR and the spec are
   real; shielded *privacy* is quantum-safe (perfect hiding + statistical ZK) but shielded
   *value-binding* is NOT post-quantum (a real posture hole, `PQ-SHIELDED-COMMITMENT.md`); and the
   fully-private N-leg ZK clearing that reveals nothing is the frontier — do not overclaim either as
   proved.
