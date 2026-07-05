# Commitment / anchor waist census — "what other 31-bit waists need to expand?"

> **STATUS (regrounded):** the census's two HIGHEST waists have since been
> LIFTED. The whole-chain light-client anchor is now 8-felt
> (`SEG_ANCHOR_WIDTH = 8` / `SEG_DIGEST_WIDTH = 8`,
> `circuit-prove/src/ivc_turn_chain.rs:254,267`; `WholeChainAttestation` fields
> at `lightclient/src/lib.rs:136,139`) and the IVC attenuation-fold accumulator
> is now 8-felt (`ACCUMULATED_HASH_WIDTH = 8`, `circuit/src/ivc.rs:187`, with a
> build-time `assert_eq!(ACCUMULATED_HASH_WIDTH, 8, "the faithful floor is 8
> felts")`). Rows #1 and #2 below are now **class D (at floor)**. The live
> remainder is #3 sovereign (STAGED, still 4-felt), #4 `custom_proof_commitment`
> (4-felt, VK-affecting, deliberately deferred), cap-open, and #5 the
> identity-fold C\* question.

> The faithful floor is **8 felts / ~124-bit collision resistance**
> (`docs/FAITHFUL-COMMITMENT-LAW.md`, grounded at
> `docs/reference/faithful-commitment.md`), matching the deployed FRI ~130-bit
> soundness. A commitment narrower than that is a *waist*: a low-collision door
> under a high-soundness proof. The
> [`dont-launder-a-load-bearing-insecurity`] scar was EXACTLY a 31-bit
> commitment rationalized as "the existing scheme." This census answers the
> owner's question — after the cap-open 1-felt waist and the Custom 4-felt
> waist were found, *what else is below floor?* — by walking every
> commitment / PI / anchor column on a deployed soundness-load-bearing path
> and classifying each.

## The collision-bits table (the part everyone wants is short)

Most commitments are AT floor (8-felt) or BENIGN (below-floor but not a
soundness collision surface). The genuinely-below-floor *and*
soundness-load-bearing set is small. Verdicts:

- **A — DEPLOYED below-floor, load-bearing** → a real waist, must lift.
- **B — STAGED below-floor** → lift before it is deployed (free today).
- **C — BENIGN** → below-floor but not a soundness collision surface
  (light-client-reproducible from public data, fails-closed, off-AIR-backed,
  exact-value encoding, or deprecated/retired) → fine, reason named.
- **D — AT FLOOR (8-felt)** → the good case, confirmed.

| commitment / anchor | felts | bits (collision) | class | evidence (file:line) |
|---|---|---|---|---|
| Per-cell state commit `OLD/NEW_COMMIT` (EffectVM PI) | **8** | ~124 | **D** | `circuit/src/effect_vm/pi.rs:27,30` |
| `hash_many_8` squeeze (8 distinct felts) | **8** | ~124 | **D** | `circuit/src/poseidon2.rs:401` |
| Cap-open BEFORE/AFTER wide carriers (`wide_commit_anchors`) | **8** | ~124 | **D** (wide leg) | `node/src/turn_proving.rs:1157`; `circuit/src/effect_vm_descriptors.rs:1005` |
| `EMIT_EVENT_TOPIC_HASH` / `PAYLOAD_HASH` | **8** | ~124 | **D** | `circuit/src/effect_vm/pi.rs:574,577` |
| `custom_program_vk_hash` (8-limb of 32B VK) | **8** | ~124 | **D** | `circuit/src/effect_vm/pi.rs:289`; `circuit-prove/src/custom_proof_bind.rs:111` |
| `SCHEMA_NOTE_SPEND/CREATE/BURN` binding fields (8 limbs/32B) | **8** | ~248 raw | **D** | `circuit/src/effect_action_air.rs:639` |
| **Whole-chain anchor `genesis_root`/`final_root`** (light-client) | **8** | ~124 | **D** (LIFTED, was A) | `circuit-prove/src/ivc_turn_chain.rs` `SEG_ANCHOR_WIDTH=8`; `lightclient/src/lib.rs:136,139` |
| **Whole-chain `chain_digest` / segment `acc`** (`SEG_DIGEST_WIDTH`) | **8** | ~124 | **D** (LIFTED, was A) | `circuit-prove/src/ivc_turn_chain.rs` `SEG_DIGEST_WIDTH=8`; `lightclient/src/lib.rs:142` |
| **IVC attenuation-fold `AccumulatedHash`** (`ACCUMULATED_HASH_WIDTH`) | **8** | ~124 | **D** (LIFTED, was A) | `circuit/src/ivc.rs` `ACCUMULATED_HASH_WIDTH=8` |
| **Cap-open 1-felt V3 commit (no-rotation fallback)** | **1** | ~15 | **A** (known) | `node/src/turn_proving.rs:1162` (`wide_from_felt`) |
| **`custom_proof_commitment` (Custom proof_bind col 72)** | **4** | ~62 | **A** (known) | `circuit-prove/src/custom_proof_bind.rs:61,70` |
| `SOVEREIGN_TRANSITION_PROOF_COMMITMENT` (inner-proof PI commit) | **4** | ~62 | **B** | `circuit/src/effect_vm/pi.rs:246` |
| `SOVEREIGN_TRANSITION_PROOF_VK_HASH` (inner-proof VK) | **4** | ~62 | **B** | `circuit/src/effect_vm/pi.rs:241` |
| `SOVEREIGN_WITNESS_KEY_COMMIT` (Ed25519 owner-key digest) | 4 | ~62 | **C** | `circuit/src/effect_vm/pi.rs:224` |
| `TURN_HASH`, `EFFECTS_HASH`, `EFFECTS_HASH_GLOBAL`, `PREVIOUS_RECEIPT_HASH` | 4 | ~62 | **C** | `circuit/src/effect_vm/pi.rs:34,102,108,119` |
| 7× bilateral roots (transfer/grant/intro), `UNILATERAL_ATTESTATIONS_ROOT` | 4 | ~62 | **C** | `circuit/src/effect_vm/pi.rs:163,167,172,175,179,183,187,522` |
| `FEDERATION_ID`, `OWNER_CELL_ID` | 4 | ~62 | **C** | `circuit/src/effect_vm/pi.rs:602,608` |
| `NOTESPEND_NULLIFIER`, `NOTECREATE_COMMITMENT`, `BURN_TARGET_PI` | 1 | ~15 | **C** | `circuit/src/effect_vm/pi.rs:647,677,704` |
| `BRIDGE_MINT_VALUE_LIMBS` (4×16-bit exact value) | 4 | exact | **C** | `circuit/src/effect_vm/pi.rs:275` |
| `BRIDGE_LOCK` / `CREATE_ESCROW` value limbs (RETIRED sentinel) | 4 | n/a | **C** | `circuit/src/effect_vm/pi.rs:280,285` |
| Cap-open turn-identity pins `actor/src/dst` (`fold_bytes32`) | 1 | ~15 | **C\*** | `node/src/turn_proving.rs:1173`; `circuit/src/cap_root.rs` `fold_bytes32` |
| `cap_root` Merkle root + `CapLeaf.target`/heap roots (sorted-tree) | 1 | ~15 | **C\*** | `circuit/src/cap_root.rs`; `circuit/src/heap_root.rs` |
| `note_spending_air` legacy single-felt commit (col 5) | 1 | ~15 | **C** (deprecated) | `circuit/src/note_spending_air.rs:109`; `circuit/src/effect_action_air.rs:1267` |
| `garbled_air` 4-felt circuit-commit / output-label hash | 4 | ~62 | **C** (deprecated) | `circuit/src/garbled_air.rs:66,391` |
| `bilateral_aggregation_air` 4-felt turn/effects/receipt + roots | 4 | ~62 | **C** | `circuit/src/bilateral_aggregation_air.rs:142` (mirrors the C PI roots) |
| dregg-query MMR root (BLAKE3, off-chain index) | 32B | n/a | **C** | `dregg-query/src/mmr.rs` (not a circuit-soundness anchor) |

`C\*` = single-felt cell-IDENTITY projection. Below floor, but identity is
additionally bound by ownership / cap-membership opening, not by the
collision resistance of the fold alone — flagged for confirmation, not an
established exploit. See "the identity-fold question" below.

## The ranked answer — the real waists to lift (class A/B), beyond cap-open + Custom

The two already-known waists (cap-open 1-felt, Custom 4-felt) are being
lifted by sibling lanes. **The new findings this census surfaces are the
aggregation / IVC anchors**, which are the *top* of the trust stack: a
whole-history light client trusts these directly.

### 1. Whole-chain light-client anchor — `genesis_root`/`final_root` + `chain_digest`  ⟵ HIGHEST — **CLOSED (lifted to 8-felt)**

`lightclient::verify_history` reads `WholeChainAttestation { genesis_root,
final_root, num_turns, chain_digest }`. These come from the recursion root's
exposed segment claim `[first_old8, last_new8, count, acc_0..7]`
(`ivc_turn_chain.rs` `SEG_LAST_NEW`/`SEG_COUNT` offsets; `acc` =
`SEG_DIGEST_WIDTH`). **This waist has been lifted.** The endpoints are now
`SEG_ANCHOR_WIDTH = 8` felts (`first_old8`/`last_new8`) and the ordered-history
commitment `acc` is `SEG_DIGEST_WIDTH = 8` felts — both AT the ~124-bit floor
the *per-turn* legs meet (8-felt `OLD/NEW_COMMIT`).
`WholeChainAttestation.genesis_root`/`final_root` are typed
`[BabyBear; SEG_ANCHOR_WIDTH]` and `chain_digest` is
`[BabyBear; SEG_DIGEST_WIDTH]` (`lightclient/src/lib.rs:136,139,142`).

The original gap: this sits ABOVE every per-turn close, so a narrow anchor here
(the pre-lift ~15-bit `first_old`/`last_new` or ~62-bit `acc`) would have fooled
the whole-history attestation regardless of how faithful each turn's internal
8-felt commit is. The 8-felt twin already existed in the prover (`FinalizedTurn`
`wide_old_root8`/`wide_new_root8`, the WIDE temporal tooth
`TurnChainError::WideChainBreak`, `MissingWideAnchor` fail-closed); the lift
wired it into the **exposed claim** — `expose_claim` now emits `first_old8`/
`last_new8` (8 felts each) and the 8-felt `acc`, `WholeChainAttestation` + host
tooth compare all 8, and `Dregg2.Circuit.RecursiveAggregation` is aligned. The
recursion root op-list changed and `RecursionVk` re-emitted as part of the lift.

### 2. IVC attenuation-fold `AccumulatedHash` — **CLOSED (lifted to 8-felt)**  ⟵ HIGH

`circuit/src/ivc.rs` `ACCUMULATED_HASH_WIDTH = 8` is the delegation /
attenuation fold-chain accumulator (distinct from the whole-chain accumulator
above). **This waist has been lifted.** The width is now 8 felts, guarded by a
build-time `assert_eq!(ACCUMULATED_HASH_WIDTH, 8, "the faithful floor is 8
felts")` (`circuit/src/ivc.rs:2459`), and the doc-comments now correctly state
8 felts = ~124-bit collision resistance rather than laundering a 4-felt
(~62-bit) width as "124-bit". The lift (`ACCUMULATED_HASH_WIDTH`,
`StateTransitionAir`, `extend_accumulated_hash_wide`) re-emitted the attenuation
IVC AIR's VK and aligned its Lean twin — done in this campaign, which also made
the comments true rather than just de-laundered.

### 3. Sovereign inner-transition proof commitment + VK — 4-felt, STAGED (class B)

`SOVEREIGN_TRANSITION_PROOF_{COMMITMENT,VK_HASH}` (4-felt each) bind an inner
recursively-verified STARK whose public inputs are **adversary-chosen** — so,
like `custom_proof_commitment`, they ARE collision-relevant. Today they are
**sentinel-zero / not deployed** (`pi.rs:209`; the recursive verifier is a
follow-up), so lifting them costs nothing now. They live in the v2 PI prefix,
so widening shifts `BASE_COUNT` and cascades the `RotationLayout`/`PiV3` drift
guard + Lean layout facts — widen them 4→8 now so they never ship at 4-felt.

### The identity-fold question (`cap_root` / `fold_bytes32`, class C\*)

The cap-open turn-identity pins (`actor`/`src`/`dst`), the `cap_root` Merkle
root, and `CapLeaf.target`/heap roots are single-felt Poseidon2 projections
(~15-bit). These are cell-IDENTITY anchors, not state digests: a transfer's
`src`/`dst` and the cap membership are *additionally* bound by the
cap-membership opening (the cap-reshape crown, `verify_full_turn_bound`) and
by ownership, so a 31-bit identity collision does not by itself authorize a
forged move. They are flagged C\* — **below floor, plausibly load-bearing if
the single-felt root is ever the *sole* authority anchor for a light client**
— and warrant a dedicated confirm-or-lift pass alongside the cap-open wide
lift (the sorted-Poseidon2 root would widen to the 8-felt squeeze the same way
the state commit did). Not asserted as an exploit here; named so it is not
mistaken for settled.

## Why the rest are benign (class C, named so they are not re-flagged)

- **Light-client-reproducible (the big class).** `TURN_HASH`, `EFFECTS_HASH`,
  `EFFECTS_HASH_GLOBAL`, `PREVIOUS_RECEIPT_HASH`, the 7 bilateral roots,
  `UNILATERAL_ATTESTATIONS_ROOT`, `FEDERATION_ID`, `OWNER_CELL_ID` are
  reconstructed by the off-AIR verifier / light client from **public turn
  data** (call_forest, nonces, schemas) and PI-matched. The client holds the
  preimage and recomputes the same 4-felt projection — there is no blind
  trust, so a 4-felt collision buys nothing (the `EFFECTVM-AIR-VERIFICATION-CENSUS.md`
  benign off-AIR PI-match class). Unlike `OLD/NEW_COMMIT`, the client never
  has to identify an unknown preimage by these.
- **Off-AIR-backed digest.** `SOVEREIGN_WITNESS_KEY_COMMIT` (4-felt) is an
  Ed25519 owner-key digest whose full 256-bit binding is the off-AIR
  signature verify; widening the digest closes no gap (`pi.rs:217-222`).
- **Fails-closed cross-check welds.** `NOTESPEND_NULLIFIER`,
  `NOTECREATE_COMMITMENT`, `BURN_TARGET_PI` are single-felt **welds** whose
  full 256-bit binding lives in the `SCHEMA_NOTE_*`/`SCHEMA_BURN` binding
  proofs (8 limbs); the single felt only forbids the EffectVM from using a
  *different* value than the certified one, and a real value is ~never the
  zero sentinel (`pi.rs:642-646`).
- **Exact-value encodings, not hashes.** `BRIDGE_MINT_VALUE_LIMBS` is a
  4×16-bit little-endian decomposition of a u64 — a *faithful exact* encoding
  (64 bits, no collision), not a digest. `BRIDGE_LOCK`/`CREATE_ESCROW` limbs
  are RETIRED zero sentinels (effects deleted).
- **Deprecated / off-chain.** `note_spending_air` single-felt and
  `garbled_air` 4-felt are superseded by the schema/DSL forms (8-limb);
  `dregg-query`'s MMR is a BLAKE3 256-bit **off-chain index**, not a
  circuit-soundness anchor.

## The lift — Rust + Lean, now

Every class-A/B width lift changes a circuit surface (EffectVM descriptor PI
prefix, recursion root op-list, or an AIR column geometry) and so re-emits the
verifier key, AND requires aligning the Lean twin (the layout/aggregation
facts are emitted from Lean, law #1). That is expected and fine — the VK
re-emit is part of the lift, not a reason to defer it. The order, by
soundness-criticality:

1. ✅ **DONE — Whole-chain anchor 1/4-felt → 8-felt** (highest; the top-of-stack
   light-client trust anchor). `SEG_ANCHOR_WIDTH = 8` / `SEG_DIGEST_WIDTH = 8`,
   `expose_claim` emits `first_old8`/`last_new8` (8 felts each),
   `WholeChainAttestation` + host tooth widened to 8,
   `Dregg2.Circuit.RecursiveAggregation` aligned. The prover's `wide_*_root8` was
   wired into the exposed claim; `RecursionVk` re-emitted.
2. ✅ **DONE — IVC attenuation-fold `AccumulatedHash` 4-felt → 8-felt** —
   `ACCUMULATED_HASH_WIDTH = 8` across `circuit/src/ivc.rs` +
   `StateTransitionAir`, Lean IVC twin aligned, build-time floor assert added.
3. **Sovereign transition-proof commit+VK 4-felt → 8-felt** (staged today, so
   free to widen) — `SOVEREIGN_TRANSITION_PROOF_{COMMITMENT,VK_HASH}_LEN` 4→8;
   cascades `BASE_COUNT` + the `RotationLayout`/`PiV3` drift guard.
4. **Cap-open 1-felt → 8-felt** + **Custom `proof_commitment` 4-felt → 8-felt**
   (the two already-known waists, owned by sibling lanes).
5. **Identity-fold / `cap_root` confirm-or-lift** (C\*) — widen the
   sorted-Poseidon2 root squeeze the same way the state commit did.

Lifting to 8-felt also makes the previously-laundering doc-comments TRUE
(8-felt genuinely is ~124-bit), retiring the "4-felt = 124-bit collision"
relabeling that was the scar.
