# Crypto-Hypothesis Ledger — every load-bearing named cryptographic assumption on the verified surface

Status: 2026-06-08. Owner of this pass: `crypto-ledger` agent (task #97).
Bar: l4v. `#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`; NO `sorry` / `:= True` / `native_decide`.

This ledger inventories EVERY named cryptographic hypothesis the verified Lean tower rests on, and for
each classifies it as:

- **DISCHARGEABLE** — a named hypothesis PROVEN by a real reduction against a deeper carrier or a real
  impl/structural fact (e.g. the sponge CR reduced to the permutation; commitment binding reduced to
  the hash; the threshold gate reduced to the SNARK's weighted-sum row). A discharge is a REAL
  reduction, never a relabel.
- **IRREDUCIBLE PRIMITIVE** — a standard cryptographic assumption named honestly: curve/pairing math,
  or the collision-resistance / unforgeability of an underlying hash/signature. These are NOT faked and
  NOT `:= True`; they are the genuine bottom of the trust stack, carried as explicit `Prop` hypotheses
  so the trust boundary is visible (the `PortalFloor` discipline: carrier named, `*_sound` takes it as
  an explicit hypothesis).

The architecture is uniformly: **every hash-injectivity / commitment-binding portal is DISCHARGEABLE
down to a small set of IRREDUCIBLE primitives.** No load-bearing hypothesis is `:= True`; each toy
`Reference` carrier is the GENUINE soundness Prop over a provably-injective stand-in (HOLDS) and is
provably FALSE on a broken oracle (the `Forge`/`Collide` witnesses) — i.e. non-vacuous in both
directions.

---

## §0 — The IRREDUCIBLE PRIMITIVE floor (the honest bottom — 8 + 3 named assumptions)

These are the genuine cryptographic assumptions. Everything else reduces to them. They live as `Prop`
carriers in `Dregg2/Crypto/PortalFloor.lean` (the 8 post-cutover §8 TCB portals) and
`Dregg2/Crypto/BlsThreshold.lean` (the 3 federation pairing primitives, new this pass).

| # | Primitive | Carrier (Lean) | Assumption | File:line |
|---|-----------|----------------|------------|-----------|
| 1 | ed25519 EUF-CMA | `SignatureKernel.unforgeable` | signature unforgeability (Edwards-curve DLog) | `PortalFloor.lean:47` |
| 2 | STARK/FRI extractability | `VerifierKernel.extractable` | FRI proximity + Fiat-Shamir soundness | `PortalFloor.lean:77` |
| 3 | Pedersen/DLog binding | `PedersenKernel.binding` | discrete-log hardness | `PortalFloor.lean:110` |
| 4 | Poseidon2 CR | `Poseidon2Kernel.collisionHard` | collision-resistance | `PortalFloor.lean:149` |
| 5 | BLAKE3 CR + preimage | `Blake3Kernel.collisionHard` | collision + preimage resistance | `PortalFloor.lean:182` |
| 6 | Nullifier unlinkability | `NullifierKernel.unlinkable` | anonymity (determinism is PROVED, free) | `PortalFloor.lean:210` |
| 7 | AEAD + X25519 authenticity | `SealKernel.authentic` | ChaCha20-Poly1305 / X25519 authenticity | `PortalFloor.lean:236` |
| 8 | HMAC-SHA256 unforgeability | `MacKernelE.unforgeable` | keyed-hash EUF-CMA | `PortalFloor.lean:270` |
| 9 | KZG10 evaluation binding | `KzgBinding` (named obligation) | `q`-SDH / SXDH over BLS12-381 pairing | `BlsThreshold.lean:§2` |
| 10 | BLS aggregate unforgeability | `BlsAggUnforgeable` (named obligation) | co-CDH over BLS12-381 pairing | `BlsThreshold.lean:§2` |
| 11 | Weighted-threshold poly-IOP | `SnarkPolyIOP` (named obligation) | poly-IOP + FS soundness (⊇ #9) | `BlsThreshold.lean:§2` |

Non-vacuity for #1–#8 is machine-checked in `PortalFloor.lean §9/§9b`: each carrier HOLDS for an
injective/echo reference oracle AND is provably FALSE for a forgeable/colliding oracle
(`instSignatureForge_not_unforgeable`, `instPoseidon2Collide_not_collisionHard`, …). Pinned by
`#assert_axioms` (`PortalFloor.lean:532–545`). Real instances are the Rust `@[extern]` oracles
(`dregg_ed25519_verify`, `dregg_stark_verify`, `dregg_poseidon2_hash`, `dregg_blake3_hash`,
`dregg_aead_open`, `dregg_hmac_sha256`, `dregg_pedersen_commit`, `dregg_nullifier_derive`), which leave
the carriers as the standing obligation.

---

## §1 — The Poseidon2 sponge CR & the whole commitment tower (ALL DISCHARGEABLE to primitive #4)

The single most load-bearing assumption in the system is **Poseidon2 sponge collision-resistance**,
and the entire full-state commitment / system-roots tower reduces to it.

### `Poseidon2SpongeCR` — DISCHARGED against the real p3-poseidon2-circuit-air (task #13)

`Dregg2/Circuit/Poseidon2Binding.lean:169`
```lean
def Poseidon2SpongeCR (sponge : List ℤ → ℤ) : Prop := ∀ xs ys, sponge xs = sponge ys → xs = ys
```

**Is the SPONGE discharged (not just the permutation #13)?** YES. The bridge is pinned to the REAL
sponge construction, not an abstract injective hash:

- `Poseidon2RealParams` + `babyBearD4W16` (`Poseidon2Binding.lean:91,131`) record the EXACT real
  permutation: BabyBear (`p = 2^31−2^27+1`), width 16, d=4, sbox_degree 7, 8 full + 13 partial rounds,
  capacity_ext 2 / rate_ext 2 — mirroring `p3 Poseidon2Config::BABY_BEAR_D4_W16` one-for-one. The
  `#guard`s at `Poseidon2Binding.lean:144–154` RE-DERIVE `rate_ext`/`capacity_ext`/`width_ext` with the
  SAME `const fn` formulas as the Rust, so any drift on EITHER side breaks the build.
- The sponge MODE is named: `PaddingFreeSponge`, absorb rate_ext-chunks, squeeze rate_ext (overwrite),
  matching `circuit/src/ops/hash.rs` `add_hash_slice` (`Poseidon2Binding.lean:80`).
- `Poseidon2RealizedSponge` (`Poseidon2Binding.lean:175`) bundles `params_are_real : params =
  babyBearD4W16` WITH `spongeCR`, so the named assumption documents EXACTLY which efficient
  Poseidon2 it bridges to — the real fast circuit's sponge, not "some injective sponge".

So `Poseidon2SpongeCR` IS the CR of the real BabyBear-W16 PaddingFreeSponge. Classification:
**IRREDUCIBLE PRIMITIVE** at the sponge level (= primitive #4, lifted from 2-to-1 compression to the
list-sponge); the permutation/parameter correspondence to the real AIR is discharged structurally
(re-derived dims + literal constants).

The in-circuit witness `Poseidon2Emit.spongeCompressN` is proved FAITHFUL to the emitted `merkle_hash`
chain by `emit_faithful_poseidon2_compress` (`Poseidon2Binding.lean:18,200`).

### The three injectivity portals — ALL DISCHARGED from `Poseidon2SpongeCR`

`StateCommit.lean` parameterizes the whole per-effect circuit-soundness tower over three portals; all
three discharge from the SINGLE sponge CR (`Poseidon2Binding.lean §2–§3`):

| Portal | Discharge | Proof |
|--------|-----------|-------|
| `compressNInjective compressN` (frame digest) | LITERALLY `Poseidon2SpongeCR compressN` (`Iff.rfl`) | `compressNInjective_iff_poseidon2CR` (`:194`) |
| `cellLeafInjective CH` (per-cell leaf) | CR ∘ injective-encoder (`LeafRealization`) | `cellLeafInjective_of_realization` (`:233`) |
| `logHashInjective LH` (receipt-chain) | CR ∘ injective-encoder (`LogRealization`) | `logHashInjective_of_realization` (`:256`) |

The encoder-injectivity in the leaf/log case is a STRUCTURAL field (a canonical serialization is
provably injective — NOT a crypto assumption); the `Reference` section PROVES a genuine injective
`Value → ℕ` encoder by mutual structural induction (`encV_inj`/`encFields_inj`, `:328–366`), so the
bundle fires on a real instance. The sole crypto carrier is the shared `spongeCR`.

### `compressInjective` (2-to-1) — IRREDUCIBLE PRIMITIVE #4

`StateCommit.lean:207` `compressInjective : ∀ a b c d, h a b = h c d → a=c ∧ b=d` — the 2-to-1 node
CR. Used by `recStateCommit_binds` (`StateCommit.lean:535`) to make the full-state root an injective
commitment to (live-cell digest, rest hash). Same primitive #4, stated for the 2-input compression.

### system_roots / listDigest / keyedDigest — DISCHARGEABLE to `compressNInjective` (= #4)

- `ListCommit.lean` `ListDigestBindsList` (`:46`): equal list digests ⇒ equal lists, from
  `compressNInjective cN` + `listLeafInjective LE` (injective leaf encoder, structural). The
  `Reference` exhibits a concrete injective Horner-fold leaf encoder (`:58`).
- `KeyedCommit.lean` `KeyedDigestBindsKeys` (`:36`): the keyed (label) digest binds keys, same proof,
  "zero new crypto beyond `compressNInjective`" (`:10`).
- `Exec/SystemRoots.lean`, `Exec/RecordCommit.lean`, `Exec/FieldsMap.lean` consume these for the
  `system_roots` sub-block (sturdyref_root / seal columns), so the system-roots binding is the SAME
  primitive #4 chained.

**Verdict:** the ENTIRE commitment / state-root / system-roots / list-digest tower is DISCHARGEABLE to
the single IRREDUCIBLE PRIMITIVE #4 (Poseidon2 CR), which is itself pinned to the real circuit AIR.

---

## §2 — CapTP handoff signature-soundness (DISCHARGEABLE to primitive #1, ed25519 EUF-CMA)

The CapTP capability-handoff / authorization path routes through `SignatureKernel` (primitive #1):

`Dregg2/Exec/FullForestAuthPortal.lean` — ONE soundness portal over the 10-variant `Authorization`,
each arm spelled out in a concrete §8 oracle:

| Arm | Crypto leg | Primitive |
|-----|-----------|-----------|
| `.signature` / `.bearer` / `.stealth` | `SignatureKernel.sigVerify` | #1 ed25519 |
| `.capTpDelivered` | `SignatureKernel.sigVerify` ×2 (introducer + sender) | #1 ed25519 |
| `.proof` / `.custom` | `VerifierKernel.verify` (STARK) | #2 |
| `.token` | `MacKernelE.verifyTag` (HMAC macaroon) | #8 |
| `.unchecked` | fail-closed | — |
| `.breadstuff` | pure-predicate | — |

The instance's `soundness` Prop is the CONJUNCTION of the three genuine §8 carriers the reachable arms
consume (ed25519 `unforgeable` ∧ STARK `extractable` ∧ HMAC `unforgeable`) — NEVER `True`
(`FullForestAuthPortal.lean:26`). Each per-variant theorem takes the relevant carrier as an EXPLICIT
hypothesis (`signature_arm_sound (hunf : unforgeable) … : accept → Signed pk m`). The consumer
discharges `unforgeable` with the PROVED reference theorem `instSignatureKernel_unforgeable`
(`PortalFloor.lean:312`), not `trivial`.

The swiss/sturdyref handoff witnesses (`ValidateHandoffWitness.lean`, `SwissHandoffWitness.lean`) bind
their handoff state through `compressNInjective` / `logHashInjective` (= primitive #4), so the WITNESS
binding is CR; the AUTHENTICITY of the handoff (who may hand off) is the ed25519 leg above.

**Verdict:** CapTP handoff signature-soundness is DISCHARGEABLE to IRREDUCIBLE PRIMITIVE #1 (ed25519
EUF-CMA), consumed as an explicit carrier, never faked.

### §2a — The ed25519 EUF-CMA reduction made EXPLICIT (`Dregg2/Crypto/Ed25519Reduction.lean`)

`PortalFloor §1` unpacks the carrier in the SOUNDNESS direction (`accept ⇒ Signed`). This pass closes
the OTHER half — the explicit *reduction* the bar demands: **protocol-forgery ⇒ signature-forgery**.
The EUF-CMA game is named as a first-class predicate so a protocol break PRODUCES a concrete
cryptographic break (not just "carrier ⇒ safe").

- **IRREDUCIBLE PRIMITIVE.** `Ed25519EufCma K := ∀ pk m s, ¬ SigForgery K pk m s`, where
  `SigForgery K pk m s := K.sigVerify pk m s = true ∧ ¬ K.Signed pk m` (`Ed25519Reduction.lean §1`).
  This is the EUF-CMA assumption stated as the negation of the adversary's win condition — primitive #1
  (Edwards-curve / Curve25519 DLog), named honestly. `eufCma_iff_sound` proves it is DEFINITIONALLY the
  same content as `sigVerify_sound` (no new assumption — a sharper FRAMING), and `eufCma_of_unforgeable`
  lets any consumer holding `K.unforgeable` obtain it.

- **REAL REDUCTION (proven, no fresh axiom).** ONE reduction shape covers all THREE ed25519-backed
  call paths the auditor named — `protocol_forgery_to_sig_forgery` (`§6`) + the per-surface forms:
  | Surface | Path | Reduction theorem |
  |---------|------|-------------------|
  | handoff unforgeability | `Exec/CapTPHandoffSound.validateHandoff2` §1 leg | `handoff_forgery_to_sig_forgery` (`§3`) |
  | blocklace insert (A1) | `finality.rs` insert-time `verify_block_signature` | `block_forgery_to_sig_forgery` (`§4`) |
  | agent `Authorization` | `FullForestAuthPortal` `.signature`/`.bearer`/`.stealth` arm | `auth_forgery_to_sig_forgery` (`§5`) |

  Each takes a SUCCESSFUL protocol forgery (validating handoff / inserted block / authorized turn whose
  key never signed) and constructs an explicit `SigForgery` — hence a break of `Ed25519EufCma`.
  `eufCma_repels_all_surfaces` (`§6`) is the contrapositive: under the named primitive, NONE of the
  three surfaces admits a forgery. This is what newly TIES the blocklace `signed : Bool` carrier
  (previously an uninterpreted §8 obligation, `Blocklace.lean:19`) to primitive #1 — the
  byzantine-repelling DAG facts assumed honest signatures; this reduction is WHY that assumption is
  sound (an impersonating block ⇒ an ed25519 forgery).

- **Non-vacuity teeth (BOTH directions, `§7`).** On the honest reference oracle `ref_eufCma` HOLDS
  (so the soundness keystones fire — `ref_no_forged_handoff`). On the forgeable accept-everything
  oracle (`PortalFloor.instSignatureForge`), `forge_not_eufCma` proves `Ed25519EufCma` is FALSE AND
  `forge_{handoff,block,auth}_forgery` exhibit CONCRETE protocol forgeries on each surface — strip the
  carrier and the protocol concretely breaks, proving the reduction is not a vacuous relabel.

All keystones `#print axioms`-clean: `protocol_forgery_to_sig_forgery` / `eufCma_repels_all_surfaces`
/ the three per-surface reductions / `forge_*` depend on NO axioms; `eufCma_of_unforgeable` /
`ref_eufCma` ⊆ `{propext, Classical.choice, Quot.sound}`. No `sorry` / `:= True` / `native_decide`.

**Distinction (the bar's ask):** `Ed25519EufCma` is an IRREDUCIBLE PRIMITIVE (curve assumption, named
not faked). `protocol_forgery_to_sig_forgery` is a REAL REDUCTION (a proof transporting protocol
acceptance into a fresh signature forgery), not a relabel — it introduces no axiom and is refuted on
the broken oracle.

---

## §3 — Macaroon / credential HMAC (DISCHARGEABLE to primitive #8, HMAC unforgeability)

`Dregg2/Authority/CaveatChain.lean` — the macaroon as a real HMAC-authenticated append-only caveat
chain. `MacKernel.unforgeable` (`:87`) is the carrier; `chain_unforgeable` (`:392`) is THE
de-vacuified theorem: given the §8 EUF-CMA carrier, a forged chain implies forging an HMAC tag under
the chaining key. The toy collapsing kernel makes `unforgeable` provably FALSE
(`Demo.collapse_not_unforgeable`) — refutes, not papers over. Same primitive as `MacKernelE`
(`PortalFloor.lean:270`, primitive #8) and the `.token` arm of §2.

**Verdict:** DISCHARGEABLE to IRREDUCIBLE PRIMITIVE #8 (HMAC-SHA256 unforgeability).

---

## §4 — Threshold decryption share-MAC (DISCHARGEABLE to a named BLAKE3-PRF carrier)

`Dregg2/Distributed/ThresholdDecrypt.lean` — the t-of-n decryption (Shamir/GF(256)). The Shamir
algebra (reconstruction `shamir_any_t_reconstruct`, secrecy `shamir_below_t_undetermined`, the combine
gate) is FULLY PROVED (no crypto). The ONLY crypto residue is the share-MAC: `Blake3Prf` (`:295`) is
the named carrier (BLAKE3 keyed = secure MAC), and `share_mac_detects_tamper` (`:302`) is the genuine
reduction (tampered share passing MAC ⇒ contradiction with `Blake3Prf`), NOT faked.

**Verdict:** Shamir algebra fully PROVED; share-integrity DISCHARGEABLE to `Blake3Prf` (a keyed-MAC
specialization of primitive #5).

---

## §5 — BLS12-381 / KZG federation aggregation (NEW this pass — `Dregg2/Crypto/BlsThreshold.lean`)

This was the ONE genuinely-uncovered crypto surface (task #92): `federation/src/threshold.rs` + the
`hints` crate wrap a BLS12-381 + KZG **weighted-threshold signature** — a constant-size aggregate
quorum cert. No Lean model existed. This pass adds a faithful model + reduction.

`hints::verify_aggregate` (`hints/src/lib.rs:208`) is a THREE-GATE conjunction; the module mirrors it
gate for gate (`ThresholdCert.accepts`, `BlsThreshold.lean §3`):

| Gate | Rust | Lean | Classification |
|------|------|------|----------------|
| 1. threshold | `agg_weight < threshold ⇒ Err` (`lib.rs:210`) | `aggWeight ≥ threshold` | **DISCHARGEABLE** — pure `Nat`/`Finset` arithmetic |
| 2. SNARK | `verify_proof` poly-IOP (`verifier.rs:126`) | `SnarkOk` / `SnarkContract` | reduces to `KzgBinding` (#9) via `SnarkPolyIOP` (#11) |
| 3. final BLS | `e(apk,H(m)) = e(g₀,σ')` (`lib.rs:228`) | `BlsAggregateOk` / per-member `SignedBy` | **IRREDUCIBLE** `BlsAggUnforgeable` (#10) |

The DISCHARGEABLE content (proved, no crypto) is the SNARK's *combinatorial heart* — the `b∈{0,1}^n`
boolean row + the weighted-sum row (`verifier.rs:160,173`), modelled as `Finset` selector arithmetic:

- `quorum_weight_suffices` (`:§3b`) — accept + `SnarkContract.aggWeight_eq` (the weighted-sum row
  binding `aggWeight = Σ_{i∈selected} w_i` via KZG) ⇒ the HONEST selected weight reaches the threshold.
  This is what makes the threshold gate a statement about the REAL committee weight, not a forgeable
  scalar.
- **HEADLINE `accepting_cert_has_quorum`** (`:§3b`) — accept (3 gates) + the SNARK carrier discharged
  into `SnarkContract` + the BLS carrier discharged into per-member `SignedBy` ⇒ `∃ S ⊆ members,
  selectedWeight S ≥ threshold ∧ selectedWeight S ≤ totalWeight ∧ ∀ i∈S, SignedBy i m`. The
  quorum-cert SOUNDNESS, reduced to the 3 named pairing primitives.
- **ANTI-GHOST `subquorum_cannot_accept`** (`:§3c`) — a sub-threshold selected weight ⇒ ¬accept, GIVEN
  the SNARK binding. Proves the threshold gate is non-vacuous: stripping the SNARK binding is exactly
  what would let a sub-quorum forge a cert.

Non-vacuity: `SignedBy` is a GENUINE per-member `Prop` field of `Committee` (NOT `True`); the reference
`fed4.SignedBy i m := i ≤ 2` makes `nonsigner_breaks_bls` (`:§4`) provably FALSE on a non-signer. The
equal-weight `#guard`s (`:§4b`) pin the count semantics against `threshold.rs`'s equal-weight wrapper.

The IRREDUCIBLE primitives #9/#10/#11 are named curve/pairing assumptions (KZG `q`-SDH binding, BLS
co-CDH unforgeability, poly-IOP soundness) — discharged into the `SnarkContract` / `SignedBy`
hypotheses, the same `PortalFloor` discipline. Pinned by `#assert_axioms`
(`BlsThreshold.lean:§5`): all keystones ⊆ `{propext, Classical.choice, Quot.sound}`.

**Verdict:** the federation quorum-cert is now MODELLED: threshold/selector arithmetic PROVED;
soundness DISCHARGEABLE to 3 honestly-named pairing primitives. The remaining federation residual
(task #92) is the checkpoint-prune safety + wiring this carrier into the consensus cert path.

---

## §6 — Discharge worklist, ordered by leverage

Everything load-bearing is already discharged to the §0 floor. The remaining work is depth/breadth, not
correctness gaps. Ordered by leverage:

1. **[HIGHEST] Wire the BLS quorum-cert carrier into the consensus cert path** (task #92 residual). The
   `BlsThreshold` reduction exists; the federation `Stingray`/`EpochReconfig` cert-verification should
   consume `accepting_cert_has_quorum` so a verified epoch handoff inherits "a genuine weighted quorum
   signed". Plus the checkpoint-prune safety lemma. Leverage: closes the last uncovered consensus-crypto
   surface end-to-end.

2. **[HIGH] Real-impl differential for the BLS path.** Add `federation/src/threshold_diff.rs` (sibling
   to `threshold_decrypt_diff.rs`) transcribing the `BlsThreshold` selector/weight semantics and
   asserting agreement with the real `hints::verify_aggregate` on test vectors — the differential
   discipline that welds the Lean model to what Rust computes. (Rust side; note for SWAP/apps owner.)

3. **[MEDIUM] Tighten the leaf/log encoder realizations to the REAL serialization.** `LeafRealization`
   / `LogRealization` carry the encoder as a structural field with a PROVED toy instance. The real
   discharge pins `encodeLeaf` / `encodeLog` to the actual byte serialization the circuit absorbs
   (the `add_hash_slice` input layout), making the structural field a re-derivation of the real wire
   format rather than a canonical stand-in. Leverage: removes the last abstraction in the §1 tower.

4. **[MEDIUM] KZG binding → SXDH/`q`-SDH reduction depth.** `KzgBinding`/`SnarkPolyIOP` are named as
   the poly-IOP soundness obligation. A deeper discharge would model the KZG `verify_opening` pairing
   equation (`verifier.rs:39`) and reduce binding to the `q`-SDH game (the CryptHOL/UCBridge route, cf.
   `Crypto/UCBridge.lean`'s DLog→binding asymptotic). Leverage: turns #9/#11 from named to
   game-reduced, matching the Pedersen UC treatment.

5. **[LOW] Nullifier unlinkability (#6) as a game.** Currently determinism is PROVED and `unlinkable`
   is the named anonymity carrier. A statistical-unlinkability game would deepen it; low leverage (no
   downstream soundness theorem consumes anonymity, only privacy).

6. **[LOW] Replace the toy `Reference` CR sponge with a verified Poseidon2 permutation eval.** The
   ultimate discharge of primitive #4 is a Lean evaluation of the BabyBear-W16 permutation proven equal
   to the Rust round function. Very high effort, standard-assumption leverage only (CR of an ideal
   permutation remains assumed regardless). Defer — this is the irreducible bottom.

---

## §7 — Honesty notes (the bar)

- **No `:= True` load-bearing carrier remains.** Verified by `PortalFloor.lean §9b` (every carrier
  FALSE on a broken oracle) and the new `BlsThreshold` `nonsigner_breaks_bls` / `subQuorum_rejected`.
- **A discharge is a reduction, not a relabel.** `compressNInjective_iff_poseidon2CR` is `Iff.rfl`
  (the frame portal IS the sponge CR — definitional, the strongest discharge); the leaf/log/list/keyed
  discharges COMPOSE CR with a PROVED injective encoder; the BLS threshold discharge COMPOSES the SNARK
  weighted-sum binding with `Finset` arithmetic. None introduce a fresh axiom.
- **The IRREDUCIBLE floor is named, not hidden.** 8 `@[extern]` portals + 3 pairing primitives, each a
  `Prop` carrier passed as an explicit hypothesis to its `*_sound` theorem. The trust boundary is the
  carrier set, machine-checked by `#assert_axioms` across every file.

## §8 — Build evidence (this pass)

- `lake build Dregg2.Crypto.BlsThreshold` → `Build completed successfully (2944 jobs)`.
- `lake build Dregg2.Crypto.BlsThreshold Dregg2.Crypto.PortalFloor Dregg2.Circuit.Poseidon2Binding` →
  `Build completed successfully (2968 jobs)`.
- `#print axioms` on the BLS keystones: `accepting_cert_has_quorum`, `quorum_weight_suffices`,
  `subquorum_cannot_accept`, `Reference.passingCert_has_quorum`, `Reference.nonsigner_breaks_bls` — all
  ⊆ `{propext, Classical.choice, Quot.sound}` (no `sorryAx`).
- Pre-existing UNRELATED breakage noted, NOT in this surface: `Dregg2/Intent/SealedAuction.lean`
  (`unexpected token 'omit'`, an apps-workflow file, clean working tree @ `559a7678e`) — fails the full
  `Dregg2` root build independently of this change. Flagged for the apps owner (task #95).
