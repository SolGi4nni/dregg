# DESIGN — the Bazaar apex: v4 semantic legs on the FWS1 substrate + the four halls

**Design lane D2, 2026-07-23** (`docs/SPRINT-poster-honesty-closure-2026-07-23.md` §DESIGN WAVE,
§Campaign C5). Design + additive Lean law modules only; NO deployed descriptor / VK / wire / Rust
change from this lane. Companion: `docs/DESIGN-shielded-dark-value-campaign.md` (`7fbef7341b`) owns
the C4 routing plan and the two ember decisions (#17 posture, VK timing) — this doc does not fork
them. Ledger of record: `docs/deos/THE-DARK-BAZAAR.md` (re-grounded 07-22).

**Substrate, said out loud (law #1):** every relation this design names is Lean-authored AIR
(DescriptorIR2 through the FWS1 emit path — `Emit/ShieldedWholeNoteSwapSubstrateDescriptor.lean` is
the working precedent). `shielded_exact_apex_v4.rs` is ABI/transcript only ("transcript data, never
proof authority"); it stays that way. Anything that decides value is authored in Lean and emitted.

---

## 0. Ground truth at HEAD (what the apex already stands on)

| banked object | what it is | what it is NOT |
|---|---|---|
| **FWS1** `shielded-whole-note-swap-substrate-v1` (`f540ed95a1`; 15,611 cols, 100 PIs, no clear value/asset lane) | one selected hidden opening supplies nullifier + 16-lane wide binding + fixed 2-in/2-out whole-note swap + FXO4 output root (derived, never caller-supplied) + depth-32 AAFI exact transition, under HidingFRI | not settlement authority; omits 19 Dark-AMM + 27 ring lanes + FXC4 rule; four witness welds absent (membership, spend authority, counterparty provenance, outer transition) |
| **v4 boundary** `circuit-prove/src/shielded_exact_apex_v4.rs` | the 100-PI ABI (no clear value/asset), FNI4/FNS4/FXC4/FXA4 domains, the exact 146-lane FXC4 preimage + `PreparedShieldedConsequenceV4` non-divergence constructor | proof acceptance; the FXC4 root is Rust transcript assembly, not an in-AIR recompute |
| **C5 wound + fixes** `Dregg2/Circuit/ShieldedWideJoinPin.lean` (`2ca3ca47f7`) | the narrow-join decouple, the launder, Fix A (shared witness), Fix B (wide join under CR), the cross-scheme obligation — as theorems | instantiated on the real carrier (closed THIS LANE, §1-leg-1) |
| **consequence plane** `Market/PrivateClearingGameConsequence.lean`, `Market/DarkBazaarConsequenceOutbox.lean`, the durable private worker (`cd3ea449b0`) | lossless-tuple replay identity, one-shot dispatch, prepare-first outbox, crash recovery by observation | aware of v4 (they consume a settlement; the apex must PRODUCE one) |
| **acceptance-token custody** (`4272ac0e8` + `c4d11dc89`) | non-`Clone` v3 acceptance token binding the exact 76-lane statement + carrier digest inside the `SignedTurn` | committee/finalizer registration; single-verifier, not signer-independent |
| **dealerless path** FHTRI005 (`3118f74a4`) | typed threshold-BFV ceremony to `AwaitingCrossTermProvider`; FHTRI004 one-use tombstones | a live malicious/PQ cross-term provider; authenticated q0 broadcast + same-opening ceremony authority |
| **exact-v3 reality** (HORIZONLOG 07-22) | anti-double-spend/receipt foundation; 76 PIs expose nullifier/value/asset/root/count/outer; value-zero executor slice | dark value — "do not promote this into dark value" |

The Bazaar doc §3.4 lists the six house-blind requirements. This design decomposes them into
**five legs on one shared witness** — the unit of work below.

---

## 1. The apex, decomposed: five legs on ONE witness

The apex relation = FWS1's one-opening architecture EXTENDED in place, never a second proof glued
on. Every leg is a constraint block over the SAME hidden opening cell — that architecture is
literally Fix A (`Market.WideCarrierSameOpening.fws1_one_opening_is_fix_a`), and gluing a leg on as
a sidecar proof is exactly how the C5 wound was made. One relation, one witness, more constraint
blocks per stage.

### Leg 1 — SAME-OPENING (C5), now instantiated on the real carrier · **Lean landed this lane**

`metatheory/Market/WideCarrierSameOpening.lean` (NEW, rooted in `Market.lean`,
`#assert_all_clean` 16 keystones, non-vacuous `#guard`s) instantiates `ShieldedWideJoinPin` on the
deployed `wide_value_binding.rs` shapes — and SHARPENS the wound's price:

- **The collision is FREE, not birthday.** The legacy squeeze is
  `hash_fact(value mod p, [asset mod p, randomness, 0])` — it reduces mod BabyBear `p` BEFORE
  hashing, so `v` and `v + p` present *literally identical* hash inputs
  (`legacy_input_aliases`; `#guard` on concrete numbers). The "~2^15.5 birthday / ~2^31 chosen"
  framing over-priced the attack: ANY hash, zero cost, no CR break. The landed abstract falsifier
  fires at the deployed squeeze with a constructive `⟨0,0⟩/⟨p,0⟩` collision
  (`deployed_squeeze_join_decouples`, `deployed_dark_value_decouples_free`).
- **Fix B's floor decomposes: ONE named CR floor, the rest proved.** Injectivity of the 16-lane
  wide image splits into limb-decomposition injectivity on `u64` (`limbs_recompose`/`limbs_inj` —
  PROVED, the arithmetic the AIR's bit gates enforce) + assembly injectivity over the exact
  `wide_input_columns` lanes (`spongeInput_faithful` — PROVED, structural) + one named
  `node8`-under-`DOMAIN_A` CR floor (`SpongeCROnCarrier`). Only ONE floor even though the carrier
  publishes two sponges: both absorb the same payload
  (`real_wide_join_forces_same_opening` consults `laneA` alone). The closing theorem:
  `real_wide_join_rejects_the_free_alias` — the very pair the squeeze hands over free is separated
  by the wide join.
- **Fix A = FWS1's architecture**, dispatched THROUGH the landed abstract theorem, not re-proved.

**Design consequence for v4:** the apex takes Fix A (one opening cell feeds carrier hash, swap
rule, conservation, FXC4 lanes) — FWS1 already has this shape. Fix B remains the join discipline
for any residual TWO-proof seam (the transitional ring↔apex composition, below): the join key is
the 16 wide lanes, never the legacy felt. `RING_LEG_CLAIM_LEN = 3`'s one-felt `value_binding` slot
ceases to be the value law; the legacy felt survives only as a non-authoritative compatibility
lane inside the carrier (where the AIR recomputes it from the same limbs — internally consistent,
never a join key). Retirement of `legacy_binding` as a join = campaign C5's shipped line.

### Leg 2 — CONSEQUENCE (FXC4: the 19+27 lanes and the pinned rule) · **binding law landed this lane**

The apex must prove the complete Dark-AMM (19 lanes) + ring (27 lanes) consequence obeys the
pinned FXC4 rule, over the same witness. Two halves:

- **The binding half (SPEC, landed):** `metatheory/Market/Fxc4ConsequenceBinding.lean` (NEW,
  rooted, 9 keystones) proves the exact deployed 146-lane `canonical_fxc4_preimage` layout is
  LOSSLESS (`encode_binds`, pure `List.append_inj` over the pinned widths — no hash) and states
  the leg's law under one named `node8` CR floor: `consequence_root_binds_all_legs` — a shared
  consequence root forces every leg equal — with substitution teeth in the
  `substituted_*_cannot_dispatch` register (Dark-AMM surface, ring surface, selected leg, wide
  binding, output root). This is the good felt-width shape: 8 lanes over a lossless preimage —
  the structural opposite of the `legacy_binding` squeeze.
- **The semantic half (AUTHORING, the campaign's work):** today the FXC4 root is Rust transcript
  assembly; FWS1's PI lanes 68–75 carry the *whole-note* consequence (FWS1 domain), not FXC4. The
  apex relation must (i) RECOMPUTE the FXC4 root in-AIR over the shared witness (the
  `Fxc4ConsequenceBinding` law is the spec that recompute refines; FWS1's derived-output-root
  discipline is the precedent — no caller-supplied root), and (ii) CONSTRAIN the 19+27 lanes to
  the pinned rule: the Dark-AMM transition valid (constant-product over the hidden reserves) and
  the ring clearing valid (the `shielded_ring_clearing_air.rs` semantics, whose Lean model is
  `LedgerRealizationExt.shielded_ring_fused_clears` / `Market.ShieldedRingEndpointDescriptor`).
  Selectors (`RULE_ID`, ring length, leg) stay code-owned — bound in the preimage (the teeth
  above), pinned as constants in the AIR.

**Transitional composition, honestly named:** until the AMM/ring semantics are folded into the one
apex relation, any period in which ring proof and apex carrier COEXIST as two proofs must join on
the wide lanes (Fix B), never the legacy felt — and if the ring keeps a different value
representation, `CrossSchemeSameOpening` is a real proof obligation, not wiring
(`cross_scheme_join_needs_argument`).

### Leg 3 — OUTPUT NOTES (from derived root to spendable notes)

FWS1 already derives the FXO4 ordered-pair output root in-AIR from hidden output openings. What
the apex adds is INSTALLATION — output notes must become spendable, atomically:

- **In-relation:** the output notes append into the note accumulator with the same AAFI discipline
  the input spend uses (authenticate empty leaf at cursor, append FNI4 leaf carrying the output's
  16-lane wide binding, exact count increment) — so "output of swap k" and "spendable note" are
  one object, not a bridge. The FNI4 leaf payload is the wide binding (already the
  `ShieldedExactLinkedLeafV4` shape) — value never appears clear.
- **In-executor:** one durable transaction installs {exact frame, nullifier, output notes,
  executor state} — the CAS-last pattern (`f0fa44145`) extended with the output-note mutation; the
  half-installed state is unrepresentable on restart (replay reconstructs from the durable prefix,
  `98a66d1d3`). `substituted_output_root_cannot_share_root` gives the transcript half; the
  executor half follows `PrivateClearingGameConsequence`'s `DurableReplay` interface — reuse, not
  re-author.

### Leg 4 — COMMITTEE (signer-independent finality)

The Bazaar bar: "the persistent v4 frame is signer-independent and finalized by the
federation/committee; no single prover, dealer, issuer, or frontend gains the whole witness."
Design, patterned on what is banked:

- **Acceptance-token custody lifts to quorum custody.** v3's non-`Clone` acceptance token
  (`4272ac0e8`/`c4d11dc89`: exact statement + carrier digest bound in the `SignedTurn`) becomes
  mintable only from a quorum of independent verifications of the SAME carrier digest — the token
  constructor takes k-of-n verifier attestations over one digest, not one verifier's word. The
  one-global-chain topology (`ea28662e0`/`e6f58f9b9`: global exact-nullifier/frame chain, global
  commit boundary, explicit executor/exact-head authority) is where the quorum-minted token
  registers.
- **Witness distribution is the FHTRI005 lane, not this leg.** Committee FINALITY (no single
  verifier decides) is separable from house-BLINDNESS (no single party holds the witness); the
  latter waits on the malicious/PQ cross-term provider + authenticated q0 broadcast + the
  VSS/Ristretto↔q0 same-opening ceremony (Bazaar §3.3). Do not launder leg-4 progress as §3.4
  item 6 — finality lands first, blindness is the harder residual.
- **Ember decision (surfaced, not made):** committee membership/threshold policy — reuse the BFT
  federation roster (n=4 stream-finalization, [[project-federation-payoff]]) as the v4 finality
  committee, or a distinct verifier set? And the felt-width caveat applies: the finality
  certificate must sign the FULL 8-lane digests (the wound census's "BFT finality cert signs
  lane-0" is the anti-pattern this leg must not reproduce).

### Leg 5 — the four FWS1 witness welds (named in `DESIGN-shielded-whole-note-swap-substrate.md`)

Same-witness constraint blocks, not new proofs: **membership** (selected opening authenticated
against `historical_note_root` — the pinned-root discipline of C4 stage (b),
`ShieldedSpendDescriptor.root_is_pinned` is the Lean precedent); **spend authority**
(`selected.owner` derived from `selected_secret` in-AIR); **counterparty provenance** (the
counterparty opening authenticated as historical note / market reserve / accepted clearing output
— for the Bazaar this is where the FHE/MPC clearing result enters as the counterparty); **outer
transition** (the before/after outer commits' transition executed, not just bound — joins the
executor's `FNS3`-anchor discipline from the 07-22 receipt-epoch correction).

---

## 2. Staging (additive beside v3; ONE ember-fired flip at the end)

No migration theater: v4 installs beside live v3 and becomes THE authority at one deliberate
epoch; v3's 76-PI clear-coordinate exposure retires then, not incrementally.

1. **(design/spec — done this lane)** the two law modules; this doc.
2. **(Lean authoring)** extend the FWS1 relation file-by-leg: welds (leg 5) → FXC4 semantic block
   (leg 2) → output-note append (leg 3). Each stage re-emits a NEW named descriptor
   (`shielded-exact-apex-v4::…`), byte-pinned, PROVENANCE-rowed — FWS1's emit path is the
   template; the FWS1 v1 descriptor itself is never mutated (its name is its identity).
   Gate per stage: the corresponding falsifier UNSAT in the emitted relation + the law-module
   theorem discharged against the emitted object (the `ShieldedSpendPortDischarge` pattern:
   hypotheses die against the real emitted constraints).
3. **(Rust routing, campaign C4/C5 lanes — not this lane)** producer/verifier for the new
   descriptor behind a non-default path; differentials: the free-alias pair refused end-to-end;
   a substituted Dark-AMM lane refused by the deployed verifier.
4. **(committee)** quorum-minted acceptance token + finalizer registration (leg 4), still beside
   v3.
5. **(the flip — EMBER-FIRED)** the one VK epoch: v4 becomes the settlement authority consumed by
   the private worker; batched with the felt-width E-kind rotations and gated on the
   aggregate-turn-VK classification, exactly as `DESIGN-shielded-dark-value-campaign.md` §5
   already states. This doc adds no new decision — it converges on the same single epoch.

---

## 3. The halls, designed against the apex legs

The four halls (Bazaar §1) are not four cryptosystems — each is the SAME five-leg apex shape with
a different rule block and leakage budget. What follows names the delta per hall.

### 3.1 The Dark Pool (GATED SUBSTRATE → one canonical relation)

Missing (per the ledger): "one canonical full-width shielded relation must join the hidden reserve
opening, AMM lanes, exact spend, output notes, persistence, and committee authority." That IS the
apex with the reserve as a second first-class hidden opening:

- **The reserve is a note.** Hold pool reserves as hidden openings in the same accumulator
  discipline (wide-binding leaf payloads); the constant-product transition is a rule block over
  {selected note, reserve-in, reserve-out} — the 19 Dark-AMM lanes become derived-in-AIR
  functions of hidden cells, exactly as FWS1 derives its output root. The same-opening laws
  transfer verbatim: `WideCarrierSameOpening` is carrier-generic in `H8`, so the reserve binding
  inherits `real_wide_join_forces_same_opening` with zero new Lean.
- **The BFV terminal joins by same-opening, not adjacency.** The fused one-coordinate HidingFRI
  cut (`7ba02bc122`) proves 1 of the ~98,304-equation private terminal family
  (`PrivateBookBfvNttFamily` stages the rest). The join between "the ciphertext the committee
  computes on" and "the reserve/book the proof commits" is `Market.DarkBazaarSameOpening`'s
  relation — already stated as a theorem with its RED (two independent bindings prove nothing);
  the `SameOpeningGadget` residual named there is the Dark Pool's genuine crypto work, the
  BFV-side twin of C5.
- **Sequencing:** reserve-as-note relation (pure apex reuse) → AMM rule block → BFV same-opening
  gadget → committee (leg 4, shared). The hall ships in that order; the first two stages need no
  new floor.

### 3.2 The Oracle Pit (FRONTIER — compose, don't invent)

The language exists: fhIR + the convex/certificate tower (`CertQp`, `QpCertificateBundle`,
`PriceCert`, `FhIRClearingPlan`, `OracleWeld`). The hall is a composition:

- **Market maker:** a quadratic/PWL scoring rule whose pricing certificate is a `CertQp` object —
  the T=1 pattern of `FhEggClearing` (fold → cross → allocation, with `crossing` the volume
  argmax) generalized to the convex objective; the certificate is checked, never trusted.
- **Oracle policy:** the `OracleWeld` boundary (outcome ingestion is a policy-gated weld, not a
  trusted feed); private position ingestion = the `DarkBazaarPrivateIngressCutover` pattern.
- **Consequence:** `PrivateClearingGameConsequence` consumes the settled position UNCHANGED — its
  replay tuple is market-agnostic. This is the hall with the least new cryptography and the most
  reuse; its first slice is a `Market/OraclePitClearing.lean` law module patterned on
  `FhEggClearing` (histogram → convex prox), which any later lane can execute against.

### 3.3 The Netting Vault (GATED SUBSTRATE → N-way netting)

Missing: "general N-way no-viewer compression, distributed witness production, and a live
settlement application."

- **N-way netting IS the ring, revealed less.** `Market/Clearing.lean` + `Intent/Ring.lean`
  already prove multilateral conservation/fairness/atomicity; the vault's delta is the LEAKAGE
  BUDGET: publish net per-party settlement only — the ring endpoints stay hidden openings, the
  net is an output note per party. FWS1's fixed 2-in/2-out swap generalizes to N-in/M-out with
  per-asset conservation structural in the rule block (the whole-note transfer equations, summed);
  the N≥3 generalization is authoring work on the FWS1 relation, not new theory.
- **Distributed witness:** the collaborative Shamir-row handoff (`4ec3896a0`/`817c6a6d9`) +
  `DistributedPrivateProverBoundary` name today's honest boundary (custody/encryption/fold proven;
  malicious polynomial consistency, key establishment, share-native PQ PCS explicitly NOT closed).
  The vault must not claim no-viewer until that boundary closes — same discipline as leg 4's
  finality/blindness split.
- **Live app:** season-end guild netting through the existing Bazaar journey (offer → private
  clearing → consequence), reusing the outbox/worker plane end-to-end.

### 3.4 The Sealed Exchange (LIVE PATH — the apex's consumer)

Already the live bounded shape. Its apex delta is exactly "the live player path consumes v4
instead of v3-exact" — no hall-specific design beyond §2's staging; the full combinatorial
exchange (beyond fixed private-book/uniform-allocation families) rides the FhEgg/DrEX clearing
tower (`Clearing`/`FhEggClearing`/`ShieldedClearing`), which is rung-proven and waiting on the
same apex relation for its private execution instance.

---

## 4. What landed this lane (receipts) + surfaced decisions

**Landed (additive, path-limited, both rooted in `Market.lean`, `lake build Market` green,
8764 jobs):**

- `metatheory/Market/WideCarrierSameOpening.lean` — C5 same-opening instantiated on the deployed
  carrier; the free-collision sharpening; Fix B's floor decomposed to one named CR floor; 16
  keystones `#assert_all_clean`, non-vacuous.
- `metatheory/Market/Fxc4ConsequenceBinding.lean` — the consequence leg's lossless-preimage law
  over the exact 146-lane layout + substitution teeth; 9 keystones, non-vacuous.
- this doc.

**Ember decisions surfaced (not made):**

1. **Committee shape (leg 4):** reuse the BFT federation roster as the v4 finality committee vs a
   distinct verifier set; k-of-n threshold; and the finality certificate MUST sign full 8-lane
   digests (felt-width class).
2. **FWS1 vs apex descriptor identity:** the apex re-emits under a NEW name
   (recommended here: FWS1 v1 stays immutable as the banked substrate; the apex is
   `shielded-exact-apex-v4::…` with its own PROVENANCE row) — confirm, since the alternative
   (versioning FWS1 in place) would blur the "intentionally not named v4" boundary `f540ed95a1`
   deliberately drew.
3. **(standing, owned by the campaign doc)** #17 value-law posture and VK-epoch timing —
   unchanged; this design converges on the same single flip.

**Explicitly out of this design:** the FRI floor (D1's lane); the live cross-term provider
(FHTRI005 residual, its own protocol lane); GPU/perf claims (exact release-mode measurements on
hbox/persvati only, per the Bazaar ledger §4).
