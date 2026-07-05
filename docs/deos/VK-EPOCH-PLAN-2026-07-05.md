# The coordinated VK epoch — scoped, reconciled against HEAD (2026-07-05)

> **STATUS: EXECUTED (2026-07-05).** The VK batch — **G5 tags 18/19 in-AIR
> satisfaction-descriptor emit** — landed. Phase 0 verdicts confirmed: **DECO is
> NON-VK (Reading A)** — a Stripe `Effect::Mint` rides the already-emitted
> `mintVmDescriptor2R24` PI-46 pin (col 68 = `PARAM_BASE(68)+param::MINT_HASH(0)`),
> so no new descriptor row and DECO is OUT of the VK batch; its
> producer/executor/fold-tooth is decoupled NON-VK follow-through (see below).
> **G5 orphan confirmed** — `EmitDischargeVaultSat.lean` was a scratch runner
> (not in lakefile, imported by nothing); the two descriptors were built +
> `#assert_all_clean` (piCount 47) but unemitted. Wired into `EmitRotationV3.lean`
> beside tag-17 + crown-imported into `Dregg2/Deos.lean`.
> **GATES (all green):** regen scoped to +2 staged rows in
> `rotation-v3-staged-registry.tsv` + the one `V3_STAGED_REGISTRY_FP` re-pin;
> **drift PASS** (re-emit byte-identical); **`lake build Dregg2` green** (4254
> jobs) with the apex `#assert_axioms lightclient_unfoolable_circuit_sound`
> (ClosureFinal.lean:268) + `deployed_system_secure` (AssuranceCase.lean:942)
> re-verified axiom-clean over the new registry; **G5 prove exercise 10/10 green**
> (`circuit/tests/gentian_discharge_vault_prove.rs` — honest discharge+vault
> prove-and-verify, all 6 forge arms refused; fixtures byte-identical to the
> emitted registry rows); **cargo check** circuit/circuit-prove/turn/cell/sdk
> green; **no carrier regression** (bridge deployed-tooth cheap arms green, old FP
> unreferenced). The sound deployed-default flip stays GENTIAN-blocked and OUT, as
> scoped.
>
> **NOT DONE (decoupled follow-through, precisely scoped — NOT part of the
> coordinated regen since DECO is NON-VK):** the DECO on-wire *live* path —
> (1) `generate_rotated_stripe_mint_wide` producer filling the mint row's
> `param0`/PI-46 with `stripe_payment_hash_felt` + a Stripe-context dispatch that
> routes a Stripe `Effect::Mint` through the PI-46-pinned `mintVmDescriptor2R24`
> (plain `Effect::Mint` currently routes to `supplyMintVmDescriptor2R24` with NO
> pin — `trace_rotated.rs:5030`; and `generate_rotated_effect_vm_trace` applies
> the pin only for `Effect::BridgeMint` — `:617`); (2) executor felt-attach in
> `bridge/src/stripe_mirror.rs` (compute + retain `stripe_payment_hash_felt` on
> `VerifiedPayment`; today only the BLAKE3 `payment_nullifier` exists); (3) the
> DECO deployed fold tooth (twin of `bridge_binding_deployed_tooth.rs`). These
> MUST land atomically (executor felt → producer → dispatch → fold-live → real-
> STARK tooth) or the felt is a dead shadow field; that is why they are held as
> one cohesive lane rather than shipped half-built.



**Grounded at** `/Users/ember/dev/breadstuffs` @ `db466dcd9` (the fresh post-squash
baseline — history was big-banged; every file:line below is against the LIVE tree, not
old SHAs). Tree is green (drift PASS, no-degraded PASS, core crates build).

**What this doc is.** HORIZONLOG and several design docs say various built-but-staged lanes
"ride the big-bang regen" / "the ONE shared universal-fold descriptor regen." This doc
verifies each candidate at HEAD and scopes **exactly** what a coordinated circuit-descriptor
regen must (and must not) batch. The honest headline is up front because it changes the
shape of the epoch:

> **The seven-carrier universal-fold "big bang" is NOT fireable, and this epoch is not that.**
> Six of seven carriers (factory / sovereign / membership / dsl / bridge-deepest /
> hatchery-contract) are blocked on geometry-widening or VK-emit **walls**, not emits
> (`docs/WELD-STATE.md` §4–§5, `[@wave-1..5]` stop-conditions). Firing a regen that ships
> them would be vacuous binding (the fail-open law). What is genuinely **emit-ready and
> coordinatable now** is a *small* batch: the **DECO** (8th carrier) on-wire emit and the
> **G5 tags 18/19** in-AIR satisfaction-descriptor emit (joining the already-emitted tag-17).
> Bridge's tuple item is superseded and already regenerated. That is the whole batch.

---

## 0. The reconciled candidate verdicts (one line each)

| # | candidate | HORIZONLOG framing | **verdict at HEAD** |
|---|---|---|---|
| 1 | **DECO on-wire emit** | "rides the coordinated big-bang" | **BATCH** — proof spine + fold arm + socket built & axiom-clean; remainder = producer (missing) + executor felt-attach + descriptor pin. SHALLOW. *(Crux: may be NON-VK — see §1.)* |
| 2 | **G5 tags 17/18/19 → in-AIR** | "promote from STAGED into the recursive AIR (VK bump)" | **PARTIAL BATCH** — tag-17 descriptor already emitted; tags 18/19 gates+descriptors+producers **built & clean**, remainder = registry-emit + crown-wire + producer-live-wire. Emit the staged descriptors. The **sound deployed-default flip is OUT (GENTIAN-blocked)** — see §2. |
| 3 | **PR#23 bridge-tuple 46→72** (`bridgeTuplePiExposure`) | "rides the big-bang regen" | **SKIP — SUPERSEDED + already regenerated.** Absent from all HEAD code (HORIZONLOG-only). The deployed `withMintHashPin` single-digest pin at PI 46 already landed (drift PASS). See §3. |
| 4a | accumulator 8-felt apex flip | "the flat-mem weld" | **SKIP — separate gated epoch** (whole-image 1-felt→8-felt digest flag-day, `docs/WELD-STATE.md` §5 item 8). Not this batch. |
| 4b | value8 `setField` | — | **SKIP — REFUTED** as a completeness/`fields[0..7]` ~31-bit residual, not a soundness regen item (`docs/WELD-STATE.md` §5 item 5). |
| 4c | umem flip | "the wide-welded VK epoch" | **SKIP — its own deliberately-gated VK epoch** (`HORIZONLOG.md:369`). Coordinate the regen window; do not auto-batch. |
| — | off-AIR manifest rollout (tags 13–16,17,18,19) | "one verifier-upgrade window" | **NOT A DESCRIPTOR REGEN** — a *verifier-code* rollout, VK bytes unchanged. Separate lighter epoch; keep out of the VK regen. See §2.0. |

**Net batch = DECO emit + G5 18/19 in-AIR descriptor emit.** Everything else is
superseded, refuted, or a distinct gated epoch.

---

## 1. DECO on-wire emit (candidate 1) — BATCH, SHALLOW

### What is BUILT + axiom-clean at HEAD
- **Felt anchor:** `deco_payment_hash_felt` = `hash_fact(hash_fact(amountCents,[currency,recipient]),[paymentIntentId])` — `circuit/src/dsl/deco_payment.rs:46`; byte→felt projector `stripe_payment_hash_felt:84`. Felt-domain, NOT the byte-domain BLAKE3 `payment_nullifier` (the anti-vacuity law).
- **Recursion leaf + descriptor:** `circuit-prove/src/deco_leaf_adapter.rs` — `deco_to_descriptor2()` (`:171`, `"deco-commitment-leaf::dregg-deco-stripe-v1"`, `public_input_count=DECO_CLAIM_LEN=5` `:101/:224`); `prove_deco_leaf` (`:341`), `prove_deco_leaf_with_claim` (`:358`), `prove_deco_payment_binding_node_segmented` (`:391`); anchor exposed at leaf claim lane `DECO_LEAF_PAYMENT_HASH_PI=4` (`:104`). Teeth (forged amount / forged payment_hash → UNSAT) present as `#[ignore]` slow tests.
- **Witness socket:** `CarrierWitness::Deco(DecoWitnessBundle)` — `circuit-prove/src/joint_turn_aggregation.rs:150/201`; `carrier_witness: Option<CarrierWitness>` on the leg (`:130`). *(NB: this contradicts `docs/WELD-STATE.md:211` "witness socket NOT generalized" — the socket IS built at HEAD; WELD-STATE's snapshot predates it.)*
- **Fold arm (fail-closed):** `Some(CarrierWitness::Deco(bundle))` — `circuit-prove/src/ivc_turn_chain.rs:3180`; admits via `carrier_claim_pins_admitted(…, DECO_PAYMENT_HASH_PI, …, Some((PARAM_BASE+param::MINT_HASH, VmRow::First)))` (`:3183-3191`), dual-exposes (`:3192`), re-proves the leaf (`:3201`), folds (`:3210`). `DECO_PAYMENT_HASH_PI=46` (`:2881`).
- **Lean flip:** `metatheory/Dregg2/Circuit/DecoBindingFromFold.lean` — `deco_binding_from_fold` (`:140`), `backedAt_from_fold` (`:171`), `deco_authenticates_from_fold` (`:208`); non-vacuous both poles (`honest_companion_fires:261`, `forged_payment_hash_unsat_demo:323`); `#assert_axioms`-clean ⊆ {propext, Classical.choice, Quot.sound}. `DecoBackingAttack.lean` stands beside it (both imported at `metatheory/Dregg2.lean:706/709`).

### The remainder (the on-wire emit gap), grounded
Gap comment: `circuit-prove/src/ivc_turn_chain.rs:2876-2880` — "the deployed `stripeMint`
descriptor EMIT (`withPaymentHashPin` + the `generate_rotated_stripe_mint_wide` producer +
the TSV regen) rides the coordinated big-bang … until it lands, `stripeMint` legs carry NO
payment-hash pin → this arm REFUSES them (fail-closed)."

1. **Producer — DOES NOT EXIST.** Only the bridge twin `generate_rotated_bridge_mint_wide` exists (`circuit/src/effect_vm/trace_rotated.rs:3860`, dispatched at `:4974` on `Effect::BridgeMint`). No `generate_rotated_stripe_mint_wide`; no `Effect::Mint`-with-Stripe-context dispatch branch fills a payment_hash PI.
2. **Executor felt-attach — NOT DONE.** `bridge/src/stripe_mirror.rs` computes only the byte-domain BLAKE3 `payment_nullifier` (`:73`), never the felt `deco_payment_hash_felt`/`stripe_payment_hash_felt` (0 grep hits in `bridge/`, `turn/executor/`). The producer needs the felt anchor attached to the mint row's `param0`.
3. **Descriptor pin + TSV regen** — no deco/stripe row in `circuit/descriptors/*` (0 hits).

### ⚑ The CRUX reconciliation (verify before scoping the VK cost)
`DECO_PAYMENT_HASH_PI = 46` is the **same PI slot** as bridge's `BRIDGE_MINT_HASH_PI = 46`,
and the deployed mint descriptor **already carries a first-row hash pin at PI 46**
(`mintVmDescriptor2R24` = `mintV3BridgeHash` = `withMintHashPin`, TSV
`rotation-v3-staged-registry.tsv` `dregg-effectvm-mint-v1-rot24-v3-staged`,
`public_input_count:51`, `pi_binding col 68 pi_index 46` — regen landed, drift PASS per
`metatheory/Dregg2.lean:708`). Therefore:

- **Reading A (likely — DECO is NON-VK):** a Stripe `Effect::Mint` routes through the
  existing PI-46-pinned mint descriptor; the fold admission
  (`carrier_claim_pins_admitted`) is satisfied by that already-emitted pin. Then DECO's
  entire remainder is **non-VK**: the `generate_rotated_stripe_mint_wide` producer (fill
  PI-46 with the felt `stripe_payment_hash_felt`) + the executor felt-attach + a dispatch
  branch. No new descriptor, no fingerprint move, no regen. DECO would then **not be a VK
  epoch item at all** — just a producer/executor wiring lane that flips its own fold arm
  from fail-closed to live.
- **Reading B (if a distinct descriptor is required):** `stripeMint` is a new sibling
  descriptor (twin of `mintV3BridgeHash`) → one new registry fingerprint, `public_input_count`
  bump on that descriptor only, append at TAIL (never touch `[0..46)`), + 3 registry
  fingerprints. SHALLOW per-descriptor VK, no geometry widening (the anchor is an
  executor-written `param0` felt, `docs/deos/DECO-CARRIER-PLAN.md` §3).

**Action item (Phase-0 verification):** determine whether `Effect::Mint` from Stripe is
admitted by `mintVmDescriptor2R24`'s existing PI-46 pin (Reading A) or needs a distinct
`stripeMint` descriptor (Reading B). Grep the mint dispatch (`trace_rotated.rs:4974`
neighborhood — note `Effect::Mint` and `Effect::BridgeMint` are distinct kernel effects, so
plain mint may currently route through a producer that does **not** pin PI-46) and the
descriptor the plain-mint fold leg admits against. **This single fact decides whether DECO
is in the VK batch at all.** Recommended default: prefer Reading A (reuse the emitted pin) —
it avoids a needless second mint-descriptor fingerprint and is the cleaner deployment.

### VK / geometry cost (DECO)
- **Geometry:** none — no pre-limb / `B_SPAN` widening; the anchor is an executor-written
  `param0` felt (SHALLOW class, `DECO-CARRIER-PLAN.md` §3).
- **PIs:** ONE tail felt (`DECO_PAYMENT_HASH_PI`, claim_len 1) — and under Reading A that PI
  is already emitted.
- **VK move:** either **zero** (Reading A) or **one descriptor fingerprint** (Reading B).

---

## 2. G5 tags 17/18/19 satisfaction (candidate 2) — PARTIAL BATCH

There are **two distinct staging layers** here that HORIZONLOG's one-line P3 conflates.
Keep them apart — they are different epochs with different VK impact.

### 2.0 Layer 1 — off-AIR manifest tags (VK UNCHANGED) — NOT in this regen
`docs/deos/{SETTLE-ESCROW,DISCHARGE-OBLIGATION,VAULT-DEPOSIT}-WELD-DESIGN.md` §4 all agree:
tags 17/18/19 are **slot-caveat-manifest entries carried in public inputs and re-evaluated
by off-AIR verifier code** — "The AIR constraint polynomials are unchanged, so the VK bytes
are unchanged." Steps 1–5 (Lean rung, `pi.rs` tag const, `verify.rs` arm, executor
projection, teeth tests) are **landed**. The only remaining step is the **verifier-code
rollout** (ship the upgraded verifier to consumers, then allow cells to declare the caveat):
`DISCHARGE-OBLIGATION-WELD-DESIGN.md:137-142`, `VAULT-DEPOSIT-WELD-DESIGN.md:152-157` —
"a *verifier-code* rollout, not a proving-key rotation … one verifier-upgrade window can
carry all the off-AIR manifest tags (17, 18, 19, 13–16) at once."

**Verdict:** this is a real, ready, *lighter* epoch — but it is **NOT a descriptor regen**
and must not be batched into the VK epoch. Fire it in its own verifier-upgrade window.

### 2.1 Layer 2 — in-AIR satisfaction descriptors (VK-affecting) — THE batch item
HORIZONLOG P3's "promote INTO the recursive AIR (VK bump)" is the *fold-proof-witnessed*
form: a pure light client that only checks the batch proof (not a re-executing verifier)
witnesses the capacity satisfaction. This lives in the `*SatVmDescriptor2R24` family.

**Ground truth (this REVISES HORIZONLOG:168-185's "machinery absent / inequality gates
unbuilt" pessimism — the machinery is now BUILT):**

- **Lean soundness keystones — clean.** `metatheory/Dregg2/Deos/CapacitySatisfaction.lean`
  `#assert_all_clean` (`:477-494`, 16 theorems): escrow `satisfaction_witnessed` (`:162`);
  **discharge** `discharge_satisfaction_witnessed` (`:316`) + teeth (`:288/:296/:305`);
  **vault** `vault_satisfaction_witnessed` (`:406`) + teeth (`:380/:388/:396`).
- **Lean emit descriptors — built & clean.** `metatheory/Dregg2/Deos/DischargeSatDescriptor.lean`
  `dischargeSatVmDescriptor2R24` (`:162`, `piCount==47` `:426`, `#assert_all_clean:438` with
  `early_discharge_unsat`/`cursor_not_advanced_unsat`/`wrong_amount_unsat`);
  `VaultSatDescriptor.lean` `vaultSatVmDescriptor2R24` (`:223`, `piCount==47` `:548`,
  `#assert_all_clean:561` with `vault_zero_mint_unsat`/`vault_dilution_unsat`).
- **Rust gates + producers — built (real selectors, no placeholder).**
  `circuit/src/effect_vm/discharge_weld.rs`: `discharge_satisfaction_gates` (`:251`, two
  additive equalities + **due-ness range check `DUE_BITS=28`** `:97/:286`), `DISCHARGE_SEL_COL=PARAM_BASE+2`
  → `DISCHARGE_SEL_PI=46` (`:60/:63`), producer `fill_discharge_aux` (`:393`).
  `vault_weld.rs`: `vault_satisfaction_gates` (`:354`), **overflow-safe multi-limb product**
  `product_gates` (`:268`, `LIMB_BITS=15`/`CARRY_BITS=16`) + `borrow_compare_gates` (`:306`)
  — i.e. the `Tb·m ≤ Sb·d` product that overflows ~31-bit BabyBear is done in-AIR
  overflow-safe, resolving HORIZONLOG:180-182's named blocker; `VAULT_SEL_COL` → `VAULT_SEL_PI=46`
  (`:62/:64`), producer `fill_vault_aux` (`:604`). Both modules declared in
  `circuit/src/effect_vm/mod.rs:175/181`.
- **Real STARK prove/refuse — exercised.** `circuit/tests/gentian_discharge_vault_prove.rs`
  proves real STARKs over checked-in fixtures (`circuit/tests/fixtures/{discharge,vault}-sat-v3-staged.json`).

**What is NOT yet done (the emit + wiring gap) — the batch work:**
1. **Registry rows** — no `dischargeSat`/`vaultSat` row in `circuit/descriptors/rotation-v3-staged-registry.tsv`
   (tag-17 `settleEscrowSatVmDescriptor2R24` IS there, row 58). The emit runner
   `metatheory/EmitRotationV3.lean:117` emits ONLY tag-17.
2. **Orphan emit runner** — `metatheory/EmitDischargeVaultSat.lean` is a scratch runner: NOT
   a `[[lean_exe]]` in `metatheory/lakefile.toml`, imported by nothing, the sole importer of
   `Discharge/VaultSatDescriptor`. Fold its emit into `EmitRotationV3.lean` (or give it a lake
   target) so 18/19 leave orphan status.
3. **Crown wiring** — `metatheory/Dregg2/Deos.lean` imports tag-17's `SettleEscrowSatDescriptor`
   (`:121`) + `SettleEscrowSatWideDescriptor` (`:140`) but **not** `Discharge/VaultSatDescriptor`.
4. **Producer live-wiring** — `fill_discharge_aux`/`fill_vault_aux` are called only from the
   test; wire them into the live rotated-trace generator (`trace_rotated.rs`) and bind
   `PERIOD/AMOUNT/CLOCK` cols (`discharge_weld.rs:71-75`) + the vault slot params through the
   PI/manifest-param path.
5. **No wide-descriptor / selector-binding analog** — tag-17 has `SettleEscrowSatWideDescriptor.lean`
   + a selector-binding module; 18/19 have no wide+selector-binding twin yet.

### ⚑ The honest ceiling (what the emit does NOT buy — the GENTIAN blocker)
Emitting the 18/19 satisfaction descriptors to the **staged** registry (`-staged.tsv`) makes
them available and keeps Lean↔TSV in sync — but it does **NOT** flip the deployed default to
a pure-light-client-witnessed discharge/vault. That flip is blocked by the **same GENTIAN
residuals tag-17 hit** (`HORIZONLOG.md:114-167`):
- **The bare-descriptor dodge** — escrow settlement rides a normal effect whose honest proof
  verifies under the BARE wide descriptor; a pure LC can't reject a forged settle routed
  through the bare descriptor unless the decode+force gates live on EVERY deployed wide
  member = a registry-wide flag-day (`:144-148`).
- **Row-locality** — the every-row selector-force vs settle-row-only satisfaction gate makes
  the honest declared settle unsatisfiable as naively welded (`:151-167`, empirical, real STARK).
- **In-AIR `B_AUTHORITY_DIGEST`→selector forcing** — the terminal blocker to a sound pure-LC
  flip (recompute the authority digest in-AIR + decode the required-tag floor + force sel=1),
  a Poseidon2-preimage-and-decode gadget (`:123-127`).

**Verdict for the batch:** **emit** the 18/19 in-AIR satisfaction descriptors to the staged
registry (small, drift-keeping, joins tag-17), and wire the crown + producers — this is real
batch work and is VK-touching (new staged-registry fingerprints). But scope the **sound
deployed-default flip OUT** of this epoch: it is the GENTIAN in-AIR-authority-digest +
bare-descriptor flag-day build, a deeper lane (`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`
§6), not an emit.

### VK / geometry cost (G5 18/19)
- **Geometry:** none — `piCount==47` on both (tag-17 shape); tags are VALUES, not layout
  offsets. No `B_SPAN` widening for the satisfaction descriptors themselves. *(Note: the
  escrow AFTER-gate v10→v11 `B_SPAN 51→119` geometry drift already landed for tag-17 —
  `docs/WELD-STATE.md:221-223`; 18/19 ride the same landed geometry.)*
- **VK move:** two new staged-registry descriptor fingerprints (`dischargeSat`, `vaultSat`)
  + their drift-gate pins. Additive; does not move the deployed default cohort VKs.

---

## 3. Bridge tuple 46→72 (candidate 3) — SKIP: SUPERSEDED + already regenerated

**Verdict: DROP `bridgeTuplePiExposure`.** It is absent from all HEAD code — it appears only
in `HORIZONLOG.md:29-30` (the stale 2026-07-02 PR#23 coordination note). Grep across
`.lean/.rs/.json/.tsv` finds it in no code file.

The deployed bridge-mint carrier is the felt-domain **single `mint_hash` digest** pinned at
**PI 46** via `withMintHashPin`, and it **already landed + regenerated**:
- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:5306` —
  `mintVmDescriptor2R24 = mintV3BridgeHash = withMintHashPin (withSelectorGate selM.MINT mintV3)`;
  `#guard mintV3.piCount==46`, `#guard mintV3BridgeHash.piCount==47` (`:5312`); `withMintHashPin`
  is additive (one `.piBinding .first` on `prmCol 0` at tail, `:5221`), teeth
  `withMintHashPin_publishes` (`:5274`) `#assert_axioms`-clean.
- Emitted: `circuit/descriptors/rotation-v3-staged-registry.tsv` `dregg-effectvm-mint-v1-rot24-v3-staged`,
  `public_input_count:51`, `pi_binding col 68 pi_index 46`. `metatheory/Dregg2.lean:708`:
  "regen landed, drift PASS." The flip `BridgeBindingFromFold.lean` supersedes `BridgeBackingAttack`.

The 26-limb full-fidelity binding survives only as the **fold leaf**
`circuit-prove/src/bridge_leaf_adapter.rs` (PIs 0..25, the recursion-side re-prove of the
foreign note-spend), NOT as a deployed-descriptor 46→72 widening. PR#23's Part-B bare-tuple
exposure was correctly dropped as superseded by the fold-witnessed mint_hash binding
(consistent with `HORIZONLOG.md:55-74`, `BridgeBackingAttack.lean:11/84` single-`mint_hash`
model). **Nothing to batch; nothing to coordinate on the descriptor side** beyond noting PR#23's
Lean sides (`Crypto/Deco.lean`, `Verify/Stripe*`) auto-merge clean and its
`effect_vm_descriptors.rs`/TSV conflicts resolve **by regeneration** if that PR is landed
after main (never hand-merge — `HORIZONLOG.md:30-33`).

---

## 4. Candidate-4 classifications (built-but-staged sweep)

- **Accumulator 8-felt apex flip** — **SKIP (separate gated epoch).** The whole-image final
  1-felt digest squeeze → 8-felt chip-chain cut (`commitment.rs:1219`) is "the deliberately-gated
  separate epoch" (`docs/WELD-STATE.md:596-598` §5 item 8). The six component roots are already
  faithful; the deployed apex does not need this flip to accept the DECO/G5 emits. Not this batch.
- **value8 `setField`** — **SKIP (refuted, not a soundness regen item).** The `fields[0..7]`
  flat-record ~31-bit surface is "allowlisted, self-deleting when fields-welded; not a root,
  does not block carriers" (`docs/WELD-STATE.md:587-589` §5 item 5). A completeness/liveness
  seam, not a soundness descriptor move. Confirmed out of scope.
- **umem flip** — **SKIP (its own deliberately-gated VK epoch).** "commit the wide-welded VK +
  flip the deployed default off rotated+per-map" (`HORIZONLOG.md:369`, memory
  `project-umem-as-primitive-epoch`). Staged-by-design. It may share a regen *window* with this
  epoch but is not auto-batched here — its flip is a full deployed-default VK rotation, larger
  than the DECO/G5 emits. Coordinate the window; keep the flips independent.

---

## 5. THE ORDERED EPOCH PLAN (the v-shape)

Naming: the deployed cohort is rotation-v3 R=24 (`EFFECT_VM_WIDTH=188`,
`circuit/src/effect_vm/columns.rs:31`); the current descriptor tip is v13-geom
(`docs/HANDOFF-v13-VK-EPOCH.md` §1c — that prior epoch's regen already landed the escrow-v11
geometry + the mint_hash pin). This epoch is a **v3-registry descriptor-ADD** (no geometry
widening), call it **v13→v13.1**.

### Phase 0 — the two verifications that set the batch (do FIRST, cheap)
- **DECO Reading A vs B** (§1 crux): does a Stripe `Effect::Mint` admit against the
  already-PI-46-pinned `mintVmDescriptor2R24`, or need a distinct `stripeMint` descriptor?
  This decides whether DECO is even VK-affecting. Prefer Reading A.
- **G5 flip-vs-emit boundary** (§2.1): confirm the 18/19 emit targets the **staged** registry
  (`-staged.tsv`) and does **not** attempt the deployed-default flip (GENTIAN-blocked). The
  emit is in scope; the flip is not.

### Phase 1 — VK-shape changes (atomic, BEFORE the regen)
These are the Lean/descriptor edits that *change what the regen emits*. Land them so the
regen is a pure re-projection.
1. **G5 18/19 Lean emit** — fold the `dischargeSatVmDescriptor2R24` / `vaultSatVmDescriptor2R24`
   emit into `metatheory/EmitRotationV3.lean` (beside tag-17's `:117`); import
   `DischargeSatDescriptor` + `VaultSatDescriptor` into `metatheory/Dregg2/Deos.lean` (beside
   `:121`); retire the orphan `EmitDischargeVaultSat.lean` (or promote it to a lake target).
   Build the missing wide-descriptor + selector-binding twins if the staged emit requires them
   (mirror `SettleEscrowSatWideDescriptor.lean`).
2. **DECO descriptor** — ONLY under Reading B: add the `stripeMint`/`withPaymentHashPin` Lean
   emit (twin of `withMintHashPin`, `EffectVmEmitRotationV3.lean:5221`). Under Reading A: NO
   Phase-1 descriptor change (the PI-46 pin is already emitted).
3. **Gate:** every touched Lean emit `#assert_axioms`-clean; `lake build` the WHOLE tree (not
   per-file — the shared-`Config`/registry umbrella hazard, memory §per-file-green-hides-red).

### Phase 2 — the ONE regen + apex re-verify
1. **`scripts/emit-descriptors.sh`** (→ `emit_descriptors.py`) — the single idempotent command
   that regenerates every `circuit/descriptors/*.json` + `*.tsv` from the Lean source of truth
   and re-pins the `*_FP` sha256 constants. On a clean tree it is a no-op; after Phase 1 it
   emits the new `dischargeSat`/`vaultSat` (+ `stripeMint` under Reading B) rows and re-pins
   fingerprints.
2. **`scripts/check-descriptor-drift.sh`** — the Lean↔JSON freshness gate; must return PASS.
3. **Apex re-verify** (the acceptance gate — the whole point):
   - `lightclient_unfoolable` (`ClosureFinal.lightclient_unfoolable_circuit_sound`,
     assembled at `metatheory/Dregg2/Circuit/CircuitSoundnessAssembled.lean`) clean under the
     new fingerprints.
   - The 5 AssuranceCase guarantees (`metatheory/Dregg2/AssuranceCase.lean`) clean.
   - `#assert_axioms` on the DECO + G5 flip files unchanged (⊆ {propext, Classical.choice,
     Quot.sound}). The dual `lightclient_complete` (`CircuitCompleteness.lean:154`) if the
     completeness beachhead is in the gate set.

Because this epoch is **additive** (new staged descriptors + at most one re-projected mint
pin), the apex re-verify should not require re-proving the closure — the shared `[0..46)`
prefix is untouched, and the new descriptors are staged members, not deployed-default cohort
moves.

### Phase 3 — non-VK follow-through (AFTER the regen, producer/executor/flip)
1. **DECO producer** — write `generate_rotated_stripe_mint_wide` (twin of
   `generate_rotated_bridge_mint_wide`, `trace_rotated.rs:3860`) filling the mint row's
   `param0`/PI-46 with `stripe_payment_hash_felt`; add the Stripe `Effect::Mint` dispatch branch
   (near `trace_rotated.rs:4974`).
2. **DECO executor felt-attach** — `bridge/src/stripe_mirror.rs`: compute + retain the felt
   `stripe_payment_hash_felt` on the `VerifiedPayment` so `from_retained_deco` projects it (today
   only the BLAKE3 `payment_nullifier` exists, `:73`). This flips the DECO fold arm from
   fail-closed to live.
3. **G5 18/19 producer live-wiring** — call `fill_discharge_aux`/`fill_vault_aux` from the live
   rotated-trace generator (today test-only); bind `PERIOD/AMOUNT/CLOCK` + vault slot params.
4. **DECO deployed tooth** — `circuit-prove/tests/deco_binding_deployed_tooth.rs` (twin of the
   bridge deployed tooth): honest-accept + forged-payment-identity→UNSAT through
   `prove_turn_chain_recursive → verify_turn_chain_recursive`.

### The deploy (ember-gated, eyes-open)
The descriptors are committed in-repo, so "distribute the new VK to light clients" =
`git push origin main` + client rebuild (NOT a genesis step — `docs/HANDOFF-v13-VK-EPOCH.md`
§1c). **Re-genesis is NOT required** for a staged-registry descriptor add (no deployed-default
cohort VK moves, no PI values shift on live effects). If Reading B lands a `stripeMint` that
becomes a deployed-default member, revisit — a deployed-PI shift would need the eyes-open
devnet re-genesis (`generate.sh --force`, `HANDOFF` §1d, ember's call).

---

## 6. BLAST RADIUS + size

- **Descriptors that MOVE:** 2 new staged rows (`dischargeSatVmDescriptor2R24`,
  `vaultSatVmDescriptor2R24`) + their 2 drift fingerprints; **+0** under DECO Reading A, **+1**
  (`stripeMint`) under Reading B. The deployed-default cohort's 56 descriptors are **untouched**
  (shared `[0..46)` prefix never touched; appends at TAIL only — `docs/WELD-STATE.md:564`).
- **Geometry:** **NOT widening.** No `B_SPAN` / `NUM_PRE_LIMBS` change; `EFFECT_VM_WIDTH=188`
  unchanged. This is a **PI-tail-append / staged-descriptor-add** regen, the cheapest class.
  (Contrast the blocked carriers' §5-item-9/10/11 geometry-widening walls, which this epoch
  deliberately excludes.)
- **Lean re-ground:** additive — the apex + 5 guarantees re-verify under new fingerprints; no
  closure re-proof expected (additive staged members). `#assert_axioms` sets unchanged on the
  flip files.
- **Size estimate:** **SMALL.** Phase-1 Lean emit + crown wiring (a few imports + emit lines +
  possibly two wide/selector-binding twins for 18/19) ~ a focused day; Phase-2 regen is one
  script run + one apex re-verify; Phase-3 is the DECO producer + executor + G5 producer wiring
  + one deployed tooth (bridge-sized, reuses built adapters). Orders of magnitude smaller than
  the mythical seven-carrier bang (which is NOT fireable and NOT this).

---

## 7. What must COORDINATE

- **alif's PR #23** (`feat/stripe-kernel-attested`) — its `Crypto/Deco.lean` + `Verify/Stripe*`
  auto-merge clean; its `bridgeTuplePiExposure` widening is SUPERSEDED (§3) — do not resurrect
  it. If PR#23 lands after main, resolve its `effect_vm_descriptors.rs`/staged-TSV conflicts
  **by regeneration**, never hand-merge (`HORIZONLOG.md:30-33`). Same-landing follow-up flagged
  in the PR body: `proof_verify.rs` reconstruct PI [46..) from `apply_bridge_mint` (Fiat-Shamir).
- **The other terminal's DreggNet-native redesign** (`HORIZONLOG.md:11-25`, Fable) — its P3 is
  exactly this G5 17/18/19 promote; its P1/P2 (PrepaidLease budget-escrow, umem workload runtime)
  are separate substrate additions. Sequence the G5 emit around whichever session is live in
  `circuit/` + `metatheory/Dregg2/Deos/` (shared-file clobber hazard — main-loop owns
  `EmitRotationV3.lean` / `Dregg2/Deos.lean` / the TSVs; memory §swarm-shared-tree-clobber).
- **The descriptor artifacts** — `circuit/descriptors/*.{json,tsv}` + the `*_FP` constants are
  Lean-machine-generated; the ONLY sanctioned edit path is `scripts/emit-descriptors.sh` after
  moving the Lean emit. Never hand-edit a descriptor or a fingerprint.
- **The off-AIR manifest verifier-upgrade window** (§2.0, tags 13–16,17,18,19) and the **umem
  wide-weld VK epoch** (§4) — both distinct epochs that may share a deploy window with this one
  but must fire as their own coordinated flips. Do not fold them into this regen.

---

## 8. One-line summary for the driver

Batch = **DECO on-wire emit** (proof spine done; add the producer + executor felt-attach; likely
NON-VK if it reuses the emitted PI-46 mint pin — verify first) **+ G5 tags 18/19 in-AIR
satisfaction-descriptor emit** (gates/descriptors/producers built & clean; add registry rows +
crown wiring + live producer wiring; sound deployed-flip stays GENTIAN-blocked and OUT of scope).
**Skip** the superseded bridge-tuple (already regenerated), the accumulator/value8/umem items
(separate gated epochs / refuted), and the off-AIR manifest verifier rollout (not a descriptor
regen). It is a small, additive, geometry-stable v13→v13.1 regen — **not** the not-fireable
seven-carrier universal-fold bang.

---

## 9. GENTIAN FLAG-DAY — the bare-descriptor dodge CLOSED (soundness core landed 2026-07-05)

> **STATUS: the SOUND CORE + the anti-launder forge + the DEPLOYED-ALIGNED column-parametric keystone
> (§9.1b, `gentianDeployedBareRefuse` — the sound emit-weld TARGET, traceWidth widening baked in) are
> LANDED + GREEN + crown-wired; the emit-map + regen + apex geometry-cascade re-verify is the remaining
> multi-run grind (RESUME AT §9.3 STEP 1), then the ember-gated deploy.**
> This section supersedes §2.1's "sound deployed-flip stays GENTIAN-blocked / OUT" for the SOUNDNESS
> question: the terminal blocker §2.1 named (in-AIR `B_AUTHORITY_DIGEST`→selector) was already
> discharged by PATH (b) in `CarrierBoundFloorGadget` (decode from the caveat-manifest columns, no
> separate digest limb). The dodge is now closed IN PROOF; what remains is the mechanical (but
> geometry-widening) whole-cohort emit + the apex re-verify.

### 9.1 What LANDED this session (proven, axiom-clean, committed)

- **Lean soundness core — `metatheory/Dregg2/Deos/BareCohortFloorRefuse.lean`** (`#assert_all_clean`,
  17 keystones, non-vacuous both poles). The FLOOR==0-REFUSE weld: reuse the PROVEN caveat-manifest
  floor decode (`CarrierBoundFloorGadget.carrierGates`, bound to the committed manifest at PI 45 by
  `caveatCommit`/`caveatCommit_binds`) + one new `floorZeroRefuseGate` (`floorCol == 0`).
  - **`declared_escrow_unsat_under_bare`** — the PRIMARY named forge: a settle-escrow routed to any
    BARE cohort member `d` is UNSAT when the committed manifest declares escrow (the decode lights
    `floorCol = 1`; the refuse gate demands `0`; jointly unsatisfiable). ∀ `d` — covers every member.
  - **`declared_tag_unsat_under_bare` (tag-parametric)** + instances
    `declared_{discharge,vault}_unsat_under_bare` — the same closes tags 18/19.
  - **`non_declared_floor_zero`** — completeness: a non-declaring cell decodes `floorCol = 0`, refuse
    inert (no false reject; the flip is complete, not merely sound).
- **Rust deployed-column shadow — `circuit/src/effect_vm/bare_floor_refuse_weld.rs`** (7/7 tests).
  Per capacity tag {17,18,19}: a decode block over the caveat-commit-bound type-tag columns
  (`caveat_tag_col(k)` = 643/650/657/664 at v13 geometry) + `floor_zero_refuse_gate`, at disjoint
  aux headroom. `bare_floor_refuse_gates()` = 3 blocks + 4 uniformity = 43 gates.
  - **THE ANTI-LAUNDER FORGE TOOTH BITES:** `declared_escrow_is_unsat_under_bare`,
    `declared_discharge_and_vault_are_unsat_under_bare` (declared-capacity row → `floor=1` → refuse
    bites → UNSAT); `non_declared_cell_is_accepted_by_bare` (no false reject);
    `caveat_uniformity_bites_on_non_uniform_manifest`.
- Commits: `f74ab2694` (escrow core), `b11416faa` (capacity-general), `addfa3c32` (Rust shadow+tooth).

### 9.1b What LANDED the SECOND session (2026-07-05 pt2 — the deployed-aligned soundness enabler)

- **Drift-pin fix** — `circuit/src/effect_vm/carrier_floor_weld.rs:348` pinned the STALE
  `caveat_tag_col(0) == 291`; corrected to the v13 value `643` (derived: `CAVEAT_BASE = V1_WIDTH(188) +
  2·B_SPAN(227) = 642`, `caveat_tag_col(k) = 642 + 1 + 7·k` = 643/650/657/664). Both drift-pin tests
  (`carrier_floor_weld` + `bare_floor_refuse_weld`) green.
- **Column-parametric DEPLOYED soundness — `metatheory/Dregg2/Deos/BareCohortFloorRefuseDeployed.lean`**
  (`#assert_all_clean`, 12 keystones, non-vacuous). Lifts `BareCohortFloorRefuse`'s abstract-column
  (`CARRIER_BASE = 388`, single block) keystone to the **DEPLOYED caveat columns** (`ebDep k = 642 + 1 +
  7·k` = 643/650/657/664) with **three DISJOINT aux blocks** (escrow 17 / discharge 18 / vault 19 at
  `GRAD_ROT_WIDTH(1581) + b·REFUSE_STRIDE(16) + {bit/inv/or/floor}`, mirroring the Rust
  `bare_floor_refuse_weld` deployed alignment EXACTLY — `#guard`s pin 643/650/657/664 + fcDep 1593/1609/
  1625 + 36 disjoint aux cols). `declared_tag_unsat_at` is column-parametric over ANY containing
  descriptor (membership hypotheses), so it composes over the three-block deployed member;
  `declared_{escrow,discharge,vault}_unsat_deployed` are the three closed dodges. **`hbind` is
  dischargeable by the LIVE PI-45 caveat pin** because the tag columns ARE the deployed `caveatCommit`
  columns (not a free assumption). `gentianDeployedBareRefuse d` bakes the traceWidth widening
  (`max d.traceWidth 1626`, `#guard REFUSE_TRACE_WIDTH == 1626`) so the emitted-descriptor SHAPE is
  proven. This is the **true, non-laundered soundness enabler** for the emit-weld: the emit maps THIS
  transformer over `v3RegistryBare`.
- **Crown-wire** — both `BareCohortFloorRefuse` (was reachable only standalone) and the new
  `BareCohortFloorRefuseDeployed` imported into `Dregg2/Deos.lean`; `lake build Dregg2` green (4256 jobs)
  with both axiom-clean in the apex corpus.
- Commits: `carrier_floor_weld` drift fix, `BareCohortFloorRefuseDeployed` add, crown-wire (three
  checkpoints this session).

### 9.2 ⚑ THE GEOMETRY CORRECTION (verified against HEAD — supersedes the "geometry-stable" premise)

`transferVmDescriptor2R24.trace_width == 1581 == GRAD_ROT_WIDTH` (measured in
`circuit/descriptors/rotation-v3-staged-registry.tsv`). The refuse block's DECODE-WITNESS aux columns
(bit/inv/or/floor, ~44 for three disjoint tag blocks) start AT `GRAD_ROT_WIDTH` — i.e. **beyond** every
member's current width. So welding the refuse into the emit is **NOT** a PI-tail-append / geometry-stable
regen: it **widens each cohort member's `trace_width`** (1581 → ~1626). This is the honest flag-day cost —
a per-member geometry widening (the `main` table arity moves), larger than §6's "cheapest class" estimate.
(The escrow SATISFACTION descriptor already paid an analogous widening — `WELD-STATE.md:221-223` B_SPAN
51→119; the bare-cohort refuse pays it across the whole cohort.)

### 9.3 The remaining ordered step (the ember-gated flip — RESUME POINT, grounded 2026-07-05 pt2)

> **RESUME AT STEP 1.** The soundness enabler (§9.1b) is LANDED + green: the deployed-aligned,
> column-parametric refuse transformer `gentianDeployedBareRefuse` (in
> `Dregg2/Deos/BareCohortFloorRefuseDeployed.lean`) is the transformer to map over the cohort — it is
> PROVEN sound at the deployed columns with the traceWidth widening baked in. Steps 1–4 are the
> geometry-cascade grind that reds the apex tree; the ember-gated deploy is Step 5.

1. **Emit weld (STEP 1) — the VK-shape change.** In
   `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean`, change `v3Registry` (def at `:5372`) to
   map each `v3RegistryBare` member through `gentianDeployedBareRefuse` (import
   `Dregg2.Deos.BareCohortFloorRefuseDeployed`). Order: `withDfaRcPins (gentianDeployedBareRefuse d)`
   (the refuse widens traceWidth 1581→1626; `withDfaRcPins` is width-invariant + adds 4 PIs → the
   welded member keeps piCount+4 and width 1626). Do NOT touch the 9 cap-open members
   (`v3RegistryCapOpen` tail at `CapOpenEmit.lean:1280`, widths 1910+) — they are not the bare route and
   their aux would collide (out of task scope).
   - **`#guard` breakage to fix (expected — the flag-day):** `EffectVmEmitRotationV3.lean:5376-5378`
     (`w.traceWidth == b.traceWidth` — now 1626 ≠ 1581, update), `:5382-5385` (piCount guards — recompute
     with the widened width; piCount is UNCHANGED by the refuse, only width moves, so these stay if they
     only check piCount), `:5387` (length 36 — unchanged), and the member-name guards downstream (names
     now carry the `-gentian-deployed-bare-refuse` suffix — either accept the suffix in the guards or add
     it in the expected strings).
   - **G5 free-param binding (the real soundness item at `gentian_discharge_vault_prove.rs:33-35`):**
     bind `PERIOD_COL/AMOUNT_COL/CLOCK_COL` (`discharge_weld.rs:71-75`, today producer-filled FREE) to
     the committed caveat params + `clock` to the published block height via PI/manifest-param pins.
     Mirror for the vault slot params. (This is the discharge/vault SATISFACTION descriptor soundness,
     orthogonal to the bare-refuse; land it alongside.)
2. **Apex cascade re-ground (STEP 1 tail — the multi-run grind).** ⚑ The reference sites (grounded):
   `Dregg2/Circuit/{CircuitSoundnessAssembled,CircuitSoundness,RotatedKernelRefinement,
   RotatedKernelRefinementExercise,RotatedKernelRefinementAttenuate,RotatedKernelRefinementMintBurn}.lean`
   + `Emit/CapOpenEmit.lean` reference `v3Registry`/`v3RegistryBare`. The refinement theorems that state
   "Satisfied2 (member) → genuine kernel step" survive appended constraints IF they drop-extra (a
   satisfying witness of the welded member still satisfies the base gates); the ones that rfl-match the
   EXACT constraint list / `Rfix` position / `traceWidth` need re-grounding. Build the WHOLE tree
   (`lake build Dregg2`), not per-file (the shared-registry red-umbrella hazard). Mirror how v13
   cascaded: bump the offset/position sites as lake surfaces them.
3. **ONE regen (STEP 2).** `scripts/emit-descriptors.sh` → **ALL cohort fingerprints move + every
   `trace_width` moves** (1581→1626). `scripts/check-descriptor-drift.sh` must PASS (`lake build Dregg2`
   then re-emit byte-identical). This re-pins the `*_FP` sha256 constants in
   `circuit/src/effect_vm_descriptors.rs` — the Rust registry FP checks then pass on the new bytes.
4. **Apex re-verify (STEP 4).** `#assert_axioms` clean on
   `ClosureFinal.lightclient_unfoolable_circuit_sound` + `AssuranceCase.deployed_system_secure` + the 5
   guarantees UNDER the widened/welded cohort VKs.
5. **Live-wire routing + producers (STEP 3).** Un-stage `rotated_descriptor_name_for_declared_escrow`
   (`trace_rotated.rs:2343`, currently STAGED `:2338`) + discharge/vault analogs; wire
   `fill_carrier_decode`/`fill_discharge_aux`/`fill_vault_aux` from the live rotated generator so an
   honest declared-capacity turn routes through + proves the SATISFACTION descriptor on the default
   path (the bare member now REFUSES it).
6. **Deploy (STEP 5, ember fires — NOT done):** the re-genesis (`generate.sh --force`) + LC VK
   redistribution (`git push origin main` + client rebuild). Because this moves the deployed-default
   cohort VKs AND every `trace_width`, it IS an eyes-open devnet re-genesis (per `HANDOFF-v13` §1d),
   not a mere staged-add. ember's call.

### 9.3b The anti-launder verification (run after the regen)

After STEP 2 regen, GREP the regenerated `circuit/descriptors/rotation-v3-staged-registry.tsv` for the
refuse columns on every `-v3-staged` cohort row: the floor cols `1593/1609/1625` (the three per-tag OR
terminals) and the `floor==0` refuse gate must be present in the COMMITTED rows (not just Lean). Extend
`bare_floor_refuse_weld.rs`'s forge to assert the DEPLOYED regenerated descriptor's constraint list
CONTAINS the refuse block (parse the emitted JSON, not the synthetic row), so the tooth bites on the
deployed default. The Lean `declared_{escrow,discharge,vault}_unsat_deployed` is the proof; this grep +
forge is the deployed-bytes witness that the flip is real, not staged.

### 9.4 The anti-launder GATE (respected)

The flip is REAL, not laundered: `declared_tag_unsat_under_bare` PROVES the forge is UNSAT on the default
path for every bare member + every capacity tag, and the Rust tooth BITES today. The dodge is closed the
instant the emit-weld + regen land the refuse into the deployed VKs. Until then the deployed descriptors
are byte-identical (STAGED) — the sound core is proven but not yet flipped, and this doc does not claim
otherwise.

### 9.5 Noted pre-existing drift (not this session's)

`circuit/src/effect_vm/carrier_floor_weld.rs:348` pins `caveat_tag_col(0) == 291`, stale at v13 geometry
(the deployed `CAVEAT_BASE` moved to 642 → `caveat_tag_col(0) == 643`). That concrete drift-pin test is
likely RED at HEAD independent of this work; the definitional binding (`caveat_tag_col = CAVEAT_BASE + 1
+ k·ENTRY_SIZE`) is correct. Fix the pin when touching that module.
