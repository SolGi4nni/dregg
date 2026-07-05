# V12 GEOMETRY EPOCH — the bang's final act (design spec)

> **STATUS: SHIPPED — then superseded by v13.** This is no longer a proposal; the v12
> geometry widening LANDED exactly as specced. The three named octets are live in the tree:
> `B_CHILD_VK_OCTET = 88`, `B_CONTRACT_HASH_OCTET = 96`, `B_PUBKEY_OCTET = 104`
> (`circuit/src/effect_vm/trace_rotated.rs`), with producer fill in
> `cell/src/commitment.rs::compute_rotated_pre_limbs` and `turn/src/rotation_witness.rs`
> (child_vk8 on CreateCellFromFactory rows, contract_hash8 on hatchery-mint rows, pubkey8
> unconditionally — O1 resolved as route (a), the turn-level octet). The four per-carrier
> third edges also landed: `metatheory/Dregg2/Circuit/{Factory,Sovereign,Membership,Hatchery}BindingFromFold.lean`
> (+ Bridge/Dsl/Custom/Deco twins) and `Emit/MembershipAuthRootEdge.lean` (the §4 fields
> read-open gadget). HEAD has since grown ONE more accumulator step past v12: the **v13
> fields-octet grow** (`NUM_PRE_LIMBS 112 → 169`, `B_SPAN 151 → 227`, +56 fields[0..7]
> completion lanes + 1 pad limb). So the constant table in §2d below reads at the *pre-v12*
> (v11) geometry — kept for the historical delta it documents; the live values are v13's
> 169/227/169/170/171. Everything under here is preserved as the design rationale of a
> completed epoch.

Status (historical): **DESIGN / SCOPE ONLY** at time of writing. This was the fireable spec for the
one geometry widening that unblocks the four carriers walled by BANG WAVES 1/2/3 +
hatchery-contract. Read alongside `docs/WELD-STATE.md` §1a, §3, §5 items 9/10/11.

The through-line: three carriers (factory, sovereign, membership) + hatchery-contract
are blocked because their third-edge anchors are **not AIR-reconstructable committed
felts** — they are BLAKE3 folds, executor-only recomputes, or zero-defaulted sentinels.
The ONLY sound fix is a geometry widening that surfaces the needed material into the
rotated **pre-limbs** (`compute_rotated_pre_limbs → wireCommitR → state_commit → the
faithful 8-felt commit`) so the deployed AIR can gate carrier teeth against a committed
column. This is the established **v10 (37→67)** / **v11 (67→88)** accumulator-grow
pattern applied one more time.

---

## 1. THE MATERIAL v12 must surface

Each row: the value, its current committed-but-unfaithful (or uncommitted) form at HEAD,
and the faithful AIR target.

| # | material | current form at HEAD (unfaithful) | faithful v12 target | serves |
|---|---|---|---|---|
| M1 | **child_vk[8]** | rotated PI 38 carries `hash_to_bb(owner_pubkey)` under the MISNOMER `child_vk_derived` (`effect_vm_bridge.rs:137-139`); the REAL installed authority `effective_vk` (`apply.rs:2376-2395`, a `[u8;32]` VK hash — Derived/FromSet/Fixed) **never reaches the VmEffect**. Cells leaf is `(key,key)`, 1-felt contents; params carry only param0/param1 (`fold_bytes32_to_bb`, ~31-bit) | `child_vk8 = bytes32_to_8_limbs(effective_vk)` — 8 faithful felts on the CreateCellFromFactory rows | factory + hatchery-invariant (see M-shared) |
| M2 | **contract_hash[8]** | SDK stored-only in `MintedKind::Attested{contract_hash:[u8;32]}` (`hatchery_mint.rs:182`); read by **zero** AIR constraints, off-VK | `contract_hash8 = bytes32_to_8_limbs(contract_hash)` — 8 faithful felts on the hatchery-mint rows | hatchery-contract |
| M3 | **owner/actor pubkey[8]** | committed ONLY via BLAKE3 folds: `compute_authority_digest_8` = `blake3(residue⊇public_key)` (`commitment.rs:849`) + whole-state BLAKE3 (`:209`); **0 hits** for `pubkey` in `trace_rotated.rs`. Membership's `compress(sender_pubkey)` (`membership_verifier.rs:143`, 1-felt `hash_many`) is likewise absent | `pubkey8 = bytes32_to_8_limbs(pubkey)` — 8 faithful felts (raw key limbs, not a pre-hashed fold) | sovereign (owner key) + membership (sender key) — **see open-question O1** |

**M-shared (hatchery-invariant):** `invariant_digest === child_program_vk === factory's
child_vk` (WELD-STATE §3 hatchery-invariant row). So M1 double-serves — hatchery-invariant
gates the SAME `child_vk8` octet on the CreateCellFromFactory leg it already rides. **No
extra material.**

**NOT geometry material (assessed, do NOT add a pre-limb):**

- **membership `authorized_root`** — `root_felt_from_slot(fields[set_root_index])`. This
  is a READ out of the per-cell field map, and `fields_root` (block limb **36**,
  `B_FIELDS_ROOT`) is **ALREADY a deployed-faithful 8-felt root** (`effFieldsWriteV3` /
  `FieldsOpenEmit`, WELD-STATE §1b, Rfix 39). Binding the authorized-root needs an
  **in-AIR fields-map READ-open** at `set_root_index` against the committed `fields_root`
  — the same open mechanism `FieldsOpenEmit` already provides, in a read variant. This is
  a **separate gadget build, NOT a v12 pre-limb add.** v12 surfaces only the SENDER (M3);
  the ROOT is closed by an in-AIR open against material that is already committed.

- **bridge `mint_hash` / 26-limb tuple** — genuinely uncommitted, but the sound path is
  re-proving the REAL foreign note-spend STARK as a foldable G2 leaf
  (`note_spend_leaf_adapter.rs`, new) + recompute `mint_hash` in-circuit + expose a
  `mint_hash` PI on `mintV3`. That is a **terminal own-lane build, orthogonal to geometry**
  (folding `bridge_action_air` is UNSOUND). v12 does not touch bridge.

So the geometry payload is exactly **M1 + M2 + M3 = three 8-felt octets** (child_vk,
contract_hash, pubkey), each filled on the rows of the effect that owns it and inert-zero
elsewhere (the v11 completion-limb discipline).

---

## 2. THE GEOMETRY CASCADE (88 → N, B_SPAN, the constants)

### 2a. The confirmed geometry formula (verified against v9/v10/v11)

A rotated block = `NUM_PRE_LIMBS` pre-iroot limbs + iroot (1) + state_commit (1) + the
chained-absorption intermediate carriers. The chain is a **4-wide head** (limbs 0..3) +
**3-wide groups** over the remainder + 1 carrier for the iroot absorption, requiring
`(NUM_PRE_LIMBS − 4) ≡ 0 (mod 3)` to avoid an arity-2 leftover (the invariant v11
explicitly preserved — `trace_rotated.rs:92-96`).

```
chain_carriers = (NUM_PRE_LIMBS − 4)/3 + 1
B_SPAN         = NUM_PRE_LIMBS + 2 + chain_carriers
               = NUM_PRE_LIMBS + 3 + (NUM_PRE_LIMBS − 4)/3
```

Checks: v9 N=37 → B_SPAN 51 ✓ · v10 N=67 → 91 ✓ · v11 N=88 → 119 ✓.

### 2b. v12 primary (three named octets, +24)

`NUM_PRE_LIMBS 88 → 112` (`+24 = M1[8] + M2[8] + M3[8]`). `112 − 4 = 108 = 36×3`
(clean, **no pad needed**).

```
chain_carriers = 108/3 + 1 = 37
B_SPAN         = 112 + 3 + 36 = 151        (119 → 151)
B_IROOT        = 112                        (was 88)
B_STATE_COMMIT = 113                        (was 89)
B_CHAIN_BASE   = 114                        (was 90; 37 sites at 114..150)
```

New pre-limb offsets (append AFTER the v11 accumulator completion at 67..87):

```
B_CHILD_VK8      = 88..95   (M1, filled on CreateCellFromFactory rows)
B_CONTRACT_HASH8 = 96..103  (M2, filled on hatchery-mint rows)
B_PUBKEY8        = 104..111 (M3, filled on sovereign/membership actor rows)
```

That the +24 lands exactly on a `÷3` boundary (108) is a nice confirmation the three-octet
payload is the "right" clean number — it mirrors the factory §5-item-9(a) per-material
estimate ("+8 → 96") summed over the three walled materials.

### 2c. v12 compaction option (ONE shared octet, +9)

Because a rotated block commits exactly one cell's one effect, M1/M2/M3 are **mutually
exclusive per row** (a factory-birth row, a hatchery-mint row, and a sovereign/membership
actor row are disjoint). They could share ONE `B_CARRIER_MATERIAL8` octet, selector-routed
by the committed effect discriminant. `+8` alone gives 96 (96−4=92, not ÷3), so pad +1 →
**N=97, B_SPAN 131** (`93/3+1=32` carriers). Saves 15 trace columns per block ×2 blocks +
chain, at the cost of three selector-gated in-AIR recompute gates reading one shared octet.
**Recommendation: use the primary (+24) three-octet layout** — each material has a fixed
home and each gate is unconditional per-descriptor, which is more auditable under the
anti-vacuity discipline. Offer the shared octet only if ember wants the narrower trace.

### 2d. The constant/file carriers (where the geometry lives)

*(the "pre-v12" column below is the v11 geometry this epoch started from; the "v12 value"
column is what this epoch shipped. HEAD is now v13 — `NUM_PRE_LIMBS 169`, `B_SPAN 227`,
`B_IROOT 169`, `B_STATE_COMMIT 170`, `B_CHAIN_BASE 171` — one accumulator step further.)*

| constant | pre-v12 (v11) value | file:line | v12 value (primary) |
|---|---|---|---|
| `NUM_PRE_LIMBS` | 88 | `circuit/src/effect_vm/trace_rotated.rs:90` | 112 |
| `B_SPAN` | 119 | `trace_rotated.rs:97` | 151 |
| `B_IROOT` | 88 | `trace_rotated.rs:166` | 112 |
| `B_STATE_COMMIT` | 89 | `trace_rotated.rs:168` | 113 |
| `B_CHAIN_BASE` | 90 | `trace_rotated.rs:170` | 114 |
| `AFTER_BASE` | `V1_WIDTH+B_SPAN` (237) | `trace_rotated.rs:175` | derived (`186+151=337`) |
| `CAVEAT_BASE` | `V1_WIDTH+2·B_SPAN` (287) | `trace_rotated.rs:177` | derived (`186+302=488`) |
| `V9_NUM_PRE_LIMBS` | 88 | `cell/src/commitment.rs:702` | 112 |
| (twin) `NUM_PRE_LIMBS` | 88 | `turn/src/rotation_witness.rs:67` | 112 |
| `B_SPAN` (Lean) | 119 | `metatheory/…/Emit/EffectVmEmitRotationV3.lean:162` | 151 |
| `B_IROOT` (Lean) | 88 | `EffectVmEmitRotationV3.lean:179` | 112 |
| `B_STATE_COMMIT` | 89 | `EffectVmEmitRotationV3.lean:181` | 113 |
| `preLimbsAt_length` | 88 | `EffectVmEmitRotationV3.lean:242` (`rfl`) | 112 |
| `#guard B_SPAN == B_IROOT+31` | 31 | `EffectVmEmitRotationV3.lean:215` | `+39` (2+37) |
| `rotV3SitesAt` / `rotV3WidePin` | 30 sites | `EffectVmEmitRotationV3.lean:264,314` | +N sites (per-limb hash chain grows) |

The Rust producers that FILL the pre-limbs (the two flat-record twins, currently
zero-filling 67..87 per the v11 discipline): `cell/src/commitment.rs::compute_rotated_pre_limbs`
and `turn/src/rotation_witness.rs`. v12 adds M1/M2/M3 fill logic here (and the circuit
trace producers in `trace_rotated.rs` fill the genuine columns on the applicable rows).

---

## 3. THE BLAST RADIUS — ordered steps (mirroring the v10/v11 template)

The exact template is **v10 = `44ee7b604`** (a single 13-file geometry monolith) followed
by the v11 span **`8535635cf → 85a163c18 → e74b8fadd → cbaf7b05b → … → 980b46cef`**
(geometry re-lay → producer node8 fill → apex forcing → registry regen → FP re-pins). v12
is the SAME shape with a larger payload. Ordered:

**STEP 1 — geometry re-lay (the monolith, one file group; template `44ee7b604` / `8535635cf`).**
Move every geometry constant 88→112 / B_SPAN 119→151 and cascade the offsets. Files
(exactly the set v10/v11 moved — grounded via `grep '119\|B_SPAN' metatheory/Dregg2/Circuit/`):
- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` — the monolith: `B_SPAN`,
  `B_IROOT`, `B_STATE_COMMIT`, `preLimbsAt` (+3 octets, `preLimbsAt_length` rfl → 112),
  `rotV3SitesAt` + `rotV3SitesAt_pin` re-proved (grow the site list), `rotV3WidePin`,
  `colOnly`/`graduable` rcases (N-way), the `#guard`s, `maxRecDepth` bump for the wider rfl.
- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationWide.lean` — the wide parallel re-lay.
- `metatheory/Dregg2/Circuit/Emit/{CapOpenEmit,CapInsertEmit,CapRemoveEmit,AccumulatorOpenEmit,AccumulatorInsertEmit,FieldsOpenEmit,HeapOpenEmit}.lean`
  — every after-spine keystone splices at `w + 119`; each `+119 → +151`.
- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitUMemWeldWide.lean` — wide umem weld offsets.
- `metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean` — heapWrite splice AFTER-block `+119→+151`.
- `metatheory/Dregg2/Circuit/CircuitCompletenessNonVacuityReal.lean` — concrete witness AFTER cols / omega hyps / base.
- `metatheory/Dregg2/Circuit/Satisfied2FaithfulActive.lean` — the v10-touched consumer.
- `metatheory/Dregg2/Deos/SettleEscrowSatWideDescriptor.lean` — escrow wide-descriptor (the `956b8be93` drift twin; do it IN the monolith this time, not as a lagging fix).
- `circuit/src/effect_vm/trace_rotated.rs` — the Rust consts (§2d) + the wide-delta literals (`+480→+…`, carrier-count messages).
- `cell/src/commitment.rs` + `turn/src/rotation_witness.rs` — the `V9_NUM_PRE_LIMBS`/`NUM_PRE_LIMBS` twin consts.
- `circuit/src/effect_vm_descriptors.rs` — the two stale "67"/"37" prose comments (kill them).

New octets **inert ZERO** at this step (genuine producers are STEP 2). Checkpoint: `lake
build Dregg2` `#assert_axioms`-clean + all rotated Rust suites green at the new geometry
(v11's STEP-1-COMPLETE bar). **Mechanical** — same files, same proofs, wider numbers.

**STEP 2 — producer fill (template `e74b8fadd`/`cbaf7b05b`).** Fill M1/M2/M3 into the new
limbs: the circuit trace producers in `trace_rotated.rs` write the genuine
`bytes32_to_8_limbs(effective_vk / contract_hash / pubkey)` on the applicable rows; the two
flat-record twins (`commitment.rs::compute_rotated_pre_limbs`, `rotation_witness.rs`) fill
the same. Wire `effective_vk` THROUGH the bridge to the VmEffect (fix the
`effect_vm_bridge.rs:137` misnomer: either carry the real vk or rename the vm-key field —
WELD-STATE §5-item-9 second divergence). Add the `bytes32_to_8_limbs` map-op fill. The
degraded-felt gate (`.ast-grep/rules/faithful-commitment-felt.yml`) must stay green (these
are faithful 8-felt, not folds).

**STEP 3 — apex forcing + the three registry regens (template `39a026351`/`980b46cef`
+ `824c2963e`/`ce511ac8b` FP re-pins).** Regenerate ALL THREE registries + the transfer
twin — every rotated descriptor's `trace_width`/`b_span` moves:
- `circuit/descriptors/rotation-v3-staged-registry.tsv` (**58** descriptors)
- `circuit/descriptors/rotation-wide-registry-staged.tsv` (**57**)
- `circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv` (**57**)
- `circuit/descriptors/rotation-wide-transfer-staged.tsv` (transfer twin)

≈ **172 descriptors move**. Re-pin the fingerprints (FP re-pin). Re-verify the apex:
`CircuitSoundnessAssembled.lean` — the six-root `Rfix` pins (17/27/28/39/56/12 + the
cap-write family) re-ground at the new widths; `lightclient_unfoolable` + the 5
`AssuranceCase` guarantees + `deployed_system_secure_grounded` clean under the new VKs.
**The keystone re-proof is MECHANICAL** (as in v11): no NEW keystone is needed for the
geometry itself — the pre-limbs absorb into the SAME `wireCommitR` chain, so the existing
`preLimbsAt`/`rotV3SitesAt` machinery just grows. NEW keystones are needed only for the
per-carrier GATES (STEP 5), not for the widening.

**STEP 4 — the wide/welded descriptor re-weld + host-width fixes (template
`19c8b78e1`/`d99837ca9`/`52ed38d40`).** Fix the stale fields/heap-family host widths + the
geometry-grow delta across the wide + umem-welded descriptors; bump `setFieldDyn` and the
capacity-weld descriptor widths to the new B_SPAN geometry (the `52ed38d40 801→955`
equivalent). Escrow floor (`SettleEscrowSatWideDescriptor`) already handled in STEP 1.

**STEP 5 — the per-carrier THIRD EDGE (now mechanical — see §4).** Only NOW that each
material is a committed pre-limb do the four carriers get their gates. Each is a
per-descriptor `public_input_count` bump + an in-AIR gate to the new committed limb + the
leaf dual-expose + fold tooth + `BackingAttack → BindingFromFold` flip.

**STEP 6 — devnet re-genesis.** Commitment VALUES shift (the pre-limb vector grew), so the
deployed default rotates once (gated human-go) + devnet re-genesis. Same as every prior
geometry epoch.

**Blast summary:** ~13-15 Lean files (the fixed geometry-consumer set), ~172 descriptors
regenerated across 3 registries + transfer twin, 3 FP re-pins, one apex re-verify, one
devnet re-genesis. **The geometry re-lay + regen + apex re-verify is MECHANICAL** (v11 did
it in a bounded WIP span, RED-between-checkpoints); the NOVEL work is the four per-carrier
gates in STEP 5 (each a small new keystone — see §4).

---

## 4. THE PER-CARRIER THIRD EDGE AFTER v12 (each becomes class-1-style)

Once the material is a faithful pre-limb, the third edge is the uniform 5-step build
(WELD-STATE §4). Per carrier:

- **factory** — PI-emit at TAIL `[FACTORY_PI_LO..+8)` = `child_vk8`; in-AIR gate
  `emitted_PI[i] == pre_limb(B_CHILD_VK8 + i)` on the CreateCellFromFactory descriptor
  (direct equality — the material is already the 32B VK's 8 limbs, no hash gate needed);
  leaf dual-expose via `prove_descriptor_leaf_dual_expose_at` (done, parametric); fold tooth
  (twin of `custom_binding_deployed_tooth.rs`); flip `FactoryBackingAttack → FactoryBindingFromFold`.
  **Class-1 post-v12.** ⚑ still kill the `child_vk_derived` misnomer in STEP 2.

- **hatchery-invariant** — RIDES factory's leg + gates the SAME `child_vk8` octet
  (`invariant_digest === child_vk`) + one extra connect to the contract-attestation leaf.
  **Shares factory teeth; class-1 post-v12.**

- **hatchery-contract** — PI-emit `contract_hash8` at TAIL on the hatchery-mint (Factory)
  descriptor; in-AIR gate against `B_CONTRACT_HASH8` (direct equality); leaf/tooth/flip.
  **Class-1 post-v12** (was DEEPEST only because the material was uncommitted; v12 commits it).

- **sovereign** — PI-emit `KEY_COMMIT` teeth (the existing 4-felt `SOVEREIGN_WITNESS_KEY_COMMIT`
  cols, `columns.rs:274`); in-AIR gate `Poseidon2(B_PUBKEY8) == KEY_COMMIT`, `IS_SOVEREIGN_CELL`-gated
  → forged key UNSAT. **This gate needs a Poseidon2-over-8-limbs sub-gate** (the material is
  raw pubkey limbs; the teeth are its compression). That Poseidon2 gate is a small NEW
  keystone but reuses the deployed node8/`CHIP_RATE 16` primitive. P1 (fill the dead-zero
  teeth from `before_cell.public_key()`) + P2 (the gate) now fire TOGETHER — no laundered
  vacuity. Ed25519 stays off-AIR. Flip `SovereignBackingAttack → SovereignBindingFromFold`.
  **Class-1 post-v12 modulo the one Poseidon2 sub-gate.**

- **membership** — TWO endpoints: (i) SENDER: PI-emit + in-AIR gate
  `compress(B_PUBKEY8) == leaf` (compress = 1-felt `hash_many` → a Poseidon2 sub-gate, same
  as sovereign, reuses node8); (ii) ROOT: the in-AIR **fields-map READ-open** at
  `set_root_index` against the committed `fields_root` (limb 36) — reuses `FieldsOpenEmit`,
  NOT geometry. Both close together; flip `MembershipBackingAttack → MembershipBindingFromFold`.
  **Class-1 post-v12 modulo the compress sub-gate + the fields read-open gadget.**

Note: factory + hatchery gates are **direct-equality** (material is already hashed);
sovereign + membership gates need **one Poseidon2 sub-gate** each (raw key → its
compression), both riding the existing node8 primitive. Bridge is untouched by v12 (own
note-spend-STARK lane).

---

## 5. OPEN QUESTIONS / RISKS

- **O1 (the pubkey-role question — needs an ember/design call).** Sovereign's material is
  the OPERATED CELL's owner key (`before_cell.public_key()`, per-block). Membership's is
  the TURN ACTOR's key (`InputRef::Sender → sender_pk`, turn-level). These are **different
  roles** and NOT definitionally the same felt (they coincide for a sovereign self-turn,
  which authorization already forces, but a Hosted-cell membership check has an arbitrary
  turn sender). Resolution options: (a) surface ONE `pubkey8` as **turn-level actor context**
  absorbed into each block (like `cells_root`/`iroot`), letting both gates recompute their
  respective compressions — cleanest, one octet; (b) surface owner-key (per-block) AND
  sender-key (turn-level) as TWO octets (+8 → 120; note `120−4=116` is NOT ÷3, so pad to
  121). **Recommend (a)** unless membership must bind a sender distinct from the block's
  cell owner in a case that matters. Flag for ember.

- **O2 (compress-in-AIR vs raw-limb match).** Surfacing the RAW pubkey limbs (not the
  pre-hash) is correct: it lets the in-AIR gate recompute `Poseidon2/compress(pubkey8)` and
  match the teeth, which is what makes a forged key UNSAT. Committing the pre-compressed
  1-felt instead would re-introduce the vacuous self-pin (the teeth == the committed value,
  both prover-adjacent). So **raw pubkey8 + an in-AIR compress gate** is the sound choice,
  not "commit the 1-felt compress." The compress gate is a Poseidon2 sub-gate over node8 —
  small, non-novel.

- **O3 (authorized_root is a DIFFERENT mechanism, confirmed).** It is a **pre-limb-add? NO
  — an in-AIR fields_root READ-open.** `fields_root` is already a committed-faithful root;
  the authorized-root felt is a map value under it. So membership's root anchor rides the
  existing `FieldsOpenEmit` open family, not the geometry. v12 must NOT waste a pre-limb on
  it. (This is the assessment the task asked for.)

- **O4 (a genuine terminal seam that geometry CANNOT fix).** **Bridge's foreign note-spend**
  cannot be made faithful by widening — its authority lives in an external STARK, not in
  dregg committed state. It requires re-proving the real note-spend STARK as a foldable
  leaf (own lane). Geometry surfaces dregg-owned material only. Also **in-AIR Ed25519**
  (sovereign route (b)) stays a named terminal crypto seam — v12 route (a) sidesteps it by
  committing the key and gating `Poseidon2(key)==teeth`, but the SIGNATURE itself remains
  off-AIR (verified in `authorize.rs`), which is the accepted design (the gate binds the
  key, the executor binds the sig).

- **R1 (regen scale / clobber).** Three registries + ~172 descriptors move; this is a
  main-loop-owned quiet-window operation (shared-manifest clobber hazard). Do STEP 1+3 in
  one uninterrupted span (v11 ran RED-between-checkpoints on a WIP branch — acceptable per
  the memory's WIP discipline).

- **R2 (do NOT run any per-carrier STEP 5 gate before STEP 1-3 land).** Firing a gate
  against an inert-zero limb, or flipping a `BackingAttack` before the material is filled +
  committed, launders vacuity (the fail-open law). Order is load-bearing.

---

## 6. SIZE ESTIMATE

**Multi-day epoch, but MOSTLY MECHANICAL** — the same shape as v11 (which was a bounded
WIP span of ~15 commits over ~1 day of geometry + producer + apex + regen). Breakdown:

- STEP 1-4 (geometry re-lay + producer fill + regen + apex re-verify): **MECHANICAL**,
  ~1-1.5 days. Same files, same proofs, wider numbers. No new keystone for the widening
  itself — the pre-limbs absorb into the existing `wireCommitR` chain. This is the
  well-worn v10/v11 groove.
- STEP 5 (four per-carrier third edges): the NOVEL work, but each is small and mostly
  shared. Factory + hatchery-contract + hatchery-invariant = direct-equality gates (~0.5
  day each, and hatchery-invariant rides factory). Sovereign + membership need one
  Poseidon2 compress sub-gate each (reusing node8) + membership needs the fields read-open
  gadget (~1 day each). ≈ **2-3 days** for STEP 5 across the four carriers.
- STEP 6 (devnet re-genesis): a few hours, gated.

**Total: a ~4-5 day epoch, ~70% mechanical geometry re-lay + regen (novel-risk-free, the
established pattern) and ~30% genuinely new per-carrier gate keystones (small, node8-reusing,
non-novel-crypto).** No new cryptographic primitive is introduced; no terminal seam is
crossed (bridge + Ed25519-sig stay in their named off-AIR lanes). This is fireable as ONE
coordinated epoch or handed to ember for a route (primary +24 vs shared +9; O1 pubkey-role)
greenlight before STEP 1.

---

## 7. ONE-SCREEN SUMMARY (for the greenlight ask)

- **What:** widen the rotated pre-limbs `88 → 112` (B_SPAN `119 → 151`) to surface three
  faithful 8-felt octets — `child_vk8`, `contract_hash8`, `pubkey8` — so the deployed AIR
  can gate factory / hatchery-contract / hatchery-invariant / sovereign / membership teeth
  against committed material instead of BLAKE3 folds, executor-only recomputes, and
  zero-defaulted sentinels.
- **Why now:** BANG WAVES 1/2/3 all stopped on the SAME wall — "no AIR-reconstructable
  committed anchor." This is the shared unblock. `authorized_root` (in-AIR fields-open) and
  `bridge` (note-spend STARK) are NOT geometry and stay in their own lanes.
- **Cost:** the v10/v11 groove — ~15 Lean/Rust geometry files, 3 registry regens (~172
  descriptors), 1 apex re-verify, 1 devnet re-genesis. Mechanical.
- **Decisions ember owns:** (1) primary +24/three-octet vs compaction +9/shared-octet;
  (2) O1 — one turn-level `pubkey8` (recommend) vs separate owner+sender octets;
  (3) greenlight the re-genesis.
- **After:** all four walled carriers become class-1-style third-edge builds; only bridge
  (own lane) + the deeper custom per-turn VK epoch remain before the coordinated bang.
