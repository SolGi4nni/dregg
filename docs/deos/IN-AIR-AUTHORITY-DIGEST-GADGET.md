# The in-AIR authority-digest → selector forcing gadget (GENTIAN KEYSTONE)

This is the design for the **terminal blocker** of the sealed-escrow VK flip (and the whole
house-capacity weld class): the in-AIR recomputation of `compute_authority_digest_felt` over the
witnessed declaration, the required-tag decode, and the selector-forcing constraint that makes a
**pure light client** — holding only the commit — demand the capacity selector with no opt-in.

It is the realization, in-AIR, of the `hverifier` obligation that
`metatheory/Dregg2/Deos/SettleEscrowSelectorBinding.lean`
(`escrow_selector_bound_to_declaration`) leaves as an explicit verifier discipline hypothesis.

## 1. What is already true (the fulcrum this stands on)

Three pieces are proven and (for the carrier) deployed:

* **COVERAGE** is pure-light-client-witnessed. The capacity manifest rides the AIR-bound rotated
  carrier (`caveatCommit` → PI), so omission is impossible for a light client binding the wide
  commit (`Dregg2.Deos.CapacityCarrier`, deployed). A declared escrow entry cannot be dropped.
* **SATISFACTION soundness + its in-AIR gates** are proven and built. The four selector-gated
  equality gates `sel · (col − const) == 0` over the rotated BEFORE/AFTER field columns force the
  sealed-escrow `SettleFieldGate` over the committed state
  (`Dregg2.Deos.CapacitySatisfaction.satisfaction_witnessed`,
  `circuit/src/effect_vm/satisfaction_weld.rs`).
* **The WIDE fulcrum.** The welded descriptor's satisfaction-gate field columns are graduated into
  the ~124-bit wide commit a pure light client binds
  (`Dregg2.Deos.SettleEscrowSatWideDescriptor`, `beforeFieldCol_absorbed` / `afterFieldCol_absorbed`):
  the columns `bb + 4 + k` lie inside the 37 pre-iroot limbs the wide carriers consume, so
  `rotV3Wide_binds_published` (under `Poseidon2WideCR`) binds them.

The **one remaining gap**: the satisfaction gates are *selector-gated*. They bite only when the
capacity selector `sel` (`ESCROW_SEL_COL`) is `1`. A forger settling a half-open escrow dodges the
weld by simply setting `sel = 0` — UNLESS the selector is **forced on** for any cell whose committed
declaration requires the escrow capacity. `SettleEscrowSelectorBinding.lean` proves the forcing
*given* a verifier that pins `ESCROW_SEL_PI = 1` whenever the re-derived required-tag floor demands
the escrow selector — but a **pure light client holds only the commit, not the declaration
preimage**, so it cannot perform that re-derivation off-band. The forcing must be moved IN-AIR.

## 2. The recipe to recompute (`compute_authority_digest_felt`)

The committed declaration is *already* bound into the wide commit. `cell/src/commitment.rs::
compute_authority_digest_felt` folds the authority residue — including `cell.program`, hence the
`Predicate`/`Cases` `state_constraints` that carry the capacity declaration — into a single felt:

```
authDigest = hash_bytes( b"dregg-cell:v9-authority-digest v1"
                         ‖ identity ‖ mode ‖ permissions ‖ vk ‖ delegate ‖ delegation
                         ‖ program(postcard(state_constraints)) ‖ fields[8..16]
                         ‖ visibility ‖ commitments ‖ proved ‖ side-table-roots )
```

That felt is `pre[24]` = the `B_AUTHORITY_DIGEST` rotated limb (r23), absorbed into the wide
commit (`compute_rotated_pre_limbs`). A pure light client binds `authDigest` via
`rotV3Wide_binds_published`, but it does **not** hold the byte preimage. So to make the selector
demand un-dodgeable in-AIR, the AIR must, over a *witnessed* declaration:

1. **Recompute** `authDigest` in-AIR from the witnessed declaration bytes (the `hash_bytes` sponge).
2. **Bind** the recomputed digest equal to the committed `B_AUTHORITY_DIGEST` limb (col `bb + 24`,
   wide-bound). Under collision-resistance this forces the witnessed declaration to be the committed
   one (or, weaker but sufficient: to have the same required-tag floor — exactly `DeclCommitBinds`).
3. **Decode** the required-tag floor from the witnessed declaration (`required_capacity_caveat_tags`
   in-AIR) into a boolean `floorHasEscrow` column.
4. **Force** the selector: `floorHasEscrow · (sel − 1) == 0`. When the floor includes escrow,
   `sel` is forced to `1`, lighting the satisfaction gates; when it does not, the gate is inert.

This is the GENTIAN gadget. It removes the last caller-asserted input (`hverifier` / the off-band
`required_tags`), discharging the obligation for a **pure light client**.

## 3. The gadget structure (degree-2 gates + the recompute chain)

The four constraints split cleanly into a **proven-now equality skeleton** and a **named recompute
chain**:

| Constraint | Shape | Status |
|---|---|---|
| (1) recompute-bind | `witDigestCol − authDigestCol == 0` | gate proven-now |
| (2) decode-boolean | `floorCol · (floorCol − 1) == 0` | gate proven-now (subsumed by the is-zero gadget below) |
| (3) selector-force | `floorCol · (sel − 1) == 0` | gate proven-now |
| (4a) recompute chain | `witDigestCol == hash_many(witnessed floor)` | **DISCHARGED (Option B)** — a felt-domain chip lookup, sound by `chip_lookup_sound` against `ChipTableSound` |
| (4b) decode soundness | `floorCol == (escrow ∈ witnessed floor)` | **DISCHARGED** — the in-AIR is-zero + OR-fold gadget, pure field arithmetic, no floor |

**DISCHARGE STATUS (Option B realized).** Both named-modeled hypotheses are now PROVEN gates, so the
selector forcing holds for a pure light client under ONLY two named CR floors (`ChipTableSound` +
`FloorDigestBinds`), with NO off-band `hverifier`/`hrecompute`/`hdecode`:

  * **`hdecode` DISCHARGED** by the in-AIR DECODE gadget. The witnessed required-tag floor rides
    fixed-arity felt columns `[F0, F1]` (arity 2 ≤ `CHIP_RATE`, the representative; the chip lookup is
    fixed-arity so more slots repeat the same gadget). For each slot a degree-2 is-zero gadget —
    defining gate `b_k + (F_k − 17)·inv_k − 1 == 0` plus forcing gate `(F_k − 17)·b_k == 0` — forces
    `b_k = (F_k == 17)` over the integral domain; the OR-fold `floorCol − (b0 + b1 − b0·b1) == 0`
    forces `floorCol = (escrow ∈ floor)`. The floor column IS the decoded floor by construction —
    pure arithmetic, NO crypto floor.
  * **`hrecompute` DISCHARGED** by the recompute chip lookup. A poseidon2 chip `Lookup` whose digest
    column is `witDigestCol` and whose inputs are the floor columns is forced by the deployed lever
    `DescriptorIR2.chip_lookup_sound` (against `ChipTableSound`, the deployed chip faithfulness) to
    carry `witDigestCol = hash_many(floor)` — the felt-domain Option-B floor digest. The recompute-bind
    gate (1) ties it to the committed `B_AUTHORITY_DIGEST` limb (read, under Option B, as that same
    felt-domain floor digest, wide-bound by `gentian_auth_digest_absorbed`). `FloorDigestBinds` (equal
    floor digests ⟹ equal floors — the felt analog of `ConstraintBinding.DeclCommitBinds`) then forces
    the witnessed floor equal to the committed one.

The discharged keystones are `Dregg2.Deos.InAirAuthorityDigestGadget.gentian_selector_forced_discharged`
/ `gentian_settle_forced_discharged` (+ `recompute_discharged`, `decode_discharged`, the
partial/phantom UNSAT teeth), `#assert_all_clean` (13 keystones), no off-band hypothesis. Rust shadow:
`circuit/src/effect_vm/authority_digest_weld.rs` (`gentian_decode_gates`, `gentian_recompute_lookup`,
`gentian_gadget_constraints`, `gentian_decode_witness` + the producer teeth).

Constraints (1)(2)(3) are ordinary `VmConstraint::Gate` polynomials of degree ≤ 2 — the SAME
vocabulary the satisfaction weld uses — over three columns:

* `authDigestCol = BEFORE_BASE + B_AUTHORITY_DIGEST` (col 212 = `EFFECT_VM_WIDTH` 188 + 24; Lean `EFFECT_VM_WIDTH + 24`): the
  committed r23 limb, wide-bound (`gentian_auth_digest_absorbed`).
* `witDigestCol = PARAM_BASE + 3` (col 71): the recompute output, a free param the producer fills.
* `floorCol = PARAM_BASE + 4` (col 72): the decoded `floorHasEscrow` bit, a free param.

(`ESCROW_SEL_COL = PARAM_BASE + 2`, col 70, the existing satisfaction selector.)

The forcing chain, given the committed declaration requires escrow:

```
authDigestCol = authDigest(committed)              -- committed limb, wide-bound
witDigestCol  = authDigestCol                       -- gate (1)
witDigestCol  = authDigest(witnessed)               -- recompute (4a)
⟹ authDigest(witnessed) = authDigest(committed)
⟹ required(witnessed) = required(committed)         -- DeclCommitBinds (the CR floor)
⟹ escrow ∈ required(witnessed)                      -- hreq
⟹ floorCol = 1                                      -- decode (4b)
⟹ sel − 1 = 0  ⟹  sel = 1                           -- gate (3)
⟹ the four satisfaction gates bite                  -- settleEscrowWide_forces_settle_gate
```

So a satisfying proof of the gentian descriptor on a cell declaring the escrow capacity has the
sealed-escrow gate forced over the committed state — **un-dodgeably, for a pure light client**, with
the *only* crypto floor being `DeclCommitBinds` (the authority-digest collision-resistance, the same
shape as the `Poseidon2WideCR`/`Poseidon2SpongeCR` floors the deployed wide commit already carries).

## 4. The hard part — the recompute chain (4a) and decode (4b)

(1)(2)(3) are expressible and proven in the current IR. (4a) is the genuinely hard remaining piece:
`compute_authority_digest_felt` is `hash_bytes` over a **variable-length postcard-serialized blob**.
The current descriptor IR has a Poseidon2 **chip table** (`TID_P2` / Lean `poseidon2ChipTableDef`)
that constrains a single fixed-arity permutation per lookup row (`chip_lookup_sound_N`), and the
wide commit's chained `wire_commit_8_chip` is built from those lookups over **felt-domain** limbs.
It does **not** have a constraint vocabulary for byte-to-felt packing + a rate-aware,
variable-length sponge-absorption state machine. Two sound realizations:

* **Option A — the literal byte-sponge.** Add a new constraint variant (a `ByteHashChain` /
  sponge-absorb) or a custom byte-sponge table the descriptor `Lookup`s into, recomputing
  `hash_bytes` over the witnessed declaration bytes exactly. This is new IR machinery AND new VK
  bytes. It recomputes the EXACT deployed `authDigest` over the existing r23 limb.

* **Option B — the felt-domain restructure (recommended).** Commit a small **felt-domain
  required-floor digest** as a dedicated rotated limb (the way `perms_digest`/`vk_digest` already
  ride limbs 33/34 — `compute_rotated_pre_limbs`), computed via felt-domain `hash_many` over the
  decoded required-tag floor. The in-AIR recompute is then a **fixed-arity felt-domain chip
  lookup** — expressible with the EXISTING chip machinery (`chip_lookup_sound_N`) — and the decode
  (4b) becomes felt arithmetic over that limb, not a byte parse. This is a flag-day VK bump (a new
  committed limb) but reuses the deployed IR; it is the lower-risk, lower-novelty path and the one
  the rest of the rotated commitment already follows for authority sub-state.

Either way (4a)+(4b) are **VK-affecting** and STAGED. The first proven rung (this pass) establishes
the equality skeleton (1)(2)(3) + the forcing composition under the CR floor — the soundness core —
so that whichever recompute realization lands, the selector forcing is already proven sound.

## 5. The first proven rung (this pass)

`metatheory/Dregg2/Deos/InAirAuthorityDigestSelector.lean` (`#assert_all_clean`):

* `gentianSelectorDescriptor legA legB` — the WIDE welded descriptor
  (`settleEscrowSatVmDescriptor2R24Wide`) PLUS the three gentian gates (1)(2)(3).
* `gentian_auth_digest_absorbed` — the committed `B_AUTHORITY_DIGEST` limb (col `EFFECT_VM_WIDTH + 24`)
  is inside the 37 pre-iroot BEFORE limbs the wide carriers absorb (`24 < 37`), so a pure light
  client binding the wide commit binds it (the same `rotV3Wide_binds_published` chain
  `beforeFieldCol_absorbed` uses).
* `gentian_gate_holds` — a generic helper: any gate of the gentian descriptor vanishes on a
  satisfying non-last row (the `Satisfied2.rowConstraints` reduction).
* **`gentian_selector_forced`** — the keystone: under `DeclCommitBinds`, a committed declaration
  requiring escrow + the in-AIR recompute-bind gate (1) + the recompute/decode faithfulness of the
  witnessed columns forces `sel = 1`. **No off-band `hverifier`.**
* **`gentian_settle_forced`** — composes the forced selector with the welded satisfaction gates:
  the four sealed-escrow conjuncts (`Deposited` before / `Consumed` after) are forced over the
  committed wide-bound columns. This reaches the SAME conclusion as
  `escrow_selector_bound_to_declaration` **without** the `hverifier` hypothesis — the discharge.
* `gentian_partial_unsat` / `gentian_phantom_unsat` — the teeth: a half-open or phantom settle on a
  declared-escrow cell is UNSAT.
* `escrowBit` decode + both-polarity `#guard`s; the gate bodies bite on concrete rows.

The named-modeled hypotheses (`hrecompute : witDigestCol = authDigest witnessed`,
`hdecode : floorCol = escrowBit (required witnessed)`) stand in for (4a)/(4b) — the recompute/decode
gadget faithfulness — exactly as `CapacitySatisfaction` models `stateCommit = hash b`. The gates
themselves are real `VmConstraint2` constraints forced by `Satisfied2`.

`circuit/src/effect_vm/authority_digest_weld.rs` — the STAGED Rust shadow: builds the three gentian
gates (recompute-bind, decode-boolean, selector-force) over the named columns, with tests that an
honest declared-escrow row forces `sel = 1` and the gate bodies bite a forged row. NOT emitted into
any committed VK / registry; the deployed descriptors are byte-identical.

## 6. VK impact + staging

* The equality skeleton (1)(2)(3) is VK-affecting *only* once emitted into a committed welded
  descriptor — it is STAGED beside the deployed cohort, NOT emitted, NOT flipped. Deployed
  descriptors / VK byte-identical; descriptor-drift gate green.
* The recompute chain (4a)/(4b) is the genuinely-new VK (and, under Option A, new IR) work.
* **STAGE, do not flip.** Build + prove beside the deployed; commit the welded VK beside (not over)
  the deployed; flip only in the lockstep verifier-code + descriptor epoch, coordinated with the
  temporal-caveat and umem VK epochs (one upgrade window). The deployed default — no cell declares a
  capacity caveat — is unchanged this pass.

## 7. The true distance to "escrow is a deployed truth"

* **DONE before this pass:** coverage (pure-light-client, deployed), satisfaction soundness + gates,
  the WIDE fulcrum, the selector-binding spec (`SettleEscrowSelectorBinding`, under `hverifier`).
* **DONE this pass:** the in-AIR selector-forcing soundness core — `gentian_selector_forced` /
  `gentian_settle_forced` discharge the `hverifier` obligation in-AIR under the CR floor; the staged
  equality skeleton (Lean descriptor + Rust gates), `#assert_all_clean`, deployed byte-identical.
* **DONE (the discharge pass):** Option B realized — `hrecompute` (4a) discharged to a felt-domain
  chip lookup + `chip_lookup_sound`; `hdecode` (4b) discharged to the in-AIR is-zero + OR-fold decode.
  `gentian_selector_forced_discharged` / `gentian_settle_forced_discharged` hold under ONLY
  `ChipTableSound` + `FloorDigestBinds` (no off-band hypothesis), `#assert_all_clean`; the Rust gadget
  shadow + producer-witness + gate-eval teeth are green (`authority_digest_weld.rs`). STAGED — deployed
  descriptors / VK byte-identical, drift gate green.
* **REMAINING to a sound escrow FLIP (precise) — the COMMIT-TARGET BLOCKER (verified 2026-06-28).**
  The proven gadget's discharge of `hcommitLimb` requires the committed limb the gadget reads
  (`gentianAuthDigestCol = EFFECT_VM_WIDTH + 24`, the `B_AUTHORITY_DIGEST` r23 limb) to carry the
  *felt-domain* `hash_many(required-tag floor)`. The deployed commitment puts a DIFFERENT value there:
  `turn/src/rotation_witness.rs:367` sets `pre_limbs[24] = compute_authority_digest_felt(cell)` — the
  *byte-domain* `hash_bytes` over the WHOLE authority residue (program / permissions / vk / delegate /
  delegation / mode / fields[8..16] / visibility / commitments / proved / side-table roots). For any
  real escrow cell `compute_authority_digest_felt(cell) ≠ hash_many(floor)`, so:
    - the recompute-bind gate forces the gadget's limb-24 trace column to `hash_many(floor)`; the wide
      commit then absorbs that, producing a published-commit ≠ the light client's real commit (which
      absorbs the true `authDigest`). An HONEST declared-escrow turn therefore CANNOT produce a
      light-client-accepted gentian proof — the producer step (2) is not satisfiable against the
      deployed limb 24. (Confirmed: the staged shadow only checks gate-eval over a hand-built row whose
      limb 24 IS the floor digest; it does not — and cannot — also satisfy the deployed wide commit.)
    - the literal "reinterpret limb 24 as the floor digest in `compute_rotated_pre_limbs`" path is
      UNSOUND: limb 24 (`= B_RECORD_DIGEST`) is load-bearing — it is the v1 OLD_COMMIT's fourth root
      input (`record_digest`, audit P0-2 cross-leg binding) and the forced limb for the
      SetPermissions / SetVerificationKey / MakeSovereign / Refusal record-forcing pins
      (`record_pin_offset`, welded to PI 38, verifier-anchored to `compute_authority_digest_felt`).
      Overwriting it with `hash_many(floor)` destroys those bindings and the authority-residue commit.
  The SOUND realization is a NEW dedicated felt-domain floor-digest limb (the `perms_digest` /
  `vk_digest` pattern at limbs 33/34).

  **HEADROOM-LIMB REFINEMENT (verified 2026-06-28).** The "width/layout flag-day" earlier framed as the
  cost of the new limb is NOT required. Pre-limb indices **12..23** (`r11..r22`, the "app-register
  headroom") are GENUINELY UNCONSTRAINED-FREE columns, not zero-gated and not app-bound:
    - no gate forces them to zero, and no weld reads them — `EffectVmEmitRotationV3.weldsAt`
      (`EffectVmEmitRotationV3.lean:327`) welds ONLY offsets 1,2,3 (r0/r1/r2), 4..11 (fields[0..7]),
      and 25 (`B_CAP_ROOT`); every gated authority sub-limb is ≥ 24 (`trace_rotated.rs:120-168`). The
      rotation descriptor's constraint list is `v1-constraints ++ weldsAt ++ rotPins ++ hashSites`
      (`rotateV3`, `:373`) — nothing constrains offsets 12..23.
    - they ARE in the absorbed set — `wireCommitR`/`wire_commit` chains over all 37 limbs incl. 12..23
      (`rotation_witness.rs:297`; `preLimbsAt`, `EffectVmEmitRotationV3.lean:194`), so a value there
      lands in the wide commit a pure light client binds.
    - the producer writes them as ZERO only by DEFAULT (`vec![ZERO]`, nothing assigns 12..23 —
      `rotation_witness.rs:349,361`), i.e. they are reserved-for-future-app headroom, not a zero-gate.
  So writing `hash_many(floor)` into one of them (say offset 12) is a VALUE-ONLY layout change:
  same trace width + chain structure → deployed descriptors / base-layout VKs stay BYTE-IDENTICAL (only
  each cell's commitment VALUE shifts → a devnet re-genesis). This removes obstacle (a) entirely — no
  pre-limb-vector extension, no width/layout flag-day, no shifting of iroot/state_commit/chain.

  **BUT the value-only write is NOT a sound flip by itself — the BINDING GAP remains.** A free headroom
  limb carrying `hash_many(floor)` is bound INTO the commit by the anti-ghost keystone
  (`wireCommit_binds`) but is NOT forced to equal `hash_many(real declared floor)` by any constraint —
  exactly because it is unwelded. `gentian_selector_forced_discharged`
  (`InAirAuthorityDigestGadget.lean:325`) is conditional on `hcommitLimb : limb = hash committedFloor`;
  an HONEST producer satisfies it, but a forger writing the cell (at `CreateCell` or any
  caveat-mutating effect) can witness the limb = `hash(empty)` while the cell declares escrow, get it
  absorbed legitimately, and later dodge the gadget (`floorCol = 0` ⟹ no selector forcing). The
  `perms_digest`/`vk_digest` limbs avoid this precisely because they are FORCED — pass-through
  `colEq B_PERMS` welds + the setPerms/setVK declared-param force + the record-pin anti-ghost
  (`EffectVmEmitRotationV3.lean:2203,2216,2605`). So a sound flip still requires:
    (b) a new Lean wide-commit absorption proof for the chosen headroom limb,
    (c) retargeting `gentianAuthDigestCol` off limb 24 onto it (Lean gadget + `authority_digest_weld.rs`),
    (d) computing `hash_many(floor)` into it in `compute_rotated_pre_limbs` + `rotation_witness`, AND
    (e) **the per-effect floor-digest BINDING welds** (the perms/vk pattern: force-to-`hash(floor)` at
        creation/caveat-mutating effects + frozen pass-through + anti-ghost teeth) so the limb is bound
        to the cell's REAL declaration — VK-affecting for the create/authority descriptor cohort, with
        new Lean proofs. (An alternative that sidesteps (e): redesign the gadget to decode the floor
        directly from the already-coverage-bound caveat manifest columns rather than from a digest limb.)
  (e) is a TARGETED flag-day on the create/authority cohort — far smaller than the 190-site full-layout
  flag-day, but NOT value-only. Only THEN can:
  1. EMIT the `gentianGadgetDescriptor` (now reading the new floor-digest limb) into a staged registry —
     the chip-lookup table-id + the floor / is-zero / lane columns — the flag-day VK bytes.
  2. A satisfying STARK PRODUCER fill the floor / is-zero-witness / lane columns + the genuine chip rows
     AND the new floor-digest limb consistently, then a full `prove_vm_descriptor2` /
     `verify_vm_descriptor2` — honest proves, forged (sel=0 dodge / wrong floor / wrong digest) refuses.
  3. Commit the welded VK beside the deployed; route a declared-escrow turn through the gentian
     descriptor on the live verify path; the lockstep flip.
  Until the binding welds (e) (or the manifest-decode redesign) land, the gadget is a CONDITIONAL truth
  (sound under `hcommitLimb`); the flip MUST NOT be taken — a value-only headroom-limb write alone leaves
  the limb forger-choosable at the writing effect (the binding gap), and the limb-24 overwrite would
  accept forgeries on the record-pin surfaces. SettleEscrow is NOT a deployed pure-light-client truth.
  (The operative blocker is now the binding gap (e), NOT a width flag-day.)
* **UNLOCKS 18/19/Custom/temporal:** the selector-forcing core is tag-agnostic — `gentian_selector_forced`
  is parametric in the required-tag predicate, so discharge (18) and vault (19) reuse it verbatim
  for the *coverage→selector* half once their satisfaction gates land (18 needs the range-checked
  due-ness inequality; 19 needs the overflow-safe product comparison — `VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`
  §6 BLOCKER 2). The same gadget binds any declared caveat's selector to the committed declaration,
  which is the shared shape the temporal-caveat and Custom-VK welds also need.
