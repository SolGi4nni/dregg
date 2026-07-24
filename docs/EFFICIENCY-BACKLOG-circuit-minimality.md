# EFFICIENCY BACKLOG — circuit minimality beyond the Epoch-2 bundle

2026-07-18. Ranked backlog of circuit efficiency / minimality work OUTSIDE the committed Epoch-2
bundle (rate-8 absorb bundle, chip one-hot flag/tag retype + per-shape tuples, H4+caveat,
separate-absorb floor shape, narrow-bus retirement, TURN_HASH limb widening, bare-V3 stratum
retirement, heap-open closure, D5 PI-map regen). Provenance: five hunt lenses (aux-tables,
registry-vestiges, other-AIRs, recursion-wrap, semantic-minimum) over HEAD, with the largest and
shakiest claims independently re-derived by two adversarial verifier passes (verifier 2 pinned
HEAD = `2e5fcd2b4`). One claim was refuted — see the graveyard; it is not silently dropped.

## 2026-07-19 round — measured/landed, all byte-safe

Three items advanced by a measurement/proof lane that touched no descriptor bytes; each was then
independently re-derived by an adversarial verifier pass. Nothing was silently adopted.

- **E7 — ADVANCED + verified CONFIRMED** (`9959af6cc`). Census reproduced by full per-column parse
  (387 of 1,857 committed cols mechanically killable = 20.8%, byte-exact per-member table); the
  narrowing-soundness bridge landed and CI-rooted (`ChipNarrowLookup.lean`, 6 keystones
  `#assert_axioms`-clean, model-level — does NOT touch the FRI floor or the Rust LogUp impl).
  Verifier nits (both immaterial, neither drives value): "126 lookup-only" is 131 on the natural
  definition of a de-emphasized descriptive stat; the commit *message* says "7 zero-killable
  members" where the doc table and the parse agree on 8. Regen now mechanical; staged below.
- **E4 — ADVANCED + verified CONFIRMED** (`daa0a16`). Measurement harness + additive
  `create_config_with_fri_full` landed byte-safe (shipped configs unchanged). Lean-ledger verdicts
  at the member statement (no Rust soundness formula in the harness): deployed (6,19,16)
  perFold/johnson/capacity/commit = 109/73/130/67; (8,15,16) = 105/76/136/60; (8,14,16) =
  105/72/128/60 (capacity EXACTLY at the 128 drift margin, zero headroom). **ε_C finding the
  ledger exists for:** lb 6→8 costs 7 commit-phase bits (67→60) — invisible to both closed-form
  columns — and perFold falls BELOW the current 109 floor, so the cutover is a documented floor
  re-pin + an (arity 8, lb 8) hΦ fiber-discharge instance, NOT knobs-only. **New free lever:**
  `log_final_poly_len=4` alone is −5.9%/−6.9% bytes at zero ledger movement and zero prove-time.
  Projections onto 151 KB: (8,15)→~134 KB, (8,14)→~127 KB, (8,15)+lfpl4→~125 KB. Prover cost
  ~3.9–4.0× at lb 8. Shapes are mocked single-instance widths (measurement fixtures, ship
  nowhere); the soundness numbers carry the tree's standing FRI caveats (johnson = idealisation,
  capacity = refuted-conjecture canary).
- **E2 — ADVANCED + verified CONFIRMED** (`1df4bc4cc`). Byte-safe probe minted the REAL rotated
  `transferVmDescriptor2R24` leaf at full production `ir2_config` knobs and the unchanged leaf-wrap
  absorbed it at fold arity 8: wrap green (root 229,594 B, verifies in-circuit), two arity-8 leaves
  aggregate green. Non-vacuity teeth held: arity-2 = 402,539 B / 8 commit phases (all fold-by-2)
  vs arity-8 = 373,951 B / 4 commit phases, schedule `[2,2,3,1]` (log_arity 3 present ⇒ the arity-8
  reconstruct arm demonstrably ran) — commit phases halved at this fixture height, −7.1% leaf wire
  free rider. The soundness half was already Lean-proven and CI-rooted at HEAD
  (`FriLedgerSound.arity8_costs_seven_times_arity2_at_logBlowup6`: 112→109 per-fold, goodCount ×7,
  `#assert_axioms`-clean; `FriArityFiberDischarge` discharges hΦ unconditionally at the deployed
  arity-8 setup). Verdict: GO. The ~3.8× commit-phase claim is at the deployed 2^19 wrap height
  (~18→~6 rounds); this fixture shows 8→4. Nothing deleted/re-pinned/regen'd — deploy staged below.

**Refuted this round (NOT silently dropped — see E11 and the graveyard):** E11's "floor rises to
the pow-16 set" premise is FALSE — `create_recursion_config` (lb 3/38q/pow 14) is production-live
(`gpu_backend.rs:4459` + the inner-FRI prove/verify wrappers), and `recursive_witness_bundle` is
referenced from `node/src/mcp/proof.rs`; it is not a zero-production-caller dead stratum, so the
gate re-pin would launder a gap. E11 is downgraded to HELD-VERIFICATION pending a production-path
read; it is NOT a clean deletion lane. *(RESOLVED 2026-07-19 by the E11-prodread deep read — see
E11: pow-14 is NOT live-necessary; the three cited edges are config-inert / producer-less /
stale-comment. E11 re-scopes as an accept-surface retirement, not a dead-code deletion.)*

**Lanes that died (contended, no landing):** E15 (CCC route-or-retire) and E17-docs.

## 2026-07-19 round (continued) — soundness-core proof + member-precise falsifier, byte-safe

Two more items advanced by proof/falsifier lanes that touched no descriptor bytes, each
independently re-derived by an adversarial verifier pass; E11's suspended premise was resolved by a
production-path read. Nothing silently adopted.

- **E8 — ADVANCED + verified CONFIRMED** (`b0c73d084`). Soundness core PROVEN byte-safe, no regen.
  New `metatheory/Dregg2/Circuit/Emit/BilateralAggregationCompact.lean` (1,064 lines, 14
  `#assert_axioms` clean — subset {propext, Classical.choice, Quot.sound}, no sorry): the compacted
  `bilateralAggDescriptorV3` (width 87→52 — the 35-gate `sched==expected` block deleted, verified
  tautological; middle-row identity gap closed by 13 identity-carry window gates; 48 constraints,
  outer PI 23 unchanged; full v3 wire `#guard`-pinned before the descriptor file exists) is
  machine-checked against the DEPLOYED `Satisfied2`: (A) `expand_satisfies` — every v3-accepted
  trace expands to full `Satisfied2` of the byte-identical deployed v2 descriptor; (B)
  `contract_preserves` — every identity-row-constant honest v2 witness contracts to v3; (C) STRICT:
  `gapTrace_satisfies` EXHIBITS a v2-accepted 3-cell bundle forging middle-cell `turn_hash[0]=7`
  (middle-row identity is in-AIR unconstrained in v2 — the per-row-CG-2 doc claim is falsified by
  exhibit and corrected comment-only, v2 byte-pin rebuilt green), which v3 refuses
  (`gap_no_v3_preimage`); Rung-1/Rung-2 crowns carried through the bridge. Verifier reproduced the
  byte-safety (4 files: the new Lean, a 25-line doc-only correction to `EffectVmEmitBilateralAgg`,
  one `Dregg2.lean` import, HORIZONLOG), a fresh Lean elaboration (all 14 `#assert_axioms` firing
  live), and every width/constraint number (35 = COUNTS_LEN 7 + ROOTS_LEN 28; 70−35+13=48;
  87−35=52). **Bundled CI defect the verifier caught (does NOT affect soundness or byte-safety):**
  rooting the previously-orphaned `BilateralAggregationEmit/Refine/Rung2` into `Dregg2.lean` leaves
  three now-stale `scripts/lean-orphans-allow.txt:32-34` entries that red `check-lean-orphans.sh` —
  de-list them at cutover. Byte win STAGED (−40.2% main-trace committed columns, 70→48 constraints),
  not measured; the proof-byte delta is a cutover-time measurement. Recipe: BUNDLED-CUTOVER §E8.
- **E10 — ADVANCED + verified CONFIRMED** (`a8cd5e35f`). Member-precise falsifier landed byte-safe
  (`circuit/tests/zzz_e10_freeze_owner_falsifier.rs`, single-file forge probe, no regen). Over the
  LIVE `cellSealVmDescriptor2R24`, a self-consistent seal whose ONLY moved variable is the AFTER
  owner octet (`B_PUBKEY_OCTET` 105–112) — lifecycle record-pin `PI[46]=Sealed` satisfied, economic
  frame frozen, `wireCommitR` + NEW_COMMIT self-consistent — PROVES + VERIFIES through the deployed
  per-descriptor `prove_vm_descriptor2`/`verify_vm_descriptor2`; the control lifecycle-freeze forgery
  is REJECTED (a live discriminator, not accept-everything). Root (read, not asserted): `cellSeal =
  graduateV1 (rotateV3WithLifecyclePayloadGate … cellSealVmDescriptor)` — NOT `v3OfFrozen`, so it
  carries none of `frozenAuthorityColEqs`; the pubkey octet is in no freeze/weld set on either path,
  and the verifier PI reconstruction does NOT compensate (`proof_verify.rs:552` binds NEW_COMMIT to
  the prover's CLAIMED post, not an independent re-execute). So NOTHING at the AIR/verifier level
  rejects a changed-owner seal — a witness-gen faithfulness hole faithful `apply_cell_seal` never
  produces. The same free-AFTER-owner shape is shared by all 41 no-freeze members, so the no-freeze
  class is PROVEN a real gap: the byte-safe E10 dedup on the 16 carriers is greenlit, and the real
  close is a Lean-authored owner-freeze colEq (both ride the regen — recipe: BUNDLED-CUTOVER §E10).
  Verifier reproduced the single-file byte-safety, the AIR root-cause read, and the live
  accept/reject asymmetry.
- **E11 — RESOLVED + verified CONFIRMED** (`bd247bbaf`, census-only docs lane; folded into §E11 and
  the graveyard above). The suspended lever un-sticks: pow-14 `create_recursion_config` (lb 3/38q) is
  NOT necessary on the live prove/verify path — re-scoped as an accept-surface retirement, not a
  dead-code deletion. Verifier CONFIRMED: zero descriptor/VK/TSV/Lean bytes moved; every code-census
  claim re-derived at HEAD (the three "production-live" edges are config-inert, producer-less, and a
  stale comment); the honest ordering (surface removal + gate re-pin 71→73 in ONE cutover) preserved.

## Vocabulary

Evidence classes (arch-review vocabulary):

- **[M]** — measured on a real prove/verify at HEAD.
- **[P]** — parsed/read from code or descriptors at HEAD; a structural fact.
- **[A]** — analytic: calibrated-model extrapolation, not measured on this exact path.
- **[U]** — unknown: needs a probe before the number can be trusted.

Verification tags: **CONFIRMED** = independently re-derived by a verifier pass; **hunt-only** =
single-lens parse, no second derivation; **REFUTED** = graveyard.

Wire pricing used throughout: composite ~188 B/col on the main batch, [M]-calibrated by the S2
deletion itself (−960 cols → −181,757 B; post-S2 transfer proof = 375,053 B, cells 394,400;
`docs/MEASURE-legacy-1felt-chain-drop.md`). Aux-instance pricing: 28.5 B/col opened + 19q ×
2.48 B/col ≈ 75.6 B/col **[A]** (calibrated at h=64/256; h=8 paths are shorter).

Effort unit = **lane**, calibrated: the S2 deletion = 1 heavy lane; the narrow-bus campaign = 6 lanes.

Risk classes: **byte-safe** (no VK/FP/FS change) · **regen** (VK/FP re-pin, no statement or value
change) · **semantic-change** (statement, soundness posture, or published-value change).

## Decisions that expire at the Epoch-2 freeze

Four items get an epoch cheaper if decided before the Epoch-2 flag day; deferral costs a second
VK/FS epoch later:

1. **E3 — mutable-last limb schedule.** The v10 absorption order is being frozen in the bundle;
   reordering later is another flag day.
2. **E4 prep — run the FRI re-grid measurement now** at post-S2 and mocked-floor widths so the
   (lb,q) point can land inside the same FS epoch.
3. **R11 fold-side costing.** D7 priced the floor-shape branches on the wire only (+9,043 B for
   the preprocessed round); each extra instance/round also adds per-query input-round Merkle paths
   + opened-value Horner chains to EVERY leaf-wrap circuit. Uncosted **[U]**; belongs in the
   Stage-3 B-vs-F decision before it is made, not after.
4. **E12 — pin children on the wide tree** before the staged wide-tree flip ships, or the seam
   ships with it.

## BUNDLED-CUTOVER — the one ack-gated regen window

Every item here is regen- or FS-epoch-class: each mints new VK / FRI-transcript / descriptor bytes,
so **no two can run in parallel** — a second concurrent regen clobbers the first. They land together
in ONE clean-window ack-gated regen (the Epoch-2 flag day). The measure/prove halves have already
landed byte-safe and are verified (E7/E4/E2 above; E1 soundness-core proven; E8 soundness-core proven
`b0c73d084`; E10 falsifier landed `a8cd5e35f`); what remains is the single coordinated cutover below.
`docs/VK-REGEN-LOG.md` records the flip; full per-step text lives in the HORIZONLOG entries dated
2026-07-18/19 under each key.

**Landed already:** **S2** dead-stratum deletion (Epoch 1) — −32.6% proof bytes on the deployed
member, verified, shipped. It is the pricing calibrant (188 B/col main; −960 cols → −181,757 B) and
the method proof (`compactS2` + `compactOk` gate); it does not re-run.

**Sequencing inside the window** (each step waits for the prior regen to settle):

1. **Epoch-2 chip one-hot/tag retype** (the bundle proper — narrow-bus retirement, per-shape tuples,
   TURN_HASH limb widening, bare-V3 stratum retirement). E7 and E9(b) sequence AFTER this.
2. **§E2 fold-arity flip** (semantic-change, defines the FS epoch the rest ride).
3. **§E4 FRI re-grid** (rides the E2 FS epoch — a lone flip would be a second flag day).
4. **§E7 narrow-bus swap** (mechanical, but mints 24 new VKs — after the chip retype, not parallel).
5. **§E1 + §E8 + §E10 + regen riders** (per-member compaction, the bilateral-v2 expected-block
   deletion, the owner-freeze colEq + 83-col dedup, and everything else gated only on VK re-pin).

### §S2 — DONE (Epoch 1)

Reference only. Uniform dead-stratum kill, landed and measured; the compactor method and 188 B/col
pricing below inherit from it.

### §E1 — per-member v1-face compaction (soundness-core proven, HELD-REGEN, contended files)

`compactS2`-style value-preserving face compaction at the Lean emit, per-member kill-set (not the
uniform S2 one): ~149 dead cols on transfer, 8,847 dead col-instances registry-wide. Recipe:
(1) drive the per-member kill-set through `RotWideCompactS2.compactS2` + the `compactOk` gate;
(2) delete columns, renumber densely; (3) producer fill + width pins follow; (4) regen descriptor
emit + registry TSV + VK re-pin. Its two files (`circuit/descriptors/rotation-wide-registry-staged.tsv`,
`metatheory/.../EffectVmEmitRotationV3.lean`) are DIRTY from a live lane — settle before flipping.
Probe first: name the 34–39-col unidentified bands (RV-F8) before the compactor eats the evidence.

### §E7 — by-name narrow-bus swap (census + bridge landed `9959af6cc`, mechanical regen)

**CUTOVER STARTED 2026-07-24 — 2 of ~24 members DEPLOYED.** `poseidon2-hash-arity2` 10→3 and
`merkle-membership-depth2` 24→10 now emit the NARROW (`poseidon2narrow` = `TID_P2_NARROW`, wire 8)
18-wide tuple; **21 committed columns deleted from the deployed bytes.** Their emit + Refine modules
re-point at `ChipNarrowLookup.chip_lookup_narrow_sound_of_wide_table` under the deployment-shaped
same-rows hypothesis `t.tf poseidon2narrow = narrowTable (t.tf .poseidon2)` (the Lean face of Rust
`narrow_hist`), discharged CONCRETELY in each non-vacuity witness (`witTf_narrow_wire`,
`concrete_narrow_wire`) — no new assumption. Verified: 15/15 emit-gate + audit tests green on
persvati (honest prove+verify on the narrow bus; forged digest / forged parent / tampered leaf /
tampered sibling / forged claimed root / forged PI teeth ALL still bite), 5/5
`gate1_adversarial_audit` cross-descriptor rejects green, full `lake build` green, and the CANONICAL
`scripts/emit_descriptors.py` run reproduces both files byte-exact (a verified no-op — the bytes
came from the machine-checked `#guard` pins, never a sweep). Drift class: GEOMETRY-WIDEN (both moves
are SHRINKS). Remaining members below.

Sequence AFTER the Epoch-2 chip retype (E7 does not inherit it); cannot run parallel with other
regens (mints new VK/bytes for 24 members). Recipe:
1. In each by-name emit module (`NoteSpendingLeafEmit`, `BlindedMembershipEmit` +4ary,
   `AttestedFactMembershipEmit`, `MerkleMembership{,4ary}Emit`,
   `Predicates{Arithmetic,Gt,Le,Lt,Neq,InRange}Emit`, `NonRevocation{,Adjacency}Emit`,
   `AdjacencyMembershipEmit`, `DfaRouting*`, `DyckParse*`, `BoundPresentationEmit`,
   `EffectVmEmitTurnChainBinding`, derivation/cross-side/bundle-fold producers) swap
   `.lookup {table := .poseidon2, tuple := chipLookupTuple ins digestCol laneCols}` →
   `.lookup {table := poseidon2narrow, tuple := chipLookupTupleNarrow ins digestCol}`; delete lane
   cols, renumber densely; drop note-spend-leaf's 8 unref cols {15, 55–61} + derivation's col 0.
2. Re-point each Refine/Rung2 proof `chip_lookup_sound` →
   `chip_lookup_narrow_sound_of_wide_table` / `narrow_lookup_holdsAt_sound` (identical conclusion).
3. Regen GOLDEN strings via `emitVmJson2` + re-emit `by-name/` (drift gate recurses into by-name).
4. Rust twins: layout consts + witness builders stop filling lanes
   (`membership_descriptor_4ary.rs` `MEMBERSHIP_4ARY_WIDTH` 18→11, `LANE_BASE` deleted). Prover side
   needs NOTHING — `TID_P2_NARROW` parse arm, `BUS_P2_1` AIR send, `narrow_hist` multiplicity
   serving are already live in `descriptor_ir2.rs`.
5. Canaries: honest prove+verify per member + each module's forge teeth re-run.
6. Optional rider (semantic-change, same regen): the 1-felt `SenderAuthorized` waist fix
   (`membership_verifier.rs:1076-1101` → 8-felt root + wide-tag chain).

### §E4 — FRI re-grid flip (measurement landed `daa0a16`, rides the E2 FS epoch)

A lone flip is a second FS flag-day — ride the epoch E2 already spends. Recipe:
1. Flip `circuit/src/descriptor_ir2.rs::IR2_FRI_LOG_BLOWUP` 6→8 + `IR2_FRI_NUM_QUERIES` 19→15
   (or 14 — capacity sits EXACTLY at the 128 drift margin), optionally
   `IR2_FRI_LOG_FINAL_POLY_LEN` 0→4 (measured free bytes, same FS epoch).
2. Re-derive `circuit-prove/tests/fri_params_soundness_budget.rs` floors via `dregg_fri_ledger` at
   the lb-8 reading — perFold drops below the current 109 floor: a *documented re-pin*, not a
   relax-in-place.
3. Extend `metatheory/Dregg2/Circuit/FriArityFiberDischarge.lean` with the (arity 8, lb 8)
   `friSetupK` instance (k=3, b=8; window dOut ≥ |L| − 2n) — lb 8 is not among the discharged
   configs; without it the new perFold rides an undischarged hypothesis.
4. Price ε_C at the new statement in the cutover commit (commit column 67→60) and NAME the chosen
   posture (compensating levers: ext_deg at ~+31 bits/degree, or the still-unpriced commit-pow knob).
5. Regen descriptor emit + registry TSVs + VK re-pin + apex re-verify inside the bundle; update
   `docs/VK-REGEN-LOG.md`. `fri_regrid_post_s2_measure`'s always-on baseline pin then goes red until
   the candidate table is re-grounded (deliberate tripwire).

### §E2 — fold-arity 8 + double-prove retirement (probe GO `1df4bc4cc`, semantic-change)

Proofs are NOT interchangeable across the flip — this defines the FS epoch. Recipe:
1. Flip `INNER_FRI_MAX_LOG_ARITY` 1→3 at `plonky3_recursion_impl.rs:116` so `ir2_leaf_wrap_config()`
   ≡ production `ir2_config` knobs; retire the `:401-411` PROBE comment.
2. Delete the per-turn re-mint: `finalized_turn_from_full_turn` consumes the node's served
   `Ir2BatchProof` directly — `turn/src/rotation_witness.rs:749-762` re-prove + `:685-687` mint
   self-verify die; KEEP the fail-closed 8-felt wide-anchor tie.
3. Collapse the `DreggStarkConfig`/`DreggRecursionConfig` split ("SIDESTEP option a" fossil,
   `ivc_turn_chain.rs:927-935`, ~15 leaf adapters) so the production mint IS the fold input type.
4. Re-pin posture: the rotated chain leaves `ir2LeafWrapRotatedConfig` (the ONE config the
   arity-2 per-fold posture describes) for the arity-8 ledger row; move
   `fri_params_soundness_budget.rs` expectations via the exported `dregg_fri_ledger`.
5. gnark long pole: add an arity-8 `fold_row` beside `friFoldRowArity2`
   (`chain/gnark/fri_verify_native.go:228`); bundle with apex lever B so the ETH wrap re-lands once.
   `dregg_outer_config.rs:139-142` (ETH-wrap OUTER shrink, arity-2 lb-3) is a SEPARATE knob and may
   stay.
6. Gates after flip: `e2_fold_arity_recompose_probe` (becomes the standing regression gate),
   `rotation_batchstark_leaf_smoke` (repoint its stale geometry pins — already red at HEAD on the
   1702-wide/50-PI member vs its 1647/46 assertion), `ivc_turn_chain` chain tests,
   `fri_params_soundness_budget`.

### §E8 — bilateral-v2 expected-block deletion (soundness-core proven `b0c73d084`, semantic-change)

Soundness core proven byte-safe (`BilateralAggregationCompact.lean`, §2026-07-19 continued); this is
the cutover half. Independent of the map/IMT/rotation cluster and of E9's `joint_turn_aggregation.rs`.
Recipe:
1. Emit `circuit/descriptors/dregg-bilateral-aggregation-v3.json := emitVmJson2 bilateralAggDescriptorV3`
   (the bilateral leg of `scripts/emit_descriptors.py` or a one-line `lake env lean` driver); MUST
   byte-equal the `#guard` pin already committed in `BilateralAggregationCompact.lean` §2.
2. Rust twin in `circuit/src/bilateral_aggregation_air.rs`: `include_str!` the v3 file;
   `BILATERAL_AGGREGATION_DESCRIPTOR_NAME` → `dregg-bilateral-aggregation-v3`; DELETE
   `AggregationInnerRowV2.expected_counts/expected_roots`; `build_aggregation_trace_v2` width 87→52
   (cum 49, consistent 50, n_cells 51); KEEP the padding-row identity mirror (load-bearing under v3 —
   the carry gates fire on padding transitions); callers (`node/src/api.rs:3989-3997`, wasm, MCP
   `dregg_bilateral_action`) drop the expected args.
3. Re-pin `circuit-prove/tests/bilateral_aggregation_emit_gate.rs` `GOLDEN_JSON` to the v3 bytes;
   hand-built twin shape width 52 / 48 constraints / 15 window gates; re-pin the descriptor SHA/VK
   (`bilateral_aggregation_descriptor_matches_lean_pin`).
4. Same-commit doc fixes in `bilateral_aggregation_air.rs`: (a) module header (~15-90) — per-row CG-2
   + retired 112-wide layout → v3 (boundary bindings + identity carries, per-row and now true
   in-circuit); (b) the CG-5 `edge_fp` "~124-bit" claim (~581) is wrong for a 1-felt fingerprint
   (~31-bit image, birthday ~2^15.5) — state the off-AIR exact multiset re-derivation is the real
   closure, or widen `edge_fp` to 4 felts in the SAME regen if an in-circuit collision claim is wanted.
5. Same commit: de-list the three now-stale `scripts/lean-orphans-allow.txt:32-34` entries
   (Emit/Refine/Rung2 are reachable since `b0c73d084` rooted them) so `check-lean-orphans.sh` greens.
6. Canary + gate: Rust twin of `gapTrace` (middle-row forged turn-id) must flip ACCEPT(v2) →
   REJECT(v3); honest multi-cell bundle proves+verifies; `cargo test -p dregg-circuit-prove bilateral`
   + the `multi_cell_cross_fed_binding` gauntlet; MEASURE the proof-byte delta at cutover (width
   −40.2% is the staged column count, not a measured byte number).

### §E10 — frozen-authority owner-limb close + 83-col dedup (falsifier landed `a8cd5e35f`, semantic-change)

The falsifier (byte-safe, landed) PROVED the AFTER owner limb is unforced on the no-freeze class; the
regen half closes it and dedups the 16 carriers. Do NOT run parallel with another regen or a live
descriptor-editing lane. The real close is a Lean-authored owner-freeze colEq (the AIR is
Lean-authored — never hand-written in Rust). Recipe:
1. Lean `EffectVmEmitRotationV3.lean`: add `pubkeyFreezeColEqs(w) := (List.range 8).map (fun i =>
   colEq (w+B_PUBKEY_OCTET+i) (w+AFTER_BLOCK_OFF+B_PUBKEY_OCTET+i))`, appended as a single `++`
   right-operand (v1 stays left) to every non-owner-moving member's rotate wrapper (both `v3Of` movers
   like cellSeal and `v3OfFrozen` value members); the only exception is a future transferOwnership;
   mirror `authorityHeadroomFreezes`. Prove `pubkeyFreeze_freezes` (AFTER octet == BEFORE on a
   satisfying transition row); keep the graduable + refinement keystones verbatim (`.gate`/
   `when_transition` past `rotateV3` — composition unchanged); `#assert_axioms` clean (subset of
   propext/Classical.choice/Quot.sound), no sorry/admit.
2. Emit: regenerate the staged registry TSVs (`rotation-wide-registry-staged.tsv` +
   `rotation-wide-umem-welded-registry-staged.tsv`) and the by-name descriptor JSONs — MINTS new
   per-member VK + proof bytes (the byte-safe half stops here).
3. Rust: no hand-AIR edits; `descriptor_ir2`/`ir2_eval_accepts`/`prove_vm_descriptor2` pick up the new
   colEqs from the parsed descriptor automatically.
4. CANARY: `circuit/tests/zzz_e10_freeze_owner_falsifier.rs` must FLIP — the owner-forge prove/verify
   verdict ACCEPTED → REJECTED (invert the final assert to assert rejection + control still-honest-
   accepts); the honest seal still proves+verifies; the lifecycle/economic teeth in
   `effect_vm_rotation_flip.rs` stay green.
5. The byte-safe E10 emit-tuple dedup on the 16 carriers (~83 dup cols ≈ 15.6 KB + 5.3K cells/proof)
   rides the SAME regen; MEASURE the proof-byte delta at cutover.

### Regen riders (gated only on the VK re-pin — fold in, do not schedule separately)

- **E5** map-ops instance split (op≤3 width 421 vs AAFI 897) — CONTENDED (IMT-migration cluster).
- **E6** absent-op deletion — HELD-REGEN + Lean lemma; CONTENDED (same cluster).
- **E13** legacy Memory table retirement + degree-8 kill — `setFieldDyn` in the dirty registry TSV.
- **E14** umem cohort-boundary flip (`cohort := false`→`true` + TableDef swap + byte-parity pin).
- **E8** bilateral-v2 expected-block delete (width 87→52) — soundness core PROVEN byte-safe
  (`b0c73d084`); promoted to its own **§E8** subsection above (full recipe).
- **E10** owner-freeze colEq + 83-col dedup — falsifier landed byte-safe (`a8cd5e35f`); promoted to
  its own **§E10** subsection above (full recipe).
- **E16(b)** envelope binding-descriptor drop (envelope v5 FS re-pin; coordinate lightclient/wasm).
- **E17 regen riders** — tables-decl sync, welded-placeholder filter, PI-layout normalization,
  duplicate-gate / arity-3 drop, strata quarantine.

**Not in this bundle:** **E11** (production-path read DONE 07-19: retire-able — re-scoped as an
accept-surface retirement cutover with its own bundled gate re-pin; see E11) and
**E15** (lane died this round). The **E10 falsifier** landed byte-safe this round (`a8cd5e35f`); its
dedup + owner-freeze colEq close ride the regen (§E10). E9(a), E16(a)(c)(d) are byte-safe and run
OUTSIDE the regen window.

## Ranked backlog — summary

| # | Item | Verified cost today | Yield | Effort | Risk | vs Epoch-2 |
|---|------|--------------------|-------|--------|------|------------|
| 1 | E1 v1-face dead-band compaction | ~28 KB/proof (7.5%), 8,847 dead col-instances | ~29 KB/proof mean, ~9.5K cells/member | 1–2 lanes | regen | independent; ride the regen |
| 2 | E2 double-prove retirement + fold-arity 8 | 1 extra full prove/turn + ~3.8× commit-phase hashing in every wrap | seconds/turn off the recursion stack | 2–3 lanes | semantic-change | independent |
| 3 | E3 mutable-last limb schedule | chip h=64 where 32 suffices (34 members) | ~12.7K cells (~15% of floor); kills the h-64 cliff | hours + rider | semantic-change | BEFORE freeze |
| 4 | E4 FRI re-grid (8,14–15,16) | (6,19) chosen at a 3.0×-smaller member | projected 151→115–125 KB [A] | 1 lane | regen | with/after bundle |
| 5 | E5 map-ops instance split | 476 all-zero cols ≈ 36 KB on heapWrite/refusal | 36–68 KB on 10 map members | 1 lane | regen | independent |
| 6 | E6 absent-op deletion | MapAbsent instance ≈ 18–27 KB + 1 witness chip path × 7 members | strongest single lever on the chip-64 cliff | 1–2 lanes | regen + Lean lemma | independent |
| 7 | E7 by-name zoo re-emit | 387 of 1,857 committed cols mechanically dead (lanes-only + unref); note-spend-leaf −62% width | dominant share of every private-payment sub-proof | 1 lane (census + bridge LANDED; **cutover STARTED — 2 members deployed, −21 cols**) | regen | does NOT inherit Epoch-2 |
| 8 | E8 bilateral-v2 expected-block deletion | 35 duplicated cols+gates, live per multi-cell turn | width 87→52 + closes middle-row identity gap | 1 lane (soundness core PROVEN `b0c73d084`; regen mechanical) | semantic-change | independent; ride the regen |
| 9 | E9 joint-turn binding leaf | free-witness digest + 1 uni-STARK + 1 wrap per joint turn | delete a layer or make it real | 0.5–1 lane | semantic-change | rides tag retype if (b) |
| 10 | E10 frozen-authority falsifier + 83-col dedup | 83 duplicate cols ≈ 15.6 KB (16 members); no-freeze class PROVEN a witness-gen gap | 15.6 KB + 5.3K cells + owner-freeze colEq close | 1 lane (falsifier LANDED `a8cd5e35f`; dedup + colEq ride regen) | byte-safe then regen | dedup + close ride regen |
| 11 | E11 Golden-v1 accept-surface retirement | ~900 lines; pow-14 config sets the gate's weakest column | read DONE: pow-14 NOT live-necessary; gate floor un-pins 71→73 WITH surface removal | 1 lane + canary | accept-surface cutover (no regen) | independent; never split surface removal from re-pin |
| 12 | E12 pinned children on wide/joint trees | 2 of 3 tree folds fold unpinned children | closes the foreign-child seam pre-flip | 0.5–1 lane | semantic-change | BEFORE wide flip |
| 13 | E13 Memory-table retirement + degree-8 kill | 2 AIRs + 3 buses for one member's 2 ops; lone deg-8 gate | main degree uniformly ≤2; whole subsystem deleted | 1–2 lanes | regen | ride the regen |
| 14 | E14 umem cohort boundary flip | 29 extra cols + byte sends × 57 welded proofs | ~2–3 KB × 57 | 0.5 lane | regen | independent |
| 15 | E15 CCC route-or-retire | Lean-proved AIR unrouted; live gate = Rust sums; 154/172 range cols | decision + 172→~30 cols if routed | 0–2 lanes | semantic-change if routed | independent |
| 16 | E16 ops-layer routing | O(K)×minutes per fold request; ~100 KB envelope freight | amortized folds; smaller envelopes | ~1 lane + hours | mixed | independent |
| 17 | E17 hygiene riders | fossils, false parity claim, placeholder members, PI ballast | audit-surface shrink | ≤0.5 lane each | mostly regen riders | ride the regen |

---

## Ranked backlog — detail

### E1 — v1-face dead-band compaction (rank 1)

- **What/where:** On every wide member, the L0 v1 executor face is largely unread: on post-S2
  transfer (W=1704), **149 committed columns are referenced by zero constraints** — cols 14–53
  (40 retired-verb selectors; `RETIRED_SELECTORS`, `circuit/src/effect_vm/columns.rs:186-188`),
  70–75 (6 params), 90–97 + 101–185 + 187 (94 of 98 v1 aux, including the entire 60-col v1
  balance **bit**-decomposition band `NEW_BAL_LO/HI_BIT_BASE`, `columns.rs:310-313`, superseded by
  the 15-bit-limb avail weld), plus 9 gentian-tail cols. Registry-wide: min 141 (transferFee),
  mean 155.2, max 207 (heapWrite), **8,847 dead col-instances = 8.5% of total registry width**
  (`circuit/descriptors/rotation-wide-registry-staged.tsv`).
- **Verified cost today:** 149 × 188 B ≈ **28.0 KB/proof = 7.47% of the 375,053 B post-S2 proof**;
  registry mean ≈ 29.2 KB; ~9.5K committed cells/member. [P] census, [A] pricing ([M]-calibrated
  via the S2 drop). **CONFIRMED by both verifiers** (semantic-minimum variant exact; the
  registry-vestiges variant's transfer detail refuted — see graveyard).
- **Fold-ins (same compactor pass):** 21 members still carry the 4 transitively-dead H4 chip sites
  the uniform S2 kill-set missed (~2,176 main cells + 1,024 aux cells + ~6.4 KB each; hunt-only
  [P]); heapWrite has 1 further dead arity-2 site + 8 orphan cols [P]; gentian-refuse aux is
  9–12 cols dead where carried [P]; the 34–39-col dead bands on note/refusal/heap members are
  included in the totals but their stratum identity is **[U]** — read the note-region emit and
  name the band before the compactor eats it.
- **Fix sketch:** a `compactS2`-style value-preserving face compaction at the Lean emit
  (`RotWideCompactS2.compactS2` machinery + `compactOk` gate already exist), with a **per-member**
  kill-set instead of the uniform one. Pure column deletion; producer fill + width pins follow.
- **Effort:** 1–2 lanes (S2-class). **Risk:** regen. **Dependencies:** independent of the A/B/F
  floor-shape choice; ride the Epoch-2 regen window (Design A explicitly keeps the v1 face, so
  nothing in the bundle deletes this band on its own).

### E2 — retire the per-turn double-prove; escalate fold arity (rank 2)

**STATUS 2026-07-19: probe GO + verified CONFIRMED (`1df4bc4cc`). The `[U]` recompose-at-arity>1
question is answered [M]: the unchanged leaf-wrap absorbs a full-`ir2_config` arity-8 leaf and two
arity-8 leaves aggregate, both green in-circuit; commit phases halve at fixture height (8→4,
schedule `[2,2,3,1]`), −7.1% leaf wire free rider. Soundness half already Lean-proven + CI-rooted.
Bytes untouched; the semantic cutover is staged below (BUNDLED-CUTOVER §E2).**

- **What/where:** Every IVC-bound turn is proven twice: the production artifact mints under
  `ir2_config` (lb 6, 19q, fold-by-8; `circuit/src/descriptor_ir2.rs:5452-5456`), then
  `turn/src/rotation_witness.rs:749-762` re-proves the identical descriptor/trace/PI vector under
  `ir2_leaf_wrap_config` (fold-by-2; `circuit-prove/src/ivc_turn_chain.rs:951`,
  `plonky3_recursion_impl.rs:116-119`), plus a mint self-verify (`rotation_witness.rs:685-687`).
  The arity-2 choice is a still-unresolved PROBE (`plonky3_recursion_impl.rs:401-411` — "isolate
  whether higher-arity folding is the obstruction"); the in-circuit verifier reads count/arity
  from the proof, so direct consumption of the arity-8 proof is plausible but unexercised **[U]**.
  Downstream, arity-2 is baked into every recursion layer AND the gnark wrap
  (`friFoldRowArity2`, `chain/gnark/fri_verify_native.go`; `dregg_outer_config.rs:139-142`).
- **Verified cost today:** one full extra descriptor prove per finalized turn (~425–440 ms post-S2
  [A]; the hunt's 638 ms was the pre-S2 [M] figure) + ~18 commit rounds instead of ~6 in every
  in-circuit verifier: **~3.8× on the commit-phase Merkle-path term** (whole hashing table drops
  by less than 3× — the input-round paths are arity-independent). The 2^15-row poseidon2-W16
  shrink table (~11,000 perms) is precisely this term. [P] structure, [A] arithmetic.
  **CONFIRMED by both verifiers** (with the quantitative hedge above).
- **Fix sketch:** exercise the recompose path at arity >1 against a real `ir2_config` proof; if
  green, consume the production proof directly, delete the re-mint, collapse the
  `DreggStarkConfig`/`DreggRecursionConfig` split (the "SIDESTEP option a" fossil,
  `ivc_turn_chain.rs:927-935`; 15 leaf adapters affected); add an arity-8 `fold_row` to gnark.
- **Effort:** 1–2 lanes dregg-side + 1 gnark lane. **Risk:** semantic-change — arity-8 at lb 6
  costs ~3 per-fold soundness bits (112→109); the decision goes through `dregg_fri_ledger`, not a
  comment. **Dependencies:** independent of Epoch-2; compounds with apex lever B; this is where
  the latency lives once the bundle lands (post-Epoch-2 the recursion stack is >99% of settlement
  latency — R11).

### E3 — pre-freeze decision: mutable-last limb schedule (rank 3)

- **What/where:** The Lean-pinned absorption order puts every transfer-mutated limb first
  (`pre[1]=balance_lo, pre[2]=nonce, pre[3]=balance_hi`; mirrored at
  `cell/src/commitment.rs:1075-1083`), so D1's rate-8 simulation found zero BEFORE/AFTER chip
  dedup — the streams diverge at step 1 (`docs/DECIDERS-rotated-arch-D1-D7.md:87-89`).
- **Verified cost today:** chip height 64 where ~32 would suffice on the 34-member transfer class;
  the capOpen/noteSpend family misses the 64 cliff by 1–2 permutations. [P] order, [A] dedup
  projection (D1's simulator, needs one re-run under the reordered schedule). Hunt-only.
- **Expected yield:** BEFORE/AFTER chains share ~21 of 23 rate-8 steps as identical chip tuples →
  chip height 64→**32** for the 34-member class (~12.7K cells ≈ ~15% of the 82.7K-cell floor);
  subsumes D6 follow-up #2 with margin; de-risks the witness-node8 axis on map-op members.
- **Fix sketch:** re-run the D1 simulator mutable-last (hours); pin the v10 schedule accordingly.
  Seed choice couples: a per-object seed (design B) kills this dedup — decide the two together.
  BEFORE/AFTER need no in-hash domain separation (each digest has its own PI slot).
- **Effort:** hours + free rider on the Epoch-2 emit. **Risk:** semantic-change (published anchor
  values change — the flag day already planned). **Dependencies:** MUST be decided before the
  Epoch-2 freeze; retrofit = another epoch.

### E4 — FRI re-grid at post-bundle scale (rank 4)

**STATUS 2026-07-19: measurement landed byte-safe + verified CONFIRMED (`daa0a16`). The
projection endpoints are now measured [M] on mocked-floor shapes and the ledger verdicts are read
from the compiled `dregg_fri_ledger` [M-ledger]; shipped configs unchanged, no FS re-pin, no
descriptor bytes. Harness `fri_regrid_post_s2_measure.rs` + additive `create_config_with_fri_full`
(exposes the never-gridded `commit_proof_of_work_bits`). The cutover flip is staged below
(BUNDLED-CUTOVER §E4).**

- **Ledger verdicts [M-ledger]** (perFold / johnson / capacity / commit, member statement,
  ext 4, arity 2^3, m=7): deployed (6,19,16) = 109/73/130/67; (8,15,16) = 105/76/136/60;
  (8,14,16) = 105/72/128/60 (capacity EXACTLY 128, zero headroom). **The ε_C finding the ledger
  exists for:** lb 6→8 costs 7 commit-phase bits (67→60), invisible to both closed-form columns,
  and perFold (105) falls BELOW the current 109 floor — so the cutover is a *documented floor
  re-pin* + the (arity 8, lb 8) hΦ fiber-discharge instance (lb 8 is not among the discharged
  configs), NOT a knobs-only flip. lfpl-4 and commit-pow-8 twins read column-identical ledgers
  (both knobs are ledger-invisible).
- **Measured bytes [M]** (21 real proves, tamper-reject polarity per shape): post-S2 main proxy
  (8,15,16) −11.3%, (8,14,16) −16.0%, (8,15)+lfpl4 −17.4% (floor proxy −10.6/−15.5/−17.8%). **New
  free lever:** `log_final_poly_len=4` alone = −5.9%/−6.9% bytes at ZERO ledger movement and zero
  prove-time (still FS-epoch class). Prover cost ~3.9–4.0× at lb 8 (re-proves every fold — budget
  for the recursion wrap); verify time mildly drops. Projected onto 151 KB: (8,15)→~134 KB,
  (8,14)→~127 KB, (8,15)+lfpl4→~125 KB — the 115–125 [A] optimistic end needs the lfpl stack or
  (8,14)'s zero-headroom capacity, eyes-open. Scope: shapes are MOCKED single-instance widths
  (fixtures, ship nowhere), so absolute bytes over/understate the member by construction; the
  soundness numbers are the ledger's and carry its standing FRI posture caveats.

- **What/where:** `ir2_config` = (lb 6, 19q, pow 16) was chosen from a grid measured when the
  member proof was 120.4 KiB (`.docs-history-noclaude/PROOF-ECONOMICS.md`) — **3.0× smaller than
  today's post-S2 375 KB** (4.5× vs pre-S2), and ~4.8× smaller than nothing: the Epoch-2 floor
  moves the knee again. At floor scale, LDE volume at lb 8 ≈ today's at lb 6 (21.2M vs 25.2M
  cell-evals).
- **Verified cost today:** the gate floors admit (8,15,16) → 136/76 and (8,14,16) → 128/72
  against floors 128/71 (`circuit-prove/tests/fri_params_soundness_budget.rs:185,196`), and the
  gate's own doc records that lb 6→8 improves every numeric floor. Unused knobs:
  `commit_proof_of_work_bits` hardwired 0 (`circuit/src/plonky3_prover.rs:176`) and
  `log_final_poly_len = 0`, never in any grid. [P]/[M-dated]. **CONFIRMED** on every checkable
  fact; the payoff endpoint is a model number.
- **Expected yield:** projected ~151 KB → ~115–125 KB at the floor shape **[A]**; the measured
  old-era (8,15)-vs-(6,19) delta was −11.5%, so treat 115–125 as the optimistic end until the
  measurement lane runs. Also the only lever that shrinks every query-proportional term the
  recursion wrap re-verifies.
- **Fix sketch:** re-run `ir2_fri_grid` at post-S2 and mocked-floor widths; push candidates
  through the Lean `dregg_fri_ledger` — ε_C (commit-phase, height-dependent) already binds BELOW
  the Johnson column, so the two closed-form columns are not sufficient. Carry the gate's own
  label: capacity-128 is a refuted-conjecture drift canary, not security headroom.
- **Effort:** 1 measurement lane + ledger pin update. **Risk:** regen (FS change).
  **Dependencies:** measure now; land the flip with/after the Epoch-2 FS epoch. Related [U]: the
  recursion wrap re-verifies 38q at (3,38,pow14) — the same up-blowup logic would shrink the gnark
  wrap circuit; scope unknown.

### E5 — split the 897-col map-ops monolith (rank 5)

- **What/where:** `Ir2Air::MapOps` is always MAP_WIDTH=897 (`descriptor_ir2.rs:1913,2132`); the
  op≤3 layout ends at col 421 and everything in [421,897) is structurally zero on op≠4 rows
  (`:1874-1876`). `heapWriteVmDescriptor2R24` and `refusalVmDescriptor2R24` carry only
  `map_op write`, so their committed map instance is 53% all-zero columns on every row.
- **Verified cost today:** 476 dead cols × 75.6 B/col ≈ **36.0 KB** wire on heapWrite/refusal
  proofs; the full 897-col instance ≈ 67.8 KB on each of the 10 map-carrying members — a line
  item the transfer-calibrated review never priced. [P] structure **CONFIRMED**, [A] pricing
  (model not measured on an h=8 aux instance).
- **Fix sketch:** split into op≤3 (width 421) and AAFI (897) arms selected off the constraint
  list exactly like `map_absent` already is (presence flag + width fn + Lean twin).
- **Effort:** 1 lane. **Risk:** regen. **Dependencies:** independent; rides any regen.

### E6 — delete the `absent` map op (subsumed by `aafi_insert`) (rank 6)

- **What/where:** On all 7 absent-carrying members the `absent` op and the `aafi_insert` have the
  same guard, same key (var 68), same 8-felt root group, and absent's new_root == root [P,
  TSV parse]. The AAFI arm already carries the pointer-bracket non-membership proof
  (`low_addr < key < low_next` against the same root, `descriptor_ir2.rs:1906-1913`;
  `imtAbsent_excludes`), and `noteCreateVmDescriptor2R24` already inserts with no absent op —
  the in-registry existence proof.
- **Verified cost today:** the entire MapAbsent instance (MA_WIDTH=358) ≈ 18–27 KB [A] + one
  BUS_MAP_LOG interaction + **one full 16-deep witness node8 chip path (~16–17 unique perms)** per
  carrier. noteSpend/createCell miss the chip-64 cliff by ONE permutation — deleting a whole
  witness path is strictly stronger than the D6 one-terminator consolidation. Hunt-only.
- **Fix sketch:** Lean lemma that the emitted `aafi_insert` discharges the `opensTo none`
  conjunct the kernel refinement consumes (mirror of `imtAbsent_excludes` inside `imtInsert`);
  then stop emitting absent ops; MapAbsent AIR + MA_* layout (~200 lines Rust + Lean twin) go dead
  registry-wide.
- **Effort:** 1–2 lanes. **Risk:** regen, gated on the Lean lemma (the lemma is what keeps this
  out of semantic-change territory). **Dependencies:** independent; combines with E3 on the cliff.

### E7 — by-name predicate/membership zoo re-emit (rank 7)

**STATUS 2026-07-19: census CONFIRMED (full per-column parse of the deployed bytes at
`ea75575c0`) + the narrowing-soundness bridge LANDED
(`metatheory/Dregg2/Circuit/ChipNarrowLookup.lean`, CI-rooted, #assert_axioms-clean), committed
`9959af6cc` and independently re-derived by an adversarial verifier pass (byte-exact: 387/1,857 =
20.8%, per-member table reproduced; two immaterial nits that do not drive value — see the
2026-07-19 round note). The bridge is model-level (DescriptorIR2 denotation) — it does NOT touch
the FRI floor or the Rust LogUp impl. Bytes untouched; what remains is the single mechanical regen
lane below (BUNDLED-CUTOVER §E7).**

- **What/where (CONFIRMED, was hunt-only):** the graduated-lane idiom (7 unused permutation
  lanes per single-output chip site) is endemic in the non-rotated Lean-emitted descriptors.
  Hunt figures reproduced exactly on 8 of 9 members (note-spend-leaf measures **126** lookup-only
  + 8 unreferenced = 134/149 (89%), hunt said 125; cross-side-existence-v2 measures **18**/24,
  hunt said 17; every other figure exact: blinded 29/33, attested-fact 29/34, merkle-depth2
  21/24, predicate-arith 20 of 25–27 each, 4ary-general 7/18, non-revocation 15/27,
  bundle-tree-fold-v2 8/10).
- **The census refinement the hunt missed — lookup-only ≠ killable.** A lookup tuple entry is an
  expression over committed columns, so a free witness read only at tuple INPUT positions
  (siblings, blinding factors — 34 cols on note-spend-leaf alone) must STAY committed. The
  mechanically killable set is columns at output-LANE positions 18..24 only, plus fully
  unreferenced cols: **387 of 1,857 committed columns (21%) across the 26 parsed members**, and
  every digest (out0) column is read downstream (no dead lookups — the narrow swap covers every
  site). Per-member kill (width → new width): note-spend-leaf 84 lanes (12 chip LUs) + 8 unref
  {15, 55–61} = 149→57 (−62%); attested-fact 34→13; blinded-membership 33→12; blinded-4ary-d2/d8
  27→13 each; merkle-depth2 24→10; 4ary-general 18→11; predicate-arith 25→11 ×4, neq 26→12,
  inrange 27→13; non-revocation 27→13; non-rev-adjacency 37→23; adjacency-membership 32→18;
  dfa-routing 22→8; dyck-parse 38→24; bound-presentation 29→22; turn-chain-binding 14→7;
  poseidon2-hash-arity2 10→3; derivation 386→378 (7 lanes + unref col 0);
  cross-side-existence-v2 24→10; bundle-tree-fold-v2 10→3. Zero killable on
  automatafl-step/resolve, accumulator-nonrev, bridge-action, field-delta-result-range,
  presentation-freshness, quantified-absence, temporal-predicate (all columns algebraically
  read).
- **Soundness core (LANDED, byte-safe):** the combinator already existed —
  `NarrowChip.lean::chipLookupTupleNarrow`/`siteLookupNarrow` (18-wide `[arity, ins(16), out0]`
  on `poseidon2narrow` = `.custom 3` = wire 8 = Rust `TID_P2_NARROW`, whose parse/AIR/multiplicity
  plumbing is deployed with zero users). What was missing and is now proven
  (`ChipNarrowLookup.lean`): `narrowTable_sound` — the 18-PREFIX of the deployed wide chip table
  is `ChipTableSoundNarrow` (the model of Rust `narrow_hist`: ONE physical chip serves both
  buses), so `chip_lookup_sound_narrow` fires with no assumed hypothesis;
  `chip_lookup_narrow_sound_of_wide_table` (identical digest equation forced);
  `narrow_served_by_same_rows` + holdsAt twins (completeness: no honest witness lost).
- **Verified cost today:** 21% of zoo committed width (55–70% on the payment-path members), at
  per-predicate / per-payment frequency. These descriptors are separate Lean emit modules —
  **the Epoch-2 chip changes do not re-emit them**; without a pass of their own they keep the
  old shape forever.
- **Staged regen recipe (ONE mechanical lane, post-Epoch-2):** (1) in each by-name emit module
  (`NoteSpendingLeafEmit`, `BlindedMembershipEmit` (+4ary), `AttestedFactMembershipEmit`,
  `MerkleMembership{,4ary}Emit`, `Predicates{Arithmetic,Gt,Le,Lt,Neq,InRange}Emit`,
  `NonRevocation{,Adjacency}Emit`, `AdjacencyMembershipEmit`, `DfaRouting*`, `DyckParse*`,
  `BoundPresentationEmit`, `EffectVmEmitTurnChainBinding`, derivation/cross-side/bundle-fold
  producers) swap `.lookup {table := .poseidon2, tuple := chipLookupTuple ins digestCol
  laneCols}` → `.lookup {table := poseidon2narrow, tuple := chipLookupTupleNarrow ins
  digestCol}`, delete the lane columns from the layout, renumber densely, drop note-spend-leaf's
  8 unref cols + derivation's col 0; (2) swap `chip_lookup_sound` for
  `chip_lookup_narrow_sound_of_wide_table` / `narrow_lookup_holdsAt_sound` in each Refine/Rung2
  proof (identical conclusion — mechanical); (3) regenerate GOLDEN strings via `emitVmJson2` +
  re-emit `by-name/` through the emit script (drift gate recurses into by-name); (4) Rust twins:
  layout consts + witness builders stop filling lanes (e.g. `membership_descriptor_4ary.rs`
  `MEMBERSHIP_4ARY_WIDTH` 18→11, `LANE_BASE` deleted); prover side needs NOTHING (narrow serving
  is live); (5) canaries: honest prove+verify per member + each module's forge teeth re-run.
  Mints new VK/bytes for all 24 touched members — cannot run parallel with other regens. Fold in
  the 1-felt waist fix (SenderAuthorized authorized-set root is a single ~31-bit felt,
  `turn/src/executor/membership_verifier.rs:1076-1101` → 8-felt root + wide-tag chain) — that
  component is semantic-change and can ride the same regen.
- **Effort:** 1 lane + regen (census + proofs done). **Risk:** regen (waist fix:
  semantic-change). **Dependencies:** sequence AFTER the Epoch-2 chip retype so the sweep
  happens once.

### E8 — bilateral aggregation v2: delete the self-checked expected block (rank 8)

**STATUS 2026-07-19 (continued): soundness core PROVEN byte-safe + verified CONFIRMED
(`b0c73d084`). `BilateralAggregationCompact.lean` (14 `#assert_axioms` clean) machine-checks the
width-87→52 compaction against the deployed `Satisfied2` — v3 accept-set ⊆ v2 (injective expand,
contract∘expand = id), STRICT via an exhibited middle-row `turn_hash[0]=7` forgery v2 accepts and v3
refuses; the per-row-CG-2 doc overstatement is now falsified by exhibit and corrected comment-only.
Bytes untouched; the cutover is staged (BUNDLED-CUTOVER §E8). Verifier caveat: rooting the
now-un-orphaned Emit/Refine/Rung2 modules leaves 3 stale `scripts/lean-orphans-allow.txt` entries
that red `check-lean-orphans.sh` — de-list at cutover (§E8 step 5).**

- **What/where:** `dregg-bilateral-aggregation-v2.json` (width 87, 70 constraints): **35 of 38
  gates are exactly `sched[13+i] == expected[49+i]`, and both blocks are filled by the prover from
  the same `AggregationInnerRowV2`** (`circuit/src/bilateral_aggregation_air.rs:332-408`); no PI,
  boundary, or lookup pins the expected block externally. Identity PIs bind first/last rows only —
  middle rows' turn-identity columns are unconstrained. Live per multi-cell turn via
  `node/src/api.rs:3989-3997` + wasm. **CONFIRMED** (verifier 2, full constraint-by-constraint
  parse).
- **Verified cost today:** 35 duplicated cols + 35 gates per bilateral-turn proof (height small,
  so cells minor — the cost is a whole extra per-turn instance, a claims gap, and dual maintenance
  of the legacy 112-col and v2 87-col layouts in one file).
- **Fix sketch:** drop the expected block (width 87→52) and pin the schedule per-row via a window
  gate on the identity slots; re-emit from `EffectVmEmitBilateralAgg.lean`. Also fix the doc-level
  claims: per-row PI equality is overstated today, and the `edge_fp` "~124-bit" collision claim
  (`bilateral_aggregation_air.rs:563-585`) is wrong for a 1-felt output (~31-bit; the off-AIR
  multiset check is what closes it).
- **Effort:** 1 lane + regen. **Risk:** semantic-change (middle-row strengthening — in the
  strengthening direction). **Dependencies:** independent; can fold into E9(b)'s rebuild.

### E9 — joint-turn binding leaf: delete it or make it real (rank 9)

- **What/where:** `JointTurnAggregationAir` (`circuit-prove/src/joint_turn_aggregation.rs:
  1360-1411`) has exactly 4 constraints; the `hash_4_to_1` accumulator fold is computed host-side
  only, so `bundle_digest` is a free witness in-AIR and col 1 (`cell_commit`) is read by zero
  constraints. It is a hand-written Rust AIR (Lean-authored-AIR law violation), its anchors are
  1-felt (tid = TURN_HASH[0]; digest content = PI 43, the bare-V3 ~31-bit stratum — zeroed on wide
  members), it gets its own recursion wrap (`joint_turn_recursive.rs:293-334`), and the joint tree
  passes no expose hook, so nothing ties binding rows to the leaves in-circuit. The recursive fold
  has zero production callers (own test + perf only). [P], both hunt lenses agree; verifier-read
  adjacent facts confirmed.
- **Verified cost today:** per joint turn on that path: 1 uni-STARK + 1 recursion wrap
  (~tens of seconds at the ~80 s/layer scale) + 1 extra agg leaf, attesting what the host gate
  already checks; plus the standing in-circuit/host soundness asymmetry.
- **Fix sketch:** (a) delete the binding proof and have the verifier recompute the
  1-hash-per-cell chain over the leaf PIs it already checks; or (b) port the segment pattern —
  expose each leaf's tid via `prove_descriptor_leaf_with_pi_slice_expose`
  (`ivc_turn_chain.rs:1028`) and `connect` at the combine, wide 8-felt tail as content. All
  machinery exists.
- **Effort:** (a) <1 lane; (b) ~1 lane. **Risk:** semantic-change (posture change either way, in
  the honest direction). **Dependencies:** (b) rides the Epoch-2 tag retype; neither inherits the
  bundle otherwise (this AIR does not use the chip).

### E10 — frozen-authority: falsifier on the 41, dedup on the 16 (rank 10)

**STATUS 2026-07-19 (continued): falsifier landed byte-safe + verified CONFIRMED (`a8cd5e35f`).
`zzz_e10_freeze_owner_falsifier.rs` proves the deployed AIR/verifier ACCEPTS a self-consistent
`cellSealVmDescriptor2R24` seal whose only moved variable is the AFTER owner octet
(`B_PUBKEY_OCTET` 105–112), while the control lifecycle-freeze forgery is REJECTED — so the `[U]` on
the no-freeze class is now `[M]`: a real witness-gen faithfulness hole `apply_cell_seal` never
produces. Root read (not asserted): cellSeal is `graduateV1 (rotateV3WithLifecyclePayloadGate …)`,
not `v3OfFrozen`, so the pubkey octet is unforced on either path, and `proof_verify.rs:552` binds
NEW_COMMIT to the prover's CLAIMED post, not a re-execute. The 16-carrier dedup and the real close (a
Lean-authored owner-freeze colEq) are staged (BUNDLED-CUTOVER §E10).**

- **What/where:** Only 16/57 members carry the 83 freeze-shaped colEq gates (AFTER limb k =
  BEFORE limb k at delta 179); **41 members have zero freeze-shaped colEq at any delta** [P].
  Whether each such member's semantic gates + verifier-side PI reconstruction
  (`trace_rotated.rs:665-686`) fully compensate is **[U]** — this is the witness-gen-perimeter
  axis made member-precise. Separately, on the 16 carriers the 83 AFTER columns are pure
  duplicates by constraint.
- **Verified cost today:** 83 cols ≈ 15.6 KB wire + 5.3K cells per proof on the 16-member class,
  plus 83 gates. [P] parse; hunt-only (two lenses agree on the 16-member list).
- **Fix sketch:** falsifier first (hours, byte-safe): forge a changed owner-limb on
  `cellSealVmDescriptor2R24` and observe what rejects it — AIR, executor, or nothing. Then emit
  the AFTER absorb tuples referencing the BEFORE columns directly for frozen limbs (absorb tuples
  are arbitrary `LeanExpr::Var` refs; the weld-tower layering is the only thing forbidding it) —
  deletes the 83 cols AND the 83 gates. The anchor stays a function of the state snapshot alone
  (`cell/src/commitment.rs:1320-1377`); column sharing changes no published value. Note: sharing
  kills width, not absorb count — both chains still absorb all 178 limbs.
- **Effort:** falsifier hours; dedup ~1 lane. **Risk:** falsifier byte-safe; dedup regen.
  **Dependencies:** dedup rides the Epoch-2 emit; falsifier independent, run early.

### E11 — retire the Golden-v1 accept surfaces; then re-pin the gate floor (rank 11)

**STATUS 2026-07-19 (late, E11-prodread): PRODUCTION-PATH READ DONE — pow-14 is NOT necessary on
the live prove/verify path; the suspended lever un-sticks, re-scoped as an ACCEPT-SURFACE
RETIREMENT (not a dead-code deletion).** Full-depth read of every `create_recursion_config`
(lb 3/38q/pow 14) edge at HEAD `f4e7f871f`:

- **The live finalized-turn path never touches pow-14.** Node commit pipeline
  (`node/src/turn_proving.rs:1082` — "the live capability-gated node turn proves ROTATED") →
  rotated tree + joint aggregation run wall-to-wall at `ir2_leaf_wrap_config()` =
  `(6,19q,pow 16, arity 2)` (`ivc_turn_chain.rs:941-957/2173/2602/2913`,
  `joint_turn_aggregation.rs` HEAD `:780/:908/:1047/:1154`); GPU dispatch at
  `create_gpu_ir2_leaf_wrap_config()` (`gpu_backend.rs:4522/:4583`); root verify =
  `verify_recursive_batch_proof_with_config(root, &ir2_leaf_wrap_config())`
  (`ivc_turn_chain.rs:2661/:3898`). The 07-19 refutation's three "production-live" edges dissolve
  under reading: (1) `gpu_backend.rs:4459` passes `create_recursion_config()` into a parameter
  literally named `_cpu_config` — IGNORED (pure postcard re-tag, `:4468-4484`), and its sole
  callers are `tests/gpu_recursion_fold_e2e.rs:159/:357` (production dispatch calls
  `_with_lookups` directly); (2) the pow-14-defaulted inner-FRI wrappers' only non-test
  reachability is the Golden-v1 chain below, which has NO producer; (3) the
  `node/src/mcp/proof.rs` "reference" is one stale comment (`:426`) naming a DELETED demo command
  (`cmd_make_recursive_witness`), inside a function that unconditionally errors — the v1
  standalone effect-vm material is hard-retired (`proof.rs:431-440`).
- **The Golden-v1 producer is caller-less.** `RecursiveProofProducer::produce` is reached only via
  `turn::from_components_with_compression(.., true)` / `from_components_strict_recursive` —
  ZERO callers of either in the tree (the one caller passes `false`,
  `turn/src/witnessed_receipt.rs:403`). Its inner AIR `EffectVmShapeAir` is self-described
  NON-soundness-equivalent (structural subset; `recursive_witness_bundle.rs:51-58`).
- **What IS still live at pow-14: verify-only ACCEPT surfaces for a producer-less artifact class.**
  `dregg-verifier scope-recursive` (`verifier/src/main.rs:49/:369`) →
  `replay_chain_recursive` → `verify_recursive_proof_variant` →
  `verify_recursive_layer_bytes` → `verify_recursive_batch_proof` (default pow-14 engine); plus
  exported-but-uncalled `verifier::verify_recursive_replay` (its named producer type
  `RecursiveIvcStep` does not exist in the tree) and the `cross_fed.rs:601-614` passthrough
  transcode (field always `None` in production). This is why the re-pin was rightly HELD: until
  these accept surfaces are removed, a field verifier still ACCEPTS proofs at the 71-Johnson
  knobs, and re-pinning the gate over "surviving configs" would launder exactly that gap. The
  honest order is: retire the accept surfaces and re-pin the gate IN THE SAME CUTOVER.
- **What/where (scoped stratum, ~900 core lines + plumbing):** `recursive_witness_bundle.rs`
  (590) + `effect_vm_p3_air.rs` (296); turn-side constructors/`RecursiveProofVariant`/
  `WitnessBundle.recursive_proof`; verifier-side `scope-recursive` +
  `verify_recursive_replay{,_from_bundle}` + `replay_chain_recursive` + DTOs + cross_fed arm;
  `create_recursion_config` + its default-config wrappers (keep `_with_config` forms);
  `create_gpu_recursion_config` (`gpu_backend.rs:3970-3986`) + the `gpu_recursion_proof_to_cpu`
  default wrapper; demo scope-recursive checks. Tests that need a FOREIGN config for rejection
  teeth (`ivc_turn_chain_rotated.rs:617-673` VK-pin tooth, `descriptor_leaf_recursion.rs`) keep
  minting from a TEST-LOCAL `create_recursion_config_with_fri(3,0,1,38,0,14)` — they need *a*
  foreign config, not *the shipped* one.
- **Verified cost today:** 0 proof bytes (this was never a wire lever) — the payoff is the gate
  floor un-pin: Johnson 71 → 73 (the (6,19,16) set becomes weakest), capacity 128-exact-zero-
  headroom → 130, commit-column weakest moves off `recursionConfig` (Lean ledger:
  `FriLedgerSound.lean:385-389/:696/:714-716`); plus ~900-line TCB shrink; plus retiring a
  non-soundness-equivalent shape-AIR accept surface (soundness-positive). [M] census at HEAD.
- **Fix sketch (STAGED — an FS/accept-surface cutover, NOT a descriptor regen):** no descriptor,
  member VK, or staged TSV byte moves (`compute_recursive_vk_hash` is its own VK universe and
  dies with the stratum). One cutover lane: delete stratum + accept surfaces; re-pin
  `fri_params_soundness_budget.rs` (`shipped()` 7→6, `DEPLOYED_JOHNSON_FLOOR` 71→73 read FROM the
  Lean ledger, not asserted) and move the `recursionConfig` FriLedgerSound theorems to a
  retired/historical section; canary = a stored Golden-v1 fixture chain flips VERIFIED →
  REJECTED. Wire decision at cutover: keep `WitnessBundle.recursive_proof` field but reject
  `Some` (postcard/witness_hash-stable) vs remove field (shape change).
- **Effort:** 1 lane + canary. **Risk:** accept-surface change to the shipped `dregg-verifier`
  CLI (subcommand removal is user-visible); zero regen risk. **Dependencies:** independent of the
  Epoch-2 regen bundle, but MUST bundle its own gate re-pin with the surface removal (never
  split them).

### E12 — pin children on the wide and joint tree folds (rank 12)

- **What/where:** The module doc claims every child folds through
  `into_recursion_input_pinned` (`ivc_turn_chain.rs:171-183`); true for the scalar tree
  (`:3708-3732`), false for the wide tree (`:2467-2468`, bare `into_recursion_input`) and the
  joint tree (`joint_turn_recursive.rs:371-372`). The wide tree is the staged flip-precursor.
  [P], hunt-only.
- **Verified cost today:** the foreign-child seam the pin was built to close, re-opened on 2 of 3
  paths; plus doc-vs-code drift; plus FOUR near-duplicate tree folds at three soundness levels.
- **Fix sketch:** route wide + joint through the pinned farmable primitive (needs an 8-felt twin
  of `merge_two_segment_proofs`); consolidate the folds while there.
- **Effort:** 0.5–1 lane. **Risk:** semantic-change (closes a seam). **Dependencies:** land
  BEFORE the wide-tree flip ships.

### E13 — retire the legacy Memory table; kill the lone degree-8 gate (rank 13)

- **What/where:** `setFieldDynVmDescriptor2R24` is the sole carrier of `mem_op` in either
  registry; it alone keeps `Ir2Air::Memory` (18 cols, `descriptor_ir2.rs:1713`) + `MemBoundary`
  (28 cols, `:1726`) + BUS_MEM_LOG/CHECK/ADDRS (`:354-356`) + their Lean surface deployed — the
  flat-address regime the universal memory table superseded. The same member holds the registry's
  only main gate above degree 2: `∏k=0..7 (col69 − k)` — **CONFIRMED** (56 members deg ≤2, this
  one deg 8), forcing an 8-chunk main quotient where siblings sit at 2.
- **Verified cost today:** ~46 committed cols + byte-table pull + 2 instances on setFieldDyn
  proofs (~3–4 KB) — plus two AIR arms, three buses, and a boundary discipline maintained for one
  member's dynamic access to an 8-slot bank the static setField siblings already cover.
- **Fix sketch:** re-emit the dynamic slot as an 8-way one-hot mux in main (~8–16 cols, all
  deg ≤2) or as a umem op; delete Memory + MemBoundary + BUS_MEM_* wholesale; main-side degree
  becomes uniformly ≤2 registry-wide. Check the odd `value == addr` (both var 69) on the wire
  **[U]** before migrating.
- **Effort:** 1–2 lanes. **Risk:** regen. **Dependencies:** VK regen rides Epoch-2.

### E14 — flip the umem boundary to the cohort form (rank 14)

- **What/where:** All 57 welded members carry exactly one `umem_op` write — precisely the cohort
  eligibility — but the Lean emitter hard-codes `cohort := false`
  (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitUMemWeldWide.lean:83-86`, no justification stated),
  so every welded proof commits the width-38 GENERAL boundary (UB_WIDTH=38) instead of the
  width-9 cohort AIR (UBC_WIDTH=9) that is built, proven, and routed by zero registries — a second
  narrow-bus-pattern instance. **CONFIRMED, every link** (including that even the
  `umem-cohort-*-staged` TSVs declare the general sem).
- **Verified cost today:** 29 extra cols + the general form's key canonical-decomp +
  lex-comparator byte sends per welded proof ≈ 2–3 KB × 57 members [A]; plus the built-dead UBC
  code.
- **Fix sketch:** flip `cohort := true` in `weldUMemIntoWide` AND swap the hard-coded general
  `umemBoundaryTableDef` (the verifier's nit: it is not one word) + Rust byte-parity pin + regen.
- **Effort:** 0.5 lane. **Risk:** regen. **Dependencies:** independent.

### E15 — cross-cell conservation: route or retire (rank 15)

- **What/where:** The live per-asset Σδ=0 gate is Rust arithmetic
  (`turn/src/executor/proof_verify.rs:1712-1767`); the Lean-proved CCC AIR is self-documented
  "ADDITIVE — NOT wired" (`cross_cell_conservation_air.rs:37-41`). The v2 descriptor spends
  **154 of 172 columns on bit-decomposition range checks** while the batch's byte table exists.
  [P], hunt-only.
- **Verified cost today:** ~0 prover cycles (unrouted), full maintenance (Lean twin, 201 pinned
  constraints, tests) + the good-one-dead/weak-one-deployed pattern.
- **Fix sketch:** decide. Retire = trivial. Route = re-emit with byte-bus range lookups
  (172 → ~30 cols) + the verifier wiring its own docs describe.
- **Effort:** 0–2 lanes by branch. **Risk:** retire byte-safe; route semantic-change (posture
  improvement). **Dependencies:** independent.

### E16 — ops-layer routing: accumulator, envelope freight, anchor decider, shrink packing (rank 16)

- **(a)** The node re-wraps ALL retained turns from scratch per fold request
  (`node/src/mcp/handlers_verify.rs:151-160`); the O(1) online accumulator is built and unrouted.
  Cost: O(K) × ~80–130 s/node re-paid per request [M-scale from the apex measurements]. Fix:
  route the accumulator or cache leaf wraps by turn hash. ~1 lane.
- **(b)** Every whole-chain envelope carries and verifies the binding-descriptor proof declared
  non-load-bearing (`ivc_turn_chain.rs:1585-1588`, `:3839`; `accumulator.rs:58-60`) — ~100 KB
  [A-rough, unmeasured [U]] + O(n) `seam_pairs` accumulator state. Fix: optional/drop at the
  Epoch-2 FS re-pin (envelope v5); coordinate lightclient/wasm. Small.
- **(c)** Root-VK anchor identity: K-dependence is documented; member-MIX dependence is
  plausible and untested **[U]**. Decider: fold two 2-turn chains of different verbs, compare
  root VK fingerprints. Hours; if mix-dependent, make the wrap-normalized accumulator the sole
  anchor-bearing path (~1 lane).
- **(d)** Lever A shrink packing landed opt-in and the settlement path still proves at the
  default (`apex_shrink_gnark_export.rs:457-459`). One timed prove + flip the default. Hours.
- **Risk:** (a)(d) byte-safe; (b) regen; (c) decider byte-safe. **Dependencies:** independent.

### E17 — hygiene riders on the Epoch-2 regen (rank 17, each ≤0.5 lane)

- Tables-decl sync: declared-tables list is a facade (memory/map_ops declared by all 57, lookups
  grammar-forbidden; tid-84 used undeclared; decorative arities) and the D3 Δ47 arity fossil has
  now survived TWO regens — the fix is emit-side (sync `TableDef.arity` in the Lean weld layers,
  as the Rust welds already do), or it survives Epoch-2 as well. [P] regen.
- Welded placeholder members: noteSpend/noteCreate welded twins are producer-unexercisable
  placeholders inside an accepted-form registry the wire verifiers iterate
  (`EffectVmEmitUMemWeldWide.lean:71-72`; `effect_vm_descriptors.rs:1233-1237`) — filter them out.
  Adversarial-surface removal, not bytes. [P] regen.
- Fossil test registry: `rotation-wide-transfer-staged.tsv` (91 KB, one weaker shadow member)
  carries a byte-identity claim that is false at HEAD (`effect_vm_descriptors.rs:1203-1204`);
  demote to a test fixture or delete. [P] byte-safe.
- PI layout normalization: 36 of 68 PI slots bound by zero members (adds 1–7, 42–43 to D5's
  known set); wide-anchor start offset varies across 9 values (52/50/51/46/58/62/67/70/4) — the
  stale-index bug class. Fold fixed-position layout into the Epoch-2 PI-map regen. [P] regen.
- Duplicate gates + arity-3: seven capOpen members carry one literally duplicated gate; chip
  arity 3 has zero uses registry-wide — drop it from the admissible set at the one-hot retype.
  [P] regen.
- Strata freight: ~45 retired effect-VM JSONs (v1 + ir2-216 generations) still shipped/pinned/
  tested; `cap_delegation_nonamp` twin; hand `CrossSideExistenceAir`/`BundleTreeFoldAir` impls
  (with a width-8-vs-24 doc drift); binary membership twin. Quarantine or delete with the regen.
  [P] byte-safe.
- automatafl: hand-Rust AIR (813+773 lines, self-labeled "translation validation") still in-tree
  while the Lean-emitted step/resolve descriptors have zero in-tree consumers **[U]** — route or
  retire; the descriptors themselves are dense (no width wound). [P]/[U] semantic-change if routed.
- Byte-bus nibble pair-batching: 32 → ~20 interactions on transfer (−48 aux base cols ≈ −3K
  cells / 4–9 KB [A]) via paired lookups against a 256-row table — measure first: the dated
  PROOF-ECONOMICS measurement found the 2^8 table's LDE dominant at a different grid. [A] regen.
- Stale FRI-config docs at three load-bearing sites (`plonky3_recursion_impl.rs:380-391`,
  `ivc_turn_chain.rs:55,876-877`, `dregg_outer_config.rs:56-63`) — a lane retuning from the docs
  would mis-mint. Doc sweep, hours. [P] byte-safe.
- `edge_fp` claims fix (see E8). [P] byte-safe.

---

## Already tracked elsewhere (cross-references only)

- **Narrow-bus retirement** — Epoch-2 bundle (chip one-hot/tag retype, per-shape tuples); E7
  sequences after it; E14 is a second instance of the same built-but-unrouted pattern.
- **TURN_HASH limb widening** — Epoch-2 bundle; E9(b) rides the same tag retype.
- **Bare-V3 stratum retirement** — Epoch-2 bundle; E9's digest anchor is pinned to it today.
- **Heap-open wound** — tracked in the excellence backlog; E5/E6 touch the same map machinery but
  neither closes it. Related uncosted knob: HEAP_TREE_DEPTH=16 drives ~500 of MapOps' 897 cols
  (2^16 leaves per cell heap) **[U]**.
- **D5 PI-map regen / D6 chip-64 consolidation** — Epoch-2 scope; E17's PI item extends D5;
  E3+E6 subsume D6 follow-up #2 if taken.

## Graveyard — refuted, with corrections

- **REFUTED — registry-vestiges F1, transfer-level detail.** Claimed: 161 dead cols on transfer,
  including "cols 2..53 = 52 of 54 v1 selectors". Independent re-parse (verifier 2): **149** dead;
  cols 2–13 are referenced (transition hi/lo self-copies), the dead selector band is 14–53 (40 of
  54); registry total 8,847 not 8,851; share 8.5% not ~9%. Where registry-vestiges F1 and
  semantic-minimum F1 conflicted, semantic-minimum is correct; E1 carries the corrected numbers.
  The aggregate thesis (the dead-band class and its ~28–29 KB/proof cost) survives.
- **REFUTED — E11 deletion premise (2026-07-19 census).** Claimed: `recursive_witness_bundle` /
  `create_recursion_config` (lb 3/38q/pow 14) is "routed by zero production callers," so deleting
  the stratum lets the ledger floor "rise to the pow-16 set." Census: the pow-14 config is
  production-live (`gpu_backend.rs:4459` + the inner-FRI prove/verify wrappers in
  `plonky3_recursion_impl.rs`) and `recursive_witness_bundle` is referenced from
  `node/src/mcp/proof.rs`. It is NOT a dead stratum; a gate re-pin over "surviving configs" would
  launder a live weakest-column gap. E11 is downgraded to HELD-VERIFICATION (production-path read
  first); the width/line-count facts survive descriptively, the deletion + re-pin recipe is
  withdrawn. Unlike the F1 entry, no aggregate thesis survives here — the lever itself is suspended.
  *(Superseded 2026-07-19 late: the E11-prodread deep read resolved the suspension — the grep-census's
  three edges are config-inert (`_cpu_config` ignored at `gpu_backend.rs:4468`), producer-less, and a
  stale comment; pow-14 is NOT live-necessary. The lever un-sticks as an accept-surface retirement —
  see E11 for the honest ordering: surfaces and gate re-pin in ONE cutover.)*

Corrections absorbed into confirmed items (adjusted, not refuted):

- E2: "638 ms at HEAD" was the pre-S2 [M] figure; post-S2 ≈ 425–440 ms [A]. "~17 leaf adapters"
  → 15. Flat "~3×" hashing → ~3.8× on the commit-phase term only; whole table < 3×.
- E4: "measured on a member ~4.6× smaller than today's" → 3.0× vs today's post-S2 proof (4.5× vs
  pre-S2). The 115–125 KB endpoint is [A] model projection; measured old-era delta was −11.5%.
  Capacity-128 is a drift canary, not headroom.
- E14: "one-word Lean change" understated — the weld also hard-codes the general boundary
  TableDef; still ~0.5 lane.
- E8: the finding's own doc-critique stands — "per-row PI slots equal the outer PI's" in the v2
  doc overstates; bindings are first/last row only.

## Open unknowns worth one probe each

- E1: identity of the 34–39-col dead bands on note/refusal/heap members (read the note-region
  emit before compaction).
- E10: RESOLVED (`a8cd5e35f`) — nothing at the AIR/verifier level rejects a forged owner-limb on
  the no-freeze class; it is a proven witness-gen faithfulness gap (close = the §E10 owner-freeze colEq).
- E13: setFieldDyn's `value == addr` mem-op oddity.
- E16(c): member-mix invariance of the K-fold root VK.
- Pre-freeze item 3: fold-side cost of the Epoch-2 floor-shape branches (absorb instance /
  preprocessed round) in every leaf-wrap circuit.
- AT-F8: whether the two 30-bit after-balance range teeth (wires 76/77, on 41/57 members) remain
  necessary once the wide chain + avail weld carry the balance limbs — needs the Lean weld
  semantics, not the wire.
- Descent's prove entry (assumed to ride the custom wide member; untraced).

## Top-3 recommended next moves after the Epoch-2 bundle

**1. Run the dead-band compactor (E1, folding E5).** This is the same shape as the S2 lane that
already landed and measured −181,757 B, so both the method (`compactS2` + `compactOk` gate) and
the pricing (188 B/col, [M]-calibrated) are proven; the delta is a per-member kill-set instead of
a uniform one, plus the map-ops arm split. Expected return is ~29 KB/proof mean across all 57
members and ~36–68 KB on the map-op members, all pure deletion at regen risk class. If the
Epoch-2 regen window is still open it rides for free; if not, this lane justifies its own regen
day and becomes the natural vehicle for the E6, E13, E14, and E17 riders — and for E3 if the
mutable-last schedule missed the freeze. One prerequisite probe: name the 34–39-col unidentified
bands (RV-F8) before the compactor eats the evidence.

**2. Resolve the arity probe and delete the double-prove (E2).** Once the bundle lands, the main
proof stops being the settlement bottleneck — the recursion stack is >99% of latency, and its
dominant term is commit-phase Merkle hashing inflated ~3.8× by a fold-by-2 choice that was
explicitly a diagnostic probe, never a decision. One lane exercises the recompose path at
arity >1 against a real `ir2_config` proof; if green, the per-turn re-mint deletes, the
config-type wall falls, and every leaf-wrap/agg/shrink circuit shrinks its hashing table — with
the −3-bit-per-fold soundness trade made explicitly through `dregg_fri_ledger` rather than
inherited from a comment. The gnark arity-8 `fold_row` is the long pole; bundle it with apex
lever B so the ETH wrap re-lands once.

**3. Run the FRI re-grid measurement lane (E4).** The deployed (6,19) point was tuned on a member
3× smaller than today's and ~4.8× smaller than the Epoch-2 floor; the gate's own floors already
admit (8,15,16) and (8,14,16), and the arithmetic says lb-8 at floor scale costs the prover what
lb-6 costs today. The lane is: re-run `ir2_fri_grid` at post-S2 and mocked-floor widths, push the
candidates through the Lean ledger (ε_C binds below the Johnson column, so the closed-form check
is not sufficient), and re-pin inside the same FS epoch the bundle already spends. Projected
return is ~151 → 115–125 KB [A] — and even the pessimistic measured-era −11.5% would make it the
cheapest large wire lever left, since below ~120 KB the only remaining levers are query count,
instance/round count, and Poseidon2 itself.
