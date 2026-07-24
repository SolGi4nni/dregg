# WOUND — narrowed-digest security boundaries (the felt-width class)

**Opened 2026-07-19.** Found while chasing an unrelated FRI-soundness question ("why an 8-to-1
fold?"). The 8-to-1 fold is fine (costs `log₂7 ≈ 2.8` bits, documented). But the question surfaced
the *real* version of the worry: places where a Poseidon2/BabyBear digest (8 felts, ~124 bits) is
silently squeezed to **one felt (~31 bits, birthday-collidable at ~2^15.5)** and then used as a
**security boundary** — a commitment, a signed payload, a membership key, an authorizing equality.

The v10 / "faithful 8-felt" / `Faithful8` campaign was real and closed the sites it *targeted*
(cell state commitment, heap/fields/cap roots, umem boundary — `reference-umem-boundary-31bit` is
**closed at HEAD**). But it **widened roots, not key-spaces**, and its two defenses do not
generalize:

- `scripts/check-no-degraded-felt.sh` covers exactly **three files**
  (`cell/src/commitment.rs`, `turn/src/rotation_witness.rs`, `circuit/src/effect_vm/trace_rotated.rs`).
- The `Faithful8` type wall only bites where a value flows into a **typed octet sink**.

Every finding below lives in the **complement of both** — the class regrows there. The recurring
tell: **a doc-comment asserting collision-resistance over a value that has been squeezed to one felt.**

Provenance tags: **[V]** = verified by direct read this session · **[A]** = agent-read, not yet
independently confirmed · **[?]** = severity needs one more trace before pricing.

---

## Probe findings — deeper seams surfaced by the Lean-port recon (2026-07-19)

The four terrain probes turned up holes **bigger than felt-width**, and one correction to my own
readiness claim. Captured here so they ride the same campaign.

- **#15 Shielded `merkle_root` is wire-supplied, not pinned to the committed accumulator [A, HIGH].**
  `apply_shielded_transfer` (`turn/src/executor/apply.rs:1315-1412`) reconstructs the tree
  `from_serialized_parts(payload.merkle_root, …)` and verifies membership against **that** root — with
  NO check it equals the live committed commitment-tree root. A prover supplies a root of their choosing
  and proves membership in an attacker-built tree. Theft/inflation vector **larger than any birthday
  collision**; widening the felt does not fix it.
- **#16 Shielded value-link is honest-prover-trusted [A, HIGH].** `verify_value_link` (leaf-value ↔
  Pedersen-leg-value equality) is called **only in a test** (`circuit-prove/tests/shielded_transfer_m2a.rs`),
  never in `apply_shielded_transfer`. Conservation over `value_binding` is attested, not proved — the real
  inflation exposure, independent of the 31-bit width.
- **#17 Shielded PQ-commitment disagreement [A].** The Lean apex rests on Shor-broken Ristretto Pedersen
  (`commit_hidden_asset`, DLog) while `spend_circuit.rs:42-48` declares a "PQ cutover (Option A)" making
  the Poseidon2 `value_binding` authoritative — the two disagree on which commitment is load-bearing.
- **Consequence for #10:** the shielded pool is **not** "widen 3 felts." It is "port the Rust-authored
  `spend_circuit` AIR to Lean + pin `merkle_root` to the committed accumulator + fold the value-link
  into the AIR + resolve the PQ-commitment story." Felt-width is the entry point, not the fix. Reachable
  only in a `prover`-enabled executor (verify-only fails closed); not in the committed VK.
- **Correction to #4/#10 (note/nullifier):** I over-claimed this as "finish an existing port." The
  accumulator NODE digests are 8-felt + proven (`DeployedHeapTree`/`SortedTreeNonMembershipHeap8`), but
  the note commitment/nullifier **value and the sorted key** are still 1-felt and UNSTARTED.
  **CORRECTION (07-20 scoping):** the "new bracketing math" fear was too pessimistic — the sorted-gap
  soundness (`Crypto/NonMembership.lean`) is already `[LinearOrder Digest]`-**generic**, so instantiating
  `Digest := Lex (Fin 8 → ℤ)` gives the whole adjacency bracketing FOR FREE (the IMT/Heap8 wrappers are
  ℤ-typed but their proofs never touch ℤ arithmetic — mechanical generalization, machine-confirmable by a
  one-section spike). The genuine new work is bounded and nameable: **one lex-`<`-over-8-felts AIR gadget**
  (✅ **LANDED / VERIFIED 2026-07-22** — `Circuit/Emit/LexCompare8Emit.lean::lexLt8_refines`: the emitted
  `lexLt8Descriptor` decides `toLex a < toLex b` as a proven iff (`lexLt8_sound`+`lexLt8_complete`, canonicity
  hypotheses explicit, teeth incl. LSB-decider limb-7 + p-boundary canary), with the order-corollaries +
  sorted-tree wiring bridge in `Crypto/Digest8KeySpike.lean` (`Digest8Key := Lex (Fin 8 → ℤ)`, `LinearOrder`
  via `Pi.Lex`, `sorted_gap_excludes_digest8`); `#assert_axioms`-clean, rooted, rebuild-confirmed), a
  **leaf-schema widening** (addr/nextAddr → 8 felts,
  arity-17 leaf), and the **easy value widening** (`hash_many→hash_many_8`, `felt_to_bytes32→digest8_to_bytes32`).
  The compare-gadget half is DONE; the residual is leaf-widening + value-widening + the ember-gated deploy.
  Still HIGH — but the cost is now just a leaf widening, **not new combinatorics**. Plus the
  **ember-gated, frozen** kernel flip (`NullifierAccumulator.lean:12-23`, "do NOT fire piecemeal").
- **#12 interface_id has NO Lean model and NO wide twin** — left behind when cap_root grew its `_8`.
  Reusable wide primitive exists (`Market/WideCommitBoundary.lean` `wireCommitR8`/`Poseidon2Width8`;
  Rust `hash_many_8`/`digest8_to_bytes32`). Anti-laundering: the fold accumulator must be 8-felt
  end-to-end, not just the final squeeze. Severity MODERATE (discovery/factory-identity, not funds).
  **CORRECTION (07-22): the "NO wide twin" half is STALE.** At HEAD `cell/src/interface.rs::compute_interface_id`
  is a FULL 8-felt fold end-to-end (`hash_many_8` at every step, `0x1FACE`+`len` seed, 8-lane sorted,
  `digest8_to_bytes32` tail) — the Rust widening ALREADY LANDED. **The Lean proof-half is now
  LANDED** (`metatheory/Dregg2/Cell/InterfaceIdWidth.lean`, rooted, `#assert_axioms`-clean): FALSIFIER
  `narrow_conflates`/`narrow_colliding_interfaces_share_vk` (the pre-widening 1-felt lane-0 leaf
  conflates two DISTINCT method sets ⇒ they share a `derive_service_factory_vk` factory VK), FIX SOUND
  `wideId_injective`/`wide_separates` (the deployed 8-felt fold is injective in the leaf list under the
  wide-hash CR floor `Function.Injective hash8`, a NAMED hypothesis), the exact anti-launder
  `finalSqueezeOnly_still_conflates` (widening ONLY the final squeeze STILL conflates), and the arity
  tooth `seed_arity_injective`. Site #12 is **byte-safe PROVEN** (Rust-fixed + machine-checked).

## Update log — 2026-07-24

- **#20 Spend delegation-ancestor key — NEWLY LOGGED, and the first EARNED
  `check-no-degraded-felt.sh` suppression in the tree.** `63a5bdd362` (the repair that restored the
  deployed `noteSpend` prove path, broken since the 07-23 descriptor sweep) threaded the producer
  half of `7d49b0f449`'s third map-op, `spendAncestorFreshOp`. Its honest "this spend rides no
  delegated capability" sentinel is `undelegated_spend_ancestor()`
  (`circuit/src/effect_vm/trace_rotated.rs:1402,1415`) = `fold_bytes32_to_bb(cred_nul(mint_provenance()))`
  — a 32-byte BLAKE3 nullifier squeezed to ONE felt. The ast-grep gate fired because
  `trace_rotated.rs` is one of its three scoped files. **The disposition below is a suppression, so
  it has to be argued, not asserted** — the reasoning, both directions, is at the site.

  - **NOT a commitment position (so not a law violation in the law's own terms).** The felt lands
    only in `row[PARAM_BASE + 3]` (col 71). The rotated commitment is `recompute_block_commit`'s
    chain over `row[BEFORE_BASE..]` / `row[AFTER_BASE..]` (bases 188 / 427); no PI binds col 71
    (`rotateV3WithNullifierPin` pins `prmCol 0` only). It is a map-op KEY in a witness column — the
    law's own "fine per-effect param projector" case. The ROOT it opens against is already faithful
    (the producer writes `revoked_tree.root8()` into all 8 lanes of `REVOKED_ROOT_GROUP`).
  - **Widening is NOT representable producer-side — verified, not assumed.**
    `Dregg2/Circuit/DescriptorIR2.lean:301-313` types `root, newRoot : Fin 8 → EmittedExpr` but
    `key : EmittedExpr` — a map-op key is ONE felt by construction, and the deployed op is
    `key := .var SPEND_ANCESTOR_PARAM_COL` (`EffectVmEmitRotationV3.lean:2410`). The INSERT side is
    one felt too (`revokedInsertOp` keys `param0` = `child_hash[0]`, `trace.rs:683`), so widening
    only the open side makes the `.absent` op unopenable rather than safer. 8-felt keys = change
    `MapOp` + lex-8 sorted/AAFI bracketing = **VK-affecting Lean AIR**, same epoch as #5/#11.
  - **Soundness: the width buys the attacker NOTHING here. Argued, not waved.** The set is keyed by
    the SAME projection on both the insert and the open side, and a projection is a function, so
    `A` revoked ⟹ `key(A) ∈ set` ⟹ the `.absent` open is UNSAT regardless of what collides with it.
    Collisions only ADD to the set's key-space preimage — they **over**-revoke, never under-revoke.
    A 31-bit collision cannot make a revoked ancestor look fresh at any width. (This is the *inverse*
    of the classic degraded-commitment danger, where a collision swaps the committed value; a
    non-membership op over a same-fold-keyed set has the opposite failure direction. Worth
    generalizing: not every narrow felt in this catalogue is a soundness felt — #5's key family
    deserves the same both-sides check before it is priced as a theft vector.)
  - **Availability: the width IS independently load-bearing, and this one is REAL — ~2^31, cheap,
    permanent, system-wide.** The revoked set is grow-only and its key domain is attacker-writable:
    `RevokeDelegation` inserts `hash_to_8(child_id)[0]`, and `CellId::derive_raw`
    (`types/src/lib.rs:891`) is BLAKE3 over an attacker-chosen `(public_key, token_id)` — so
    candidates are ground **offline**, no chain interaction until the hit. ~2^31 offline hashes find a
    child id whose lane 0 equals a chosen target; one legitimate create+delegate+revoke plants it
    forever. Aimed at THIS sentinel — public, fixed, system-wide — it permanently bricks every
    undelegated `NoteSpend`. Aimed at a victim's real ancestor id it bricks that lineage. With no
    adversary, N ancestors × M revocations collide at ≈ N·M/2^31 (~5% at 10^4 × 10^4), which caps the
    honest registry scale. **It gets worse when we do the right thing next:** today a producer could
    dodge a poisoned key only by exploiting the unbound-witness hole that `7d49b0f449`'s lineage weld
    is meant to close.
  - **Not to be confused with the bigger, separate hole.** Col 71 is an unbound witness column: a
    prover parks any non-revoked felt (this public constant will do) and the op is satisfied
    regardless of the exercised lineage. Zero work, pure soundness, `7d49b0f449`'s named follow-up —
    and **width-independent**, so it neither excuses nor is excused by #20. Both close in the same
    AIR epoch; neither closes the other.
  - **Rejected as a repair:** a producer-side "refuse to revoke a child whose key equals the
    sentinel" guard. It would block the systemic variant *via our own tooling only* — an adversarial
    prover mints the same trace, because the AIR accepts any key. That is a mitigation that looks like
    a fix, i.e. the laundering shape this catalogue exists to catch. Named here, deliberately not
    written.
  - **Kind D**, severity **HIGH for availability / NONE for soundness**. The 3rd `fold_bytes32_to_bb`
    the repair added is `cell/src/derivation.rs:1045`, inside `#[cfg(test)]` — the cross-crate domain
    pin, explicitly out of the law's scope and correct by construction (it must recompute the same
    value from the authority or the pin is vacuous).

## Update log — 2026-07-22

- **#18 + #19 zkOracle / render attestation commitments — NEWLY LOGGED, code NOT touched.** Two
  attestation welds were never in this catalogue. Both are in the complement of both defenses (not in
  `check-no-degraded-felt.sh`'s three files; no `Faithful8` sink on the path). Verified by direct read.

  - **#18 — `content_commitment` (the zkOracle CROSS-LEG WELD).**
    `zkoracle-prove/src/attestation.rs:47` is `pub fn content_commitment(response_body: &[u8]) ->
    BabyBear { hash_bytes(response_body) }` — one felt. `ZkOracleAttestation::content_commit`
    (`:89`) is that felt, and its doc-comment says it "bind[s] all three legs to the SAME response";
    it binds them to the same **~31-bit image** of the response. It then rides the narration data
    lane: `dungeon-on-dregg/src/narrator.rs:417-418`
    `fn attestation_commit_field(att) -> FieldElement { field_from_u64(att.content_commit.0 as u64) }`
    (same encoding again at `:1064` on the live-attest path), pushed as the second `data` field of the
    `NARRATION_TOPIC` `Effect::EmitEvent` (`:400-413`), and is read back off the committed receipt by
    the public `bound_attestation_commit` (`:316`) — a real consumer path, not a dead field.
    **The tell is the padding:** `field_from_u64`
    (`cell/src/program/eval.rs:2953`) writes the value big-endian into bytes `[24..32]` of a zeroed
    `[u8;32]`, so the receipt carries a 32-byte field whose leading 28 bytes are structurally zero —
    it **looks** like every other ~256-bit commitment on the wire and is ≤31 bits. Contrast the
    FIRST data field on the same event, `narration_commitment` (`:292-298`), which is a real
    domain-separated BLAKE3 32-byte `symbol` — the prose is bound wide, the attestation weld is not.
    Cost: ~2^15.5 to find two bodies sharing a `content_commitment`, ~2^31 to hit a chosen one. What
    breaks: WHICH authenticated oracle body backs a committed narration. Kind **C** — there is no
    wide `content_commitment`; one must be BUILT (⇒ Lean-authored, Rust calls in).
  - **#19 — `RenderAttestation`'s two welds.** `zkoracle-prove/src/render.rs:198`
    `pub output_commit: BabyBear` is the gate in `verify_render_attestation` (`:295`, recompute over
    the presented output, refuse mismatch); `:201` `pub template_commit: BabyBear` (from
    `template_commitment`, `:166`, `hash_bytes` over the segment encoding) is the gate in
    `verify_render_reproducible` (`:312`, "generated by THIS template"). Both single felts.
    `template_commit` is the load-bearing one — a collision is a **template substitution** that
    passes the reproducibility check. `output_commit` has a genuine compensating tooth: the colliding
    output must ALSO replay the same `CompactCert` (`verify_cfg_compact`, `:299`), which constrains
    the search to structurally-identical renders — real, but not a width argument. Kind **C**.

  **⚠ ANTI-PATTERN — do NOT repair these by re-hashing the narrow felts.** The obvious "widen it"
  move (`hash_many_8([content_commit, template_commit, …])`, or any wide fold seeded from the
  EXISTING `BabyBear`s) launders ~31 bits into a ~124-bit-looking digest: the wide output is a
  function of a 31-bit input, so its collision set is exactly the narrow one. This is the already-
  catalogued `finalSqueezeOnly_still_conflates` shape (#12, `Cell/InterfaceIdWidth.lean`) — proved
  there that widening only the final squeeze STILL conflates. The **correct** derivation re-hashes
  the REAL PREIMAGES, 8-felt end-to-end with no 31-bit waist anywhere in the chain: the response /
  output BYTES, the template's own structural encoding (`PromptTemplate::template_hash`,
  `attested-dm/src/prompt_template.rs:257-280` — an existing domain-separated BLAKE3 over
  `(data_from, segment count, per-segment tag ‖ len ‖ bytes)`, which is the right shape and is
  already 32 real bytes), and the bindings. Related prior art with the same waist: the recursion leaf
  `circuit-prove/src/zkoracle_leaf_adapter.rs` already keeps every INTERNAL carrier 8-felt but
  exposes a 1-felt claim lane, and its header names the un-done weld to `content_commitment` — that
  weld should be built at 8 felts, not by squeezing the leaf to match the narrow attestation.

  Code NOT changed in this lane; logged only.
- **#12 interface_id — PROOF-HALF LANDED, site byte-safe PROVEN.** Re-audit found it ALREADY
  Rust-widened at HEAD (full 8-felt `hash_many_8` fold, arity-seeded, 8-lane sorted,
  `digest8_to_bytes32` tail); the wound's "NO wide twin" was stale. Authored
  `metatheory/Dregg2/Cell/InterfaceIdWidth.lean` (rooted in `Dregg2.lean`, `#assert_axioms`-clean,
  `lake build` exit 0) — falsifier (1-felt lane-0 leaf conflates distinct method sets → shared factory
  VK), fold soundness (`wideId_injective` under the wide-hash CR floor), the anti-launder
  (`finalSqueezeOnly_still_conflates`), and the arity tooth. Mirrors the #1/`FinalityCertWidth`
  pattern. Nothing deployed touched.
- **#3 cap-uniqueness — PROOF-HALF LANDED, deploy stays gated.** Re-audit confirms the executor's
  leg-(1) root gate STILL compares the NARROW lane-0 `felt_to_bytes32(compute_canonical_capability_root_felt)`
  at HEAD (`commitment.rs:665`), while the off-chain state commitment already absorbs the WIDE
  `digest8_to_bytes32(compute_canonical_capability_root_8)` (`commitment.rs:684`). Authored
  `metatheory/Dregg2/Cell/CapUniquenessWidth.lean` (rooted, `#assert_axioms`-clean, `lake build` exit
  0) — falsifier (`narrow_capRoot_underdetermines`: distinct wide roots collide on lane 0), wide-encoding
  soundness (`wide_capRoot_determines`), the wound's own **"redundant projection" DOWNGRADE proved**
  (`narrow_root_is_projection_of_wide`/`narrow_gate_redundant`: the narrow value is lane 0 of the wide
  root the state commitment binds), and the compensating tooth (`accept_implies_unique`: uniqueness is
  the felt-independent leg-(2) dup-scan). **RESIDUAL:** widening leg (1)'s in-circuit gate ITSELF is a
  committed-state binding change (ember-gated deploy), out of scope; the security-carrying WIDE binding
  is already deployed, so the site is defense-in-depth-narrow, PROVEN redundant.

## Update log — 2026-07-20

- **#11 freshness/revocation rail — FOLD-IN LANDED (ember chose ①c(b)).** Redundancy premise
  CONFIRMED by read: the limb-26 `nullifierFreshOp` `.absent` map-op is the freshness authority over
  EXACTLY the set the deleted `DslRevocationTree::revoked_leaves` seeded (`full_turn_proof.rs`
  threads `FullTurnWitness::spent_nullifiers` → the limb-26 BEFORE tree; the `.absent` key IS the
  published nullifier `param0`; the BEFORE root8 is absorbed into the pinned OLD commit; forge
  test `circuit/tests/vk_epoch_notes_light_client_binding.rs`). DELETED: the whole 1-felt rail
  (`circuit/src/dsl/revocation.rs`, `non_revocation{,_adjacency}_witness.rs`,
  `NonRevocation{,Adjacency}Emit.lean` + the Refine/Rung2 satellite proofs + `descriptor_by_name`
  registration + the SDK `NonRevocationProof`/`NonRevocationWitness` component + verifier bindings
  (a)/(b) + `expected_revocation_root` threading). ADDED: `spendAncestorFreshOp` — the limb-37
  delegation-ancestor `.absent` open on spend turns (`EffectVmEmitRotationV3.noteSpendV3`, Lean
  single-file-checked; theorem `noteSpendV3_opens_delegation_ancestor`, #assert_axioms-clean).
  RESIDUALS (named): the ancestor key column (`param3`) is not yet in-circuit-bound to the cap
  lineage; registry re-emit + Rust spend-generator threading (param3 fill + revoked map-heap) are
  the integrator's; keys stay 31-bit (#5's lane). Freshness capacity 14 → 65534.

## Update log — 2026-07-19 (post-pricing, verified reads)

- **#6 CI exit_code — FIXED + VERIFIED GREEN.** `ci_verdict_public_inputs` now returns `Option`
  and REFUSES non-canonical exit codes (`exit_code_is_canonical` = `0 ≤ e < BABYBEAR_P`); prove →
  `Err`, verify → `false`. Canary `failing_exit_code_cannot_alias_into_the_pass_gate` +
  8/8 `ci_assurance::tests` pass (`--features substrate`). The trusted reconstructor is fail-closed
  by construction, so a future caller cannot reintroduce the alias.
- **#1 finality cert — CONFIRMED real, cost (a) ~2^31 offline hashes + 1 proof.** The `:686` segment
  tooth binds the aggregate to its own execution, NOT the committee's *signature* to the wide root.
  `final_root` is a host-searchable `wire_commit_8` (`joint_turn_aggregation.rs:1156`). **Fix is
  clean and NOT AIR:** the wide root already exists in the PIs; widen `finality_signing_message` +
  `FinalityCert.finalized_root` + the seam to all 8 lanes. Kind E → rotation epoch.
- **#3 cap-uniqueness — DOWNGRADE to defense-in-depth.** State commitment already binds the wide cap
  root independently (`commitment.rs:243`); the narrow gate is a redundant projection. Fix is
  actually-hard (declared-root writers widen in lockstep; slot is committed state → circuit binding),
  NOT the quick swap I first ranked.
- **#4 note/nullifier — MINT BLOCKED, availability real via shielded path.** Deployed node injects no
  `proof_verifier` ⇒ cleartext `NoteSpend` fail-closes (`apply.rs:1195`); every real verifier's base
  `verify()` is hardcoded `false`. Availability break is reachable via the *shielded-transfer* path
  (`apply.rs:1370`, self-contained `verify_stark_side`, ~31-bit keys) — ties #4↔#10. Residual: the
  Lean-authoritative producer's note-effect semantics (`exec-lean` `wire_state_to_ledger`) not fully
  traced; all evidence says no value created.
- **#8 topic mask — RECLASSIFY to low-severity design limitation.** Inherent 64-bucket `u64` lattice;
  collisions cause spurious wakes (no payload/cap leak; recipient still filters on the true hash).
  Real per-topic attenuation = a change to the Lean-authored firmament `NotifyCap` model.
- **#14 leg_is_wide — FIXED + VERIFIED GREEN.** Deleted the `#[cfg(not(feature = "prover"))] → false`
  stub; extracted the classifier to an unconditional module-level `vk_hash_is_wide(&[u8;32])` (deps —
  ungated `WIDE_REGISTRY_STAGED_TSV` const + non-optional `blake3` — confirmed available without
  `prover`). Non-prover **lib compiles**; canary `wide_leg_classifier_works_without_prover` **passes**.
  Now one unconditional code path, so the light-client verify build classifies wide legs correctly and
  binds their ~124-bit anchors instead of a slot-0 residual.

## Follow-ups opened 2026-07-19

- **Restore non-prover (light-client) test coverage → `project-ci-meaningfulness-audit`.** `cargo test
  -p dregg-sdk --no-default-features` did not compile on HEAD: ungated tests reference `prover`/
  `exec-lean`-only symbols (`descriptor_authority_class` — fixed one instance; `dregg_exec_lean` import
  — still open; likely more). So the wasm/light-client verify config's tests have not been running —
  **which is exactly where #14's bug survived.** Restore it: gate the remaining ungated tests, then
  wire `--no-default-features` into CI so the trust-minimized config is actually exercised.
- **Kind-E rotation epoch designed** → `docs/DESIGN-felt-width-rotation-epoch-2026-07-19.md` (E1 pure-
  Rust #1; E2 descriptor-PI-widening #2/#9/#11, Lean AIR).

---

## Triage — worst first

| # | Site | file:line | Cost | Kind | Prov |
|---|------|-----------|------|------|------|
| 1 | BFT finality cert — signed message is 4 bytes of lane-0 | `lightclient/src/lib.rs:281` | ~2^31 cheap + 1 proof (see note) | E | **[V]** signature narrow; compensating "segment tooth" is a launder (binds aggregate to itself, not the sig to the wide root) |
| 2 | Federation membership gate — bare 1-felt PI compare, public SDK export | `sdk/src/verify.rs:202,214` | ~2^31 | E | [A][?] |
| 3 | Executor cap-uniqueness gate — narrow root, wide twin exists 19 lines away | `turn/src/executor/execute_tree.rs:328` | ~2^15.5 | B | **[V]** breaks root-binding (1), NOT the structural dup-scan (2, `:345`) — **PROOF-HALF LANDED 07-22** (`CapUniquenessWidth.lean`; redundant-projection DOWNGRADE proved; leg-(1) gate widening = gated deploy) |
| 4 | Note commitment + nullifier — 1 felt each, no `_8` variant | `cell/src/note.rs:329,243` | ~46k spends | C | [A] availability **certain**; mint contingent on deployed verifier [?] |
| 5 | Accumulator leaf **keys** (nf/cm/revoked) — 31-bit addresses | `circuit/src/effect_vm/trace_rotated.rs:1377,1575,1661` | ~2^31 | D | [A] roots are `Faithful8`, membership answered by key |
| 6 | CI pass gate — `exit_code % BABYBEAR_P` aliases failure→0 | `dregg-doc/src/ci_assurance.rs:255` | **zero** | A | **[V]** `2013265921 % p = 0`, gate is `COL_EXIT==0`, bond path unguarded |
| 7 | Fiat mint gate — payment identity folded to 1 felt | `circuit/src/dsl/deco_payment.rs:107` | ~2^16 | C | [A] bridge gate live (`bridge/src/stripe_deco.rs:287`); fold arm fail-closed |
| 8 | Topic wake mask — `1u64 << (topic_hash[0] % 64)` | `starbridge-v2/src/swarm.rs:111` | **~64 evals** | ? | [A][?] load-bearing vs optimization unconfirmed |
| 9 | `SenderAuthorized` authorized-set root — 1 felt, leaf proves no path | `turn/src/executor/membership_verifier.rs:105` | ~2^31 | D/E | [A] |
| 10 | Shielded pool — `merkle_root`/`nullifier`/`value_binding` declared **`u32`** | `turn/src/action.rs:1005`; `circuit-prove/src/shielded/spend_circuit.rs:462` | direct inflation on value collision | C | [A] `Effect::ShieldedTransfer` live |
| 11 | Freshness/revocation root — 1 felt, tree depth 4 ≤14 entries | `sdk/src/full_turn_proof.rs:5248` | grind padding leaves | D/E | [A] |
| 12 | `interface_id` — ~~1 felt, no wide twin~~ **Rust-widened to 8-felt at HEAD**; a factory VK is derived from it | `cell/src/interface.rs:275`; `directory/src/service_factory.rs:92` | ~2^31 → colliding interfaces share a VK | C | [V] **BYTE-SAFE PROVEN 07-22** (`InterfaceIdWidth.lean`; wound "no wide twin" was STALE) |
| 13 | sandstorm-bridge — narrow throughout; byte-identity claim now **false** | `sandstorm-bridge/.../cell.rs:87,138` | ~2^31 (hostile host) | C/drift | [A] `cell/src/state.rs:535` widened, sandstorm did not — correctness drift too |
| 14 | `leg_is_wide` cfg trap — non-prover build forces **every** leg narrow | `sdk/src/full_turn_proof.rs:5144` | verifies ~124-bit anchors at 31 bits | A | [A] wasm verifier is exactly this config; live trap, no current caller |
| 18 | zkOracle `content_commitment` — the **cross-leg weld** is ONE `BabyBear`, then zero-padded to 32 bytes and bound into a receipt | `zkoracle-prove/src/attestation.rs:47,89`; `dungeon-on-dregg/src/narrator.rs:417-418,1064` | ~2^15.5 birthday / ~2^31 targeted | C | **[V]** `BabyBear(pub u32)`; `field_from_u64` puts it in the LAST 8 bytes of a `[u8;32]` ⇒ **looks** ~256-bit on the wire, carries ≤31 bits |
| 19 | `RenderAttestation` — `output_commit` (the verify-gate weld) and `template_commit` (the "generated by THIS template" gate) are both single felts | `zkoracle-prove/src/render.rs:166,198,201` | ~2^15.5 birthday / ~2^31 targeted | C | **[V]** `verify_render_attestation:295` gates on `output_commit`; `verify_render_reproducible:314` gates on `template_commit` |
| 20 | Spend delegation-ancestor key — the public, fixed, system-wide "undelegated" sentinel is ONE felt in the grow-only revoked set's key domain | `circuit/src/effect_vm/trace_rotated.rs:1402,1415` | ~2^31 **offline** grind ⇒ permanent DoS on every undelegated `NoteSpend` | D | **[V]** availability HIGH / soundness NONE — same-fold-keyed `.absent` can only over-revoke; `MapOp.key : EmittedExpr` is one felt in the deployed IR ⇒ widening is VK-affecting. **The tree's one EARNED `check-no-degraded-felt` suppression** |

**Tier 2 (~62-bit, 4 felts):** `circuit-prove/src/dsl_leaf_adapter.rs:152` (`DFA_RC_LEN=4`, leaf exposes 8
on the wire — cheapest real fix), `sovereign_leaf_adapter.rs:85` (`KEY_COMMIT_LEN=4`, authorizes a
sovereign turn, six lines from `COMMIT_LEN=8`), `verifier/src/lib.rs:466` (receipt chain).

**Checked-benign (coverage, not omission):** `storage/src/bucket_commitment.rs:112`,
`starbridge-apps/site-host/src/site.rs:174` (1-felt root is one input to a `wire_commit_8` fold that
binds all limbs — no 31-bit intermediate); `circuit/src/effect_vm/trace.rs:673` anchor tags (all 8
bound via `compute_effects_hash`); `commit/src/typed.rs:565` (30 bits/limb ⇒ 240-bit). Display
strings / hash-map keys / `#[cfg(test)]` fixtures not itemized.

---

## The six repair kinds (kind decides the mechanism and who can touch it)

- **A — Logic bugs, not width. Fix now, no crypto.** #6 (range-check `exit_code`), #14 (cfg gate).
- **B — Gate swap to existing wide twin, AND retire the narrow twin** so it can't be reached again.
  #3.
- **C — No wide scheme exists; must BUILD it — and these are circuit commitments ⇒ authored in
  Lean, Rust calls in.** ⚠️ TRIPWIRE (`~/.claude/CLAUDE.md` law #1). #4, #7, #10, #12, #13, #18, #19.
  Substrate partly exists (`CommitmentTreeAccumulator`, `DeployedHeapTree`/`Heap8Scheme` are
  Lean+wide); the work is authoring the wide note/nullifier/interface/attestation schemes there and
  routing deployed narrow paths through them. **NEVER hand-write the wide commitment in Rust.**
  And for every one of these: the wide scheme must fold the **REAL PREIMAGES** 8-felt end-to-end —
  re-hashing the existing narrow felt is `finalSqueezeOnly_still_conflates`, proved to still conflate.
- **D — 31-bit KEYS inside accumulators; widening the root did nothing.** The sorted-tree membership
  descriptor's key width — also Lean-authored AIR. #5, #9, #11, #20. The IR-level statement of the
  whole kind (found while pricing #20): `DescriptorIR2.lean:301-313` gives a `MapOp` 8-felt `root` /
  `newRoot` groups but a **scalar `key : EmittedExpr`**. That one type line is why every D site is
  un-widenable producer-side and why they must all ride ONE VK epoch. Price the D sites BOTH
  directions before calling them theft vectors: a same-fold-keyed `.absent` op can only over-include
  (availability), while a `.present`/membership-authorizes op is the soundness shape.
- **E — Narrow signed / PI payloads; wire + Fiat-Shamir changes ⇒ batch into ONE rotation epoch.**
  #1, #2, #9, #11. Cheap now (nothing deployed), only gets more expensive.
- **F — Generalize the two defenses (the meta-repair; without it we play whack-a-mole).**
  (i) lint the whole tree for `felt_to_bytes32` / `.as_u32()` / `[0]` / `as u32` at security
  boundaries; (ii) extend the `Faithful8` type wall to **keys, PI vectors, signed payloads** so
  narrow-at-a-boundary becomes *un-representable*, not merely linted.

---

## Notes / open severity questions (verify before pricing)

- **#1 exact cost:** depends on whether an attacker can mint alternate valid aggregates for a chosen
  final state cheaply (own a cell, drive turns ⇒ ~2^31 cheap root computations + 1 proof) vs. must
  prove each candidate (~2^31 proofs). Signature is narrow either way ⇒ fix = widen
  `finality_signing_message`. Trace `verify_turn_chain_recursive` / `genuine_table_public_inputs`.
- **#4 mint leg:** the legacy AIR's Merkle path chains from the 1-felt commitment
  (`circuit/src/note_spending_witness.rs:538`); whether the mint is reachable depends on which
  `ProofVerifier` `turn/src/executor/apply.rs:1221` is configured with (trait object, PI buffer
  "advisory"). Availability break is unconditional regardless.
- **#2 threat model:** attacker builds their own ring and chooses siblings ⇒ controls the preimage,
  same as the action-binding 15 lines below (`sdk/src/verify.rs:218`) which correctly uses 8 felts.

## Meta-lesson (for memory)

The campaign widened **roots**, not **keys/payloads**; the lint covers **three files**; the class
lives in the **complement of both defenses**. A doc-comment asserting collision-resistance is a
*name*, not a proof — read the width, not the comment. Same discipline that surfaced the FRI floor:
check whether the deployed value equals what the proof/scheme actually binds.
