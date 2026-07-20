# PLAN — shielded pool (#10) apex redesign, "Option A"

**Scoping doc. 2026-07-20. Read-only pass; no code changed.** Implements the decision in
`docs/DECISION-shielded-redesign-2026-07-20.md` (ember: **B now + A redesign**): route the deployed
single shielded-transfer path through the existing ring-clearing apex so it closes all three seams —
#15 (wire-supplied `merkle_root`), #16 (test-only value-link), #17 (Shor-broken Ristretto gate) — on a
PQ Poseidon2 gate, and retires the Rust-authored `spend_circuit` AIR (house law #1).

This plan cites file:line at HEAD. Where it says "the apex," it means the machinery in
`circuit-prove/src/shielded_ring_clearing_nleg_air.rs` and `…_air.rs` (2-leg endpoint) plus
`circuit-prove/src/shielded_spend_leaf_adapter.rs`.

---

## 0. Ground truth — what runs today vs. what we route to

**What the deployed path does NOT do (the surprise to internalize first):** the deployed transfer path
`apply_shielded_transfer` (`turn/src/executor/apply.rs:1315`) does **not** touch the ring-clearing apex
at all. It calls `ShieldedTransfer::verify_stark_side()` (`apply.rs:1347`; impl
`circuit-prove/src/shielded/transfer.rs:146-170`), which verifies each input's **standalone hiding
uni-STARK** (`verify_dsl_zk` against `shielded_spend_circuit()`) against a `merkle_root` that came
straight off the wire, then runs the Ristretto conservation gate (`apply.rs:1357`). The ring apex, both
the N-leg (`shielded_ring_clearing_nleg_air.rs`) and the 2-leg endpoint-wide
(`shielded_ring_clearing_air.rs`), exists in `circuit-prove` and is exercised only by its own tests. It
is **not wired into the deployed path, not emitted to `circuit/descriptors/`, and not in
`PROVENANCE.json`** (grep confirms: no shielded row in the sha256 map, no shielded `*.json` on disk).

So "route through the apex" is a genuine subsystem rewrite of `apply_shielded_transfer`, not a config
flip.

**Two apex mechanisms exist; A needs BOTH welded into one descriptor:**

- **(M-conserve) the ring-clearing AIR** (`shielded_ring_clearing_nleg_air.rs:330`
  `shielded_ring_clear_descriptor(n)`) enforces **in-AIR**: the value-binding recompute + connect to the
  spend leaf under Poseidon2 CR (`:436-451`), Σ conservation over `pedTwoGen (v,r)` (`:384-395`), and the
  bit-decomposition range gadget (`:397-408`). This is what closes #16/#17 — conservation and value↔leaf
  binding become circuit constraints on Poseidon2, not off-AIR Ristretto.
- **(M-root) the merkle_root-into-committed-kernel commitment**, realized in the 2-leg **endpoint-wide**
  descriptor (`shielded_ring_clearing_air.rs:449`, name `"shielded-ring-clear-2-endpoint-wide"` `:823`):
  each leg's `merkle_root` column is a limb of the 178-limb pre/post kernel block
  (`common_limb_cols` slots 17/18, `:723-724`) that is absorbed into the eight-lane `wireCommitR8`
  pre/post commitments (`:762-773`) and PI-pinned (`:798-808`). That is what pins `merkle_root` to a
  **committed turn root** and closes #15. The deployed-shape consumer already exists:
  `prove_shielded_spend_root_binding_node_segmented` (`shielded_spend_leaf_adapter.rs:594`), whose
  docstring names itself the "ready consumer" of the `Effect::ShieldedTransfer` VK-regen piece
  (`:588-591`), connecting the leg's nullifier + commitments-root lanes to the turn root (`:649-651`).

**Honest naming caveat (do not launder):** a single shielded transfer is *not* a ring/swap. The N-leg
apex encodes matcher semantics a transfer does not have — `Layout::new` **asserts `n >= 2`** (`:165`),
and the ring gates (fusion `offer==note` `:346-356`, cyclic edge `want_asset[i]==offer_asset[(i+1)%n]`
`:358-365`, partial-fill `want_min ≤ offer` `:410-427`) presuppose a cycle of counterparties. So "a
degenerate 1-leg ring" is a slight abuse: what we actually build is a **degenerate single-transfer
clearing descriptor** that keeps the apex's conservation/range/value-binding-connect machinery
(M-conserve) and the endpoint kernel-commitment machinery (M-root) but **drops the ring/fusion/
partial-fill matcher gates** and generalizes the per-leg (1-in/1-out) shape to the transfer's M-in/K-out
Σ conservation. The plan below says exactly which gates stay and which go.

---

## 1. The routing: how `apply_shielded_transfer` goes through the apex

**Target shape.** A shielded transfer with M inputs and K outputs becomes: (a) M shielded-spend
leaves, one per input, each `prove_shielded_spend_leaf_with_claim` exposing `[nullifier, merkle_root,
value_binding]` (`shielded_spend_leaf_adapter.rs:469`); (b) one **transfer-clearing leaf** proving the
degenerate descriptor (below); (c) an apex fold binding each input's claim tuple to its spend leaf by
in-circuit `connect`, and binding the shared `merkle_root` lane to the turn's committed commitments-root.

**The degenerate descriptor** (new; authored in Lean — see §5). Take
`shielded_ring_clear_descriptor(n)` (`nleg_air.rs:330`) as the template and:

- **KEEP** — value-binding recompute per input (`:436-451`), Σ conservation value coordinate
  (`:386-389`), the range gadget on every input `value` and every output `out_val` (`:397-408`), the
  in-ring pairwise-distinct-nullifier gate over the M inputs (`:367-382`), and the `[nf,root,vb]`
  PiBinding per input (`:453-465`).
- **DROP** — fusion gates (`offer_asset==asset`, `offer_amount==value`, `:346-356`), cyclic ring edges
  (`:358-365`), partial-fill compare (`:410-427`), and the `want_*`/`offer_*` matcher columns
  (`lc::OFFER_ASSET…WANT_MIN`, `:139-143`). A plain transfer has no matcher.
- **GENERALIZE** — from N legs of (1 input note ⇒ 1 output note) to **M input `value[i]` and K output
  `out_val[j]`** with `Σᵢ value[i] == Σⱼ out_val[j]` (single value coordinate; multi-asset stays M2-b).
  Relax the `n >= 2` assertion (`:165`) to `M ≥ 1, K ≥ 1`. Re-derive the no-wrap bound
  `(M+K)·2^VALUE_BITS ≤ p` (cf. `ring_no_wrap_ok` `:245`).
- **ADD the endpoint kernel commitment** — carry each input's `merkle_root` (and the nullifiers) as
  limbs of the pre/post kernel block absorbed into the `wireCommitR8` commitment, exactly as the 2-leg
  endpoint descriptor does (`…_air.rs:709-773`). That is the M-root weld (§2).

**What `apply_shielded_transfer` becomes** (`apply.rs:1315-1412`):

- `from_serialized_parts(payload.merkle_root, …)` (`apply.rs:1331`) — the `merkle_root` argument is
  **removed** as an authoritative input (§2). The executor supplies the *committed* accumulator root; the
  wire `merkle_root` is retired.
- `transfer.verify_stark_side()` (`apply.rs:1347`) — **replaced** by a single apex verification:
  reconstruct the M spend leaves + the transfer-clearing leaf from the wire proof, fold them
  (`prove_shielded_ring_clearing_apex`-analog, `nleg_air.rs:824`), and verify the folded apex proof binds
  to (i) the committed commitments-root and (ii) the fresh-nullifier set. Membership + nullifier
  derivation + value-binding + conservation + range are now **one** proof.
- `check_range_proof_shape()` (`apply.rs:1351`) and GATE 2 `verify_full_conservation_bytes`
  (`apply.rs:1357`) — **removed** (conservation + range are now in-AIR; §§3–4). GATE 2's Ristretto call
  is the #17 wound; it goes.
- GATE 3 nullifier-set inserts (`apply.rs:1370-1409`) — **stays**, unchanged. It is the only committed
  kernel mutation and is already proved sound in Lean (`Dregg2/Circuit/ShieldedTransferStark.lean` part
  (A): `ShieldedTransfer` on the kernel = iterated `noteSpendNullifier`). The `value 0` placeholder
  (`apply.rs:1396`) stays — the shielded amount lives in the commitment, never in `bal`.

**What stays on the wire** (`turn/src/action.rs:1003-1020`): `inputs` (per-input nullifier +
value_binding + proof, `:983-990`), `input_legs`/`output_legs`, and enough to reconstruct the apex. What
**leaves** the wire: `merkle_root: u32` (`:1005`, §2), `output_range_proofs` (`:1012`, now in-AIR), and
`conservation: ConservationProof` (`:1019`, now in-AIR) — unless we keep the Ristretto legs as a
non-TCB compatibility residual (§4 decision point).

---

## 2. `merkle_root` pin — closing #15

**The wound** (#15, the worst): today the executor rebuilds membership against the wire-supplied root —
`ShieldedTransfer::from_serialized_parts(payload.merkle_root, …)` sets `merkle_root: BabyBear::new(payload.merkle_root)` (`transfer.rs:284`), and every input's proof is checked against *that* root
(`transfer.rs:152-159`, pi index `pi::MERKLE_ROOT`). A malicious prover supplies a root of a tree they
built and proves membership in it — spend a note that was never created.

**The fix — pin to the committed accumulator.** The apex already exposes `merkle_root` as a claim lane
(`nleg_air.rs:455`, `PiBinding` slot 1) and the endpoint descriptor already absorbs it into the
committed kernel commitment (`…_air.rs:723-724` → `wireCommitR8` `:762-773`). The routing must
`connect` that lane to the turn's **already-committed commitments-root**, not to a free wire felt. The
mechanism is built: `prove_shielded_spend_root_binding_node_segmented` (`shielded_spend_leaf_adapter.rs:594`)
`connect`s the leg's `merkle_root` lane (root-bound lane index 1, `:649-651`) to the segment leaf's
commitments-root. Concretely:

- **Which committed root:** the shielded commitment tree's root as carried in the turn's committed
  commitments-root (the same accumulator `NoteSpend`/the effect-VM commit path pins). The redesign must
  route the shielded note tree into that committed accumulator (today the shielded nullifier set
  pollutes `note_nullifiers.root8()` as a Stage-B placeholder, `apply.rs:1386-1395`; the committed
  shielded-commitment accumulator is the Stage-B/D wiring this plan finally does).
- **How it's exposed:** as a PI on the transfer-clearing descriptor that the executor fills from the
  *ledger's* committed root — never from `payload`.
- **How the wire field is retired:** delete `ShieldedTransferPayload::merkle_root: u32` (`action.rs:1005`)
  and the `from_serialized_parts(merkle_root, …)` parameter (`transfer.rs:264-290`). A prover-chosen root
  becomes unrepresentable: there is no wire slot for it, and the in-AIR `connect` forces the membership
  root to equal the committed accumulator or the fold is UNSAT.

Net: #15 moves from "trusted wire felt" to "in-AIR equality against the committed turn root."

---

## 3. Value-link fold — closing #16

**The wound** (#16): `verify_value_link` (`cell-crypto/src/value_commitment.rs:1659`) — which checks that
the STARK leaf value equals the Pedersen-leg value — runs **only in tests**
(`circuit-prove/tests/shielded_transfer_m2a.rs:475,495,509`), never in `apply_shielded_transfer` (it
needs the secret opening, so it *cannot* run there as written). Deployed conservation
(`verify_full_conservation_bytes`, GATE 2) proves only that the *Ristretto legs* balance — a prover can
decouple the STARK-witnessed leaf values from the legs and mint.

**The fix — the apex makes the link a load-bearing in-AIR gate, no opening required.** The apex
RE-COMPUTES `value_binding[i] = hash_fact(value[i], [asset[i], randomness[i], 0])` from the same witness
cells and `connect`s it to the spend leaf's exposed `value_binding` lane under Poseidon2 CR
(`nleg_air.rs:436-451`; leaf side `spend_circuit.rs` C7a `:278-281`, PI pin C7b `:310-314`). Then it
enforces `Σ value[i] == Σ out_val[j]` **over those same in-AIR `value` cells** (`nleg_air.rs:386-389`).
So the value that conserves is *provably* the value bound into the spent note's leaf — there is no
second, free "Pedersen value" to decouple. This is the exact `RealCrypto.ring_conserves_pedersen_list`
hypothesis→conclusion the Lean already carries (`Dregg2/Shielded/RealCrypto.lean` §1;
`ValueBindingCommit.binds_value_and_asset`).

Consequences:
- `verify_value_link` (`value_commitment.rs:1659`) and its test-only invocations are **retired** — the
  property it checked out-of-band is now a circuit constraint. The Ristretto GATE 2
  (`verify_full_conservation_bytes`, `apply.rs:1357`) is **removed** (§4).
- The `value_binding` lane graduates from "ATTESTED off-AIR Pedersen link" (its documented grade,
  `shielded_spend_leaf_adapter.rs:73-76,581-586`) to the **authoritative** no-mint anchor.

---

## 4. #17 PQ cut — Poseidon2 `value_binding` authoritative

**The wound** (#17): the code/docs declare Poseidon2 `value_binding` authoritative and Ristretto
"retired" (`spend_circuit.rs:38-48,124-133`, `value_commitment.rs:1648-1658`), but the **only no-mint
gate that actually runs** on the deployed path is the Ristretto DLog aggregate (GATE 2), which is
Shor-broken. The comments materially overstate the posture. (Move B corrects the comments *now*; A makes
the code match the comments.)

**The cut.** After §3, the authoritative no-mint gate is the in-AIR Poseidon2 chain: value-binding
recompute (`nleg_air.rs:436-451`) + Σ conservation (`:384-395`) + range gadget (`:397-408`), all resting
on `HashCR` (Poseidon2 collision-resistance) — the *same* floor Merkle membership and nullifiers already
stand on, and quantum-safe. The Ristretto legs are no longer in the no-mint TCB.

**Drop or keep the Ristretto legs — decision point.** Two options:

- **(4a) Drop entirely.** Remove `output_range_proofs` (`action.rs:1012`), `conservation`
  (`action.rs:1019`), input/output `legs`, `verify_full_conservation_bytes`, and the whole
  `commit_hidden_asset`/Bulletproof surface from the deployed path. Cleanest; smallest TCB; matches the
  "PQ cutover" claim exactly. Cost: loses the >2^VALUE_BITS amount range that the off-AIR Bulletproof
  currently covers (see §6 residual — this is the price of honesty until the in-AIR Bulletproof lands).
- **(4b) Keep as a non-TCB belt-and-suspenders.** Retain the Ristretto legs + Bulletproof range as a
  *redundant, explicitly-non-authoritative* check (as `verify_value_link`'s check (2) already frames
  itself, `value_commitment.rs:1672-1678`), so large amounts keep a range gate while the in-AIR range is
  capped at 2^VALUE_BITS. Cost: the Shor-broken curve stays linked; must be documented as
  non-load-bearing so no one re-reads it as the guarantee.

**Recommendation: 4b for the A landing, 4a once the in-AIR Bulletproof (residual §6) lands.** Keeping the
legs as a *named non-TCB* range crutch avoids regressing the large-amount range the day A ships, while
the value-binding + conservation move firmly to Poseidon2. The comments must state, unambiguously, that
the legs are not in the no-mint TCB.

**What the light client sees.** Today: nothing — shielded is `#[cfg(feature="prover")]`, fail-closed on
verify-only (`apply.rs:1417-1431`), and not in the committed VK
(`docs/DECISION-shielded-redesign-2026-07-20.md` §Stakes). **After A:** the transfer-clearing apex folds
into the committed turn (it publishes pre/post kernel commitments, `…_air.rs:762-808`, that fold into
`aggregate_tree` like any segment leaf), so a pure light client that checks the turn VK now witnesses
membership + nullifier + value-binding + conservation + range on Poseidon2 — the membership-into-committed
root and the no-mint gate become **light-client-visible**, where today they are node-operator-trust only.
This is the real prize of A: it moves shielded from a prover-trust surface into the committed VK.

---

## 5. The VK change + Lean-port target (house law #1)

**Is this Lean-authored AIR?** Partly, and this is the load-bearing house-law-1 item. Today:

- The **spend circuit** `shielded_spend_descriptor()` (`spend_circuit.rs:192`, C1–C7b as `ConstraintExpr`
  data `:199-315`) is **Rust-authored** — house-law-1 DEBT, exactly as the decision doc flags. The leaf
  adapter *lowers* it (`shielded_spend_leaf_adapter.rs:254`, walking the source), but the source AIR is
  hand-written in Rust.
- The **ring descriptors** (`shielded_ring_clearing_nleg_air.rs:330`, `…_air.rs:449`) are also
  **Rust-authored** — the constraints are built as `VmConstraint2`/`LeanExpr` data in Rust.
- There **is** a Lean twin for the 2-leg endpoint: `Market/ShieldedRingEndpointDescriptor.lean:498`
  `shieldedRingEndpointDescriptor`, name-matched (`:570`) and `#guard`-checked at traceWidth 1537
  (`:568`) / piCount 27 (`:569`). But it is **not in the emit/PROVENANCE pipeline** — no shielded `*.json`
  is emitted, no `PROVENANCE.json` row. So even the Lean twin is not the ground-truth emitted object the
  Rust consumes; the Rust descriptor is authoritative, and the Lean is a parallel author.

  ⚠ **Drift check the redesign must resolve:** the Lean twin `#guard`s traceWidth **1537**
  (`ShieldedRingEndpointDescriptor.lean:568`) while the Rust `FINAL_TRACE_WIDTH`
  (`shielded_ring_clearing_air.rs:305`) is computed from the endpoint layout — confirm these agree
  (an emit-equality gate would catch this; none exists today).

**The Lean-port target.** House law #1 (AIR is authored in Lean; Rust only calls the emit path) requires
the transfer-clearing descriptor to be **emitted from Lean**, not built as Rust `VmConstraint2`. Name the
targets:

- **`metatheory/Market/ShieldedSpendDescriptor.lean`** (NEW) — Lean-author the shielded-**spend** AIR
  (the C1–C7b currently in `spend_circuit.rs`), emitting an `EffectVmDescriptor2`/`CircuitDescriptor`
  the Rust `shielded_spend_to_descriptor2()` consumes instead of the hand-written
  `shielded_spend_descriptor()`. This retires the marquee house-law-1 debt for the spend leaf.
- **`metatheory/Market/ShieldedTransferClearDescriptor.lean`** (NEW, or extend
  `ShieldedRingEndpointDescriptor.lean`) — Lean-author the **degenerate transfer-clearing** descriptor
  of §1 (conservation + range + value-binding-connect + endpoint kernel commitment, no ring gates),
  emitting the object the routing folds.
- Wire both into the emit pipeline (`Dregg2/Circuit/Emit/*`, cf. `PROVENANCE.json` emitters list) so
  they land in `circuit/descriptors/*.json` with a sha256 row — the same provenance every other deployed
  descriptor carries. The refinement obligations already exist to hang the new descriptor on:
  `Dregg2/Shielded/ClaimRefinement.lean` (`shielded_spend_claim_refines`, membership+nullifier PROVED),
  `Dregg2/Circuit/ShieldedTransferStark.lean` (kernel part PROVED, STARK residual named to the FRI/AIR
  floor), `Dregg2/Shielded/RealCrypto.lean` (§PQ CUTOVER: value-binding HashCR floor).

**The VK flip — who must move.** New descriptors ⇒ new `vk_hash`es. But note the *starting* state:
shielded has **no committed descriptor VK today** (it verifies via standalone `verify_dsl_zk`, and is not
in the emit registry). So:

- This is **additive** to the descriptor registry: a new `dregg-shielded-spend-*` and
  `dregg-shielded-transfer-clear-*` JSON + `PROVENANCE.json` sha256 rows + VK. It is **not** a rotation
  of an existing deployed descriptor's VK.
- **However**, routing the apex into the committed turn (§4) means the shielded segment now folds into
  `aggregate_tree`. **Confirm whether the turn's aggregate VK is descriptor-agnostic** (segment leaves of
  any descriptor fold uniformly) or descriptor-enumerated. If descriptor-agnostic, the light client's
  committed *turn* VK is unchanged and only the new leaf VK is added (clean, additive). If the aggregate
  VK enumerates admissible descriptors, then admitting the shielded segment **changes the committed turn
  VK** → this becomes a **coordinated rotation-epoch change**: light client, node, and the descriptor
  registry (`circuit/descriptors/`, the `rotation-*-staged-registry.tsv` files) all flip together at an
  epoch boundary. **This is the single most important unknown to resolve before building** — it
  determines whether A is additive or a coordinated flag-day.

Who flips, in the rotation-epoch case: (1) the **descriptor registry** (`PROVENANCE.json` + rotation
TSVs) gains the shielded rows; (2) the **node** builds/verifies the new apex; (3) the **light client**
accepts the new turn VK at the epoch. Coordinate exactly as any VK rotation.

---

## 6. The two named residuals — the post-A frontier

Both are already named honestly in `shielded_ring_clearing_nleg_air.rs:85-91`. A closes the seams but
leaves these; do not let A's landing read as "shielded done."

- **`pedTwoGen` ≠ real Ristretto** (`nleg_air.rs:85-88`). Conservation runs over the two-**coordinate**
  abstraction `pedTwoGen (v, r)`, not the real group point `v·G + r·H`. The value-mint hazard is closed
  in-AIR by the range gadget (d), so this is a **faithfulness** gap, not a mint hole — but the in-AIR
  conservation is over an abstraction of the curve, not the curve. **What it needs:** full EC-in-circuit
  arithmetic (the real curve-point excess in-AIR), or a decision to make the Poseidon2 commitment the
  *sole* value commitment and drop the Pedersen coordinate model entirely (which §4a already points at).
  Scope: research; the EC-in-AIR build.
- **BabyBear large-amount range cap ~2^30/N** (`nleg_air.rs:89-91`, `VALUE_BITS=27` `:130`). One BabyBear
  field caps a conserving sum near `2^30/N`; amounts above `2^VALUE_BITS` still lean on the off-AIR
  Bulletproof (the reason §4 recommends keeping the legs as a non-TCB crutch initially). **What it needs:**
  an **in-AIR Bulletproof** (or a multi-limb in-AIR range) to lift the full 64-bit amount range into the
  circuit, at which point §4a (drop the legs) becomes safe. Scope: research; the in-AIR range build.

These two are the honest next frontier *after* A lands, per the decision doc's own framing.

---

## 7. Staging — additive-then-cutover, not a flag-day

**Recommendation: staged-additive, then cutover.** The safest sequence, given greenfield (nothing
deployed) and the fail-closed verify-only path:

1. **Lean-author + emit the two new descriptors** (§5): `ShieldedSpendDescriptor.lean` and the
   transfer-clearing descriptor, wired into the emit pipeline with `PROVENANCE.json` rows. Land them
   **beside** the existing Rust descriptors first, with an **emit-equality gate** (Rust descriptor ==
   Lean-emitted, byte/structural) — this both discharges house law #1 and catches the traceWidth-1537
   drift flagged in §5. No behavior change yet.
2. **Build the apex routing in `circuit-prove`** as a new function (`apply`-callable) that reconstructs
   the M spend leaves + transfer-clearing leaf, folds, and verifies against a *supplied* committed root —
   with both-polarity teeth (honest transfer verifies; wire-chosen root / decoupled value / non-member /
   double-spend all UNSAT). This mirrors the existing apex teeth (`nleg_air.rs:1002-1128`). No `apply`
   change yet.
3. **Cut over `apply_shielded_transfer`** (`apply.rs:1315`) in one commit: replace `verify_stark_side` +
   GATE 2 with the apex verification (§1), retire the wire `merkle_root` (§2), keep GATE 3. Because
   shielded is greenfield and fail-closed off the prover path, there is no migration window to preserve —
   this is a straight replacement, not a byte-identical cutover. (Per the no-greenfield-migration-theater
   feedback: make the right proven-Lean object BE the object; delete the debt.)
4. **Resolve the VK-flip question (§5) before step 3 ships.** If additive, land step 3 directly. If it
   changes the committed turn VK, sequence step 3 at a **rotation epoch** with the registry + light client.

Do **not** attempt an in-place VK rotation of the current standalone-verify path — there is no committed
shielded VK to rotate; the honest shape is "add the emitted, committed descriptor + delete the
Rust-authored standalone path."

---

## Honest difficulty + risk summary

This is a **genuine subsystem rewrite**, not a wiring change: the deployed path (`verify_stark_side` +
Ristretto conservation) is *entirely replaced* by an apex fold, the AIR must be **re-authored in Lean and
emitted** (retiring the Rust-authored `spend_circuit` and ring descriptors — the marquee house-law-1
debt), and a **committed shielded-commitment accumulator** must be introduced so `merkle_root` has a real
committed root to pin to (today it pins to nothing; the shielded set only pollutes a placeholder). The
single largest risk is the **VK-flip classification (§5)**: whether admitting the shielded segment into
the committed turn changes the aggregate turn VK — that decides additive-vs-coordinated-flag-day and must
be answered from the aggregation code *before* building, or the whole staging plan can invert. Secondary
risks: the "degenerate 1-leg ring" is really a **new M-in/K-out clearing descriptor** (the N-leg apex
asserts `n≥2` and encodes swap semantics a transfer lacks), so it is authored work, not a free
specialization; and a **traceWidth drift** already exists between the Lean twin (1537) and the Rust
endpoint layout with no equality gate to catch it. The redesign genuinely closes #15/#16/#17 on a
quantum-safe Poseidon2 floor and — the real payoff — moves shielded from node-operator-trust into the
**light-client-checked committed VK**; but it lands with **two named, un-closed residuals** (`pedTwoGen`
≠ real Ristretto; ~2^30/N amount cap), so A is a real closure of the theft/mint seams, **not** a
"shielded is finished" claim. Recommend keeping the Ristretto legs as an explicitly-non-TCB large-amount
range crutch until the in-AIR Bulletproof (§6) lands, then dropping the curve stack entirely.
