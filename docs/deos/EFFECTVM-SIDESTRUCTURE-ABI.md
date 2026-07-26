# The EffectVM Side-Structure ABI

*How every one of dregg's side-structures — the shielded pool, the attested-data lane, the
DrEX/Market clearing, the intent/ring solver, the cross-chain holdings — plugs into the core
effect-VM through ONE uniform interface: `{proof, committed-claim, trust-grade, state-delta}`,
verified by grade, bound by an in-circuit `connect`, composed at the weakest leg. Present-tense,
what-is; every "would-be native" names its gap and its grade.*

Grade of this document: **REPLAYABLE** for the census (re-derivable by reading the cited code);
the ABI itself is a design over PROVED machinery (the fold fabric) with named gaps.

---

## 0. The thesis, and the hypothesis it validates

**Hypothesis (from the brief): the leaf-adapter fold fabric IS the proto-ABI.** *Confirmed.*

The `circuit-prove/src/*_leaf_adapter.rs` family plus the carrier fold arms in
`ivc_turn_chain.rs::prove_chain_core_rotated` (`circuit-prove/src/ivc_turn_chain.rs:3112-3520`)
already implement, eight times over, exactly a `{proof, committed-claim, bind}` interface. A
leaf-adapter is a side-structure's proof re-proven as a **recursion-foldable leaf** that
**re-exposes a committed-claim tuple** (`expose_claim`) which a **binding node `connect`s**
in-circuit to the deployed turn's descriptor PIs — a forged claim is UNSAT, so no root is minted.
This document names that latent interface, states the missing fourth field (the trust-grade
dispatch and the state-delta the segment already carries), and gives each side-structure its
conformance path and its soundness obligation.

The eight carriers conforming through the `CarrierWitness` match
(`joint_turn_aggregation.rs:150-505`): `Custom`, `Bridge`, `Deco`, `Sovereign`, `Factory`,
`Hatchery`, `Membership`, `Dsl`. The ABI below is the generalization of their shared shape to
the five census side-structures (§1) — the marquee of which, the shielded pool, conforms
through exactly this shape (its own leaf adapter + binding node, folded by the ring-clearing
AIRs rather than a `CarrierWitness` arm).

---

## 1. The census — 5 side-structures × integration state

| # | Side-structure | Integration state | Committed-claim surface today | Cite |
|---|---|---|---|---|
| 1 | **Shielded pool** (marquee) | **LEAF-ADAPTED** (built) | 3-felt claim `[nullifier, merkle_root, value_binding]` re-exposed by `prove_shielded_spend_leaf_with_claim` + a lane-connecting binding node; the ring-clearing AIRs fold those leaves | `circuit-prove/src/shielded_spend_leaf_adapter.rs:469-490`; `shielded_ring_clearing_air.rs`; `spend_circuit.rs` |
| 2 | **Attested-data lane** | **BESIDE** | `AttestedFact{measurement, payload, report_data, grade}`; NO state-delta, NO leaf; one downstream consumer — `GradedMark::from_tee_attested` composes it into the graded oracle-mark weld | `tee-verify/src/attested_data.rs:161-175`; `tee-verify/src/oracle_mark.rs`; `metatheory/Market/OracleWeld.lean` |
| 3 | **DrEX / Market clearing** | ring = **NATIVE**; Market tower = **NATIVE via ledger-realization** (proven) | ring → native `Effect::Transfer` legs through `recKExec`; the clearing's ledger-realization is proven down to `settleRing`/`recKExec` (full-fill, partial-fill, pool-fill, shielded fusion) | `intent/src/verified_settle.rs:201-350,680`; `metatheory/Market/LedgerRealizationExt.lean:5-27` |
| 4 | **Intent / ring solver** | **BESIDE** (untrusted-search + verified-check) | none — TRUSTED search; output re-verified by the settle path, no proof of its own | `intent/src/solver.rs:51-59`; `lib.rs:10-18`; `verified_settle.rs:214-247` |
| 5 | **Cross-chain holdings** | governance = **BESIDE**; circuit pilot = **LEAF-FOLDED (commitment-only)** | `ProvenForeignHolding{chain,holder,asset,amount,snapshot,consensus_proven}`; leaf folds an 8-felt identity commitment, MPT/keccak OFF-AIR | `dregg-governance/src/proven_foreign_holding.rs:154`; `circuit-prove/src/{custom_proof_bind,mpt_holding_leaf}.rs` |

The through-line: **the marquee (shielded) is leaf-adapted, the DrEX pair is native (ring by
construction, Market clearing by proven ledger-realization), the holdings pilot is leaf-folded — and
the two still-beside structures (attested-data, the solver-as-prover target) each already carry a
claim tuple that maps cleanly onto the ABI's committed-claim field.** What those lack is the *leaf
wrap + expose + connect* the deployed carriers have.

---

## 2. The core the ABI must plug into

### 2.1 The native effects (the descriptor tower)

`Effect` (`circuit/src/effect_vm/effect.rs:75+`) is the closed set of VM-native effects:
`NoOp, Transfer, SetField, GrantCapability, RevokeCapability, EmitEvent, SetPermissions,
SetVerificationKey, RefreshDelegation, Mint, BridgeMint, NoteSpend, Custom, …`. Each has a
Lean-emitted, fingerprint-pinned `EffectVmDescriptor` rendered by `emitVmJson` and ingested by
`lean_descriptor_air::parse_vm_descriptor` (`circuit/src/effect_vm_descriptors.rs:1-7,80-...`).
A native effect is *proved* by its descriptor's AIR: balance moves, cap_root advances, nullifier
freshness (`nullifierFreshUMem`, `effect_vm_descriptors.rs:866`) are all in-circuit constraints.

**The open native seam the ABI generalizes** is already visible in the descriptor ledger:
`Effect::ShieldedTransfer` is a pinned `NamedResidual` — the executor verifies the shielded proof;
binding that verification into the effect_vm descriptor is the VK-affecting weld follow-up
(`circuit/tests/effect_enum_descriptor_residual_gate.rs:112`). `Effect::Custom` shows the closed
shape: its AIR does NOT verify the external proof (`circuit-prove/src/custom_proof_bind.rs:7-13`),
and the deployed recursion fold backs it — the sub-proof leaf is re-proven and its 8-felt PI
commitment recomputed in-circuit and lane-connected (`custom_proof_bind.rs:15-21`). The ABI is the
disciplined way to close residuals like the former without a bespoke circuit each time.

### 2.2 The proved invariants (what the ABI must preserve)

The record kernel's soundness laws, over the `balance` field of a content-addressed `Value`
record (`metatheory/Dregg2/Exec/RecordKernel.lean`):

- **Conservation (Law 1)** — `recKExec_conserves` (`RecordKernel.lean:584-596`): every committed
  turn preserves `recTotal` (Σ balances); its per-asset refinement is
  `maExec_conserves_per_asset` (`RecordKernel.lean:699`) and the receipt-chain lift
  `Exec/Receipt.lean`.
- **No state change without authority (attenuation)** — `recKExec_authorized`
  (`RecordKernel.lean:601-607`): the `authorizedB k.caps turn` gate; composed with
  `attenuate_narrows`/`attenuate_subset` (`Dregg2/Authority/Caveat.lean:162,170`) — a delegated
  key can *only* shrink authority.
- **No-forgery** — the descriptor AIR pins every state advance to a hash recomputed in-circuit
  (`new_cap_root == hash_2_to_1(old, entry)`, `effect.rs:93,124-126`); a prover cannot invent a
  new root.
- **Nullifier no-double-spend** — `nullifierFreshUMem` + the `NOTESPEND_NULLIFIER` PI (198) and
  the committed `nullifier_root` (`note_spend_leaf_adapter.rs:70-71`); the runtime nullifier-set
  grow-gate rejects a reused nullifier.

The receipt chain binds the whole turn: a `WitnessedReceipt` commits
`(old_commit, new_commit, effects_hash, previous_receipt_hash)` and
`chain_tamper_evident` (`Exec/Receipt.lean`) makes history append-only. **Whatever a
side-structure asserts, the composite turn's receipt must still satisfy these four laws.** That
is the invariant-safety burden of §5.

---

## 3. The uniform Side-Structure ABI

### 3.1 The four fields a side-structure exposes

A side-structure `S` contributing to a turn exposes a **claim record**:

```
SideClaim {
  proof            : Proof            // HOW S convinces the VM (see 3.2 — dispatch by grade)
  committed_claim  : [BabyBear; N]    // WHAT S asserts about shared state (the expose_claim tuple)
  trust_grade      : TrustGrade       // PROVED | ATTESTED | REPLAYABLE (DREGGFI-VISION.md §1:26-29)
  state_delta      : Segment          // the state transition S induces (the [first_old8,last_new8,count,acc] anchor pair)
}
```

Grounding, field by field, in the deployed carrier fabric:

- **`committed_claim`** is the `expose_claim` PI table. Every conforming leaf re-exposes a fixed
  tuple read from its own FRI-bound descriptor PIs (not free scalars):
  `prove_descriptor_leaf_with_pi_slice_expose(desc, proof, pis, cfg, pi_lo, len)`
  (`ivc_turn_chain.rs:1280-1339`) exposes `main[pi_lo..pi_lo+len]`. Examples: the note-spend
  leaf's `NOTE_SPEND_CLAIM_LEN=7` tuple `[nullifier, merkle_root, value_lo, asset, dest_fed,
  value_hi, mint_hash]` (`note_spend_leaf_adapter.rs:125-132`); the custom leaf's 8-felt
  `custom_proof_commitment`; the holdings leaf's 8-felt identity commitment.
- **`state_delta`** is the `Segment` — `[first_old8(8), last_new8(8), count(1), acc(8)]`, exactly
  `SEG_WIDTH = NUM_CHAIN_CLAIMS` lanes (`ivc_turn_chain.rs:254-278`). The two 8-felt anchors are
  the ~124-bit faithful state-commit endpoints; `acc` is a real Poseidon2 sponge digest
  (`seg_poseidon_commit`). A side-structure's delta IS its `(old_root → new_root)` step; a leg
  that changes state exposes it here, bound in-circuit to the descriptor's real rotated roots.
- **`trust_grade`** is not a byte on the leaf today — it is *structural*: it is **which check is
  in-circuit** (§3.2). This document's proposal is to make it an explicit associated const so the
  composition rule (§3.4) is checkable, not implicit.
- **`proof`** is a `RecursionOutput<DreggRecursionConfig>` (a foldable leaf) for PROVED, or an
  off-AIR verified result (an `AttestedFact`-shaped claims struct) for ATTESTED, or nothing beyond
  the public inputs for REPLAYABLE.

### 3.2 VERIFY — dispatch by grade

The VM verifies `S` by a **dispatch on `trust_grade`**:

- **PROVED** → *the fold path.* Re-prove `S`'s real statement as an IR-v2 recursion leaf
  (`prove_<S>_leaf_with_claim`), then verify it in-circuit by folding it under the recursive
  verifier — `build_and_prove_aggregation_layer_with_expose` inside the binding node. A leaf that
  does not verify mints no foldable output. The lesson from the bridge carrier is load-bearing:
  the leaf must re-prove the **real** statement, not a binding-only shadow — folding the
  binding-only `bridge_action_air` was **refused** as unsound (a prover-chosen tuple), and the
  sound backing is the re-proven note-spend STARK (`note_spend_leaf_adapter.rs:19-28`).
- **ATTESTED** → *the attestation-check path.* The authenticity crypto stays OFF-AIR,
  executor-verified, as a **named §8 carrier**; only a Poseidon2 *commitment* to the claim is
  recomputed in-AIR and folded. This is the deployed DECO posture: the leaf "verifies only the
  Poseidon2 commitment binding `PaymentFacts → payment_hash`; ed25519/HMAC/SHA-256 stay OFF-AIR"
  (`ivc_turn_chain.rs:3208-3219`; `deco_leaf_adapter.rs:27-34`). The TEE cert-chain check
  (`tee-verify/src/lib.rs:159-260`, `snp.rs:343-368`) is the off-AIR verifier; its output binds
  through the commitment lane.
- **REPLAYABLE** → *the re-derivation path.* A pure function over public data; the VM (or any
  verifier) recomputes it. No leaf needed beyond exposing the inputs; the "proof" is that anyone
  reruns it (e.g. a ranking list, `DREGGFI-VISION.md:29`).

The dispatch is **fail-closed at admission**: `carrier_claim_pins_admitted(desc, pis, PI_LO,
CLAIM_LEN, name, Some((col, row)))` (`ivc_turn_chain.rs:3173-3181` for bridge) refuses a leg whose
deployed descriptor does not genuinely pin the claim teeth at the expected column/row — a
pin-less or wrong-column descriptor is rejected, never silently degraded.

### 3.3 BIND — the in-circuit `connect`, and the invariants the bind must satisfy

Binding is a three-step node, uniform across carriers (bridge shape,
`note_spend_leaf_adapter.rs:768-834`; custom shape, `joint_turn_recursive::prove_custom_binding_node_segmented`):

1. **Dual-expose the leg leaf** — `prove_descriptor_leaf_dual_expose_at(desc, proof, pis, cfg,
   claim_pi_lo, claim_len)` (`ivc_turn_chain.rs:1528-1622`): expose ONE `expose_claim` table
   carrying the **segment** `[0..SEG_WIDTH)` (bound to the descriptor's real rotated roots) ++ the
   leg's **claimed teeth** `[SEG_WIDTH..SEG_WIDTH+claim_len)` (read from the same FRI-bound PIs).
2. **`connect` the teeth to the backing leaf's genuine claim, lane by lane** —
   `for k in 0..claim_len { cb.connect(leg[SEG_WIDTH+k], backing[k]); }`
   (`note_spend_leaf_adapter.rs:817` binds the single mint-hash lane; the 7-lane and n-lane
   variants at `:652,730`). A leg claiming a tuple no verifying sub-proof backs is a `connect`
   conflict ⇒ UNSAT ⇒ no root.
3. **Re-expose ONLY the segment** — `cb.expose_as_public_output(&seg)` — so the bound node folds
   into `aggregate_tree` like any per-turn segment leaf, and the tree combine
   (`segment_combine_expose`, `ivc_turn_chain.rs:3610-3645`) telescopes state continuity
   (`L.last_new8 == R.first_old8`), count additivity, and the ordered digest.

**The bind must satisfy the VM's invariants (the load-bearing constraint):**

- *Conservation.* The segment anchors the leg to the descriptor's real `(old_root → new_root)`;
  the native balance/umem AIR already enforces Σδ=0 for the effect the leg proves. A side-structure
  that moves value owes a per-asset balance the leaf itself proves (§5).
- *No-forgery.* The teeth are read from **FRI-bound descriptor PIs**, never free scalars; the
  backing leaf re-proves the **real** statement. Equality (`connect`) not assignment.
- *Attenuation.* Authority-bearing claims (sovereign key-commit, membership auth-root) bind
  through the cap_root/`recKExec_authorized` gate; the teeth are the committed authority witness.
- *Nullifier.* A spend leaf exposes its nullifier as a claim lane
  (`NOTE_SPEND_CLAIM_LEN` lane 0) connected to the deployed `NOTESPEND_NULLIFIER` PI + the
  faithful `nullifier_root`; the grow-gate then rejects reuse.

### 3.4 GRADE composition — the turn is graded at its weakest leg

The composite turn's grade is the **minimum** over its legs on the trust-minimization order
(`DREGGFI-VISION.md:26-29`, "honestly graded at its weakest leg",
`tee-verify/src/attested_data.rs:71-77`):

```
REPLAYABLE  (strongest: trust nothing but your machine + public chain)
  >  PROVED  (trust the proof checker + named crypto assumptions)
  >  ATTESTED (trust the HW-vendor root + side-channel residual)
```

- A **PROVED turn requires all-PROVED legs** — every side-structure's check is in-circuit (folds).
  One ATTESTED leg (an off-AIR authenticity carrier) makes the whole turn ATTESTED-for-that-input.
- The grade is **per-claim, not per-product**: a DrEX fill is "ATTESTED for the price input,
  PROVED for the clearing arithmetic, never uniformly PROVED" (`attested_data.rs:71-77`;
  `DREGGFI-VISION.md:84` frames moving the mark ATTESTED→PROVED as the frontier).
- Composition is monotone under fold: the tree combine cannot *raise* a grade — a segment carrying
  an ATTESTED leg stays ATTESTED up the tree. (This document proposes carrying the grade as a
  reserved segment lane so the root's grade is itself a fold output, not an out-of-band claim.)

### 3.5 The concrete interface (Rust trait shape)

No such trait exists today — the pattern is an eight-armed `match` over `CarrierWitness`
(`ivc_turn_chain.rs:3112-3520`). The deliverable is the trait that *generalizes* that match; each
arm becomes an instance. Grounded in the real signatures:

```rust
/// A side-structure that contributes a graded, bound claim to a turn.
/// Instances: the 8 deployed carriers, and the 5 census side-structures once conformed.
pub trait SideStructure {
    /// The re-provable backing witness (e.g. BridgeWitnessBundle.note_spend:
    /// NoteSpendingWitness; DecoWitnessBundle.witness: DecoLeafWitness).
    type Witness;

    /// The committed-claim tuple width (NOTE_SPEND_CLAIM_LEN=7, BRIDGE_MINT_HASH_CLAIM_LEN=1, …).
    const CLAIM_LEN: usize;
    /// Where the deployed descriptor pins the teeth (BRIDGE_MINT_HASH_PI=46,
    /// FACTORY_CHILD_VK_PI_LO=47, MEMBERSHIP_CLAIM_PI_LO=50, …). None ⇒ derived per-member.
    const CLAIM_PI_LO: usize;
    /// The (column, row) the admission check expects the pin at (fail-closed).
    const PIN_SITE: (usize, VmRow);
    /// PROVED if `prove_backing_leaf` verifies in-fold; ATTESTED if authenticity is off-AIR.
    const GRADE: TrustGrade;

    // ---- VERIFY (dispatch by GRADE) ----
    /// PROVED path: re-prove S's REAL statement as a foldable IR-v2 leaf that re-exposes
    /// the CLAIM_LEN-lane committed claim. (= prove_note_spend_leaf_with_claim et al.)
    fn prove_backing_leaf(
        w: &Self::Witness, claim: &[BabyBear], cfg: &DreggRecursionConfig,
    ) -> Result<RecursionOutput<DreggRecursionConfig>, String>;

    /// Read the exposed claim off a minted leaf. (= read_exposed_note_spend_claim.)
    fn read_claim(out: &RecursionOutput<DreggRecursionConfig>) -> Option<[BabyBear; /*CLAIM_LEN*/ _]>;

    // ---- BIND (uniform across all instances) ----
    /// Fail-closed admission: the deployed descriptor MUST pin the teeth at PIN_SITE.
    /// (= carrier_claim_pins_admitted.)
    fn admit(desc: &EffectVmDescriptor2, pis: &[BabyBear]) -> Result<(), String>;

    /// The binding node: dual-expose the leg (segment ++ teeth), connect teeth→backing.claim,
    /// re-expose the segment. (= prove_note_spend_mint_binding_node_segmented.)
    fn bind_node(
        dual_leg: &RecursionOutput<DreggRecursionConfig>,
        backing_leaf: &RecursionOutput<DreggRecursionConfig>,
        cfg: &DreggRecursionConfig,
    ) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError>;
}
```

The whole `prove_chain_core_rotated` carrier match then collapses to: `admit` → dual-expose leg →
`prove_backing_leaf` → `bind_node`. That refactor is *not* required for conformance — it is the
readable shape the eight arms already instantiate.

### 3.6 The Lean refinement obligation each side-structure owes

The fold gives a *circuit* guarantee (the leaf verifies, the teeth connect). Soundness of the
*model* requires a `_refines_` theorem tying the committed claim to a `recKExec`-style law. Each
side-structure owes:

```
theorem S_claim_refines (turn : Turn) (claim : SideClaim S) (k k' : RecordKernelState)
    (hbound : boundInTurn claim turn)          -- the fold connected the teeth (circuit ⇒ this hyp)
    (hstep  : recKExec k turn = some k') :      -- the composite turn committed
    -- S's assertion implies the VM's law over the state it touched:
    ConservesOn S k k' ∧ AuthorizedOn S k turn ∧ NullifierFreshOn S k turn
```

This is the shape already discharged for the ring (`Market/Fairness.lean:130`
`cycleValid_fulfilled_respects_limits` returns `recTotalAsset k' b = recTotalAsset k b ∧
RingBalanced ∧ limit-respecting`), for the market tower (the ledger-realization weld,
`Market/LedgerRealization{,Ext}.lean` — §4.3), and for the shielded pool
(`Dregg2.Shielded.ClaimRefinement.shielded_spend_claim_refines` — §4.1). The refinement is the
honest gate: `#assert_axioms` clean ≠ hypothesis-free — audit that `hbound`/`hstep` are the *only*
hypotheses and that the conclusion is a real law, not a tautology.

---

## 4. The integration path — per side-structure

### 4.1 Shielded pool — verified-leaf, BUILT (THE MARQUEE)

**Verdict: verified-leaf, PROVED for membership + nullifier + in-AIR ring conservation. The
adapter, binding node, fused ring AIRs, and the Lean refinement obligation exist.**

The base object (`shielded/mod.rs`, `pool.rs`): the shielded transfer is its *own* composed
proof object, not woven into `effect_vm`/`descriptor_ir2`. `Effect::ShieldedTransfer` exists
(`turn/src/action.rs:1542-1545`, `LinearityClass::Conservative`) and remains a pinned
`NamedResidual` with no descriptor rung (`effect_enum_descriptor_residual_gate.rs:112`).

The two halves, and where each stands:

- **The STARK half (membership + nullifier) → a PROVED leaf, BUILT.** `dregg-shielded-spend-v1`
  (`spend_circuit.rs`, 3 PIs) proves in-circuit: the note commitment
  `hash_fact(value,[asset,owner,rand])` is a member of the 4-ary Merkle tree at `merkle_root`,
  and `nullifier = hash_fact(leaf, key[0..4])`. Its committed claim is exactly
  `[nullifier, merkle_root, value_binding]`. The IR-v2 leaf/expose/connect treatment exists:
  `prove_shielded_spend_leaf_with_claim` re-exposes the 3-felt tuple
  (`SHIELDED_SPEND_CLAIM_LEN`, `shielded_spend_leaf_adapter.rs:469-490`) and
  `prove_shielded_spend_binding_node` connects a leg's claimed tuple to the verifying sub-proof
  lane-by-lane (a `connect` conflict ⇒ UNSAT ⇒ no root). The Lean refinement obligation (§3.6)
  is discharged as `Dregg2.Shielded.ClaimRefinement.shielded_spend_claim_refines` — a valid
  claim refines an authorized, never-re-spendable VM step, non-vacuous in both polarities.

- **The value-balance half (conservation) → in-AIR, PROVED for a ring.** `Σ value_in = Σ
  value_out` is the authoritative in-AIR field gate of the ring-clearing AIRs
  (`shielded_ring_clearing_air.rs`; a minting / non-conserving ring is UNSAT —
  `nonconserving_ring_is_unsat`), with the Poseidon2 `value_binding` as the PQ value
  commitment and in-AIR range over the BabyBear no-wrap window (`wraparound_mint_ring_is_unsat`,
  `out_of_range_output_is_unsat`). The off-AIR Schnorr excess is retired from the TCB (the
  Option-A cutover, `docs/deos/PQ-SHIELDED-COMMITMENT.md §5`). Named residual: the full 64-bit
  multi-limb in-AIR range widening.

**The "ring over shielded notes" weld** (DrEX rung-3, `DREGGFI-VISION.md §4.3`) is built at
both layers: the fused ring AIR folds `prove_shielded_spend_leaf_with_claim` leaves
(`shielded_ring_clearing_air.rs`, e.g. `honest_shielded_2ring_folds_and_verifies`), and the
Lean side proves the fusion — `shielded_ring_fused_clears` (`Market/LedgerRealizationExt.lean`),
where `LegFused` ties the matched cycle's offer asset/amount to a real spent member note. The
Lean fusion is spec-level; the in-AIR arithmetic tying the cleared amounts to the note values
is the ring AIR's conservation gate.

**Named residuals:** (a) the `Effect::ShieldedTransfer` descriptor rung to retire the
`NamedResidual` (VK-affecting — rides the big-bang regen); (b) the 64-bit multi-limb in-AIR
range widening.

### 4.2 Attested-data lane — BESIDE → verified-leaf (ATTESTED grade)

**Verdict: verified-leaf, grade ATTESTED by construction.**

Today (`tee-verify/src/attested_data.rs:161-175`): `AttestedFact{kind, measurement, payload,
report_data, tcb_ok, grade=Attested}` is minted by a four-check fail-closed verifier
(`attest_data`, `:218-254`) rooted in a pinned TEE root (Nitro G1 `lib.rs:51,159-260`; SNP ARK/ASK
`snp.rs:343-368`). No `effect_vm` code touches it — the BESIDE classification stands — but it has
one real non-test consumer: `tee-verify/src/oracle_mark.rs`, where `GradedMark::from_tee_attested`
composes an `AttestedFact` over a price payload into the graded oracle-mark weld (no bare-price
constructor; both polarities tested), tied to Lean via `metatheory/Market/OracleWeld.lean`
(`oracle_weld_composite_grade`, restating `no_bad_debt`/`lending_sound` over the `AttestedMark`) —
the weld `DREGGFI-VISION.md` §7 (the oracle-inputs edge) documents. (A *sibling* turn-integrated
path exists via the predicate registry,
`deos-hermes/src/tee_fact.rs:9-16,41,107`, which binds the turn/session commitment into the quote's
`report_data` — but it mints a predicate result, not an `AttestedFact`.)

Field mapping onto the ABI: `AttestedFact` already carries **committed-claim** (`payload` +
`report_data` binding) and **trust-grade** (`grade`, always `Attested`); it carries the
**attestation as verified claims** (`measurement`/`report_data`/`tcb_ok`), but **no state-delta**
and **no leaf**.

**Conformance work:** the in-AIR path is the existing `zkoracle_leaf_adapter.rs` pattern — a
Poseidon2-only commitment leaf that recomputes a chain commitment over the witnessed attestation
body IN-AIR and exposes it as PI-pinned claim lanes (`zkoracle_leaf_adapter.rs:1-70`). Wire
`report_data` (or the `zkoracle_leaf_commit` of the body) as the claim teeth; the TEE cert-chain
verify stays OFF-AIR as the named §8 carrier — **grade ATTESTED, structurally**. The state-delta is
supplied by the *consuming* effect (e.g. a `settleRing` priced by the attested mark), not by the
fact itself: the attested fact is an *input* leg, its segment the identity delta.

**Honest gap:** the leaf commitment currently diverges from `content_commitment`
(`zkoracle_leaf_adapter.rs:9-40`, `zkoracle_leaf_commit ≠ hash_bytes` because the chip bus exposes
8 of 16 permutation lanes) — welding requires either re-pointing the attestation commitment or
widening the chip bus. Until then the fold's connect target is `zkoracle_leaf_commit`, not
`content_commitment`.

### 4.3 DrEX / Market clearing — ring NATIVE, Market tower NATIVE via ledger-realization

**Verdict: ring = native (keep); Market clearing = native-via-ledger-realization, proven.**

The **ring** conforms as native: `verified_settle.rs` lowers a settlement to
`Effect::Transfer` legs (`extract_legs`, `:201-208`) and folds each through the verified per-asset
executor, cross-checked against the real Lean FFI `record_kernel_step`
(`verified_settle.rs:311-350,680`; `verified_gate.rs:13-18`) — the proved `Exec.recKExec`. It is
conservation-asserted (`settleRing_conserves`) and fail-closed. Two honest caveats: the FFI
cross-check only fires when the gate is installed (`verified_settle.rs:701`); and `finalize_verified`
is a separate entry surfaced beside `finalize`, not the committing turn itself
(`trustless.rs:1638-1664`).

The **Market clearing tower** (`metatheory/Market/`) inherits the ring's native path through the
proven ledger-realization refinement: `Market/LedgerRealization.lean` welds the full-fill / tight
cycle (`fullFill_cycle_ledger_realized`), and `Market/LedgerRealizationExt.lean:5-27` welds the
rest — genuine partial fills in full generality (`partialFill_cycle_ledger_realized`, with the
sharp non-vacuity that a non-tight book's FULL-fill lowering does NOT conserve), the per-fill
pool absorption (`pool_fill_ledger_realized`), and the rung-3 shielded fusion
(`shielded_ring_fused_clears`) — each down to `settleRing`/`recKExec`, so the clearing's
conservation IS the kernel's `recTotalAsset`, not a local `netFlow`. Fairness is proven at the
same level: `uniform_price_envy_free` and `uniform_price_optimal`
(`Market/Optimality.lean:147-198`, with a `#guard`-pinned concrete instance).

**Named residuals** (what stays model, per `LedgerRealizationExt.lean`'s own ledger): the pool
`∀`-schedule solvency lift over the `ℚ → ℤ` boundary (the per-fill tie is kernel-real; its
kernel gate `recKExecAsset_overdraw_refused` is the reserve-floor analogue), and the Lean-side
tie between the spec-level fusion (`LegFused`) and the ring AIR's in-AIR amount arithmetic
(§4.1).

### 4.4 Intent / ring solver — stays external (untrusted-search + verified-check)

**Verdict: stays external; conforms as an untrusted producer whose output the settle path
verifies.**

The solver is the textbook untrusted-search + verified-check pattern. It is TRUSTED today — "Ring
trade discovery runs on the executor. A malicious executor could front-run, censor, or produce
suboptimal solutions" (`lib.rs:10-12`) — producing `RingTrade{participants, settlements, score}`
(`solver.rs:51-59`) via Johnson's-cycles + Shapley-Scarf TTC. Its output is **re-verified** by the
settle path: `settle_fulfillment_verified` re-derives legs from the independently-lowered turn and
fails closed on `LegCountMismatch`/`LegDataMismatch` (`verified_settle.rs:214-247`) — the solver
cannot smuggle a leg the lowering didn't produce. Predicate caveats are checked through the
canonical registry, not trusted (`solver.rs:167,192-216`).

**Conformance:** the solver does **not** plug into the ABI as a leaf — it is the *search* half. Its
*output* plugs in as native `Transfer` legs (§4.3). The target state (`lib.rs:18`, "Solvers produce
STARK proofs of solution validity, verifiable by anyone") would make the solver itself a PROVED
side-structure whose committed claim is "this settlement is a valid cleared cycle of these
intents" — a leaf whose teeth connect to the cleared legs. That is the honest gap: today the check
is re-execution, not a foldable proof.

**Honest gap:** solver-STARK-of-validity (target, not built); the batch-binding is the only public
input surface today (`trustless.rs:784-798`).

### 4.5 Cross-chain holdings — governance BESIDE, circuit LEAF-FOLDED (commitment-only)

**Verdict: leaf-folded (commitment-only) is the ABI-conforming path; governance tally stays
beside; grade = consensus-verified light-client (foreign-chain consensus off-fold) → ATTESTED-class
until the walk/keccak fold.**

Two surfaces:

- **Governance (`dregg-interchain-gov`) = BESIDE.** The light-client verdict
  (`consensus_proven: bool`) becomes a `ProvenForeignHolding{chain, holder, asset, amount,
  snapshot, consensus_proven}` (`proven_foreign_holding.rs:154`), granted weight only at the top
  rung (`holding_weight.rs:745-757`, fail-closed on `!is_consensus_proven`). **No proof material
  crosses into the apex** — the fact deliberately drops the Merkle branches / sync-committee sigs
  (`proven_foreign_holding.rs:18-25`). This is a governance side-structure; keep it beside.
- **Circuit pilot = LEAF-FOLDED via `custom_proof_bind` + `custom_leaf_adapter`.** This IS the ABI
  conformance, and `custom_proof_bind.rs` is the **generic verified-leaf adapter**: it takes a
  `BoundCustomProof{program, proof_bytes, public_inputs, witness_values}`
  (`custom_proof_bind.rs:107-125`) and a claimed binding `ClaimedProofBind{vk_hash[8],
  commitment[8]}` (`:145-151`). ⚠ The off-AIR `verify_proof_bind` this bullet used to describe as
  the checker is GONE (stark-kill `dd038c08e`); what survives in the module is the canonical
  derivation `custom_proof_pi_commitment` (an 8-felt `WideHash`), and the four conditions are now
  discharged IN-CIRCUIT by the fold — the sub-proof leaf is re-proven (so "the STARK verifies" is
  the leaf's own satisfiability), its commitment is recomputed in-circuit and `connect`ed to the
  leg's claimed lanes, and the program VK8 rides the same connect. A custom leg offered WITHOUT a
  carrier witness is refused at arm selection (`require_no_unbacked_proof_bind`), so there is no
  path that skips it. An MPT
  holding-commitment leaf (`mpt_holding_leaf.rs`) is folded via the `CarrierWitness::Custom` arm
  (`ivc_turn_chain.rs:3112-3154`), its 8-felt identity commitment connected to the leg's
  `custom_proof_commitment` (PI 46..53). Crucially the MPT walk + keccak stay **OFF-AIR**,
  executor-verified named carriers (the DECO posture, `mpt_holding_leaf.rs:32-41`).

**Conformance work:** `custom_proof_bind` already *is* the chain-agnostic ABI adapter for any
foreign proof — a new chain plugs in by providing a `CellProgram` whose AIR checks its
inclusion+consensus and whose PI commitment is the holding identity. **Honest gap:** the fold binds
only the *identity* commitment; foreign-chain finality (sync-committee BLS / Tendermint / Solana
supermajority) and the MPT walk/keccak stay off-AIR (rung-2, `VERIFIED-LIGHTCLIENT-FOLD-PILOT.md`
P1/P2 named) — so the grade is "consensus-verified light-client," an ATTESTED-class input, not a
uniformly-PROVED turn.

---

## 5. The invariant-safety argument (load-bearing)

**Claim: a side-structure plugging in through this ABI cannot violate the VM's four proved
invariants, because the bind is equality-into-FRI-bound-PIs (not free assignment), the state-delta
is anchored to the descriptor's real roots, and admission is fail-closed — and because each plugin
discharges a per-invariant obligation the composite receipt then inherits.**

The composite turn's receipt commits `(old_commit, new_commit, effects_hash, prev_hash)` and is
tamper-evident (`Exec/Receipt.lean`). For the composite to be sound, each plugged-in claim must be
covered. What each plugin owes, per invariant:

| Invariant (core law) | What the plugin owes | Enforced by |
|---|---|---|
| **Conservation** `recKExec_conserves` (`RecordKernel.lean:584`) / per-asset `maExec_conserves_per_asset` (`:699`) | Expose a per-asset Σδ the leaf proves. Native effects: the balance/umem AIR. Shielded: the in-AIR field gate `Σ value_in = Σ value_out` + in-AIR range in the ring-clearing AIRs (§4.1) — PROVED over the BabyBear no-wrap window; 64-bit multi-limb widening named. Ring/market: `settleRing_conserves` / the ledger-realization weld (§4.3). | segment `first_old8→last_new8` anchored to descriptor roots; `connect` in `segment_combine_expose` |
| **No-forgery** (hash-pinned advances) | Re-prove the **real** statement, not a binding-only shadow (the `bridge_action_air` refusal, `note_spend_leaf_adapter.rs:19-28`). Teeth read from FRI-bound PIs, never free scalars. | `prove_backing_leaf` folds under the recursive verifier; `connect` = equality |
| **Attenuation-only** `recKExec_authorized` (`:601`) + `attenuate_narrows` (`Caveat.lean:162`) | Authority claims bind the committed authority witness (sovereign KEY_COMMIT, membership auth-root) through the cap_root gate; a claim cannot amplify. | `carrier_claim_pins_admitted` (fail-closed) + the in-AIR non-amp order gates (`effect.rs:106-108`) |
| **Nullifier no-double-spend** `nullifierFreshUMem` (`effect_vm_descriptors.rs:866`) | Expose the nullifier as a claim lane connected to the deployed `NOTESPEND_NULLIFIER` PI + `nullifier_root`; the runtime grow-gate rejects reuse. | claim lane 0 `connect` (`note_spend_leaf_adapter.rs:70-71,652`); nullifier-set gate |

**Why the bind cannot cheat:**

1. **Equality, not assignment.** The teeth are `cb.connect(leg[·], backing[·])`
   (`note_spend_leaf_adapter.rs:817`) — a DSU merge that is UNSAT on conflict, not a write. A leg
   whose claimed tuple no verifying sub-proof backs mints no root
   (`forged_nullifier_does_not_fold`, `forged_mint_hash_does_not_fold`,
   `note_spend_leaf_adapter.rs:1018-1053`).
2. **State-delta anchored, not free.** The segment anchors are sourced from the descriptor's real
   rotated commitment PIs (`prove_descriptor_leaf_dual_expose_at`, `ivc_turn_chain.rs:1547-1603`);
   a leg cannot claim a state transition its descriptor did not commit — the wide/narrow anchor
   sourcing is structural (`n >= WIDE_PI_COUNT`), and a misclassification fails *closed*
   (`WitnessConflict`), never open (`:1549-1558`).
3. **Fail-closed admission.** A side-structure whose deployed descriptor does not pin its claim
   teeth at the expected column/row is **refused** (`carrier_claim_pins_admitted`,
   `ivc_turn_chain.rs:3173-3181`) — the fail-open law. A pin-less descriptor never silently
   degrades to a fabricated fold.
4. **Grade cannot launder.** An ATTESTED leg (off-AIR authenticity) makes the turn ATTESTED — it
   cannot be re-badged PROVED, because the in-circuit fold only witnesses the *commitment*, and the
   composition rule (§3.4) grades at the weakest leg. This is why DECO's ed25519 and the TEE
   attestation lane are honestly ATTESTED, not laundered as PROVED.

**The residual honesty:** the invariant-safety is a *circuit* guarantee until each plugin
discharges its **Lean refinement obligation** (§3.6) — the `S_claim_refines` theorem that ties the
committed claim to the `recKExec` law. Discharged for the ring (`Fairness.lean:130`), the market
tower (`Market/LedgerRealization{,Ext}.lean`), and the shielded pool
(`Dregg2/Shielded/ClaimRefinement.lean`); named-open for the light-client walk/keccak
(`VERIFIED-LIGHTCLIENT-FOLD-PILOT.md` P1/P2). `#assert_axioms`
clean is necessary, not sufficient: audit that the refinement's only hypotheses are
`hbound`/`hstep` and that its conclusion is a real law.

---

## 6. Summary — the verdict table and the first build

| Side-structure | Mode | Grade | Named residuals |
|---|---|---|---|
| **Shielded pool** | verified-leaf (BUILT: adapter + binding node + fused ring AIRs) | PROVED (membership+nullifier+in-AIR ring conservation) | `Effect::ShieldedTransfer` descriptor rung (VK regen); 64-bit multi-limb in-AIR range |
| **Attested-data** | verified-leaf | ATTESTED (structural) | `zkoracle`-pattern commitment leaf; `zkoracle_leaf_commit ≠ content_commitment` weld |
| **DrEX ring** | native (keep) | PROVED (conservation+IR) | FFI-gate-conditional; `finalize_verified` beside `finalize` |
| **DrEX Market clearing** | native via ledger-realization (proven) | PROVED (IR + uniform-price optimality/envy-free) | pool `∀`-schedule `ℚ → ℤ` lift; spec-level fusion ↔ in-AIR amount tie |
| **Intent solver** | external producer | (output PROVED via ring) | solver-STARK-of-validity (target, not built) |
| **Cross-chain holdings** | leaf-folded (commitment) | ATTESTED-class (consensus off-fold) | MPT walk + keccak in-AIR (P1/P2); finality stays rung-2 |

**The marquee integration exists.** The shielded pool — the census's headline seam — is
leaf-adapted: `prove_shielded_spend_leaf_with_claim` over the 3-felt claim
`[nullifier, merkle_root, value_binding]`, its lane-connecting binding node, the fused
ring-clearing AIRs that fold those leaves, and the Lean `shielded_spend_claim_refines`
obligation (§4.1) — realizing the DrEX "ring over shielded notes" weld: two conforming
side-structures folded in one turn. The open build fronts are now the attested-data commitment
leaf (§4.2, including the `zkoracle_leaf_commit ≠ content_commitment` weld), the
`Effect::ShieldedTransfer` descriptor rung (VK-affecting, rides the big-bang regen), and the
light-client walk/keccak fold (§4.5).

---

## See also

- The proto-ABI: `circuit-prove/src/*_leaf_adapter.rs`, `custom_proof_bind.rs`,
  `ivc_turn_chain.rs::{prove_chain_core_rotated, prove_descriptor_leaf_with_pi_slice_expose,
  prove_descriptor_leaf_dual_expose_at, segment_combine_expose}`, `joint_turn_aggregation.rs`
  (`CarrierWitness`).
- The core: `circuit/src/effect_vm/effect.rs`, `circuit/src/effect_vm_descriptors.rs`,
  `metatheory/Dregg2/Exec/{RecordKernel,Receipt}.lean`.
- The grade spine: `docs/deos/DREGGFI-VISION.md §1,§7`; `tee-verify/src/attested_data.rs`.
- The side-structures: `circuit-prove/src/shielded/`, `tee-verify/`, `intent/`,
  `metatheory/Market/`, `dregg-interchain-gov/`, `dregg-governance/`, the light-client crates
  (`eth-lightclient/`, `cosmos-lightclient/`, `bridge/`).
