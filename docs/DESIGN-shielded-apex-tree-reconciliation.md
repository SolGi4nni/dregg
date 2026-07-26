# DESIGN — Shielded Apex Tree Reconciliation

**Architectural design. 2026-07-24. Ground-truthed at HEAD `4dd6748d38`.** Read-only pass except this
file. Extends `docs/PLAN-shielded-apex-redesign-2026-07-20.md` and
`docs/DECISION-shielded-redesign-2026-07-20.md` (ember's decision: **B now + A redesign**) with the
piece those docs assume but do not build: **the committed tree the pin binds to does not exist, and the
two trees in play cannot be unified by "pinning" — they have different structure, width, and leaf
content.** This doc states that two-trees problem precisely, gives the reconciliation design grounded in
the real types, maps it to the #15/#16/#17 closures, gives the proven-object wiring recipe, and lays out
the staged lanes with ordering and VK-epochs.

The one-line thesis: **the circuit half of the fix is already proven in Lean and merely unrouted; the
missing half is a committed shielded-note accumulator — a new ledger accumulator, privacy-preserving by
construction — that makes the proven descriptor's `AccumulatorSound` hypothesis true in reality. "Route
through the apex" closes nothing until that accumulator exists.**

House-law-1 note: all AIR / constraint work below is authored in Lean and emitted; the Rust changes are
executor state (a new accumulator set) and the emit/route plumbing. The security-bearing descriptors
(`shieldedSpendDesc`, `shieldedValueLinkDesc`, `shieldedWideValueLinkDesc`) are **already Lean-authored**
(`metatheory/Dregg2/Circuit/Emit/*`); nothing new is hand-authored in Rust AIR.

---

## 1. The two-trees problem, stated precisely

### 1.1 The membership tree the transfer proves against (prover-side, uncommitted)

The deployed shielded path is `apply_shielded_transfer` (prover-gated,
`turn/src/executor/apply.rs:1713`). It reconstructs the transfer from the wire:

```
ShieldedTransfer::from_serialized_parts(payload.merkle_root, …)   // apply.rs:1748-1749
```

`payload.merkle_root: u32` (`turn/src/action.rs:1021`, the third field of `ShieldedTransferPayload`)
becomes `BabyBear::new(merkle_root)` (`circuit-prove/src/shielded/transfer.rs:286`). Every input's hidden
spend proof is checked against **that** root: `input.public_inputs(self.merkle_root)` pins
`pis[pi::MERKLE_ROOT] = merkle_root` (`transfer.rs:91-95`, verified `transfer.rs:155`).

That membership tree is an **arity-4 plain Poseidon2 Merkle tree** whose leaf is a **hiding** note
commitment. From the spend circuit (`circuit-prove/src/shielded/spend_circuit.rs` module doc, mod.rs
`:26-40`):

- membership: `parent = hash_fact(current, [sib0, sib1, sib2, position])` up to `merkle_root`;
- the leaf is constrained to the note commitment `hash_fact(value, [asset_type, owner, randomness])`
  (C6a/C6b) — **the value is hidden inside the hash**;
- nullifier: `nullifier = hash_fact(leaf_commitment, key[0..4])`;
- value-binding: `value_binding = hash_fact(value, [asset_type, randomness, 0])` (C7).

The root is a **single felt (~31-bit BabyBear)**. It is supplied on the wire and **pinned to nothing** —
this is seam #15 (the theft seam; `DECISION §1`). Nowhere does the executor compare this root to any
committed accumulator.

### 1.2 The committed accumulator (ledger-side, cleartext)

The committed commitments accumulator is `note_commitments: Mutex<CommitmentSet>`
(`turn/src/executor/mod.rs:858`). Its `root8()` is absorbed into the committed rotation state at each turn
alongside the nullifier and revoked roots:

```
self.note_nullifiers.lock().unwrap().root8(),      // executor/mod.rs:1940
self.note_commitments.lock().unwrap().root8(),      // executor/mod.rs:1941  (commitments_root)
self.note_revoked.lock().unwrap().root8(),          // executor/mod.rs:1942
```

`CommitmentSet` (`cell/src/commitment_set.rs:60`) is a grow-only `(commitment → value)` map. Its `root8`
is a **`CanonicalHeapTree8` — a depth-16, BINARY (arity-2 NODE) sorted indexed-Merkle tree** (`circuit/src/heap_root.rs:62`
`HEAP_TREE_DEPTH = 16`; leaf digest `hash[addr, value, next_addr]`, `heap_root.rs:107-109`). The leaf is:

```rust
// cell/src/commitment_set.rs:262-273
HeapLeaf::entry(
    fold_bytes32_to_bb(commitment),     // addr = folded commitment felt
    split_u64(value).0,                  // value = NOTE_VALUE_LO, low 30 bits — CLEARTEXT
)
```

**The committed leaf carries the cleartext note value.** This root is **8 felts (~124-bit)**. It is
written by exactly one path: `apply_note_create` (`apply.rs:2142`), the **cleartext** note-create effect,
which inserts `(commitment, value)` with `value: u64` public (`apply.rs:2250-2266`).

### 1.3 The three-way divergence

The membership tree (1.1) and the committed accumulator (1.2) are **genuinely different trees**, on three
independent axes:

| Axis | Shielded membership tree (§1.1) | Committed accumulator (§1.2) |
|---|---|---|
| **Population** | prover-built; shielded outputs never appended anywhere committed | grown only by cleartext `apply_note_create` |
| **Width** | 1 felt (~31-bit BabyBear) | 8 felts (~124-bit) |
| **Structure** | arity-4 plain Poseidon2 Merkle | depth-16 arity-2 sorted indexed-Merkle (IMT, `next_addr` links) |
| **Leaf** | `hash_fact(value,[asset,owner,rand])` — **hiding** | `hash[fold(commitment), split_u64(value).0, next_addr]` — **cleartext value** |

Consequences that make "pin `merkle_root` to the committed root" impossible as-is:

1. **Population.** `apply_shielded_transfer`'s only committed mutation is the GATE-3 nullifier inserts
   (`apply.rs:1783-1826`). It appends **no** output commitment to `note_commitments`. The output legs
   (`payload.output_legs`, `apply.rs:1756`) carry Ristretto `commitment_bytes` used only for the
   conservation gate (`apply.rs:1774-1781`) — **not** the Poseidon2 hiding note commitment a future spend
   would prove membership of. **Where does a shielded output land so it becomes spendable? Nowhere
   committed.** It is spendable only via the prover's own off-ledger note tree — which is exactly why the
   prover can choose `merkle_root` (#15). The explicit placeholder says so (`apply.rs:1808`): *"`0` is a
   placeholder until the shielded accumulator wiring is designed … segregating the committed accumulator
   from the Rust double-spend dedup set is Stage-B/D work."*

2. **Structure + leaf.** Even if we appended shielded outputs to `note_commitments`, the shielded
   membership gadget proves an **arity-4 plain Merkle** path, while `note_commitments.root8()` is a
   **depth-16 arity-2 sorted IMT**. The spend proof cannot open against it. And the committed leaf
   requires a **cleartext value** (`split_u64(value).0`), which a shielded note must not reveal — a
   shielded leaf has no public value to put there.

3. **There is no committed shielded tree at all.** The shielded nullifiers *are* committed (they pollute
   the shared `note_nullifiers.root8()`, domain-separated per `apply.rs:28`), but the shielded
   *commitments* are committed **nowhere**. So there is no committed root that contains the shielded notes
   for `merkle_root` to be pinned to.

**Net:** #15 is not a missing equality check — it is a missing accumulator. The redesign's foundational
work is introducing a committed shielded-note accumulator; only then does a `merkle_root` pin have a real
root to bind.

### 1.4 There is also no on-ramp

There is no `Shield`/`Deshield` effect (`Effect` enum, `action.rs:1043`; the only note effects are
`NoteSpend`, `NoteCreate`, `ShieldedTransfer`). So how value first *enters* the shielded pool is
undefined in the deployed path — see §7 open questions.

---

## 2. What is already proven vs what is missing

The surprising ground truth (verified at HEAD): **the circuit half of the fix is already authored and
proven in Lean, and merely not routed into the emit pipeline or the executor.**

### 2.1 Proven, unrouted — the circuit half

Three Lean-authored descriptors exist, are type-checked in `Dregg2.lean`, but are **absent from
`EmitByName.byNameDescriptors`** (`metatheory/EmitByName.lean:108`; the only shielded entry wired is
`shielded-whole-note-swap-substrate-v1`, `:217-218`):

- **`shieldedSpendDesc`** — `metatheory/Dregg2/Circuit/Emit/ShieldedSpendDescriptor.lean:264`, name
  `"dregg-shielded-spend-pinned-root::v1"`, traceWidth 48, piCount 4
  (`piNUL=0, piROOT=1, piVB=2, piCOMMITTED=3`). **THE #15 PIN is in-AIR** (`:255-258`):
  ```
  -- ⚑ THE #15 PIN: the root lane AND the chain's final fold are the COMMITTED root PI
  , .base (.piBinding .first cROOT piCOMMITTED)
  , .base (.piBinding .last  cROOT piCOMMITTED)
  , .base (.piBinding .last  cPAR  piCOMMITTED)
  ```
- **`shieldedValueLinkDesc`** — `…/Emit/ShieldedValueLinkDescriptor.lean:205`,
  `"dregg-shielded-value-link-conserve::v1"`, width 23, PI 2 (#16: leaf↔leg value-link + conservation).
- **`shieldedWideValueLinkDesc`** — `…/Emit/ShieldedWideValueLinkDescriptor.lean:247`,
  `"dregg-shielded-wide-value-link-conserve::v1"`, width 30, PI 9 (#17: full 8-lane Poseidon2 wide binding).

The soundness is proven against the **emitted objects**, not a reconstruction:

- `ShieldedSpendPortDischarge.emitted_accept_is_committed`
  (`metatheory/Dregg2/Circuit/ShieldedSpendPortDischarge.lean:156`): a satisfying `shieldedSpendDesc`
  trace forces `IsCommittedNote(row0.cCUR) ∧ (last.cPAR ≡ piCOMMITTED) ∧ (row0.cROOT ≡ piCOMMITTED) ∧
  (piROOT ≡ piCOMMITTED)` under only `ChipTableSound` — i.e. the exact committed-root pin
  `ShieldedMerkleRootPin.deployed_admits_but_pin_rejects` said the deployed predicate failed to force.
- `ShieldedValueLinkPin.genuine_note_inflates` (falsifier: a genuinely-owned `v`-note mints `v+1` with
  conservation passing) → `linked_no_inflation` (fix). `emitted_linkHolds`
  (`ShieldedSpendPortDischarge.lean:267`) proves the value-link **by construction** (leafValue = legValue =
  `rowAt cVAL`).
- `ShieldedWideValueLinkDescriptor.narrow_binding_collision_exists` (`:678`): the deployed 1-felt
  (~31-bit) value-binding floor is **UNSATISFIABLE** by pigeonhole (2^32 canonical openings into `p<2^31`);
  `wide_binding_binds` (`:774`) is the payoff over the named `WideBindingCR`/`Poseidon2Width8` floors.

All `#assert_axioms`-clean, non-vacuous (each fires on an explicit satisfying witness).

### 2.2 Missing — the state half (and why it is the whole game)

The discharge proves theft-closure **under a named hypothesis**:

```
-- ShieldedSpendPortDischarge.lean:174
def NoteAccumulatorCR (hash) (committedRoot) : Prop :=
  AccumulatorSound (Hair hash) (IsCommittedNote hash) committedRoot
```

`pin_accept_is_note_committed` (`:182`) concludes "pinned accept ⟹ genuine committed note" **assuming**
`NoteAccumulatorCR`. In reality `AccumulatorSound` holds only if `committedRoot` is the root of a real
ledger accumulator that (a) is maintained from ledger state, not the wire, and (b) admits a leaf iff a
genuine shielded note was appended. **That accumulator does not exist** (§1.3). Building it is the
reconciliation.

There is a second, sharper reason the state half is load-bearing: `piCOMMITTED` is a **public input**. If
the executor fills it from anything the prover controls, #15 simply **reopens** one level up — you'd be
pinning `merkle_root` to a prover-suppliable "committed root." The descriptor's proof and the state
accumulator are two halves of one closure; **neither closes #15 alone.** The proven descriptor makes the
pin a circuit constraint; the committed accumulator makes `piCOMMITTED` a value the prover cannot forge.

---

## 3. The reconciliation design

Three candidate designs, grounded in the real types. **R1 is recommended** as the foundational change;
**R3 is the light-client-visibility endgame layered on R1, not a substitute; R2 is rejected.**

### R1 — a dedicated committed shielded-note accumulator (RECOMMENDED)

Introduce a **fourth ledger accumulator**, `note_shielded: Mutex<ShieldedNoteSet>`, a direct fourth
instance of the exact pattern already used three times (`note_nullifiers`, `note_commitments`,
`note_revoked`; `executor/mod.rs:1940-1942`). Its leaf is the **hiding** Poseidon2 note commitment — the
`shieldedSpendDesc` leaf image `hash[value, asset, owner, rand, 0, NS_FACT_MARK, 1]`
(`ShieldedSpendPortDischarge.IsCommittedNote`) — with **no cleartext value column**. Its tree is the
shielded membership encoding, so spend proofs open against it directly, and its `root8()` is **8 felts**
(this alone retires the ~31-bit width entry point of #15).

- **Append.** `apply_shielded_transfer` appends each output note's hiding commitment to `note_shielded`,
  journaled for rollback (mirroring `note_commitments`' `record_note_commitment_inserted` /
  `journal.rs:657` remove-on-rollback). The append is **proven in-AIR** by a shielded grow-gate — and this
  gate is already modeled: `ShieldedWholeNoteSwapSubstrateDescriptor`
  (`metatheory/Dregg2/Circuit/Emit/ShieldedWholeNoteSwapSubstrateDescriptor.lean`, the one wired shielded
  descriptor) *"proves the private computation, output-note commitment, and binary depth-32 linked exact
  append"* (`circuit-prove/src/shielded_whole_note_swap_substrate.rs:16-18`, `TREE_DEPTH = 32`,
  `PREDICATE_NAME "…::one-opening-aafi32-v1"`). Generalizing that append from a whole-note two-party swap
  to an M-in/K-out transfer is the grow-gate work.
- **Membership pin.** The executor supplies `note_shielded.root8()` as `piCOMMITTED`. The connection of
  the spend leaf's `merkle_root` lane to a committed segment root already exists as a mechanism:
  `prove_shielded_spend_root_binding_node_segmented` (`circuit-prove/src/shielded_spend_leaf_adapter.rs:594`)
  `connect`s the leg's `merkle_root` lane (lane 1) to a segment's commitments-root and re-exposes the
  segment so it *"folds into `aggregate_tree` like any per-turn segment leaf"* (`:570-578`); its negative
  pole `forged_merkle_root_does_not_fold` (`:817`) makes a mismatched root UNSAT. Point that connect
  target at `note_shielded.root8()`.
- **Commit.** Add `shielded_note_root` as a **new base limb** in the rotation carrier. This is a
  precedented move: `revoked_root` is *"the new base limb 37, so every limb index ≥ 37 shifts +1"*
  (`turn/src/rotation_witness.rs:72`; carrier order at `:25-26`), added by the same class of flag-day as
  `B_DISC` (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:177`). Concretely: a new
  `layoutGroup .shielded`, a `B_SHIELDED_ROOT` offset, the completion-limb shift, and the Lean keystone
  absorption-order regen.
- **Privacy preserved.** Leaves are hiding commitments with no value column; the committed root moves when
  the shielded set moves (so a node that accepted a shielded output carries a different root than one that
  did not) but reveals nothing about values, owners, or linkage. Cross-turn continuity is preserved exactly
  as for `commitments_root` (turn N after-root = turn N+1 before-root over the same hiding leaves).
- **Discharges `NoteAccumulatorCR` in reality.** `note_shielded` *is* the tree whose membership implies a
  genuine append; `AccumulatorSound` holds by construction of the grow-gate + the executor's append. The
  named floor collapses to Poseidon2 CR — the same floor Merkle membership and nullifiers already stand on.

**Why R1:** it keeps the proven `shieldedSpendDesc` membership encoding (minimal circuit re-authoring),
the append is already modeled by the substrate, privacy is structural, and the add-a-root flag-day is
precedented. It is the honest reading of *"the shielded commitments must actually LIVE IN a committed
accumulator"* — a **dedicated** one, disjoint from the cleartext `note_commitments`.

### R2 — reuse `note_commitments` with hiding leaves (REJECTED)

Land shielded outputs in the existing `note_commitments` as `HeapLeaf::entry(fold(hiding_commitment), 0)`,
and re-author the spend membership gadget to prove the depth-16 arity-2 sorted IMT.

Rejected: (a) heavy re-authoring of the shielded-spend membership gadget (arity-4-plain → depth-16 IMT
with `next_addr` relinking); (b) it entangles cleartext and shielded accounting in one tree; (c) the leaf
value column is **load-bearing** for the cleartext grow-gate (`split_u64(value).0`, read by the noteCreate
row) but **meaningless** for a shielded leaf — a soundness smell where two leaf semantics share one tree.
A dedicated accumulator (R1) is strictly cleaner.

### R3 — the apex/substrate route (the PLAN's "route through the apex"), layered on R1

Route the transfer through a single Lean-authored clearing descriptor (generalize
`ShieldedWholeNoteSwapSubstrate` to M-in/K-out, or the `shielded-ring-clear-2-endpoint-wide` endpoint
descriptor, `circuit-prove/src/shielded_ring_clearing_air.rs:823`, width 1537 / PI 27) that proves
membership + append + conservation + value-link in **one** proof, publishing pre/post kernel commitments
that fold into the committed turn — making the whole thing **light-client-visible** (today shielded is
node-operator-trust only, `#[cfg(feature="prover")]`, fail-closed on verify-only, `apply.rs:1834`).

**Crucial clarification vs the PLAN.** R3 is **not** an alternative to R1 — it is **how** you prove over
R1's accumulator in one light-client-visible proof. The apex's own endpoint kernel block is a
**synthetic** *"canonical ring-kernel block"* built from the ring's in-circuit columns
(`shielded_ring_clearing_air.rs:705-727`, with `merkle_root` at limbs 17/18 absorbed into `wireCommitR8`);
it does **not** by itself equal the deployed committed shielded root. The `merkle_root`→committed-root
binding is the separate root-binding node (`shielded_spend_leaf_adapter.rs:594`) that folds a segment into
`aggregate_tree`. So R3 ⊇ R1: **the apex is the proof surface; R1 is the state it must bind.** "Route
through the apex" closes #15 only if the apex's committed-root lane is R1's `note_shielded.root8()`.

**Recommendation:** build R1 as the foundational state change (the committed shielded accumulator + its
base limb + the append grow-gate), route the already-proven `shieldedSpendDesc` + value-link + wide-value-
link descriptors to prove membership+pin+link+conservation over it, and treat R3 (the single-proof apex
fold into the committed turn) as the light-client-visibility endgame layered on top — not a shortcut that
skips R1.

---

## 4. The #15 / #16 / #17 closure map

| Seam | Wound (deployed, at HEAD) | Closure | Proven object |
|---|---|---|---|
| **#15** theft | membership vs wire `merkle_root`, pinned to nothing (`apply.rs:1748`, `transfer.rs:286`) | R1 committed accumulator **+** `shieldedSpendDesc` in-AIR `piROOT≡piCOMMITTED` **+** executor sources `piCOMMITTED` from `note_shielded.root8()` **+** 1→8 felt width | `ShieldedSpendPortDischarge.emitted_accept_is_committed` (`:156`); `pin_accept_is_note_committed` under `NoteAccumulatorCR` (`:182`), discharged in reality by R1 |
| **#16** mint | leaf↔leg value-link runs only in tests; GATE-2 conserves the free Pedersen legs, not the STARK leaf values (`apply.rs:1774`; `transfer.rs:196` "does not prove leaf↔leg value equality") | `shieldedValueLinkDesc`: recompute `value_binding`, `connect` to the leaf, Σ-conserve over the **same in-AIR value cells**; retire test-only `verify_value_link` + GATE 2 | `ShieldedValueLinkPin.genuine_note_inflates` (falsifier) → `linked_no_inflation`; `emitted_linkHolds` (`:267`) |
| **#17** PQ posture | the only no-mint gate that *runs* is the Shor-broken Ristretto DLog aggregate (GATE 2), while comments claim Poseidon2-authoritative | move the no-mint gate to `shieldedWideValueLinkDesc`'s 8-lane Poseidon2 wide binding on `WideBindingCR`; Ristretto leaves the no-mint TCB | `narrow_binding_collision_exists` (1-felt floor UNSAT, `:678`); `wide_binding_binds` (`:774`) |

**Named residuals** (unchanged from PLAN §6; not closed by this reconciliation): `pedTwoGen` is a
coordinate abstraction of the real Ristretto curve, not the group point; one BabyBear field caps a
conserving sum near `2^30/N` (`shielded_ring_clearing_nleg_air.rs:85-91`), so large amounts still lean on
the off-AIR Bulletproof. Keep the Ristretto legs as an **explicitly non-TCB** large-amount range crutch
until an in-AIR Bulletproof lands, then drop the curve stack (PLAN §4a/4b). These bound the honesty of the
#17 claim: the mint hazard is closed in-AIR, but conservation runs over an abstraction of the curve.

---

## 5. Proven-object wiring recipe (the automatafl pattern)

The descriptors are **already authored** (§2.1); the work is register → emit → provenance → embed → route.
This mirrors the automatafl SHIP series (`c8789758e8` and predecessors) that just did exactly this.

1. **Register in `metatheory/EmitByName.lean`** (`byNameDescriptors`, `:108`): add three `import`s
   (`~:33-83`) and three tuples, each `("<file>.json", <fully-qualified descriptor>)` — modeled on
   `("shielded-whole-note-swap-substrate-v1.json", …shieldedWholeNoteSwapSubstrateDescriptor)` (`:217-218`):
   - `("dregg-shielded-spend-pinned-root-v1.json", …ShieldedSpendDescriptor.shieldedSpendDesc)`
   - `("dregg-shielded-value-link-conserve-v1.json", …ShieldedValueLinkDescriptor.shieldedValueLinkDesc)`
   - `("dregg-shielded-wide-value-link-conserve-v1.json", …ShieldedWideValueLinkDescriptor.shieldedWideValueLinkDesc)`

   Bump `#guard byNameDescriptors.length` (`:236`, currently 59). If any file is checked in
   newline-terminated, add its basename to `BY_NAME_NEWLINE_TERMINATED` (`scripts/emit_descriptors.py:132-155`).
2. **Emit** the JSON: `DREGG_VK_REGEN_ACK="$(git rev-parse HEAD:metatheory/Dregg2)" scripts/emit-descriptors.sh`
   (wraps `scripts/emit_descriptors.py`; `EmitByName.lean` is `EMITTERS:113` → `split_by_name:809` writes
   `circuit/descriptors/by-name/<name>.json`). Add `DREGG_VK_REGEN_ALLOW_DIRTY=1` if `metatheory/Dregg2`
   is dirty. `lake build` the import closure first.
3. **PROVENANCE.json** (`circuit/descriptors/PROVENANCE.json`) is regenerated by that **same run**
   (`install_and_stamp → write_provenance`, `emit_descriptors.py:979`); each new row lands under
   `by_name_sha256` (hash over the emitted Lean bytes). Verify:
   `python3 scripts/emit_descriptors.py --verify-provenance --strict`.
4. **Rust embed (shielded pattern):** a new `circuit-prove/src/shielded_spend_pinned.rs` (etc.) with
   `pub const DESCRIPTOR_JSON: &str = include_str!("../../circuit/descriptors/by-name/dregg-shielded-spend-pinned-root-v1.json")`,
   `PREDICATE_NAME`, a fail-closed `descriptor()` parse (`if descriptor.name != PREDICATE_NAME { … }`), and
   prove/verify wrappers — modeled on `shielded_whole_note_swap_substrate.rs:46-48,345-347`. Add
   `pub mod …;` to `circuit-prove/src/lib.rs`. (The alternative by-name `STATIC_GOLDENS` dispatch in
   `circuit/src/descriptor_by_name.rs` is the automatafl pattern; the shielded pattern is preferred here
   because each descriptor has a bespoke prove/verify surface.)
5. **No `rotation-*-staged-registry.tsv` row** for these by-name descriptors — those TSVs are the
   unrelated rotation-state registry family. **However**, R1's new base limb (§3) *does* require a
   rotation-registry regen (the `EffectVmEmitRotationV3.lean` `B_*` offsets + the `rotation-*-staged-registry.tsv`
   family) — that is the flag-day, tracked as lane L1 below, not part of this by-name wiring.
6. **Route into `apply_shielded_transfer`** (`apply.rs:1713`): replace `verify_stark_with_wide_bindings`
   (`:1763`) + GATE 2 `verify_full_conservation_bytes` (`:1774`) with (a) verification of the pinned
   descriptors, (b) the `note_shielded` append, (c) `piCOMMITTED` sourced from `note_shielded.root8()`;
   retire `from_serialized_parts(payload.merkle_root, …)` and the wire `merkle_root: u32`
   (`action.rs:1021`). Keep GATE 3 nullifier inserts (`apply.rs:1783`). Delete the `apply.rs:1808`
   placeholder.

---

## 6. Staged lane plan — ordering + VK-epochs

Greenfield (nothing deployed; shielded fails closed off the prover path), so this is staged-additive then
a straight cutover, per the no-greenfield-migration-theater discipline. Order is dictated by data
dependencies, not politeness.

| Lane | Work | Surface (file:line) | Byte-safe / regen | VK-epoch | Depends on |
|---|---|---|---|---|---|
| **L0** | `ShieldedNoteSet` accumulator + executor field + append/rollback journal | new `cell/src/shielded_note_set.rs`; `executor/mod.rs:858,1197,1941`; `journal.rs:526,657` | byte-safe (new Rust type, additive) | none yet | — |
| **L1** | Add `shielded_note_root` as a new rotation base limb | `EffectVmEmitRotationV3.lean` `B_*` (`:174-211`); `rotation_witness.rs:25-75`; regen `rotation-*-staged-registry.tsv` | regen | **VK-epoch (heaviest): re-baselines the WHOLE rotated cohort** — a base limb shifts every rotated descriptor's `trace_width`, so all rotated descriptor VKs change (precedent: `revoked_root` base limb 37) | L0 |
| **L2** | Shielded note-append grow-gate, Lean-authored (generalize the substrate's aafi append) | new `…/Emit/ShieldedNoteAppendDescriptor.lean`; byte-pinned `#guard` | regen | **VK: `dregg-shielded-note-append::v1`** (additive descriptor) | L0 |
| **L3** | Emit-wire the three proven descriptors (§5 steps 1-4) | `EmitByName.lean:108,217,236`; `circuit/descriptors/by-name/*`; `PROVENANCE.json` | regen | **VK: `dregg-shielded-spend-pinned-root::v1`, `…value-link-conserve::v1`, `…wide-value-link-conserve::v1`** (additive) | — (parallel to L0-L2) |
| **L4** | Route `apply_shielded_transfer` (§5 step 6): verify pinned descriptors + append + source `piCOMMITTED`; retire wire `merkle_root` + GATE 2 | `apply.rs:1713-1828`; `action.rs:1021` | behavior cutover | shielded effect VK-regen | L1, L2, L3 |
| **L5** | Fold the shielded segment into the committed turn (R3 light-client visibility) | `shielded_spend_leaf_adapter.rs:594`; `ivc_turn_chain.rs:4089` merge; new `CarrierWitness::Shielded` fold arm (`:3506`) | regen + trust-distribution | **VK-epoch: a new root-VK anchor shape** (fold binds leaf identity transitively; existing anchors unchanged, so not a rotation) — see verdict below | L4 |

**Ordering:** L0 → L1 (needs L0's root) and L0 → L2 (append over L0's tree); L3 is independent (the
descriptors already exist); L4 is the cutover and needs L1 + L2 + L3; L5 is the endgame on L4.

**Byte-safe vs regen split:** only L0 is byte-safe. L1/L2/L3/L5 are all VK-affecting. There are **two
coordinated VK epochs**, not one: **L1** is the heaviest (a carrier base-limb re-baselines every rotated
descriptor VK, exactly as the `revoked_root` flag-day did), and **L5** introduces a new root-VK anchor
shape the light client must be provisioned to accept (per the §6 verdict). L2/L3 add new leaf/descriptor
`vk_hash`es + enumerated-registry rows. **Batching guidance:** fold L1 with the other pending carrier
changes (nullifier segregation, open question 3) into ONE rotation epoch to avoid two full-cohort
re-baselines; L2/L3/L4/L5 can then ride that epoch or a following one. Sequence with the node, light
client, and registry — a straight replacement (greenfield, fail-closed), not a byte-identical cutover.

**VK-aggregation classification (the PLAN §5 "single most important unknown") — VERDICT: a coordinated
VK epoch, not additive.** Folding a shielded-transfer leaf into the committed turn introduces a **new
root-VK anchor shape** that the light client, node, and registry must be jointly provisioned to accept.
Verified from the actual aggregation code. The subtlety is that "descriptor-agnostic" is true of the fold
*mechanism* but false of the committed root VK *value*:

- **Mechanism is agnostic (nothing to enumerate).** The single merge primitive
  `merge_two_segment_proofs` (`circuit-prove/src/ivc_turn_chain.rs:4089`, drained by `aggregate_tree`
  `:5205`, `aggregate_tree_streaming`, `merge_pool`) reconstructs each child's AIRs from the proof
  metadata and reads each child's preprocessed commitment **out of the child proof**
  (`left.stark_common.preprocessed.commitment`, `:4696-4717`) — there is **no `match` on descriptor name,
  no admissible-VK list, no committed VK set inside the fold circuit.** Any well-formed leaf folds.
- **But the committed root VK transitively binds every leaf's identity.** The child's VK-core is baked as
  an **op-list constant**, not a public input: `pin_preprocessed_commit` does
  `circuit.alloc_const(val, "VK-identity pin")` + `connect` (fork `plonky3-recursion/.../verifier/batch_stark.rs:244-246`).
  That constant "lives in every node's op-list up to the root, so the root VK pin transitively certifies
  the whole tree's leaf identity" (`ivc_turn_chain_rotated.rs:1189`; module doc `ivc_turn_chain.rs:171-183`).
  `recursion_vk_fingerprint` hashes the preprocessed commitment among the root shape
  (`plonky3_recursion_impl.rs:711-778`). The anchor scope is stated authoritatively
  (`ivc_turn_chain.rs:1876-1879`): the fingerprint varies with tree structure **and leaf trace heights**;
  *"a client accepting several window shapes holds one anchor per shape."* A shielded-transfer leaf has a
  distinct wrapped-leaf shape, so any chain folding it yields a root fingerprint no existing anchor matches.
- **Admission is an enumerated registry SET, not a committed registry root.** The descriptor set is
  enforced by iterating committed TSVs at host admission (`verify_descriptor_participant` /
  `rotated_descriptor_selector` over `WIDE_REGISTRY_STAGED_TSV`, `joint_turn_aggregation.rs:1365-1438`;
  `admit_welded_leg`, `ivc_turn_chain.rs:2359-2405`) and at the SDK light client (`verify_full_turn_bound`
  requires binding **exactly one** cohort descriptor and pins `vk_hash = blake3(descriptor_json)`,
  `sdk/src/full_turn_proof.rs:4490-4549`). There is no Merkle registry-root in the turn PI; adding a
  descriptor moves an **enumerated set**, not a single committed root.

**The precise, non-overstated reading (important):** existing shapes' anchors are **unchanged** — an old
Transfer-only chain still verifies under its old anchor; this is **not** a rotation that invalidates prior
proofs. What a shielded descriptor does is **introduce a new-never-seen root-VK shape** that must be
trust-distributed. So L5 is a **coordinated, VK-affecting rollout ("VK epoch")** in the repo's own terms
(`docs/deos/VK-EPOCH-PLAN-2026-07-05.md`; `ivc_turn_chain.rs:2423,2537`), not a silent additive change.
Truly additive folding (turn VK untouched for the new shape too) would require the **not-yet-fireable
"universal-fold" normalization** (`VK-EPOCH-PLAN-2026-07-05.md:52` — "the seven-carrier universal-fold big
bang is NOT fireable"); under today's code it is a flag-day. Also required: a new (compile-forced) fold
arm — `mint_rotated_turn_leaf` has no wildcard (`ivc_turn_chain.rs:3506-3509`, "the wave must decide its
fold branch") — and provisioning the new leaf `vk_hash` + registry rows to the enumerators above.

---

## 7. Open architectural questions (honest)

1. **The value on-ramp.** There is no `Shield`/`Deshield` effect (§1.4). If the pool is to be funded, a
   shield effect (cleartext note → hiding shielded commitment) must append to `note_shielded` **and**
   conserve (a cleartext value burned equals a hidden value minted, provable without revealing the hidden
   value beyond a range). If the pool is closed (shielded-in, shielded-out only), the genesis of the first
   shielded note is undefined. **Resolve before L4** — L4's append is only half the lifecycle.

2. **One committed shielded tree encoding — the deepest sub-decision.** The spend membership gadget proves
   an **arity-4 plain Merkle** tree; the substrate append proves a **depth-32 linked AAFI IMT**. R1 needs
   **one** committed encoding for both membership and append. Options: (a) keep arity-4 plain Merkle as the
   committed tree and give the append a plain-Merkle grow-gate (append-at-index soundness argued
   separately); (b) migrate the spend membership to the AAFI IMT (which natively supports append-at-free-
   index and non-membership/freshness, like the nullifier set), re-authoring the membership gadget. (b) is
   cleaner for append soundness and unifies with the substrate; (a) is less circuit churn. This is the
   central unresolved encoding choice under R1.

3. **Shielded nullifier segregation.** Shielded nullifiers currently share `note_nullifiers.root8()`
   (domain-separated, `apply.rs:28`, `:1808`). Keep sharing, or segregate into a `shielded_nullifier_root`?
   The placeholder flags segregation as Stage-B/D work. Decide alongside L1 (both are carrier changes;
   batching them saves a flag-day).

4. **L5 is a VK epoch, RESOLVED** (§6 verdict) — the fold mechanism is descriptor-agnostic but the
   committed root VK transitively binds every leaf's identity (`alloc_const` op-list pin), so a shielded
   leaf introduces a new root-VK anchor the light client must be provisioned to accept. This is a
   coordinated flag-day, not additive (though existing anchors are untouched — not a rotation). The only
   way to make it truly additive is the not-yet-fireable universal-fold normalization. No residual unknown
   here; the open decision is whether to accept the flag-day now or wait for universal-fold.

5. **Residuals `pedTwoGen` / range cap** (§4) — out of scope for tree reconciliation, but they bound how
   strong the #17 claim may be stated: mint closed in-AIR, conservation over a curve abstraction, large
   amounts on a non-TCB Bulletproof.

---

## Summary

The shielded membership tree and the committed accumulator are three-way different (population, width,
structure+leaf), and the committed leaf carries a **cleartext value** a shielded note must hide — so
"pin `merkle_root` to the committed root" is impossible until a **committed shielded-note accumulator
exists**. That accumulator (R1: a fourth ledger set of hiding leaves, a new rotation base limb, an in-AIR
append grow-gate) is the redesign's foundational, privacy-preserving state change. The circuit half —
`shieldedSpendDesc`'s in-AIR `piROOT≡piCOMMITTED` pin (#15), `shieldedValueLinkDesc` (#16),
`shieldedWideValueLinkDesc` (#17) — is **already proven in Lean and merely unrouted**; its
`NoteAccumulatorCR` hypothesis is exactly what R1 discharges in reality. "Route through the apex" (R3) is
the light-client-visibility endgame **layered on R1**, not a substitute — the apex's kernel block is
synthetic and binds nothing committed on its own. The staged lanes (L0 accumulator → L1 carrier flag-day →
L2 append gate → L3 emit-wire → L4 route → L5 fold) name their VK-epochs. The PLAN's flagged "single most
important unknown" is **resolved**: the turn fold is descriptor-agnostic in mechanism but the committed
root VK transitively binds every leaf's identity, so there are **two coordinated VK epochs** — L1 (a
carrier base limb re-baselines the whole rotated cohort, precedented by `revoked_root`) and L5 (a new
root-VK anchor shape for the folded shielded leaf) — not a silent additive change (existing anchors are
untouched, so neither is a rotation). The honest open questions are the value on-ramp, the single
committed tree encoding, and nullifier segregation (batch it into L1's epoch).
