# Nullifier / Revocation Accumulator — Design (review-first, not implemented)

Status: PARTIALLY IMPLEMENTED (2026-07-07). The proven **accumulator gate** is landed green
(`metatheory/Dregg2/Exec/NullifierAccumulator.lean`, `#assert_axioms`-clean, non-vacuous — see §9).
The **VK-epoch flip** (wiring the roots into `RecordKernelState` + the commitment/frame apex) is NOT
done — it is ember-gated and coordinated with the parked umem VK epoch. §10 records a key finding that
revises this doc's staging, and gives the exact flag-day touch-list. The circuit side already deploys
most of the machinery this design points at (the reuse story, §5).

## 1. Current cost — the two-cost problem, grounded

Two gates carry a whole append-only set in kernel state and check membership by list scan:

- **The double-spend gate.** `RecordKernelState.nullifiers : List Nat := []`
  (`metatheory/Dregg2/Exec/RecordKernel.lean:317`). The spend step
  `noteSpendNullifier` (`RecordKernel.lean:934`) does:

  ```
  def noteSpendNullifier (k : RecordKernelState) (nf : Nat) : Option RecordKernelState :=
    if nf ∈ k.nullifiers then none
    else some { k with nullifiers := nf :: k.nullifiers }
  ```

  `nf ∈ k.nullifiers` is a `List.Mem` scan — **O(#history)** per spend — and the whole set
  is a field of `RecordKernelState`, so it is carried in state and (at the FFI/wire boundary)
  crosses **per turn**.

- **The revocation gate.** `RecordKernelState.revoked : List Nat := []`
  (`RecordKernel.lean:325`), consumed by `revocationGate`
  (`metatheory/Dregg2/Exec/FullForestAuth.lean:481`):

  ```
  def revocationGate … (s) : Bool := !(s.kernel.revoked.contains na.credNul)
  ```

  `List.contains` — again **O(#revoked)** per authorization, and the whole `revoked` set rides
  in state.

**The two costs are distinct** and a `HashSet` fixes only the first:

1. **The check cost** — O(n) membership scan. A `HashSet`/`RBSet` in state would make this
   O(1)/O(log n). But…
2. **The wire cost** — the *entire* set is a component of the state that crosses the FFI
   boundary and is committed each turn. A `HashSet` does **not** shrink the wire: you still
   move n elements. At millions of spends this is fatal regardless of the check structure.

The real fix carries **only a root** in state (O(1) wire) and moves the membership evidence
**with the transaction that needs it** (the spend/auth supplies a proof), not with every turn.
That is an **accumulator**.

Note the shape asymmetry that rules out the naive answer: this is a **spent-set** that needs
**insert + non-membership** (prove `nf` is *absent*, then add it). A plain append-only MMR
(`metatheory/Dregg2/Lightclient/MMR.lean`) proves **membership** ("this receipt is in the log")
and is complete-by-density; it cannot prove **non-membership**, so it is the wrong structure for
a double-spend gate. It stays the right structure for the receipt index — different job.

## 2. The accumulator structure — SMT vs indexed-Merkle-tree

The candidate structures for an insert + non-membership set commitment:

| | Sparse Merkle Tree (SMT) | Indexed / sorted Merkle tree |
|---|---|---|
| Non-membership | leaf at `H(key)` is empty (default-hash subtree) | predecessor/successor **gap bracketing**: two adjacent present leaves `lo < key < hi` ⇒ absent |
| Depth / path cost | fixed **256** (one level per key-bit); every op opens a 256-long path | **`log₂ n`** over *present* leaves only (deployed depth **16**, `circuit/src/heap_root.rs:54`) |
| Insert | write one leaf at `H(key)` | splice at sorted position; update predecessor's "next" link + add leaf |
| Hash calls / proof size | ~256 Poseidon2 per op | ~16 (present-count-bounded), Aztec-style |
| Emptiness proof | default-subtree hash (needs a "zero" convention) | bracketing by two real neighbors (no zero convention) |

**Pick: the sorted / indexed Merkle tree** (Aztec's nullifier-tree family), for three reasons:

1. **The tree already chose it.** The deployed circuit accumulator writes are *already*
   sorted-tree fresh-key inserts, not 256-bit SMT writes:
   `circuit/src/heap_root.rs::CanonicalHeapTree8::insert_witness` (`heap_root.rs:763`), and the
   Lean model `SortedTreeNonMembershipHeap8` proves non-membership by exactly the
   predecessor/successor bracketing (`GapOpen8.inner`,
   `metatheory/Dregg2/Circuit/SortedTreeNonMembershipHeap8.lean:93`). A 256-depth SMT would be a
   *new, heavier* structure to build, prove, and deploy; the indexed tree is what exists.

2. **Cost.** The gate proof is `O(log₂ present)` ≈ 16 Poseidon2 compressions, not 256. For a
   spent-set that only ever grows, the present-leaf count is exactly the spent count, and the
   sorted tree's path is over that, not over a fixed 256-bit key space.

3. **No zero-hash convention.** Non-membership is two real membership openings plus an ordering
   check — the honest combinatorial core (`sorted_gap_excludes`,
   `metatheory/Dregg2/Crypto/NonMembership.lean:68`), which is already fully proved with no crypto
   residue. The SMT's "this subtree is all-default" is an extra convention to bind.

**The hash: Poseidon2**, to match the circuit. The deployed node hash is the wide 8-felt
Poseidon2 compression carried by `Heap8Scheme` / `CanonicalHeapTree8`; its collision-resistance
is the single named floor `Poseidon2SpongeCR` (`metatheory/Dregg2/Circuit/Poseidon2Binding`),
the same floor the cap-root / heap / MMR advances already ride. The root is an 8-felt `Digest8`
(~248-bit binding), **not** the legacy single ~31-bit felt of the deprecated
`circuit/src/note_spending_air.rs` (see its own deprecation notice at `note_spending_air.rs:3`).

### The algebraic-accumulator alternative (present, and why it is not the base structure)

There is a *second* accumulator already in the tree: the rational-function batch accumulator
`Acc = P(α) = ∏(α − h_j)`, per-row non-membership via `v = P(h) ≠ 0`
(`metatheory/Dregg2/Circuit/Emit/AccumulatorNonRevocationEmit.lean`,
`circuit/src/dsl/accumulator.rs`, `circuit/src/accumulator_types.rs`). It is excellent for
**batch non-revocation of a delegation chain** (prove k ancestors all absent in one AIR, cheap
arithmetic, no Poseidon2) but it is **not an insertable set commitment**: `Acc = ∏(α−h_j)` is a
Schwartz–Zippel snapshot at a Fiat–Shamir challenge `α`, recomputed per proof; it does not model
"insert `nf` and rebind the root that the next spend reads." So it is a **companion**
(read-side, batch) not the base structure. See §7 for how it rides alongside.

## 3. State + wire change

Replace the two `List Nat` fields with two `Digest8` roots:

```
-- RecordKernel.lean:317, :325  (BEFORE)
nullifiers : List Nat := []
revoked    : List Nat := []

-- (AFTER)
nullifierRoot : Digest8 := emptyRoot   -- Poseidon2 sorted-tree root of the spent-set
revokedRoot   : Digest8 := emptyRoot   -- Poseidon2 sorted-tree root of the revoked-set
```

- **State / wire cost drops to O(1):** one fixed-width 8-felt root per set, independent of the
  spent count. That is the whole point — the wire carries the *commitment*, never the set.
- **Who supplies the witness.** The kernel no longer holds the set, so the *transaction*
  supplies the evidence. The spend/auth carries a **non-membership witness** for `nf`:
  the predecessor/successor leaves + their Merkle openings + the ordering (`GapOpen8`,
  `SortedTreeNonMembershipHeap8.lean`). For the insert it *additionally* carries the
  **post-insert opening**: the spliced leaf's membership path in the rebuilt tree reaching the
  new root (`insert_witness` → `HeapInsertWitness8`, `heap_root.rs:763`).
- **Who tracks the tree.** The client (spender / delegator, or a service it queries) maintains
  the full sorted tree off-ledger and produces witnesses; the kernel holds only the root and
  *verifies* O(log n). This is the standard accumulator split: prover holds the set, verifier
  holds the commitment. For a spent-set the "current tree" is public (it is the double-spend
  frontier), so any node or a light indexing service can serve witnesses — the witness is not
  secret (only the *value* behind a nullifier is; the nullifier itself is public once spent).
- **Model-level ghost set.** For the Lean theorems we keep a *specification-only* `keysOf8 root`
  — the set of keys the root commits to (`SortedTreeNonMembershipHeap8.lean:73`). It is a `Set ℤ`
  derived from the root, **not** a carried field: it never crosses the wire, it exists only to
  *state* the invariants. `SpineCommits8` binds `keysOf8 root` to the concrete sorted spine the
  witnesses open against.

## 4. Proof obligations — the theorems that must still hold

The current guarantees are three theorems over the list model. Each maps to a sorted-tree
statement, and the sorted-tree lemmas needed are **already proven**.

### (a) `note_no_double_spend` — a spent nullifier cannot be re-spent

- **Now** (`RecordKernel.lean:942`): `nf ∈ k.nullifiers → noteSpendNullifier k nf = none`.
- **Accumulator form.** The spend takes a non-membership witness `g : GapOpen8 S8 nullifierRoot nf`.
  The step fails-closed unless the witness verifies *against the committed root*. Soundness:

  > `nonMembership_sound8` (`SortedTreeNonMembershipHeap8.lean:149`): a `GapOpen8` valid against
  > the spine the root commits to ⟹ `nf ∉ keysOf8 S8 root`.

  Contrapositive is exactly the guarantee: **if `nf ∈ keysOf8 root` (already spent), NO valid
  `GapOpen8` exists** — the bracketing neighbors cannot straddle a present key (`sorted_gap_excludes`
  / `GapOpen8.excludesSpine`, both fully proved, no crypto). So the gate cannot pass ⇒ fail-closed.
  The list `if nf ∈ …` scan is replaced by "verify the witness"; the *rejection* is now forced by
  the combinatorics of a sorted tree instead of by a scan.

### (b) `note_spend_inserts` — a committed spend actually adds `nf`

- **Now** (`RecordKernel.lean:950`): `noteSpendNullifier k nf = some k' → nf ∈ k'.nullifiers`.
- **Accumulator form.** A committed spend advances `nullifierRoot → nullifierRoot'` under the
  insert witness. The insert is faithful:

  > `update_sound8` (`SortedTreeNonMembershipHeap8.lean:164`): given the old root commits `spine`,
  > `nf` fresh over the old root, and the new root commits `sortedInsert nf spine`, then
  > `∀ y, y ∈ keysOf8 newRoot ↔ (y = nf ∨ y ∈ keysOf8 oldRoot)`.

  The `y = nf` disjunct is `note_spend_inserts`: the new committed set is exactly the old set
  **plus** `nf`, in sorted order (`update_preserves_sorted8` keeps it a sorted tree for the next
  op). The composed anti-replay `note_spend_then_reject` (`RecordKernel.lean:958`) then falls out:
  after the spend `nf ∈ keysOf8 nullifierRoot'`, so by (a) no valid non-membership witness exists
  on `nullifierRoot'` ⇒ a second spend of `nf` fails-closed.

### (c) NEW soundness — you cannot forge a non-membership proof for an already-spent nullifier

This is the obligation the list model got *for free* (the set was in trusted state) and the
accumulator must earn, because the witness is now **adversary-supplied**. Statement:

> For all roots `root`, keys `nf`, and witnesses `g`: if `nf ∈ keysOf8 root` then there is no
> `g : GapOpen8 S8 root nf` with `g.coversSpine spine` for the committed `spine`.

Provable in two layers:

1. **Combinatorial layer (unconditional, already proved).** `GapOpen8.excludesSpine`
   (`SortedTreeNonMembershipHeap8.lean:183`, `#assert_axioms`-clean) proves a valid gap open
   forces `nf ∉ spine`. Since `keysOf8 root = spine` under `SpineCommits8`
   (`keysOf8_eq_spine`, `:76`), a present `nf` admits no valid open. **No forgery at the
   combinatorial level** — the ordering constraints are contradictory for a present key.

2. **Binding layer (the one crypto floor).** The above assumes the witness's neighbor openings
   really reach `root` — i.e. the prover cannot open a *different* spine than the one `root`
   commits. That is Poseidon2 collision-resistance: `SpineCommits8` binds `root ↔ spine`, and its
   realizability rests on `Poseidon2SpongeCR` (the deployed `Heap8Scheme.node8` carrier). A forged
   witness would be a Poseidon2 collision. This is the **single named floor** the whole circuit
   soundness apex already rests on — no *new* trust is introduced.

So (c) = `nonMembership_sound8` read as a security claim: **accept ⇒ absent**, contrapositively
**present ⇒ no accepting witness**, modulo one Poseidon2-CR floor already in the TCB.

### Non-vacuity (do not launder)

Each theorem must be witnessed TRUE-and-FALSE. `NonMembership.lean` already carries the pattern
(`nonmembership_sound_teeth`, `:412`: a genuine member is *not* a non-member — the relation is
two-valued). The sorted-tree port must reproduce it: a concrete tree where `nf` present ⇒ the gate
rejects (mutation canary), matching the deployed `accumulator_nonrev_audit_extra.rs` /
`accumulator_nonrev_golden.json` canaries that already bite the analogous teeth.

## 5. Reuse — the census (most of this exists)

This design is a **weld**, not a greenfield build. The circuit + assurance layers already have:

- **Sorted-tree non-membership (combinatorial core).**
  `metatheory/Dregg2/Crypto/NonMembership.lean` — `sorted_gap_excludes` (`:68`), the
  `Satisfies ↔ NonMember` bridge (`:199`), the STARK `extractable` carrier + derived
  `nonmembership_verify_sound` (`:262`), dial-wired at `acceptanceOnly`. Fully proved, crypto
  residue only in `extractable`.
- **The 8-felt heap-lane twin** (the deployed geometry). `SortedTreeNonMembershipHeap8.lean`:
  `keysOf8`, `GapOpen8`, `nonMembership_sound8`, `update_sound8`,
  `update_preserves_sorted8` — the exact insert + non-membership lemmas §4 needs, over the
  deployed `Heap8Scheme` node hash.
- **The deployed insert.** `circuit/src/heap_root.rs::CanonicalHeapTree8::insert_witness`
  (`:763`) → `HeapInsertWitness8`; `insert_witness_recomputes_post_root` (`:940`) is the Rust
  faithfulness test.
- **The emit-gated AIR twins.** `AccumulatorOpenEmit.lean` (the after-spine for the three
  dedicated accumulator roots — `nullifier_root` @ limb 26, `commitments_root` @ 27,
  `cells_root` @ 0) and `AccumulatorInsertEmit.lean` (`accumInsert_writesTo8`: non-membership +
  after-membership + spine bindings FORCE the faithful 8-felt insert). These are the
  circuit-side realization of exactly this design.
- **Poseidon2** — the single shared hash/floor (`Poseidon2SpongeCR`), same as cap-root / heap /
  MMR / receipt advances.
- **The algebraic batch companion** — `AccumulatorNonRevocationEmit.lean` +
  `accumulator_types.rs` (`compute_accumulator`, `derive_alpha`, `AccumulatorNonRevocationWitness`)
  for cheap batch non-revocation of a delegation chain.
- **MMR** stays the receipt-index structure (`MMR.lean`) — *not* reused here (membership, not
  non-membership) but named so the boundary is explicit.

**What is genuinely greenfield (the gap this design closes):** the **executor state** still
carries `List Nat` (`RecordKernel.lean:317,325`). The circuit commits `nullifier_root` @ limb 26,
but the Lean *executor model* has not been migrated off the list to the root. This design is the
plan to close that seam: swap the two fields to `Digest8`, re-express `noteSpendNullifier` /
`revocationGate` as witness-verifying steps, and re-derive (a)/(b)/(c) from the already-proven
`nonMembership_sound8` / `update_sound8`. It **subsumes** the censused sorted-tree
set-move soundness (memory: "sorted-tree set-moves are Poseidon2/Compress-CR-forced in-circuit,
forgery UNSAT", `project-circuit-soundness-apex.md`) by making the *executor* carry the same root
the circuit already forces.

## 6. Migration — one design, both gates

The double-spend gate and the revocation gate are the **identical shape**: a monotone-growing
key set with insert (spend / revoke) and a per-transaction check (non-membership for a fresh
spend; membership-or-not for an auth). So:

- **One parametric sorted-tree accumulator** instantiated twice: `nullifierRoot` and
  `revokedRoot`. `AccumulatorOpenEmit` already instantiates the *same* after-spine three times
  (nullifier / commitments / cells) parametric over `(groupCol, keyCol, valueCol)` — a fourth
  (`revoked`) is the same instantiation, no new spine proof.
- **Directionality.** The double-spend gate *requires non-membership* (fail-closed if present).
  The revocation gate is the dual: it *requires membership-absence to pass* — `revocationGate`
  passes iff `credNul ∉ revokedRoot`. Same `nonMembership_sound8` lemma, opposite gate polarity:
  spend inserts on success; revoke inserts on the `cap_revoke` step and the auth gate reads
  non-membership. `gateOK_revoked_fails` (`FullForestAuth.lean:495`) is re-expressed: a credential
  whose `credNul ∈ keysOf8 revokedRoot` admits no non-membership witness ⇒ the gate's
  non-membership leg cannot pass ⇒ `gateOK = false`. The teeth theorem stays non-vacuous by the
  same argument as §4(c).
- **Staged, additive, then cutover** (the project's migration doctrine). The `Digest8` roots were
  *added* to `RecordKernelState` the same way `nullifiers` / `commitments` / `bal` were added
  (all `:= default`), so old proofs that ignore them are unaffected. Land the root fields + the
  witness-verifying step defs beside the list defs; prove (a)/(b)/(c) over the roots; flip the
  gate to read the root; retire the `List Nat` fields. The list→root flip is a **VK epoch** on the
  circuit side (the deployed default reads the inline map-op lane; flipping to the after-spine is
  the descriptor swap `AccumulatorOpenEmit`'s header calls out) — coordinate with the parked umem
  VK epoch, do not flip piecemeal.

## 7. Circuit integration — the non-membership proof rides the spend's STARK

The spend already carries a STARK spending proof + nullifier derivation (the §8 CryptoPortal:
`nullifier = poseidon2(commitment ‖ spending_key ‖ creation_nonce)`, the note-spend AIR /
`SCHEMA_NOTE_SPEND` in `circuit/src/effect_action_air.rs`). The non-membership proof does **not**
become a separate proof — it is **another set of columns/constraints in the same AIR**, so one
STARK covers derivation **and** the accumulator update:

1. **Derivation → key.** The existing AIR computes `nf` from the witnessed
   `(commitment, spending_key, creation_nonce)` in-circuit (Poseidon2). That `nf` is the **key**
   fed to the accumulator columns — the *same* felt, so there is no cross-proof binding to forge
   (the nullifier the non-membership is proved for is the one the spend derives).
2. **Non-membership columns.** The predecessor/successor neighbor leaves + their Merkle openings
   + the ordering gadget (`lo < nf < hi`) — the deployed `GapOpen8` witness columns, opened
   against `nullifierRoot` carried as a PI. This is the `AccumulatorInsertEmit` §(a) leg.
3. **Insert columns.** The spliced leaf's membership path in the rebuilt tree reaching
   `nullifierRoot'` (the AFTER root), also a PI — `AccumulatorInsertEmit` §(b)/(c) legs. The AIR
   binds `nullifierRoot` (before, PI) → `nullifierRoot'` (after, PI) as the state transition the
   kernel commits.
4. **One accept.** A single verifying STARK now witnesses: (i) the spender knows the key,
   (ii) `nf` was **absent** from the committed spent-set, (iii) the new root is the old set **plus
   `nf`**. The kernel does O(1) work: check the proof, swap `nullifierRoot ← nullifierRoot'`. No
   set crosses the wire; the PIs are two 8-felt roots + the derived nullifier.
5. **Batch companion.** Where a turn touches a *delegation chain* (k ancestors, revocation), the
   algebraic `AccumulatorNonRevocation` AIR (`AccumulatorNonRevocationEmit.lean`) proves all k
   non-revocations in one cheap arithmetic AIR against `revokedRoot`'s snapshot `Acc = ∏(α−h_j)` —
   riding *beside* the sorted-tree insert, not replacing it (the sorted tree is the insertable
   source of truth; the algebraic accumulator is a cheap read-side batch check).

The integration adds **no new trust boundary**: derivation + non-membership + insert all land in
one STARK over Poseidon2, and the only floor is `Poseidon2SpongeCR` (already in the apex TCB) plus
FRI/STARK extractability (already carried as `extractable`).

---

## Key decision points for review

1. **Structure: sorted/indexed Merkle tree (recommended) vs 256-depth SMT.** Recommendation is the
   indexed tree — it is what the circuit already deploys (`CanonicalHeapTree8`,
   `SortedTreeNonMembershipHeap8`), it is `O(log present)` ≈ depth-16 not 256, and its
   non-membership is the already-proved gap-bracketing with no zero-hash convention. The SMT's
   only edge is simpler insert logic (no predecessor relink) at the cost of a fixed 256-path and a
   new structure to build/prove. **Decision: confirm the indexed tree, or accept the SMT's heavier
   path for its simpler insert.**

2. **Who carries the witness.** Recommendation: the client / a public indexing service tracks the
   full sorted tree and produces `GapOpen8` + insert witnesses; the kernel holds only the root.
   The spent-set is public, so witness-serving is not a privacy leak (only note *values* are
   hidden, not the nullifiers). **Decision: is a client-side tree acceptable operationally, or is
   a bundled node-side witness service wanted at genesis?**

3. **Migration path / VK epoch.** The `Digest8` roots land additively (like `nullifiers`/`bal`
   did), (a)/(b)/(c) get re-proved over the roots from the existing `nonMembership_sound8` /
   `update_sound8`, then the gate flips list→root. The flip is VK-affecting on the deployed circuit
   (inline map-op lane → after-spine descriptor swap). **Decision: bundle this flip with the parked
   umem VK epoch (recommended — one flag-day), or run a dedicated nullifier-root epoch?**

4. **Two accumulators, one design — confirm the dual polarity.** Double-spend gate = require
   non-membership, insert on success. Revocation gate = require non-membership-to-pass, insert on
   `cap_revoke`. Same parametric sorted tree, instantiated for `nullifierRoot` and `revokedRoot`.
   **Decision: confirm both gates share the one accumulator (recommended), vs keeping revocation on
   the cheaper algebraic batch accumulator alone** (which does not support the persistent-insert
   root, only per-proof snapshots — so it cannot be the sole revocation source of truth).

---

## 9. Landed — the proven accumulator gate (`Dregg2/Exec/NullifierAccumulator.lean`)

The novel security content is implemented and green, over a standalone `NfAccState` (the two
`Digest8` roots — exactly the pair the VK flip lands in `RecordKernelState`). The three §4
obligations are re-derived from the already-proven Heap8 lemmas; nothing crypto is re-proved:

- **`witness_fresh`** — a valid `NfAccWitness` PROVES its key absent (`nonMembership_sound8`); the
  witness *earns* non-membership, it is not assumed.
- **(a)/(c) `present_no_witness`** — a key already committed by `root` admits NO valid witness
  (`IsEmpty (NfAccWitness …)`), the contrapositive of `nonMembership_sound8` + the unconditional
  `GapOpen8.excludesSpine`. This is the no-double-spend / non-forgeability keystone.
- **(b) `spend_inserts_root`** — the committed spend advances the root so `nf` is now present
  (`update_sound8` `y=nf` disjunct).
- **`spend_then_no_rewitness`** — composed anti-replay: after a spend, no second witness for the same
  `nf` exists.
- **`no_double_spend_root`** — the gate in state terms (`nf ∈ keysOf8 s.nullifierRoot ⇒ IsEmpty`).
- **Revocation dual `revoked_gate_fails`** — a revoked `credNul` admits no non-membership witness ⇒
  the revocation leg cannot pass. Same lemma, opposite polarity.

**Non-vacuity (two-valued, not laundered).** `witness_inhabited_of_bindings` is the TRUE pole (a fresh
key HAS a witness once the `compute_canonical_heap_root_8` bindings realize); `present_no_witness` is
the FALSE pole; plus decidable spine demos (25 bracketed-admissible, 20 present-refused, `sortedInsert`
grows by exactly the key / no-op on a present key). **`#assert_axioms`-clean** ⊆ {propext,
Classical.choice, Quot.sound}; `SpineCommits8` is the SOLE carrier (a hypothesis on the witness, the
one deployed Poseidon2/`Compress8CR` floor), never an axiom.

## 10. KEY FINDING — additive roots are NOT a separate cheap stage; field-add ≡ VK-epoch flip

This doc's §3/§6 framed the `Digest8`-root fields as a *cheap additive* step (land beside the lists,
old proofs unaffected) SEPARATE from the later VK-epoch flip. **That is wrong.** Verified empirically:
literally adding `nullifierRoot`/`revokedRoot` to `RecordKernelState` breaks the whole full-state
**frame** apex, because every full-state frame theorem *pins every kernel field* (that is their
anti-silent-mutation job), and honestly pinning the two new roots forces the rest-hash `RH` to
**absorb** them — which IS the VK-epoch commitment change. The field-add and the VK flip are ONE
change, not two stages:

- `Transfer.TransferSpec` / `recKExec_iff_spec` go red the moment the field lands (the `←` direction's
  `cases k'; subst …; rfl` leaves the new roots as free vars ⇒ the `↔` is *false* unless they are
  pinned) — confirmed by build.
- Pinning them in the CIRCUIT-side proof (`StateCommit`) can only come from the state hash, so
  `RestHashIffFrame` (`StateCommit.lean:229`) must gain the two clauses and `RH`/`frameDigest` must
  absorb the roots — a commitment-semantics (VK) change. (`nullifiers`/`bal` are already in
  `RestHashIffFrame` for exactly this reason — they paid the same tax when introduced.)
- The `RotatedKernelRefinement*` `fr*` **frame structures** (~29 files) each enumerate every field, so
  each needs a `frNullifierRoot`/`frRevokedRoot` field + every construction site updated.

Therefore the proofs are landed over `NfAccState` (§9), and the field-in-`RecordKernelState` is
deferred to the coordinated flag-day. **Do not fire it piecemeal.**

### VK-EPOCH TOUCH-LIST (the exact flag-day scope, for ember)

**A. Kernel state + gates**
- `metatheory/Dregg2/Exec/RecordKernel.lean` — add `nullifierRoot`/`revokedRoot : Digest8` to
  `RecordKernelState`; rewire `noteSpendNullifier` (`:934`) to consume `NfAccWitness` (verify → advance
  root) instead of the `nf ∈ k.nullifiers` scan; retire `nullifiers`/`revoked : List Nat` at cutover.
- `metatheory/Dregg2/Exec/FullForestAuth.lean` — `revocationGate` (`:481`) consumes a non-membership
  witness against `revokedRoot`; ripples to `gateOK` (`:486`), `execFullAGated` (`:515`), and the
  `NodeAuthC` payload (carry the witness).

**B. State commitment — RH must absorb the roots (the VK-affecting core)**
- `metatheory/Dregg2/Circuit/StateCommit.lean` — extend `RH`/`frameDigest` to absorb both roots;
  `RestHashIffFrame` (`:229`) +2 clauses; fix `transfer_circuit_full_sound` (`:524`),
  `recStateCommit_binds_kernel` (`:626`), `transfer_circuit_full_complete` (`:705`), and the 16→18
  destructures (`:485,:522,:616,:641,:659,:728`).

**C. Full-state frame specs (+2 clauses each, +2 proof arity)** — the `↔`-spec / `kernelFrame` family:
- `Transfer.lean` (`TransferSpec :360`, `recKExec_iff_spec :377` — verified-green exemplar, reverted),
  `EffectCommit.lean` (`kernelFrame :146` + consumers), `EffectCommit2.lean`, `EffectInstances2.lean`,
  `CommitmentCrossBind.lean`, `ClosureFloorReduce.lean`, `ClosureTransfer.lean`.
- `Dregg2/Circuit/Inst/*.lean` effect frames (~30): transfer, mintA, burnA, balanceA, spawnA,
  exerciseA, noteSpendA, noteCreateA, createCellA, createCellFromFactoryA, cellSealA, cellUnsealA,
  cellDestroyA, delegate, delegateAttenA, introduceA, attenuateA, revoke, revokeDelegationA,
  revokeDelegationFullA, refreshDelegationA, receiptArchiveLifecycleA, heapWriteA, bridgeMintA, …
- `Dregg2/Circuit/Spec/*.lean` frame specs (~30): balancemovement, notenullifier, authorityrevocation,
  cellstate{audit,log,permissions,vk,field,program,monotone}, notecommitment, …

**D. Frame STRUCTURES (add `frNullifierRoot`/`frRevokedRoot` + every construction site)** — ~29 files:
- `RotatedKernelRefinement.lean` (the `fr*` frame, `:259-273`), `RotatedKernelRefinementCapFamily.lean`
  (`KernelFrameExceptCaps :129`), …Notes, …NotesFresh, …Exercise, …IncNonce, …SetField, …MintBurn,
  …Attenuate, …Lifecycle, …CellSeal, …PermsVK, …Program, …Birth, …Misc; `CircuitCompletenessLifecycle`,
  `CircuitCompletenessSetInsert`; `TransferDecodeBridge`; `FloorsNonVacuousWave{,Birth,MiscNotes,
  PermsProgram,Lifecycle,Transfer}`.

**E. FFI / wire / seed**
- The kernel-state `@[export]` codec (`Dregg2/Crypto/UMemCodec.lean` + `exec-lean/src/lean_apply.rs`) —
  carry the two roots (replace the `List Nat` on the wire). FFI signature changes ⇒ rebuild the seed
  (`bootstrap.sh` on hbox) + spot-check a gate-ON spend still finalizes + the executor differential
  re-agrees.

**F. Circuit descriptor / VK**
- Descriptor swap the `AccumulatorOpenEmit` header calls out (inline map-op lane → after-spine) for
  `nullifier_root` @ limb 26 (+ a `revoked_root` instantiation); VK regeneration; land in the SAME
  flag-day as the parked umem VK epoch (design §6 — one flag-day, not piecemeal).

## 11. Stage E grounded — the runtime verifiers ALREADY EXIST (integration, not new crypto)

The Lean half is LANDED green + axiom-clean (§9 gate + the apex/cascade + the kernel gate-bridge
`Exec/NullifierAccumulatorKernelBridge.lean`: `noteSpendNullifierAcc` advances the committed
`nullifierRoot` via the proven `spendNullifierRoot`; the double-spend/anti-replay/revocation teeth
reduce to the banked lemmas through `toNfAccState`). The roots are FROZEN — no effect advances them
at runtime yet. Stage E makes them LIVE. Ground truth of the deployed pieces:

- `circuit/src/heap_root.rs:375` **`insert_witness(new_leaf) -> Option<HeapInsertWitness>`** — the
  deployed sorted-Merkle-heap insert: returns `None` for a present key (the fail-closed leg) or a
  witness carrying `{new_leaf, siblings, directions, old_root, new_root}`. THIS is the runtime twin of
  the Lean `NfAccWitness` (GapOpen8 non-membership + fresh-key insert); `compute_heap_root` /
  `compute_canonical_heap_root_8` is the root function `RestHashIffFrame` binds.
- `circuit/src/non_membership.rs` — `verify_accumulator_non_membership` / `prove_…` (the STARK
  RSA-accumulator flavor with an alpha challenge; the OTHER accumulator — used by revocation/suspension
  DSL, not the sorted-heap nullifier root). The nullifier root is the sorted-heap flavor.
- `cell/src/nullifier_set.rs` — the sorted-set `prove_non_membership` (binary-search neighbors) B18
  flags for incrementalization; the same sorted discipline the tree commits.

### TWO models — recommend MODEL 1 first (sound, kills the perf bomb, no wire-witness)

**Model 1 — executor-maintained sorted tree (the first cutover, RECOMMENDED).** The executor already
maintains the nullifier SET (today the `List`); swap it for the deployed `CanonicalHeapTree8` and on a
noteSpend call `insert_witness` → advance the kernel `nullifierRoot` to `witness.new_root` (fail-closed
when it returns `None` = present key). State stays executor-authoritative (O(n) memory) but per-op is
O(log n) — this KILLS the O(all-history) List scan (audit bomb #1/#2) AND makes the root live +
committed. NO wire-witness, NO effect-payload/NodeAuthC signature ripple. The Lean spec it matches is
`noteSpendNullifierAcc` (root advances) + `noteSpendNullifierAcc_no_double_spend` (present key ⇒ no
witness ⇒ `insert_witness` returns `None`). Cutover cost: `lean_apply.rs` noteSpend arm + a differential
test `advanced_root == compute_heap_root(set ∪ {nf})` at every step + Lean seed rebuild (executor binary
changes). This is the honest "make it live" minimal step.

**Model 2 — client-witnessed O(1) state (the follow-on refinement).** Retire the executor-side set;
the client carries the `HeapInsertWitness` on the wire (`UMemCodec.lean` + `lean_apply.rs` + the
NodeAuthC payload — the wide signature ripple), the executor VERIFIES it against the committed root and
advances. True O(1) state, set never crosses the wire — the original design intent (ember: "client-side
seems fine"). Soundness: a valid witness ⟹ `NfAccWitness` (so `present_no_witness` gives fail-closed);
the runtime verifier must be proven to match the Lean `NfAccWitness` acceptance (the E1 obligation).
Do AFTER Model 1 is deployed + stable — it is a strictly harder, wider change on the same committed root.

### Stage E work split (Model 1 first)
- **E1 (Lean, pure — green-checkable, no deploy risk):** if `noteSpendStmt`'s executor meaning is to
  advance the root, extend it (or add `noteSpendStmtAcc`) and prove the advance equals
  `noteSpendNullifierAcc`'s — reusing the bridge. Optional for Model 1 (the Rust executor is the
  authority; the Lean spec `noteSpendNullifierAcc` already exists) — needed for the in-circuit teeth.
- **E2 (Rust, deploy-affecting):** `lean_apply.rs` noteSpend arm maintains the `CanonicalHeapTree8`,
  advances `nullifierRoot`; differential test `advanced == compute_heap_root(set')`; retire the
  List-on-wire at cutover; rebuild the Lean seed on hbox; spot-check a gate-ON spend finalizes + the
  cross-platform executor differential re-agrees.
- **F (circuit/VK):** descriptor swap + VK regen (unchanged from §10.F).

## 12. Stage E RECON FINDING (B) — no executable Lean heap-root; the root is a trust-boundary fork

Grounded recon (isolated branch): the nullifier-accumulator model is purely ABSTRACT.
- `Heap8Scheme` (`DeployedHeapTree.lean:36`) is a hypothesis carrier: opaque field `chipAbsorb8 :
  List ℤ → Digest8` + CR hypothesis `chip8CR`. NO concrete instance exists in-tree (only mocks
  `refChipAbsorb8`/`badChipAbsorb8` for the cap non-vacuity lane).
- `Digest8 = Fin 8 → ℤ`; `NfAccWitness.newRoot` is a client-supplied FIELD; `spendNullifierRoot` is
  `{s with nullifierRoot := w.newRoot}` — it ASSIGNS the supplied root, never computes it. The bridge
  theorems (`noteSpendNullifierAcc_no_double_spend`, …) are sound but about the ABSTRACT witness
  relation; they do not constrain what a runtime root-computer emits.
- The ONLY executable root fold is RUST: `circuit/src/heap_root.rs` `compute_canonical_heap_root_8`
  (:529) + `CanonicalHeapTree8::insert_witness` (:763, `None` for a present key = fail-closed).

### The fork (ember's call — a trust-boundary, not a wiring, decision)
- **Path B (§11 Model-1 as written):** the trusted Rust root-computer in `lean_apply.rs` advances
  `nullifierRoot ← insert_witness.new_root`. Faster, deploy-affecting, BUT the committed root is
  produced by trusted Rust OUTSIDE the Lean-verified executor core (stage F's circuit re-verifies
  in-STARK, but the executor path does not). Erodes the verified-executor thesis.
- **Path A (RECOMMENDED — keeps the root in the verified core):** build the executable Lean heap-root
  via the ALREADY-ACCEPTED storage-in-lean `@[extern]`/`@[export]` precedent (`Dregg2/Storage/
  Deployed.lean`: `@[extern "dregg_poseidon2_2to1"] poseidon2Hash`, verified Lean logic over the real
  Rust Poseidon2 primitive, `@[export]` for Rust callback). Concrete `Heap8Scheme` calling the extern
  chip + an executable `CanonicalHeapTree8` Lean twin (sorted insert) + a refinement proof that the
  executable fold matches the abstract-scheme ops the banked lemmas use ⇒ the verified Lean `interp`
  itself advances the root. Same extern-Poseidon2-in-verified-core trust boundary the storage epoch
  ALREADY embraced (NOT a new TCB assumption) — coherent with the storage-in-lean north star. Larger
  greenfield; Lean-green + refinement-proved before any deploy.
