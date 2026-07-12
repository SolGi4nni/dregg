# CANONICAL-HEAP-TREE-INVESTIGATION — is the deployed heap FORCED sorted, or ASSUMED?

**Read-only soundness investigation, grounded at HEAD (2026-07-12); every claim cites file:line.**
Target: the ONE genuine residual of config-evolution kernel soundness named in
`CONFIG-EVOLUTION-SOUNDNESS-SCOPE.md` §Layer-1.3 — `MapReconcileFamily`'s leading premise
`∃ h, SortedKeys h ∧ |h| = 2^dep ∧ mapRoot h = pre-root` (the committed heap tree must be a VALID
SORTED CANONICAL heap). Question: does the DEPLOYED memory AIR force whole-tree sortedness (so the
premise discharges into `{Poseidon2SpongeCR, FRI-LDT}`), or is it only ASSUMED (a forgeable absence
→ double-spend)?

**VERDICT: B — a genuine maintained-invariant floor, currently carried as a knowledge-extraction
ASSUMPTION (NOT verdict A, NOT dischargeable from a single accepting trace).** The concrete
forge-absence witness (verdict-C shape) is real and is the sole reason the sortedness invariant is
load-bearing; the honest chain prevents it by a TRUSTED PRODUCER, not by an in-circuit gate.

---

## 1. What the deployed memory AIR FORCES (grounded)

The per-turn `Ir2Air::MapOps` AIR (`circuit/src/descriptor_ir2.rs`, `MapKind` at `:478`) and its Lean
modeler `MapOpsColumnLayout.ReconcileGatesAt` (`:577`) force, per fired map-op row, under the single
named `Poseidon2SpongeCR` floor:

* **Path binding** — a sibling-path recompute of the opened leaf to the committed pre-root BINDS the
  leaf to the committed leaf vector at the path position (`pathRecompute_binds_updates`,
  `MapOpsColumnLayout.lean:296`; `mapNode_injective` peeled per level). A forged opening is a
  Poseidon2 collision. ✓
* **`.absent` gap** — TWO membership paths at ADJACENT leaf positions under the same root, with the
  positions reconstructed IN-CIRCUIT from the direction bits (`position = Σ dirᵢ·2ⁱ`; adjacency is
  one linear constraint, `descriptor_ir2.rs:1745-1751`) and enforced `idx_upper == idx_lower + 1`
  (the dedicated `membership_adjacency_air.rs:29-33` closes the "wide-bracket" forge —
  `AIR-SOUNDNESS-AUDIT.md` finding #2), plus the key range gates `key_lo < k < key_hi`
  (`ReconcileGatesAt .absent`, `MapOpsColumnLayout.lean:587`). ✓
* **`.write` / `.insert`** — old leaf opens to pre-root and the SAME siblings recompute the new leaf
  to the post-root column, so a frozen/forged post-root is a collision (`writesToMerkle_of_path`,
  `:534`; the `toy_frozen_insert_bites` tooth, `:937`). ✓

## 2. What it does NOT force — whole-tree sortedness

`ReconcileGatesAt` bundles the AIR gates WITH a leading existential `∃ h : FeltHeap, SortedKeys h ∧
h.length = 2^dep ∧ mapRoot hash dep h = root` (`MapOpsColumnLayout.lean:578-580`). The `SortedKeys h`
conjunct is **never derived from the gates** — it is part of the premise `MapReconcileModelOk`
(`:663`) that the assembler `airAccept_forces_satisfied2_of_modelers` (`:725`) CARRIES as the `hmap`
hypothesis, NOT produced from `MainAirAcceptF`. Grep confirms there is **no whole-tree adjacent-key
range gate** on the accumulator absence path: nothing checks `key(pos i) < key(pos i+1)` for all `i`
across the committed `2^16`-leaf tree (the only `key`-comparison gate is the per-row hi/lo split
`KEY_LO_BITS`, `descriptor_ir2.rs:3625`, i.e. the `key_lo < k < key_hi` bracket — a LOCAL check).

The two `SortedTreeNonMembership{,Heap8}.lean` files are the same picture from the abstract side: both
reduce non-membership to `SpineCommits{,8}` (`SortedTreeNonMembership.lean:90`,
`Heap8:65`), whose `sorted : Sorted spine` field is an **explicit structure hypothesis** — the header
is candid: *"`SpineCommits` is a HYPOTHESIS, never an axiom"* (`:51`). They PROVE the combinatorial
bracketing (`excludesSpine`, `sorted_gap_excludes` — unconditional) and the insert algebra
(`sortedInsert_sorted`, `update_sound`), but they do NOT prove sortedness is forced in-circuit; they
CONSUME it.

**The honest crux (`MEMORY-LEGS-SCOPE.md:117-126`, confirmed):** *"the denotation quantifies over the
whole sorted 2^16-leaf heap … while the AIR opens a sibling path. Path-recompute ⟹
whole-heap-existential is a knowledge-extraction-shaped argument (under CR a path pins only the
path)."* So `SortedKeys h` is **not extractable from a single accepting trace → verdict A is FALSE.**

## 3. The concrete forge-absence exploit (verdict-C shape — the reason it is load-bearing)

Non-membership completeness needs GLOBAL sortedness: the gap at positions `p, p+1` excludes `k` only
because sorted order forbids any other position from holding a key in `(key_p, key_{p+1})`. Drop
sortedness and an adversarial prover forges an absence:

* Commit a heap whose leaf vector is `[MIN, (20,·), (30,·), (25, n), MAX, pad…]` — the real,
  already-spent nullifier `n` sits at address 25 placed **out of sorted order at position 3**.
  Compute its genuine `node8` Merkle root; put it in the `heap_root` column.
* To double-spend `n` (`addr(n)=25`): prove `n` ABSENT via the `.absent` gap using positions 1,2
  (keys 20 and 30 — adjacent ✓, both open to the genuine root ✓, `20 < 25 < 30` ✓). Every deployed
  gate ACCEPTS.
* → `n` "proven fresh" → the noteSpend insert re-spends the nullifier already present at position 3.
  **Double-spend** (identically: forge a fresh commitment / cell-creation).

Nothing in the per-turn circuit checks that position 3's key (25) violates sorted order relative to
positions 1–2 — there is no whole-tree ordering gate. This is exactly the vault/cap-open/transfer
wrap-gap class.

## 4. Why the DEPLOYED honest system does not exhibit it — the maintained invariant (verdict B)

The committed root is not free: it is CHAINED. `heap_root` starts at the sorted genesis
`empty_heap_root_8()` = fold of `{SENTINEL_MIN, SENTINEL_MAX}` (`heap_root.rs:566-599`, sorted by
construction), and frame continuity pins each turn's pre-root to the previous post-root
(`CircuitSoundness.lean:279`). The honest PRODUCER only ever emits sorted roots:
`CanonicalHeapTree{,8}::new` SORTS + dedups by `addr` (`heap_root.rs:162-163, 690-691`);
`apply_value_update` holds `addr` fixed → sorted-preserving (`:424`); `insert_witness` splices the
fresh key into its sorted position and rebuilds (`:375-409`). The chain invariant is therefore:

> **`SortedKeys(genesis)` (trivial) ∧ ∀ turn, `SortedKeys(pre) ⟹ SortedKeys(post)`.**

Value-update preserves it (Lean `heapSet_eq_listSet`, `MapOpsColumnLayout.lean:440`); a sorted insert
preserves it (`sortedInsert_sorted`, `SortedTreeNonMembership.lean:301`). So **every root the honest
chain reaches is a sorted-canonical tree** — a genuine committed-input invariant maintained
inductively across turns, not derivable from one accepting trace.

## 5. The sharp edge — the induction is NOT self-enforced by the per-turn gates

The invariant is currently kept by a **trusted producer**, not by the circuit. The deployed
`MapKind::Insert` gate is modeled (`ReconcileGatesAt .insert`, `MapOpsColumnLayout.lean:601`)
IDENTICALLY to `.write`: old leaf `(key,vOld)` and new leaf `(key,value)` at the **same** `steps` — an
in-place position overwrite, NOT a sorted splice that shifts positions; freshness is bolted on by a
paired `.absent` (header note, `MapOpsColumnLayout.lean:70-71`) which itself PRESUPPOSES sortedness (a
mild circularity). So the deployed insert gate does **not force sorted placement of a fresh key** →
the induction step of §4 is not discharged in-circuit → under a fully-adversarial prover (the proper
SNARK soundness model, where prover/executor/cell are one adversary) a non-sorted reachable root is
not ruled out by the gates. This is why the status is an **ASSUMPTION**, matching
`CONFIG-EVOLUTION-SOUNDNESS-SCOPE.md`'s classification "GENUINE-ASSUMPTION (knowledge-extraction) — the
ONE fact beyond the allowed modulus."

## 6. The discharge path (the fix — same shape as the wrap-class fixes)

The machinery to FORCE sortedness already exists: `whole_image_fold.rs` reconstructs a map root as a
**sorted-`MapKind::Insert` chain from the empty root** (`:30-66`), pinning the published root to the
fold of exactly the declared cells (`mapRoot_injective` no-extra-cells tooth). Chained from the sorted
empty root, a chain of sorted inserts yields a provably sorted tree — so routing the accumulator
absence path through the boundary-anchored regime (the STAGED umem cohort that REPLACES per-map
reconciliation, `MEMORY-LEGS-SCOPE.md:128`; `nullifier_fresh_sound` is already Merkle-path-free when
the boundary is pinned, `descriptor_ir2.rs:452,1676`) discharges `CanonicalHeapTree` into
`{Poseidon2SpongeCR, FRI-LDT}`. Concretely, close it by EITHER:

* **(i) in-circuit whole-tree sortedness** — weld the `whole_image_fold` sorted-insert-chain (or a
  per-turn adjacent-key range gate `key(pos i) < key(pos i+1)`) onto the accumulator roots, so
  `SortedKeys h` is FORCED per accepting trace; OR
* **(ii) discharge the §4 chain invariant** — strengthen the deployed `.insert` gate to FORCE sorted
  placement (a genuine sorted splice, not a position overwrite), then prove
  `SortedKeys(pre) ⟹ SortedKeys(post)` per gate and chain from the sorted genesis.

Both are one shared lane for all 7 mapOp effects (the scope doc's option (i)); (i) is the
LogUpColumnLayout-parity bar, (ii) the chain-invariant bar.

## 7. Bottom line

`CanonicalHeapTree` sortedness is **NOT dischargeable from a single accepting trace** (verdict A
false — no whole-tree ordering gate exists on the accumulator path). It is a **genuine
maintained-invariant floor** (verdict B): the honest chain keeps the heap sorted-canonical via a
sorted genesis + a sorted producer at every turn. But it is **currently carried as a
knowledge-extraction ASSUMPTION**, NOT self-enforced by the per-turn insert gate — so under the
adversarial-prover model it is a REAL residual of the same class as the wrap gaps, with a concrete
forge-absence → double-spend witness (§3). The discharge (§6) reuses the already-realized
`whole_image_fold` sorted-insert-chain. **No Lean was edited: sortedness is not provable-forced from
acceptance, so verdict A could not honestly be claimed.**

---

## RECONCILIATION (2026-07-12) — the CARRIER-CENSUS "5th-candidate" tension, decided at the gate

**The tension.** (a) The first investigation read the per-turn `MapKind::Insert` as a free-path
recompute with no sorted splice (→ real gap). (b) `heap_root.rs:39` names "genuine in-circuit
sorted-tree update/insert gates" and `whole_image_fold.rs:165` a "sorted-insert chain pinned at both
ends." IF either forced sorted placement on the DEPLOYED per-turn insert, the Lean `SortedKeys`
hypothesis would be a FAITHFULNESS DEBT (discharge in Lean), not a gap.

**The deciding read — the deployed per-turn insert gate does NOT force sorted placement.** The
per-turn grow-gate (`nullifierInsertOp`/`commitmentsInsertOp`/`cellsInsertOp`) is the `Ir2Air::MapOps`
arm for `op ∈ {read=0, write=1, insert=3}` (`descriptor_ir2.rs:2724-2851`). On an insert row the
entire gate is:

* dir bits binary-checked (`descriptor_ir2.rs:2742-2744`);
* the `not_insert` selector (`:2751`) GATES OFF the old-leaf and old-root opening on an insert
  (`is_real * not_insert`, `:2802,2831`) — so the pre-root is not even opened by the insert leg;
* the NEW leaf `hash[key,value]` is absorbed and folded up the **prover-supplied `(sib, dir)` path**
  through `node8` to `new_root8` (`:2817-2845`), with `new_root8` bound to the post-root column.

**There is NO adjacency and NO key-range check on the insert path.** The `diff == 1` adjacency gate
(`:2882`) and the two `eval_lex_lt` gap checks `lo_addr < key < hi_addr` (`:2906-2925`) live ONLY in
the SEPARATE `Ir2Air::MapAbsent` arm (`:2854-2994`). The insert leg range-checks the new key against
NOTHING: a malicious prover picks any dir bits + any siblings, folds the fresh leaf to SOME root, and
commits it — a NON-sorted placement is accepted. (The prover-side `insert_witness` self-check
`w.new_root != new_root`, `descriptor_ir2.rs:4420`, is HONEST-producer code behind the `check` flag,
not an AIR constraint.)

**Tension (b) dissolves — neither doc-comment claims the deployed insert forces sortedness.**
`heap_root.rs:39` explicitly says the sorted-tree insert gates "**are the Phase-E lane**" — an
UNDEPLOYED future, not the live per-turn path. `whole_image_fold.rs:165`'s sorted-insert chain rides
the SAME non-forcing `MapKind::Insert`; its no-extra-cells soundness rests on `mapRoot_injective` +
the empty-root PI pin (`assert_empty_root_pin`) + the boundary-table `UMemOp::Read` binding — NOT on
each insert forcing sorted placement — and it is a cross-cell-READ construction, not the per-turn
nullifier/commitment/cells insert. So `heap_root.rs:39`'s "genuine sorted-tree gates" is a NAME for
future work; verified against what it CHECKS, the deployed insert checks no order.

**VERDICT: NOT a faithfulness debt. This is the REAL residual (verdict B stands).** The deployed
insert only path-recomputes; it does not force sorted placement (quote: `descriptor_ir2.rs:2817-2845`,
no range/adjacency, `not_insert` off-gating the pre-root). The Lean carrying `SortedKeys` /
`SpineCommits.sorted` as a HYPOTHESIS is therefore HONEST and correct — the Lean does NOT under-model
a forcing gate. **No Lean discharge was wired: wiring one would claim the gate forces sortedness (it
does not) and would launder the insecurity.**

**Induction status (§4, item 4).** Genesis IS in-circuit-sortable: the empty accumulator =
`empty_heap_root_8` (sentinels only, sorted by construction — a verifier-known constant, pinnable as
`whole_image_fold::assert_empty_root_pin` already does). Per-insert PRESERVATION
(`SortedKeys(pre) ⟹ SortedKeys(post)`) is **NOT in-circuit** — this is the decisive missing half. So
the chain invariant is kept by the TRUSTED PRODUCER (the generator always builds via
`CanonicalHeapTree8` + `insert_witness`), not by the gate.

**Is the double-spend witness live?** On the DEPLOYED HONEST prover: NO — the generator emits only
sorted roots, and the paired `.absent` freshness op (`nullifierFreshOp`) refuses a present nullifier
(`trace_rotated.rs:1447-1453`). Under the fully-adversarial SNARK-soundness model (prover = executor =
cell, one adversary): YES — an earlier `.insert` can commit a non-sorted root (free placement), then a
later `.absent` bracket at sorted-looking adjacent positions misses the out-of-order spent nullifier
(§3 witness `[MIN,20,30,25,MAX]`), and every deployed gate accepts → double-spend. Same class as the
vault/cap-open/transfer wrap gaps.

**THE FIX GATE (circuit, not Lean).** On every `.insert` row, add the `MapAbsent` adjacency+range
machinery: the `diff == 1` adjacency constraint + the two `eval_lex_lt` gap checks binding the
inserted key to a genuine sorted gap `lo < key < hi` at adjacent positions `p, p+1` of the PRE-root,
AND force the post-root to be the pre-tree with the leaf spliced at that gap (a sorted-splice re-hash,
not a free-path recompute). Chained from the sorted-genesis constant this makes preservation
in-circuit and discharges `CanonicalHeapTree` into `{Poseidon2SpongeCR, FRI-LDT}` (§6 option (ii)).
The `.absent`/`.insert` pairing already threads both ops on the same pre-root, so the adjacency
witness is present — the gate additions are local to the `Ir2Air::MapOps` insert leg.
