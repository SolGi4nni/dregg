# EffectVM IR Extension — Side-Table State Binding (ADDITIVE design)

> Read-only design. Drives implementation **after** the ~48-effect emission swarm drains.
> Closes the `needs IR extension` / `IR-BLOCKED` / `*_not_witnessed_*` flags raised across
> `Dregg2/Circuit/Emit/EffectVmEmit*.lean`. **No code is edited by this doc.**

## TL;DR verdict

- **Column budget:** the 96-column aux block of the running 186-wide prover is **fully claimed**
  (state-inters, custom-count, sealing bits, sovereign/federation/owner commits, and 60 balance
  range-bit cols). There are **no free aux columns** for new persistent root columns. BUT we do **not
  need new persistent columns** — the side-table roots live in the **existing `state.fields[0..7]`
  cells** (the running prover *already* mirrors `swiss_table_root = fields[4]` and
  `refcount_table_root = fields[3]` there), and those field cells are *already absorbed* into
  `state_commit` by GROUP-4. So the binding extension is **ADDITIVE and width-neutral (186 stays
  186)**: it is a **column-assignment convention + per-effect root-update gates + universe-A spec
  obligations**, not a layout change.
- **Hash-site scheme:** GROUP-4 already binds every `fields[i]` into `state_commit`. Tampering any
  side-table mirror cell ⇒ its `fields[i]` differs ⇒ `inter2`/`inter3` differ ⇒ `state_commit`
  differs ⇒ last-row `pi_binding state_commit == PI[NEW_COMMIT]` UNSAT under Poseidon2 CR. The
  anti-ghost tooth **already extends to side-state the moment the side-table root lands in a
  `fields[i]` cell**. The one *spare* GROUP-4 absorb slot (site3's 4th input, currently `.zero`) is
  reserved as the **overflow root slot** if we ever exceed 8 field cells.
- **New gate-kind:** **NOT needed for soundness** of insert/append/keyed-update (escrow, queue FIFO,
  delegation, sturdyref, commitment-set). The **root-equality + hash-site** mechanism already in the
  IR suffices: `new_root` is a `fields[i]` cell, the executor's set mutation determines it, GROUP-4
  binds it, and *membership/order/freshness* is discharged as a **universe-A `ActiveComponent.binds`
  obligation** (the model already does this via `ListCommit.listDigest` / `keyedDigest`). The **one
  genuine exception** is **NoteSpend non-membership (nullifier freshness)** — the `notenullifier`
  spec needs a *non-membership* witness, which the row cannot express with a single root cell. The
  minimal close there is the **existing per-row `notespend_nullifier` PI cross-binding** (the
  spend-proof PI certifies freshness off-AIR) PLUS a `nullifier_acc_root = fields[i]` append-binding;
  a heavy in-circuit Merkle non-membership gate is **explicitly avoided** unless an audit refutes the
  PI cross-binding.
- **Lean⟷Rust⟷prover sync:** **`lean_descriptor_air.rs` needs ZERO changes** — its hash-site
  interpreter is fully data-driven (loops `hash_sites`, appends one Poseidon2 aux block per site,
  binds each `digest_col < trace_width`). New side-table hash sites are just more list entries. The
  changes are **Lean-only** (per-effect emit files: add the root-update gate + reuse GROUP-4 sites)
  plus, for the running bespoke `effect_vm/air.rs`, the side-table mirror cells are **already
  written** (swiss/refcount) — escrow/queue/deleg/commitment mirrors get the same one-line
  `fields[i]` assignment pattern in trace-gen. **No `EffectVmEmit.lean` struct change.**

---

## 1. GATHERED FLAGS — complete IR-extension flag list

Source: grep over `Dregg2/Circuit/Emit/EffectVmEmit*.lean` (committed). Effect → side-table → what
the per-row circuit currently can NOT bind.

| Effect (emit file) | Side-table touched | Flag text / theorem | What's unbound |
|---|---|---|---|
| `createEscrow` (`EffectVmEmitCreateEscrow.lean:30`) | `escrows` list | "needs IR extension: an escrows-list-root column (a 15th data column…)" | escrow record append |
| `createCommittedEscrow` (`…CreateCommittedEscrow.lean:40`) | `escrows` list | "needs IR extension: (1) an escrows-list-root column…" | committed-escrow append (+ value-commit, out of VM scope) |
| `refundEscrow` (`…RefundEscrow.lean:32`) | `escrows` | "needs IR extension: an escrows-list-root column (a 15th data column…)" | escrow removal |
| `releaseEscrow` (`…ReleaseEscrow.lean:33`) | `escrows` | "needs IR extension: an escrows-list-root column…" | escrow removal + recipient credit |
| `bridgeLockA` (`…BridgeLockA.lean:32`) | `escrows` (bridge-park) | "needs IR extension: an escrows-list-root column…" | bridge-lock park append |
| `bridgeCancel` (`…BridgeCancel.lean:33`) | `escrows` | "needs IR extension: an escrows-list-root column…" | bridge-park removal |
| `bridgeFinalize` (`…BridgeFinalize.lean:33`) | `escrows` | "needs IR extension: an escrows-list-root column…" | bridge resolution |
| `refreshDelegation` (`…RefreshDelegation.lean:4,300,307`) | `delegations` map | thm `delegations_not_witnessed_by_capRoot` — "a `delegations_root` column + hash-site would…" | delegation epoch bump |
| `revokeDelegation` (`…RevokeDelegation.lean:28`) | `delegations`/caps | "IR GAP — needs IR extension: cap-root hash-site (inherited)" | delegation snapshot invalidation |
| `delegate` (`…Delegate.lean:33`) | caps c-list | "IR GAP — needs IR extension: cap-root hash-site (inherited)" | cap_root is abstract `Injective D`, not concrete Poseidon2 site |
| `delegateAtten` (`…DelegateAtten.lean:28`) | caps c-list | "IR GAP — needs IR extension: cap-root hash-site (inherited)" | attenuated cap install |
| `attenuateA` (`…AttenuateA.lean:38`) | caps c-list | "IR GAP — needs IR extension: cap-root hash-site" | cap_root scalar, no concrete site |
| `introduce` (`…Introduce.lean:29`) | caps (recipient) | "IR GAP — needs IR extension: cap-root hash-site (inherited)" | recipient c-list update |
| `dropRef` (`…DropRef.lean:38`) | caps/refcount | "IR GAP — needs IR extension: cap-table hash-site (inherited from `attenuateA`)" | refcount/cap-table mutation |
| `seal` (`…Seal.lean:32`) | `sealedBoxes` store | "needs IR extension: a sealedBoxes-store-root column absorbed by a [new hash-site]" | sealed-box insert |
| `unseal` (`…Unseal.lean:30`) | caps table | "needs IR extension: a caps-table-root column absorbed by a new [hash-site]" | sealed-box open |
| `createSealPair` (`…CreateSealPair.lean:32`) | caps table | "needs IR extension: a caps-table-root column absorbed by a new [hash-site]" | brand-pair register |
| `queueAllocate` (`…QueueAllocate.lean:31`) | `queues` table | "needs IR extension: a queue-side-table-root column (a data column…)" — IR-BLOCKED for list leg | queue create |
| `queueEnqueue` (`…QueueEnqueue.lean:31`) | `queues` | "needs IR extension: (a) a queue-buffer-root column absorbed by a NEW merkle/list-accumulator [hash-site]" | FIFO append |
| `queueDequeue` (`…QueueDequeue.lean:30`) | `queues` | "needs IR extension: (a) a queue-buffer-root column absorbed by a NEW merkle/list-accumulator…" | FIFO head advance |
| `queueResize` (`…QueueResize.lean:31`) | `queues` | "needs IR extension: a queue-side-table-root column absorbed by a NEW merkle/list-accumulator…" — IR-BLOCKED for re-cap+occupancy leg | capacity change |
| `queuePipelineStep` (`…QueuePipelineStep.lean:33`) | `queues` (src+sink) | "needs IR extension: a queue-side-table-root column absorbed by a NEW merkle/list-accumulator…" — IR-BLOCKED for routing leg | cross-queue route |
| `queueAtomicTx` (`…QueueAtomicTx.lean:12,35,44`) | `queues`×N + `bal` + `escrows` | "THE FUNDAMENTAL IR MISMATCH … needs IR extension: a BATCH/SEQUENCE descriptor form (NOT a single `EffectVmDescriptor`)" — **IR-BLOCKED at per-effect level** | atomic multi-queue batch |
| `noteSpend` (`…NoteSpend.lean:33,48`) | `nullifiers` set | "needs IR extension: a nullifiers-accumulator-root column absorbed by [a hash-site]" **AND** "a Merkle/sorted-set NON-MEMBERSHIP gate-kind (freshness witness for `nf`)" | nullifier append **+ non-membership** |
| `noteCreate` (`…NoteCreate.lean:32`) | `commitments` set | "needs IR extension: a commitments-accumulator-root column (a 15th [data column]…)" | commitment append |
| `swissExport` (`…SwissExport.lean:47,…`) | `swiss` table | IR-BLOCKED (header) — guard + list-structure not in descriptor; SCALAR portion only | swiss entry create |
| `swissHandoff` (`…SwissHandoff.lean:35,151`) | `swiss`/handoff | IR-BLOCKED (header) | handoff routing |
| `swissDrop` (`…SwissDrop.lean:29,140`) | `swiss`/refcount | IR-BLOCKED (header) | swiss GC |
| `enliven` (`…Enliven.lean:30,144,326`) | `swiss` table | IR-BLOCKED (header) | swiss validate/route |
| `pipelinedSend` (`…PipelinedSend.lean:30,120`) | log/eventual | IR-BLOCKED (header) — log-receipt prepend | deferred dispatch |

**Off-row `frame-only` flags (a distinct class — NOT side-table-root, but stated for completeness):**
`createCell_offrow_unenforced` (`…CreateCell.lean:290`), `factory_offrow_unenforced`
(`…CreateCellFromFactory.lean:278`), `cellDestroy_offrow_unenforced` (`…CellDestroy.lean:221`),
`cellSeal_offrow_unenforced` (`…CellSeal.lean:203`), `refusal_offrow_unenforced`
(`…Refusal.lean:215`), `makeSovereign_offrow_unenforced` (`…MakeSovereign.lean:254`). These are
**passthrough/new-cell** rows whose intent is invariant under the *actor's* frozen state block; they
are closed by the *new cell's own* row (a separate trace row), not by a side-table root — out of
scope for this doc except where a side-table also moves.

**Distinct side-tables, deduped:** `escrows`, `delegations`, caps c-list (`caps`, **already** has
`cap_root` but as abstract `Injective D` not concrete site), `queues`, `swiss` (sturdyref) +
refcount, `nullifiers`, `commitments`, `sealedBoxes`. **= 8 side-tables.**

---

## 2. THE LAYOUT — confirmed facts

`Dregg2/Circuit/Emit/EffectVmEmit.lean` (§0) and `circuit/src/effect_vm/columns.rs`:

- **186 = 54 sel · 14 state_before · 8 param · 14 state_after · 96 aux.**
- State block (14): `bal_lo(0) · bal_hi(1) · nonce(2) · fields[0..7] (3..10) · cap_root(11) ·
  state_commit(12) · reserved(13)`.
- **GROUP-4 (`effect_vm/air.rs:2649-2698`, `EffectVmEmitTransfer.lean:133-163`):** 4 ordered H4 sites
  - `inter1 = H4(bal_lo, bal_hi, nonce, field[0])`  → aux[8]
  - `inter2 = H4(field[1], field[2], field[3], field[4])` → aux[9]
  - `inter3 = H4(field[5], field[6], field[7], cap_root)` → aux[10]
  - `state_commit = H4(inter1, inter2, inter3, **ZERO**)` → `state_after.state_commit`
  - **Every `fields[0..7]` and `cap_root` is ALREADY absorbed.** `reserved(13)` is absorbed by **no
    site** (the transfer-keystone `state.RESERVED` finding — it's the sealing-mask, bound elsewhere by
    the Stage-2 `RESERVED_BIT_*`/`RESERVED_MODE` aux gates, not GROUP-4).
- **AUX 96, fully claimed:** `8..10` inters · `11` custom-count-acc · `7` seal-pow2 · `12..20`
  reserved-bits+mode · `21..22` resize sign/mag · `23..27` sovereign-witness · `28..35`
  federation+owner · `36..65` new-bal-lo 30 bits · `66..95` new-bal-hi 30 bits. **`0..7` are the
  per-row selector-gated scratch** already used by `EnlivenRef`/`DropRef`/`ValidateHandoff` Merkle
  witnesses (`columns.rs:19-57`). **No persistent free aux.**
- **The running bespoke prover ALREADY mirrors two side-table roots into field cells**
  (`columns.rs:28-57`): `swiss_table_root = state.fields[4]`, `refcount_table_root = state.fields[3]`,
  with the 1-hop append-only Merkle chain enforced in aux[0,1,6,7] on `Enliven`/`DropRef` rows. **This
  is the proven pattern to generalize.**

---

## 3. DESIGN

### A. Side-table-root columns — **reuse `state.fields[0..7]`, width-neutral**

The economic state needs `bal_lo/bal_hi/nonce/cap_root/state_commit/reserved` (6 of 14) plus the 8
`fields[0..7]`. The 8 field cells are the **root-mirror budget**. Assign (extending the running
prover's existing `fields[3]=refcount`, `fields[4]=swiss`):

| Cell | Constant name (Lean `state` ns + `columns.rs::state`) | Side-table |
|---|---|---|
| `fields[0]` | `FIELD_BASE+0` (kept free / cell-domain field[0], absorbed by `inter1`) | — (general cell field) |
| `fields[1]` | `ESCROW_ROOT` | `escrows` list digest |
| `fields[2]` | `QUEUE_ROOT` | `queues` table digest |
| `fields[3]` | `REFCOUNT_ROOT` *(existing: refcount_table_root)* | refcount / dropRef |
| `fields[4]` | `STURDYREF_ROOT` *(existing: swiss_table_root)* | `swiss` table digest |
| `fields[5]` | `DELEG_ROOT` | `delegations` map digest |
| `fields[6]` | `NULLIFIER_ROOT` | `nullifiers` accumulator |
| `fields[7]` | `COMMIT_ROOT` | `commitments` accumulator |
| `cap_root(11)` | `CAP_ROOT` *(existing)* | caps c-list (already absorbed by `inter3`) |

`sealedBoxes` (Seal/Unseal/CreateSealPair) shares the **caps-table semantics** — the existing emit
files (`…Seal.lean`, `…Unseal.lean`, `…CreateSealPair.lean`) ask for a "caps-table-root" — so seal
pairs fold into **`CAP_ROOT`** (the c-list root) under a domain tag, *not* a new field cell. This
keeps the budget at exactly 8 fields + cap_root = 9 root carriers for 8 side-tables, with `field[0]`
free as a general cell-domain field.

**This is ADDITIVE:** the column *indices* don't move; `field[i]` is already a wire and already in
GROUP-4. The 40+ landed effect files and the transfer descriptor reference `state.FIELD_BASE+i` /
`saCol (FIELD_BASE+i)` — those offsets are **unchanged**. We are only fixing the *meaning* of cells
that today most effects leave in passthrough. No `EffectVmDescriptor`/`EffectVmEmit.lean` struct
change; no 186→N width change.

> **Overflow contingency.** If a future side-table can't share a cell (9th distinct root), the spare
> capacity is **site3's 4th absorb input** (currently `.zero` at `EffectVmEmitTransfer.lean:159` /
> `air.rs:2694`). Replacing that `ZERO` with a 9th root cell (a new aux column, say `aux[…]` —
> requires reclaiming one balance-bit col or +1 width) absorbs it into `state_commit` directly. **Not
> needed now** (8 cells cover the 8 side-tables); flagged as the single minimal width-touch if ever
> required, blast radius = 1 GROUP-4 site input + 1 trace-gen assignment + universe-A spec.

### B. Hash-sites — **GROUP-4 already absorbs the root cells; anti-ghost extends for free**

No new hash-site *mechanism* is needed for the field-cell roots, because GROUP-4 site1 (`inter2`
absorbs `field[1..4]`) and site2 (`inter3` absorbs `field[5..7]`) **already** fold every field cell
into `state_commit`:

```
ESCROW_ROOT  = field[1] ─┐
QUEUE_ROOT   = field[2]  ├─ inter2 = H4(f1,f2,f3,f4) ─┐
REFCOUNT     = field[3]  │                            │
STURDYREF    = field[4] ─┘                            ├─ state_commit = H4(inter1,inter2,inter3,0)
DELEG_ROOT   = field[5] ─┐                            │        │
NULLIFIER    = field[6]  ├─ inter3 = H4(f5,f6,f7,cap) ┘        │
COMMIT_ROOT  = field[7] ─┘                                     │
                                                  last-row pin: state_commit == PI[NEW_COMMIT]
```

**Anti-ghost tooth (already proven shape, `EffectVmEmitTransferSound.lean`):** tamper any
`side_table` → honest digest `field[i]` changes → `inter{2|3}` changes (Poseidon2) → `state_commit`
changes → last-row `pi_binding state_commit == PI[NEW_COMMIT]` is UNSAT under Poseidon2 collision-
resistance. **The moment an effect writes its real side-table root into `state_after.field[i]`, the
GROUP-4 site enforces it.** The per-effect emit file needs only:

1. a **root-update gate** `field[i]_after = update(field[i]_before, element)` — see §C;
2. **passthrough** on the *other* root cells (the existing frame gate already pins
   `field[j]_after == field[j]_before` for untouched `j`).

No new `VmHashSite` for the roots themselves. (Optional: a *per-effect* H2 site
`new_root = H2(old_root, leaf)` mirroring the existing `Enliven`/`DropRef` 1-hop chain when the
update is an append — this **already** fits the IR's `VmHashSite` with `arity:=2`, and the
interpreter handles arity 2/4 today, `lean_descriptor_air.rs:1129`.)

### C. Membership / update gate-kind — **existing kinds suffice; ONE narrow exception**

For each mutation class, the minimal mechanism:

- **Append (escrow create, queue enqueue, commitment insert, sealedBox insert):**
  `new_root = H2(old_root, leaf)`, an **append-only accumulator**. Expressible **today**: a
  `VmGate` pinning `field[i]_after == aux[k]` where `aux[k]` is an `arity:2` `VmHashSite` over
  `[ .col (sbCol (FIELD_BASE+i)), .col leaf_aux ]`. **This is exactly the running
  `Enliven`/`DropRef` chain** (`air.rs:1592-1752`). **No new gate-kind.** Membership/well-formedness
  of the *leaf* is the **universe-A `ActiveComponent.binds` obligation** (`EffectCommit2.lean:113-124`,
  `listComponent` digest = `ListCommit.listDigest`).
- **Removal (escrow refund/release, queue dequeue, bridge cancel):** the executor recomputes the new
  list digest; the row pins `field[i]_after == aux[k]` to the recomputed root. Because the digest is
  **order/content-sensitive** (`listDigest` sponge), an honest removal is the *only* preimage —
  binding-soundness is the universe-A `binds`/`encodes` pair on the `escrows`/`queues`
  `ActiveComponent`. **No new gate-kind.** (We do **not** prove removal *in-circuit*; we bind the
  *resulting root*, and the spec obligation certifies the root corresponds to an honest removal — the
  same projection-vs-soundness boundary the v2 framework already draws.)
- **Keyed update (delegation epoch, refcount decrement, refresh):** `keyedComponent`
  (`EffectCommit2.lean:154-162`, `keyedDigest (KL k) cN S`) — root over a `Finset κ` of keyed leaves.
  Row pins `field[i]_after` to the recomputed keyed digest. **No new gate-kind.**
- **FIFO order (queue):** the `queues` digest is over `(head, tail, buffer)` so **order is intrinsic
  to the digest** — a reordered queue has a different `QUEUE_ROOT`. The `queuefifocore.lean` spec's
  `binds` carries the FIFO-order obligation. **No new gate-kind**; the root-equality + universe-A
  spec is the FIFO enforcement.
- **NON-MEMBERSHIP (nullifier freshness — the ONE genuine exception):**
  `noteSpend` must prove `nf ∉ nullifiers` *before* appending. A single root cell cannot express
  "`nf` is absent". The **minimal close** (prefer over a heavy in-circuit Merkle/sorted-set
  non-membership gate):
  - keep the **existing `notespend_nullifier` per-row PI cross-binding** (`air.rs:1069-1093`):
    `param[NULLIFIER] == PI[NOTESPEND_NULLIFIER]`, where the **spend binding-proof** (a *separate*
    recursively-verified proof) certifies `nf` fresh against the spent note's authenticated set —
    freshness is enforced by *that* proof's own circuit, cross-bound by PI;
  - add `NULLIFIER_ROOT = field[6]` **append** (`new = H2(old, nf)`) so the *post-state* set is bound
    into `state_commit` (closing the `…NoteSpend.lean:33` accumulator-root ask);
  - the `notenullifier.lean` `ActiveComponent.binds` carries "append of a *fresh* `nf`" as the spec
    obligation.
  **A dedicated in-circuit non-membership `VmConstraint` kind is NOT added** unless a UC/soundness
  audit shows the PI cross-binding is forgeable (then the minimal addition is a *sorted-set
  neighbour-pair* gate: two leaves `lo < nf < hi` adjacent in the sorted accumulator — a `VmGate`
  triple, still **no new `VmConstraint` constructor**, just three algebraic gates + one `arity:2`
  site). Flag for the crypto-first dependency order, not this swarm.

**Verdict C: the four existing `VmConstraint` kinds (`gate`/`transition`/`boundary`/`piBinding`) +
the existing `VmHashSite` (arity 2/4) are SUFFICIENT for all 8 side-tables. No new gate-kind.**

### D. Lean ⟷ Rust ⟷ prover sync — **what actually changes**

| Layer | Change | Additive? |
|---|---|---|
| `EffectVmEmit.lean` (the IR struct) | **NONE.** No new field on `EffectVmDescriptor`, no new `VmConstraint`/`HashInput`/`VmHashSite` constructor. (Optionally add named `def ESCROW_ROOT : Nat := FIELD_BASE+1` … convenience constants in the `state` ns — pure aliases, no semantics.) | ✅ trivially |
| Per-effect `EffectVmEmit*.lean` (the 30 IR-BLOCKED files) | Add (1) a root-update `VmGate` on the owning `field[i]`, (2) optionally one `arity:2` append `VmHashSite`, (3) the universe-A `binds`/`encodes` link to the effect's `ActiveComponent`. Replace the `IR-BLOCKED`/`not_witnessed` theorem with a `*_root_witnessed` positive theorem. | ✅ per-file, no shared change |
| `lean_descriptor_air.rs` (generic interpreter) | **NONE.** Hash-site loop is data-driven (`:1424-1437`): appends one Poseidon2 aux block per site, binds `digest_col`, arbitrary arity 2/4 (`:1129`), bounds checked vs `trace_width` (`:1031-1054`). New sites = more JSON array entries; the FULL air width auto-grows (`air_width`, `:978`). | ✅ zero-change |
| `effect_vm/air.rs` (bespoke running prover) | Trace-gen: write the real `escrows/queues/deleg/nullifier/commitment` digest into `state_after.field[i]` on the owning rows — the **same one-line pattern** already used for `swiss=field[4]`/`refcount=field[3]` (`air.rs:1592-1752`). GROUP-4 (`:2649-2698`) is UNCHANGED — it already absorbs all field cells. Per-effect 1-hop append gate mirrors the existing Enliven/DropRef block. | ✅ per-effect trace-gen, GROUP-4 untouched |
| `effect_vm/pi.rs` | **NONE required** (state_commit already binds all roots transitively). *Optional* per-table PI root mirror (like `APPROVED_HANDOFFS_BASE`) only if an effect needs to expose a root to an off-AIR verifier. | ✅ optional |
| 186-col prover width | **UNCHANGED.** Root cells are existing `field` columns; per-effect append sites add their Poseidon2 aux blocks via the generic interpreter's auto-grow (already how transfer's 4 GROUP-4 sites are laid out). | ✅ |

**The running 186-col prover needs NO width change.** The only structural Rust touch is the
**generic interpreter requires nothing**, and the **bespoke air's trace-gen** gets per-effect
`field[i]` digest writes (additive, mirrors landed swiss/refcount code).

### E. Per-blocked-effect close plan

| Effect | Root cell | Update gate | Site | Spec obligation (universe-A) |
|---|---|---|---|---|
| `createEscrow` / `createCommittedEscrow` | `ESCROW_ROOT=field[1]` | `field[1]' = H2(field[1], escrow_leaf)` | `arity:2` append | `escrowholdingcreate`/`escrowcommitted` `binds` |
| `refundEscrow` / `releaseEscrow` | `ESCROW_ROOT` | `field[1]' = recomputed listDigest` | (root-equality) | `escrowholdingrefund`/`…release` `binds`/`encodes` |
| `bridgeLockA` / `bridgeCancel` / `bridgeFinalize` | `ESCROW_ROOT` (bridge-park) | append / recompute | `arity:2` / eq | `bridgeoutbound{lock,cancel,finalize}` `binds` |
| `queueAllocate` / `queueEnqueue` / `queueDequeue` / `queueResize` / `queuePipelineStep` | `QUEUE_ROOT=field[2]` | `field[2]' = recomputed queue digest` (order-sensitive) | eq (+ `arity:2` for enqueue) | `queuefifocore`/`queuepipeline*` `binds` (FIFO order intrinsic) |
| `queueAtomicTx` | `QUEUE_ROOT` (+`bal`+`ESCROW_ROOT`) | **multi-component** — see note | eq×N | `queueatomictx` `binds` — **still IR-BLOCKED as a single descriptor; close via the BATCH form (below)** |
| `refreshDelegation` / `revokeDelegation` | `DELEG_ROOT=field[5]` | `field[5]' = keyedDigest update` | eq | `refreshdelegation` `binds` (replaces `delegations_not_witnessed_by_capRoot`) |
| `delegate` / `delegateAtten` / `attenuateA` / `introduce` / `dropRef` | `CAP_ROOT(11)` (+ `REFCOUNT=field[3]` for dropRef) | **make `cap_root` a CONCRETE Poseidon2 site** (today abstract `Injective D`) — `cap_root' = H2(cap_root, cap_leaf)` | `arity:2` append (already absorbed by `inter3`) | `authority{attenuation,revocation,unattenuated}` `binds` — **closes the "cap-root hash-site" gap** |
| `seal` / `unseal` / `createSealPair` | `CAP_ROOT` (sealedBox shares c-list root, domain-tagged) | `cap_root' = H2(cap_root, seal_leaf)` | `arity:2` | `sealboxoperations`/`sealpaircreation` `binds` |
| `noteSpend` | `NULLIFIER_ROOT=field[6]` | `field[6]' = H2(field[6], nf)` **append** + keep `notespend_nullifier` PI cross-bind | `arity:2` + PI | `notenullifier` `binds` (**non-membership = spend-proof PI obligation**, §C) |
| `noteCreate` | `COMMIT_ROOT=field[7]` | `field[7]' = H2(field[7], commitment)` | `arity:2` | `notecommitment` `binds` |
| `swissExport` / `enliven` / `swissDrop` / `swissHandoff` | `STURDYREF_ROOT=field[4]` (+`REFCOUNT=field[3]`) | **already** the running 1-hop chain (`air.rs:1592-1752`) — port the Lean gate to mirror | `arity:2` | `swiss{export,enliven,drop,handoff,frame}` `binds` |
| `pipelinedSend` | log hash (not a side-table root) | log-receipt prepend → `LH` surface | (out of GROUP-4; `Surface2.LH`) | `queuepipelinedsend` `binds` |

**`queueAtomicTx` remains genuinely IR-BLOCKED at the single-`EffectVmDescriptor` granularity**
(`…QueueAtomicTx.lean:12-44`): it touches N queues + bal + escrows in one atomic step. Its close is
**not** a new column but a **BATCH/SEQUENCE descriptor** — a *list* of `EffectVmDescriptor`s chained
by `transition` continuity (`next.state_before == this.state_after`), which the IR **already
supports** (the `transition` kind, `EffectVmEmit.lean:160`). So: emit the atomic-tx as a
**sub-sequence of single-effect rows** whose `state_commit` chains, with a boundary pin tying the
combined old/new roots (the `ATOMIC_TX_COMBINED_OLD/NEW_ROOT` params already exist,
`columns.rs:561-564`). **No IR struct change — a higher-level descriptor *composition*, deferred to
the batch-emission step.**

### F. Stray / suspected-duplicate file cleanup list

Scanned `Dregg2/Circuit/Emit/` (52 `.lean` files at audit time — the swarm is writing live).

- **No real open-hole/`admit`/axiom leaks found.** The only textual matches in the emit files are
  prose (axiom-hygiene notes) and `#assert_axioms`; no open holes in any emit file.
- **`EffectVmEmitBridgeLock.lean` does NOT exist** — only **`EffectVmEmitBridgeLockA.lean`** (24 KB,
  canonical). The non-`A` name surfaced once in a directory listing early in this session but is
  **absent now** (the swarm removed/renamed it mid-session). **No BridgeLock/BridgeLockA dupe to
  purge** — confirm `EffectVmEmitBridgeLock.lean` stays absent in the aggregate-verify; if it
  reappears as a 0-line/stub, purge it (the `A` file is the real one).
- **`EffectVmEmitBridge.lean`** (336 lines) is a **DISTINCT** file: the "faithful-encoding bridge for
  the TRANSFER row" (a transfer-encoding helper), **NOT** a bridge-effect emit. Keep — but the name
  collides semantically with the bridge-*effect* family (`BridgeLockA`/`BridgeCancel`/
  `BridgeFinalize`/`BridgeMint`). **Suspected-confusing name, not a dupe** — flag for a rename to
  `EffectVmEmitTransferEncoding.lean` to avoid swarm confusion; do NOT delete.
- **Transfer trio** `EffectVmEmitTransfer.lean` / `…TransferSound.lean` / `…TransferUnify.lean` are
  **three distinct, load-bearing** layers (descriptor / full-state-soundness keystone / universe-A
  collapse). **Not dupes — keep all three.**
- **Delegate pair** `EffectVmEmitDelegate.lean` (unattenuated) / `…DelegateAtten.lean` (attenuated)
  are **distinct effects** (`delegate` vs `delegateAttenA`). **Not dupes.**
- **Action for aggregate-verify:** confirm `EffectVmEmitBridgeLock.lean` (non-A) and any 0-line
  `EffectVmEmit*` stub does not reappear; if a file fails to elaborate or is import-orphaned (not
  reachable from the Emit root), purge it there. No file currently identified as broken.

---

## Appendix — why this is the right altitude (not a quick-fix)

The side-table roots are bound into `state_commit` **transitively through the existing GROUP-4
Poseidon2 tree**, so the anti-ghost guarantee the transfer keystone proves
(`EffectVmEmitTransferSound.lean`) **lifts to side-state with no new trust assumption** — exactly the
3-corner triangle the coverage memos demand (independent declarative eSpec ⟸ executor⟺spec ∧
circuit⟺spec, the circuit side pinned by an injective state commitment). The universe-A
`ActiveComponent.binds`/`encodes` (`EffectCommit2.lean`) is the *already-built* injective-digest
portal for each list/keyed table; this design only **routes its root into a field cell GROUP-4
already hashes**, rather than inventing a parallel binding. The single real soundness frontier —
nullifier **non-membership** — is named, scoped to the crypto-first dependency order, and given a
minimal sorted-neighbour fallback that still adds **no new `VmConstraint` constructor**.
