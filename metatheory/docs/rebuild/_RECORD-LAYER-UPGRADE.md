# Record-Layer Upgrade — the committed field MAP (read-only design pass)

> Drives an implementation wave. **No code edited by this doc.** Coordinates with
> `_IR-EXTENSION-DESIGN.md` (which proposed *stealing* user field cells for side-table roots —
> this doc FREES them) and `_POLICY-LANGUAGES-REFRESH.md` (a richer record enables richer
> predicates). Read those two alongside.

## TL;DR verdict

- **The wall is REAL and quantified (§A).** A cell has exactly **8** `FieldElement` slots
  (`cell/src/state.rs:11`, `STATE_SLOTS = 8`). They are contended **three ways**: (1) user app data
  (shipped apps already burn 5–8 of 8), (2) special-cased stores (`fields[7]`=seal commitment,
  `swiss_table_root`/`refcount_table_root` are *separate* named u32 roots already — `state.rs:78,84`),
  (3) the IR-extension's proposed f1–f7 side-table roots. The IR-extension plan would alias
  `ESCROW/QUEUE/DELEG/NULLIFIER/COMMIT_ROOT` onto `fields[1..7]` (`_IR-EXTENSION-DESIGN.md:138-143`),
  leaving apps **field[0] only**. `subscription` and `compartment-workflow-mandate` and
  `storage-gateway-mandate` **already overflow that** today. **This is the wall.**
- **The Lean record is ALREADY an unbounded name-keyed map.** `Exec/Value.lean:65` is
  `record : List (FieldName × Value)`; `Value.scalar`/`setField`/`balOf`/`SlotCaveat` are all
  **name-keyed**, never index-bounded. So the 8-cap is **purely a Rust `[FieldElement; 8]` + circuit
  8-column constraint** — NOT a Lean constraint. This is the leverage: the verified semantic core
  does not need to change shape; we make the Rust state-rep and the *circuit width* catch up to what
  Lean already proves over a map.
- **The fix (§B): a `fields_root` committed map.** Replace the fixed `[FieldElement; 8]` (Rust) /
  add a `fields_root` column (circuit) with a Poseidon2 **keyed accumulator** committing a
  `key → value` map. Apps get unlimited fields; the **circuit width stays fixed** (one root column);
  reads/writes are proven against the root by membership/update — **reusing the exact hash-site
  mechanism the side-table roots already use** (`_IR-EXTENSION-DESIGN.md §B/§C`). Backward compat
  via a **hybrid**: keep the proven `fields[0..7]` cells *as reserved low keys* `0..7` (the existing
  corpora index those), add the map for keys `≥ 8`.
- **Side-table roots get a DEDICATED home (§C).** This **reconciles** with `_IR-EXTENSION-DESIGN.md`:
  instead of stealing `fields[1..7]`, the side-table roots (escrow/queue/deleg/nullifier/commit/
  sturdyref) move into a **dedicated `roots` namespace** — either their own small fixed sub-block
  (a `[FieldElement; N_ROOTS]` parallel to `fields`) OR reserved high keys in a *separate*
  `system_root` accumulator. User fields and system roots never collide again.
- **Proof-repair (§D): most Lean proofs LIFT untouched** because the field model is already
  name-keyed. What breaks is concentrated in (1) the Rust `CellState` struct + its serde/commitment,
  (2) the **circuit** GROUP-4 hash tree (8 field columns → 1 root column), (3) the canonical
  commitment (`commitment.rs`). The Lean `recKExec_*` / `stateStepGuarded_*` / `setBalance_balOf`
  keystones are **field-name-indexed and lift verbatim** once `Value.scalar` over the map agrees
  with the old list-record on keys `0..7`.
- **Beachhead (§E): add `fields_root` ALONGSIDE the fixed fields** (hybrid, zero deletion), wire ONE
  app (`subscription`, the app that maxes out 8 slots) to read/write a key-`8` map field end-to-end
  with a membership proof, **old fixed-field proofs untouched**. Green + `#assert_axioms` clean.

---

## §A — THE SQUEEZE, QUANTIFIED

### A.1 How many fields exist (ground truth)

| Layer | Capacity | Source |
|---|---|---|
| Rust `CellState.fields` | **8** `FieldElement` (`[u8;32]`) | `cell/src/state.rs:11,47` (`STATE_SLOTS = 8`) |
| Rust per-field metadata | 8 × `FieldVisibility` + 8 × `Option<commitment>` | `state.rs:49,52` |
| Circuit state block | **8** field columns `fields[0..7]` = state cols `FIELD_BASE+0..7` = abs `3..10` | `EffectVmEmit.lean:66` (`FIELD_BASE=3`), `_IR-EXTENSION-DESIGN.md:104-108` |
| Lean `RecordCell` | **UNBOUNDED** name-keyed map `List (FieldName × Value)` | `Exec/Value.lean:65` |

The Lean/Rust/circuit are **already mismatched**: Lean is an unbounded map, Rust+circuit are an
8-array. The upgrade *closes* this mismatch in the capacity-increasing direction.

### A.2 Who uses which slot (the three-way contention, concrete)

**(1) User app data** — shipped starbridge-apps and their slot consumption:

| App | Slots used (index) | Free slots | Source |
|---|---|---|---|
| `subscription` | **0,1,2,3,4,5,6,7 — ALL 8** | **0** | `subscription/src/lib.rs:168-182` |
| `compartment-workflow-mandate` | 0,1,2,3,4 | 3 | `compartment-workflow-mandate/src/lib.rs:92-104` |
| `storage-gateway-mandate` | 0,1,2,3,4,5,6 | 1 | `storage-gateway-mandate/src/lib.rs:91-109` |
| `governed-namespace` | 0,1,2,3,4,5 (6,7 *reserved for future*) | 2 (already earmarked) | `governed-namespace/src/lib.rs:178-212` |
| `identity` | 2,3,4,5 | (0,1,6,7) | `identity/src/lib.rs:129-154` |
| `nameservice` | 2,3,4,5,6 | (0,1,7) | `nameservice/src/lib.rs:104-131` |

`governed-namespace` literally documents the wall (`src/lib.rs:54`): *"Slots 6 and 7 are reserved
(`Immutable`-by-default) for future …"* — a `registry root` and a `tombstone root` it **cannot
add** because there are no more slots. `subscription` is **already at 8/8** — it cannot grow at all.

**The smoking gun — an app already hand-rolling this design under duress.** `subscription`
documents (`subscription/src/lib.rs:16-23`) that it *wanted* 8 dedicated `message_slot[i]` slots but
*"The cell substrate has `STATE_SLOTS = 8` total … which is"* too few, so it stuffs all messages into
**a single `message_root` commitment in slot 6** with per-message tuples stored off-cell. That is
**exactly the committed-field-map this design generalizes** — `subscription` already pays the
membership-proof cost by hand for ONE field because the substrate forces it. This upgrade promotes
that ad-hoc, per-app workaround into a first-class, verified, reusable substrate primitive.

**(2) Special-cased stores** (kernel-reserved, NOT general user data):

- `fields[7]` = sealed-box commitment in the Lean/Rust seal flow (`RecordKernel.lean:551`:
  *"dregg1's per-cell `state.fields[7]` seal commitment"*; Rust `apply_seal`/`apply_unseal`).
- `swiss_table_root`, `refcount_table_root` — already **separate** named `[u8;32]` fields on
  `CellState` (`state.rs:78,84`), NOT inside `fields[]`. But the **circuit** mirrors them INTO
  `fields[3]`/`fields[4]` (`_IR-EXTENSION-DESIGN.md:118-121,138-139`) — so the circuit *does* steal
  two of the 8 user columns.

**(3) Proposed side-table roots** (`_IR-EXTENSION-DESIGN.md:132-143`): the IR-extension assigns

```
fields[1]=ESCROW_ROOT  fields[2]=QUEUE_ROOT  fields[3]=REFCOUNT  fields[4]=STURDYREF
fields[5]=DELEG_ROOT   fields[6]=NULLIFIER    fields[7]=COMMIT_ROOT
```

leaving **only `fields[0]`** "free / cell-domain" (`_IR-EXTENSION-DESIGN.md:137`).

### A.3 The collision, stated precisely

The IR-extension's own table (`_IR-EXTENSION-DESIGN.md:137`) gives apps **field[0] only**. But:

- `subscription` needs **8** user fields (0/8 free) → **direct collision on all 7 stolen slots**.
- `governed-namespace` wants slots 6,7 for its OWN registry/tombstone roots → collides with
  `NULLIFIER`/`COMMIT_ROOT`.
- ANY app using `SetField` on `fields[1..7]` while a side-table root lives there would either corrupt
  the root or be locked out by an `Immutable` caveat on the root cell.

**Concretely blocked today:** (a) `subscription` cannot add a single new field; (b)
`governed-namespace` cannot land its two documented future roots; (c) any app needing >1 user field
under the IR-extension is dead. The 8-field cap, contended three ways, is the wall.

---

## §B — EXTENSIBLE USER FIELDS: the committed field MAP

### B.1 Core idea

Add a single **`fields_root`** that commits an arbitrary **`key → value` map** via a Poseidon2 keyed
accumulator (the **same `keyedDigest` / `ListCommit.listDigest` mechanism** the side-table roots use,
`_IR-EXTENSION-DESIGN.md §C`, `EffectCommit2.lean:154-162`). Apps get unlimited fields; the circuit
carries **one root column** instead of 8 value columns. A field read/write is proven against the root
by a **membership/update witness** — exactly the append/keyed-update gate the IR-extension already
proves sufficient for side-tables (no new gate-kind needed).

```
old (fixed):   state.fields[0..7]   = 8 value columns, each absorbed by GROUP-4
new (hybrid):  state.fields[0..R-1] = R RESERVED low keys (kept as columns, backward-compat)
               state.fields_root    = 1 column, Poseidon2 keyedDigest over keys ≥ R
```

### B.2 Backward-compat strategy: HYBRID (reserved low keys + map tail)

Do **NOT** rip out the 8 fixed cells. Keep `fields[0..R-1]` as fixed columns (`R` chosen below) so
**every existing corpus / app / proof that indexes `fields[idx]` for `idx < R` is byte-identical**.
Add `fields_root` for keys `≥ R`. Two sub-options for `R`:

- **R = 8 (purely additive, recommended for the beachhead):** keep all 8 fixed cells, add
  `fields_root` as a 9th carrier for keys 8,9,10,…. Zero change to existing apps; `subscription`
  (8/8 full) gains keys ≥ 8. **This is width +1 root column in the circuit** (or reuse the spare
  GROUP-4 `ZERO` absorb slot, `_IR-EXTENSION-DESIGN.md:158-162`, so width stays 186).
- **R = small (e.g. 2: `balance`-adjacent hot fields stay fixed, rest move to map):** a later
  consolidation that shrinks the fixed block. Higher proof-repair cost (apps re-key 2..7 into the
  map). **Deferred** — the beachhead is R = 8.

The **canonical key encoding**: reserved keys `0..R-1` are the old slot indices (so `fields[3]` ≡
key `3`); user map keys are `≥ R`. A field READ is: if `key < R` read the fixed column; else
membership-prove against `fields_root`. The Lean side already does this uniformly via `FieldName`
(see B.4) — the fixed/map split is a **Rust+circuit implementation detail invisible to the proofs**.

### B.3 Rust state-rep change (`cell/src/state.rs`)

```rust
pub struct CellState {
    pub fields: [FieldElement; STATE_SLOTS],            // R = 8 reserved low keys (UNCHANGED)
    pub field_visibility: [FieldVisibility; STATE_SLOTS],
    pub commitments: [Option<[u8;32]>; STATE_SLOTS],
    // NEW — additive, #[serde(default)] so old serialized cells deserialize:
    pub fields_root: [u8; 32],                          // Poseidon2 keyedDigest over the map tail
    pub fields_map: BTreeMap<u64, FieldElement>,        // OFF-COMMITMENT witness store (keys ≥ 8)
    // … nonce/balance/swiss_table_root/refcount_table_root unchanged …
}
```

- `fields_root` is the **committed** root (goes into `compute_canonical_state_commitment` exactly as
  `swiss_table_root` does, `state.rs:75-78`). `fields_map` is the **prover-side witness** (the actual
  key→value entries; not itself committed — its digest `fields_root` is). `#[serde(default)]` keeps
  every existing `CellState` deserializing (the additive-extension pattern already used for
  `delegation_epoch`/`swiss_table_root`, `state.rs:69,77`).
- Read: `get_field(key)` → `if key < 8 { fields[key] } else { fields_map.get(key) }`.
- Write: `set_field(key, v)` → fixed cell if `key < 8`, else `fields_map.insert(key,v)` then
  recompute `fields_root` (the keyed accumulator update).

### B.4 Lean state-rep change (`Exec/Value.lean` / `RecordKernel.lean`) — MINIMAL

The Lean record is **already** `record : List (FieldName × Value)` (`Value.lean:65`) — an unbounded
name-keyed map. **No AST change is required** for capacity: `Value.scalar f`/`setField f v` already
read/write arbitrary names. The ONLY Lean-side addition is a **digest commitment lemma** binding the
record's tail (keys outside the reserved set) to a `fields_root` value, so the circuit's
single-root-column claim has a Lean witness:

```lean
/-- The committed digest of a record's USER MAP (keys ≥ reserved). Reuses `ListCommit.listDigest`
    (the same injective accumulator the side-table roots use). -/
def fieldsRoot (v : Value) : FieldElem := ListCommit.listDigest (userTail v)

/-- Membership: reading key `k` (k ≥ reserved) returns `x` ⟺ `(k,x)` is in the committed tail.
    Lifts `ListCommit` membership; the read/write laws (`setField_scalar_self`,
    `setBalance_balOf`) already hold over the list. -/
theorem fieldsRoot_membership … 
```

`fieldsRoot` reuses `EffectCommit2.keyedDigest`/`ListCommit.listDigest` (the **already-built injective
digest portal**, `EffectCommit2.lean:113-162`) — the same mechanism §C / the IR-extension uses for
side-tables. This is the seam: the circuit binds **one column** `fields_root`; the Lean
`ActiveComponent.binds`/`encodes` obligation certifies it equals `fieldsRoot (cell c)`; and the
EXISTING name-keyed `Value.scalar`/`setField` laws give the read/write semantics for free.

### B.5 Circuit change (the width-fixed win)

- Replace the GROUP-4 absorption of `fields[1..7]` value cells (`_IR-EXTENSION-DESIGN.md:108`,
  `inter2/inter3` over `f1..f7`) with absorption of the **reserved low keys + the `fields_root`
  column**. In R=8-hybrid the cleanest realization: keep `inter2/inter3` over `fields[0..7]` for
  backward-compat AND add `fields_root` into the **spare GROUP-4 `ZERO` absorb slot**
  (`EffectVmEmitTransfer.lean:159`, `_IR-EXTENSION-DESIGN.md:158-162`) → **width stays 186**.
- A map field write emits an `arity:2` keyed-update `VmHashSite` (`fields_root' = update(fields_root,
  key, val)`) — **the same site form** the IR-extension uses for side-table appends
  (`_IR-EXTENSION-DESIGN.md:200-216`). **No new `VmConstraint` kind** (the IR-extension already
  proved gate/transition/boundary/piBinding + arity 2/4 sites suffice, `:239-240`).

---

## §C — DEDICATED SIDE-TABLE-ROOT NAMESPACE (reconciling `_IR-EXTENSION-DESIGN.md`)

The IR-extension's only error is its **home** for the roots, not its mechanism. It stole user
`fields[1..7]` (`_IR-EXTENSION-DESIGN.md:138-143`). With §B freeing user fields onto `fields_root`,
the roots get their **own** namespace, never colliding with app data:

**Option C1 — a dedicated `roots` sub-block (recommended).** Add a small fixed
`system_roots: [FieldElement; 8]` to `CellState`, parallel to `fields`, holding
`ESCROW/QUEUE/REFCOUNT/STURDYREF/DELEG/NULLIFIER/COMMIT/CAP` roots by a *fixed, kernel-owned* index.
In the circuit these are their own state columns (or one `system_root` keyed digest over them, if
width is precious). Apps **never** address `system_roots` (no `SetField` reaches it — it is mutated
only by the kernel's escrow/queue/etc. transitions). The IR-extension's §B/§C/§E close-plan transfers
**verbatim** — the gates and hash-sites are identical, only the column *constant* changes from
`FIELD_BASE+i` to `SYSTEM_ROOT_BASE+i`.

**Option C2 — high keys in `fields_root` itself, kernel-reserved.** Reserve a key band (e.g. keys
`2^32 + i`) inside the SAME `fields_root` accumulator for system roots; apps are forbidden (by a
`SlotCaveat`/admission check) from writing those keys. Fewer columns, but couples user and system
mutation into one root → a user write and a system write both recompute the same root (more
proof-coupling). **C1 is cleaner** (orthogonal roots, independent gates) and is the recommendation;
C2 is a width-minimizing fallback.

Either way the **invariant** is: *user fields and system roots are disjoint namespaces with disjoint
mutators* — the executor's `SetField` path can only touch user keys; escrow/queue/null/etc. kernel
transitions can only touch `system_roots`. This is strictly **stronger** than today (where the
circuit aliased `swiss/refcount` into user-addressable `fields[3]/fields[4]`, a latent collision).

**Reconciliation note for `_IR-EXTENSION-DESIGN.md`:** its tables `:132-143` and `:259-272` should
re-target `FIELD_BASE+i` → `SYSTEM_ROOT_BASE+i` (C1). Its anti-ghost argument (`:181-194`) is
UNCHANGED — `system_roots` are absorbed into `state_commit` by the same GROUP-4 tree, so tampering a
system root still flips `state_commit` and goes UNSAT. The two docs compose: this doc owns the user
namespace + `fields_root`; that doc owns the per-effect root-update gates over `system_roots`.

---

## §D — PROOF-REPAIR SCOPE (honest)

### D.1 What LIFTS (designed so old fixed-field access is a special case of map-access)

Because the Lean field model is **already name-keyed**, the verified semantic keystones do **not**
change shape. They lift verbatim once `Value.scalar`/`setField` over the hybrid (fixed-cell +
map-tail) record agrees with the old pure-list record on the reserved keys (a `decide`-level
equivalence on `key < R`):

- `setBalance_balOf` (`RecordKernel.lean:583`) — `balance` is a reserved key; **unchanged**.
- `recKExec_conserves` / `recKExec_authorized` / `recKExec_unauthorized_fails` / `recKExec_frame`
  (`RecordKernel.lean:667,684,693,702`) — all read `balOf`/`authorizedB`, name-keyed; **lift verbatim**.
- `recTransfer_balOf_delta` / `recTransfer_balanceSum_conserve` (`:632,651`) — name-field deltas;
  **lift**.
- `stateStepGuarded_eq` / `_admits` / `_caveat_violation_fails` (`EffectsState.lean:269,280,292`) —
  caveat gate is over `FieldName`, not index; **lift verbatim**. `SlotCaveat` (`RecordKernel.lean:81`)
  is name-keyed already.
- `flatten_width` (`Value.lean:140`) — width is a function of the SCHEMA; the schema gains a
  `fields_root` field of width 1, so width changes by a constant — **re-proves by the same induction**.

These lift **because** we choose the hybrid encoding so that "fixed cell `idx`" = "map key `idx`":
old field access is literally a special case of the new map access. The proofs were never
array-bounded, so they have nothing to break.

### D.2 What MUST be RE-PROVEN (concentrated, enumerable)

1. **Record/cell digest (canonical commitment).** `compute_canonical_state_commitment`
   (`commitment.rs:1+`, ctx `dregg-cell:canonical-state-commitment v2`, `:61`) must absorb
   `fields_root` (and `system_roots` under C1). **MUST bump the version suffix** (`v2`→`v3`) per the
   stated policy (`commitment.rs:56-61`) — this cleanly invalidates stale commitments rather than a
   silent cross-version collision. Re-prove: digest injectivity over the new shape (the
   `ListCommit`/`keyedDigest` injectivity lemmas already exist, `EffectCommit2.lean`).
2. **Circuit GROUP-4 field-column gates.** The transfer-keystone full-state soundness
   (`EffectVmEmitTransferSound.lean`, the anti-ghost UNSAT) is proven over `fields[0..7]` columns.
   Moving the map tail to `fields_root` requires re-proving that **tampering a map field flips
   `fields_root` flips `state_commit` ⇒ UNSAT** — this is the SAME anti-ghost shape, now routed
   through the keyed-accumulator (the IR-extension already argues this lifts for side-table roots,
   `_IR-EXTENSION-DESIGN.md:181-194`; we reuse that argument for `fields_root`).
3. **The `fieldsRoot_membership` read/write laws (NEW, §B.4).** A map field read returns `x` iff
   `(k,x)` is committed in `fields_root`; a write updates `fields_root` correctly. Discharged off the
   existing `ListCommit`/`keyedDigest` membership+update lemmas (`EffectCommit2.lean:113-162`) — new
   wrappers, not new axioms.
4. **Rust evaluators that index `fields[idx]`.** `StateConstraint::evaluate`'s arms
   (`program.rs:246,1258,1318,1368,…` — the ~30 `new_state.fields[idx]` reads) now read
   `get_field(idx)` (fixed-or-map). Pure Rust refactor (not a Lean proof), but it is the
   **differential surface**: the Lean `SlotCaveat.eval` is the spec; the Rust `evaluate` must keep
   matching it for keys ≥ 8 too. Differential test (kernel-vs-Rust) is the assurance gate, NOT a new
   trust assumption.

### D.3 Ordering (least-disruptive first)

1. Lean `fieldsRoot` def + `fieldsRoot_membership` (additive defs, nothing else imports them yet) — green.
2. Rust `CellState.fields_root` + `fields_map` additive fields with `#[serde(default)]`; `get_field`/
   `set_field` accessors that fall through to fixed cells for `key < 8` — every existing test still
   passes (additive).
3. Canonical commitment absorbs `fields_root`, bump `v2`→`v3` — re-prove injectivity.
4. Circuit `fields_root` column into the spare GROUP-4 slot (width-neutral) + the keyed-update site;
   re-prove the anti-ghost UNSAT for a map field.
5. Re-target `_IR-EXTENSION-DESIGN.md` side-table roots to `system_roots` (C1) — now decoupled from
   user fields.

### D.4 VACUITY GUARD (reject the temptation)

The cheap-and-wrong move is to make `fields_root` `:= 0`/`:= True`/an unconstrained column —
"present but not load-bearing" — so the proofs "pass." **Reject it.** The non-vacuity bar (per
MEMORY: *Don't Launder Vacuity as "Honest"*): every new lemma must witness **both** a TRUE and a
FALSE instance —
- `fieldsRoot_membership` must show a present key reads its value **AND** an absent key does NOT
  (`#eval`/`#guard` a positive and a negative, no `native_decide`).
- the circuit anti-ghost must show an honest map write is SAT **AND** a tampered map value is **UNSAT**
  (the anti-ghost tooth, mirroring `EffectVmEmitTransferSound.lean`).
- `fields_root` must be **proven injective enough** that two distinct maps cannot share a root
  (off `ListCommit` injectivity) — a `:= 0` stub would collapse this and is forbidden.

A labeled vacuity is still a broken guarantee. The map must genuinely commit the data.

---

## §E — STAGED, BUILDABLE PLAN + BEACHHEAD

Each stage **green + `#assert_axioms` clean** (no new axioms below the line). An implementation wave
executes them in order; stage *N+1* depends only on *N*.

| Stage | Deliverable | Green gate |
|---|---|---|
| **0 — BEACHHEAD** | Lean: `fieldsRoot` + `fieldsRoot_membership` (pos+neg `#guard`). Rust: `CellState.fields_root`+`fields_map`+`get_field`/`set_field` (additive, `#[serde(default)]`). Wire **`subscription`** (the 8/8-full app) to write ONE key-`8` map field + read it back with a membership check, end-to-end. **All old `fields[0..7]` proofs + corpora untouched.** | Lean builds; subscription tests pass; new pos/neg guards pass; `#assert_axioms` clean |
| 1 | Canonical commitment absorbs `fields_root`; bump `v2`→`v3`; re-prove digest injectivity | commitment tests + injectivity lemma green |
| 2 | Circuit: `fields_root` column into spare GROUP-4 `ZERO` slot (width-neutral 186); keyed-update site; **anti-ghost UNSAT for a tampered map field** | prover SAT(honest)+UNSAT(tampered); circuit-soundness theorem green |
| 3 | `system_roots` sub-block (C1); re-target `_IR-EXTENSION-DESIGN.md` roots off `fields[1..7]` onto `system_roots`; user `fields[1..7]` **freed** | escrow/queue/null/etc. emit files green on `SYSTEM_ROOT_BASE`; no app/root collision |
| 4 | Migrate `governed-namespace` (its two documented future roots) + any app wanting >8 fields onto the map; differential kernel-vs-Rust on map-field `StateConstraint::evaluate` | apps green; differential clean |
| 5 (deferred) | Optional R-shrink (R=8→small): move hot apps' tail fields into the map, shrink the fixed block | apps re-keyed; proofs lift |

### The beachhead, concretely (Stage 0)

1. **Lean** (`RecordKernel.lean` or a new `Exec/FieldsMap.lean`): `def fieldsRoot (v : Value) :
   FieldElem := ListCommit.listDigest (userTail v)` + `theorem fieldsRoot_membership` (reuse
   `ListCommit` lemmas) + `#guard` a present key reads its value and `#guard` an absent key does not.
   **No existing def changes.**
2. **Rust** (`cell/src/state.rs`): add `fields_root: [u8;32]` + `fields_map: BTreeMap<u64,
   FieldElement>` with `#[serde(default)]`; add `get_field(key)`/`set_field(key,v)` that read/write
   the fixed array for `key < 8` and the map otherwise, recomputing `fields_root` on map writes.
   **`fields[0..7]` array + all existing accessors UNCHANGED.**
3. **App** (`subscription`): it is at 8/8 (`subscription/src/lib.rs:168-182`). Add a `key-8`
   "next-payload-overflow" map field; a test writes it via `set_field(8, …)`, reads it back, and
   checks the membership proof against the recomputed `fields_root`. This proves the END-TO-END path
   (Rust write → root update → membership read) on the app that the 8-cap actually blocks.
4. **Untouched:** every `fields[idx<8]` access, every existing app, every existing Lean keystone,
   every committed corpus. The beachhead is **purely additive** — it proves the map works without
   disturbing a single proven guarantee, then later stages free the user namespace and re-home the
   side-table roots.

---

## Appendix — interplay with `_POLICY-LANGUAGES-REFRESH.md`

A richer record enables richer predicates, and vice-versa:

- The policy doc flags **"No allowlist / set-membership over field VALUES"** and **"No prefix /
  string-structure predicate"** (`_POLICY-LANGUAGES-REFRESH.md:63,70`) — those gaps are *easier* once
  a field can itself be a **committed sub-map root** (a field whose value is a `fields_root`-style
  accumulator, against which a `StateConstraint` proves membership). The map mechanism here is the
  substrate for set-valued field predicates.
- Conversely, the policy doc notes only `SlotCaveat` is wired into `stateStepGuarded`
  (`:37-38`); the map upgrade keeps that wiring intact (caveats are name-keyed) and simply lets
  caveats target map keys ≥ 8 — so a future `allowedTransitions`/membership predicate over a map
  field is in-scope.
- **Order of operations:** land this record-layer beachhead (Stage 0–2) BEFORE the policy-language
  enrichment, because the richer predicates want the map substrate to commit set-valued fields
  against. The two docs share the `ListCommit`/`keyedDigest` portal (`EffectCommit2.lean`) as the
  common injective-accumulator foundation.
