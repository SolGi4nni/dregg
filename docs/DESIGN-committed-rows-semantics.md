# DESIGN — `RowSemantics.committedRows`: scope, breakage, payoff, verdict

**Status:** design + feasibility verdict. The Lean denotation is PROTOTYPED AND GREEN in
`metatheory/Dregg2/Circuit/Emit/CommittedRowsSemantics.lean` (11 keystones `#assert_all_clean`).
Nothing is landed in the shared IR: `metatheory/Dregg2/Circuit/DescriptorIR2.lean` is untouched.

**Substrate, said out loud:** this is Lean-authored AIR metatheory. The prototype authors no
descriptor and adds no constraint. The verdict below turns substantially on the fact that
*realizing* `committedRows` means writing a new hand-authored constraint family in
`circuit/src/descriptor_ir2.rs` — Rust-authored AIR — which is the same debt class as the existing
`Ir2Air::MapOps` arm, not a foundation.

---

## 0. The finding this comes from

`AttestedAutomatonEmit.lean` §7 (committed `3e8b0827c0`):

> The subset check "the run's edges are edges of the committed automaton" IS achievable at `O(|w|)`
> in this IR — but NOT by a `lookup`. A `lookup` targets a `TableDef`, and the only
> content-committing row semantics is `exactPublicRows`, whose contents are the DESCRIPTOR'S OWN
> BYTES: any lookup-based binding must therefore declare every edge (`O(|Q|·|Σ|)`) and additionally
> inherits the unit-capacity exact-multiset receive, i.e. the Eulerian obstruction. There is NO
> table semantics in `RowSemantics` whose contents are committed by a ROOT rather than listed.

That gap forced the attestation through `MapOp`, whose deployed realization is a
depth-`MAP_TREE_DEPTH = 16` binary-Merkle path per opened row.

**The finding decomposes into two independent gaps.** Conflating them is what makes
`committedRows` look like one change; it is two, and they have very different prices.

| | Gap | What it costs today | What removes it |
|---|---|---|---|
| **A** | **Capacity.** An `exactPublicRows` receive is UNIT capacity per declared row: `PublicLookupBalanced` demands the lookup log be a *permutation* of the manifest, and `descriptor_ir2.rs` realizes it as **one `Ir2Air::ExactPublicRow` batch instance per declared row**. | The Eulerian obstruction (a run must traverse every declared edge exactly once ⇒ no witness), plus a measured **+1.76 KiB wire / +0.15 ms prover CPU per declared row** and a hard wall at `MAX_EXACT_PUBLIC_ROWS = 128`. | A shared, multiplicity-carrying table (the mechanism the byte/range tables already use). **The soundness question is already answered:** `DfaRoutingSubsetTableCost.tableRouting_refines_classify_subset` proves the refinement never used the exactness leg, and both tamper canaries still bite under the weaker `Satisfied2Subset`. |
| **B** | **Contents provenance.** Contents are the descriptor's bytes, so declaring `E = |Q|·|Σ|` rows costs `O(E)` descriptor bytes and re-issues the descriptor per automaton. | ~10 descriptor bytes per row; a different descriptor object (and VK) for every automaton. | `committedRows (root)` — contents become a WITNESS pinned by a root. |

Gap A is the expensive one and it is **already discharged in Lean**. Gap B is what
`committedRows` is actually about. Section 4 is where that distinction decides the verdict.

---

## 1. What `RowSemantics.committedRows (root : EmittedExpr)` would MEAN

Prototyped verbatim, and green, in `CommittedRowsSemantics.lean`. The constructor would carry the
table id, arity (inherited from `TableDef`), the **column expression carrying the commitment**, and
the **committed tree depth**:

```lean
structure CommittedRowsDecl where
  id    : TableId
  arity : Nat
  root  : EmittedExpr      -- the analog of a MapOp's root group
  depth : Nat              -- the committed leaf domain is 2 ^ depth
```

The faithfulness leg that replaces `TableDef.publicContentsFaithful`:

```lean
def CommittedContents (hash : List ℤ → ℤ) (cd : CommittedRowsDecl) (R : ℤ) (t : VmTrace) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ cd.depth
    ∧ MapMerkleRoot.mapRoot hash cd.depth h = R ∧ t.tf cd.id = rowsOfHeap h
```

— the table's contents are not descriptor bytes but the **graph of some sorted, `2^depth`-leaf heap
whose deployed binary-Merkle `mapRoot` is `R`**. `depth` is not decoration: §3 shows the entire
economics turns on whether the commitment is packed to the table's own row count or kept at the
deployed `2^16` leaf domain.

The acceptance predicate is additive, exactly like `Satisfied2Public` / `Satisfied2U` /
`Satisfied2Custom`:

```lean
structure Satisfied2Committed … extends Satisfied2 … where
  committedContents : CommittedContents hash cd R t
  rootPinned        : ∀ i < t.rows.length, cd.root.eval (envAt t i).loc = R
```

### The lever, and the payoff, machine-checked

* `committed_lookup_opens` — a table row `[k, v]` of a committed table **IS** an
  `opensToMerkle hash cd.depth R k (some v)`. This is precisely the primitive `MapOp.holdsAt`
  supplies per row, obtained instead from one table membership.
* `lookup_replaces_mapOp` — **the payoff.** The conclusion `AttestedAutomatonEmit.att_row_reads`
  extracts from a per-row `MapOp` (`next` is the COMMITTED automaton's step, not merely some
  declared edge) is derived from a `Lookup` plus `CommittedContents`, under the **same**
  `Poseidon2SpongeCR` floor and no extra hypothesis.
* `committedRoot_binds_contents` — the table-level analog of `root_binds_automaton`: two committed
  tables under the same root agree at every key they both carry. One felt, one table content.
* Non-vacuity, both legs at ONE root: `committed_and_commits_automaton` shows the very heap
  `AttestedAutomatonEmit` commits (`autoHeap d`, total over the deployed `2^16` leaves) realizes
  `CommittedContents` at `autoRoot hash d`, so §3's hypotheses are simultaneously satisfiable;
  `committed_lookup_reads_step` fires the whole route end to end.

### The felt-width wound is INHERITED, not repaired

Every theorem above consuming `Poseidon2SpongeCR hash` for `hash : List ℤ → ℤ` inherits
`AttestedAutomatonEmit`'s stated wound verbatim: at the DEPLOYED BabyBear codomain
(`p = 2013265921 ≈ 2^31`) that hypothesis is **false** — a birthday search finds a colliding root in
~2^15.5 work. A `committedRows` root is the same kind of felt and would need the same 8-felt weld.
This design does not improve that and does not claim to.

---

## 2. What BREAKS

### 2a. Lean — almost nothing, and that is the load-bearing observation

The prototype's whole denotation **compiles without touching `DescriptorIR2.lean`**. That is the
evidence: a table whose `RowSemantics` is *not* `exactPublicRows` already has prover-supplied
contents in `Satisfied2` — `TableDef.publicContentsFaithful` is `True` there, `PublicLookupBalanced`
likewise. `committedRows` adds a **leg**; it changes **no existing obligation**.

Concretely, `Satisfied2`'s obligations are affected as follows:

| Obligation | Effect of `committedRows` |
|---|---|
| `rowConstraints` (incl. `Lookup.holdsAt`) | unchanged — membership in `t.tf l.table`, contents-agnostic |
| `rowHashes`, `rowRanges` | unchanged |
| `memAddrsNodup` … `memBalanced` | unchanged |
| `memTableFaithful`, `mapTableFaithful` | unchanged (different table ids) |
| `publicTablesFaithful` (`Satisfied2Public`) | unchanged — `True` at the new sem via the `_` arm |
| `publicLookupBalanced` (`Satisfied2Public`) | unchanged — `True` at the new sem via the `_` arm |
| **new** `committedContents` | contents become a WITNESS pinned by a root |
| **new** `rootPinned` | the root column carries the public commitment on every row |

Adding the enum constructor touches exactly **five** `RowSemantics` match sites tree-wide, of which
**one** is exhaustive:

| Site | Shape | Breaks? |
|---|---|---|
| `DescriptorIR2.lean:478` `TableDef.publicContentsFaithful` | `\| _ => True` | no |
| `DescriptorIR2.lean:499` `PublicLookupBalanced` | `\| _ => True` | no |
| `DescriptorIR2.lean:1501` `RowSemantics.tag` | **exhaustive** | **yes — 1 line** |
| `DescriptorIR2.lean:1523` `TableDef.toJson` | `\| _ => ""` | no (but wants a new arm to emit the root) |
| `TinyAutomataCompose.lean:189` `tdRows` | `\| _ => 0` | no (wants an arm: a committed table declares 0 rows) |

`deriving Repr, DecidableEq` on `RowSemantics` survives: `EmittedExpr` derives both
(`Exec/CircuitEmit.lean:69`). No byte-pinned wire golden moves — an additive constructor changes no
existing `sem` tag, so `demoV2` / `demoPublic` / `demoU` / `demoC` and the Rust `DEMO_*` mirrors
stay byte-identical.

**Lean verdict: additive. It does not red-umbrella the tree.**

### 2b. Rust — this is where the work is

Six files carry `TableSem` (33 · 30 · 8 · 2 · 2 · 2 sites). The load-bearing ones:

1. **`descriptor_ir2.rs:880-891` — decode.** One new `Some("committed_rows") => …` arm.
2. **`descriptor_ir2_canonical.rs:237-252 / 695-708` — the canonical fixed-record codec.**
   Deliberately exhaustive, by design: *"adding a descriptor constructor or field makes this module
   fail to compile until a new schema version is designed."* An additive tag byte `9` is
   backward-compatible bit-for-bit for every existing descriptor, but the module's stated policy is
   a schema-version bump — and `EFFECT_VM_DESCRIPTOR2_CANONICAL_VERSION` is encoded *into* the
   record at line 484, so a bump changes `effect_vm_descriptor2_semantic_fingerprint` for **every**
   descriptor. That is a registry/VK-churn decision, not a code change. Named, not laundered.
3. **`descriptor_ir2.rs:1412-1436` — `check_descriptor2`'s lookup gate**, which today rejects a
   lookup into any custom table that is not `ExactPublicRows` ("no realized lookup relation"). New
   arm + arity/depth well-formedness.
4. **`descriptor_ir2.rs:2714-2730` — the main AIR's send site.** Today an exact-public lookup sends
   on a per-table bus at multiplicity `ONE`, unconditionally. A committed table wants the same send
   plus a receive that is **multiplicity-carrying**, not unit-capacity.
5. **⚑ `Ir2Air::CommittedRows` — a NEW AIR arm. This is the whole cost.** It must, in-circuit:
   * hold the table rows in a committed trace, sorted strictly increasing by key
     (`eval_lex_lt_counted` + `eval_canon_decomp_counted` exist, reusable from the `MapAbsent`/AAFI
     arms);
   * **recompute the commitment over its own rows**: `E` leaf absorbs via `chip_absorb_tuple` plus
     `E − 1` `node8` compressions via `node8_lookup_tuple` (both primitives already exist and are
     arity-generic) folded to a packed depth-`⌈log₂ E⌉` root;
   * expose that root to the main AIR (bus or PI) so `rootPinned` is enforced;
   * serve queries via `LookupBus::table_entry(.., multiplicity)`.
   Structurally this is *a second `Ir2Air::MapOps` with the tree materialized instead of opened*.
   `MapOps` is ~400 lines of AIR plus comparable trace assembly.
6. **`descriptor_ir2.rs:4234-4295` presence detection, `:5786-5817` trace assembly,
   `:5846-5866` `instance_airs`, `:6014-6024` the prove/verify wiring** — one new branch each, plus
   a real witness generator that builds the heap, computes the packed root and fills the sibling and
   chain columns.
7. **`descriptor_ir2.rs:4434-4441`** — the exact-public typed-identity check has a committed analog
   (contents vs recomputed root) that must be written, not inherited.

**Rust verdict: a new hand-authored constraint family.** Every `Ir2Air` arm today is Rust-authored
AIR whose relation to its Lean denotation is *tested*, never *proved* — there is no formal semantics
of Rust, so this is unit testing with zero formal content. Adding `committedRows` adds one more such
arm. The `MapOp` route reuses an arm that already exists, is already exercised by the prover tests,
and is already the object every heap/cap/nullifier opening rides.

---

## 3. THE PAYOFF, quantified

### 3a. First, a correction to the attested cost headline

`AttestedAutomatonEmit` §7 states `MAP_TREE_DEPTH · |w| = 16·|w|` chip rows for the map-op route.
Read against the deployed `Ir2Air::MapOps` arm (`descriptor_ir2.rs:3290-3401`) that is an
**undercount by one per row**:

* the arm issues **34 chip-bus lookups** per opened `read` row — an old-leaf and a new-leaf absorb,
  plus an old-chain and a new-chain `node8` per level (`for lvl in 0..HEAP_TREE_DEPTH`, two
  `p2.lookup_key` calls each);
* on a `read` row `old_value = value` and `new_root = root`, so each pair is the **same tuple** and
  dedups in `chip_hist` (`:5610-5677`, one row per unique permutation with a multiplicity column);
* net: **17 unique chip permutations per opened row** = 1 leaf absorb + 16 `node8`, not 16.

(Upper bound: across rows, distinct keys share their upper path nodes above the LCA, so a real
multi-open batch is somewhat below `17·|w|`. That sharing only helps the map-op route, so the
comparison below is conservative *against* `committedRows`.)

`#guard mapOpPermsPerRow == 17` and `#guard mapOpLookupsPerRow == 34` pin this in
`CommittedRowsSemantics.lean` §6. ⚠ These are counts read off the AIR, not measurements of a proven
object; every `#guard` is compiled evaluation of a closed `Bool` and proves no `Prop`.

### 3b. The two routes' bills

| Route | Chip permutations | Scales with |
|---|---|---|
| `MapOp` (deployed, attested) | `17 · \|w\|` | word length |
| `committedRows`, packed depth `⌈log₂ E⌉` | `2E − 1`, **once**; each lookup is one bus send, zero permutations | committed table size |
| `committedRows`, kept at deployed depth 16 | `2·65536 − 1 = 131071`, once | nothing (catastrophic) |

At the tiny-automata sizes `TinyAutomataSatisfiable` measures — reachable product spaces
2 / 6 / 12 / 25 over `k = 1…4`, so `E = |Q|·|Σ| = 4 / 12 / 24 / 50`:

* packed commitment cost: **7 / 23 / 47 / 99** permutations, once;
* crossover word length (`⌈(2E−1)/17⌉`): **|w| = 1 / 2 / 3 / 6**;
* at `k = 4` (`E = 50`): `|w| = 8 → 136 vs 99`; `|w| = 32 → 544 vs 99` (**5.5×**);
  `|w| = 128 → 2176 vs 99` (**22×**).

**And the other polarity, so the win is not laundered:** if the commitment is kept at the deployed
`2^16` leaf domain, `committedRows` costs 131071 permutations and does not pay until `|w| = 7711`.
The `depth` field is the whole design.

### 3c. The wire/instance axis — where the money actually is

MEASURED, from `circuit/tests/tiny_automata_prover_shape_measure.rs` (production `ir2_config`, both
shapes satisfiable):

* deployed `exact_public_rows`: **+1.76 KiB wire and +0.15 ms single-thread prover CPU per declared
  row**, one batch instance per declared row (`1 + k·n` instances), hard wall at
  `MAX_EXACT_PUBLIC_ROWS = 128`. Composition costs **+28.1 KiB and +2.43 ms per additional
  automaton** at `n = 16`.
* shared multiplicity-carrying table: **+1.06 KiB and +0.26 ms per additional automaton**, always 2
  batch instances, no cap — **26× / 9× cheaper**.

⚑ **That is Gap A, not Gap B.** The 26×/9× is bought by making the receive multiplicity-carrying —
which does not require a root at all, keeps the declared bytes, and whose *soundness* is already a
theorem (`tableRouting_refines_classify_subset`, plus `badTrace_not_subset_satisfied` /
`mutFin_not_subset_satisfied` showing both canaries still bite under the weaker hypothesis).

What Gap B (`committedRows`) adds **on top of** Gap A is:

1. ~10 descriptor bytes per row removed (`E = 50` → ~500 bytes; the attested descriptor is 1190
   bytes total, so this is real but small);
2. the descriptor becomes **generic** — one object and one VK for every table instead of one per
   table (the property `attestedDesc` already has via the root-in-`pi[2]` trick);
3. the table's *contents* need never be shipped to the verifier at all.

Against the anchor that is actually witnessed — `AttestedAutomatonEmit` §7's measured numbers,
standing behind `attWit_satisfies`: 4 columns, 6 constraints, 3 PIs, **zero declared rows**, wire
**1190 bytes constant**, main area `4·|w|`, `5·|w|` map-op rows, `17·|w|` chip permutations — the
committed-rows route would trade `17·|w|` permutations for `2E−1` permutations plus `|w|` bus sends,
keeping the 1190-byte constant descriptor and the genericity.

---

## 4. VERDICT

**Scale: weeks, not days.** The Lean side is ~1 day (the denotation is written and green; what
remains is the enum constructor, the tag, the JSON arm, a wire golden and rewiring the shadow decl
to read from `TableDef`). The Rust side is **2–4 weeks**: a new `Ir2Air` arm of `MapOps` complexity
(sorted-key comparator + in-circuit packed-root recompute + multiplicity-carrying receive), plus
decode, canonical-codec schema decision, well-formedness gate, presence detection, trace assembly,
`instance_airs`, and the Lean↔Rust differential tests that make any of it meaningful.

**Is it worth it versus just welding the `MapOp` root? No — not now, and the ordering is not close.**

1. **The `MapOp` root weld fixes something that is currently FALSE; `committedRows` fixes something
   that is currently EXPENSIVE.** `root_binds_automaton` / `attested_refines_committed` /
   `forged_edge_refused` are today conditional on `Poseidon2SpongeCR` at a BabyBear codomain where
   it is refuted (~2^15.5 birthday). The attestation is a Lean theorem, **not a deployed security
   property**. Welding the root to 8 felts (mirror `beforeCapRootGroup` / `beforeHeapRootGroup` —
   real lanes plus the after-spine keystone) is a bounded, named repair that must happen
   **regardless of which route wins**, because `committedRows` would need the identical weld.
2. **Gap A captures essentially all of the measured cost win, and its soundness is already
   proved.** 26×/9× on wire and prover CPU, no `MAX_EXACT_PUBLIC_ROWS` wall, and
   `tableRouting_refines_classify_subset` already shows the exactness leg was never load-bearing.
   The IR change is a `RowSemantics.subsetRows` tag plus a shared multiplicity table AIR — strictly
   smaller than `committedRows` and it reuses the byte/range table mechanism verbatim. If any
   scaling work is done here, this is the one.
3. **`committedRows` wins only in a narrow regime: small committed table, many queries.** For the
   ledger workloads the map is a `2^16`-leaf heap and `E` is huge — there the recompute is 131071
   permutations and `MapOp` is simply right. The win exists in the tiny-automata / policy-table /
   DFA regime, i.e. the games and attestation surface, not the ledger.
4. **It adds one more hand-authored Rust constraint family.** Every `Ir2Air` arm is Rust-authored
   AIR whose correspondence to its Lean denotation is unit-tested, never proved. `MapOp` is an arm
   we already carry and already exercise; `committedRows` is a new one. Adding debt of that class to
   save permutations on a surface whose binding is not yet a deployed property is the wrong trade.

**Is the `MapOp` route simply good enough? For the attested-automaton object as it stands: yes.**
`17·|w|` chip permutations at `|w| ≤ 128` is ≤ 2176 permutations — the chip table is shared and
amortized across the whole batch, the descriptor is 1190 bytes and constant, zero rows are declared,
and it is the only route with a real `Satisfied2Public` witness at every `k`. The honest statement of
its price is the one already in `AttestedAutomatonEmit` §7 (corrected here from 16 to 17 per row),
and that price is not what is currently wrong with the object. What is currently wrong is the
31-bit root.

### Recommended order

1. **Weld the attestation root to 8 felts.** Fixes a false hypothesis at deployed parameters; days;
   required by every route.
2. **If (and only if) declared-table scaling bites: land Gap A** — a shared multiplicity-carrying
   `RowSemantics`. Soundness theorem already exists; 26×/9× measured; kills the Eulerian
   obstruction and the 128-row wall.
3. **Land `committedRows` only when a workload appears with small `E`, large `|w|`, and a table that
   is not automaton-shaped** (where the `pi[2]`-root trick does not already give genericity). Keep
   `CommittedRowsSemantics.lean` as the pre-built denotation for that day; it is green and its
   keystones are kernel-clean.

---

## Residuals, named

* The `2E−1` and `17·|w|` figures are **arithmetic over the deployed AIR's structure**, not
  measurements of a proven object. The only witnessed descriptor costs cited here are
  `AttestedAutomatonEmit` §7's (behind `attWit_satisfies`) and the
  `tiny_automata_prover_shape_measure.rs` wire/CPU numbers (both shapes satisfiable). No cost is
  quoted for an unsatisfiable descriptor.
* Cross-row upper-path sharing in the `MapOps` chip histogram is not quantified; it reduces the
  map-op bill below `17·|w|` and therefore only weakens the `committedRows` case.
* The 2–4 week Rust estimate is an engineering judgement from the size of the existing `MapOps` arm,
  not a measurement.
* `CommittedRowsSemantics.lean` proves the denotation and the lever. It does **not** prove that any
  Rust AIR realizes them — that gap is the standing one for every `Ir2Air` arm, and calling it
  "translation validation" would be a lie.

---

## ⚠ Verify addendum — the `True` fall-through is the semantic break

An adversarial verify flagged that the "what breaks" enumeration was weighted toward *compile-time*
breakage. The **semantic** break is sharper and easier to miss, because it does not break anything —
it silently weakens:

`TableDef.publicContentsFaithful` (`DescriptorIR2.lean:477-480`) is

```lean
match td.sem with
| .exactPublicRows rows => tf td.id = exactPublicTable rows
| _                     => True
```

so **every row-semantics other than `exactPublicRows` falls through to `True`** — it carries *no*
contents obligation at all, on the stated grounds that "other row-semantics are enforced by their
existing specialized global legs." A newly added `committedRows root` constructor would therefore
inherit `True` by default: the table's contents would be **completely unconstrained** unless its own
specialized global leg (`mapRoot`-of-table faithfulness) is written *and wired into `Satisfied2`* in
the same change.

That is the exact shape of the fail-open class this tree has catalogued: a new case that lands in a
permissive default and is green from day one. So the constructor and its obligation must land
**together**, and the obligation must be reachable from `Satisfied2` — adding the constructor first
"to see what breaks" would produce a descriptor that proves nothing about its own table and compiles
clean.
