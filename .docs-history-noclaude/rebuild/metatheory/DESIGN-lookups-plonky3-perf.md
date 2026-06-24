# DESIGN — LogUp lookup arguments + plonky3 performance for the dregg2 circuit mapping

Status: design (read-only research, no code changed). Author: subagent for task #9.
Grounded in the actual code read on 2026-06-06. Paths absolute.

Project memory directive (PROOF-SYSTEM REORIENTATION 2026-06-05): "Lookups=YES."
This doc makes that concrete against the plonky3 checkout we actually pin and the
circuit mapping we actually have.

---

## 0. TL;DR

- The plonky3 we pin (`82cfad7`) ships a **real, complete LogUp implementation** as
  the `p3-lookup` crate, plus a lookup-aware multi-table prover `p3-batch-stark`
  (`prove_batch` / `StarkInstance`). Both are **already declared optional deps** in
  our circuit crate (`/Users/ember/dev/breadstuffs/circuit/Cargo.toml:31-33`, behind
  the `recursion` feature group). **Nothing currently routes any real AIR through
  them** — the only references are a single test import in
  `src/plonky3_recursion_impl.rs:45-46`. Our production prover path is plain
  `p3-uni-stark::{prove,verify}` (no permutation trace, no buses).
- Two places in the mapping pay a **large, avoidable** column/constraint cost that
  LogUp removes:
  1. **Range checks** are done by **bit-decomposition**: `Σ ranges.bits` boolean aux
     columns + a booleanity gate per bit + a recomposition gate
     (`/Users/ember/dev/breadstuffs/circuit/src/lean_descriptor_air.rs:166-249`). A
     32-bit balance = **32 columns + 33 constraints per checked wire**. LogUp turns
     this into **2 aux columns total** (one shared range table + one multiplicity
     column) regardless of how many wires you range-check.
  2. **Set non-membership / absence** is done by a **polynomial accumulator product**
     `∏(α − eᵢ)` over the whole set, materialized as a hashed running accumulator
     (`src/non_membership.rs`, `src/quantified_absence.rs`,
     `src/accumulator_types.rs`). That is `O(|set|)` prover work folded into a
     degree-7 Poseidon chain, and it is **not** a STARK lookup — it's a bespoke
     algebraic gadget whose soundness is carried separately. A LogUp **non-membership
     bus** replaces it with a single auxiliary column and a globally-balanced sum.
- The **Lean-side change is small and additive**: `Dregg2.Circuit.Lookup` already has
  the right denotation (`LookupConstraint` = membership-in-table,
  `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/Lookup.lean:34-87`). What is
  missing is (a) emitting lookups/buses into the descriptor JSON the Rust side
  ingests, and (b) a `kind` (Local vs Global-bus) + `count_weight` field so the
  emitter can express range tables, dispatch buses, and non-membership buses.
- The **Rust-side change is the bulk of the work**: teach `lean_descriptor_air.rs` to
  carry interactions and implement `p3_lookup::InteractionBuilder`, then add a
  prover entrypoint that goes through `p3-batch-stark::prove_batch` instead of
  `p3-uni-stark::prove`. The single biggest structural fact: **uni-stark cannot prove
  lookups**; you must move to the batch-stark prover (or hand-roll the permutation
  trace + an extra commit round, which is strictly more work than reusing
  `prove_batch`).

---

## 1. What the plonky3 LogUp implementation actually is (grounded)

Checkout: `/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/lookup/`.

LogUp = logarithmic-derivative lookup. The math (from `lookup/src/logup.rs:1-18`):

```
multiplicative form:   ∏(α − aᵢ)^{mᵢ}  =  ∏(α − bⱼ)^{m'ⱼ}
logup (additive) form: ∑ mᵢ/(α − aᵢ)  =  ∑ m'ⱼ/(α − bⱼ)
```

It is realized with **one auxiliary ("permutation") column per lookup** carrying a
running sum `s`, with three constraints (`logup.rs:59-62, 226-263`):

- initial: `s[0] = 0`
- transition: `s[i+1] = s[i] + contribution[i]`, encoded *cleared of denominators* as
  `(s_next − s_local)·denom − numerator = 0`
- final: `(cumulative_sum − s_local)·denom − numerator = 0` (global) or the
  transition wrapped around for local (`logup.rs:252-264`).

`numerator/denominator` are the rational `∑ mᵢ/(α − combined_eltᵢ)` collapsed over a
common denominator (`logup.rs:101-146`), where a tuple `(k0,k1,…)` is folded with a
second challenge β: `combined = Σ kⱼ·β^j` (`logup.rs:74-96`). So **two challenges per
lookup column** (α for the running sum, β for tuple-folding —
`LookupProtocol::num_challenges = 2`, `logup.rs:269-271`).

Two flavors (`types.rs:16-23`):

- **`Kind::Local`** — intra-AIR. Running sum must return to **zero** over the trace.
  Both query and table live in the same AIR. Used for "this column is in this
  in-AIR table." Constraint is unconditional (`logup.rs:259-264`).
- **`Kind::Global(bus_name)`** — cross-AIR. Each AIR contributes a prover-supplied
  `cumulative_sum`; the verifier checks **Σ cumulative_sum over all AIRs on the bus =
  0** (`logup.rs:314-324`, `verify_global_final_value`). This is how a range *table*
  AIR and many *query* AIRs share one channel.

Two ergonomic bus wrappers (`lookup/src/bus.rs`):

- **`LookupBus`** (subset / table lookup): `lookup_key(builder, key, mult)` pushes a
  positive interaction with `count_weight=1`; `table_entry(builder, key, n)` pushes a
  negative interaction with `count_weight=0`. "Every query hits a real entry."
  (`bus.rs:22-77`). **This is the range-check and set-membership primitive.**
- **`PermutationCheckBus`** (multiset equality): `send`/`receive`, both weight 1.
  "Sends exactly equal receives." (`bus.rs:79-141`). **This is the dispatch /
  permutation-of-carrier primitive** (relevant to StateCommit's sorted carrier — §4.3).

`count_weight` (`builder.rs:31-39`) is the soundness weight feeding the height-bound
constraint `Σ weightᵢ·heightᵢ < p`: `1` for queries that must hit a real entry, `0`
for table-provider rows. The bus wrappers set it for you.

How an AIR opts in: it bounds its builder on **`InteractionBuilder`**
(`builder.rs:59-94`) and calls `push_interaction` / `push_local_interaction` (or the
bus helpers). Lookups are then *extracted symbolically* by running the AIR against
`InteractionSymbolicBuilder` (`types.rs:44-54`, `Lookups::from_air`) — no manual
column bookkeeping; column indices are auto-assigned local-first then global
(`types.rs:59-89`).

### The prover reality (this is the load-bearing constraint on the design)

- Permutation-trace generation lives in `LogUpGadget::generate_permutation`
  (`logup.rs:369-646`): batch-inverts all denominators (Montgomery trick,
  `logup.rs:534-538`), builds per-row contributions, then a **parallel prefix sum**
  for the running-sum column (`logup.rs:560-645`). Returns a
  `RowMajorMatrix<SC::Challenge>` (an **extension-field** aux trace).
- That aux trace must be **committed in an extra round** and the global cumulative
  sums must enter the transcript. **`p3-uni-stark` does none of this.** The crate that
  does is **`p3-batch-stark`** (`82cfad7/batch-stark/`): `prove_batch`
  (`batch-stark/src/prover.rs:88`) consumes `StarkInstance { air, trace, public_values,
  lookups }` (`batch-stark/src/lib.rs:7`), derives lookups via `Lookups::from_air`
  through `CommonData::from_instances` (`batch-stark/src/common.rs:159,258`), generates
  the permutation traces, and the verifier checks the global sum to zero. **This is
  the prover entrypoint our Lean-driven AIR must target to actually get LogUp.**

So: the gadget is done, the multi-table prover is done, **the wiring from our
descriptor AIR to that prover is the work.**

---

## 2. Where our mapping pays the cost LogUp removes

### 2.1 Range checks — the field-soundness path (the #1 win)

Today (`src/lean_descriptor_air.rs:157-249`): a `RangeSpec{wire, bits}` is enforced by
**bit decomposition**. The AIR width grows by `Σ ranges.bits` boolean aux columns
(`air_width`, `:223-225`), each aux column gets a degree-2 booleanity gate
`b·(b−1)=0`, and there is a degree-1 recomposition gate `Σ bᵢ·2ⁱ − wire = 0`
(`:247-249`, `:160-164`). Cost per range-checked wire:

| approach | aux columns | constraints | trace blowup |
|---|---|---|---|
| **bit-decomp (current)** | `bits` (e.g. 32) | `bits` booleanity + 1 recomp | linear in `bits`, **per wire** |
| **LogUp range bus** | **1** running-sum col (ext field) + 1 shared mult col on the table AIR | 3 (init/trans/final) **per query AIR**, amortized | **flat** — independent of `bits`, shared across all wires |

For a transfer turn with, say, 4 balance/amount wires at 32 bits each, bit-decomp =
**128 boolean columns + 132 constraints**. LogUp = **one range-table AIR** (a single
preprocessed column listing `[0, 2^16)` or a chunked `[0,2^8)` table) plus, in each
query AIR, **one aux column** (and 8-bit limb decomposition only if `bits > table
width`, which is far cheaper than full bit-decomp). This is the canonical LogUp win
and the one to ship first.

Memory's field-wraparound concern (`Lookup.lean:8-12`: "a balance near the field
modulus could WRAP and forge value") is **exactly** what the range bus enforces, and
more cheaply.

### 2.2 Set non-membership / nullifier / absence (the #2 win, higher soundness value)

Today: `src/non_membership.rs` + `src/quantified_absence.rs` + `src/accumulator_types.rs`
enforce set (non-)membership by a **polynomial accumulator product** `∏(α − eᵢ)`
materialized as a hashed running accumulator (`non_membership.rs:309 compute_set_accumulator`,
`quantified_absence.rs:16-21` "Acc_all / Acc_satisfying"). The membership AIR's
`constraint_degree` is **7** because it folds a Poseidon hash per element
(`quantified_absence.rs:94-95`). This is `O(|set|)` prover hashing and a bespoke
gadget whose soundness is carried *outside* the STARK lookup machinery.

LogUp replacement — a **non-membership bus** (the standard LogUp trick):
- The set/blacklist AIR provides each member once as a `table_entry` on a bus
  `nullifier_set` (weight 0).
- The spend AIR, for the value it claims is absent, does **not** `lookup_key` it;
  instead it provides a witnessed **sorted-neighbor pair** `(lo, hi)` from the set with
  `lo < query < hi` and `lookup_key`s the *adjacency pair* `(lo, hi)` against a
  `sorted_adjacency` table the set AIR emits. Non-membership = "query strictly between
  two adjacent present elements," which is two range checks (also LogUp) plus one
  membership lookup of the adjacency edge. (We already have
  `src/membership_adjacency_air.rs` and `src/body_membership.rs` — the adjacency notion
  exists; it is just not wired to a LogUp bus.)
- For **nullifier double-spend** specifically (memory: nullifier enforced in
  `note_spending_air.rs:971`), the cleanest LogUp form is a **multiplicity-bounded
  send bus**: each spent nullifier is `send`-ed exactly once; a global cumulative-sum
  = 0 across the turn forest proves no nullifier is sent twice. This makes
  no-double-spend a **bus-balance** property — auditable, composable across AIRs, and
  it is the soundness tooth memory has been circling (the cross-AIR binding, not an
  in-VM hash).

This is the higher-leverage change for the crown jewel (circuit⟺protocol soundness):
a bus balance is a *clean* algebraic statement of "set semantics," far easier to
relate to the Lean denotation than a bespoke Poseidon accumulator.

### 2.3 Dispatch / effect selection (a structural win for the EffectVM)

The effect VM (`src/effect_vm_p3_air.rs`, `src/effect_action_air.rs`,
`src/action_dispatch` on the Lean side `Dregg2/Circuit/ActionDispatch.lean`) selects
one of 51 effect handlers per row. Without lookups this is typically encoded as a
big selector/one-hot with a constraint per handler. With a **`PermutationCheckBus`
("dispatch")** (the textbook use, `bus.rs:84-89` even names it `DISPATCH`), the
decoder AIR `send`s `(opcode, args)` and each handler AIR `receive`s the rows it owns;
the bus balance proves every emitted effect is handled exactly once and vice versa.
This is how you get a **multi-table effect VM** instead of one monolithic AIR — and it
is the natural substrate for the recursion/aggregation work (task #10).

---

## 3. Concrete design

### 3.1 Lean side (`Dregg2.Circuit.*`) — additive, small

`Dregg2/Circuit/Lookup.lean` already nails the *denotation*: `LookupConstraint` =
"evaluated tuple ∈ finite table" (`Lookup.lean:34-46`), `rangeCheck e k` with proved
meaning (`Lookup.lean:78-100`), and `CircuitL = gates + lookups` (`:53-64`). Keep all
of it. Add:

1. **A `kind` discriminator on the emitted lookup** so the Rust side knows
   Local-table vs Global-bus vs permutation-bus. Mirror `p3_lookup::Kind`:
   ```
   inductive LookupKind | localTable | globalBus (busName : String) | permBus (busName : String)
   ```
   Denotation is unchanged for `localTable`/`globalBus` (membership); `permBus` denotes
   multiset equality of sends vs receives (a `Multiset` equality — Mathlib has it).
   For range checks specifically, `rangeCheck` stays as is and lowers to a
   `globalBus "range"` (shared range table) — the *meaning* `∃ n<2^k` is the proof
   obligation, the *bus* is the enforcement, exactly as the module's docstring already
   says (`Lookup.lean:14-18`).

2. **A `count`/`count_weight` per emitted interaction** (matching
   `SymbolicInteraction.count` / `count_weight`, `builder.rs:24-38`). For a pure
   membership/range check this is the row's `is_active` selector and weight 1; the
   emitter can default it to `const 1` so existing `rangeCheck` callers are unchanged.

3. **Extend the descriptor emitter** (`Dregg2/Exec/CircuitEmit.lean`,
   `emitDescriptorJson`) to serialize lookups/buses into the JSON grammar the Rust
   parser reads (`lean_descriptor_air.rs:286-300` documents the current grammar). Add
   an optional `"lookups":[…]` array alongside the existing `"ranges":[…]`:
   ```
   {"kind":"range"|"bus"|"perm","bus":S,"fields":[<expr>,…],"count":<expr>,"weight":N}
   ```
   Keep `"ranges"` for now (back-compat); the lowering of `rangeCheck` → a `range`
   bus entry can be done in the emitter so both old and new prover paths see something
   sane. **No change to `Constraint`/`ConstraintSystem`/`satisfied`** — this is the
   same additive discipline `Lookup.lean` already established.

4. **(Proof obligation, the real Lean work):** a transport lemma that
   `CircuitL.satisfied` (gates ∧ all lookups-hold) is *equivalent to* "the emitted
   descriptor with its bus interactions is LogUp-satisfiable." We can only state the
   *denotational* half in Lean (membership/multiset-equality); the LogUp soundness
   itself (that a balanced bus ⇒ the multiset relation) is a property of the
   `p3-lookup` argument, i.e. an assumption at the Lean↔Rust seam, *the same status as
   the existing collision-resistance portals in `StateCommit.lean:55,154-156`.* Be
   honest about this in the module: LogUp is the *enforcement*, the membership is the
   *meaning*, and the bridge between them is a named cross-system portal (do **not**
   pretend Lean proves FRI/LogUp soundness).

### 3.2 Rust side (`circuit/src/`) — the bulk

A. **Carry interactions in `LeanDescriptor`.** Add `lookups: Vec<LeanLookup>` next to
   `ranges` (`lean_descriptor_air.rs:176-216`), where `LeanLookup` records
   `{kind, bus_name, fields: Vec<LeanExpr>, count: LeanExpr, weight: u32}`. Parse it in
   the JSON decoder (`parse_expr` infra already exists, `:394-410`).

B. **Implement `p3_lookup::InteractionBuilder` for the descriptor AIR's eval path.**
   In `LeanDescriptorAir::eval`, after emitting the arithmetic gates, for each
   `LeanLookup` call the matching bus helper: `LookupBus::lookup_key` / `table_entry`
   for range+membership, `PermutationCheckBus::send`/`receive` for dispatch
   (`bus.rs`). The builder generic must be widened from `AB: AirBuilder` to
   `AB: AirBuilder + InteractionBuilder` on the eval where lookups are present.
   `InteractionSymbolicBuilder` (`symbolic.rs:145`) and the batch-stark folders both
   implement `InteractionBuilder`, so this is purely a trait-bound widening.

C. **Add a lookup-aware prover entrypoint.** New fn `prove_lean_descriptor_batch`
   that builds a `StarkInstance { air, trace, public_values, lookups: Lookups::from_air(&air) }`
   and calls `p3_batch_stark::prove_batch` (`batch-stark/src/prover.rs:88`) instead of
   `p3_uni_stark::prove`. For the **range table** and **nullifier set**, emit them as
   *their own* `StarkInstance`s (a one-column table AIR providing `[0,2^w)` / the set
   members) sharing the bus with the query instances; the global cumulative sums
   balance to zero across the batch (`logup.rs:314-324`). `p3-batch-stark` +
   `p3-lookup` are **already optional deps** (`Cargo.toml:31-33`); gate the new path
   behind the existing `recursion` feature (or a new `lookups` feature) so the
   uni-stark golden path is untouched until cutover.

D. **Migrate the two costly gadgets:**
   - Replace the bit-decomposition range gates with range-bus `lookup_key`s. Keep
     bit-decomp behind a feature flag for one release as a differential oracle
     (prove the *same* `RangeSpec` both ways, assert both accept honest / reject
     wrapped). Do **not** delete it until the LogUp path is differentially validated —
     memory: "never downgrade a ProofTier; never match a buggy oracle." Here the
     oracle is our *own verified* bit-decomp, which is sound, so it's a legitimate
     differential.
   - Re-express `non_membership` / `quantified_absence` / nullifier as a
     non-membership/multiplicity bus (§2.2). This is a bigger change; stage it after
     range checks land and the batch-stark path is trusted.

### 3.3 What stays a portal (be honest)

The Lean side proves **meaning** (membership / multiset equality / range). It does
**not** prove that LogUp's balanced running sum implies that meaning — that is the
`p3-lookup` argument's soundness, a cross-system assumption at the same tier as the
`CH`/`compress` collision-resistance portals already in `StateCommit.lean`. Name it as
a portal (`LogUpEnforcesMembership`), don't launder it.

---

## 4. Efficiency wins, quantified

### 4.1 Range checks
- **Columns:** `Σ bits` boolean columns → **1 ext aux column per query AIR + 1 shared
  table**. For a 32-bit wire: 32 → ~1 (plus, if `bits` > table width, a handful of
  8-bit limbs, not 32 single bits).
- **Constraints:** `bits` booleanity + 1 recomposition → **3** (init/trans/final),
  amortized across *all* wires range-checked on the same bus.
- **Degree:** unchanged-ish — booleanity is degree 2; the LogUp transition constraint
  degree is `1 + max(deg num, deg denom)` (`logup.rs:339-367`), which for a
  single-field range lookup with `count` a selector is degree ~2-3. No worse, and the
  column count dominates FRI cost anyway.

### 4.2 Set membership / non-membership / nullifier
- **Prover work:** `O(|set|)` Poseidon hashing in the accumulator (degree-7 chain,
  `quantified_absence.rs:94-95`) → `O(|set| + |queries|)` field ops with **one batch
  inversion** (`logup.rs:534-538`). Poseidon-per-element disappears.
- **Soundness shape:** bespoke accumulator-quotient → **global bus balance = 0**, a
  single clean algebraic invariant. This is the better substrate for circuit⟺protocol
  soundness and for the no-double-spend tooth.

### 4.3 StateCommit sorted carrier (a subtle, real win)
`StateCommit.lean:24-25,172-177` hashes the untouched cells `S.sort (·≤·)` in
**canonical sorted order**. In-circuit, the prover *supplies* the sorted sequence; the
AIR currently trusts that it is a permutation of the actual carrier (the binding comes
from the digest, not from a proof of permutation). A **`PermutationCheckBus`** between
the unsorted carrier and the sorted trace would *prove* the sorted column is a genuine
permutation of the live cells (send unsorted, receive sorted, balance = 0), plus a
cheap "adjacent rows are ≤" range/order check. That closes the gap memory worries
about (anti-ghost: can't drop/duplicate a cell in the sorted view) **without** a
second Merkle pass. Stage this last; it interacts with the StateCommit proofs.

---

## 5. Lean vs Rust split (at a glance)

| change | side | size | risk |
|---|---|---|---|
| `LookupKind` + `count`/`weight` on emitted lookup | **Lean** (`Lookup.lean`, `CircuitEmit.lean`) | small, additive | low — denotation unchanged |
| serialize `"lookups"` into descriptor JSON | **Lean** (`CircuitEmit.lean`) | small | low — additive grammar |
| `LogUpEnforcesMembership` portal (named assumption) | **Lean** | tiny | honesty item, not a proof |
| `LeanLookup` in `LeanDescriptor` + JSON parse | **Rust** (`lean_descriptor_air.rs`) | small | low |
| impl `InteractionBuilder` in descriptor eval | **Rust** | medium | medium — trait-bound widening |
| `prove_lean_descriptor_batch` via `prove_batch` | **Rust** (new) | medium | medium — new prover path, feature-gated |
| range-bus replacing bit-decomp (differential first) | **Rust** | medium | low — own sound oracle |
| non-membership/nullifier bus | **Rust** | large | medium — restructures `non_membership`/`quantified_absence` |
| StateCommit permutation bus | **Rust** + StateCommit proofs | large | higher — touches commit proofs |

---

## 6. Recommended order (by leverage)

1. **Lean emitter** gains `kind`/`count`/`weight` + `"lookups"` JSON (unblocks
   everything; pure additive).
2. **Rust:** `LeanLookup` + `InteractionBuilder` impl + `prove_lean_descriptor_batch`
   through `p3-batch-stark` (feature-gated, uni-stark path untouched). Land **one**
   end-to-end test: a range-table AIR + a query AIR on one bus, honest proof verifies,
   wrapped/out-of-range value rejected (the differential against the existing
   bit-decomp `RangeSpec`).
3. **Range checks** migrate to the range bus; bit-decomp kept one release as
   differential oracle, then removed.
4. **Nullifier / non-membership** to a bus (the soundness-leverage change; coordinate
   with the cross-AIR binding tooth in memory).
5. **Dispatch bus** for the multi-table effect VM (sets up task #10
   recursion/aggregation).
6. **StateCommit permutation bus** last.

## 7. Open questions for ember

- **Prover cutover:** OK to make `p3-batch-stark` the prover for *all* descriptor AIRs
  (so single-table proofs are just a 1-instance batch), or keep `p3-uni-stark` for the
  no-lookup path and only use batch-stark when lookups are present? (Batch-stark adds a
  commit round; for lookup-free AIRs that's pure overhead. Recommend: dispatch on
  "has lookups.")
- **Range table strategy:** one global `[0,2^16)` table + 16-bit limbs, vs an
  `[0,2^8)` byte table + byte limbs (smaller table, more limbs). Byte table is the
  usual choice; confirm field/limb width against the BabyBear modulus we use.
- **Non-membership encoding:** sorted-adjacency lookup (range + edge membership) vs a
  multiplicity-bounded send bus for nullifiers specifically. They're for slightly
  different jobs (static blacklist vs dynamic spend set); we likely want both.
- This is the prover/proof-system DECISION memory keeps flagging as "ember's Mina
  wheelhouse" — `p3-batch-stark` is the plonky3-native answer; if we pivot toward
  pickles/kimchi for recursion, the *bus abstraction* still carries, but the prover
  entrypoint changes.
