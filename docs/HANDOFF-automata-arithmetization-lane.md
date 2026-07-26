# HANDOFF — the automata-arithmetization / proof-composing lane

**Parked 2026-07-26, clean.** Nothing half-applied, nothing uncommitted, every claim in-file matches
what was actually measured or proved. This doc is written so the lane can be picked up cold.

**This lane is NOT release-critical.** It is compiler/circuit infrastructure. The Sunday Discord
dungeon does not depend on any of it. If you are here to ship the bot, you can ignore this entire
document — that is the honest scoping, and it is why the lane was parked rather than pushed.

---

## What the lane was about

It started as: *improve the compiler/metaprogramming stack, and re-derive the hand-maintained
circuits automatically without regressing performance or assurance.* It ended as three joined
things:

1. **A certified compiler** — a spec becomes a live descriptor *and* its machine-checked soundness.
2. **A certified optimizer** — peephole passes proven to preserve `Satisfied2`, reaching descriptors
   we actually ship.
3. **Composable tiny automata** — many small machines fused into one proof-carrying circuit, with a
   measured cost law.

---

## What landed (all committed, all with `#assert_all_clean` gates)

### Compiler + optimizer
- `Dregg2/Crypto/Arith/ArithmetizeTypedPredicate.lean` — the elaborator: spec → emitted
  `EffectVmDescriptor2` + proof.
- `Dregg2/Metatheory/TypedLinearPredicateOptimizerCost.lean` — `optimize_descriptor_cost_nonincrease`
  (∀-program, descriptor-level) with semantic companions so the bound cannot be bought by weakening
  the circuit. Strict result: `descriptor_shareAnd_exact_saving`, mutation-canaried.
- `Dregg2/Metatheory/TypedLinearPredicateOptimizedWiring.lean` — the live compiler finally *calls*
  the certified optimizer; `sound`/`canonical_iff`/`public_sound` transported.
- The peephole family (`Dregg2/Circuit/Peephole*.lean`, ~15 modules). The one that matters:
  **`PeepholeBaseGateScan.lean`** — certified `SatisfiabilityPreservation` on **real deployed
  descriptors**, ∀-member across the bare cohort, with the deployed constructors identified to the
  recogniser's *by `rfl`*.

### Deployed circuits proving their specs
- `Dregg2/Crypto/PrivateGraphRewriteAirBridge.lean` — `Satisfied2 ⟹ ∃w, Accepts` for the shipped
  hypergraph-rewrite AIR. Spec byte-untouched, arbitrary nonempty trace.
- `Dregg2/Crypto/HierarchicalGraphFrame.lean` — the frame converse, unconditional at the deployed
  resolution, escape priced as a `RomForgery` (not a free `∨ ∃ collision`).

### Guards → circuits (the proof-composing half)
- `Dregg2/Crypto/HandlebarsGuardDecision.lean` — templater guards are decidable; **caught two real
  refactor bugs** with separating words exhibited.
- `Dregg2/Crypto/GuardToAutomatonCircuit.lean` — the pipeline: guard → DFA (the Deriv tower's
  ≅-class frontier *is* a DFA) → witnessed circuit. `guardDfa_decides` + `nodb_pipeline`.
- `Dregg2/Crypto/InjectionGuardCircuit.lean` — same pipeline at the byte alphabet, both poles fired.

### Composition + cost
- `Dregg2/Circuit/Emit/TinyAutomataSatisfiable.lean` — `prodRunWit_satisfies` (witnessed, general in
  k). **Product-first area `3·|w|`, independent of k; 0 nonlinear mults.** Four automata cost the
  same circuit as one.
- `Dregg2/Circuit/Emit/TinyAutomataPacked.lean` — `s` steps per row; `packWit_satisfies`; `s=1` is
  byte-identical to the unpacked descriptor.

---

## The four facts a successor most needs

1. **The deployed run-table carrier cannot prove a word longer than 128 symbols.**
   `MAX_EXACT_PUBLIC_ROWS = 128` (`circuit/src/descriptor_ir2.rs:378`), enforced **per table**
   (`:1487`). Not per-k — an earlier reading of mine divided by k and was wrong.
   Packing lifts it: `⌈n/s⌉ ≤ 128` ⇒ **n ≤ 128·s**. `s=8` is what brings n=1024 into reach.

2. **The two shapes have opposite performance profiles.** The shared-table shape (2 instances,
   `sem:"range"`) is Merkle-bound (~90%). The **deployed** per-row carrier is **DFT- and
   instance-bound** (Merkle ~8.4%), and pays ~0.11 ms per declared row. Any "make it faster" work
   must say which shape it optimises. See the retraction at the top of
   `circuit/tests/tiny_automata_prove_time_attack.rs`.

3. **`costOf.forcedTraceRows` WAS wrong for multi-lookup descriptors — FIXED 2026-07-26.** It
   assumed `lookupCount = 1` and reported the declared row count; a packed descriptor has
   `lookupCount = s`, so the honest trace length is `declaredRows / s`. The model (not the call
   sites) was repaired in `TinyAutomataCompose` §1a: the field is now a three-valued
   `ForcedRows := unpinned | pinned n | contradictory` computed as `declaredRows / lookupCount` per
   table and `meet`-ed across tables, and `DescCost.area : Option Nat`. `costOf_forced_sound` proves
   that for any descriptor with a `Satisfied2Public` witness the published number is `pinned` at
   that trace's *actual* row count — the field can no longer silently lie.
   **The re-check of every consumer is DONE** (28 `#guard` statements referencing `costOf` across 8 Lean files — an earlier count of "12 sites across 7 files" undercounted and was corrected by an adversarial verify;
   `costOf`/`forcedTraceRows`/`area` have no Rust or doc consumers). Exactly ONE published number
   was wrong: `TinyAutomataPacked`'s `costOf (packK4 s)` reported `forcedTraceRows = 8` at every
   `s ∈ {1,2,4,8}`; it now reads `pinned 8/4/2/1` and its area `some 24/20/18/17`, agreeing with the
   four witnesses' own trace lengths. Every other consumer is single-lookup-per-table
   (`tableRoutingDesc`, `lanesDesc`) or declares no `exactPublicRows` table at all
   (`attestedInstance`, `weldInstance`, `dfaRoutingDesc` → `unpinned`, previously the sentinel `0`).

4. **The standing gate that made this lane trustworthy:** never quote a cost for a descriptor
   without a `Satisfied2Public` witness. An entire cost-law headline was retracted for measuring
   descriptors no prover can satisfy (the lanes route needs a common Eulerian word; the components'
   Eulerian sets were disjoint).

---

## Next steps, in the order I would take them

1. ~~Re-audit `costOf` consumers~~ — **DONE 2026-07-26**, see fact 3. One wrong number found
   and restated; the model itself now carries `costOf_forced_sound`.
2. **Wait for the `MapOp` denotation move** — another terminal is building
   `Dregg2/Circuit/MapKindImtGates.lean` (`holdsAtS`/`writesToMerkleS`). When it lands, the
   automaton-binding in `AttestedAutomatonWeld8.lean` becomes a *deployed* security property for
   free. **Acceptance test already written as a falsifier:** `weld_completion_lanes_free` must flip
   from provable to refutable. Currently the weld is wire-only — `MapOp.holdsAt` reads
   `(m.root 0)`, lane 0 only.
3. **Make a shipped guard actually proven.** `zkoracle-prove/src/injection.rs` re-implements the
   matcher in Rust rather than calling an `@[export]` of the Lean, so `InjectionGuardCircuit` proves
   the *Lean mirror*, not the shipped bytes. Two routes: `@[export]` the Lean `derives`, or **ship
   the emitted table as data and reduce the Rust to a table walk** — `bytesDfa`/`bytesRunDesc` are
   exactly what that second route consumes.
4. **`RowSemantics.committedRows`** — the named IR gap (prototype in
   `Dregg2/Circuit/Emit/CommittedRowsSemantics.lean`, design in
   `docs/DESIGN-committed-rows-semantics.md`). ⚠ `TableDef.publicContentsFaithful` falls through to
   `True` for every non-`exactPublicRows` semantics, so a new constructor inherits **no** contents
   obligation and compiles clean — constructor and obligation must land together.

---

## Adjacent finding: AI × the dungeon (not this lane's work, but scoped here so it isn't lost)

**They have never been wired together.** The LLM lives entirely in the `/hermes` path
(`discord-bot/src/{hermes_channel,start,key}.rs`). All five dungeon/game commands — `descent`,
`native_descent`, `overworld`, `rpg_world`, `dungeon_offering` — have **zero** LLM/Brain references.

**Hermes is not required to connect them.** `discord-bot/src/llm_provider.rs` is a plain BYO
multi-provider abstraction (Anthropic / OpenAI / OpenRouter / Kimi / DeepSeek) exposing just
"endpoint + auth + default model" for a single chat turn. Hermes is one *consumer* of it, not a
gateway to it. A dungeon command can call the provider directly.

Deliberately **not** started: the release surface is another terminal's active area, and this was
raised at the end of a sprint. Recorded so the option is cheap to pick up, not so it looks endorsed.
