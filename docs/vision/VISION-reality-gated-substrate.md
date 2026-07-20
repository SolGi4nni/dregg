# Vision — The Reality-Gated Substrate

**Frame (ember):** "think about what/how we could be building with a larger,
more ambitious vision — larger/longer individual swarm-cycles that move us
comprehensively AND swiftly toward the objective." Not incremental lane-by-lane.
AMBITIOUS SWEEPS.

**The objective, one line.** dregg's *entire semantic layer* — the full
constraint vocabulary, the `CellProgram` structure, the lowering, every program +
game + policy, the executor's whole admission path — is **Lean-authored, emitted,
and the deployed node provably routes through it.** No mirror. No LARP. The
deployed thing IS the proven thing, all the way down.

**The through-line this makes literally true (MEMORY.md):** *"a turn = the
exercise of an attenuable proof-carrying token over owned state, leaving a
receipt."* When the substrate is reality-gated, the token's exercise is
adjudicated by proven Lean, the state transition is a proven Lean function, and
the receipt attests a Lean-computed verdict. The sentence stops being a slogan and
becomes a theorem about the running node.

Status: **VISION + CAMPAIGN.** Read-only probe; nothing here is committed or
landed. Every "current state" claim is cited `file:line` against HEAD.

---

## 0. Where we stand — the slice, honestly

On 2026-07-18/19 we proved the pattern **on one slice** and wired it to reality.
This is real and it is the seed of everything below — but it is a *slice*, and the
honesty of this vision depends on saying exactly how thin.

**What LANDED (the reality-gate, `fc3f2dda8` + `fb6791fb0`):**

- **ONE Lean evaluator over the DEPLOYED substrate.**
  `metatheory/Dregg2/Exec/DeployedConstraint.lean:210` (`admits`) is authored over
  `[FieldElement;16]` registers + the unbounded-key heap, **unsigned 256-bit**
  field arithmetic, the `field_to_u64` low-64 lane, the genesis-nonce escape, the
  exact `ProgramError` variants — Mathlib-free (`:34` import discipline) so its
  initializer splices into the FFI archive.
- **It is `@[export]`'d and the node routes through it.**
  `DeployedConstraint.lean:413` (`@[export dregg_constraint_admits] admitsFFI`).
  The routing chain: `cell/src/program/eval.rs:280` consults
  `super::oracle::installed_oracle()` FIRST → `cell/src/program/oracle.rs:32`
  (the `ConstraintOracle` trait seam, wasm/zkVM-safe) →
  `exec-lean/src/constraint_oracle.rs:166` (`LeanConstraintOracle` marshals to
  wire, calls `dregg_lean_ffi::shadow_constraint_admits`) → the proven symbol →
  installed at native startup by `node/src/lib.rs::register_constraint_oracle`.
- **The reality-gate is PROVEN by a flip→change→revert→restore hand-link canary**
  (`fc3f2dda8` body): the linked binary's admission decision *is* the Lean source
  — recompile one Lean `.o`, re-splice, relink, same wire flips its verdict.
- **The two historic divergences were BUGS, reconciled to the sound deployed
  semantics:** `fieldGte` = unsigned 256-bit `Nat` compare (the old Exec copy's
  signed `Int` was wrong; canaried at `2^255`, `DeployedConstraint.lean:443`);
  heap `Immutable` first-write-free (`:156`, canaried `:449-457`).
- **Two games are Lean-sourced at the DATA layer + refined onto this evaluator.**
  `dregg-multiway-tug/src/program_loader.rs` and `dungeon-on-dregg/src/descent.rs:191`
  `include_str!` a Lean-emitted `CellProgram` (`metatheory/EmitMultiwayTugProgram.lean`,
  `metatheory/EmitDungeonProgram.lean`), drift-gated by `program/regen.sh`. Tug's
  `program_admits_legal_play_deployed` (`fb6791fb0`) proves every tooth's verdict
  on a legal play EQUALS `DeployedConstraint.admits .ok` — the refinement lands on
  the evaluator eval.rs actually calls.

**What this slice COVERS — and does not:**

| Axis | Covered by the slice | The rest (this campaign) |
|---|---|---|
| Constraint teeth | the **PURE** subset: ~11 `StateConstraint` + 11 `HeapAtom` variants | the ~40–60-variant alphabet's **context/witness** variants (`FieldGteHeight`, `SenderAuthorized`, `PreimageGate`, `RateLimit`, `Custom`, `Witnessed`, `AffineLe/Eq/DeltaLe`, `AllowedTransitions`, …) stay Rust-evaluated (`eval.rs:264`, still 2921 lines) |
| Program structure | none | `CellProgram` dispatch (None/Predicate/Cases/Circuit) + `TransitionGuard` default-deny — the stapleable-slot gate — still Rust (`cell/src/program/types.rs:6,62,84,970`) |
| Wire identity | none | the postcard-variant-index alphabet that IS the wire spec is a hand-maintained Rust enum |
| Deployed policies | **2** of ~10 (tug, dungeon) emit from Lean | automatafl, deos-apps, governed-namespace + the **6 with no Lean at any resolution**: faction, quest, spween, dungeon-non-descent (`SEMANTIC-LEAN-BOUNDARY.md:139-142`) |
| AIR lowering | none | `circuit/src/custom_leaf_lowering.rs` (the crypto pole — hard kinds have **no Lean at all**) |
| Circuit layout | none | ~600 hand-encoded layout constants; `layout_generated.rs` is `@generated` and **production reads it ZERO times** (`CIRCUIT-LEAN-BOUNDARY.md:1.1`) |
| Executor pipeline | the per-constraint decision only | dispatch → apply → fold → receipt; the admission path (`turn/src/executor/execute_tree.rs:1023`) is a thin caller only for the pure subset |

**And the slice introduced ONE new seam we must retire, not calcify:** the
marshaller `encode_constraint`/`build_wire` (`exec-lean/src/constraint_oracle.rs:30,91`)
is **38 hand-authored Rust arms** that "MUST match `parseConstraint`" by
doc-comment, pinned by a differential test. It is a small, real, new mirror. A
comprehensive vision has to eat it.

So: the pattern is proven, wired, and canaried on a thin slice. The rest of this
document is the ambitious, comprehensive, swift path to make it **the whole
substrate.**

---

## 1. The ambitious end-state — painted concretely

When this campaign is done, here is what an engineer sees when they open the tree:

**1. The semantic layer is a Lean library; Rust is a runtime.** `cell/src/program/`
no longer *defines* meaning. `StateConstraint` / `SimpleStateConstraint` /
`HeapAtom` / `TransitionCase` / `TransitionGuard` / `CellProgram` are **Lean
inductives over the one deployed substrate** (`DField`/`DInput`, extended). Their
serialization + the postcard-variant-index wire identity are **emitted from Lean**;
the Rust enum is `@generated` (or a thin codec generated from the emitted schema).
A new constraint variant is a Lean edit + regen — never a hand-appended Rust arm.

**2. Every admission decision is COMPUTED BY proven Lean.** The ~2921-line
`evaluate_constraint_full` match is **deleted**. `eval.rs` is a thin caller into
the exported `dregg_constraint_admits`, and the oracle returns `Some` for **every**
variant (the `None` fall-through is unreachable — there is nothing left in Rust to
fall through to). The `#assert_axioms`-clean `_iff` characterization theorems now
constrain the *deployed* decision, because they are theorems about the same
function the node runs. The "three sources that disagree" (`SEMANTIC-LEAN-BOUNDARY.md:2a`)
collapses to one.

**3. The whole admission PATH is Lean-sourced.** `CellProgram::evaluate`'s
top-level dispatch, the `Cases` guard selection, and the security-critical
**default-deny** (`is_method_dispatching`, the stapleable-slot gate) are Lean
functions, exported, and `execute_tree.rs`'s admission call is a thin router into
them. "Does the node admit this turn?" is, end to end, a proven Lean computation.

**4. Every deployed policy IS a Lean object.** All ~10 game/app/policy families —
tug, dungeon, automatafl, the deos-apps, governed-namespace, faction, quest,
spween, and the schema games — are **Lean `CellProgram` values**, emitted +
drift-gated, each **proven to refine its Lean model onto the complete
`DeployedConstraint`.** The airPlay↔`program()` gap (`SEMANTIC-LEAN-BOUNDARY.md:2b`,
"0 of 10 reach the deployed program") closes to **10 of 10**. Edit a threshold in
Lean, re-emit, and the deployed referee changes — with the correctness proof
riding along.

**5. Lean owns the circuit geometry.** The ~600 hand-encoded layout constants are
retired; `EmitLayoutManifest.lean` emits the full manifest + the proven-disjoint
group table + the PiLayout/fold ABI + the witness symbol table; production READS
the emit. A layout mistake is a compile-time impossibility, not a byte-pin that
fails after a human shipped the wrong offset. The `field_key`-guess class and the
completion-lane (limb-37/38) forgery class are **structurally unrepresentable**.

**6. The in-circuit enforcement provably matches the admission semantics.** The
AIR lowering (`custom_leaf_lowering.rs`, including the hard crypto kinds:
Poseidon2→lookup, Merkle-Lagrange, ChainedHash2to1, TableFunction) is a **proven
Lean function** whose per-program descriptor output carries a theorem: *the emitted
AIR admits iff the `CellProgram` semantics (item 2's `admits`) hold.* The
forged-trace-fold soundness hole reaches the proof.

**7. The turn is one proven pipeline.** The executor's apply/fold/receipt steps
are refined onto (or exported from) a Lean executor model; the remaining NAMED
hypotheses are discharged (or explicitly ride the labeled STARK floor per the
iterative-approximative method). The complete chain — **dispatch → admit → apply →
receipt** — is a machine-checked Lean pipeline the deployed node routes through.
The through-line is a theorem.

The shape of the invariant: **Rust keeps exactly the denotation** — field/Poseidon2
arithmetic, the wasm/zkVM guest, the p3 AIR interpreter, wire I/O, witness *value*
computation. **Lean owns everything ABOUT meaning** — every constraint, every
program, every layout fact, every "does it admit." That is the boundary law from
`CIRCUIT-LEAN-BOUNDARY.md:0`, realized across the *whole* substrate, not one file.

---

## 2. The leverage — the machinery that makes this ONE effort, not N

The slice did not just prove a point; it minted **reusable machinery**. The
ambitious move is fast *only if* we generalize that machinery FIRST, so the
remaining work is **application, not research** (MEMORY: *dispatch identified work
immediately; the pattern is proven → fan empowered agents*). Five reusable assets:

**L1 — The one deployed substrate (`DField` / `DInput` / `DHeapAtom`).** The single
highest-leverage asset. `DeployedConstraint.lean:49-106` already encodes deployed
state as Lean: unsigned 256-bit `Nat` field, `field_to_u64` low lane, 16 registers
+ heap `Option`s, the presence/nonce flags. **Every** subsequent evaluator,
program, and AIR is authored over this ONE model and composes for free. The
substrate unification the audits name as "the long pole" (`SEMANTIC-LEAN-BOUNDARY.md:5`)
is **half-built** — extending it once (to carry `EvalContext` + `WitnessBundle`) is
the leverage that makes Cycles A/C/E instantiation rather than N substrate fights.

**L2 — The generic reality-gate kit (oracle-seam + export + canary).** The slice
built the whole mechanism: `@[export]` + `lean_init.c` bridge + `build.rs` gate
target/symbol-probe/check-cfg + archive splice + a **wasm/zkVM-safe runtime trait
seam** (`cell/src/program/oracle.rs`, the `intent::IntentVerifiedGate` pattern) +
a native backend installed at startup + the **flip→change→revert→restore hand-link
canary**. This is now a *template* (instance #1 = `IntentVerifiedGate`, #2 =
`DeployedConstraint`). Generalize it into a declarable framework: *name a seam,
write the Lean decision procedure, wire the backend* — and the FFI dance, install,
and canary come for free. Then Cycles A/B mint new exported evaluators cheaply.

**L3 — The emit + regen + drift-gate harness.** `check-descriptor-drift.sh`,
`scripts/emit_descriptors.py`, `EmitAllJsonV2.lean`, `EmitLayoutManifest.lean`,
and the per-game `program/regen.sh` already turn a Lean value into an
`include_str!`'d artifact with a regenerate-and-diff gate. This is the
staged-additive-then-cutover template that keeps the tree green while the source of
truth relocates. Every program (Cycle C), schema (Cycle B), and layout table
(Cycle D) plugs into the **same** harness — one emit path, N artifacts.

**L4 — The differential + canary falsifier factory.** `deployed_constraint_probe` /
`deployed_constraint_differential` fuzz the exported Lean decision against Rust
across the subset **including the known-divergent boundaries** (field modulus,
sign boundary, absent-vs-zero, genesis nonce). This is the falsifier every ported
tooth ships with — it caught the two real bugs. Generalize: a boundary-aware
differential generator so each new variant/program arrives with its own adversarial
gate, not a hand-written one.

**L5 — The refinement bridge (`marshal-model-into-DInput`, prove-verdict-equal).**
Tug's `tugRegIdx`/`tugSlots`/`Constraint.toDC` + `program_admits_legal_play_deployed`
(`fb6791fb0`) is the template for landing any game's *existing* Lean model onto the
*one* deployed evaluator: marshal the symbolic model into a `DInput`, prove the
local verdict equals `DeployedConstraint.admits`. **One target evaluator, N game
refinements** — Cycle C is this bridge applied ~10 times, fan-outable across a
swarm because the pattern is fixed.

**The leverage thesis:** build L1–L5 into first-class kits at the head of the
campaign, and the body of the campaign is *instantiation*. That is what turns "N
bespoke multi-month efforts" into "a few coordinated sweeps."

---

## 3. The big swarm-cycles

Six ambitious cycles. Each is a **long, coordinated sweep** (a coherent front with
many parallel lanes under one integrator), not a lane. Stated as: what it
DELIVERS, what Rust it DELETES, and how it composes.

### Cycle A — The complete evaluator (the keystone)

**Sweep:** extend `DeployedConstraint` from the pure subset to the **entire
constraint vocabulary**. Widen `DInput` (L1) to carry the marshalled `EvalContext`
+ `WitnessBundle`; author the context/witness teeth in Lean (`FieldGteHeight`,
`SenderAuthorized`, `PreimageGate`, `RateLimit`, `AffineLe/Eq/DeltaLe`,
`AllowedTransitions`, and the `Custom`/`Witnessed` dispatch); export them through
the L2 kit; widen the oracle so `admits` returns `Some` for **all** variants.

**Delivers:** the *entire per-constraint admission decision* computed by proven
Lean. The `_iff` characterization theorems constrain the deployed decision.
`SEMANTIC-LEAN-BOUNDARY.md:2a` (three disagreeing sources) collapses to one.

**Deletes:** the ~2921-line `evaluate_constraint_full` / `evaluate_simple_constraint`
/ `evaluate_heap_atom` match arms (`eval.rs`). `eval.rs` becomes a thin caller;
the oracle `None` branch becomes unreachable.

**Composes:** unblocks Cycle C (games refine onto the *complete* evaluator, not a
subset) and Cycle F (the dungeon Int→Nat bridge, BLOCKED today by the very
signed/unsigned divergence, is unblocked once the non-pure variants are covered —
`fb6791fb0` names this). This is the **highest-value, most load-bearing** object;
it is the keystone.

**Genuinely hard, named:** some `Custom` variants dispatch to *registered*
verifiers (crypto). Those reach the same undischarged crypto floor and either get a
Lean model of the verifier registry or stay a NAMED seam — not every variant
collapses to a self-contained pure function, and that boundary must be stated, not
LARPed.

### Cycle B — The program structure + wire identity (kill the marshaller)

**Sweep:** move the `CellProgram` top-level dispatch (None/Predicate/Cases/Circuit),
`TransitionCase`/`TransitionGuard`, and the **default-deny** gate into Lean,
exported (sub-sweep **B0 = default-deny reality-gate first** — small,
security-critical, retires the stapleable-slot hole class at the deployed object).
Emit the **constraint-vocabulary SCHEMA** (the tag↔postcard-index table) from Lean;
**generate** the Rust enum codec AND the L2 marshaller wire codec from it.

**Delivers:** the whole admission *path* — structure, dispatch, default-deny, wire
identity — Lean-sourced. **The new marshaller seam (§0) is eliminated by
construction:** both the Rust encoder and the Lean `parseConstraint` are generated
from one emitted schema, so they cannot drift.

**Deletes:** hand-maintained `enum StateConstraint` append-by-hand (`types.rs:970`);
the 38 hand-authored marshaller arms (`constraint_oracle.rs`); the Rust default-deny
`match`.

**Composes:** feeds Cycle C (programs are authored against the Lean structure) and
hardens Cycle A (the exported evaluator's inputs are now a generated wire, not a
hand contract). Runs largely parallel to A; the schema-emit lands *after* A widens
the covered variant set so the generated codec covers everything.

### Cycle C — Every deployed program emitted + refined (the fan-out)

**Sweep:** author **every** game/app/policy as a Lean `CellProgram` value, emit +
drift-gate (L3), `include_str!` it, and prove each refines its Lean model onto the
complete `DeployedConstraint` via the L5 bridge. The **6 policies with no Lean at
any resolution** (faction, quest, spween, dungeon-non-descent) get a Lean model
authored first; the deos-apps + governed-namespace **re-authored mirrors are
converted into emitted values — deleting the mirror** (not blessing it).

**Delivers:** every deployed referee IS a Lean object; the airPlay↔`program()` gap
closes **10 of 10** (`SEMANTIC-LEAN-BOUNDARY.md:2b`). Every policy's correctness is
machine-checked to the object the node runs.

**Deletes:** every hand-rolled `CellProgram::Cases`/`Predicate` author site
(`SEMANTIC-LEAN-BOUNDARY.md:58` census); the `Dregg2/Apps/*` re-authored mirrors.

**Composes:** DEPENDS on A (refine onto the complete evaluator) + B (the structure/
schema). **This is the swarm cycle** — one fixed pattern applied ~10 times,
fan-outable wide because it is application, not research. Model-authoring for the
6 no-Lean policies can start in Wave 1.

### Cycle D — Lean owns the circuit geometry (independent front)

**Sweep:** execute `CIRCUIT-LEAN-BOUNDARY.md` Steps 1–8. Wire the already-`@generated`
`layout_generated.rs` into production (Step 1); emit + read the octet→register map,
killing the `field_key` class (Step 2, the exemplar retired); emit the
**proven-disjoint** group table (`RotatedLayout.groupTable`, `RotatedLayout.lean:119-121`),
making the completion-lane forgery **unrepresentable** (Step 3); PiLayout/fold ABI
(Step 5); the 231 weld-site symbol table (Step 6); the 15 witness generators (Step 7).

**Delivers:** zero hand-encoded circuit layout; the two historic soundness/liveness
bug classes structurally closed; a layout change is a one-line Lean edit.

**Deletes:** ~600 hand layout constants; ~26 byte-pins + ~3 drift-guards (each in
the commit that makes it vacuous — never before).

**Composes:** **fully orthogonal to A/B/C** — different files, different lock
domain — so it runs as its own concurrent swarm from day one. Feeds Cycle E (the
lowering emits *into* this geometry).

### Cycle E — The AIR lowering in Lean (the crypto pole)

**Sweep:** author `lower_cellprogram`/`gate_body` — **including the hard kinds**
(Poseidon2→TID_P2 lookup, Merkle-Lagrange child reconstruction, ChainedHash2to1
copy-forward, TableFunction bivariate-Lagrange) — as a **proven Lean function**
whose output is the emitted descriptor, carrying the theorem *the emitted AIR
admits iff the `CellProgram` semantics (Cycle A's `admits`) hold.*

**Delivers:** the deepest cryptographic dead-end closed — in-circuit enforcement
provably matches admission; forged-trace-fold soundness reaches the proof.

**Deletes:** `custom_leaf_lowering.rs` (858 lines) + the two duplicate re-impls
(`note_spend_witness.rs`, `shielded_spend_leaf_adapter.rs`).

**Composes:** DEPENDS on A (needs `admits` as the semantics the AIR must match) +
benefits from D (emits into the Lean-owned geometry). **The hardest cycle** —
genuine circuit-authoring-in-Lean for kinds that have **no Lean today**, adjacent
to the FRI-soundness frontier. Start the research spike in Wave 1 so it is not a
serial tail. Feeds Cycle F's soundness.

### Cycle F — The whole-turn weld (the capstone)

**Sweep:** refine the executor's dispatch/apply/fold/receipt onto (or export from)
a Lean executor model, so the complete turn is one proven Lean pipeline the node
routes through. Discharge the remaining NAMED hypotheses: `MerkleSound`/`AirSpec`
(the deployed Poseidon2 STARK — consuming Cycle E and the FRI-soundness campaign),
tug's reverse direction (`admitted ⇒ legal` via airPlay membership), the dungeon
Int→Nat bridge (unblocked by Cycle A).

**Delivers:** *"a turn = an attenuable proof-carrying token over owned state,
leaving a receipt"* is machine-checked end to end at the deployed object.

**Composes:** the capstone — DEPENDS on A + B + C and consumes E. **Honest floor:**
the STARK soundness is its own frontier (no adversary model; the "57 calculator bits" was an
informal estimate — proven deployed readings: commit ε_C **51 bits**
`FriDeployedHeightPairing.deployed_wrap_commitBits`, query **~31.5 bits** `DeployedProximitySoundness`;
`project-fri-soundness-reality`); F welds the *architecture* conditionally on that
labeled floor (the iterative-approximative method) and names it as a placeholder,
never as discharged.

---

## 4. The guardrails — today's pitfalls, baked into the cycle design

Every failure mode the LARP audit found is a standing tripwire. These are not
advice; they are the **definition-of-done** for every cycle.

**G1 — NO MIRROR. Collapse-to-one, or it doesn't count.** The #1 disease
(`SEMANTIC-LEAN-BOUNDARY.md:B`) is a parallel Lean copy blessed by a differential.
**Rule:** the Lean object is THE source; the Rust hand-copy is **DELETED** (or
generated from Lean), not pinned. A cycle whose DoD is "the differential is green"
has FAILED; the DoD is "the Rust hand-copy is gone and the node computes via the
Lean symbol." The slice passes this (one evaluator, exported, routed); every cycle
must.

**G2 — NO LARP. The title must equal the theorem statement.** No
"CONNECTED"/"deployed"/"proven-correct" in a header unless an `@[export]` +
reality-gate canary backs it (`GAME-PROOF-LARP-AUDIT.md` demoted three such
headers; `fb6791fb0` fixed the tug `Iff.rfl` tautology + its false "reds on edit"
canary). **Rule:** every cycle names its remaining hypotheses explicitly, and the
adversarial audit reads theorem *statements*, not titles. Vacuous/tautological
theorems are forbidden by prompt.

**G3 — PROVE OVER THE DEPLOYED SUBSTRATE, or NAME the bridge.** Never quantify a
"soundness" theorem over an abstraction the deployment never instantiates (Exec
`Value` records, name-keyed maps). **Rule:** land the proof on `DInput`/`DField`
(L1), or explicitly NAME the marshalling bridge as the remaining seam (as tug's
refinement and the dungeon inversions honestly do). Cycle C's every refinement must
reach the deployed substrate, not a private model.

**G4 — NO GREENFIELD THEATER.** dregg is greenfield; nothing is deployed
(`feedback-no-greenfield-migration-theater`). **Rule:** the drift gate is
*scaffolding you remove* when you delete the Rust copy — not an end-state. Do not
dress cycles in byte-identical/flag-day/consensus-visible costume. Make the right
proven-Lean object BE the object + delete the debt. The only real constraints are
**correctness, internal consistency, and the wasm/zkVM build.**

**G5 — RETIRE THE NEW MARSHALLER SEAM; don't calcify it.** The reality-gate's
hand-authored wire codec (§0) is a small new mirror. **Rule:** Cycle B eliminates
it by generating both sides from one emitted schema. It must not become a permanent
pinned mirror — a mirror born of the fix is still a mirror.

**G6 — BUILD-SAFETY IS LAW, not theater.** `dregg-cell` compiles to wasm32 + the
SP1 zkVM guest; **neither can link the archive** (`oracle.rs:8-15`). **Rule:** the
runtime trait-seam architecture is non-negotiable — never a hard FFI edge from
cell/turn. Every cycle preserves both builds; the native backend is the only place
the archive links.

**G7 — SUBSTRATE RULINGS ARE EMBER'S CALLS, canaried at the boundary.** The
unsigned-vs-signed and present-zero-vs-absent edges are where the copies diverged —
*semantic decisions*, not mechanical ports (`SEMANTIC-LEAN-BOUNDARY.md:5`).
**Rule:** each divergence is surfaced with both behaviors, reconciled to the SOUND
deployed semantics, and `#guard`-canaried at the exact boundary (as
`DeployedConstraint` did for `2^255` and heap-immutable first-write).

**G8 — SWARM DISCIPLINE (from the record).** Build-lock contention caps width
(`feedback-build-lock-contention`): fan READ-ONLY/Lean lanes wide, keep BUILD lanes
~1–2 per target, use separate `CARGO_TARGET_DIR`/persvati/hbox-lake, integrator =
single lock owner, build the WHOLE tree after shared-struct changes. Ground-truth
into every lane prompt (real signatures, absolute paths) or lanes build a mirror.
Green + self-reported "done" is NOT verification — the gate is the adversarial audit
+ your own whole-tree build.

---

## 5. The sequencing — the swift comprehensive route

The critical path is **A → C → F**, with **E** as the parallel hard crypto pole
feeding F, **B** feeding C, and **D** running independently alongside from day one.

**Wave 0 — Mint the kits (short, front-loaded).** Generalize L1–L5 into first-class
machinery: extend the substrate to carry context/witness (L1); the declarable
reality-gate framework (L2); the uniform emit/regen harness (L3); the boundary-aware
differential generator (L4); the refinement-bridge template (L5). *Everything after
is instantiation.* Also: kick off the Cycle E research spike and Cycle C
model-authoring for the 6 no-Lean policies now, so the hard/long tails start early.

**Wave 1 — Three concurrent fronts.**
- **Front A** (keystone): the complete evaluator. Highest value, unblocks the most.
- **Front B** (structure + schema + marshaller-kill): sub-sweep **B0 = default-deny
  reality-gate first** (small, security-critical). Schema-emit lands after A widens
  the variant set.
- **Front D** (layout): fully independent swarm, own lock domain, CIRCUIT Steps 1–3
  first (retire the exemplar + the historic soundness bug), then 4–8.

**Wave 2 — Fan-out (after A + B).**
- **Cycle C**: every program emitted + refined onto the complete evaluator. Wide
  swarm; fixed pattern; application not research.

**Wave 3 — The hard poles (after A + D).**
- **Cycle E**: the AIR lowering in Lean (the crypto pole; its spike began Wave 0).
- **Cycle F**: the whole-turn weld + hypothesis discharge — the capstone,
  consuming E, conditional on the labeled STARK floor.

**The unlock chain, explicitly:** A unlocks C's honest refinements + F's dungeon
bridge; B unlocks C's structure + kills the marshaller; D is standalone value + the
geometry E emits into; E needs A's semantics + feeds F; F makes the through-line a
theorem. **Swiftness comes from:** (1) generalizing the kit before instantiating,
(2) running A/B/D as three concurrent fronts, (3) fanning C wide, (4) starting E's
and C's long tails in Wave 0 so they are not a serial tail.

---

## 6. What is genuinely hard — stated plainly

This is bold, and honesty is the point (`feedback-integrator-must-not-compress-scope`):

- **Not every constraint collapses to a pure Lean function.** The `Custom`/`Witnessed`
  variants dispatch to registered crypto verifiers; they reach the undischarged
  crypto floor. Cycle A covers the decidable teeth and NAMES the verifier-dispatch
  boundary — it does not pretend a registered ML-DSA check is a `#guard`.
- **Cycle E is research, not a port.** The hard AIR kinds (Merkle-Lagrange,
  Poseidon2→lookup, chained-hash, table-function) have **no Lean today**; authoring
  them as *proven* functions is circuit-authoring-in-Lean adjacent to the FRI
  frontier — months, honestly.
- **Cycle F rides the STARK floor.** "The whole turn is proven" is *conditional* on
  the deployed STARK soundness (no adversary model; the "57 calculator bits" was an informal
  estimate — proven deployed readings: commit ε_C **51 bits**
  `FriDeployedHeightPairing.deployed_wrap_commitBits`, query **~31.5 bits** `DeployedProximitySoundness`;
  `project-fri-soundness-reality`), which is its own campaign. F welds the
  architecture conditionally and labels the floor — never asserts it discharged.
- **The context/witness marshalling grows the wire.** For variants that read live
  node state (chain height, sender identity), the L1 substrate and the L2 wire get
  bigger; the marshaller may not fully vanish for those — the generated-codec win
  (G5) is cleanest for the pure/structural subset.
- **Substrate rulings are real behavior decisions.** unsigned-vs-signed,
  present-zero-vs-absent — ember must rule on each edge; these are the exact points
  where a careless port re-introduces a divergence bug.

None of this shrinks the vision. It sets the resolution honestly: the
**architecture** is comprehensively reachable and the **pattern is proven**; the
two hard poles (E, F) carry real research and a labeled floor, and the campaign is
designed so that everything except those poles is fan-outable instantiation.

---

## 7. One-paragraph brief (for a launch)

We proved the reality-gate on a slice: one Lean constraint evaluator
(`DeployedConstraint.lean`), `@[export]`'d, that the deployed node's admission
decision provably routes through — canaried by a flip→change→revert hand-link, with
two historic divergence bugs reconciled to the sound deployed semantics. That slice
minted reusable machinery (the deployed substrate, the oracle-seam+canary kit, the
emit/regen harness, the differential factory, the refinement bridge). The ambitious
move is to generalize that machinery once, then run six coordinated sweeps that make
dregg's **entire** semantic layer — every constraint, the program structure, every
deployed policy, the circuit geometry, the AIR lowering, and the whole turn
pipeline — Lean-authored, emitted, and provably routed-through, deleting the Rust
mirrors as we go, so "the deployed thing IS the proven thing" holds all the way
down and the through-line becomes a theorem about the running node.

*(◕‿◕) the substrate stops being a shadow and becomes the source.*

---

*Prepared read-only, 2026-07-19. Current-state claims cited `file:line`@HEAD; the
rot maps this builds on: `docs/audit/GAME-PROOF-LARP-AUDIT.md`,
`docs/audit/SEMANTIC-LEAN-BOUNDARY.md`, `docs/audit/CIRCUIT-LEAN-BOUNDARY.md`. The
landed slice: `fc3f2dda8` (reality-gate) + `fb6791fb0` (refinement).*
