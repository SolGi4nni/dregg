# Automatafl: wiring the deployed game to the Lean-authored AIR (and shipping a complete zk/trustless/distributed match)

Status: DESIGN + scope, written before the cutover; the cutover has SINCE HAPPENED. This document
maps the deployed path against ground truth (file:line @ HEAD 67b3d8a38), states the loader/
witness-gen/repoint/deletion plan, flags the drift that must be repaired first,
and gives an ordered build plan. It is authoritative over any stale memory; where
it and the code disagree, the code wins.

⚑ 2026-07-25 — §4.3's deletion step is DONE, and went further than planned. `f44e26e7b` deleted the
hand-written Rust AIR (`src/air.rs`, `src/moves.rs`, `src/builder.rs`) and its proving tests;
`e3c5bb8b9` then also deleted `src/reference.rs`, which §4.3 planned to KEEP — the rules-conformance
audit found the transcribed oracle divergent from the Creator-Approved ruleset, so every transition
now routes to `@[export] dregg_automatafl_rules` with no Rust fallback. Read the file references
below as a snapshot of the pre-cutover tree.

House-law framing (CLAUDE.md #1): the automatafl AIR is authored in Lean and Rust
must only CALL IN. Today the deployed match proves through a **hand-written Rust
AIR**. This is the debt. This design repoints the deployed proof at the
Lean-emitted descriptor so the object that is PROVEN becomes the object that is
DEPLOYED — then the Rust AIR is deleted.

---

## 0. TL;DR

- **Deployed path is real and D1-only.** A played `AutomataflMatch` lowers, one
  Custom `LeafBundle` per turn, each proving `boards[i+1] == automaton_step(boards[i])`
  through the hand-written Rust AIR (`dregg-automatafl/src/{air,moves,builder}.rs`),
  folds via `fold_match → prove_turn_chain_recursive` into one `WholeChainProof`,
  self-attests through the light client, and ranks on the `ugc-dregg`
  proof-carrying board storing no moves. The board is **n = 5** in tests / **n = 11**
  in the stock game.
- **There is a live descriptor DECODER but no dispatch arm for automatafl, and the
  leaf-fold path does not consume descriptors at all — it consumes `CellProgram`s.**
  So "wire the loader" is really two gaps: (a) register automatafl in
  `descriptor_by_name`, and (b) add a **descriptor-native leaf** so a fold turn can
  be built from an `EffectVmDescriptor2` + raw trace instead of a `CellProgram`.
- **Three-way divergence must be repaired first (STEP).** PROVEN (Lean
  `automataflStepDesc`) = 254 wide / 20 PIs / 405 constraints / **0 lookups**,
  packed-felt board commitment. ARTIFACT on disk (`automatafl-step.json`) = 269 / 32 /
  418 / **2 Merkle lookups** — a **stale** emission. DEPLOYED (Rust `build_d1`) = 32
  PIs / 2 board-root Merkle lookups — matches the stale artifact, not the Lean. The
  Lean refinement proves the 254/20 object; nothing deployed uses it.
- **Board size is a blocking gap.** Lean emits board-size **n = 2** only. Deployed
  is n = 5 / n = 11. The Lean layout is n-parametric (`automataflStepDescN n`,
  "descN 11 tiles clean") but only descN 2 is byte-pinned + routed. The deployed-size
  descriptor must be emitted + pinned before it can back the deployed match.
- **Witness-gen is Rust, trusted, fail-closed — and it is the crux.** No Lean trace
  generator exists (only the SAT ⇒ semantics soundness direction). The current
  `builder.rs::automaton_gadget` already computes the intermediate column values, but
  for the diverged 269/32 layout. The front-end columns (0..252) were authored to
  mirror the Rust allocation ("byte-identical to the frozen absolute layout"); only
  the board-commitment TAIL diverges. So the witness-gen is "reuse the front-end
  fill, rewrite the tail," not a from-scratch rebuild.
- **Cutover-deletes-first is a prerequisite for RESOLVE, not for STEP.** The STEP
  descriptor is clean (just stale in width). The RESOLVE descriptor carries
  STAGED-ADDITIVE superseded columns (`cMidV2`/`cMidV3`/… — the buggy-board
  corrections landed beside the old columns). Wiring resolve cleanly requires
  deleting the superseded columns and re-pinning first. Since the deployed match
  folds D1 only, this does not block the STEP cutover.
- **Trustless/distributed completeness is partial.** The fold → light-client →
  proof-carrying-board path exists and is real at the ARCHITECTURE resolution (it
  inherits the undischarged FRI/STARK floor — not cryptographic soundness). The
  multiplayer surface exists (web/Discord/TG/WeChat, commit→reveal→resolve + sealed
  fog). But the proof attests only the **automaton step**, never the players'
  **resolved moves** — the RESOLVE descriptor that proves real 2-player turns is
  emitted but NOT folded. A complete match proof needs resolve folded and its
  fold-join PI seam discharged.

---

## 1. The deployed path (accurate)

### 1.1 Play → leaves → fold → board

```
AutomataflMatch { start: Board(n=5|11), turns }             dreggnet-game-board/src/lib.rs:276
  .leaves()                                                  lib.rs:296
    for each turn i:
      let b = build_d1_honest(&boards[i]);                   dregg-automatafl/src/air.rs:770
      if !b.air_accepts() { return D1Refused }               (in-memory constraint check, NOT the STARK)
      LeafBundle {
        program:        b.cellprogram(),                     builder.rs:757  (CellProgram::new(descriptor, 1))
        witness_values: b.trace_witness(rows),               builder.rs:762  (HashMap<col-name, Vec<Felt>>)
        num_rows:       2,
        public_inputs:  b.pis.clone(),                       32 felts: [old8 ‖ new8 ‖ board_old_root8 ‖ board_new_root8]
      }
prove_automatafl_match(&m)                                   lib.rs:444
  → prove_match(Game::Automatafl, &leaves)                   lib.rs:386
      → fold_match(&leaves)                                  dregg-multiway-tug/src/fold.rs:746
          → build_match_turns → mint_turn (per leaf)         fold.rs:727, :371
              CustomWitnessBundle { program, witness_values, num_rows, public_inputs }
              → mint_custom_leg → FinalizedTurn (rotated)    circuit-prove/src/joint_turn_aggregation.rs:216
          → prove_turn_chain_recursive(&turns)               → WholeChainProof
  → verify_history_bytes(proof, vk)                          dregg-lightclient (prover-side self-attest)
GameBoard::submit → ugc_dregg::Registry::submit_proof        lib.rs:529 (O(1) accept, stores no moves, ranks)
```

Downstream: `dreggnet-prove-service` (`PlayedMatch::Automatafl`, `lib.rs:453`) runs
the fold as the async background worker; the discord-bot crown / proof-carrying
leaderboard (`discord-bot/src/commands/crown.rs`) submits and ranks.

### 1.2 What the proof actually asserts, and how the CellProgram becomes a proof

The Custom leaf is proven by `prove_custom_leaf_with_commitment`
(`circuit-prove/src/custom_leaf_adapter.rs:534`). Critically, the actual proving is
**already over an `EffectVmDescriptor2`**, derived from the CellProgram at prove time:

```rust
let lowered  = lower_cellprogram(program)?;            // custom_leaf_lowering.rs:524  → Lowered { desc, chains }
let desc2    = &lowered.desc;                           // an EffectVmDescriptor2
let base_trace = augmented_base_trace(&lowered, program, witness_values, num_rows, pis)?;
                                                        // = program.generate_trace(witness_values) + fill_chain_columns
let inner    = prove_vm_descriptor2_for_config(desc2, &base_trace, pis, …)?;   // the STARK is over desc2
… expose in-circuit PI-commitment; wrap as a recursion leaf …
```

So the CellProgram is used only to (a) forward-lower to `desc2` via
`cellprogram_to_descriptor2`, and (b) generate the base trace from the named
`witness_values`. The recursion/fold sees a descriptor. **This is the seam the
wiring exploits:** if we can hand the path a pre-built `desc2` (the Lean-emitted
one) plus a matching raw trace, the CellProgram — and thus the hand-written Rust
AIR — is no longer needed.

State binding: the state-binding leg (`prove_custom_leaf_with_state_commitment`,
`custom_leaf_adapter.rs:653`) re-exposes PIs `[0..16)` = `[old8 ‖ new8]` so the fold's
binding node `connect`s the leaf to the cell's real rotated roots. Both the Rust
(32-PI) and Lean (20-PI) layouts keep this 16-felt prefix; only the app tail
(board commitment, PIs `[16..)`) differs. So the Lean descriptor is drop-in
compatible with the state-binding fold.

### 1.3 Honest scope of "verified" today

- `b.air_accepts()` in `leaves()` is an **in-memory constraint evaluation** of the
  Rust `Builder`, not the STARK. It gates lowering; it is not the proof.
- The `WholeChainProof` / light-client accept is real but inherits the **undischarged
  FRI/STARK soundness floor** (see memory `project-fri-soundness-reality`): the
  deployed posture is calculator-bits, not cryptographic soundness. The wiring below
  is orthogonal to that floor — it closes the *arithmetization* gap (deployed AIR ≠
  proven AIR), not the FRI gap.
- The Lean refinement (`astep_sat_imp_automatonStep`) is over `automataflStepDesc`,
  which **nothing deployed proves**. That is precisely the debt.

---

## 2. The loader: decoder EXISTS, dispatch + descriptor-native leaf are the gaps

### 2.1 What exists

- **Decoder:** `parse_vm_descriptor2(json) -> EffectVmDescriptor2`
  (`circuit/src/descriptor_ir2.rs`) decodes any by-name JSON. The
  `automatafl-{step,resolve}.json` files parse today (confirmed: step = 269/32/418,
  resolve = 457/20/548).
- **Live dispatch table:** `descriptor_by_name(name) -> Option<EffectVmDescriptor2>`
  (`circuit/src/descriptor_by_name.rs:353`) is the production, fail-closed
  name→descriptor loader (`STATIC_GOLDENS`, `descriptor_by_name.rs:80`). It is used
  on the **predicate/verify** path (`bridge/src/verifier.rs`), NOT the leaf-fold path.
- **Emit + drift authorship:** `EmitByName.lean:106-109` routes
  `automatafl-{resolve,step}.json ← {automataflResolveDesc, automataflStepDesc}`;
  `emit_descriptors.py` re-derives + drift-checks.

### 2.2 The two gaps

1. **No automatafl arm in `descriptor_by_name`.** `automatafl-step` /
   `automatafl-resolve` are absent from `STATIC_GOLDENS` and from every
   `PredicateKind`. Adding two `include_str!` consts + two rows is trivial; it makes
   `descriptor_by_name("dregg-automatafl-step-d1-n2")` return the descriptor. (This
   is only needed if we route the game through the by-name table; the leaf could
   equally `include_str!` + `parse_vm_descriptor2` directly. Prefer the table so the
   drift gate and dispatch-soundness test cover it.)

2. **The leaf-fold path takes a `CellProgram`, not a descriptor.** `LeafBundle`
   (`fold.rs:78`) and `CustomWitnessBundle` (`joint_turn_aggregation.rs:216`) both
   carry `program: CellProgram`. To fold the Lean descriptor we need a
   **descriptor-native leaf**:
   - Add `prove_custom_leaf_descriptor_with_state_commitment(desc: &EffectVmDescriptor2,
     base_trace: &[Vec<Felt>], pis: &[Felt], config)` — a sibling of
     `prove_custom_leaf_with_state_commitment` that **skips** `lower_cellprogram` and
     `augmented_base_trace`, calling `prove_vm_descriptor2_for_config(desc, base_trace,
     pis, …)` directly, then the identical expose/wrap.
   - For the current Lean descriptors (0 lookups) there are **no chip/chain columns**,
     so `fill_chain_columns` is unnecessary — the base trace is exactly the `trace_width`
     columns. (A lookup-bearing descriptor would additionally need the chain-fill plan;
     the Lean step/resolve deliberately retired all lookups, so this is moot.)
   - Thread a descriptor variant through `LeafBundle`/`CustomWitnessBundle` (e.g. an
     enum `LeafSource::CellProgram(..) | LeafSource::Descriptor { desc, base_trace }`)
     so `mint_turn`/`mint_custom_leg` dispatch to the descriptor-native prover. This is
     the main plumbing lift; it is additive and does not disturb the multiway-tug leaves.

Effort (loader + descriptor-native leaf): ~1–2 focused days, mostly in
`circuit-prove` (the leg plumbing) with a small `descriptor_by_name` addition.

---

## 3. The witness generator (the crux)

### 3.1 What the descriptor needs, and what we have

`prove_vm_descriptor2_for_config` needs a `base_trace: Vec<Vec<Felt>>` where column
`k` carries the value the descriptor's index-`k` gates read — the FULL column layout:
board cells (old+new) with per-cell `{0,1,2,3}` range membership, coord bit-ranges,
the auto row×col one-hot + `AUTO = Σ selRow·selCol·board` dot product, the four ray
scans (per step: prefix-sum in-bounds bit, gated shifted read, hit one-hot, `dist`/
`what` recompositions, occlusion gates, hit-in-bounds bit, `cond_nonzero` inverse),
the back-end `decideAxis` truth table (×2 axes), `chooseOffset`, the step + board-update
gates, and the packed-felt board commitments.

- `src/reference.rs` (the game oracle) computed only `old → new`
  (`automaton_step`, `apply_turn`) — it did NOT produce the intermediate AIR columns.
- `src/builder.rs::automaton_gadget` DID produce every intermediate
  column value (that is how `air_accepts()` passed), but into the diverged
  269/32 Rust layout.

### 3.2 The design: reuse the front-end fill, rewrite the tail

Because the Lean layout was authored to mirror the Rust allocation order — the emit
file pins the front-end column bases explicitly (`A_FRONT_WIDTH 2 = 58`,
`A_DECIDE_X_BASE 2 = 58`, `A_DECIDE_Y_BASE 2 = 105`, `A_CHOOSE_BASE 2 = 152`,
`A_STEP_BASE 2 = 209`, `A_BACK_TAIL 2 = 252`, `packFeltBase 2 = 252`) and states the
front-end is "byte-identical to the frozen absolute layout" — the column *values* for
indices `0..A_BACK_TAIL` transfer directly from the existing `automaton_gadget`
computation. The only genuine rewrite is the board-commitment TAIL:

- Rust (deployed): two `board_root8` MerkleHash8 sites → 8+8 root felts as PIs `[16..32)`,
  backed by 2 arity-16 Poseidon2 lookups.
- Lean (target): degree-1 **pack gates** → 2 (n=2) / more (n≥3) packed felts as PIs
  `[16..20)`, no lookup.

So the witness generator is: a Rust function `automatafl_step_trace(old, next, n)
-> (Vec<Vec<Felt>>, Vec<Felt>)` that (a) runs the reference to get `next`, (b) fills
columns `0..A_BACK_TAIL` using the existing gadget value logic (extracted from
`builder.rs`, kept as a witness-only helper), (c) fills the packed-felt tail per the
Lean pack layout, (d) returns the 20-PI vector. Trusted-Rust, fail-closed: a wrong
column fails `prove_vm_descriptor2` (the constraint is UNSAT), it never mis-accepts.

### 3.3 Can it reuse reference.rs / builder.rs?

- **reference.rs: keep and reuse** for the `old → next` turn (and, for resolve, the
  move validation / conflict resolution). It is the oracle the trace fills against.
- **builder.rs value logic: extract, do not delete yet.** The column-VALUE
  computations (ray casts, one-hots, decide/choose/step) are the witness generator's
  body. The plan is to lift them into a witness-only module (`witness.rs`), drop the
  constraint-EMITTING half (`assert_zero`/`assert_binary`/`assert_member`/the
  descriptor builder), and retarget the tail. This is the "keep reference.rs (and the
  value helpers) if the witness-gen uses it" branch of the deletion plan (§5).

Effort (witness-gen, STEP, n = 2): ~2–3 days including a differential test that the
generated trace satisfies the decoded Lean descriptor for a battery of boards.
Scaling the tail to n = 5 / n = 11: another ~1–2 days (and depends on §4).

### 3.4 Is the cutover [delete old / V2 / V3] a prerequisite?

- **STEP (the deployed path): NO.** `automataflStepDesc` carries no staged-additive
  cruft — it is clean at 254/20/405/0-lookups. The only "cleanup" it needs is a
  re-emit to disk (§4.1) to un-stale the artifact. Witness-gen fills a clean layout.
- **RESOLVE (future D3 fold): YES, recommended before witness-gen.** The resolve
  descriptor carries STAGED-ADDITIVE superseded columns —
  `AutomataflResolveEmit.lean` §2.5/§2.6 emit `cCarryV2`/`cWBoardV2`/`cMidV2` (chunk-3)
  and `cFtV2A`/`cMidV3` (chunk-5) ADDITIVELY after the old buggy board columns, with
  the PI bound to the corrected board. A witness-gen must fill *every* column,
  including the superseded buggy ones (their gates still constrain the trace). That is
  fillable but wasteful and drift-prone. Per memory
  `feedback-mapping-is-the-launchpad-not-the-outcome` ("go UNADDITIVE: DELETE the
  superseded object + rewire"), the resolve descriptor should be **re-authored to drop
  the old/V2 columns and re-pin to the corrected board** before it is wired. This is a
  Lean-side cleanup, tracked separately; it does not block STEP.

---

## 4. Repoint + Rust-AIR-deletion plan

### 4.1 Prerequisite — un-stale + emit the deployed-size step descriptor (Lean side)

1. Re-run the emit so `circuit/descriptors/by-name/automatafl-step.json` matches the
   current `automataflStepDesc` (254/20/405/0-lookups). The on-disk file is a stale
   pre-"retire lookups" emission (last emitted 2026-07-18; the Lean moved 2026-07-19).
   This also removes the 2 Merkle board-root lookups and drops PIs 32 → 20. **Confirm
   the drift gate (`emit_descriptors.py` recursing `by-name/`) actually fails on this
   today** — if it is green, the by-name automatafl drift check is not wired and that
   is its own wound to close.
2. Emit + byte-pin the **deployed board size**: `automataflStepDescN 5` (tests) and
   `automataflStepDescN 11` (stock game) to their own by-name files, routed in
   `EmitByName.lean`. The layout is already n-parametric ("descN 11 tiles clean"); this
   is a mechanical re-pin, but it is REQUIRED — the deployed match is not n = 2.

### 4.2 The repoint (Rust side)

3. Register the automatafl step descriptor(s) in `descriptor_by_name` (§2.2.1).
4. Land the descriptor-native leaf (§2.2.2).
5. Land the witness generator (§3).
6. Change `AutomataflMatch::leaves()` (`lib.rs:296`) to, per turn: load the
   deployed-size Lean descriptor, generate the trace via §3, and build a
   descriptor-native `LeafBundle`. The `build_d1_honest`/`air_accepts`/`cellprogram`/
   `trace_witness` calls are removed.
7. Differential gate (keep until deletion): fold BOTH the old Rust-AIR leaf and the
   new Lean-descriptor leaf for a battery of matches; assert both self-attest and rank
   identically. This is the STAGED-ADDITIVE-THEN-CUTOVER guard.

### 4.3 The deletion

8. Once the Lean-descriptor path is the sole fold path and the differential gate is
   green across n = 5 / n = 11:
   - **Delete** `src/air.rs`, `moves.rs`, `builder.rs` and the AIR-
     proving tests (`air_accepts` refinement battery, the D1/D2/D3 self-accept tests).
   - **Keep** `reference.rs` (the oracle the witness-gen runs) and the extracted
     witness-only value helpers (§3.3). If those helpers are lifted into a new
     `witness.rs`, `builder.rs` deletes cleanly.
   - Update `lib.rs` re-exports and the `surface.rs`/`game.rs` consumers that import
     `build_*`/`Builder` (they use the playable surface, not the fold — audit each).
9. Update the crate doc (`dregg-automatafl/src/lib.rs`) from "hand-authored Custom-VK
   circuit" to "reference oracle + witness generator that fills the Lean-emitted
   descriptor; Rust calls into the Lean AIR."

---

## 5. What EXISTS vs what is NEEDED for complete zk / trustless / distributed automatafl

| Capability | Exists | Needed |
|---|---|---|
| **Foldable per-turn leaf** | D1 automaton-step, Rust AIR | D1 via **Lean** descriptor (this doc); then D3 resolve leaf |
| **Recursive fold → one proof** | `fold_match → WholeChainProof` | reused unchanged |
| **Light-client O(1) accept** | `verify_history_bytes` + `ugc-dregg` submit/rank, stores no moves | reused; still inherits the **FRI/STARK floor** (calculator-bits, not sound) |
| **Proven AIR = deployed AIR** | NO — deployed proves Rust AIR; Lean proves `automataflStepDesc` | the repoint (§4) |
| **Refinement of the step** | `astep_sat_imp_automatonStep(N)` — CLOSED, unconditional mod `StepCanon` (range gadget), n-generic | applies to the DEPLOYED proof only after the repoint |
| **Refinement of the whole turn (moves)** | `resolve_step_sat_imp_applyTurn` — CLOSED mod ONE seam: the fold-join PI equality (Leg R MID = Leg A OLD) | discharge the seam with a real fold object; wire resolve into the fold |
| **Proof attests the players' moves** | NO — only the automaton step is folded | fold the **resolve (D3)** leaf so the ranked proof is the real 2-player match, not automaton drift |
| **Multiplayer / distributed surface** | YES — `AutomataflOffering`/`surface.rs`, web + Discord/TG/WeChat, commit→reveal→resolve, per-viewer sealed fog | connect surface moves → resolve leaves so the played match IS the proven match |
| **On-device (wasm) proving** | NO — server-side worker (`dreggnet-prove-service`) | compile the prover to wasm for "moves never leave the device" (separate workstream) |
| **Cryptographic hiding (true ZK)** | NO — succinct, not hiding; "moves not posted" is data-availability | HidingFRI / a hiding wrap if a cryptographic transcript-privacy claim is wanted |
| **Deployed-size descriptor** | NO — Lean pins n = 2 only | emit + pin descN 5 / descN 11 (§4.1) |

The honest one-line posture after the STEP repoint: *the deployed automatafl
leaderboard proves, through the byte-pinned Lean-authored automaton-step AIR (whose
`Satisfied2 ⇒ automatonStep` refinement is machine-checked and unconditional), that
each ranked match is a valid automaton-step chain — under the still-undischarged
FRI/STARK soundness floor, and attesting the automaton steps, not yet the players'
resolved moves.*

---

## 6. Ordered build plan

1. **[Lean] Un-stale + size the step descriptor.** Re-emit `automatafl-step.json`
   from `automataflStepDesc`; verify the by-name drift gate fails on the current stale
   file (fix the gate if it does not). Emit + byte-pin `automataflStepDescN 5` and
   `automataflStepDescN 11`, route in `EmitByName.lean`. — *the prerequisite; nothing
   deployed can use the Lean AIR until its size matches.*
2. **[Rust] Descriptor loader arm.** Add automatafl step (and, later, resolve) to
   `descriptor_by_name` `STATIC_GOLDENS` + the dispatch-soundness test.
3. **[Rust] Descriptor-native leaf.** Add
   `prove_custom_leaf_descriptor_with_state_commitment` (skip lower + trace-gen) and a
   `LeafSource` variant threaded through `LeafBundle`/`CustomWitnessBundle`/`mint_turn`.
4. **[Rust] Witness generator.** Lift `builder.rs`'s column-value logic into a
   witness-only helper; add `automatafl_step_trace(old, n)` filling the Lean layout
   (front-end reuse + packed-felt tail). Test: generated trace satisfies the decoded
   descriptor for a board battery (honest accept + tamper reject).
5. **[Rust] Repoint `AutomataflMatch::leaves()`** at the descriptor-native leaf.
6. **[Rust] Differential gate** old-vs-new leaf across n = 5 / n = 11; both fold,
   self-attest, and rank identically.
7. **[Rust] Delete** `air.rs`/`moves.rs`/`builder.rs` + AIR tests; keep `reference.rs`
   + the witness helper; fix consumers + crate doc.
8. **[Lean] Un-additive the resolve descriptor** (drop old/V2/V3 columns, re-pin to the
   corrected board) — prerequisite for a clean resolve wiring.
9. **[Rust+Lean] Fold the resolve (D3) leaf** so the ranked proof attests the real
   2-player resolved turn; discharge the fold-join PI seam
   (`resolve_step_sat_imp_applyTurn`'s named residual) with the real fold object;
   connect the surface's commit→reveal→resolve moves to the resolve leaves.
10. **[separate workstreams]** wasm on-device prover; hiding wrap if a cryptographic
    privacy claim (beyond data-availability) is wanted; the FRI/STARK soundness floor
    (orthogonal, tracked in `project-fri-soundness-reality`).

Steps 1–7 close house-law #1 for the deployed D1 path (Rust AIR deleted, Lean AIR
proven-and-deployed). Steps 8–9 make the *played* match the *proven* match. Step 10
is the remaining distance to a fully sound, on-device, hiding, distributed automatafl.
