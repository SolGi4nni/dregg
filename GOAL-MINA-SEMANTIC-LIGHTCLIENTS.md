<!-- ⚑⚑ THIS REPO RUNS MULTIPLE CONCURRENT /goal SESSIONS. This file is the
     mina-semantic-lightclients lane only. See GOALS-INDEX.md for every live goal.
     Edit only THIS trail; don't clobber a sibling's. -->

> ⚑ **Multiple goals are live — see [`GOALS-INDEX.md`](GOALS-INDEX.md).**
> This file is the **mina-semantic-lightclients** lane only.

# GOAL — semantic light clients BOTH WAYS, then deploy, then a poster

**Set 2026-07-30 21:44 EDT. Deadline 09:00 (11.3 h).**

> Work until both mina→dregg and dregg→mina are **semantic, full light clients** to each other's
> protocols. **No sins, no "excuses", no "honestly labeled" aspects.** Then deploy a devnet and to
> Mina devnet using hbox to demonstrate the whole thing. Then a new poster in
> `~/src/dregg-posters` (see `2026-07-30-typst/`).

---

## ⚑ The bar, written so it cannot be quietly lowered

**"No honestly-labeled aspects" is the hard clause.** It forbids the move this project is best at:
find a hole, name it precisely, ship around it. **A named residual is still a sin here.** Nothing
below gets to be "documented"; it gets closed or it blocks the goal.

Corollary from `CLAUDE.md` (added today): **a cost estimate is never a reason to pick the worse
design.** *frozen · already deployed · flag day · would require a VK rotation · bigger change* are
not objections. **The answer to "what does it cost" is "a rebuild."**

---

## STATE — measured 2026-07-30, not assumed

### Closed tonight ✅
- **last-row endpoint forge** — a proof object existed publishing balance 999,999,999 where the
  honest turn ended at 99,950. Vacuity was the `is_transition()` **multiplier**, not missing
  algebra. Now 57/57 whole-domain windowGates; forge refused `[#0,#37]`; row-62 control unchanged.
  3 registry FPs rotated; old peers refuse to load.
- **`num_turns` alias** — a 2-turn history attested **6,308,233,219** by editing one `u64`. Dead by
  type now (`u32`), envelope v6, 0/2 admitted, wasm32 leg **measured** not read.
- **self-anchored verifies** — MCP anchor now caller-supplied and refused *before* the fold; the
  public page reads `?anchor=`; outer envelope publics deleted (v2).
- **apex vacuity** — machine-checked in ONE build unit at 5 deployed tags (`apex_is_dead_either_way`),
  by a **floor-free** route (`RootSeparated`, not `Poseidon2SpongeCR`).
- **`DreggFederation`** — deleted. Claimed to prevent double-withdrawal over an inert field.
- **law1 red** — 8 sites were 3 copies of a textbook Fib AIR; fixed by subtraction, 1560→1505.

### OPEN — this is the goal
1. ⚑ **Authorization is off-AIR.** No curve/signature table in the deployed registry. A turn proof
   establishes **no ownership**. **Largest sin; blocks "semantic" both ways.**
2. **`effects_hash` published, unbound** — Lean pin designed, elaborates clean, NOT LANDED.
3. **Nullifier binding = `assert_zero(0)`** — `Gated{Hash}` erased on the p3 path; 11 sites,
   reachability unswept.
4. **Child-VK pin is not a pin** — exposed-cap spine designed, probe green, fork plumbing unstarted.
5. **173 free-column PI pins** — held only by executor overwrite, i.e. host trust.
6. **Apex arity** — Lean arity-2 vs deployed arity-3. A1 (~20 sites) **+ the ∃-hoist together**, or
   the carriers just migrate (measured: arity alone moves 77 vacuous carriers to fresh vacuous ones).
7. **131-program compile + 905-instance prove** — never run. Gates the anchor.
8. **`setDreggRoot` is key-gated on chain**, and deployed VK ≠ current source VK.
9. ⚑ **The semantic gap itself** — Mina reads a dregg *leaf* (Merkle membership), not dregg
   semantics. dregg reads Mina's *chain*, not any account/balance/zkApp state. **This is what the
   goal's word "semantic" names, and neither side has it.**

---

## THRUST

- **A. Land what is designed and unlanded** — effects_hash pin; `Gated{Hash}` fail-closed; VK spine.
- **B. Authorization in-AIR** — the largest sin; without it neither side is semantic.
- **C. The semantic surface** — Mina reads dregg *state by claim*; dregg reads Mina *account state*.
- **D. Compute** — 131 compile + 905 prove on hbox (24c/123G, quiet).
- **E. Deploy** — dregg devnet + Mina devnet, proof-gated anchor, relay key **deleted**.
- **F. Poster** — night skin; EN plain (high-school), 中文 peer-level; scope **drawn**, not captioned.

## NEXT 3
1. `effects_hash` pin landed end-to-end (emit → Rust decoder → invert `vk_epoch_misc`).
2. Authorization in-AIR: scope + first rung.
3. `Gated{Hash}` fail-closed + reachability census.

## DONE-LOG
- 21:44 goal adopted; state inventoried from six audits + four confirmed-and-measured exploits.
- 21:50 `dregg-cell` compiles again (the `tcb_ok`→`TcbStatus` blocker landed); doctrine suite unblocked.
- 22:15 ⚑ **VALUE8 consumer re-point LANDED** — `AlgoStarkSoundKernel` green (was 6 errors + 2
  hygiene cascades). The "heartbeat timeout" was a **FALSE DEFEQ**: `Rfix 5` piCount 57 vs the
  pre-VALUE8 member at 50, and `isDefEq` burned the whole budget unfolding two 304-entry lists
  before reaching the field that differed. **Root-build adjudication unblocked for every lane.**
- 22:15 ⚑ **`Gated{Hash}` erasure CLOSED** — 1 of 12 sites was reachable and it was the deployed
  shielded spend; **probe measured a spend of a note the prover never owned, proved AND verified**.
  Now `try_from_dsl` refuses (`ErasedConstraint`) and `eval_expr`'s hash `ZERO` → `unreachable!()`
  — *"that ZERO was never actually unreachable; it WAS the erasure."* Plus `is_leaf` pinned.
  ⚠ Residual named by that lane: **the spending key is carried, not bound** — a fresh key per spend
  yields a fresh nullifier for the same note, so a double-spend survives a fully repaired C4.
  **That is a SIN under this goal and belongs to the authorization lane.**
- 22:35 **51 verdict surfaces censused; 13 could not go false for a hostile party; all 13 addressed**
  (11 repaired, 2 disclosed). Worst: `portal/dist/portal.js` **counted verifications it never ran**
  (a `setTimeout` setting `verified = true` over a cell list from the node under test — 100 fake
  cells → "100/100 verified", zero proofs); `site/grain/play.html` printed *"the computer running
  the agent couldn't have lied to you"* over two HTTP 200s from that computer; `cli`'s proof view
  was **fail-open** (`unwrap_or(true)` → every IVC step `[ok]`). Converged shape: oracle from the
  visitor, provenance printed on every verdict, and a served oracle gets a **third state** (amber
  `≡`, never green `✓`). Control **executes** the badge against a simulated hostile host.
  ⚑ I mis-told that lane four of its targets were already closed by siblings — **they were its own
  work.** It checked rather than complying. My error, not its.
- 22:35 **SEQUENCING DECISION**: `whole_history_proof.bin` is stale (`OodEvaluationMismatch`) because
  the last-row flag day rotated the circuit. **NOT re-baking yet** — the VK spine rotates every
  `RecursionVk`, so the order is **spine → re-bake once → 131 compile → 905 prove → deploy**.
  Re-baking now burns a real proving run on a shape about to change.
  ⚠ `circuit-prove` is red mid-cutover (expose-hook arity 2→3) — that IS the spine lane working.
- 22:40 **AUTHORIZATION-IN-AIR: mechanism CHOSEN, on soundness.** The requirement decides it: the
  PROVER must be unable to forge, and the prover is the host, not the owner. That refutes the cheap
  candidates rather than pricing them. A preimage/MAC/hash-ratchet authenticator is **refuted** —
  whatever the AIR forces the prover to know, the prover knows, and can re-use for a different turn;
  authority the prover can mint is not authority. A nonce/receipt chain answers "is this turn NEXT",
  never "did anyone authorize the first one". The cap-open crown alone is **refuted** — a Merkle path
  is PUBLIC data, so membership proves the cap exists and what it permits, never who invoked it (the
  crown is kept for *which cap*; it cannot supply *who*). So: an **in-AIR signature verification**,
  the one primitive where signing is separable from proving.
  ⚑ **The scheme is a hash-based one-time signature over the deployed Poseidon2 chip, NOT ed25519** —
  also on soundness, not cost: (1) ed25519-in-AIR is non-native `Fq = 2²⁵⁵−19` arithmetic whose gate
  cross-sums reach `~2⁵⁴⁰` and OVERFLOW BabyBear, so the gates are read over ℤ — the residual
  `Ed25519Gadget` names about itself — and that gap would sit at the root of authority; (2) ed25519 is
  classical, and binding authorization to ECDLP inside a PQ-oriented STARK makes authorization the
  weakest link in its own proof; (3) a hash-based signature adds **no new hardness carrier** — same
  Poseidon2 the cap tree, state commitment and FRI already ride. Native field, native chip, native
  floor. (~3 orders of magnitude cheaper than the ~10⁷-gate ed25519 verify is a CONSEQUENCE, not the
  reason.) One-time is the right granularity — a turn is a one-shot act; the many-time lift is the
  depth-16 crown indexed by turn sequence.
- 23:05 ⚑ **`effects_hash` pin: comment corrected, pin DESIGNED and PROVED with live controls**
  (`7a4db259d`, `d59941ff8`). Lean-authored AIR in `Emit/`; Rust authors nothing. The false comment
  at `EffectVmEmitRotationV3.lean` §5.PC.EH claimed `verify_vm_descriptor2` already checked the
  declared hash — it reasoned from the RETIRED v1 hand-AIR, and it was the stated reason three
  effects have no declared column. **The E1 kill-set was already the proof**: `e1_compact_generated.rs`
  deletes cols 94/95 in all 57 wide members under the criterion *"referenced by NO surviving
  constraint"*.
  ⚑ **My first draft was the exact `∃`-vacuity this tree names.** It concluded
  `∃ x y, x≠y ∧ perm x = perm y`, which `EffectVmEmitRotationR.lean:255` records as
  **unconditionally TRUE by pigeonhole** at deployed parameters. Restated on `IsCollW` (pair-specific,
  decidable); every rung is now total, no hash hypothesis anywhere. Controls include
  `ehTagGate_rejects_wrong_tag` so the acceptance control cannot be met by a gate that accepts all.
  ⚑ **Arity corrected 16→11** — `single_perm_compress` is `carrier(8) ‖ 3 fresh`;
  `descriptor_ir2::CHIP_RATE = 16` is the chip BUS, a different number. 17 declared felts ride six
  steps, the identical shape as the deployed `wire_commit_8`.
  ⚠ **NOT WIRED into the registry emit, deliberately.** The chokepoint is `emitCompact key (weldWide
  key …)`, one line — but wiring makes every wide member unprovable until `trace_rotated.rs` emits
  the 65 new columns, and that wedges every sibling lane in this shared tree tonight. Wiring + Rust
  decoder + emit regen + both test inversions is one follow-on commit. **This is a named residual and
  therefore a sin under this goal; it is the next thing on this lane, not a deferral.**
  Fail-opens measured for whoever lands it: `registry_fp` is the sha256 of Lean-emitted TSV bytes, so
  a Rust-only hash change moves NO fingerprint and two binaries would handshake `Compatible`;
  `trace_rotated.rs` has ZERO `effects_hash` references today; `prove_vm_descriptor2` zero-extends
  short rows BEFORE the width check (`descriptor_ir2.rs:6619` vs `:6487`).
- 22:50 **`effects_hash` pin PROVED (not installed).** 8 `#assert_axioms` clean; ladder `ehHop` →
  `ehChain_back` → `ehContinuity_step` → `ehPublish_binds`, with **both** polarity controls
  (accept-honest AND reject-wrong-tag — the first alone would pass for a gate accepting everything).
  Two self-corrections worth keeping: the first draft was the tree's own **∃-vacuity** (hypothesised
  the negation of something *unconditionally true by pigeonhole*), restated on a pair-specific
  decidable predicate so **every rung is total, no hash hypothesis anywhere**; and the absorb arity
  was 16→**11** (`single_perm_compress` takes ≤11; `CHIP_RATE = 16` is the chip BUS, a different
  number). 65 columns, 27 constraints, `piCount` unchanged.

- 22:50 ⚑⚑ **CONVERGENCE DECISION — ONE FLAG DAY, NOT FIVE.**
  Five lanes each produce a descriptor/VK rotation: the VK spine (every `RecursionVk`), the
  `effects_hash` pin (65 cols × 174 members), authorization-in-AIR, the 173 free-column pins, and
  the arity+∃-hoist cutover. **Landing them separately means five rotations, five re-bakes of
  `whole_history_proof.bin`, and five 131-program compiles — and each invalidates the last.**
  **Therefore: lanes PROVE and STAGE; the coordinator fires ONE convergence re-emit.** Order:
  spine + arity + authorization + effects_hash + pins all staged → **one** descriptor re-emit →
  **one** root-proof re-bake → **one** 131 compile → **one** 905 prove → deploy.
  ⚠ The `effects_hash` lane already made this call independently for its own wiring, on blast-radius
  grounds, and was right to.

  ⚑ Four measured fail-opens the convergence commit MUST NOT fall into (from that lane):
  1. `registry_fp` is sha256 of **Lean-emitted TSV bytes** — a Rust-only hash change moves NO
     fingerprint, so two binaries computing different hashes would handshake `Compatible`.
  2. `trace_rotated.rs` has **zero** `effects_hash` references today — the family could be replaced
     with every deployed path byte-unchanged.
  3. `prove_vm_descriptor2` **zero-extends short rows BEFORE the width check** (`:6619` resize vs
     `:6487` guard) — an un-updated producer proves green with zeros.
  4. New columns must route through `compacted_column(registry_key, raw)`; that class already fired
     once (`trace_rotated.rs:4696`).
- 23:05 **Root build: 2 red files, both accounted for.**
  1. `EffectVmEffectsHashPin.lean:492,501` `Function expected at` → cascading `sorryAx` on **both**
     polarity controls (`ehTagGate_accepts_honest`, `ehTagGate_rejects_wrong_tag`). ⚑ **Third time
     tonight a lane's single-file green disagreed with the root.** Suspect its own 16→11 arity
     correction leaving a call site at the old shape. Routed back with the exact errors and a
     standing instruction: **ask me for the root build rather than trusting a file build.**
  2. `CustomDeployedBytePin.lean:118,122` — the byte golden is stale. **MEASURED**: emitted
     `trace_width` **1672 → 1716**, `main` arity **1619 → 1663**, exactly **+44 columns**, from
     `ec69b6c0f`'s "appropriately wide buses". The file's own text says *"that red is the pin DOING
     ITS JOB — do not relax it, re-emit."*
     ⚑ **I did NOT re-bake it.** `git status` shows **four Emit modules mid-edit**
     (`EffectVmEffectsHashPin`, `EffectVmEmitV2`, `ShieldedSpendDescriptor`, `TurnAuthLamportEmit`).
     **Baking a golden over four lanes' in-flight work is precisely the mistake the convergence
     decision exists to prevent.** It rides the one re-emit.
- 23:05 ⚑ **The authorization lane picked LAMPORT** (`Emit/TurnAuthLamportEmit.lean` in flight) —
  hash-based, so it needs only the **Poseidon2 chip that already exists**: no curve table, and
  post-quantum as a side effect. That is the right shape for "no signature table in the registry".
- 23:20 ⚑ **CORRECTION — my root red on `EffectVmEffectsHashPin` was a MID-SAVE CAPTURE, not a defect.**
  `hbuild` rsyncs the working tree; I rsynced while that lane was mid-edit and built an intermediate
  where `.eval` sat postfix on a newline (parsed as a separate token → `Function expected at`, and
  the `#assert_axioms` cascade). **Verified at HEAD `e2416434d`: `Build completed successfully
  (3127 jobs)`, zero errors.** My first suspect — its 16→11 arity fix — was WRONG and it said so
  with the evidence.
  **New shared-tree hazard, recorded**: *a coordinator's root build can capture a lane's half-saved
  file and report it as that lane's defect.* Same family as `git add -A` staging a sibling's tree.
  **Mitigation: check `git status` on the file before believing a red in a shared tree.**
- 23:20 ⚑ **And the lane found a REAL gap while defending itself** — its two polarity controls were
  **re-typing the tag-gate body inline instead of projecting it out of `ehTagGate`**, so *both would
  have stayed green after an edit to the shipped gate*. **A control that cannot notice the thing it
  controls** — the exact class they exist to close. Now `ehTagGateBody` is factored out, both
  controls evaluate the shipped body, an `example … := rfl` ties them, and **both VALUES are pinned**
  (`== 0` honest, `== 6` on a row firing `sel::TRANSFER` while declaring tag 7) — so a gate accepting
  everything fails one and a gate refusing everything fails the other. **Neither can go vacuous
  while the other holds.**
- 23:2x ⚑ **THRUST E — THE DEPLOY PATH IS SCRIPTED, AND ONE DIRECTION IS ALREADY GREEN END TO END.**
  Two commands, `bridge/demo/{mina-verifies-dregg,dregg-verifies-mina}.sh`, runbook at
  `docs/ops/DEMO-MINA-BOTH-DIRECTIONS.md`. **Nothing deployed** — `--broadcast` is ember's.
  - **`dregg-verifies-mina.sh` — 7/7 PASS, MEASURED locally, ~2 min.** Live wire: **74,313 bytes of
    `Protocol_state.Value`** off a devnet seed's own p2p stack (pnet/Noise XX/yamux/`coda/rpcs`
    `get_best_tip`), no credential — the chain-id PSK is a public constant. Transcription:
    `state_hash(540186)` reproduced offline from the block's own 38 field elements / 819 packed
    chunks. The link: **540221 → 540222 MATCH** — `derive_state_hash(N)` equals block `N+1`'s
    `previous_state_hash`, both off the wire, **so no server is asked anything: the child block is
    the answer key.** `mina_head` 11 passed. Opening check: **proved and verified on real devnet
    block 539508, 15.9 s** wall.
  - **`mina-verifies-dregg.sh`** — tier-0 green (12 checks, 1.2 s); the deploy path green on hbox in
    **55.2 s**; steps 3–4 print `BLOCKED` naming the absent artifact, never a substitute.
  - ⚑ **`O1JS_BACKEND=native` CONFIRMED ON HBOX, and the VK is BIT-IDENTICAL** —
    `27652208543664583115415713498762761134774266267581842433036791062173037487108` both ways.
    compile 9.05→**2.22 s**, prove 7.09→**3.81 s**, verify 0.57→**0.17 s**. `npm ci` lands
    `@o1js/native-linux-x64` with no extra step. **The bit-identity is the load-bearing half**: a
    zkApp's address is a function of its VK, so a disagreement would have been a silent flag day.
  - ⚑ **BLOCKING SIN FOUND — `head-anchor` at `MINA_TIER=1` is RED, and its vk-pin row is a green
    over a FALSE PREMISE.** (a) `DreggTerminalProof.maxProofsVerified` is **1** (right — the real
    terminal program verifies its predecessor) while the harness's stand-in has no proof input and
    is **0**; Pickles says so as `prevs_verified`, and the HONEST ACCEPT dies there. Give the
    producer a `SelfProof` method and **the same gate ACCEPTS** — head → H, turns = 3, 6.2 s.
    **The gate was never what was failing.** (b) the harness prints `(vk hashes differ: FALSE)` and
    then reads the next row as evidence about the vk pin — but two `ZkProgram`s differing **only in
    NAME** compile to **the same verification key** (measured), so the pin compares two equal fields
    and passes. That row was refused by (a). **A "different program" row needs a different CONSTRAINT
    SYSTEM.** Both measured in `scripts/head-gate-rehearsal.ts`, which is written around them.
  - ⚑ **BLOCKING SIN — the seal preimage is emitted by nothing.** `advanceHead` needs `friCommit`
    and `accOutDigest`; they are **not recoverable from the proof** (the terminal seal is a hash of
    them) and `root-fri-uniform.ts`'s per-instance meta does not record them though its `context()`
    holds both. The 905-instance prove must write `.fullchain/terminal-handoff.json` or the terminal
    proof cannot be presented. Shape stated in `devnet-head-advance.ts`; env overrides accepted.
  - ⚑ **ONE KEY THAT DOES NOT EXIST, AND I DID NOT MINT IT.** The deployed zkApp address holds
    `DreggAttestedGate`; `DreggHeadGate` pins its chain in its VK and therefore in its address, so it
    needs a fresh throwaway pair. `devnet-head-deploy.ts` **refuses** and prints the one command.
  - **ANSWER TO THE GATE QUESTION**: when the chain is ready, **two commands, ~10 minutes**, most of
    it Mina block time and none of it a rebuild. Direction 2 alone is **under two minutes and is
    ready now**.
- 22:35 ⚑ **VK SPINE LANDED — child-circuit identity is bound through the root** (`e1d8ab9bc`,
  `84eac660e`; fork `emberian/plonky3-recursion@4aead01`, rev bumped). **AIR-free by construction**:
  no `eval()` edited, no constraint content authored in Rust — a fork trait method returning
  ALREADY-ALLOCATED targets, two widened hook signatures, and `connect` /
  `expose_as_public_output` / the deployed `BABY_BEAR_D4_W24` sponge on the dregg side.
  Every fold node exposes `vk_spine = commit(L.cap ‖ L.spine ‖ R.cap ‖ R.spine)`; tooth (1) now
  compares `whole_chain_anchor` = `blake3(tag ‖ vk_fingerprint ‖ root spine)` instead of the bare
  shape fingerprint. Wide family carried too. **MEASURED**: a child that verifies NOTHING, and one
  wired to check the WRONG input, both move the anchor (`65fc32cd…` → `cd0c6c62…`) and are refused.
  ⚠ **RESIDUAL, found by my own probe and NOT closed: a child's CONSTANT VALUES are not bound** —
  `ConstAir` keeps a const's value in its constraint-free MAIN trace, so a const-swapped child has
  an identical cap, spine and anchor (`65fc32cd…` unchanged). That is the original hole one level
  down, it is a **SIN** under this goal, and reaching it needs const values in the PREPROCESSED
  trace — an AIR change, i.e. **Lean-authored or ember's call, not Rust**.
  ⚑ **Flag day STAGED, NOT FIRED** per the convergence order: nothing re-emitted here. Needs, at
  convergence — every `RecursionVk`; `ugc-dregg/tests/fixtures/whole_history_{proof.bin,anchor.hex}`;
  the three checked-in anchor copies (`portal/dist/history.json`, `site/light-client/history.json`,
  `site/dist/light-client/history.json`); `root_fri_instance.rs`'s `EXPECTED_DEGREE_BITS`; the Mina
  pins in `bridge/mina-zkapp/scripts/root-air-{real,fullchain}.ts`. **No envelope bump needed** —
  the anchor stays one 32-byte `RecursionVk`, so v6 stands and I do not collide with the
  `num_turns` lane. Every pre-spine artifact now refuses to fold at `exposed_board_window`.
- 23:35 ⚑ **VK SPINE LANDED** (`e1d8ab9bc` + fork `emberian/plonky3-recursion@4aead01`). Every fold
  node exposes `vk_spine = commit(L.cap ‖ L.spine ‖ R.cap ‖ R.spine)`; leaves seed a tagged
  sentinel; `exposed_board_window` refuses a bare-`SEG_WIDTH` child as a pre-spine artifact.
  **AIR-free by construction.** `circuit-prove` lib+tests GREEN — that blocker is cleared.
  ⚑ **It corrected my framing and was right**: I asked for the *root fingerprint* to move. It must
  NOT — `recursion_vk_fingerprint` deliberately excludes `public_values`, and that
  content-independence is what lets ONE anchor serve MANY histories; if a substituted child moved
  it, it would move for every honest history too. The inversion belongs on
  **`whole_chain_anchor` = blake3(tag ‖ vk_fingerprint ‖ root spine lanes)** — what the client holds.
  MEASURED: honest `65fc32cd…`, forged-no-check `cd0c6c62…` **REFUSED**.
- 23:35 ⚑ **NEW SIN, found by that lane REFUTING ITS OWN CLAIM**: a child's **constant VALUES** are
  not bound. `ConstAir` keeps a const's value in the **constraint-free MAIN trace**, only
  `[ext_mult, out_idx]` in preprocessed — so two children differing only in a constant share cap,
  spine and anchor. MEASURED: `anchor const-swapped child = 65fc32cd…` **ACCEPTED**.
  *"The original hole one level down: from which circuit was folded to which constants sit inside a
  fixed circuit. A constant is a constraint operand; zeroing a coefficient weakens what the
  constraint says."* Dispatched.
  ⚑ **Substrate call recorded**: HOUSE LAW #1 governs DREGG's circuit logic. `ConstAir` is a p3
  primitive in a fork we maintain with no Lean authoring path short of replacing p3, so a **minimal
  local** change is permitted — one column into preprocessed, one equality, law1 delta reported, and
  **stop-and-report if it needs more than that.**
