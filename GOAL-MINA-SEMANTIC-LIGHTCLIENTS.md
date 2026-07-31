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
