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
