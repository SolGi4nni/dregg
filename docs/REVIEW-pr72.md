# Review — PR #72 (`akapug:lane/fee-loop-plus-coordination`), and the answer to issue #74

*Written 2026-08-06 against `main` @ `fc1f0f4d6`. Branch tip `148cd929b`; merge base
`7ea63fe5d` (2026-08-04), 455 commits behind our tip. Everything below is read from the
diff and from `main` at HEAD, not from the PR body.*

**Answer to #74: carve — but not into your five.** Two of your five do not survive contact
with the diff (details in §2), and the single riskiest 18 lines in the bundle are buried
inside your piece 5 instead of being their own decision. Also: **do not spend effort
rebasing.** `git merge-tree --write-tree HEAD akapug/lane-fee-loop` is **clean** — no
textual conflict against a tip 455 commits past your base. The carve is for evidence
hygiene, not for mechanics.

The reason to carve is that these have **different evidence classes**. Bundled, the new
1,025-line binary's risk silently attaches to the fee change, and the fee change's ~800
live turns silently vouch for the binary.

---

## 1. What is actually in the diff

11 commits, +2,355/−12, 15 files. Grouped by what they touch:

| # | commits | files | net |
|---|---|---|---|
| **A** | `98a2eba96` | `sdk/src/lib.rs`, `sdk/tests/public_api.rs` (new) | +6/−1 |
| **B** | `ee4c2bf05`, `e7fc89a7e` | `node/{api,genesis,lib}.rs`, `turn/src/executor/execute.rs` (doc only), `turn/tests/faucet_steady_state_solvency.rs` (new) | +557/−2 |
| **C** | `6d45a8895` | `turn/src/{turn.rs,executor/costs.rs,executor/execute.rs}`, `node/src/{state,executor_setup,lib}.rs`, `turn/tests/coordination_fee_exempt.rs` (new), `exec-lean/tests/coordination_exempt_differential.rs` (new) | +601/−3 |
| **D** | `b1854fbab`, `02cb84ad4`, `f054e3f24`, `be452866c`, `e9de200fb`, `148cd929b` | `dregg-sdk-net/src/bin/dregg-client-sign.rs` (new), `exec-lean/tests/faucet_fee_well_divergence.rs` | +1,175/−9 |
| **E** | `e5f7f54f6` | `node/src/lib.rs` | +18/−0 |

### The headline correction

**The bug in the PR title is a bug in a file this PR introduces.** `funding_shortfall` and
the `ensure_cell` that misuses it exist nowhere in `main` — the whole call site is inside
the new `dregg-client-sign.rs`. `148cd929b` and `e9de200fb` are *edits to D*, not fixes to
anything we run. There is therefore no "take the incident fix and defer the tool" option:
taking the fix **is** taking the 1,025-line tool, in its final state.

(Small note on the write-up, so the next reader is not confused: `funding_shortfall`'s first
return value is `true` when the cell is **absent**, and the local is bound to a variable
named `materialized`. The PR body's sentence "an ABSENT cell is `materialized`" reads as a
contradiction but describes the code correctly. The behaviour — absent cell always POSTs
with `amount = target_balance` — is right, and zeroing only the minimum did leave target at
`f.fund`. Consider renaming the flag `needs_materializing` when this lands.)

### Your pieces 1 and 3

- **Piece 1 is not a build fix for us.** Nothing in this repo references `BudgetSpec`
  (`grep` over `sdk/`, `dregg-sdk-net/`: zero hits). It is a *downstream consumer* export.
  That does not make it less worth taking — it is a genuine unintended regression:
  `65aabc8aa` (2026-07-20, *"verified ML-DSA sign core INSTALLED"*) dropped `BudgetSpec`
  from the root re-export in an unmentioned hunk while the subject announced something
  else. Your compile-canary `sdk/tests/public_api.rs` is the correct fix shape.
- **Piece 3 ("signer: canonical federation identity") does not exist in this PR.** No
  commit here touches `api.rs` except `ee4c2bf05`, and that is the fee-loop's
  `faucet_cell_id()` helper. Either it landed upstream already or it is in the three you
  said you would re-verify. Nothing to review.

---

## 2. The carve, with verified dependency order

Compile-level dependencies were checked at HEAD, not assumed:

- **A depends on nothing, and nothing depends on A.** `BudgetSpec` is `token/src/traits.rs:142`,
  already public. D does **not** use it.
- **D depends on nothing new.** Every import resolves at HEAD: `dregg_sdk::profiles`,
  `AgentCipherclerk::{cell_id,public_key,sign_turn}`, `dregg_sdk::install_verified_mldsa_{sign_core_real,verify_core}`,
  and `dregg_sdk_net::NodeHttpClient` with all three methods it calls
  (`fetch_executor_federation_id`, `fetch_cell_nonce`, `fetch_chain_head`). `NodeHttpClient`
  is **not** behind the `world-sink` feature (`lib.rs:95` is un-gated), and every crate dep
  the bin needs (`reqwest`, `tokio`, `postcard`, `hex`, `serde_json`) is already a **non-dev**
  dependency of `dregg-sdk-net`. No `Cargo.toml` change required. D does not need A, B or C to build.
- **B and C are independent of each other and of D.** Both touch `node/src/lib.rs`, in
  adjacent but disjoint regions; `node/src/state.rs` gains one field with exactly the two
  `NodeStateInner` literal sites that exist at HEAD, so neither piece breaks the other.
- **E depends on C** (it flips the flag C introduces) and is otherwise standalone.

**The cut:**

| | piece | order | why separate |
|---|---|---|---|
| **A** | `sdk: restore BudgetSpec root export` | any | 6 lines, compiler-checked, fixes a real unmentioned regression |
| **B** | `fee: fee well as revolving faucet` | any | ~800 live turns + a control test; touches value conservation |
| **C** | `turn+node: coordination-exempt admission class` — **node half only** | any | new consensus-relevant classification; needs the real review |
| **D** | `sdk-net: dregg-client-sign` — **the whole file, all six commits** | any | 1,025 new lines, touches nothing existing; evidence is *your* deployment |
| **E** | `node: enable the coordination class at the genesis-less devnet boot` | after C | 18 lines, largest blast radius, thinnest evidence — see §4 |

Two differences from your split that matter:

1. **Your piece 5 straddles your piece 2.** "Coordination-exempt end-to-end" is a *node*
   half (`6d45a8895`) and a *client* half (`e9de200fb`, `148cd929b`) that edits the file
   piece 2 creates. Split on that seam: node changes go in C, client changes stay in D.
   A carve where 5 cannot build without 2 is worse than the bundle; this one has no such edge.
2. **`e5f7f54f6` gets its own PR.** You flagged it yourself as "a policy call you may want
   to drop." It is the 18 lines with the widest consequences in the whole bundle, and it is
   currently the least visible thing in it.

---

## 3. Substantive findings

Ordered by what would block a merge. F1–F4 are on C/E; F5–F7 on B; the rest are smaller.

### F1 — ⚑ the devnet backfill **overrides an explicit genesis declaration** (E)

`node/src/lib.rs`, inside `if enable_faucet && !starbridge_seeded_from_genesis`:

```rust
s.coordination_fee_exempt = true;     // unconditional
```

Twenty lines above it, the fee-well backfill in the same block is guarded and says so:

```rust
if s.fee_well.is_none() {             // "so a genesis-configured well is never overwritten"
```

The coordination flag has no such guard. `starbridge_seeded_from_genesis` is only true when
`genesis.json`'s `starbridge_cells` seeded **≥ 1 cell**, so a node that boots *with* a
`genesis.json` declaring `coordination_fee_exempt: false` and no starbridge cells has that
declaration silently flipped to `true`.

C's own `state.rs` docblock states the reason the flag is genesis-declared: *"so every
committee node agrees — admission is consensus-relevant."* E defeats exactly that. Two
nodes on the same chain, one booted from genesis and one from the backfill path, disagree
on whether a `fee = 0` turn is admissible.

**Fix:** mirror the fee-well guard (only set when genesis did not declare it), and gate it
behind its own explicit switch — `--coordination-fee-exempt` or `DREGG_COORDINATION_EXEMPT=1`
— rather than riding `--enable-faucet`. A flag that changes admission should not be a side
effect of enabling a faucet.

### F2 — ⚑ the exemption removes the computron ceiling **entirely**, not just the charge (C)

The metering-honesty claim **checks out**, and I verified it rather than taking it:
`metering_budget = u64::MAX` means the tree walk never early-aborts, `computrons_used`
accumulates the true cost, and it is that variable — not `charged` — that lands in
`TurnReceipt.computrons_used` and in `TurnResult::Committed`. Receipts stay honest. ✓

But *honest metering is a reporting property, and the leash is the cap.* Before this change,
`turn.fee` was threaded into `execute_tree` as `budget` and checked at four points during
the walk (`execute_tree.rs:785, 1063, 1159, 1206`). An attacker had to fund the work they
asked for. After it, for the coordination class the bound is `u64::MAX` and the only thing
left standing between a request and the executor is `DefaultBodyLimit::max(MAX_BODY_SIZE)`
= **1 MiB** (`api.rs:1975`, layered on the whole router).

And `is_coordination` looks only at `balance_change` and effect kinds — **it does not look
at `Authorization`.** So an EmitEvent-only turn whose every action carries
`Authorization::Proof { .. }` is coordination, and `execute_tree.rs:1011` charges
`proof_verify` (1000, the most expensive entry in the table, precisely because it is real
verification work) for each one — now uncapped and free. That is the exact work the cost
model exists to bound.

**Fix:** make the exemption **bounded**, not infinite. `coordination_exempt_ceiling: u64`
with a real number (a chat turn measures ~1,254 computrons on your deployment; 100× that
is a generous ceiling and still finite). `u64::MAX` is the version of this change that
cannot be defended; a ceiling is the version that can.

### F3 — the class also zeroes the **budget-gate debit**, and two docblocks in this PR contradict each other (C)

`execute.rs:560` does `gate.try_debit(turn.fee, &turn_hash)`. With `fee = 0` that debits
nothing, so the Stingray silo budget gate does not bind on the exempt class either.

B's docblock says, of the fee loop: *"the debit + budget gate + 1/min faucet rate-limit
remain the oversight leash — no fee is zeroed."* True of B. C then zeroes the fee, and all
three of those legs go slack together. Both docblocks ship in this PR, one contradicting
the other.

**Fix:** state the residual leash accurately for the class. After C it is: the bearer token
on `/turns/submit`, the 1 MiB body limit, and (with F2 fixed) the ceiling. Not the debit,
not the budget gate, not the faucet rate limit.

### F4 — `EmitEvent` has **no cross-cell authority check**, so the free class is a free *attribution* path (C)

`apply.rs:1001` is explicit and deliberate: *"Authority is deliberately NOT gated here —
Lean's emit arm has no authority leg either; only the liveness leg is added."* Confirmed:
`apply_emit_event` checks membership and `accepts_effects()` and nothing else, and
`execute_tree.rs` has no `EmitEvent` arm at all.

This is **pre-existing** and matches the verified kernel — C does not introduce it. What C
changes is its price: emitting an event attributed to any cell in the ledger goes from
fee-bearing to free and (per F2) unbounded.

**Fix — and this is the cheapest high-value change in the review:** narrow the exemption to
`effect.cell == turn.agent`. That is the entire actual use case (`build_chat_turn` in D
emits on the signer's own cell, and the node derives `agent == derive_raw(signer, "default")`).
It costs one clause in `is_coordination`, kills F4 outright, and shrinks F2's blast radius
to self-attributed events.

### F5 — a third derivation of a cell that already has a canonical, test-pinned one (B)

`node/src/api.rs` gains `faucet_cell_id()`. But `node/src/genesis.rs:680` already exports
`pub fn devnet_faucet_cell_id()` — it existed at your merge base — and `api.rs:12670`
(`genesis_faucet_cell_matches_the_endpoint_faucet_cell`) already pins two independent
derivations against each other. The new third one is pinned by nothing. The values agree
today (`faucet_token_id()` is `default_token_id()`, api.rs:8215).

Per `CLAUDE.md`: *"Two shapes that agree today are two shapes that will disagree later."*

**Fix:** call `crate::genesis::devnet_faucet_cell_id()` from `lib.rs`; delete
`api::faucet_cell_id`.

### F6 — ⚑ the fee well can point at a cell that is not in the ledger, and the fee then **silently burns** (B)

`distribute_fee_shares` (`execute.rs:52-56`):

```rust
if let Some(wid) = fee_well {
    if let Some(w) = ledger.get_mut(wid) {
        let _ = w.state.credit_balance(fee - delivered);
    }
}
```

Absent well ⇒ the credit is dropped. `let _ =` also swallows a *failed* credit. Neither
path errors.

This matters because a `--enable-faucet` data dir with no faucet cell is a real
configuration — `POST /api/faucet` itself refuses it with *"faucet cell … is not in this
node's ledger — this data dir has no genesis"* (`api.rs:8497-8507`). On such a node, B's
backfill sets the well anyway, logs **"fee loop: … (recirculate, not burn)"**, and burns
every fee. The log now asserts the opposite of what happens. A documented behaviour that
cannot be detected is the failure mode this repo has a memory file about.

**Fix:** the backfill must check `s.ledger.get(&faucet).is_some()` before setting the well,
and warn loudly (or refuse) otherwise. Separately worth doing regardless of this PR: that
`let _ =` should not be silent.

### F7 — the "closed value set" holds only because nothing wires a proposer or treasury (B)

The split is proposer 50%, treasury 30%, well gets the remainder. `set_proposer_cell` and
`set_treasury_cell` (`turn/src/executor/mod.rs:2259, 2268`) have **zero callers anywhere in
`node/`** — so the well receives 100% and the claim "the {agents + faucet} value set is now
closed" is currently **true**. Verified, not assumed.

But it is contingent on an unstated premise. Wire either cell and 80% of every fee leaves
the set, and the drain returns at 1/5 speed — which is slower and therefore harder to
notice than the failure you originally hit. `faucet_steady_state_solvency.rs`'s `run_turn`
builds its executor with neither set, so the test's green depends on the same unstated
premise and cannot see it change.

**Fix:** add a case with a proposer wired that asserts the escape (documents the boundary),
or assert the precondition explicitly in the test.

### F8 — `#[serde(default)]` names a constituency that does not exist (C)

You asked implicitly and the brief asked explicitly: **is the default right?** Yes.
`false` is fail-closed, legacy-identical, and correct.

The *justification* is wrong: **nothing in the workspace deserializes `ComputronCosts`.**
No config file, no wire message — the `Serialize`/`Deserialize` derive is entirely
unexercised, and every construction site is `default_costs()` or `zero()`. Per `CLAUDE.md`,
compatibility is not a constraint here and a compatibility claim with no holder is the thing
to delete.

**Fix:** keep the attribute if you like (it costs nothing and is right if the struct ever
becomes configurable); delete *"keeps persisted/wire cost configs compatible"* from the comment.

### F9 — client and node negotiate the class through two unconnected switches (C + D)

The client decides `fee = 0` from `DREGG_COORDINATION_EXEMPT` (an env var read in
`fee_cost_model()`); the node decides from genesis or boot mode. There is no handshake, and
a mismatch is **silent**: the client posts `fee = 0`, the node rejects `BudgetExceeded`.
That is precisely the "necessary but not yet sufficient" state your PR body reports.

The client already calls `fetch_executor_federation_id()` on every send.

**Fix:** serve `coordination_fee_exempt` on that same endpoint and have the client read it.
That deletes the env var, deletes the failure mode, and removes the client's need to guess
the node's cost model.

### F10 — the class silently reprices node-internal turns too (C)

`submit_queue_drainer.rs:590, 654, 1098` and `relay_slash_submit.rs:100` size node-generated
turns with `new_submit_executor(&s).estimate_cost(&turn)`, which routes through
`configure_turn_executor` and therefore inherits `costs.coordination_exempt`. Any
node-internal EmitEvent-only turn becomes `fee = 0` when the flag is on. Plausibly intended,
but it is wider than "chat is free" and nothing tests it.

### F11 — substrate, said out loud

**This PR touches no AIR, no circuit, no constraint and no gadget**, so the Lean-authoring
law is not in play. But two things are worth stating plainly, because they cut in opposite
directions and both are load-bearing for how much this review is worth:

- `grep -rl 'computron' metatheory/Dregg2/` returns **nothing**, and
  `Exec/TurnExecutorFull.lean` has no notion of fee. **Computron metering is a wholly
  Rust-side, unverified admission policy.** So C cannot introduce a Lean/Rust divergence —
  the verified kernel never modelled the gate it changes. Your
  `coordination_exempt_differential.rs` is therefore *true but weak by construction*: it
  would pass whether or not the exemption were sound. Worth keeping (it pins that the
  committed state transition is untouched, which is the thing it can pin), not worth
  citing as evidence about the exemption itself.
- Conversely: nothing verified vouches for any of this, and `Turn::is_coordination` is a
  **new consensus-relevant classification that lives only in Rust**. That is where the
  review weight has to go, and it is why F1 (nodes disagreeing about it) is the finding I
  would block on.

---

## 4. Evidence class and acceptance criteria, per piece

### A — `sdk: restore BudgetSpec root export`

- **Evidence:** the compiler, via a 5-line compile canary. Terminal — nothing more is
  obtainable or needed.
- **Accept when:** it merges. It already builds against HEAD by inspection (`BudgetSpec` is
  `pub` in `dregg-token`).
- **Verdict: take as-is.**

### B — `fee: fee well as revolving faucet`

- **Evidence:** ~800 live turns on your fork, plus 4 tests including
  `control_no_fee_well_drains_faucet_to_insolvency` — a **control that reproduces the
  original drain**. That is the good shape: a falsifier that actually falsifies, pinning
  the pointer change as the *cause* of solvency rather than a correlate. Strongest evidence
  in the bundle.
- **Accept when:** F5 (use `genesis::devnet_faucet_cell_id`, drop the duplicate), F6 (refuse
  or warn when the faucet cell is absent from the ledger — do not log "recirculate" and burn),
  F7 (make the proposer/treasury premise visible in the test).
- **Verdict: take, after F5/F6.** F7 can be a follow-up.

### C — `turn+node: coordination-exempt admission class` (node half)

- **Evidence:** 7 unit tests in `coordination_fee_exempt.rs` locking both sides of the flag,
  the no-leak case (a `Transfer` at `fee = 0` still rejects under `exempt = true`), honest
  `computrons_used`, and the `estimate_cost` / `validate_without_apply` mirror. Genuinely
  well-shaped for what it tests. Plus the Lean differential, discounted per F11.
- **Blind by construction to:** F2 (no test submits an oversized coordination turn) and F4
  (no test emits on a foreign cell). Both are exactly the cases the exemption newly makes free.
- **Accept when:** F2 (bounded ceiling, not `u64::MAX`) with a test that a turn over the
  ceiling still rejects; F4 (narrow to `effect.cell == turn.agent`) with a test that a
  foreign-cell emit is not exempt; F3 and F8 (docblock corrections — the contradiction and
  the phantom constituency).
- **Verdict: take after F2 + F4.** Those two are the merge blockers, and both are small.

### D — `sdk-net: dregg-client-sign`

- **Evidence:** continuous live dogfood — your fleet signs with it daily — plus 4
  `funding_shortfall` unit cases. Real, but it is evidence about *your* deployment, and it
  is the only piece here whose evidence we cannot reproduce.
- **Risk shape:** touches nothing existing; the failure mode is "the tool is wrong", not
  "the chain is wrong". That earns a lower bar than C — but not a free pass: a `src/bin/`
  target is auto-discovered, so every `cargo build -p dregg-sdk-net` builds it forever after.
- **Accept when:** it builds and clippy-passes in our workspace; F9 (read the node's exempt
  flag over HTTP instead of `DREGG_COORDINATION_EXEMPT`) — this is what makes the tool
  correct against *any* node rather than only against a node configured to match its env;
  and rename `materialized` → `needs_materializing` in `funding_shortfall` so the next
  reader does not re-derive the confusion in the PR body.
- **Verdict: take as its own PR**, reviewed as a tool. F9 is the one substantive ask.

### E — `node: enable the coordination class at the genesis-less devnet boot`

- **Evidence:** one incident narrative — and the PR body itself reports the class was *not
  active* on the running node, so this commit's effect was never actually observed. Thinnest
  evidence, widest blast radius.
- **Verdict: refuse as written.** Not because turning it on is wrong, but because F1 makes
  it override an explicit genesis declaration on a consensus-relevant flag, and because it
  rides `--enable-faucet` rather than saying what it does. Resubmit as: guarded like the
  fee-well backfill, behind its own switch.

---

## 5. Recommendation

**Carve, on the seams in §2, and do not rebase — the branch merges clean.**

- **Take now:** A.
- **Take after small fixes:** B (F5, F6), C (F2, F4).
- **Take separately, as a tool:** D (F9).
- **Refuse and reshape:** E (F1).

If the operator wants one merge rather than five, the shortest defensible path is
**A + B + C with F2 and F4 fixed, E dropped**, and D as a follow-up PR. That gets the fee
loop and the exempt class — the parts that touch our surfaces and carry the live evidence —
without the 1,025-line tool riding along on their credibility, and without the 18 lines
that make two nodes disagree about what is admissible.

**What is not in dispute:** the fee loop is a real fix for a real drain, the control test
proves it, and the metering-honesty claim on the exempt class is **true** — I checked it
against `computrons_used`'s path into the receipt rather than taking the docblock's word.
The disagreements above are about the *bound* (F2), the *scope* (F4), and *who decides*
(F1) — not about whether the diagnosis is right. It is.

**On effort:** the offer in #74 to do the carving is appreciated and accepted for the seams
in §2, but the rebasing half is unnecessary. If it is easier, land the fixes as additional
commits on the existing branch and we will cherry-pick along the seams — the file split is
clean enough that no interactive surgery is needed.

---

## Appendix — what was verified, and how

| claim | how checked |
|---|---|
| branch merges clean into HEAD | `git merge-tree --write-tree HEAD akapug/lane-fee-loop` → tree `4c7a236e4`, no conflict paths |
| the title bug lives only in the new file | `grep -rn 'funding_shortfall'` over `main`: zero hits outside the PR |
| `BudgetSpec` unused in-repo | `grep -rn BudgetSpec sdk/ dregg-sdk-net/`: zero hits |
| when the export was dropped | `git log -S BudgetSpec -- sdk/src/lib.rs` → `65aabc8aa`, 2026-07-20 |
| D's deps all present, `NodeHttpClient` un-gated | `dregg-sdk-net/Cargo.toml` + `lib.rs:95` (no `cfg`) + the three method defs in `node_world_sink.rs` |
| metering stays honest | `metering_budget = u64::MAX` ⇒ no early abort; `computrons_used` (not `charged`) flows to `TurnReceipt.computrons_used` and `TurnResult::Committed` |
| the ceiling is gone | `budget` is checked at `execute_tree.rs:785, 1063, 1159, 1206`; only remaining bound is `MAX_BODY_SIZE = 1 MiB` (`api.rs:1975`, layered on the whole router at `2559`) |
| `Authorization` is not consulted by `is_coordination` | read the predicate; `proof_verify` charged at `execute_tree.rs:1011` |
| `EmitEvent` has no authority gate | `apply.rs:984-1016` + zero `EmitEvent` arm in `execute_tree.rs` |
| a duplicate faucet derivation already existed | `node/src/genesis.rs:680`, present at the merge base; pinned by `api.rs:12670` |
| absent fee well burns silently | `execute.rs:52-56`, `let _ = w.state.credit_balance(...)` inside `if let Some(w)` |
| proposer/treasury unwired | `set_proposer_cell`/`set_treasury_cell`: zero callers in `node/` |
| `ComputronCosts` never deserialized | `grep -rn ComputronCosts` workspace-wide: only `default_costs()`/`zero()` constructions |
| Lean models no fee | `grep -rl computron metatheory/Dregg2/`: nothing; `Exec/TurnExecutorFull.lean` has no fee |

**Not verified:** the merged tree was **not built**. `merge-tree` proves textual
mergeability, not compilation — the two `NodeStateInner` literal sites match the PR's two
additions and no symbol collides, so it is expected to build, but that is inference, not a
green. Whoever lands each piece should build it.
