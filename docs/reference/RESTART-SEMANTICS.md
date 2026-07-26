# Restart semantics — what the ABSENCE of a guard means

**The rule, in one line: every guard held in RAM must declare what its absence means, and absence
must never silently mean *allowed*.**

This exists because an audit of every bot surface for transient state came back with a sharper
finding than "some data is lost":

> The dominant sub-class is not "data is lost", it is **a GATE falls open when its state is
> absent**. Four of the top six findings are authorization or idempotency guards whose backing
> state is an empty `HashMap` at boot, so they do not refuse — they *proceed*.

That is not eleven bugs. It is **one missing decision**, taken eleven times by default, in the
direction that happens to compile.

## What counts as a guard

Anything an in-RAM value is consulted for in order to **refuse**:

* an authorization record — *who opened this run, who may end it*;
* an idempotency cursor — *what sequence number have I already acted on*;
* a dedupe set — *have I already credited this payment*;
* a resolution record — *is this match already over*;
* a ceiling — *has this user spent their budget*.

At boot every one of them is empty. So "what does this code do when the map is empty?" is **not an
edge case** — it is the state the process is in *every single time it starts*, and it is a state an
adversary gets to choose by waiting for (or causing) a restart. A deploy is an attack window.

## The three legal answers

Pick one **and write it down**, as a `RESTART:` line in the doc comment on the state itself.

### 1. REFUSE — absence denies

The gate closes when it cannot prove the actor is allowed.

Correct when the guarded act is irreversible **and the legitimate actor has another way through**.
The burden you take on with REFUSE is showing that nobody is *stranded*: a fail-closed gate that
permanently bricks a live game is not a fix, it is a different outage. If you cannot show the exit,
you want answer 2.

### 2. REBUILD — absence is repaired before the decision is taken

The fact is genuinely durable — it is on disk, in sqlite, or on-chain — and boot simply never read
it. Read it, then decide.

**This is the right answer far more often than it looks.** In this codebase the *substrate* is
almost always already durable (the gallery, the crown board, the descent board, the character
sheets, the credit ledger, the treasury, the offering move-logs — all sqlite or file-backed, all
installed at boot). The wound is one level in: **a durable substrate paired with an in-RAM key,
guard, or cursor that something else assumes survived.** The command sequence was already on-chain
and simply not read at boot. The seat key already survives restart while the record of *how the
match ended* did not. Look for the durable thing that is already there before you build a new store.

### 3. PROCEED, deliberately — absence allows, and that is argued

Forgetting is the safe direction. A rate-limit bucket that only ever punishes; a negative cache; an
in-flight lock with no `Drop` to release it; a per-user toy counter with no external claim.

The argument must name **what an adversary gains by forcing the restart, and why it is nothing.**
"It seemed fine" is not the argument.

### What is not an answer: silence

```rust
let gate = state.get(&channel).map(|d| authorize(d));
if let Some(Denied { .. }) = gate {
    return refuse();
}
// … falls through and does the thing
```

That is answer 3 with the argument omitted. `None` matches no arm, so an empty map is a green light.
Four of these shipped. If your refusal is a pattern match on `Some(..)`, the `None` case is a
decision you have already made — make it on purpose.

## Two corollaries, each paid for by a real finding

### A durable store does not make its KEY durable

`pay_processed` is a sqlite table with `reference TEXT PRIMARY KEY`. It is a perfect idempotency
guard. The bug was that the reference was minted as `sol:{addr}:{slot}:{amount}` from the RPC's
*current* slot — a number that advances every ~400ms — so the key was fresh on every poll and the
table could never recognise a repeat. The only thing making the path idempotent was an in-RAM
`last_seen` map, and that is empty at boot.

**When you ask "is this idempotent across a restart", check the key, not the table.** A durable
table keyed by a value the process invents is a durable table that dedupes nothing.

### Do not persist a guard whose absence is the forgiving direction

Answer 2 is *not* "persist everything". Persisting the wrong thing makes the opposite bug durable:

* persisting the payment watcher's `last_seen` would have made a **lost** credit permanent — a sweep
  plus a deposit between two polls lost money, and a restart was the only thing that healed it. (The
  landed fix deletes that map instead: see the fourth row below.);
* persisting `pay.rs`'s `credit_holds` would strand an `AlreadyInFlight` reservation that no `Drop`
  could ever release — the player could never spend again;
* persisting `throttle.rs`'s buckets only ever punishes: the limiter is explicitly not a security
  boundary, and a restart forgiving a rate limit is correct.

A bloated store is its own bug. Verified-transient state is a legitimate, documented answer 3.

## The test obligation

A fix to a restart-semantics wound is not landed until it has:

1. **a restart test** — write, drop the in-RAM holder, reopen from the durable source, assert. Not
   "the value round-trips": assert on *the decision the guard makes* after the reopen;
2. **an authority test**, wherever a gate is involved — after the restart, the unauthorized actor is
   still refused. A restart test that only shows the authorized actor still works cannot tell a
   rebuilt gate from a deleted one;
3. **a red-proof** — break the fix, watch the test fire, restore it. Record the exact mutation and
   the exact output. A gate that cannot go red is not a gate.

## The tooth

`discord-bot/tests/restart_semantics_declared.rs` walks every `Mutex<HashMap<…>>` /
`RwLock<HashMap<…>>` / `Mutex<HashSet<…>>` in `discord-bot/src` and fails unless a `RESTART:` line
appears in **that item's own** doc comment. It cannot check that the declaration is *true* — no
test can — but it makes the omission impossible to commit, which is the failure mode that produced
this document.

⚑ Two things about it were paid for immediately, and both are the same lesson at one level up:

* **The lookback must be contiguous, not a line budget.** The first draft searched 40 lines up. A
  sibling lane found the hole inside an hour: `PayState::credit_holds` reported as "declared" while
  carrying no declaration at all — it was inheriting a paragraph written about `PayState::watcher`
  twenty-three lines above. *Any field within the budget below a declared one silently borrowed its
  answer.* The walk now climbs only over the item's own contiguous comment/attribute preamble and
  stops dead at the first line that is neither, with exactly one permitted hop past an enclosing
  `fn accessor() -> &'static Mutex<…>` that owns a `static` in its body. A gate that accepts a
  neighbour's answer is not detecting the omission — it is laundering it.
* **The syntactic match must be normalised.** `std::sync::Mutex<std::collections::HashMap<…>>` is
  the same shape wearing a hat, and it hid from an earlier draft. Path prefixes are stripped before
  matching. A syntactic lint has to close its holes explicitly; that is the price of not needing a
  type-checker.

The test also asserts a floor on how many declared sites it found, so a refactor that renames every
map out of these shapes fails loudly rather than turning the gate into a green vacuity.

The other crates in this family are declared in prose at the site:
`dreggnet-web/src/table_seats.rs` (the table registry) and `dregg-pay/src/watcher.rs` (the payment
watcher).

## The four this document was written for

| site | the guard | answer taken |
|---|---|---|
| `discord-bot/src/commands/fiction.rs` `meta()` | who hosts a `/dungeon` run, and when the round opened | **REBUILD**, with a REFUSE floor (`opener = NO_HOST`, window restarts) |
| `dreggnet-web/src/table_seats.rs` `TableRegistry` | is this table over / whose clock is running | **REBUILD** from the durable table record |
| `discord-bot/src/bot_reactor.rs` `last_seq` | which on-chain command have I already reacted to | **REBUILD** from the committed `CMD_SEQ_SLOT`; unreadable ⇒ REFUSE to fire |
| `dregg-pay/src/watcher.rs` `last_seen` | have I already credited this payment | **REBUILD** — the transaction signature is the key, and the durable ledger is the cursor. `last_seen` is **deleted**, not persisted: the production watcher now holds no process state at all |

The fourth is the one worth reading twice, because it is the corollaries in practice. The naive fix
— persist `last_seen` — was available, small, and *wrong*: it would have made the lost-credit bug
durable while curing the double-credit. The naive key fix was equally wrong: no sound idempotency
key is derivable from `getTokenAccountsByOwner` at all (`(addr, amount)` is restart-stable but
collides with a post-sweep re-deposit at the same total; `(addr, slot, amount)` distinguishes the
re-deposit but is restart-unstable, which is exactly the shipped bug). The answer was to stop
crediting off balance totals and credit per transaction, keyed on the signature — a fact of the
chain, not of the process. The watcher then needs no cursor, because the durable `pay_processed`
table already is one.
