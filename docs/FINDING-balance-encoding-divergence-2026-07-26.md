# A signed balance crosses a proof boundary in THREE different encodings

*2026-07-26. Written while landing the limb-PI wiring, which is the thing that made it
visible. This is a **finding with a decision attached, not a repair** — the repair moves a
wire format, and wire formats are ember's call.*

## The one-paragraph version

`Dregg2/Bignum/LedgerBalance.lean` §7 already says half of this: the BYTE path biases a
signed balance and the FELT path does not, and it names that divergence as §2's root. The
half it does not say is that there are **three** encodings live, not two, and that the third
one has no notion of sign at all. All three are described in their own doc comments as "the
balance at the PI boundary". They disagree for negative balances, and one of them silently
truncates above 2⁶¹.

## The three

| # | site | encoding | domain |
|---|---|---|---|
| 1 | `cell/src/state.rs:1186` `balance_biased` → `encode_balance_le` | `(b as u64) ^ 2⁶³` — order-preserving, injective | `i64` |
| 2 | `turn/src/executor/proof_verify.rs:2607` `extract_burn_binding_params` | `balance_biased` — the same one | `i64` |
| 3 | `turn/src/rotation_witness.rs:109` `balance_lo_felt` / `:115` `balance_hi_felt` | `split_u64(balance as u64)` — **raw two's-complement cast**, no bias | `i64` |
| 4 | `circuit/src/effect_vm/cell_state.rs:16` `CellState.balance` → `split_u64` | unsigned; the type is `u64` and **there is no sign to encode** | `u64` |

(3) and (4) share the `split_u64` limb shape but not the value: (3) casts a signed balance
into it, (4) never had one.

## Why it matters, precisely

**The bias is what makes comparison work.** `biased_lt` in `LedgerBalance.lean` is proved:
`biased a < biased b ↔ a < b`. That theorem is the licence for treating an unsigned limb
comparison as a signed balance comparison. Path (3) does not apply the bias, so it does not
inherit that theorem — an unsigned comparison on its limbs is *not* the signed comparison
for any negative balance, and the issuer well's `−supply` is exactly the negative balance
the system is built around.

**Path (3) also breaks reconstruction, independently of sign.** `split_u64` computes
`hi = val >> 30` (up to 2³⁴) and then calls `BabyBear::new(hi)`, which reduces mod
`p ≈ 2³¹`. For any `val >= 2⁶¹` the high limb wraps and `join_u64` no longer returns `val`.
A raw-cast negative balance is `≈ 2⁶⁴`, so it is *always* past that wall. A biased balance
is `≈ 2⁶³`, so it is **also** always past it: **the bias alone does not fix path (3)**, and
"route the felt path through `balance_biased`" is therefore not a one-line change. The
30/34 split is sized for a value under 2⁶¹, and both signed encodings exceed it.

## What that means for the repair

The obvious move — swap `balance as u64` for `balance_biased(balance)` in
`rotation_witness.rs` — would make (3) agree with (1) and (2) on *encoding* while leaving
it broken on *range*, and it would move every state commitment the rotated witness
produces. Two consequences, both flag-day:

* every existing rotated proof stops verifying (the pre-limbs change ⇒ `state_commit`
  changes), and
* the limb split needs re-sizing, or the biased value needs a wider decomposition — which
  is the `Dregg2/Bignum` limbed representation that is already written and, per
  `project-felt-width-repair-campaign`, about 3% adopted.

So the honest sequencing is: **this rides the re-genesis flag day that is already in
flight** (`HORIZONLOG.md`, `a0687f268`), or it waits. It should not be slipped in as an
encoding tweak, because the range half would still be wrong and the resulting agreement
would be cosmetic.

## The decision, stated for ember

1. **Do all three encodings need to agree?** (1) and (2) are commitment/binding-side; (3)
   is the rotated state-block witness; (4) is a genuinely unsigned model. It is defensible
   that (4) stays unsigned and the signed ledger lives one layer up — but then (3) casting
   an `i64` into (4)'s limb shape is the bug, and it should not compile.
2. **If they must agree, the target is the biased encoding in a limb split that holds it** —
   i.e. the `Bignum` adoption, not a bias bolted onto the 30/34 split.
3. **Sequencing:** flag day, with the re-genesis already authorized, or explicitly deferred.

## What was landed instead, today

Nothing on the wire. What went in is the check that made this legible and that was itself
inert: `verify_balance_limb_pis` is now called on every effect-vm leg
(`sdk/src/full_turn_proof.rs`, `turn/src/conditional.rs`) and has a test file
(`circuit/tests/balance_limb_pi_gate.rs`). Note what that check can and cannot see: every
limb it range-checks comes from `split_u64`, whose outputs are in range *by construction*,
so the gate is a **forgery filter over the wire**, not a validator of honest values. It
cannot detect any of the divergence above. That is the correct scope for it — and it is
also why the divergence survived this long with a check sitting next to it.
