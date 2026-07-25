# Claim corrections — read before publishing anything (2026-07-25)

Three public-facing claims were falsified by lanes tonight. Two of them are in the
draft Sunday announcement. **Fix the copy before it ships, not after someone checks.**

---

## 1. ⚠ "A whole match folds into ONE proof" — FALSE IN PRACTICE for automatafl

**Draft copy:** *"A whole match folds into ONE succinct proof a light client checks
in O(1) — the moves are never posted. The board keeps the proof, not the plays."*

**What the design-audit lane found**, at `dregg-automatafl/src/surface.rs:13-17`, in
the crate's own words: the deployed surface resolves a move clash by **DROPPING
MOVES**, which is the audited-wrong rule, and `unfoldable_round` then marks that
match unfoldable. Measured over driven matches: **10 of 10 contained at least one
clash** (16.9% of rounds conflict in competent play).

So **no real automatafl match folds to a proof.** The signature mechanic — the
simultaneous-move conflict that makes the game interesting — and the folding proof
are mutually exclusive as deployed.

The fold machinery is real; it is the *surface's* clash rule that is wrong. Fixing
the surface to the proven rule is the repair, and until then the sentence must go.

## 2. ⚠ "Sealed orders / sealed simultaneous moves" — TRUSTED-HOST, not cryptographic

`dregg-automatafl/src/surface.rs:850` stores the **plaintext** move server-side at
commit time. The seal hides by **non-reveal on a trusted host**, not by a
commitment between clients. The crate is honest about this at `surface.rs:47-49`
and names the in-proof version as future work.

Anything implying a player's sealed move is cryptographically hidden *from us* is
false today. "Nobody sees your move until reveal" is true; "we cannot see it" is
not.

(The **Bazaar's** sealed orders are a different mechanism and a stronger one — that
copy stands. Do not let this correction bleed onto it.)

## 3. ⚠ "You can lose" — was FALSE, being fixed

Two lanes independently enumerated the deployed Descent teeth: `flee` costs one
breath from any depth, and a non-fleeing run can burn at most 21–26 of 26. **On 14
of 16 daily maps there is no reachable position from which you cannot go home.**
Every run banks; nothing is ever lost. Days 9 and 13 have exactly one lethal state.

The fix (`ascend` + `flee` gated on `depth == 0` + `BREATH` 26→30) is enumerated
over all 16 maps — all stay completable, zero deathless days — and is landing. Hold
the claim until it does.

---

## The pattern, and the standing rule it earns

All three share a shape with the six "guards that guard nothing" found tonight: **a
mechanism exists, is named accurately in one place, and is contradicted by what the
deployed path actually does.** In every case the honest description was *already
written down in the crate*, in a doc-comment nobody read before writing copy.

**Rule: before any public claim, open the file that implements it.** Not the doc,
not the commit subject, not the memory — the implementation. This session put a
whole announcement together from commit subjects that said `Test file only` in
their own bodies, and it took ember reading it to catch that.

Related: `feedback-a-doc-comment-is-a-name-not-a-proof`,
`feedback-commit-subjects-are-claims`.

---

## 4. ⚠ RETRACTED BY ME — "automatafl is a dead draw between competent players"

A design-audit lane reported that automatafl draws structurally: two one-ply
simultaneous-minimax seats drew 6/6, a 5× search-budget advantage still drew 5/5,
and the position freezes in 8–11 turns. **I relayed that conclusion to ember
without interrogating its method. It does not support the claim.**

**Why the evidence does not reach the conclusion:**

1. **Two DETERMINISTIC agents on a MIRROR-SYMMETRIC board play mirror-symmetric
   games.** The observed freeze is an artifact of determinism plus symmetry, not a
   property of automatafl.
2. **In a SIMULTANEOUS-move game, optimal play is generally MIXED.** A deterministic
   one-ply agent is not a weak player — it is the wrong kind of object. It cannot
   reason about the opponent reasoning about it, which is the whole game. Sealed
   simultaneous choice is precisely where pure strategies fail.
3. **"5× the search budget" at fixed one-ply depth buys nothing.** Budget is not
   depth. The asymmetric run varied a parameter that could not affect the outcome
   and read the null result as robustness.

So the measurement is real and the interpretation is wrong: it measured *these
agents' inability to break a position*, and reported it as the position being
unbreakable.

**ember's argument, which is the decisive one:** *"if the mechanics are purely
symmetric so that all asymmetry comes from inside the players then… that's just
chess."* Symmetric mechanics with asymmetry arising from PLAY is the definition of
the abstract-strategy genre — chess, go, hex. "Both sides can restore parity" would
indict every one of them. And AIs have never played automatafl competently, so no
bot result should be read as a statement about the game.

**Standing:** automatafl needs NO asymmetric opening. That recommendation is
withdrawn.

**What the lane's automatafl work leaves standing** (different evidence, unaffected):
- `adjudicateCapped` — the deployed surface already capped at `MAX_TURNS = 64` and
  called it a draw, a terminal rule that lived in Rust and in NO theorem. Proving it
  is right regardless of how often the cap is reached.
- The clash/fold finding (§1 above) — a code reading, not a play result.
- The merge-clause vacuity at n=2 and turn-vs-match termination — both structural.

**The tug findings also stand**, on different evidence: the 66% no-winner rate is a
measurement of OUTCOMES against an absolute threshold (traced to tied rows going
uncontrolled, with charm summing to 21 under exclusive control), and the missing
I-cut-you-choose is a reading of the Lean, not a play result.

**The lesson, and it is mine:** I have spent this session telling lanes not to trust
doc-comments, commit subjects, or names — and then took a lane's *conclusion* at
face value without checking whether its *method* could support it. A measurement is
evidence about the thing measured. Two blind agents drawing is evidence about the
agents.
