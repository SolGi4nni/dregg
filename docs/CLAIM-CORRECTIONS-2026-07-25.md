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
