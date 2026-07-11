# The Trust Levels — what a stranger can actually verify

The pitch is "an AI game-master you can trust." That's not one claim; it's a **ladder** of
independent, checkable guarantees. This doc says exactly what each rung proves, what it assumes,
and what is still open — honestly, so the word "verifiable" means something specific.

Verification is reported as **levels, never one green check** (`GameSession::verify_report()` returns
`{chain, replay}` separately). A viewer sees which guarantees hold, not a misleading boolean.

---

## Level 0 — Integrity: the history is untampered
**`GameSession::verify()`** re-checks the receipt hash-chain: every turn is a prev-linked
`LedgerEntry` binding `(seq, prev, narration, effect, prompt_binding, game_binding, randomness,
attestation)` through `chain_receipt_id`. Truncation, reordering, splicing, or altering any bound
field breaks the chain.

- **Proves:** the recorded history is a single, untampered, well-linked sequence.
- **Does NOT prove:** that each recorded *effect* was the rule-correct one. A party who hand-built a
  chain could pair `action = Move` with `effect = GrantItem` and still pass Level 0. That gap is
  what Level 1 closes.

## Level 1 — Rule-correctness: re-execute and check
**`GameSession::verify_replay()`** re-derives the world from genesis and, for every turn, recovers
the bound typed `GameAction`, re-runs the *same* `resolve_action`, and checks the recorded effect
equals the recomputed one. It does not advance past a mismatch.

- **Proves:** every effect was the world-legal resolution of its bound action — "the AI narrated,
  but the *world* resolved." The headline test forges one move's effect, re-links the chain so
  Level 0 *passes*, and Level 1 **catches** it (`ReplayMismatch::Effect`).
- **For random turns** it also reconstructs the verifiable draw (below) and checks the outcome —
  proving randomness-correctness, not just rule-correctness (`ReplayMismatch::Randomness`).
- **Assumes:** "the resolver is the rules." This is the **trust-minimized re-execution** layer (the
  verifier runs the real resolver as an executable spec), *not* a succinct/zk proof.

## Level 2 — Fair randomness: the roll isn't grindable
Random game events (loot, and in future crits/skill-checks) draw from **`dregg-dice`**: a
domain-separated `EventId` binds the request *before* the result, an indexed reject-free unbiased
draw stream (Lemire wide-multiply — a real chi-square-tested d-N), and a pluggable
`RandomnessSource` whose verifier is pure and source-free (a light client checks a draw it never
produced). The draw is bound into the receipt and reconstructed at Level 1.

Trust rises with the source — stated honestly per source:
- **CommitReveal (shipped):** neither party can *choose* the outcome, and the draw is fully
  reconstructible. It does **not** prevent selective abort (a last revealer withholding).
- **LB-VRF (`pqvrf/`, shipped, wiring in progress):** a **post-quantum** lattice VRF (Esgin et al.
  FC 2021, Set I) whose **uniqueness reduces to Module-SIS** — and that reduction is *proved in the
  Lean* (`Dregg2/Crypto/VRF.lean`, `lattice_vrf_unique_under_msis`) and *exhibited in the crate's
  MSIS-extraction test*. So the server cannot produce a second output. `pk = A·s`, `v = ⟨b,s⟩`
  pinned by the secret. **Assumes** pseudorandomness from MLWE (the Lean's undischarged obligation);
  **is one-time** per key (Set I — rotation for more).
- **Hybrid VRF + delayed beacon (designed; scaffolding parked):** adds timeout finalization so
  withholding buys no reroll. **Open gap:** a real drand-BLS beacon (the shipped test beacon is a
  forward-secure hash chain; the consensus `BeaconSpace` in the Lean is honest-leader liveness, a
  different object).

## Level 3 — Succinct proof (frontier, not built)
Fold the critical resolver invariants **in-circuit** via dregg's `circuit`/`circuit-prove` machinery
so a *succinct* proof attests rule-correctness without full replay. Smallest first invariant:
**inventory conservation** (no item created/destroyed except by an authorized transfer). This is the
zk frontier — designed (`docs/DESIGN-verifiable-game.md`), not yet implemented. **Honest caveat:**
dregg's ultimate STARK soundness is an *assumption*, not a discharged proof — so this rung would be
"verifiable under the deployed prover assumptions," never "trustless from first principles."

---

## Standing honest caveats (not swept under "verifiable")
- The attestation's **authentic** leg is an in-tree fixture — it does *not* prove a real model
  produced the narration bytes. The *well-formed* leg (a JSON-parse certificate) is genuine.
- The `/party` collective vote is a **majority tally**, not the quorum-certified
  `CollectiveChoiceEngine` (that's what The Commons uses); upgrading it is queued.
- None of this is audited production cryptography. It's a high-assurance reference stack where each
  guarantee names its own floor.

**The through-line:** each rung is independent and each names what it rests on. "Verifiable" here
means *this specific ladder*, checkable by a stranger — not a marketing word.
