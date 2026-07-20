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
- **LB-VRF (`pqvrf/`, shipped + wired into the engine):** a **post-quantum** lattice VRF (Esgin et al.
  FC 2021, Set I) whose **uniqueness reduces to Module-SIS** — and that reduction is *proved in the
  Lean* (`Dregg2/Crypto/VRF.lean`, `lattice_vrf_unique_under_msis`) and *exhibited in the crate's
  MSIS-extraction test*. So the server cannot produce a second output. `pk = A·s`, `v = ⟨b,s⟩`
  pinned by the secret; a forged proof is rejected on replay via `pqvrf::verify`. **Assumes**
  pseudorandomness from MLWE (the Lean's undischarged obligation); **is one-time** per key.
- **Hybrid VRF + beacon + timeout (shipped):** mixes the LB-VRF output with a **real threshold
  drand-BLS beacon** (quicknet, interop-tested against a published League-of-Entropy round), and adds
  **timeout finalization** so a withholding server gets no reroll (junk in the ignored VRF fields
  yields the *same* seed). This closes the grinding hatches: genesis-committed key-chain (#1),
  schedule-bound + BLS-verified beacon (#2), one-output-per-input (#4), timeout-no-reroll (#5).
  **Remaining:** an HTTP round-fetch client (verification is done; only the network fetch is a client
  concern) and MLWE-assumed pseudorandomness.

## Level 3 — Succinct proof (frontier, not built)
Fold the critical resolver invariants **in-circuit** via dregg's `circuit`/`circuit-prove` machinery
so a *succinct* proof attests rule-correctness without full replay. Smallest first invariant:
**inventory conservation** (no item created/destroyed except by an authorized transfer). This is the
zk frontier — designed (`docs/DESIGN-verifiable-game.md`), not yet implemented. **Honest caveat:**
the deployed prover's per-fold FRI column reads 112 bits at the arity-2
`ir2_leaf_wrap_config()` (`FriLedgerSound.rotatedLeafWrap_ledger_perFoldBits`) and **109** at the
arity-8 `ir2_config` leaf mint (`FriArityTransfer.arity8_perFold_soundness`), where ~112.6
**provably fails** (`FriArityTransfer.arity8_error_not_lt_2e112`); the deployed **commit
column binds below both, at 51** (`FriDeployedHeightPairing.deployed_wrap_commitBits`).
⚑ None of these is a *discharged proof* of soundness — they are readings of a knob ledger
transcribed from BCIKS20; `FriLdtExtractV3` is assumed. The chain is the BCIKS20
correlated-agreement chain over the deployed rate-1/64 BabyBear code
(`metatheory/Dregg2/Circuit/BabyBearFriDeployedInstance.lean`,
`FriCorrelatedAgreementSharp.lean`) — resting on named hypotheses (Poseidon2
collision-resistance on the floor). So this rung would be "verifiable under a proven,
named-floor prover," never "trustless from first principles."

---

## Standing honest caveats (not swept under "verifiable")
- The attestation's **authentic** leg is *policy-graded*, not one thing. The default carrier is an
  in-tree self-signed fixture — it does *not* prove a real model produced the narration bytes, and a
  verifier demanding `AuthenticPolicy::RequireMpcTls` (`verify_zkoracle_with_policy`) **refuses** it.
  `DmAttestationCarrier::attest_narration_live` (behind the `tlsn-live` feature) fuses a genuine
  MPC-TLS 2PC presentation as the authentic leg, and `deos_hermes::attest::attest_turn_bedrock`
  (`zk-live`) binds a live Bedrock TLS session to the completion the model actually returned. The
  *well-formed* leg (a JSON-parse certificate) is genuine on every path; "provably came from a real
  model" holds only on the Bedrock path.
- The `/party` collective vote is now **quorum-certified** on the real `collective-choice` engine
  (the same substrate The Commons uses): each ballot is a `WriteOnce` cap-bounded turn on a
  factory-born ballot cell, the tally is `Monotonic`, and a round certifies only once the polis
  `AffineLe` quorum gate (M = 3 of the 5-seat roster) admits the decision-turn — a quorum-met close
  emits a verifiable quorum certificate (with a light-client recomputation of the cast log), not a
  bare count. **Honest gap:** the quorum-certified tally is over **demo identities** (each seat's
  electorate key is `blake3(name)`); a production deployment binds each seat to a real **custody
  key** and a signed ballot. The quorum mechanism is real; the custody-key binding is the remaining
  production step.
- None of this is audited production cryptography. It's a high-assurance reference stack where each
  guarantee names its own floor.

**The through-line:** each rung is independent and each names what it rests on. "Verifiable" here
means *this specific ladder*, checkable by a stranger — not a marketing word.
