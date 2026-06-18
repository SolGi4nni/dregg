# Light-Client Trust Surface — the definition of done for "a light client can actually trust dregg"

> Goal (ember): keep working until a client running ONLY `verifyBatch` + the published public inputs —
> with NO ledger, NO executor, NO producer trust — can conclude the published `(pre,post)` is a
> **genuine, authorized, non-replayed, conservation-respecting** kernel transition.

## The reframe (the finding that subsumes the rest)
The deployed sovereign verifier `verify_and_commit_proof_rotated` (`turn/src/executor/proof_verify.rs:77`)
is **not a light client — it is a producer-replay verifier.** It fetches the trusted before-cell from the
ledger, reconstructs the circuit pre-state, *re-runs trace generation*, and **overrides the commitment PIs
from trusted storage** (`dpis[34]`←stored old, `dpis[35]`←claimed new, `dpis[38]`←recomputed off-circuit
from the trusted post-cell). Only then does it call the genuine `verify_batch`. So the *system* is sound
because the verifier re-executes against a trusted ledger — NOT because the proof forces it. A true light
client gets only what the circuit's `pi_binding` constraints force (the in-trace `state_commit` continuity
col-261 == published NEW_COMMIT + per-row balance/nonce arithmetic). The Lean apex
`lightclient_unfoolable_circuit_sound*` is internally honest + axiom-clean ({propext, Classical.choice,
Quot.sound}, no sorry/axiom) — but its `S_live`/`recStateCommit` is a RICHER commitment (whole-kernel
`RestHashIffFrame`) than the deployed circuit realizes. **The smuggles are all in the circuit↔deployment
realization seam.**

## The 6 genuine smuggles (verdict: a light client CANNOT trust dregg today)
1. **record_digest realization gap (MOST DANGEROUS).** The deployed commitment absorbs `record_digest` as a
   FREE prover-witnessed aux column (`circuit/.../air.rs:1704`); the circuit never recomputes it from the
   authority fields and never constrains before→after. Correct only because the verifier re-derives it from
   the trusted ledger post-cell (`proof_verify.rs:284-300`). Light client: a prover can publish a NEW_COMMIT
   binding ARBITRARY permissions/VK/lifecycle/deathCert/side-table roots the effect never produced — the
   authority-bearing half of the kernel is unforced. This is the literal "we do NOT have a proven-secure circuit."
2. **whole-turn composition is lead-only.** The verifier resolves ONE descriptor by `effects.first()` and proves
   ONE proof (`proof_verify.rs:154-165`, `trace_rotated.rs:279/324/337/351`). A tail effect (`[Transfer(lead),
   SetPermissions(tail)]`) rides into the committed post with NO forcing gate. The Lean forest apex
   (`ClosureForest.lean:144`) requires per-step `Satisfied2` for EVERY effect — strictly stronger than deployed.
3. **No agent/turn-header authentication on the proof path.** The proof-carrying path performs NO signature check
   (`execute.rs:466-478`); `native_signature_air` is unused (not in the rotated cohort). A light client cannot
   conclude "the rightful agent authorized THIS turn." (Distinct from the owner/cap authority disjunct — see #225.)
4. ~~**Replay: only the RELATIVE nonce is forced.**~~ **RESOLVED (2026-06-18, by analysis — NOT an in-circuit
   hole for a chain-following light client).** The nonce is folded into the per-cell commitment
   (`cell_state.rs::compute_commitment` `hash_4_to_1([bal_lo, bal_hi, nonce, fields[0]])` — VERIFIED) AND forced
   `nonce_after = nonce_before+1` in-circuit (`EffectVmEmitTransfer.gNonce`: `new_nonce − old_nonce − (1−s_noop)
   = 0`, in `transferRowGates`, with `gNonce`'s rejection tooth — VERIFIED). So a cell's commitment sequence is
   STRICTLY MONOTONIC in nonce → **no commitment ever repeats**, and the proof's `OLD_COMMIT` (PI 34) is forced
   (the first-row `pi_binding`). A light client that follows the commit chain (tracks the head = latest
   `NEW_COMMIT`, which it MUST to have a current state) accepts a turn iff its `OLD_COMMIT == head`; a stale /
   replayed proof carries an old `OLD_COMMIT ≠ head` → rejected, and the monotone nonce guarantees no later head
   ever equals it. The "absolute freshness anchor" IS the nonce-in-commit the light client already follows; the
   verifier's `proof_verify.rs` reconstruction is a full-node convenience, not the light client's basis. The
   genuine residual is a DIFFERENT property — chain-FORK resistance (the light client following the RIGHT chain)
   — which is the consensus/blocklace layer's job, not the per-proof circuit. Not a per-proof replay hole.
5. **Fee debit is out-of-proof.** Debited by the executor "PHASE 1, never rolled back" (`execute.rs:421`); the
   verifier reconstructs the pre-fee state (`proof_verify.rs:130-136`) so the proof is built against fee-removed
   state. The fee is not a constraint in the proven transition.
6. **No turn-wide cross-cell Σδ=0.** Per-cell balance arithmetic + no-underflow + NET_DELTA ARE in-circuit
   (genuine). But there is no cross-cell turn-wide conservation; a single-cell proof can't conclude no value was
   minted turn-wide (cross-cell pairing is reconstructed off-AIR).

## Floor residuals flagged (not smuggles, but named)
7. **`pi_binding` (+ `umemOp`) arms NOT in the F4 differential** (`ir2_denotation_eval_differential.rs`) — and
   `pi_binding` is the PI-35↔col-261 weld the whole forcing story rides on. The legit StarkSound floor, but this
   arm is un-differentialed (hand-transcribed `eval_enforces`). Name + differential it.
8. **`SatFloor` never constructively inhabited** (`CircuitCompletenessSatFloor.lean`) — no `: Satisfied2 := by`
   anywhere. COMPLETENESS could be vacuous if the live descriptors were unsatisfiable. Build one concrete
   inhabitant. (Does not affect soundness, which consumes `Satisfied2` as an antecedent.)
9. **`WitnessDecodes`** (`CircuitSoundness.lean:421`) — a STRONG but legit named floor (commitment-surface
   surjectivity); supplies the endpoints' existence/binding, NOT the transition. Flagged for strength, not a smuggle.

## DEFINITION OF DONE (force these in-circuit; all VK-affecting — greenfield VK rotation is expected)
- [ ] **#225 (authority):** publish the turn's `actor`/`src`/`dst` as PIs + an equality gate `pi.turn = witnessTurn`;
  weld `capOpenCols.src`/`capRoot` to the committed before-block. (Owner-authority + edge-id; turn-bound Lean layer
  landed `6b9f3c225`, PI realization pending.)
- [ ] **#1:** recompute `record_digest` in-circuit from the authority fields + a per-effect before→after transition
  gate; retire the off-circuit anchor (`proof_verify.rs:253-303`).
- [ ] **#2:** prove the whole forest, not the lead — one sub-proof/descriptor per effect (or a multi-effect
  descriptor); retire the `effects.first()`-only pins.
- [ ] **#3:** wire `native_signature_air` into the proof-carrying descriptor (agent signature over the turn-hash forced in-circuit).
- [ ] **#4:** bind an ABSOLUTE freshness anchor in-circuit (pin OLD_COMMIT to a proof-fixed receipt-chain/nonce commitment).
- [ ] **#5:** force the fee debit inside the proven transition (stop the UNDO-PHASE-1 reconstruction).
- [ ] **#6:** add a turn-wide cross-cell Σδ=0 aggregation AIR.
- [ ] **#7/#8:** differential the `pi_binding`/`umemOp` arms; construct a concrete `Satisfied2` inhabitant for `SatFloor`.

When all are forced, a client running only `verifyBatch` + the PIs concludes the genuine/authorized/non-replayed/
conserving transition with nothing trusted off-circuit. Until then: the proof is a beautiful theorem about a
commitment surface the running circuit does not yet force.
