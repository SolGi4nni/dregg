# WOUND — narrowed-digest security boundaries (the felt-width class)

**Opened 2026-07-19.** Found while chasing an unrelated FRI-soundness question ("why an 8-to-1
fold?"). The 8-to-1 fold is fine (costs `log₂7 ≈ 2.8` bits, documented). But the question surfaced
the *real* version of the worry: places where a Poseidon2/BabyBear digest (8 felts, ~124 bits) is
silently squeezed to **one felt (~31 bits, birthday-collidable at ~2^15.5)** and then used as a
**security boundary** — a commitment, a signed payload, a membership key, an authorizing equality.

The v10 / "faithful 8-felt" / `Faithful8` campaign was real and closed the sites it *targeted*
(cell state commitment, heap/fields/cap roots, umem boundary — `reference-umem-boundary-31bit` is
**closed at HEAD**). But it **widened roots, not key-spaces**, and its two defenses do not
generalize:

- `scripts/check-no-degraded-felt.sh` covers exactly **three files**
  (`cell/src/commitment.rs`, `turn/src/rotation_witness.rs`, `circuit/src/effect_vm/trace_rotated.rs`).
- The `Faithful8` type wall only bites where a value flows into a **typed octet sink**.

Every finding below lives in the **complement of both** — the class regrows there. The recurring
tell: **a doc-comment asserting collision-resistance over a value that has been squeezed to one felt.**

Provenance tags: **[V]** = verified by direct read this session · **[A]** = agent-read, not yet
independently confirmed · **[?]** = severity needs one more trace before pricing.

---

## Probe findings — deeper seams surfaced by the Lean-port recon (2026-07-19)

The four terrain probes turned up holes **bigger than felt-width**, and one correction to my own
readiness claim. Captured here so they ride the same campaign.

- **#15 Shielded `merkle_root` is wire-supplied, not pinned to the committed accumulator [A, HIGH].**
  `apply_shielded_transfer` (`turn/src/executor/apply.rs:1315-1412`) reconstructs the tree
  `from_serialized_parts(payload.merkle_root, …)` and verifies membership against **that** root — with
  NO check it equals the live committed commitment-tree root. A prover supplies a root of their choosing
  and proves membership in an attacker-built tree. Theft/inflation vector **larger than any birthday
  collision**; widening the felt does not fix it.
- **#16 Shielded value-link is honest-prover-trusted [A, HIGH].** `verify_value_link` (leaf-value ↔
  Pedersen-leg-value equality) is called **only in a test** (`circuit-prove/tests/shielded_transfer_m2a.rs`),
  never in `apply_shielded_transfer`. Conservation over `value_binding` is attested, not proved — the real
  inflation exposure, independent of the 31-bit width.
- **#17 Shielded PQ-commitment disagreement [A].** The Lean apex rests on Shor-broken Ristretto Pedersen
  (`commit_hidden_asset`, DLog) while `spend_circuit.rs:42-48` declares a "PQ cutover (Option A)" making
  the Poseidon2 `value_binding` authoritative — the two disagree on which commitment is load-bearing.
- **Consequence for #10:** the shielded pool is **not** "widen 3 felts." It is "port the Rust-authored
  `spend_circuit` AIR to Lean + pin `merkle_root` to the committed accumulator + fold the value-link
  into the AIR + resolve the PQ-commitment story." Felt-width is the entry point, not the fix. Reachable
  only in a `prover`-enabled executor (verify-only fails closed); not in the committed VK.
- **Correction to #4/#10 (note/nullifier):** I over-claimed this as "finish an existing port." The
  accumulator NODE digests are 8-felt + proven (`DeployedHeapTree`/`SortedTreeNonMembershipHeap8`), but
  the note commitment/nullifier **value and the sorted key** are still 1-felt and UNSTARTED.
  **CORRECTION (07-20 scoping):** the "new bracketing math" fear was too pessimistic — the sorted-gap
  soundness (`Crypto/NonMembership.lean`) is already `[LinearOrder Digest]`-**generic**, so instantiating
  `Digest := Lex (Fin 8 → ℤ)` gives the whole adjacency bracketing FOR FREE (the IMT/Heap8 wrappers are
  ℤ-typed but their proofs never touch ℤ arithmetic — mechanical generalization, machine-confirmable by a
  one-section spike). The genuine new work is bounded and nameable: **one lex-`<`-over-8-felts AIR gadget**
  (`eval_lex_lt` is only a doc-comment today, no def), a **leaf-schema widening** (addr/nextAddr → 8 felts,
  arity-17 leaf), and the **easy value widening** (`hash_many→hash_many_8`, `felt_to_bytes32→digest8_to_bytes32`).
  Still HIGH — but the cost is a compare gadget + a leaf widening, **not new combinatorics**. Plus the
  **ember-gated, frozen** kernel flip (`NullifierAccumulator.lean:12-23`, "do NOT fire piecemeal").
- **#12 interface_id has NO Lean model and NO wide twin** — left behind when cap_root grew its `_8`.
  Reusable wide primitive exists (`Market/WideCommitBoundary.lean` `wireCommitR8`/`Poseidon2Width8`;
  Rust `hash_many_8`/`digest8_to_bytes32`). Anti-laundering: the fold accumulator must be 8-felt
  end-to-end, not just the final squeeze. Severity MODERATE (discovery/factory-identity, not funds).

## Update log — 2026-07-19 (post-pricing, verified reads)

- **#6 CI exit_code — FIXED + VERIFIED GREEN.** `ci_verdict_public_inputs` now returns `Option`
  and REFUSES non-canonical exit codes (`exit_code_is_canonical` = `0 ≤ e < BABYBEAR_P`); prove →
  `Err`, verify → `false`. Canary `failing_exit_code_cannot_alias_into_the_pass_gate` +
  8/8 `ci_assurance::tests` pass (`--features substrate`). The trusted reconstructor is fail-closed
  by construction, so a future caller cannot reintroduce the alias.
- **#1 finality cert — CONFIRMED real, cost (a) ~2^31 offline hashes + 1 proof.** The `:686` segment
  tooth binds the aggregate to its own execution, NOT the committee's *signature* to the wide root.
  `final_root` is a host-searchable `wire_commit_8` (`joint_turn_aggregation.rs:1156`). **Fix is
  clean and NOT AIR:** the wide root already exists in the PIs; widen `finality_signing_message` +
  `FinalityCert.finalized_root` + the seam to all 8 lanes. Kind E → rotation epoch.
- **#3 cap-uniqueness — DOWNGRADE to defense-in-depth.** State commitment already binds the wide cap
  root independently (`commitment.rs:243`); the narrow gate is a redundant projection. Fix is
  actually-hard (declared-root writers widen in lockstep; slot is committed state → circuit binding),
  NOT the quick swap I first ranked.
- **#4 note/nullifier — MINT BLOCKED, availability real via shielded path.** Deployed node injects no
  `proof_verifier` ⇒ cleartext `NoteSpend` fail-closes (`apply.rs:1195`); every real verifier's base
  `verify()` is hardcoded `false`. Availability break is reachable via the *shielded-transfer* path
  (`apply.rs:1370`, self-contained `verify_stark_side`, ~31-bit keys) — ties #4↔#10. Residual: the
  Lean-authoritative producer's note-effect semantics (`exec-lean` `wire_state_to_ledger`) not fully
  traced; all evidence says no value created.
- **#8 topic mask — RECLASSIFY to low-severity design limitation.** Inherent 64-bucket `u64` lattice;
  collisions cause spurious wakes (no payload/cap leak; recipient still filters on the true hash).
  Real per-topic attenuation = a change to the Lean-authored firmament `NotifyCap` model.
- **#14 leg_is_wide — FIXED + VERIFIED GREEN.** Deleted the `#[cfg(not(feature = "prover"))] → false`
  stub; extracted the classifier to an unconditional module-level `vk_hash_is_wide(&[u8;32])` (deps —
  ungated `WIDE_REGISTRY_STAGED_TSV` const + non-optional `blake3` — confirmed available without
  `prover`). Non-prover **lib compiles**; canary `wide_leg_classifier_works_without_prover` **passes**.
  Now one unconditional code path, so the light-client verify build classifies wide legs correctly and
  binds their ~124-bit anchors instead of a slot-0 residual.

## Follow-ups opened 2026-07-19

- **Restore non-prover (light-client) test coverage → `project-ci-meaningfulness-audit`.** `cargo test
  -p dregg-sdk --no-default-features` did not compile on HEAD: ungated tests reference `prover`/
  `exec-lean`-only symbols (`descriptor_authority_class` — fixed one instance; `dregg_exec_lean` import
  — still open; likely more). So the wasm/light-client verify config's tests have not been running —
  **which is exactly where #14's bug survived.** Restore it: gate the remaining ungated tests, then
  wire `--no-default-features` into CI so the trust-minimized config is actually exercised.
- **Kind-E rotation epoch designed** → `docs/DESIGN-felt-width-rotation-epoch-2026-07-19.md` (E1 pure-
  Rust #1; E2 descriptor-PI-widening #2/#9/#11, Lean AIR).

---

## Triage — worst first

| # | Site | file:line | Cost | Kind | Prov |
|---|------|-----------|------|------|------|
| 1 | BFT finality cert — signed message is 4 bytes of lane-0 | `lightclient/src/lib.rs:281` | ~2^31 cheap + 1 proof (see note) | E | **[V]** signature narrow; compensating "segment tooth" is a launder (binds aggregate to itself, not the sig to the wide root) |
| 2 | Federation membership gate — bare 1-felt PI compare, public SDK export | `sdk/src/verify.rs:202,214` | ~2^31 | E | [A][?] |
| 3 | Executor cap-uniqueness gate — narrow root, wide twin exists 19 lines away | `turn/src/executor/execute_tree.rs:328` | ~2^15.5 | B | **[V]** breaks root-binding (1), NOT the structural dup-scan (2, `:345`) |
| 4 | Note commitment + nullifier — 1 felt each, no `_8` variant | `cell/src/note.rs:329,243` | ~46k spends | C | [A] availability **certain**; mint contingent on deployed verifier [?] |
| 5 | Accumulator leaf **keys** (nf/cm/revoked) — 31-bit addresses | `circuit/src/effect_vm/trace_rotated.rs:1377,1575,1661` | ~2^31 | D | [A] roots are `Faithful8`, membership answered by key |
| 6 | CI pass gate — `exit_code % BABYBEAR_P` aliases failure→0 | `dregg-doc/src/ci_assurance.rs:255` | **zero** | A | **[V]** `2013265921 % p = 0`, gate is `COL_EXIT==0`, bond path unguarded |
| 7 | Fiat mint gate — payment identity folded to 1 felt | `circuit/src/dsl/deco_payment.rs:107` | ~2^16 | C | [A] bridge gate live (`bridge/src/stripe_deco.rs:287`); fold arm fail-closed |
| 8 | Topic wake mask — `1u64 << (topic_hash[0] % 64)` | `starbridge-v2/src/swarm.rs:111` | **~64 evals** | ? | [A][?] load-bearing vs optimization unconfirmed |
| 9 | `SenderAuthorized` authorized-set root — 1 felt, leaf proves no path | `turn/src/executor/membership_verifier.rs:105` | ~2^31 | D/E | [A] |
| 10 | Shielded pool — `merkle_root`/`nullifier`/`value_binding` declared **`u32`** | `turn/src/action.rs:1005`; `circuit-prove/src/shielded/spend_circuit.rs:462` | direct inflation on value collision | C | [A] `Effect::ShieldedTransfer` live |
| 11 | Freshness/revocation root — 1 felt, tree depth 4 ≤14 entries | `sdk/src/full_turn_proof.rs:5248` | grind padding leaves | D/E | [A] |
| 12 | `interface_id` — 1 felt, **no wide twin anywhere**; a factory VK is derived from it | `cell/src/interface.rs:246`; `directory/src/service_factory.rs:92` | ~2^31 → colliding interfaces share a VK | C | [A] |
| 13 | sandstorm-bridge — narrow throughout; byte-identity claim now **false** | `sandstorm-bridge/.../cell.rs:87,138` | ~2^31 (hostile host) | C/drift | [A] `cell/src/state.rs:535` widened, sandstorm did not — correctness drift too |
| 14 | `leg_is_wide` cfg trap — non-prover build forces **every** leg narrow | `sdk/src/full_turn_proof.rs:5144` | verifies ~124-bit anchors at 31 bits | A | [A] wasm verifier is exactly this config; live trap, no current caller |

**Tier 2 (~62-bit, 4 felts):** `circuit-prove/src/dsl_leaf_adapter.rs:152` (`DFA_RC_LEN=4`, leaf exposes 8
on the wire — cheapest real fix), `sovereign_leaf_adapter.rs:85` (`KEY_COMMIT_LEN=4`, authorizes a
sovereign turn, six lines from `COMMIT_LEN=8`), `verifier/src/lib.rs:466` (receipt chain).

**Checked-benign (coverage, not omission):** `storage/src/bucket_commitment.rs:112`,
`starbridge-apps/site-host/src/site.rs:174` (1-felt root is one input to a `wire_commit_8` fold that
binds all limbs — no 31-bit intermediate); `circuit/src/effect_vm/trace.rs:673` anchor tags (all 8
bound via `compute_effects_hash`); `commit/src/typed.rs:565` (30 bits/limb ⇒ 240-bit). Display
strings / hash-map keys / `#[cfg(test)]` fixtures not itemized.

---

## The six repair kinds (kind decides the mechanism and who can touch it)

- **A — Logic bugs, not width. Fix now, no crypto.** #6 (range-check `exit_code`), #14 (cfg gate).
- **B — Gate swap to existing wide twin, AND retire the narrow twin** so it can't be reached again.
  #3.
- **C — No wide scheme exists; must BUILD it — and these are circuit commitments ⇒ authored in
  Lean, Rust calls in.** ⚠️ TRIPWIRE (`~/.claude/CLAUDE.md` law #1). #4, #7, #10, #12, #13. Substrate
  partly exists (`CommitmentTreeAccumulator`, `DeployedHeapTree`/`Heap8Scheme` are Lean+wide); the
  work is authoring the wide note/nullifier/interface schemes there and routing deployed narrow
  paths through them. **NEVER hand-write the wide commitment in Rust.**
- **D — 31-bit KEYS inside accumulators; widening the root did nothing.** The sorted-tree membership
  descriptor's key width — also Lean-authored AIR. #5, #9, #11.
- **E — Narrow signed / PI payloads; wire + Fiat-Shamir changes ⇒ batch into ONE rotation epoch.**
  #1, #2, #9, #11. Cheap now (nothing deployed), only gets more expensive.
- **F — Generalize the two defenses (the meta-repair; without it we play whack-a-mole).**
  (i) lint the whole tree for `felt_to_bytes32` / `.as_u32()` / `[0]` / `as u32` at security
  boundaries; (ii) extend the `Faithful8` type wall to **keys, PI vectors, signed payloads** so
  narrow-at-a-boundary becomes *un-representable*, not merely linted.

---

## Notes / open severity questions (verify before pricing)

- **#1 exact cost:** depends on whether an attacker can mint alternate valid aggregates for a chosen
  final state cheaply (own a cell, drive turns ⇒ ~2^31 cheap root computations + 1 proof) vs. must
  prove each candidate (~2^31 proofs). Signature is narrow either way ⇒ fix = widen
  `finality_signing_message`. Trace `verify_turn_chain_recursive` / `genuine_table_public_inputs`.
- **#4 mint leg:** the legacy AIR's Merkle path chains from the 1-felt commitment
  (`circuit/src/note_spending_witness.rs:538`); whether the mint is reachable depends on which
  `ProofVerifier` `turn/src/executor/apply.rs:1221` is configured with (trait object, PI buffer
  "advisory"). Availability break is unconditional regardless.
- **#2 threat model:** attacker builds their own ring and chooses siblings ⇒ controls the preimage,
  same as the action-binding 15 lines below (`sdk/src/verify.rs:218`) which correctly uses 8 felts.

## Meta-lesson (for memory)

The campaign widened **roots**, not **keys/payloads**; the lint covers **three files**; the class
lives in the **complement of both defenses**. A doc-comment asserting collision-resistance is a
*name*, not a proof — read the width, not the comment. Same discipline that surfaced the FRI floor:
check whether the deployed value equals what the proof/scheme actually binds.
