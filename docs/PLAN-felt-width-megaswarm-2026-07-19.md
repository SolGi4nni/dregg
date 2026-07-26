# PLAN — the felt-width Lean-port megaswarm

**2026-07-19.** Synthesis of the four terrain probes (see
`WOUND-felt-width-boundaries-2026-07-19.md`). Groups the repair into swarm lanes **by move-type**, so
each lane prompt carries the real Lean substrate + golden path + the anti-masquerade canary, not prose.
Not yet launched — this is the pre-swarm spec.

## The reusable proven primitive (every wide-hash lane calls into this)

`metatheory/Market/WideCommitBoundary.lean` — `wireCommitR8`, `Poseidon2Width8`,
`Poseidon2WideCR`, `wireCommitR8_binds` (8-felt commitment binding, proven). Rust side:
`hash_many_8` (`circuit/src/poseidon2.rs:409`), `single_perm_compress` (:454), `digest8_to_bytes32`
(`cell/src/commitment.rs:681`). **No wide hash gets hand-authored** — reuse these.

## The universal anti-masquerade rule (bake into every canary)

Probe 3 caught the trap: arity-4 trees already witness all 8 lanes of each node, so you *can* expose
8 root PIs with a PI-only edit — and it buys **nothing**, because the tree still chains lane-0 interior.
Probe 4 caught the twin: widening only the final squeeze while the fold `acc` stays 1-felt is a laundered
widening. **Every widening lane's acceptance test is an INTERIOR-collision forge** (two inputs colliding
on lane-0 that the wide scheme now REJECTS), never a root-format/width check. Widen the *fold*, not the
*projection*.

---

## Lane group ① — WIDEN LEAN DESCRIPTORS (already Lean-emitted; re-author the node fold → 8 lanes)

Parallel-safe (disjoint Emit files + goldens). Each: edit the node fold in the `*Emit.lean`, re-emit
the byte-pinned golden, update the Rust witness builder + PI-comparison consumer, add the interior-forge
canary.

- **①a #5 membership** — `metatheory/Dregg2/Circuit/Emit/MerkleMembership4aryEmit.lean` →
  `circuit/descriptors/by-name/merkle-membership-4ary-general.json`. Rust: `membership_verifier.rs`
  (`root_felt_from_slot` reads 8 felts; verify `&[leaf, root0..7]`), `authorized_set_root_bytes`.
  **MED-HIGH.** Contained consumer — the clean lane-① exemplar.
- **①b #6 federation** — `BoundPresentationEmit.lean` + `BlindedMembershipEmit.lean` → 2 goldens.
  ⚠ Widening `FEDERATION_ROOT` 1→8 **shifts the whole PI layout** (`REQUEST_PREDICATE_BASE`,
  `REVEALED_FACTS_BASE`, `PI_NONCE` all move); every downstream index in `sdk/src/verify.rs` +
  selective-disclosure shifts. **HIGH.**
- **①c #7 revocation** — two options: (a) re-author `NonRevocationAdjacencyEmit.lean` node fold; or
  **(b, preferred) retire `DslRevocationTree` and open freshness against the existing
  `CanonicalHeapTree8`** the main trace already commits 8-felt (`before_root8`/`after_root8` *are* the
  root). (b) deletes a duplicate scheme. **MED-HIGH (a) / HIGH (b).**

## Lane group ② — PORT HAND-RUST-AIR → LEAN + DELETE debt

- **②a #8 CI attestation** — NO Lean emitter exists (the Lean path is pointedly bypassed). Author
  `CiAttestationEmit.lean` (small: the `exit==0` gate + 25 PI bindings), emit a golden, route
  `dregg-doc/src/ci_assurance.rs` to parse it, **delete** the hand `ci_attestation_program` +
  `ci_attestation_descriptor2`. **MED, self-contained, greenfield Lean.** ← the clean lane-② exemplar,
  and it's the descriptor behind the #6 fix already landed.
- **②b delete dead debt** — `NoteSpendingAir` (`#[deprecated]`, zero constraints,
  `circuit/src/note_spending_witness.rs:754`) and `generate_blinded_merkle_poseidon2_trace`
  (`poseidon2_air.rs:647`, deployed debt behind the Lean #6 replacement). Confirm no live consumer, delete.
- **②c #2-production note-spend** — `note_spending_circuit_descriptor` (Rust-DSL BUILT descriptor) →
  Lean-emitted. Entangled with ③c (the commitment it binds). **MED-HIGH.**

## Lane group ③ — WIDEN COMMITMENT HASHES → Digest8 (glue; reuse `WideCommitBoundary`)

- **③a #12 interface_id** — no model exists; author a Lean 8-felt sorted fold over method leaves
  (end-to-end 8-felt `acc`, per the anti-laundering rule), reuse `Poseidon2Width8`. Rust:
  `compute_interface_id` → 8-lane fold, `felt_to_bytes32` → `digest8_to_bytes32`. Field width + consumer
  signatures unchanged (already `[u8;32]`); only entropy goes 31→~248 bits. **MED.** Contained.
- **③b #1 cap_root** — `_wide`/`_8` already exist and the state commitment binds them. Retire the narrow
  lane-0 `compute_canonical_capability_root` where the executor recompute-and-compare can move to `_wide`
  in lockstep (the E-batch item #3). **LOW-MED** (lockstep across declared-root writers).
- **③c #2/#4 note+nullifier value + key** — THE DEEP LANE. Digest8 commitment/nullifier output (reuse
  `hash_many_8`) is the easy half; the hard half is the **Digest8-keyed sorted order + new bracketing
  math** for the accumulator (`Crypto/NonMembership.lean` lemmas assume single-felt keys — do NOT
  transfer). **HIGH.** ⛔ The kernel flip that carries the roots in `RecordKernelState` is
  **ember-gated and frozen** (`NullifierAccumulator.lean:12-23`) — FENCED, not a swarm lane.

## Deeper seams (bigger than felt-width; a design decision, not a mechanical lane)

Surfaced by probe 4 — findings #15/#16/#17 in the wound doc. The shielded pool (#10) needs, beyond
widening: (1) pin `merkle_root` to the committed accumulator; (2) fold the value-link into the AIR so
conservation is proved not attested; (3) resolve the PQ-commitment disagreement. **These want an
ember decision before any lane touches shielded** — it is a subsystem redesign, not a widening.

## NOT swarm work

- **#1 finality cert (E1)** — pure Rust, the wide root is in hand; do it directly (spec in
  `DESIGN-felt-width-rotation-epoch-2026-07-19.md`). Not a swarm lane.
- **The ember-gated kernel flip** (③c tail) — FENCED.
- **The shielded subsystem** — needs the design decision above first.

## Sequencing recommendation

1. **Wave 0 (now, no swarm):** land #1 (E1 finality cert, pure Rust).
2. **Wave 1 — two exemplars, one per move-type:** ①a membership (widen-Lean-descriptor) + ②a CI
   attestation (port-hand-Rust-AIR). Small, self-contained, validate both patterns + the interior-forge
   canary before fanning.
3. **Wave 2 — fan the contained lanes:** ①b federation, ①c revocation(b), ③a interface_id, ②b debt
   deletion, ③b cap_root lockstep. Parallel, disjoint files.
4. **Wave 3 — the deep + gated:** ②c/③c note-spend + note/nullifier Digest8 (author the new keyed
   scheme), with the kernel flip fenced; shielded only after the seam decision.

Every lane prompt pastes: the exact `*Emit.lean` path + golden path + the real struct/field signatures
+ the interior-collision canary + "widen the fold, not the projection" + the AIR-in-Lean tripwire.
