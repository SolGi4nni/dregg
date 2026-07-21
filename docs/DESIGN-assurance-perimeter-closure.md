# DESIGN — Closing the Witness-Generation Assurance Perimeter

> Beachhead → excellence. The honest goal: **every consensus-visible value is either constrained by a
> proven-COMPLETE AIR (`air_accepts ⟺ spec`) or is a single Lean implementation Rust calls into. The
> receipt carries a real proof, not a trusted key. Nothing trusted, nothing duplicated.**

Companion to memory `project-witness-gen-assurance-perimeter` (the inventory) and orthogonal to
`project-fri-soundness-reality` (the FRI floor — every proof here rests on that undischarged
floor regardless; see `FriDeployedHeightPairing` for the deployed posture).

## 0. The finding that opened this

A STARK proves the *trace* satisfies the AIR — NOT that the witness *generator* computed the right value,
NOR that the AIR *fully* constrains the intended computation. Audit verdict: under the strict bar
`air_accepts ⟺ spec`, **the proven set is EMPTY** — every refinement is one-directional / injective /
byte-identity. The consensus ROOTS (ledger, state-commit, receipt) are trusted-Rust; the EffectVM DELTAS
are one-way constrained.

## 1. The crux is SETTLED: the `⟺` technique already exists

`NonRevocationRefineComplete.lean` is a working, reusable two-directional schema:
1. author the semantic relation;
2. prove `SAT ⟹ SEM` against *named* canonicality + crypto carriers;
3. construct a parametric satisfying trace from the semantic data;
4. **construct AND prove sound** the chip/range carriers (do not assume them);
5. compose the round-trip + discharge one concrete instance.

**So the proof campaign is REPLICATION of a proven pattern, not research.**

## 2. The perimeter splits — and the split IS the plan (two parallel, non-contending swarms)

| Class | Values | Work | Why |
|---|---|---|---|
| **ARCHITECTURE (~⅓)** — the load-bearing SECURITY gap | cap-root (#4), heap-root (#5) | **Lean circuit-authoring** | The advance is a *prepend digest* `hash[leaf,old]`, NOT the sorted-Poseidon2 tree update the value model commits. A hostile prover picks a fake digest instead of performing the real `attenuate`/`Heap.set`. `SAT⟹SEM` at true resolution is **FALSE** → no proof closes it; needs *emitted constraints* (the Phase-E splice). Heap has a head start (`heapWriteSpliceVmDescriptor` + the `MapOp` open); cap is greenfield. |
| **TECHNIQUE / STRUCTURAL (~⅔)** | non-rev (#8, ~done), garbled-eval, note-spend (#6), transfer-commit (#2 object B) | **Proof** — replicate the schema | AIRs fully constrain; only the reverse direction / a decode is missing. note-spend rides the same spine-faithfulness lemma as non-rev. |

A recursive proof (Strategy B) does NOT fix an underconstrained inner AIR — **B is compression, not
completeness; B depends on A.** Do not conflate them.

## 3. The beachhead — two exemplars of the ONE technique

- **Non-revocation (`NonRevocationRefine{,Complete}`)** — the `⟺` is *essentially proven today*
  (soundness with `FieldCanonicalDiffs` discharged by real added lookups; completeness constructed over
  the whole bracketed family with carriers *built and proven*). **Polish it** (fold the shared
  crypto-carrier trust + spine decode into one lemma) → the clean **template**.
- **Transfer commitment (`transferDescriptor_commit_iff`)** — the *highest-leverage* value (the state
  commitment, #2). The `→` legs EXIST (`transferDescriptor_full_sound` forces the commit to be the genuine
  `H4(...)` absorption of the after-state; `commit_binds_state` gives injectivity). **Add the `←`
  completeness leg** (model on non-rev) → `air_accepts ⟺ the-commitment-correctly-commits-the-state` on a
  real consensus object. THE flagship theorem.

## 4. Strategy B (recursion) and the receipt (#3)

- **Near-term #3 fix (cheap, no recursion):** make the `TurnExecuted` resolver accept *verification of the
  already-produced non-recursive EffectVM STARK* as an alternative to the ed25519 trusted-key signature.
  Retires the trusted signer today. (`conditional.rs:~500`.)
- **Do NOT flip `recursive_compress = true` as-is** — the inner `EffectVmShapeAir` is a strict subset of the
  deployed `EffectVmAir`; it would make receipts "proven" against a statement WEAKER than the STARK we ship.
- **B (recursive-default) is the apex, gated on A** — grow the inner AIR to the real `EffectVmAir`, force
  `NEW_COMMIT` in-circuit (#2), complete the inner AIRs (A) — THEN recurse. Still rests on the FRI floor.

## 5. THIS IS GREENFIELD — build the right thing, delete the debt (no cutover theater)

Nothing is deployed: no live consensus, no persisted ledgers, no users whose state forks. So there is **no
migration, no flag day, no byte-identical bar, no compat constraint** anywhere in this campaign. Do not
perform production-gravity on pre-production work. Concretely:

- **State-commit:** the Poseidon2 `wire_commit` (`rotation_witness.rs:335`) just **becomes** the commitment
  (make `execute.rs:640` chain it, prove it complete); the BLAKE3 `ledger.root()` is **deleted** (or kept
  only as a non-consensus local convenience). No "cutover."
- **Note-tree:** the Lean accumulator **is** the accumulator; `poseidon2_tree.rs`'s hand-rolled math and the
  byte-differential are **deleted**. There is no "existing tree" to stay byte-identical to.
- **cap/heap:** the Phase-E sorted-tree splice descriptor **is** the descriptor; the prepend-digest form is
  **deleted**, not kept "deployed."

The only real constraint is correctness (the `⟺` proofs) and internal consistency of the tree at any instant
— never backward-compat with a deployment that does not exist.

## 6. Multi-swarm cycle plan

- **Cycle 1 (parallel, non-contending):**
  - *Proof:* polish non-rev `⟺` into the template → add the transfer `←` completeness leg.
  - *Circuit:* author the cap Phase-E sorted-tree splice (Lean) / finish heap's `heapWriteSpliceVmDescriptor`.
  - *Cheap Rust:* `TurnExecuted` accepts EffectVM-STARK-verify as an alternative to trusted-key (#3, no recursion).
- **Cycle 2:** replicate the `⟺` schema to garbled-eval + note-spend; land `cells_root` Phase-E; deploy the
  authored-but-undeployed forced cap/heap descriptors.
- **Cycle 3:** generalize transfer `⟺` to all effect tags; make `wire_commit` the chained commitment in
  `execute.rs` and delete the BLAKE3 `ledger.root()`; discharge `hcanon` field-faithfulness.
- **Apex (post-A):** recursive-proof-default (#3 → real recursion), then attack the FRI floor
  (`FriLdtExtractV3`, an adversary object) — a separate campaign.

## 7. The honest caveat, kept in front

Everything here is `air_accepts ⟺ spec` — **soundness of the constraint relation**, still on the deployed
FRI floor (`FriLdtExtractV3` assumed, no adversary object; see `FriDeployedHeightPairing` for the posture). Closing this perimeter makes the
witness-generation axis honest; it does NOT discharge the FRI floor. Both axes are named; do not let one
launder the other.
