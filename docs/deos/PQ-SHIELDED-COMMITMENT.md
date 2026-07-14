# PQ Shielded Value-Commitment — Diagnosis + the Post-Quantum Path

**Status:** posture-alignment correction. The shielded pool's *privacy* (reveal-nothing) is already
quantum-safe; its *value-binding* (no-mint / conservation soundness) is classical discrete-log and is
therefore **NOT** post-quantum — a real hole in dregg's PQ posture. This note diagnoses it precisely,
states the exact quantum attack, and scopes the right PQ fix (hash-commitment + fully-in-AIR STARK
conservation — Option A), which *aligns with dregg's existing PQ floors and retires all DLog*. It also
marks why the previously-named "full Ristretto EC-in-AIR" roadmap item is the **wrong** PQ direction.

---

## 1. The diagnosis (cited)

### 1.1 The shielded value-binding rests on discrete-log

The note value-commitment is a two/three-generator **Pedersen commitment over Ristretto**:

- `cell-crypto/src/value_commitment.rs:1` — *"Homomorphic value commitments (Pedersen commitments over
  Ristretto)."* Built on `curve25519-dalek` (`RistrettoPoint`, `Scalar` — lines 68–70), with generators
  `V`, `H_asset`, `R` derived by hash-to-curve.
- `commit_hidden_asset(value, asset_type, blinding) = value·V + asset_type·H_asset + blinding·R`
  (`value_commitment.rs:222`, doc at `:180–196`). Its binding is stated outright as classical:
  *"under the discrete-log / DDH assumption on Ristretto"* (`:186`), *"because `V`, `H_asset`, `R` have
  unknown pairwise discrete-log relations, the committer cannot open it to a different
  `(value', asset_type')`"* (`:193–196`).
- **Conservation excess = a Schnorr proof.** `prove_asset_conservation` certifies the excess of
  `Σ C_in − Σ C_out` is purely `r_excess·R` — i.e. Σ value and Σ asset-tag both cancel
  (`value_commitment.rs:199–205`; `pool.rs:32–41`). A Schnorr proof of knowledge of a discrete log is
  **DLog**.
- **Range = a Bulletproof.** Each output leg carries a serialized `bulletproofs::RangeProof`
  (`cell-crypto/Cargo.toml:14` `bulletproofs = "5"`; `pool.rs:135–148` `output_range_proofs`). Bulletproofs
  are inner-product arguments over the **same Ristretto group** — DLog.
- **The Lean floor names it honestly.** `metatheory/Dregg2/Shielded/RealCrypto.lean:74` — the step from
  the commitment equation to the value equation *"is the `CryptoPrimitives.binding` (DLog) carrier"*; the
  module header (`:36–42`) states *"a Pedersen commitment's binding IS discrete-log."*

So the entire value-conservation soundness of the shielded pool — the property that no batch can print
money — rests on **discrete-log** (Pedersen binding + Schnorr excess + Bulletproof range), on Ristretto.

### 1.2 DLog is Shor-broken — the value-binding is NOT post-quantum

Shor's algorithm solves discrete-log on any elliptic-curve group (Ristretto/Curve25519 included) in
polynomial time on a cryptographically-relevant quantum computer. Pedersen **binding** is *exactly* a
discrete-log assumption: an opener who knows the discrete-log relation between the generators can open a
commitment to any value it likes. So a quantum adversary defeats binding.

This directly contradicts dregg's stated PQ posture (ML-DSA hybrid signing, quantum-safe finality, the
PQ metatheory — memory `project-pq-metatheory-connected`). **Crucially, the PQ metatheory does NOT cover
this.** Its floor is `MSIS · MLWESearchHard · SchnorrDLHard · HashCR`, where `SchnorrDLHard` models only
the *classical leg of the hybrid signature* (ed25519), paired with ML-DSA (MSIS) through the
hybrid-combiner keystone ("secure ⟺ EITHER component"). Signing survives Shor because MSIS is the lattice
fallback. **The shielded Pedersen binding has no such fallback** — it rests on DLog *alone*, with no
lattice companion. It is outside the PQ metatheory's scope entirely.

### 1.3 The exact quantum attack

1. A quantum adversary runs Shor on the Ristretto generators `V`, `H_asset`, `R` and recovers the
   discrete-log relations `V = a·R`, `H_asset = b·R` for known scalars `a, b` (the generators are public,
   hash-derived).
2. Given any honest output commitment `C = v·V + at·H_asset + r·R`, the adversary can now re-open it to a
   *different* value `v' > v`: pick `r'` with `v'·V + at·H_asset + r'·R = C`, i.e.
   `r' = r + (v − v')·a` (solvable because it knows `a`). The commitment is no longer binding on `v`.
3. It forges a **conservation-satisfying** batch whose outputs claim more value than the inputs: the
   Schnorr excess proof still verifies (it only certifies the excess is a multiple of `R`, which the
   adversary controls), and it forges a Bulletproof range proof for the wrapped value (Bulletproofs are
   only computationally sound — quantum-broken on the same group).
4. Result: **hidden inflation.** The adversary mints $DREGG / any shielded asset out of nothing, and the
   privacy guarantees keep the theft invisible. Conservation — the no-mint invariant — is broken.

### 1.4 What is already quantum-safe (privacy survives)

The **reveal-nothing / hiding** half is fine and needs no change:

- **Pedersen hiding is perfect (information-theoretic).** For a uniformly random blinding `r`, the
  commitment is a uniform group element regardless of the value — no amount of computation (quantum or
  not) extracts the value. Perfect hiding is unconditional, hence quantum-safe. (This is *why* only
  binding, never hiding, rests on DLog.)
- **The STARK privacy path is statistical-ZK.** The shielded-spend proof runs through `HidingFriPcs`
  (`ZK = true`); value/owner/key/path/randomness live only in the witness. Statistical ZK is quantum-safe
  (memory `project-linking-tower-forgery-closure`, `project-pq-metatheory-connected`).

So **privacy is quantum-safe; only value-binding is quantum-broken.** The hole is precisely
value-conservation soundness (no-mint), not confidentiality.

---

## 2. The PQ fix

### Option A (RECOMMENDED) — Poseidon2 hash-commitment + fully-in-AIR STARK conservation

Retire Pedersen/Ristretto/Schnorr/Bulletproofs entirely. The whole shielded value side rests on
**hashes + STARK** — dregg's existing PQ floors (`HashCR` / Poseidon2 CR, `Poseidon2ChipArithSound`,
`HidingFriPcs` statistical-ZK), the *same* primitives already carrying Merkle membership and nullifiers.

**Binding** = collision-resistance of the note value-commitment hash (the same `HashCR` the Merkle tree
and nullifier stand on). CR is a quantum-safe assumption (Grover only halves the security parameter — a
256-bit Poseidon2 output gives ~128-bit quantum CR).

**Conservation** `Σ value_in − Σ value_out = 0` proven **fully in-AIR**: the value is a STARK witness, the
conservation a field constraint, no-wrap enforced by the in-AIR range gadget. STARK soundness (HashCR /
Poseidon2ChipArithSound = hash-based) is quantum-safe.

**Hiding** = the STARK statistical-ZK (`HidingFriPcs`) — already quantum-safe.

**This is largely already BUILT.** The infrastructure exists in the current codebase:

- **The hash value-commitment already exists.** The shielded-spend circuit publishes
  `value_binding = hash_fact(value, [randomness, 0, 0])` — a **hiding Poseidon2 commitment to exactly the
  value, blinded by the note randomness** (C7, `shielded/spend_circuit.rs:39–40, 111–125, 143`; PI
  `[nullifier, merkle_root, value_binding]`). This is *already* the Option-A note-value commitment:
  binding = Poseidon2 CR, hiding = the randomness blinder. It is recomputed in-AIR and pinned to a PI.
- **In-AIR conservation already exists** as a BabyBear field gate `Σ value_in − Σ value_out = 0`
  (`shielded_ring_clearing_air.rs`, clause (c)).
- **The in-AIR range gadget already exists.** Every conservation value is bit-decomposed into `VALUE_BITS`
  boolean columns with a compile-time `RING_LEGS · 2^VALUE_BITS ≤ p` no-wrap assertion
  (`shielded_ring_clearing_air.rs::VALUE_BITS`), proven in Lean to upgrade the field gate to *integer*
  conservation (`RealCrypto.lean::twoLeg_noWrap_conservation`, `inAir_conservation_refines_pedersen`). The
  header itself says this *"moves the shielded pool's per-output Bulletproof range proof from ATTESTED
  off-AIR to a CIRCUIT constraint."* That is the Option-A range gadget, already landed for the
  BabyBear-scale range.

So the AIR *already* proves value conservation over hash-committed, in-AIR-ranged STARK witnesses. What is
still DLog is the **redundant off-AIR Pedersen aggregate** (`pedTwoGen` coordinate excess + the off-AIR
Schnorr + the off-AIR Bulletproof + the Ristretto `commit_hidden_asset` bytes). Option A is the
decision to **make the in-AIR hash+STARK path the sole value-binding and delete the DLog aggregate** — not
a from-scratch build.

**Does in-AIR conservation fully replace the homomorphic Pedersen?** Yes, for the no-mint property. The
Pedersen homomorphism was only ever a device to check `Σ C_in = Σ C_out` *without opening the values*. The
in-AIR field constraint does the same check *on the witnessed values directly, under the hiding PCS* — the
values never leave the witness, so nothing is revealed, and the STARK soundness (not DLog) is what makes
the constraint binding. The homomorphic-group elegance is replaced by a field addition the STARK proves.
The one thing Pedersen's homomorphism gave "for free" — aggregating across *independently-produced*
commitments without a shared proof — is subsumed once all legs are inside one clearing AIR (which they
already are: the ring-clearing apex folds all legs into one proof).

**Remaining migration work (Option A):**

1. **Note commitment: Poseidon2, not Ristretto.** Make the note's on-chain value-commitment the Poseidon2
   `value_binding` (already the PI) rather than the 32-byte compressed Ristretto `commitment_bytes`
   (`pool.rs::HiddenAssetLeg`, `value_commitment.rs::commit_hidden_asset`). Extend the hash preimage to
   also commit the `asset_type` (a second hashed field) to keep the multi-asset hiding — e.g.
   `hash_fact(value, [asset_type, randomness, 0])` — so one hash binds `(value, asset_type)` jointly, as
   the Ristretto three-generator commitment did. *Scale: S–M.*
2. **Conservation: fully in-AIR, not off-AIR Schnorr excess.** Delete `prove_asset_conservation` /
   `verify_asset_conservation` (the Schnorr DLog excess). The conservation `Σ value_in = Σ value_out` (and
   the per-asset routing) is already the in-AIR field gate (c); the asset-tag conservation folds in as a
   second in-AIR field sum over the witnessed `asset_type` cells (replacing the `H_asset`-component check).
   The split/merge asset-equality (the Chaum-Pedersen equal-DLog `AssetEqualityProof`) becomes an in-AIR
   equality constraint over the witnessed asset cells. *Scale: M — the gadgets exist; this is wiring the
   asset coordinate into the same in-AIR conservation the value coordinate already uses.*
3. **Range: in-AIR, not Bulletproof.** Delete `output_range_proofs` (`bulletproofs`). The in-AIR
   `VALUE_BITS` gadget already covers the BabyBear-scale range; extend it to the full 64-bit amount via a
   multi-limb (Bignum) in-AIR range (`Dregg2.Bignum.legs_noWrap_conservation` is already the N-leg /
   multi-limb keystone). *Scale: M–L (the 64-bit widening is the only real depth).*
4. **Drop the DLog crates from the shielded path.** Once 1–3 land, `curve25519-dalek`, `bulletproofs`, and
   the Schnorr excess leave the shielded value-commitment TCB. (`ed25519-dalek` stays only where it is the
   *classical leg of the hybrid signature* — that IS covered by the PQ metatheory's hybrid combiner; the
   shielded binding is the surface with no lattice fallback, so it is the one to retire.)

**Net:** Option A retires *all* DLog from shielded value-binding and lands it on the exact floors
(`HashCR`, `Poseidon2ChipArithSound`, `HidingFriPcs` statistical-ZK) the rest of dregg's PQ posture
already stands on. Most of it is already built; the migration is a cutover + a 64-bit range widening, not
new cryptography.

### Option B (FALLBACK) — lattice homomorphic commitment (Module-SIS binding)

Keep the homomorphic-Σ elegance with a PQ commitment: a lattice commitment `Com(v; r) = A·r + v·g mod q`
whose binding reduces to **Module-SIS** (the *same* `MSIS` floor the PQ metatheory already carries for
ML-DSA). It is additively homomorphic (`Com(v₁;r₁) + Com(v₂;r₂) = Com(v₁+v₂; r₁+r₂)`), so the off-AIR
`Σ C_in = Σ C_out` conservation structure survives — a smaller diff to the current homomorphic design.

**Cost vs. A:**
- Commitments and blindings are lattice vectors — kilobytes, not 32 bytes; heavier on-chain footprint.
- The range proof and excess proof must become **lattice** arguments (short-vector / bulletproof-over-Rq
  style), which are larger and less mature than the in-AIR STARK path.
- If bound *inside* the AIR, it puts lattice arithmetic in-circuit (modular vectors) — heavier than the
  Poseidon2 hashes the AIR already computes natively; if kept *off-AIR*, it re-introduces a second
  cryptographic system beside the STARK.

**Verdict: A dominates.** Option A reuses machinery the tree already carries (Poseidon2, in-AIR
conservation, the range gadget, the hiding PCS), retires *all* DLog, and adds no new cryptographic system.
Option B keeps homomorphic elegance but pays kilobyte commitments + a second (lattice) proof system for it.
Recommend A; hold B as the fallback if a use-case genuinely needs to aggregate independently-produced
commitments *outside* a single clearing AIR (the one thing the homomorphism buys that in-AIR conservation
does not).

---

## 3. The wrong direction (corrected)

The prior `SHIELDED-DREX-ASSURANCE-ROADMAP.md` component 2 named **"full Ristretto EC-point excess
in-circuit"** — realizing `Σ(v·G + r·H) = 0` over Ristretto with foreign-field EC arithmetic (point
add/double, scalar mul) in-AIR — as a NEEDED (RESEARCH) item.

For the PQ posture this is the **wrong direction**: it is heavy, deep work whose *entire purpose* is to
make the DLog Pedersen commitment more faithfully realized in-circuit — i.e. it **entrenches** the
Shor-broken discrete-log binding rather than retiring it. Building it would spend a RESEARCH-difficulty
effort deepening the exact dependency that is post-quantum-broken. It should be **deleted from the
roadmap**, not built. The PQ-correct target for the *same slot* is Option A: the Poseidon2 hash-commitment
+ the fully-in-AIR STARK conservation (which is already partly built and retires DLog).

---

## 4. Honest grade

| Property | Rests on | Quantum-safe? | Grade |
|---|---|---|---|
| Shielded **privacy** (reveal-nothing) | Pedersen *perfect hiding* (info-theoretic) + `HidingFriPcs` statistical-ZK | **YES** | Already PQ. No change needed. |
| Shielded **value-binding / no-mint** (today) | Pedersen/Ristretto binding + Schnorr excess + Bulletproof range = **DLog** | **NO — Shor-broken** | Real residual. Contradicts the PQ posture; NOT covered by the PQ metatheory (which has no lattice fallback for this surface). |
| Shielded value-binding (after **Option A**) | Poseidon2 CR (`HashCR`) + in-AIR STARK conservation (`Poseidon2ChipArithSound`) + in-AIR range | **YES** | The target. On dregg's existing PQ floors; DLog fully retired. |

**One line:** the shielded pool's *privacy* is quantum-safe today; its *value-conservation soundness* is
classical discrete-log and quantum-broken — a genuine hole in the PQ posture. The right fix is the
Poseidon2 hash-commitment + fully-in-AIR STARK conservation (Option A), most of which is already built
(`value_binding`, the in-AIR conservation gate, the `VALUE_BITS` range gadget); the migration is a cutover
that deletes the Pedersen/Schnorr/Bulletproof DLog path + a 64-bit in-AIR range widening — **not** the
Ristretto-EC-in-AIR that entrenches DLog.
