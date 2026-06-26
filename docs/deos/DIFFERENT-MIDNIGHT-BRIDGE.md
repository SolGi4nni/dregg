# A Different Midnight Bridge: native state-INCLUSION, not transition-proof

The current Midnight path (`bridge/src/midnight_verified.rs`,
`midnight_gateway.rs`) is an optimistic / watchtower bridge: Midnight checks a
federation **attestation**, and a STARK proof rides along *only as dregg-side
fraud-proof material* (`docs/deos/NATIVE-PROOF-BRIDGES.md §2`). Midnight itself
verifies nothing meaningful in-circuit — just a signature/hash.

This document designs a *different* bridge that gives Midnight something real to
check **natively, in-circuit, without ever touching FRI**: a **state-inclusion
proof**. The move is to split the two questions the current design fuses:

1. **"Is this root valid?"** — that dregg root `R` is the genuine output of a
   real kernel history. This is the FRI whole-history proof
   (`circuit-prove/src/ivc_turn_chain.rs:1286`, `WholeChainProof`), which Midnight
   **cannot** verify (Halo2+KZG/BLS12-381, no STARK/FRI backend, fixed per-entry
   VK, no recursion exposed to Compact — `docs/deos/ZKIR-V3.md:30-38`). It stays
   **off Midnight**, supplied optimistically / by checkpoint and backstopped by
   the existing watchtower.

2. **"Is this state in the root?"** — that cell `X` has committed state `Y` under
   a checkpointed root. This is *just a Merkle path*. A small circuit. The
   question is whether **Compact can express it natively** — and the answer
   turns entirely on a field/hash mismatch we resolve below.

The thesis: **the expensive, foreclosed half (the transition proof) does not
need to land on Midnight at all.** What a relying contract on Midnight actually
needs is "this cell genuinely holds this state," and that is a membership check
against a checkpointed root — the one thing Compact's standard library is *built
to do natively*.

---

## 1. The field/hash answer (the load-bearing feasibility question)

Can dregg's state root be recomputed by a native Compact Merkle verifier? **No —
not against dregg's own root.** The two hash functions live in different fields:

| | dregg state root | Compact `merkleTreePathRoot` |
|---|---|---|
| Hash | **Poseidon2**, width-16 | **Poseidon**, width-3 / rate-2 / 8 full + 60 partial rounds |
| Field | **BabyBear**, `p = 2³¹ − 2²⁷ + 1` (31-bit) | **BLS12-381 scalar field `Fq`** (Jubjub base, 255-bit, modulus `0x73eda7…00000001`) |
| Encoding | felt → bytes32 low-4-LE (`cell/src/state.rs:389`) | `MerkleTreeDigest { field: Field }` |

Grounded:

- dregg side: every committed root (`compute_fields_root`,
  `compute_heap_root`, `compute_canonical_capability_root`) is the **sorted
  Poseidon2 binary Merkle root over BabyBear** — `cell/src/state.rs:380` /
  `:409`, `cell/src/commitment.rs:554`, `circuit/src/heap_root.rs`. The felt is
  serialized to bytes32 as its low 4 little-endian bytes (`state.rs:389`).
- Midnight side: `merkleTreePathRoot<#n, T>` and `transientHash` are Poseidon
  over `midnight_curves::Fq` (the BLS12-381 scalar field), width-3, rate-2, 8
  full + 60 partial rounds (`~/midnight/midnight-zk/circuits/src/hash/poseidon/constants/mod.rs:17-26`,
  `circuit_field.rs:248`, `midnight-ledger/transient-crypto/src/hash.rs::transient_hash`).
  `MerkleTreePath<#n, T>` + `MerkleTreeDigest { field }` are first-class stdlib
  ADTs (`~/midnight/midnight-docs/docs/compact/standard-library/exports.md:49,73,338,349`).

So Compact's native Merkle gadget computes a **Poseidon-over-BLS** root. To make
it recompute dregg's **Poseidon2-over-BabyBear** root you would have to *emulate
BabyBear-Poseidon2 inside BLS12-381 constraints* — non-native 31-bit field
arithmetic, range-checked, dozens of emulated BabyBear mults per permutation,
across every path node. That is the same class of obstruction as the FRI
verifier, only smaller, and there is **no tooling** for it. **Verifying dregg's
native root natively in Compact is NOT cheaply expressible.** Be honest about
this: option (1) "native Poseidon2-Merkle-in-Compact against dregg's own root"
is *infeasible*, for exactly the field-mismatch reason.

### The re-commitment layer is what makes it feasible

The fix is not to teach Compact dregg's hash — it is to **re-commit dregg state
under Midnight's hash**. A relay maintains, alongside dregg's native
Poseidon2/BabyBear tree, a **mirror Merkle tree built with Midnight's own
`transientHash`/Poseidon over BLS `Fq`**, whose leaves are the dregg cell-state
commitments. The mirror root `R_mid : Field` is what gets checkpointed on
Midnight. Then:

- **Inclusion is fully native.** A prover submits a `MerkleTreePath<DEPTH, Field>`
  to a Compact contract; the contract calls `merkleTreePathRoot(path)` and asserts
  the result equals the checkpointed `R_mid`. Poseidon-over-BLS all the way — no
  non-native arithmetic, no FRI, a handful of Poseidon permutations. This is
  squarely inside what `merkleTreePathRoot` is for.
- **The mirror's faithfulness is the new optimistic/fraud-proof obligation.**
  `R_mid` must be the honest Midnight-hash re-commitment of the *same* cell
  states that sit under the genuine dregg root `R` (the one the FRI proof backs).
  That re-hash is done **out of circuit** by the relay (you cannot compute BLS
  Poseidon inside the BabyBear dregg circuit any more than the reverse — same
  mismatch), so its correctness is *attested*, not circuit-proven on either side.

This is the crux trade and it must be stated plainly: **the inclusion check
becomes native and cheap, at the cost of trusting (optimistically, with a fraud
backstop) that the mirror root faithfully re-commits the genuine dregg state.**

---

## 2. The architecture: optimistic mirror root + native inclusion

```
  DREGG SIDE                                          MIDNIGHT SIDE
  ─────────                                           ─────────────
  genuine cell states  ── FRI whole-history proof ──▶ (stays off Midnight;
   under dregg root R      backs "R is genuine")        backstopped by watchtower)
        │
        │  relay re-hashes the SAME leaves under
        │  Midnight Poseidon-over-BLS  (out of circuit)
        ▼
   mirror tree, root R_mid : Field  ──── attested + bonded ───▶  checkpoint R_mid
                                                                 (optimistic, dispute window)
                                                                        │
   anyone holding a cell's state + path ───  MerkleTreePath<D,Field> ──▶│
                                                                        ▼
                                              Compact: merkleTreePathRoot(path) == R_mid
                                              ── NATIVE, in-circuit, no FRI ──▶ accept inclusion
```

Two layers, two trust stories, cleanly separated:

- **Root validity** (`R` genuine, `R_mid` faithfully mirrors it): supplied
  optimistically — the relay attests `R_mid` at height `h`, posts a bond, opens a
  dispute window. The **existing watchtower** (`midnight_gateway.rs`) is the
  backstop, with a *new, simpler* fraud-proof shape (below).
- **State inclusion** (cell `X` is at state `Y` under `R_mid`): **native in
  Compact**, permissionless, instant, no trust beyond "the checkpointed `R_mid`
  is honest." This is the part the current bridge cannot offer at all.

### The new fraud proof is *simpler* than re-running FRI

Today's watchtower challenges a false *burn attestation* by re-verifying the
embedded bridge-action STARK proof. Under the mirror design the watchtower
instead challenges a **dishonest mirror root**:

> Claim: `R_mid` is the faithful Midnight-Poseidon re-commitment of the cell
> states under genuine dregg root `R` at height `h`.
>
> Fraud evidence: exhibit a cell `X` whose genuine committed state under `R` is
> `Y` (a dregg-side Merkle opening against `R`, which the FRI proof backs), but
> whose mirror leaf under `R_mid` is `Y' ≠ transientHash(X, Y)` (a mirror-side
> opening against `R_mid`). The two openings, re-hashed honestly, disagree → the
> relay re-committed wrong → slash.

Both openings are cheap to check on the dregg side (one BabyBear-Poseidon2 path,
one BLS-Poseidon path, recomputed in plain Rust by any watcher). No FRI
re-execution in the common case — the FRI proof is needed only to establish that
the *dregg* root `R` itself is genuine, and that is a one-time check per
checkpoint, not per challenge.

---

## 3. The general thesis: attestations + inclusions are the bridge primitive

Step back from Midnight. dregg's natural cross-chain primitive is **not** "verify
my transition proof" — almost no chain can, and the ones that can (via a
STARK→SNARK wrap onto a general pairing precompile, `NATIVE-PROOF-BRIDGES.md §1`)
are the exception. dregg's natural primitive is:

> **"Consume my cap-bounded attestation, and check the state it refers to is
> included under a root you already trust."**

Decompose any cross-chain claim dregg wants to make into two checkable pieces:

1. **A capability-bounded attestation** — a signature over `(claim, caveats,
   epoch, nonce)`. *Every* chain can verify a signature. dregg's whole model is
   attenuable proof-carrying tokens; "I am authorized to assert this, within
   these caveats" is exactly a cap-bounded attestation. (`midnight.rs`'s
   `FederationAttestation` is the degenerate threshold-sig instance of this.)

2. **A state inclusion** — "the state this claim is about is committed under root
   `R_chain`," checked against a **re-commitment in the target chain's own cheap
   native hash**. The hash is chosen *per target*:
   - **Midnight** → Poseidon-over-BLS mirror (`merkleTreePathRoot`), this doc.
   - **Ethereum** → keccak/SHA mirror (Solidity `MerkleProof.verify`), or skip
     the mirror once the STARK→SNARK wrap lands (`ethereum.rs`, the wrap verifies
     the *native* root, so inclusion can be against dregg's own `R`).
   - **Any Poseidon-BN254 chain** → a BN254-Poseidon mirror.

The **root's validity** is the only thing that ever needs the heavy machinery,
and it is supplied once-per-checkpoint, optimistically, with the FRI proof as the
1-of-N fraud backstop — *off* the target chain. Capabilities + inclusions are
what cross the boundary; the proof stays home as the dispute oracle.

This reframes the foreclosure (`ZKIR-V3.md`) from a wall into a non-issue for the
common case: you were never going to land the transition proof on Midnight, but
you never needed to. You needed Midnight to answer "is this cell really at this
state?", and that is a Poseidon Merkle path it can check natively. The mirror
re-commitment is the price of the field mismatch, and the watchtower already
exists to keep the relay honest about it.

---

## 4. The cleanest first build

Smallest real upgrade over the attestation-only bridge — a native inclusion
check Midnight runs in-circuit:

1. **`bridge/src/midnight_inclusion.rs`** (skeleton shipped alongside this doc) —
   the inclusion **message type**: a checkpointed mirror root `R_mid` + a
   `MirrorInclusionProof { cell_id, state_commitment, path }` mirroring the
   Compact `MerkleTreePath<DEPTH, Field>` shape, plus the **mirror re-commitment**
   builder (`mirror_leaf`, `MirrorTree`) that hashes dregg cell-state commitments
   into a Midnight-Poseidon-shaped tree. *Note:* the Rust side currently uses a
   placeholder leaf hash; the load-bearing unknown is computing **BLS-field
   Poseidon** in Rust to match Compact bit-for-bit (use
   `~/midnight/midnight-ledger/transient-crypto`'s `transient_hash`, or
   `midnight-zk`'s Poseidon, as the canonical implementation — see the module's
   `TODO(mirror-hash)`). Until that is wired the tree is structurally correct but
   not hash-compatible with Compact; that wiring is the first real task.

2. **`bridge/contracts/dregg_inclusion.compact`** (skeleton shipped) — the Compact
   **inclusion verifier**: a sealed `mirrorRoot` checkpoint field + a
   `verifyInclusion(path: MerkleTreePath<DEPTH, Field>)` circuit that asserts
   `merkleTreePathRoot(path) == mirrorRoot`. This is the native, FRI-free,
   in-circuit membership check. Compilation is gated on the `compact` toolchain
   (not installed here), same as `dregg_bridge.compact`.

3. **Checkpoint plumbing** (next, not in this skeleton) — extend the relay to
   post `R_mid` (the mirror root) as an optimistic checkpoint with a bond, and
   extend the watchtower's challenge to the **mirror-faithfulness** fraud proof of
   §2. Reuses the dispute framework already wired for the burn-attestation path.

The leverage: it is the first time a Midnight contract verifies a *dregg state
fact* in-circuit rather than trusting a federation signature — and it does so
entirely within Compact's native Poseidon-Merkle gadget, never going near the
foreclosed FRI verifier. The two halves the old design fused are now separate:
Midnight checks inclusion natively; the FRI proof keeps the root honest from the
dregg side.

---

## 5. Honest assessment

- **Native inclusion against dregg's *own* root: infeasible** (field/hash
  mismatch — Compact's Merkle is Poseidon-over-BLS, dregg's is
  Poseidon2-over-BabyBear; emulation is the FRI-class cost with no tooling).
- **Native inclusion against a *re-committed mirror* root: feasible and cheap** —
  a few Poseidon-over-BLS permutations via `merkleTreePathRoot`, exactly the
  stdlib's purpose. This is a *genuinely* native Midnight-side check, unlike the
  current attestation-only contract.
- **Cost of the mirror:** the relay must re-hash dregg state under Midnight's
  Poseidon (out of circuit, since neither chain can compute the other's hash
  in-circuit), and that re-commitment's faithfulness is optimistic + watchtower-
  backed, not proven. The fraud proof for it is *simpler* than re-running FRI
  (two cheap Merkle openings that disagree), so the 1-of-N security story holds
  and improves in clarity.
- **What stays foreclosed and stays off-chain:** the transition proof itself.
  Correctly so — it is the dispute oracle, not the bridge payload.
- **Generality:** the same attestation + re-committed-inclusion shape ports to
  any signature-and-Merkle chain by swapping the mirror hash to the target's
  native one. dregg's cross-chain primitive is the cap-bounded attestation plus a
  native inclusion, not the proof.
</content>
</invoke>
