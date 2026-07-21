# Is dregg's universal-memory (umem) construction post-quantum?

This is an honest, grounded analysis. It separates the umem **memory argument** (the
thing `Dregg2/Crypto/UniversalMemory.lean` proves sound) from the **surrounding
authorization machinery** it rides inside, and states the quantum exposure of each
cryptographic carrier by name, against the carrier floor the assurance case publishes.

The short answer: **the umem memory argument is hash-based and carries no
elliptic-curve / discrete-log assumption of its own — it is plausibly post-quantum
modulo hash output sizing and the named FRI floors. The non-PQ exposure lives in
the surrounding signature, value-commitment (Pedersen / DLog), and transport
carriers, not in the memory
argument.** So yes, umem is the post-quantum-est part of dregg.

**Update (corrected 2026-07-21) — turn authorization has a hybrid wire form but
is not yet a PQ identity boundary.** A turn token can carry ed25519 **∧**
ML-DSA-65 (FIPS 204), with both present halves verified
check (`Authorization::HybridSignature`, `turn/src/action.rs:457`; `turn/src/pq.rs`).
The hybrid's security **reduces to `discrete-log` OR `Module-SIS`** — unforgeable if
EITHER floor holds (`HybridCombiner.hybrid_secure_if_either_floor`,
`metatheory/Dregg2/Crypto/HybridCombiner.lean:213`; classical leg → DL in
`SchnorrEufCma.lean:278`, PQ leg → MSIS in `HybridCombiner.lean:194`; commits
`a875a9104` / `db1214a9f`). The transport/session KEM is the matching `X25519 ×
ML-KEM` X-Wing hybrid, reducing to `MLWE` on the PQ side (`MlKemIndCca.lean:312`,
commit `38e83fac8`). So the "one carrier swap away" caveat below is now BUILT and
staged (default-off `require_pq`, fail-closed on a present half). The current
verifier checks ML-DSA against a self-carried key rather than an independently
enrolled cell key, so the residual is both the rollout flip **and identity/key
binding**, plus the Pedersen value-commitment path. `MSIS`,
`MLWE`, and `DL` are named ASSUMPTIONS the reductions rest on — see
`docs/PQ-CRYPTO.md` for the full chain.

## What umem actually is (the object under analysis)

`Dregg2/Crypto/UniversalMemory.lean` proves that **one** Blum offline-memory multiset
argument over a unified, domain-tagged address space (`Domain × κ`, the six domains
registers/heap/caps/nullifiers/index/working — `UniversalMemory.lean:87-94`; `working`
is the transient scratch domain, commitment-inert by theorem `working_commitment_inert`
and mirrored by the Rust `UDomain::Working = 5`) soundly covers
every per-domain projection simultaneously. The three load-bearing pieces:

1. **The interior memory argument** — `universal_memory_sound`
   (`UniversalMemory.lean:210`) reduces consistency of every domain to ONE balance
   via `MemoryChecking.memcheck_sound`. This is a **multiset / LogUp** permutation
   argument; its soundness is *combinatorial inside the field* (the balance is an
   algebraic identity the STARK enforces), not a crypto assumption.

2. **The boundary roots** — the four map roots (cap/nullifier/heap/index) are derived
   sorted-Poseidon2 Merkle roots over the final memory cells: `boundaryCells`
   (`:351`), `boundary_root_derived` (`:447`), and the anti-forgery teeth
   `boundary_init_root_bound` (`:506`) and `nullifier_fresh_binds_root`
   (`:770`). These ride exactly ONE named crypto carrier:
   **`Poseidon2SpongeCR`** (`Poseidon2Binding.lean:162-178`), collision-resistance of
   the in-circuit Poseidon2 sponge. The header pins it explicitly: "Crypto enters
   ONLY as the named `Poseidon2SpongeCR` hypothesis ... never as an axiom"
   (`UniversalMemory.lean:47-48`). Floor-resolution note: the repo's own
   floor-honesty record states this hypothesis as injectivity and PROVES that
   statement false at the deployed BabyBear parameters
   (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`); the keyed computational
   `CollisionResistant` restatement is itself proved false at the deployed
   compressing parameters by the same pigeonhole
   (`FloorGames.collisionResistant_false_of_compressing`). The honest,
   actually-proved form is the query-bounded random-oracle floor
   (`RomQueryFloor.romCollision_hard` / `binaryRom_hard_linear_budget`, with the
   efficiency class `Eff` carried as a parameter). That is a resolution fact about
   the classical floor's *statement*, not a quantum exposure — the carrier's
   quantum status below is unchanged by it.

3. **The proof that wraps it** — the whole memory table + boundary roots are attested
   by the deployed batch-STARK. That soundness is the STARK floor
   (`metatheory/docs/STARK-FLOOR.md`): `StarkSound` / FRI extraction over BabyBear with a
   Poseidon2 Merkle commitment. No pairing, no DLog.

So the umem argument's *entire native* cryptographic dependency is two things:
**Poseidon2 collision-resistance** and **FRI/STARK soundness** (which itself bottoms
out in Poseidon2 CR for its Merkle commitments). Both are hash-based.

## (1) PQ vs non-PQ — by carrier

The assurance case names eight floor items (`AssuranceCase.lean:21-41`). Mapping them
onto the umem path:

### PQ — the umem memory argument itself (hash-based, no DLog)

| Carrier | Where (file:line) | Role in umem | Quantum status |
|---|---|---|---|
| **Poseidon2-permutation CR** | `AssuranceCase.lean:27-32`; `Poseidon2Binding.lean:162-178` | Sorted-Merkle boundary roots; `root_injective` anti-forgery teeth; nullifier absence binding | **PQ-plausible.** Generic hash, no algebraic structure broken by Shor. |
| **FRI / STARK soundness** | `AssuranceCase.lean:38-39`; `metatheory/docs/STARK-FLOOR.md` | Attests the memory table + balance + boundary roots | **PQ-plausible.** FRI is hash-/IOP-based; its Merkle commitments are Poseidon2. No DLog. |
| **The Blum multiset balance** | `universal_memory_sound`, `memcheck_sound` (`UniversalMemory.lean:210`) | The interior soundness — registers/heap/caps/nullifiers/index from one check | **Not cryptographic.** A field-algebraic permutation identity; nothing for a quantum computer to attack beyond the field/hash terms already counted. |
| **BLAKE3 CR** | `AssuranceCase.lean:33` | Out-of-circuit transcript/content hash | **PQ-plausible.** Generic hash. (Adjacent, not strictly inside the in-circuit memory argument.) |

### NOT PQ — the surrounding authorization / value carriers

| Carrier | Where (file:line) | Role | Quantum status |
|---|---|---|---|
| **ed25519 EUF-CMA** | `AssuranceCase.lean:34`, `:149-155`; `turn/src/action.rs:216,256,395-407,523`; `turn/src/composer.rs:22`; `turn/src/conditional.rs:481-484` | The signature that AUTHORIZES the turn whose effects produce the memory writes; `credentialValid` routes to the ed25519 carrier | **BROKEN by Shor.** ed25519 is a discrete-log scheme on Curve25519; a CRQC recovers the signing key from the public key. |
| **Pedersen / discrete-log** | `AssuranceCase.lean:37`, `:231-233`; `cell-crypto/src/value_commitment.rs`, `value_link_zk.rs`; `circuit/src/effect_action_air.rs` | Pedersen value commitments (only when values are committed rather than cleartext) | **Binding / proof soundness BROKEN by Shor** (DLog falls). Pedersen hiding itself is information-theoretic when the blinding is uniform; Shor lets an adversary equivocate openings and forge the DLog proof layer, not read a uniformly blinded value merely from the commitment. The case proves committed = cleartext (`Spec.committed_iff_cleartext`, `:233`), so this is conditional, not always on the umem path. |
| **X25519 / curve25519 ECDH** | `captp/Cargo.toml:15-17`; `cell-crypto/Cargo.toml:16-21` | CapTP transport key agreement, stealth one-time keys (`action.rs:395-407`) | **BROKEN by Shor** (ECDH = DLog). Transport-layer, adjacent to umem, not in the memory soundness. |
| **HMAC / AEAD** | `AssuranceCase.lean:35-36` | Macaroon caveat tags; sealed payloads | **PQ-plausible** (symmetric — Grover only). Adjacent to authority, not the memory argument. |

The key structural fact: **no elliptic-curve or discrete-log assumption appears
*inside* the umem memory argument.** The DLog carriers (ed25519, Pedersen, X25519)
sit in the authorization and value-hiding layers that *feed* the memory writes, not in
the soundness of the writes themselves.

## (2) Grover / Shor exposure, honestly

**Shor** (breaks DLog/factoring — the catastrophic one):
- Hits **ed25519, Pedersen, X25519** completely. These are not weakened — they fall.
  A CRQC can forge any turn signature, open Pedersen commitments to any value, and
  break CapTP transport key agreement.
- Does **nothing** to the hash-based umem memory argument (Poseidon2 CR, FRI, the Blum
  balance). Shor has no purchase on a generic hash or a multiset identity.

**Grover** (quadratic speedup on generic search — the survivable one):
- Hits **Poseidon2, BLAKE3, FRI's Merkle commitments, HMAC, AEAD keys**. The classic
  rule: an `n`-bit collision/preimage target effectively drops toward `n/2`-ish under
  quantum search (with substantial caveats — Grover parallelizes poorly, and the
  collision speedup via BHT is closer to `n/3` and rarely worth it in practice).
- **The honest sizing question for umem.** The STARK floor (`metatheory/docs/STARK-FLOOR.md:104-105`)
  states the query ledger as `130` bits conjectured (a REFUTED conjecture — Crites–Stewart,
  eprint 2025/2046; Kambiré, arXiv 2604.09724 — kept as a drift baseline) / `73` bits on the
  Johnson QUERY column, with the field challenge space `|EF| ≈ 2^124` and the Poseidon2
  commitment hash as additional caps. ⚑ `73` is the query column, not the soundness: it is
  the `m → ∞` idealisation of BCIKS20's `α` and drops the commit-phase term `ε_C`, which at
  the deployed wrap reads `71` and BINDS (`Dregg2.Circuit.FriLedger.friCommitLedger`);
  composed as ethSTARK eq. (20) the pair reads `~70`. Under Grover the relevant question is
  the **hash output / commitment width**,
  not the FRI query count: FRI soundness error is an interactive-protocol bound that
  Grover does not generically halve, but the **Poseidon2 Merkle commitment** and any
  fixed-output digest are subject to Grover preimage / quantum collision search. The
  faithful **8-felt (about 248 output bits) commitment surface is already DEPLOYED** (the
  `node8` gadget, `CAP_DIGEST_W`/`HEAP_DIGEST_W = 8`, v9→v13 geometry — see
  `docs/FAITHFUL-COMMITMENT-LAW.md` / `docs/reference/faithful-commitment.md`), and
  it has about 124 classical collision bits but only about 83 generic quantum
  collision bits under `2^(n/3)`. Thus 8 felts are faithful to the committed bytes
  but do not meet a conservative 128-bit quantum collision target; width remains
  open even though the earlier anti-truncation campaign landed.
- The grinding term (`query_proof_of_work_bits = 16`, `metatheory/docs/STARK-FLOOR.md:87`) is a hash
  preimage PoW; Grover halves its effective cost (`16 → ~8` bits). Negligible either
  way, but worth noting it is a Grover-soft term.

Net: **umem itself has a hash-width/transcript/soundness sizing problem, not a
Shor structural break.** Quantum generic collision search scales roughly as
`2^(n/3)` (not “Grover halves collision security”); the structural Shor break is
in the non-umem carriers.

## (3) What would make the WHOLE umem path fully PQ

The memory argument is already on PQ-plausible primitives. To make the *end-to-end
path* — "an authorized turn produces a sound memory commitment a light client can
trust" — fully post-quantum, three changes:

1. **Bind and require a PQ signature. — PARTIAL.** The wire token can carry
   a HYBRID `ed25519 ∧ ML-DSA-65` signature (`Authorization::HybridSignature`,
   `turn/src/action.rs:457`; `turn/src/pq.rs`; ML-DSA-65 via `fips204` in
   `dregg-pq/src/mldsa.rs`), verifying only when both halves check. Rather than swap
   ed25519 OUT, the target hybrid welds ML-DSA ON; once both keys are enrolled
   for the same identity, its EUF-CMA reduces to `discrete-log OR Module-SIS`
   (`HybridCombiner.hybrid_secure_if_either_floor`,
   `metatheory/Dregg2/Crypto/HybridCombiner.lean:213`). The capability-chain (biscuit)
   soundness rides the same floor (`CapabilityChain.chain_unforgeable_under_hybrid_floor`,
   `:237`). The Lean side routes through the `SigScheme`/`EufCma` predicate portal, so
   the proof structure is unchanged; only the realized carrier and wire format changed.
   The runtime is STAGED (`TurnExecutor::require_pq`, default off, fail-closed on
   a present-but-invalid PQ half — `turn/src/executor/authorize.rs:1054,1064`).
   More than a flip remains: ML-DSA currently verifies against the key carried in
   the authorization, while Ed25519 verifies against the target cell. The PQ key
   must be independently enrolled/pinned to that same cell and epoch.

2. **Remove / replace Pedersen value hiding.** If confidential values are wanted PQ,
   Pedersen (DLog) must go — to a hash-based or lattice commitment. The case already
   makes Pedersen conditional (committed = cleartext, `:233`); the cleartext path is
   already PQ, so the simplest fully-PQ posture is "no DLog value commitments."

3. **Size hashes for quantum collision and QROM margins.** Keep Poseidon2/BLAKE3/FRI,
   but pin widths and unbiased transcript sampling to a stated target. The faithful
   8-BabyBear commitment is about 248 output bits: about 124 classical collision bits,
   but only about 83 generic quantum collision bits under `2^(n/3)`. A conservative
   128-bit quantum collision target needs at least 384 output bits (at least 13
   canonical BabyBear limbs; 16 is a simple profile) plus construction-specific
   Poseidon2/QROM analysis. The 8-felt commitment is deployed at HEAD
   (`docs/FAITHFUL-COMMITMENT-LAW.md` /
   `docs/reference/faithful-commitment.md`; the historical widening analysis is
   archived at `.docs-history-noclaude/FAITHFUL-STATE-COMMITMENT.md`). Widening is
   open work, not merely a tuning knob. Read the FRI side on the Johnson QUERY column
   (`73`) and the commit-phase column (`71`) separately — and note that **raising queries
   cannot buy a margin here**: `ε_C` contains neither `num_queries` nor `pow_bits`, so at
   the deployed degree-4 extension the eq. (20) composite saturates at `~77.98` no matter
   how many queries are bought (`docs/reference/FRI-PARAM-FRONTIER.md` FRONTIER B). The one
   lever on that ceiling is the extension degree, at `log₂ p = 30.91` bits per degree.
   X25519 transport → a PQ KEM (ML-KEM) closes the adjacent confidentiality leg.

FRI/STARK needs no curve-to-PQ primitive swap: its transparent hash/AIR architecture
is already the right one. It still needs the width, extension-degree, transcript/QROM,
and named soundness-assumption work above; “hash-based” alone is not a completed PQ
security argument.

## (4) Verdict — is umem "the post-quantum-est part of dregg"?

**Yes, with the boundaries named.**

- The umem **memory soundness argument is post-quantum-plausible today**: its only
  native crypto carriers are Poseidon2 collision-resistance and FRI/STARK soundness
  (`UniversalMemory.lean:47-49`, `AssuranceCase.lean:27-32,38-39`), both hash-based,
  with the interior covered by a non-cryptographic field-algebraic Blum balance
  (`universal_memory_sound`, `:210`). No elliptic-curve or discrete-log assumption
  lives inside it. Its native quantum exposure is **hash width, QROM transcript,
  and FRI soundness sizing** — parameter and proof obligations, not a Shor-broken
  curve assumption.

- It is *more* post-quantum than the rest of dregg precisely because the rest of
  dregg's trust still leans on **Shor-breakable DLog carriers**: ed25519 turn
  signatures (`AssuranceCase.lean:34`), Pedersen value commitments (`:37,231-233`),
  and X25519 transport. Those are the parts that *fall* to a CRQC, not merely shrink.

- The honest caveat against overclaiming: **"umem is PQ" ≠ "the umem path is PQ."** A
  light client trusting a Q-chain trusts the STARK (PQ-plausible) *and* the signature
  that authorized the turn. As of 2026-07-09 that signature is the HYBRID `ed25519 ∧
  ML-DSA` (its EUF-CMA reduces to `DL OR MSIS`), so a quantum adversary that breaks
  ed25519's discrete log does **not** necessarily face the enrolled user's ML-DSA
  key: today it can carry its own valid ML-DSA key. The "forge authority before
  the memory argument runs" gap closes only when `require_pq` is enabled **and**
  the PQ key is independently bound to the target cell/epoch. Other residual
  non-PQ carriers on the *whole* path are the
  Pedersen value commitment (only when values are committed, and the case proves
  committed = cleartext) and X25519-only transport legs. An `X25519 × ML-KEM`
  X-Wing primitive exists, but coverage must be established for each live transport.
  The memory argument is honest;
  its input authority has a hybrid wire shape, but is not yet a sound PQ identity boundary.

The carrier floor that grounds all of this: `AssuranceCase.lean:21-41` (the eight
items), `metatheory/docs/STARK-FLOOR.md` (the FRI/Poseidon2 envelope), and
`Dregg2/Circuit/Poseidon2Binding.lean:162-178` (the sole in-circuit crypto carrier the
umem boundary roots ride). The one-line summary: dregg's *memory argument* is
hash/PQ-shaped; its *authority tokens* have a staged hybrid wire form but still
need mandatory verification and independent ML-DSA identity binding. The
Pedersen path, hash-width/QROM margin, and other external carriers remain too.
See `docs/PQ-CRYPTO.md` and `docs/deos/PQ-EVERYTHING-DREGG.md`.
