# Frontiers Beyond deos — the next-big-thing map

A read-only scout (2026-06-24) of the major dregg frontiers **other than** the
four already in flight (the soundness floor / circuit-apex; the liquid/co-turn &
promises frontier; the house capacities; the deos/joy-path). For each remaining
frontier: the verified state (ALIVE-WIRED / ORPHANED-OR-PARTIAL / ASPIRATIONAL,
with `file:line`), the single next big move, and **wire-vs-build + size**.

**Discipline.** Every claim below was checked against source at HEAD, not against
labels. Where the orphan census
(`docs/ORPHANED-CAPABILITIES-CENSUS.md`) and the codex memory disagreed with the
source, the source wins and the divergence is noted. Two census claims were
spot-checked directly: `net-client` is genuinely absent from `dregg.system` (only
a `virtio_net_client_dma` *memory-region name* appears, `sel4/dregg.system:84`),
and there are **zero** live `node/src/` callers of `verify_quorum`,
`sortition_select`, `verify_history`, or any `bridge::{ethereum,mina,midnight}`
module. The orphan labels held up.

The tree root is `/Users/ember/dev/breadstuffs` (the Rust workspace). The Lean
trunk is under `metatheory/`. Paths below are relative to the tree root unless
noted.

---

## Headline

**Highest value × tractability = the seL4 `net-client` weld** — make the booting
verified firmament network-reachable. It is the *only* frontier where a
complete, already-deployed capability (Ed25519-gated signed-turn TCP ingress,
the SAME ed25519-dalek major the SDK signs with) sits one `.system`-file edit
away from closing the loop *ingress → gate → verified executor → persist*. It is
a pure **WIRE, size S**. Every other frontier is either a larger wire (federation
DKG/BLS, light-client DA) or a genuine build (the bridge SNARK wrappers, the
executor-pd Lean-ELF runtime).

**The honest split — wires vs builds:**

| Frontier | Next move | Wire/Build | Size |
|---|---|---|---|
| **Firmament/seL4** | net-client → 6th PD in `dregg.system` | **WIRE** | **S** |
| **Federation** | DKG ceremony trigger (then BLS-QC finality gate) | WIRE (gated on a BUILD: the epoch-transition trigger) | L then M |
| **Privacy** | wire `TurnValidityProof::verify_stark` into the live encrypted-turn path | **WIRE** | **M (~50 LOC)** |
| **Light client** | weld erasure DA into node-serve + multi-peer fetch | WIRE | S–M |
| **Bridge** | wire Midnight Level-1.5 optimistic dispute | WIRE (reuse) | M (3–4wk) |

Of these, **Firmament/seL4 and Privacy are the cleanest wires**; **Federation's
beacon keychain and the bridge SNARK wrappers are the genuine builds** (a real
DKG epoch-trigger; a Groth16-of-STARK circuit that is *not in the repo*).

---

## Frontier 1 — Firmament / seL4

**State: the 5-PD assembly is ALIVE-WIRED and boots; the network ingress and the
durable-storage backend are the open seats.**

The `dregg.system` 5-PD firmament boots and is driven (`sel4/dregg.system`):

- **verifier** (`:96`, `dregg-verifier-stark-pd.elf`) — real plonky3 STARK
  (BabyBear+BLAKE3+FRI). **ALIVE-WIRED.**
- **executor** (`:118`, `dregg-executor-microkit-pd.elf`) — embeds the proved
  `dregg_exec_full_forest_auth` (`execFullForestG` + admission), boots and
  self-stages a demo turn (nonce 7→8, 30-unit transfer, real receipt; see
  `sel4/dregg-pd/executor-microkit-pd/WALL.md:16-55`, `nm` shows the entry
  symbol `T`/defined). **ALIVE-WIRED.** The Mach-O→ELF "wall" is **passed** here
  (musl-hosted Lean runtime folded from `executor-rootserver/`).
- **persist** (`:135`, `dregg-persist-stub-pd.elf`) — holds the storage seat,
  reads the executor's `commit_out` sentinel to prove the cap is live, but
  persists nothing (`sel4/dregg-pd/persist-stub/src/main.rs:39-40`: awaits the
  block-device cap). **BUILT-NOT-DRIVEN.**
- **net** (`:147`, `dregg-net-driver-pd.elf`) — sole holder of the NIC cap +
  virtio-mmio + IRQ 79. **ALIVE-WIRED.**
- **app** (`:171`, `dregg-rbg-dir.elf`) — the rbg DirectoryCell. **ALIVE-WIRED.**

Three channels: net→executor (turn_in), executor→persist (commit ready),
executor→verifier (one-way bundle) (`sel4/dregg.system:176-199`).

**net-client — ORPHANED-OR-PARTIAL.** `sel4/dregg-pd/net-client/src/main.rs` is a
complete smoltcp PD: DHCPv4 (`:104-132`), TCP listen on :5555
(`config.rs:22`), and an Ed25519 admission gate (`turn_gate.rs:7-14,94`) that
de-envelopes `[32B pubkey][64B sig][msg]` and `verify_strict()`s it before any
byte reaches the executor — using `ed25519-dalek 2`, *the same major the SDK
signs `SignedTurn` with* (`turn_gate.rs:21`). It is wired into `net.system` and
`net-full.system` but **NOT into `dregg.system`** (verified: only the
`virtio_net_client_dma` region *name* appears at `dregg.system:84,155`, no PD).

**executor-pd (the Lean-ELF heart) — ASPIRATIONAL.**
`sel4/dregg-pd/executor-pd/src/main.rs:10-21` boots as a status heart; the
blocker is the Lean runtime on bare aarch64-sel4-microkit (leanrt/leancpp ship
Mach-O-only). **But this is moot for the live path** — the sibling
`executor-microkit-pd` already carries the verified executor in `dregg.system`.

**Interactive cockpit — ALIVE-WIRED.** `deos-tutorial.system` (6 screens,
keyboard IRQ 78) and `deos-image.system` (a live Smalltalk-style browser of REAL
deos cells, keyboard IRQ 78, gpui/lavapipe cockpit baked + blitted to the
framebuffer) both boot interactively. `compositor-fb` renders a static splash;
the dynamic `servo-render`-into-scanout path is the named next rung
(`sel4/dregg-pd/compositor-fb/src/main.rs:39-44`).

**Next big move: WIRE net-client as the 6th PD of `dregg.system`.** Add the PD +
2 Microkit channels (NIC→client, client→executor) + share one DMA region.
Capability fully exists and is deployed in `net-full.system`; the stitch turns
the booting firmament into a network-reachable verified OS where signed turns
arrive *through* the Ed25519 gate at the edge. **WIRE, size S.**

---

## Frontier 2 — Federation / consensus crypto

**State: live finality is a tight Ed25519 distinct-signer quorum; the
threshold-BLS / VRF / beacon / DKG floors are real and tested but the DKG
ceremony never gets *born*, so everything downstream of a committee key is
orphaned.**

- **Live finality — ALIVE-WIRED.** `node/src/finalization_votes.rs:216-243`:
  `VoteCollector::record()` rejects non-members (`:222`) and bad Ed25519 sigs
  (`:225`), counts *distinct* signers via a `HashSet` (`:229-230`), and fires
  consensus-attested exactly once at `distinct ≥ 2f+1` (`:237`). NOT threshold
  BLS.
- **threshold.rs (BLS QC) — ORPHANED.** `federation/src/threshold.rs:283-291`
  `verify()` does a real BLS12-381 weighted-threshold aggregate check, but all
  callers are `#[cfg(test)]` (`:428-579`); **zero `node/src/` callers** (verified
  by grep). Caveat surfaced by the agent: `hints` aggregates are
  *subset-dependent* (`beacon.rs:969` proves it), so a BLS QC is a finality
  *certificate*, not a randomness beacon.
- **vrf.rs (ECVRF sortition) — ORPHANED.** `federation/src/vrf.rs:513-526`
  `sortition_select` is RFC-9381; only `#[test]` callers, zero node callers
  (verified).
- **beacon.rs (threshold-BLS beacon) — ALIVE math / ASPIRATIONAL ops.** The
  beacon math (`federation/src/beacon.rs:589-597` `beacon_at`, Shamir deal +
  Lagrange aggregate, unique-output) is complete and DKG-connected
  (`dkg.rs:268-276` mints a `BeaconCommittee`). What is missing is the *operational
  trigger*: no epoch-transition logic starts the ceremony or activates the keys.
  (This is the nuance the orphan census flattened to "ORPHANED" — math is wired,
  *operation* is not.)
- **DKG — ASPIRATIONAL.** `federation/src/dkg.rs` + `dkg_ceremony.rs` are a
  complete Feldman/JF-DKG engine (deal→verify→complaints→finalize) with a
  signed-message transport layer. `node/src/dkg_service.rs` exposes routes
  (dealing / sealed-share / status) but **no genesis or epoch handler ever
  triggers the dealer/round flow** — orphaned *behavior* inside a routed service.
- **threshold_decrypt.rs — ORPHANED.** Shamir t-of-n GF(256). The LIVE encrypted
  path uses the **executor's own** cipherclerk-derived secret, not threshold
  reconstruction (`node/src/api.rs:3439-3443` `decrypt_for_executor`), so this
  federation copy has zero live callers.

**Next big move: BUILD the DKG ceremony trigger, then WIRE the BLS-QC finality
gate.** Sequencing matters: (1) **BUILD (L)** — an epoch-transition mechanism
that, at epoch N consensus-commit, broadcasts ceremony terms, runs the 4 DKG
rounds as turns, and adopts the `BeaconCommittee`/`BeaconShare`; this is the keychain
that unblocks beacon + sortition. (2) **WIRE (M, ~150 LOC, no new crypto)** —
once a committee key exists, add `FederationCommittee::aggregate()` +
`verify()` as a second gate after the distinct-signer quorum, giving
constant-size BFT certs in place of the O(n) signer set. The "wire BLS QC into
the finality gate" line from the census is accurate *but gated* on the DKG build
landing first.

---

## Frontier 3 — Privacy

**State: the Lean privacy layer is ALIVE-WIRED and proven (0 sorry); the live
encrypted-turn pipeline runs end-to-end EXCEPT the per-turn validity-proof gate,
which is built fail-closed but never called — a fee-DoS seam.**

- **Lean privacy tiers — ALIVE-WIRED.** `Dregg2.lean` imports `Dregg2.Privacy`
  (`:30`), `Dregg2.PrivacyKernel` (`:38`), `Dregg2.Privacy.Metadata` (`:39`).
  Proven: field-tier selective disclosure
  (`Dregg2/Privacy.lean:101-109`), value-tier `committed_conservation` (Pedersen
  homomorphism, `commit_zero` *derived* not axiom, `PrivacyKernel.lean:42-51,98-108`),
  graph-tier k-anonymity/stealth/nullifier laws (`Privacy.lean:349-390`), Yao
  obliviousness for garbled 2PC (`Dregg2/Crypto/GarbledJoint.lean:89-100`), and
  the metadata boundary with a two-sided hiding/leak tooth, **0 sorry**
  (`Dregg2/Privacy/Metadata.lean`).
- **Rust `encrypted.rs` `TurnValidityProof` — ORPHANED (fail-closed gate).**
  `turn/src/encrypted.rs:315-352` `verify_stark()` is a deliberate fail-closed
  gate (rejects both empty and non-empty proofs, `:333-351`) because the prover
  side is unwired (every `EncryptedTurn` carries `proof_bytes = vec![]`). The
  live decrypt handler `node/src/api.rs:3409-3467` decrypts
  (`decrypt_for_executor`, `:3443`) and executes (`apply_encrypted_turn`,
  `:3467`) **without calling `verify_stark()`** — so a non-paying/replayed
  encrypted blob can consume an ordering slot before decryption (fee-DoS).
- **Intent submit_encrypted + lowering + bond — ALIVE-WIRED (with the gate
  gap).** `submit_encrypted` is served; the pipeline submit → threshold-decrypt
  → solver-validity-proof → lowering (`intent/src/lowering.rs:288` `seal_plan_uniform`)
  → bond lock/release (`intent/src/bond.rs:106-189`) → execute is wired
  end-to-end. The orphan is specifically the *per-turn* `TurnValidityProof`, not
  the intent flow.
- **coord `private_leg` (MixedJoint) — ASPIRATIONAL.** `coord/src/atomic.rs:1225-1476`
  models private legs with binding proofs + anti-ghost tests, but the module is
  `#[cfg(test)]`-gated (`coord/src/lib.rs:83-84`) and
  `check_private_legs_admissible()` (`:1471`) is never called on the live
  coordination path.

**Next big move: WIRE `verify_stark()` into the live encrypted-turn path.** Add
the call in `post_submit_encrypted_turn()` before `apply_encrypted_turn()` (and
enable the prover side). Closes the fee-DoS seam. The verifier already exists
fail-closed. **WIRE, size M (~50 LOC of call-site + error-path; the prover-side
enablement is the larger half).** Secondary (build): lift `MixedJoint` onto the
live 2PC commit gate (size L, coordinator state-machine refactor).

---

## Frontier 4 — Light client

**State: the verify core is ALIVE-WIRED for external consumers (SDK / wasm /
demo) and PROVEN in Lean (0 sorry, gap-free under a named FRI floor); the
DATA-AVAILABILITY layer is the real gap — light clients trust a single HTTP
server for bytes, and a tested erasure-coded DA mesh sits with zero callers.**

- **verify core — ALIVE-WIRED (external) / ORPHANED (in-node).**
  `lightclient/src/lib.rs`: `verify_history` (`:147-162`, three teeth: VK-anchor
  pin + claimed-publics binding + O(1) recursive-STARK verify),
  `verify_finalized_history` (`:357-396`, + root-seam + 2n/3+1 quorum). Reached
  by `sdk/src/lib.rs` re-export, `wasm/src/bindings_lightclient.rs`, and the
  `whole_history_demo` binary — but **zero `node/src/` callers** (verified). A
  node does not call `verify_history`; the trust boundary is external.
- **Lean unfoolability — PROVEN-NOT-SERVED.**
  `Dregg2/Circuit/RecursiveAggregation.lean:192-211`
  `light_client_verifies_whole_history` and
  `Dregg2/Distributed/FinalizedLightClient.lean:187-198`
  `light_client_accepts_finalized_history` are gap-free theorems with anti-ghost
  teeth (root-mismatch unbinds, sub-quorum invalid). Named residuals: the FRI
  `recursive_sound` floor (carried as a structure field, witnessed
  non-vacuously) and the leaf-identity / leaf-publics-at-root pinning that closes
  with one lever (thread `table_public_inputs` up the tree).
- **Data availability — the real gap.** The light client has **no fetch logic**;
  it trusts a single HTTP origin (`node/src/api.rs:1554-1610`). A real,
  k-of-n Reed-Solomon + Merkle-path + DAS sampler exists at
  `storage/src/erasure.rs` + `storage/src/availability.rs` (24 tests green) with
  **zero live callers** — the node depends on `dregg-storage` but never calls
  `encode_for_availability`/`reconstruct`/the sampler. (Cross-ref the DA-mesh
  audit `docs/DA-MESH-AUDIT.md`: node↔node gossip is ALIVE; external light-client
  retrieval is single-server-trust.)
- **RecursionVk anchor distribution — ASPIRATIONAL.** Verifier requires
  `expected_vk` as a separate input (never self-anchored from the artifact,
  `lib.rs:149`); the wasm bindings enforce the discipline
  (`bindings_lightclient.rs:311-319`) but no node-side genesis/checkpoint channel
  ships the anchor — tests self-anchor via `fold_and_attest` (`lib.rs:201-208`).

**Next big move: WIRE the erasure DA layer into the node-serve path + a
multi-peer light-client fetch.** Add a node route that serves the
`AvailabilityManifest` + chunks-with-Merkle-proofs, and a light-client side that
reconstructs from a k-of-n subset across peers — upgrading "trust one server's
bytes" to "verify any operator's chunk and reconstruct." Both ends exist and are
tested. **WIRE, size S–M** (the DAS confidence-sampling loop on top is a separate
small BUILD). The anchor-distribution harness is a smaller adjacent BUILD (S).

---

## Frontier 5 — Bridge / interop

**State: the token→proof spine is ALIVE-WIRED and load-bearing; the cross-chain
connectors are HONEST binding-only scaffolding (correct-by-design, fully tested,
gaps clearly named) — NOT wired into any live node/coord service. ~60% real,
~40% aspirational.**

- **Token → proof pipeline — ALIVE-WIRED.** `bridge/src/{convert,delta,authorize,
  present,verifier,action_binding}.rs` form the load-bearing
  macaroon/biscuit → committed-FactSet → FoldDelta → AuthorizationTrace →
  STARK-ready presentation spine. The verifier is fail-closed on unknown AIR
  names (`verifier.rs:199-203`) with timestamp-freshness teeth; `action_binding.rs`
  pins full-fidelity bridge params at 32-byte granularity (no 30-bit
  truncation). Used by sdk/credentials/preflight in production.
- **Ethereum — ASPIRATIONAL (binding-only scaffold).** The settlement state
  machine is real and tested (`ethereum.rs:366-461`), but the cryptographic core
  — the Groth16 circuit encoding the plonky3 STARK verifier — is **explicitly not
  in the repo** (`ethereum.rs:48-61`); current mode is `SnarkSystem::BindingOnly`
  (a BLAKE3 commitment, not a pairing-checked SNARK).
- **Mina — ASPIRATIONAL (binding-only).** State machine real and tested; the
  in-circuit recursion was *removed* as vacuous (the pickles step never verified
  the Kimchi proof in-circuit — the module is honest about this,
  `mina.rs:13-21`). Binding-commitment + relay-liveness only.
- **Midnight — Level-1 ALIVE / Level-1.5+ ASPIRATIONAL.** The Ed25519 2-of-3
  federation attestation + validation + replay/nonce tracking is real and tested
  (`midnight.rs:47-127,466-579`, 20+ tests). The `.compact` contract is a design
  sketch (not compiled to ZKIR v3, `midnight_contract.compact`), and the observer
  RPC is mock-only (`midnight_observer.rs:341-416`; real Substrate RPC unbuilt).
- **Live wiring — NONE.** Verified: zero `bridge::{ethereum,mina,midnight}` or
  `midnight_observer` imports in `node/src/` or `coord/src/`. The bridge crate
  reaches live code only through the token→proof spine.

**Next big move: WIRE the Midnight Level-1.5 optimistic dispute bridge.** Reuse
the existing STARK-proven dispute framework (`app-framework/dispute.rs`) + the
live attestation: implement `BridgeDisputable`, a relay service, and a
watchtower. Strictly better security than Level-1 (1-of-N vs 2/3). **WIRE
(reuse), size M (~3–4 weeks).** The cross-chain SNARK recursion (Ethereum
Groth16-of-STARK, Midnight ZKIR shared programs) are genuine downstream BUILDs,
not blocking.

---

## Synthesis — point the swarm here next

After the in-flight welds land, the ranked queue beyond deos:

1. **seL4 `net-client` → 6th PD** (WIRE, S) — highest value × tractability; the
   verified firmament becomes network-reachable in one `.system` edit.
2. **Privacy `verify_stark` gate** (WIRE, M) — closes a live fee-DoS seam on the
   already-served encrypted-turn path.
3. **Light-client DA weld** (WIRE, S–M) — retires the single-server-trust gap
   using a tested-but-orphaned erasure mesh.
4. **Bridge Midnight Level-1.5** (WIRE/reuse, M) — first real cross-chain
   security upgrade, no new crypto.
5. **Federation DKG keychain** (BUILD L → then WIRE M) — the one genuine *build*
   among the top moves; unblocks beacon + BLS-QC finality + VRF sortition all at
   once, but needs the epoch-transition trigger first.

**Genuine builds (not wires):** the federation DKG epoch-trigger; the bridge
Groth16-of-STARK and ZKIR cross-chain circuits; the executor-pd Lean-ELF runtime
(already mooted by the microkit-pd sibling). **Everything else above is a wire** —
the capability exists and is tested; the stitch is to make the living protocol
reach it.
