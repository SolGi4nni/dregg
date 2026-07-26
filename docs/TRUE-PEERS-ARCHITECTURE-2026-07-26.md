# True-Peers: cross-chain lightclients as portable STARKs — architecture + deploy checklist

*2026-07-26. The goal: formalize/STARK-ify lightclients for the chains we implement with, and make the on-chain
aspects true peers with each other. Status: delivered end-to-end at fixture-VK resolution; the deploy steps below
are ember-gated. Every claim traces to a commit; maturity is labeled.*

## The shape (why this is "true peers")

Before: chain-verifies-dregg was live (Base-Sepolia's `DreggSettlement` verifies dregg's Groth16-wrapped STARK).
dregg-verifies-chain was *trusted* — a re-executing RPC observer or a trusted mirror, no portable proof.

Now, symmetric: **dregg produces a portable STARK "chain X finalized root R at height H", and any chain verifies
it on-chain** via the same registry. Each direction is a proof, not a trust assumption.

```
  chain X consensus  ──(Lean-formalized verify DECISION)──►  emitted AIR  ──►  STARK carrying *_no_forgery
        (the light-client verification, House Law #1: Lean-authored)              │
                                                                                  ▼
                                             gnark peer-wrap (reuses the FRI-wrap) → Groth16
                                                                                  │  public inputs
                                                                                  ▼  [chainId,height,rootHi,rootLo]
                                             on-chain DreggPeerRegistry.verify → provenPeerRoot(chainId,height)
                                                                                  │
                                             ISM/DVN attest a cross-chain message IFF included under a proven root
```

## The four chains (each an AIR carrying its no-forgery theorem)

| Chain | Consensus | Theorem | From | Commit |
|---|---|---|---|---|
| ETH/Base | sync-committee ≥2/3 + finality/exec branches | `eth_no_forgery` | Lean-formalized | `3884100013` (+ full-root `807eca1839`) |
| Cosmos | Tendermint strict >2/3 stake + adjacency | `tmNoForgery` | Lean-formalized | `87f7368f63` |
| Solana | rooted stake-weighted supermajority | `sol_no_forgery` | **trusted `True`-instance → proven** | `4834d1de55` |
| Midnight | GRANDPA strict >2/3 authority weight | `mid_no_forgery` | **trusted RPC-mirror → proven** | `5b540c20df` |

Each: the gate's verify DECISION is emitted as an IR-v2 AIR descriptor; a refinement `*LcAir_sound` +
`*LcAir_no_forgery` proves a satisfying AIR witness ⟹ the chain's foreign-validity ⟹ the chain's `*_no_forgery`.
So the **STARK carries the theorem**. Crypto (BLS/Ed25519/SHA) enters as **named verified carriers** — the AIR
proves the quorum/threshold/branch LOGIC *given* the crypto results. Axiom-clean ⊆ {propext, Classical.choice,
Quot.sound}, byte-pinned goldens, all built on hbox.

## The on-chain loop

- **`DreggPeerRegistry.sol`** (`0e40bd4d1c`) — the mirror of `DreggSettlement`: verifies a peer chain's finality
  Groth16 against a pinned VK, PI contract `[chainId, height, rootHi, rootLo]`, records `provenPeerRoot`. The inert
  ISM/DVN wired LIVE onto it. Proof-gated + receipted (dreggic — the proof *is* the capability, no owner/committee).
- **Producibility** (`9ba2e575b2`) — the 4 AIRs wired into `EmitByName` + `descriptor_by_name.rs` + the by-name
  `.json`s, so a node emits+proves each via `descriptor_by_name(name) → prove_vm_descriptor2`.
- **Peer-wrap** (`1bdaea5b67`) — `chain/gnark/peer_wrap_circuit.go`, the peer twin of `SettlementCircuit`: reuses
  the FRI-wrap verbatim (no new STARK verifier), exposes `[chainId,height,rootHi,rootLo]` byte-identical to the
  registry's `splitRoot`.

## The MODE distinction (the framing that matters — see the memory)
The four are **validator-complete**: a validator does the fast native BLS/Ed25519 check itself and the STARK
carries the *proven consensus logic*. The witnessing-boolean caveat below only bites in **full-light-via-proof
mode** (an untrusted prover fills the carrier, the proof stands alone). Validators need none of the fold work.
(And "discharging the FRI floor" is *not* a residual — everyone else silently assumes FRI soundness; naming it is
us being more honest than the field.)

## Residuals (honest, current resolution — the 07-26 crypto-fold daysprint moved this a lot)

1. **In-AIR crypto (the proof-mode fold)** — a shared Lean-GENERATED gadget library now exists: SHA-256
   (`Sha256Gadget`), SHA-512 (`Sha512Gadget`), BLAKE2b (`Blake2bGadget`), BLS12-381 full tower+curve FORCED
   (`Bls12381Tower`/`TowerExt`/`Forcing`), Ed25519 field+curve FORCED (`Ed25519Gadget`). **All 4 chains' HASH
   carriers are FOLDED** (carrier bit → in-circuit derivation, no-forgery routed through the fold): ETH `FIN_OK`
   (`f94704873c`)+`EXEC_OK` (`7b30b993c6`), tm/sol (`65920071b`), mid `AUTHSET_OK` (`49913c45d`). The composition
   wall is **broken** (`Sha256FoldForcing` `47889e49a` — gate-count-independent induction) and **Midnight's `hfold`
   is fully discharged** (`Blake2bFoldForcing` `b912a1b64`); the SHA end-to-end discharge (schedule recurrence +
   outer fold) is the convergent finish in flight. REMAINING = the **EC signature aggregates only**: `BLS_OK`
   (Miller loop + final exp over the forced tower) + `ED_OK` (scalar-mult + SHA-512 + mod-L + Edwards verify over
   the forced curve) — millions of gates, foundations forced, "keep composing the generators."
2. **Deployment wall** — the folds are PROVEN, NOT DEPLOYED: removing the carrier *columns* from the deployed
   descriptors needs the IR-v2 `proofBind` recursion seam (the ~5·10^5 flat gates exceed the byte-golden `#guard`).
   No descriptor touched, no VK regen. Shared ℤ↔`p_felt` field-width residual inherited.
3. **Full-root felt-width** — CLOSED on all 4 chains (ETH `807eca1839`, tm/sol/mid `70243691a4`).
4. **Real prove path e2e** — the peer-wrap tests use a fixture VK; the full setup+prove needs a real exported LC
   shrink fixture from the Rust prove path.

## DEPLOY CHECKLIST (ember-gated — the irreversible / public steps held for you)

- [ ] **Federation-provenance stamp** of the 4 LC descriptors (`DREGG_VK_REGEN_ACK`, `docs/VK-REGEN-CONTROLS.md`).
      This RE-KEYS the federation — the AIR fingerprint feeds the recursive VK hash every verifier pins. Do this
      once the descriptors' shapes are final (i.e. after the full-root widening + any in-AIR-crypto iteration, so
      you re-key once, not per-change). Sha256s are in the wiring commits.
- [ ] **Peer-VK trusted-setup MPC ceremony** — the dev Groth16 setup is forgeable; the real ceremony produces the
      VK `DreggPeerRegistry` pins.
- [ ] **Non-EVM chainId ratification** — Cosmos 118 / Solana 501 (SLIP-44), Midnight 2718 (placeholder) are
      governance-pinned at deploy.
- [ ] **`Dregg2.lean` un-truncation** (metatheory owner) — the truncation dropped 2 untracked imports
      (`CapHashBundleCutoverCheck`, `FloorRatchetSpecimens`) breaking HEAD for fresh checkouts. Independent of this
      work but blocks a clean deploy build.

See [[project-lightclient-stark-true-peers]] for the memory record; the Mina/Kimchi "internet of proofs" bet is a
separate, deep build (deferred — Pasta/BabyBear curve-cycle mismatch, SP1 never acceptable).
