# Option-B succinct wrapper for the trustless Solana bridge

This is the design (and first code slice) for the **Option-B** path named in
`docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`: move the whole pass-1–3 Solana consensus
check off-dregg into a **relayer circuit** that emits ONE constant-size proof, and
have dregg verify that single proof by **reusing its existing recursive-STARK
verify surface** — so the on-dregg cost stays `O(1)` (one succinct check + a
public-input binding) instead of `O(votes + accounts + rotation)`.

The pass-1–3 work made the *logic* trustless (modulo the weak-subjectivity
anchor). What it did **not** change is the on-dregg *cost*: today
`verify_lock_proof_consensus_anchored` (`bridge/src/solana_trustless.rs`)
re-runs, in the dregg verifier, the full consensus check — hundreds of Ed25519
verifications, the 16-ary accounts-hash folds, the warmup/cooldown curve over
every stake account, and the whole epoch-rotation chain. Option B relocates that
to a single off-dregg prover and leaves dregg a constant-size verify. **It does
not avoid the hard parts; it pays for them once, off-chain, per proof.**

## 1. The proof statement (the relation R)

The relayer proves knowledge of a witness `w` such that the existing in-process
anchored verifier accepts. Stated as a relation over a public instance `x` and a
private witness `w`:

```text
R(x, w)  ≡  verify_lock_proof_consensus_anchored(
                proof   = w.proof,
                spl_mint   = x.spl_mint,
                min_amount = x.min_amount,
                max_amount = x.max_amount,
                anchor     = x.anchor,         // (anchor_epoch, anchor_stake_table_root)
                require_poh = x.require_poh,
                poh_policy  = w.poh_policy,
            )  ==  Ok(LockProofTrust::ConsensusVerified)
        ∧  w.proof.{spl_mint, amount, dregg_recipient, lock_id} = x.{…}
        ∧  w.proof.consensus.{slot, bank_hash, epoch} = x.{…}
        ∧  w.proof.inclusion.vault_account = x.vault_account
```

In words: *"there exists a `SolanaLockProof` whose stake table + authorized voters
derive from bank state anchored at `x.anchor`, whose ≥ 2/3 effective-stake
super-majority (the warmup/cooldown curve) validly voted `(x.slot, x.bank_hash)`,
whose `vault_account` lock record (amount `x.amount`, recipient
`x.dregg_recipient`, id `x.lock_id`) includes into the voted accounts hash, and
(if `x.require_poh`) whose PoH chains to the slot blockhash — and I am revealing
only the mint-accounting public inputs."*

### Public instance `x` — `SolanaConsensusStatement`

Exactly the values dregg's value layer needs to credit the lock, plus the trust
root the proof chains to. Nothing about *how* consensus was checked is public.

| Field | Meaning |
| --- | --- |
| `spl_mint` | the mirrored SPL mint (binds the proof to this mirror) |
| `amount` | locked lamports → minted $DREGG (the conservation quantity) |
| `dregg_recipient` | the dregg `CellId` credited |
| `lock_id` | the consume-once lock id (the replay nullifier key) |
| `slot`, `bank_hash`, `epoch` | the finalized Solana slot the lock lives in |
| `vault_account` | the Solana account holding the lock record |
| `anchor_epoch`, `anchor_stake_table_root` | the weak-subjectivity trust root |
| `new_rate_activation_epoch` | the `reduce_stake_warmup_cooldown` network constant the curve used |
| `require_poh` | whether PoH linkage was demanded |

This is a real, canonical, digestible type (the first code slice, §4): the
circuit must expose exactly these as its public inputs, and the on-dregg side
binds them. `SolanaConsensusStatement::digest()` is the single field element /
hash the wrapper proof commits to as its public input.

### Private witness `w`

Everything pass-1–3 consumes but Option B keeps off-chain: the full
`SolanaLockProof` (all votes + their `VoteTxWitness` transactions, the
stake/vote/stake-history `ProvenAccount`s + 16-ary inclusion proofs, the
`StakeProvenance` rotation chain), and the `PohAnchorPolicy`.

## 2. The relayer circuit (the off-dregg prover — the build)

The circuit **is** the Option-A verification logic, encoded as an AIR (or a
fold of AIRs) over the same field dregg's STARKs already use (`BabyBear`,
plonky3). It re-encodes, constraint-for-constraint, what these functions check:

| Sub-check | Source (today, in-process) | In-circuit cost |
| --- | --- | --- |
| Ed25519 vote-signature batch | `solana_wire::parse_verified_vote_tx` / `witness_binds` | the dominant cost: hundreds of in-AIR Ed25519 verifications (a batch-Ed25519 / accumulation gadget) |
| effective-stake curve + ≥ 2/3 | `solana_provenance::effective_stake` + `VerifiedStakeTable::tally_authorized` | integer warmup/cooldown arithmetic + a stake-weighted sum + the `3·voted ≥ 2·total` compare |
| accounts-hash inclusion | `solana_wire::{solana_account_hash, verify_account_inclusion_16ary}` | blake3 per-account leaf + 16-ary sha256 folds (a hash-heavy column set) |
| bank-hash binding | `solana_consensus::BankHashComponents::compute` | one sha256 reduction |
| stake-table derivation + rotation | `solana_provenance::{derive_stake_table, rotate}` + the anchor root match | the derivation re-hash + the per-rotation-step attested supermajority |
| PoH linkage (optional) | `solana_consensus::verify_poh_anchored` | a bounded sha256 tick chain |

The output is a single proof `π` + the public instance `x`. **This is the
multi-month build** and it is shared with Option A (you encode the same logic);
the win is that it is built once, off-chain, and never carried in every dregg
verifier. PoH over a full slot (~432k hashes) remains the recursive-PoH item
named in `solana_consensus` (`MAX_POH_REHASH`).

## 3. The on-dregg verifier (reuse, do NOT fork)

dregg already verifies recursive `BabyBear` STARKs with a **constant-cost,
VK-pinned** check — the whole-history light client. Option B's on-dregg side is a
thin reuse of exactly that surface:

- `dregg-lightclient::verify_history(agg, expected_vk)` /
  `verify_turn_chain_recursive(agg, expected_vk)`
  (`circuit-prove/src/ivc_turn_chain.rs`) — the plonky3 recursive-STARK verifier whose
  cost is **independent of the folded work**, running three teeth: (1) the VK
  pin against a configured trust anchor `RecursionVk`, (2) the carried-publics
  attestation against the binding STARK (Fiat–Shamir binds the public inputs, so
  a prover cannot swap them), (3) the root batch-STARK verify.
- The trust anchor pattern is identical to the light client's: a
  `SolanaConsensusVk` (a `RecursionVk` fingerprint of the honest relayer circuit)
  is distributed in the mirror's configuration **exactly like any SNARK VK** —
  minted once from an honest setup, NEVER read from the proof under verification.

So the on-dregg entry is:

```text
fn verify_lock_proof_succinct(
    pi: &SolanaConsensusStatement,     // the public instance x
    proof_bytes: &[u8],                // the wrapper proof π (an envelope)
    expected_vk: &SolanaConsensusVk,   // the configured trust anchor
) -> Result<LockProofTrust, LockProofError> {
    // 1. constant-cost succinct verify (REUSE the existing recursive surface):
    verify_turn_chain_recursive(decode(proof_bytes), expected_vk)?;   // teeth 1+3
    // 2. bind π's exposed public inputs to `pi.digest()` (tooth 2 already proved
    //    they equal the proof's bound publics):
    require(proof.exposed_public_digest == pi.digest())?;
    Ok(LockProofTrust::ConsensusVerified)
}
```

and the value-layer seam is the SAME swap pass-1–3 already prepared
(`docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`, "Migration"): a verified statement
routes its `(spl_mint, amount, dregg_recipient, lock_id)` through the existing
`MirrorState::credit_lock` conservation accounting — only the front gate
(signature-verify → consensus-verify → succinct-verify) changes; the Σδ=0 mint
accounting is untouched.

The dregg-side verify stays `O(1)`: one recursive-STARK check (cost independent
of the number of votes/accounts/rotation steps) plus a digest equality. That is
the entire point of Option B.

## 4. First slice (shipped) — the public-input statement shape

`bridge/src/solana_trustless.rs` now defines `SolanaConsensusStatement` (the
public instance `x` above) with a canonical, domain-separated `digest()`, and
`SolanaConsensusStatement::of_verified(proof, spl_mint, …, anchor, require_poh)`
which **derives the statement from a proof that the in-process anchored verifier
has accepted** — i.e. it pins the relation `R`'s public projection to today's
ground-truth checker. This is the contract the future relayer circuit must
satisfy: the circuit exposes `digest()` as its public input, and
`verify_lock_proof_succinct` binds it.

The statement is real and testable (deterministic digest; a change to any public
field changes the digest; the verified-constructor agrees field-for-field with the
proof). It carries no proof system yet — it is the typed seam between today's
in-process check and the succinct wrapper.

## 5. What remains to build (named precisely)

1. **The relayer consensus AIR (§2)** — the dominant, multi-month item: the
   in-circuit Ed25519 batch, the 16-ary blake3/sha256 accounts-hash folds, the
   integer warmup/cooldown curve, the derivation + rotation, the bounded PoH. The
   honest distance to a *deployed* Option B is this circuit; everything else is in
   place.
2. **`SolanaConsensusVk` minting + distribution** — the honest-setup fold that
   produces the trust anchor, distributed like the light client's `RecursionVk`.
3. **`verify_lock_proof_succinct` + `mint_against_lock_proof_succinct`** — the
   thin on-dregg verify (§3) once a real `π` exists; a straight reuse of
   `verify_turn_chain_recursive` + the `credit_lock` seam, gated behind the VK.

Until (1)–(3) land, the deployed trustless path remains
`verify_lock_proof_consensus_anchored` (the in-process check) — fully sound,
just `O(votes)` on the verifier rather than `O(1)`. Option B is an **optimization
of the on-dregg cost**, not a soundness change: both paths verify the same
relation `R` against the same weak-subjectivity anchor.
