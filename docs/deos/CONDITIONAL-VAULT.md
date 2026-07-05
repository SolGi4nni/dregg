# Conditional Timelock Vault — value locked until a release rule is met, claimable exactly once

An autonomous agent living inside dregg needs to *lock value with a release rule*:
savings it cannot touch until a date, a vested/scheduled release, a commitment
device ("I cannot spend this until block N"), a deadbolt fund that only opens when
a secret/proof is presented. A **conditional vault** is that house capacity: value
sealed under a release condition, then claimable **exactly once** by the
beneficiary when the condition is genuinely met. The danger is symmetric:

* an **early release** — claiming before the condition is met (the block height is
  not yet reached, or no valid proof);
* a **forged condition-proof** — presenting a witness that does NOT satisfy the
  locked condition (the wrong preimage) and having it accepted;
* a **double-claim / replay** — claiming a vault that has already settled, releasing
  the locked value twice; and
* a **forged lock** — a claim whose committed vault state does not reflect the real
  lock (a tampered amount or a swapped condition).

A conditional vault closes all four. The terms (`beneficiary`, `asset`, `amount`,
`release_height`, `condition`) are sealed into the cell's commitment, and a `claim`
step is **gated on the genuine satisfaction of the committed condition** and
**one-shot** — it releases the committed value to the beneficiary and flips a
committed `settled` flag; any later claim of a settled vault is REJECTED. A holder
of the commitment can tell, for any block + witness, whether the vault is genuinely
claimable — so an early claim is detectable, a forged proof diverges from the
committed condition digest, and a replay finds the settled flag already set.

This is Track 2 (capacity) of *safely live within dregg*, VK-freedom era. It is
**built, not memoed** — a new module `cell/src/vault.rs` — and it is a **weld**:
the substrate it needs (an openable committed heap, the signed balance ledger, the
one-shot/settled discipline, block height as the clock, a domain-separated hash for
the hashlock) already exists; the module joins it into the conditional-vault
capacity and adds the **forge detectors** that make the lock load-bearing.

---

## 1. What a conditional vault is

A vault cell carries `VaultTerms` — a value lock under a release rule:

> `beneficiary` may claim `amount` of `asset` once the `condition` is met.

and a one-shot `settled` flag. The `condition` is the genuine minimal slice — one
of two:

* `Condition::AtHeight` — released at/after `release_height` (the "savings until
  block N" / vested-release / commitment-device lock); claimable when the presented
  block `>= release_height`. No witness required.
* `Condition::OnProof { digest }` — released when a preimage hashing to `digest` is
  presented (the "deadbolt fund opened by a secret/proof" lock); claimable when the
  presented witness `w` satisfies `H(w) == digest`. The preimage is never stored in
  the clear — only its domain-separated hash is committed.

The lifecycle:

| op           | meaning                                                                              |
|--------------|--------------------------------------------------------------------------------------|
| `open_vault` | bind the terms digest + the locked `amount`; `settled = 0` (locked, not yet claimable) |
| `claim`      | verify the committed condition is genuinely met ∧ not-yet-settled; release the committed amount; flip `settled = 1` |
| `is_claimable_at` | at block `b` with witness `w`, whether a beneficiary's claim would be admitted |

The genuine minimal slice is a **single-beneficiary, single-asset vault with ONE
condition** (height timelock OR hashlock). Full HTLC chains (paired hashlock +
refund timelock + counterparty), multi-stage vesting curves, and partial/streamed
release are the named next slice, not stubs here.

---

## 2. The weld (what already existed, disconnected)

The module welds onto substrate already in the tree, the same vehicles
`cell/src/escrow_sealed.rs`, `cell/src/allowance.rs`, and
`cell/src/obligation_standing.rs` use:

* **The committed heap** (`CellState::set_heap` / `compute_heap_root`,
  `cell/src/state.rs`) is an openable sorted-Poseidon2 `(collection, key) →
  FieldElement` map ALREADY folded into the canonical state commitment. We reserve
  a collection id (`VAULT_COLL`) for the vault ledger — the terms digest, the locked
  `amount`, and the `settled` flag all live there, bound into the cell's commitment
  **for free**, no commitment-version bump. (Same heap-binding discipline as
  `ESCROW_COLL` / `ALLOWANCE_COLL`.)

* **The signed `i64` balance ledger** is the value primitive: the vault locks an
  `amount` — exactly the quantity `CellState::balance` carries — released to the
  beneficiary on a genuine claim.

* **Block height** is the time clock: an `AtHeight` vault is claimable only at a
  presented block `>= release_height` — the same block-height clock `allowance.rs`
  derives its epochs from.

* **The nullifier / one-shot discipline** (the escrow leg-`Consumed` tooth) is the
  shape the `settled` flag takes: a claim flips the committed `settled` bit, and
  every claim path checks it first — a settled vault is a spent nullifier and cannot
  be re-claimed.

* **A blake3 domain-separated digest** (the escrow terms digest, the obligation
  condition digest) is the shape the `OnProof` hashlock takes: the committed
  condition digest is `H(witness)` for the genuine preimage, so a forged witness
  hashes to a different value and is REJECTED. The terms digest *folds in the
  condition kind and the hashlock target*, so a vault cannot be reinterpreted under
  a different condition.

`EFFECT_TRANSFER` (the facet bit `1 << 1`, already named in `facet.rs`) is the
existing effect mask a claim's value-release rides on; no new facet bit is
introduced.

---

## 3. The soundness story — what binds the lock

The terms' digest, the locked `amount`, and the `settled` flag are written into
`VAULT_COLL`, hence into the cell's commitment. Against a holder of the commitment +
heap openings, the binding enforces:

1. **No early release.** A claim presents a block `at_block` and (optionally) a
   witness. For an `AtHeight` vault, the claim is admitted only when `at_block >=
   release_height`; for an `OnProof` vault, only when the presented witness hashes
   to the committed condition digest. A claim that meets neither → `HeightNotReached`
   / `ProofMismatch`.

2. **No forged proof.** The condition digest is committed (folded into the terms
   digest checked here). A forged witness (wrong preimage) hashes to a value that
   diverges from the committed digest → `ProofMismatch` — the same hashing the honest
   claim runs.

3. **One-shot.** The vault carries a `settled` flag in the commitment. A genuine
   claim flips it; any later claim of a settled vault → `AlreadySettled`. The value
   cannot be released twice.

4. **No forged lock.** The released amount is the *committed* amount, and the
   condition is the *committed* condition: a claim cannot release more than the vault
   locked, nor reinterpret the vault under a different condition — both diverge from
   the bound terms digest → `TermsMismatch`.

The honest-accept path (`claim` accepting) and every forge-reject path run through
the SAME `VaultState::check_claim` verification core, so a stub in either direction
fails one polarity (non-vacuity by construction).

---

## 4. The API (the genuine slice)

```rust
// a height timelock: beneficiary may claim 500 of asset at/after block 11_000.
let terms = VaultTerms::at_height(beneficiary, asset, /*amount*/ 500, /*release_height*/ 11_000);
open_vault(&mut cell, &terms)?;                              // seal & lock

// before release, not claimable; at/after release, claimable:
let view = VaultState::read(&cell)?;
vault::is_claimable_at(&view, &terms, 10_999, b"");          // == false
let released = claim(&mut cell, &terms, &Claim::at_height(beneficiary, 11_500))?; // == 500, settled

// a hashlock: beneficiary may claim by presenting the secret.
let terms = VaultTerms::on_proof(beneficiary, asset, 500, 0, b"the-secret-preimage");
open_vault(&mut cell, &terms)?;
let released = claim(&mut cell, &terms, &Claim::on_proof(beneficiary, 0, b"the-secret-preimage"))?;
```

### The forges are genuinely rejected

Every forge detector shares the `check_claim` core with the honest path, and is
proven RED-on-break by **mutation**: stubbing `check_claim` to always-accept (bypass
the one-shot, early-release, and hashlock gates) turns the early-release,
forged-proof, and double-claim tests RED — and also the honest-height test, whose
"not yet claimable before release" assertion the never-rejecting stub violates —
while the forged-lock and wrong-beneficiary tests (gated *above* the stub) and the
honest-proof path stay GREEN. **Observed under mutation: 4 failed, 8 passed.**
Reverting the stub restores the **12 conditional-vault tests** green.

| forge                                                  | rejection            |
|--------------------------------------------------------|----------------------|
| **early claim** (height not reached, no proof)         | `HeightNotReached`   |
| **forged condition-proof** (wrong preimage)            | `ProofMismatch`      |
| **double-claim / replay** of a settled vault           | `AlreadySettled` (one-shot) |
| **forged lock** (tampered amount / swapped condition)  | `TermsMismatch` (condition folded into the digest) |
| claim by a **non-beneficiary**                         | `WrongBeneficiary`   |
| **ill-formed** terms (non-positive amount / negative height) | `IllFormedTerms` |

The honest height claim after release ACCEPTS, releases the locked value, and marks
the vault settled; the honest hashlock claim with the genuine preimage ACCEPTS; and
the vault state is bound into the canonical commitment (opening locks it, claiming
re-seals it — a light client sees the vault settle), so a forge cannot be hidden.

Tests: `cargo test -p dregg-cell --lib vault::` — **19 green** (the 12
conditional-timelock tests documented here, plus 7 for the share-vault capacity
that now shares this module — see the note below).

> **Note — `cell/src/vault.rs` also hosts a second, distinct capacity.** Below the
> conditional-timelock vault (line 544+) lives the **share vault**, an ERC-4626-style
> pool whose share-price is *proven* immune to the first-depositor inflation attack
> (`ShareVaultState::shares_for_deposit`, `deposit_never_dilutes_existing_holders`).
> That capacity has its OWN Lean rungs — `metatheory/Dregg2/Deos/Vault.lean` (the
> share-price relation + no-dilution) and `metatheory/Dregg2/Deos/VaultSatDescriptor.lean`
> (the tag-19 vault-DEPOSIT in-AIR gate, staged). It is a *separate* house capacity
> from the conditional-release vault this doc describes; the §5 circuit rung below is
> the conditional-**release** vault's open follow-up, not the share vault's.

---

## 5. Next slice: circuit binding

The checks in §3–4 are **executor-level** — genuine forge rejections a verifier
runs in the clear. The remaining slice is the **in-circuit witness**, so that a
light client verifying a *batch* sees release-conditionality enforced by the
EffectVM circuit (part of the proven kernel transition) rather than re-running the
check out of band:

1. A `ClaimVault` effect descriptor whose **gate binds** *"the committed condition
   is genuinely met (`at_block >= release_height` ∨ `H(witness) == condition_digest`)
   ∧ the vault is not-yet-settled ⟹ the vault is settled (`settled' == 1`) ∧ the
   committed `amount` is released to the beneficiary"* into the commitment — the same
   shape as the value/note gates already in `circuit/descriptors/`. The gate must
   bind the condition-satisfaction predicate, the one-shot settle transition, and the
   amount release into the commitment, else the rung is FALSE (the standing
   circuit-soundness apex bar). This is the one-shot nullifier shape the noteSpend
   grow-gate already carries, specialized to the conditional-release predicate.

2. The committed lock fields (the terms digest, the `amount`, the `settled` flag)
   and the hashlock target as **heap-opening witnesses** (each opened against the
   vault cell's `heap_root`, the cell's commitment proven in the ledger root). For an
   `OnProof` vault the preimage is a private witness; only `H(witness)` and its
   equality to the committed digest are in the public statement.

3. A Lean rung: `verifyBatch accept ⟹ vault released only when its condition was
   genuinely met` — concretely, a batch containing a vault claim implies that the
   released value moved only if `at_block >= release_height` (for `AtHeight`) or the
   private witness hashed to the committed digest (for `OnProof`), the vault was
   unsettled before the claim, and the vault is settled exactly once after —
   joining the circuit-soundness obligation table (the grounded circuit what-is now
   lives at `docs/reference/lean-circuit.md`).

Until that lands, conditional vaults are sound under the executor checks and the
commitment binding; the circuit rung is the named follow-up, not a silent gap.
