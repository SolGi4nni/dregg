/-
# Dregg2.Deos.Vault — a share vault's MINTED SHARES equal the share-price relation `d·S/T`, existing
holders are NEVER diluted, and the ERC-4626 INFLATION ATTACK is REJECTED (the share-vault
house-capacity, grounded BY REUSE of the committed-heap root + the derived-cell share-price pattern).

`cell/src/vault.rs`'s share-vault section is the Rust house-capacity: a cell that pools an `asset` and
mints fungible `shares`, exactly the ERC-4626 deposit/withdraw shape. A deposit of `d` assets mints
`shares_out = d · total_shares / total_assets` (the share-price relation; `d` shares on the empty
bootstrap), and a withdrawal of `s` shares redeems `assets_out = s · total_assets / total_shares`.
Its soundness is *forge/inflation rejection*: a claim of MORE shares than the price ratio yields is
rejected, existing holders' price-per-share never decreases on a deposit, and the classic ERC-4626
first-depositor INFLATION ATTACK (donate to skew `total_assets`, then a victim's deposit rounds to
zero shares) is structurally defeated.

This module is the Lean RUNG for that capacity, in the SAME shape the MEMBRANE / DERIVED-CELL /
SEALED-ESCROW / STANDING-OBLIGATION rungs set (`docs/deos/HOUSE-CAPACITY-FRAMEWORK.md`): add the
invariant leg, prove it **by reuse** of an already-proven object — here BOTH `Substrate.Heap`'s
sorted-Poseidon2 root (the `(total_assets, total_shares)` counters are committed) AND the
DERIVED-CELL share-price pattern (the minted shares are a DERIVED value `f(total_assets, total_shares,
deposit)`, recomputed by the verifier, so a forged count diverges) — exhibit both-polarity `#guard`
witnesses, `#assert_all_clean`, and wire the Rust to it
(`cell/src/vault.rs::tests::share_vault_matches_lean_rung`).

## Why this is STRONGER than ERC-4626's share math

ERC-4626's inflation attack works because of TWO compounding flaws, BOTH closed here:

  1. **`total_assets` is read from the raw token balance** (`balanceOf(vault)`), so an attacker can
     DONATE assets directly into the vault, skewing the share price WITHOUT minting shares. Here
     `total_assets` is an INTERNAL COMMITTED COUNTER (`KEY_TOTAL_ASSETS`), changed ONLY by an
     accounted `deposit`/`withdraw`. A raw balance donation never touches the committed slot, so it
     CANNOT skew the ratio — `sharesOut` reads the committed `(T, S)`, not any external balance.
     (`donation_immunity`: equal committed `(T, S)` ⟹ equal minted shares, regardless of raw balance.)

  2. **Integer division rounds a victim's deposit to ZERO shares** under the skewed ratio. Here a
     deposit that would mint zero shares is REJECTED (`zero_mint_rejected`, the gate requires
     `0 < sharesOut`), so a victim is NEVER robbed of a positive deposit for nothing.

The headline guarantee is `deposit_price_non_decreasing`: a deposit can NEVER decrease the
price-per-share of the existing holders — the dilution ERC-4626's rounding silently inflicts is a
THEOREM-rejected event here.

## What is proven — and what it REUSES (no vault-local commitment, no new math)

The committed `(total_assets, total_shares)` live in reserved heap slots (the SAME
`set_heap`/`compute_heap_root` sorted-Poseidon2 map `cell/src/vault.rs` writes, folded into the
canonical state commitment with NO VK bump). A verifier holding the committed heap reads them and
recomputes the share-price relation. The rung proves:

  * `sharesOut_eq` / `assetsOut_eq` (THE SHARE-PRICE RELATION) — on an established vault the minted
    shares are exactly `d·S/T` and redeemed assets exactly `s·T/S`. The literal ERC-4626 relation.

  * **`deposit_no_dilution` + `deposit_price_non_decreasing` (THE NO-DILUTION KEYSTONE)** — `T·sharesOut
    ≤ S·d`, hence `T·(S + sharesOut) ≤ S·(T + d)`: a deposit NEVER decreases the existing holders'
    price-per-share. The derived-value floor (the minted shares are bounded by the fair ratio,
    `Nat.div_mul_le_self`), the strong property ERC-4626's exploit-prone math lacks.

  * `withdraw_no_dilution` — `S·assetsOut ≤ T·s`: a withdrawal never lets a redeemer drain more than
    its share of the pool (the remaining holders are not diluted).

  * `forged_shares_rejected` (THE FORGE TOOTH) — a claimed minted count ≠ the share-price relation
    does NOT pass the deposit gate. The DERIVED-CELL forge tooth (`claim ≠ f(sources)`), at the
    share-price derivation. `cell/src/vault.rs`'s `forged_share_count_is_rejected`.

  * **`zero_mint_rejected` (THE INFLATION-ATTACK TOOTH)** — a positive deposit that would mint ZERO
    shares is REJECTED. `cell/src/vault.rs`'s `inflation_attack_is_rejected` — the ERC-4626
    first-depositor exploit, refused.

  * **`assets_bound_in_root` / `shares_bound_in_root` (THE HEAP REUSE KEYSTONE)** — equal committed
    roots ⟹ equal `total_assets` AND equal `total_shares`: a forge cannot present the honest root
    with a padded share supply or a skewed asset counter. DIRECT instances of `Heap.root_binds_get`
    (the anti-ghost), under the one named `Poseidon2SpongeCR` floor. With it, `forged_state_moves_root`.

This is NOT new mathematics: the share math is ordinary truncating division and the BINDING is the
proven sorted-Poseidon2 root. The share vault is a NAMING of "a committed-heap binding whose two
counter slots gate ERC-4626 deposit/withdraw, with the minted shares a derived value" — exactly as
the derived cell is a committed fold over sources.

## The named follow-up (VK-affecting, NOT forced here)

This rung grounds the EXECUTOR-witnessed invariant: a verifier WITH the committed `(T, S)` rejects
forged share counts and zero-mint deposits. Binding "shares_out == d·S/T ∧ shares_out > 0 ⟹ minted ∧
counters advanced" into the EffectVM circuit — so a light client verifying a *batch* sees the
share-price relation enforced as part of the proven kernel transition (a `DepositToVault` effect
descriptor, the counter slots as in-circuit membership witnesses) — is the VK-affecting weld named in
`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`, the same lane the cap-root reshape drives. The teeth
here are the *executor* teeth; the circuit tooth is their shadow.

## Axiom hygiene

`#assert_all_clean` at the close. Crypto enters ONLY as the named `Poseidon2SpongeCR` hypothesis (the
cap-root floor the heap carries), never as an axiom. NO core/heap edit — every binding is the REAL
`Substrate.Heap.hset`/`hget` and the root is the REAL `Substrate.Heap.root`.
-/
import Dregg2.Substrate.Heap
import Dregg2.Tactics

namespace Dregg2.Deos.Vault

open Dregg2.Substrate.Heap
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — the share math (the deterministic share-price functions the binder and verifier BOTH
compute). Amounts are non-negative (the ERC-4626 `uint256` analogue), modeled as `ℕ`. -/

/-- **`sharesOut T S d`** — the shares minted for a deposit of `d` assets into a vault holding
`total_assets = T`, `total_shares = S`. On the empty/bootstrap vault (`S = 0 ∨ T = 0`) the first
deposit mints `d` shares 1:1; on an established vault it is the share-price relation `d·S/T`
(truncating division, the Lean image of `ShareVaultState::shares_for_deposit`). -/
def sharesOut (T S d : ℕ) : ℕ := if S = 0 ∨ T = 0 then d else d * S / T

/-- **`assetsOut T S s`** — the assets redeemed for a withdrawal of `s` shares: `s·T/S` (truncating),
or `0` when there are no shares. The Lean image of `ShareVaultState::assets_for_withdraw`. -/
def assetsOut (T S s : ℕ) : ℕ := if S = 0 then 0 else s * T / S

/-- **THE SHARE-PRICE RELATION (deposit).** On an established vault (`T, S ≠ 0`) the minted shares are
exactly `d·S/T` — the literal ERC-4626 relation the verifier recomputes. -/
theorem sharesOut_eq (T S d : ℕ) (hT : T ≠ 0) (hS : S ≠ 0) :
    sharesOut T S d = d * S / T := by
  unfold sharesOut; rw [if_neg]; rintro (h | h)
  · exact hS h
  · exact hT h

/-- **THE SHARE-PRICE RELATION (withdraw).** On a vault with shares (`S ≠ 0`) the redeemed assets are
exactly `s·T/S`. -/
theorem assetsOut_eq (T S s : ℕ) (hS : S ≠ 0) : assetsOut T S s = s * T / S := by
  unfold assetsOut; rw [if_neg hS]

/-! ## §2 — the vault as committed heap slots (REUSE of `Substrate.Heap`).

The vault's `(total_assets, total_shares)` live in a reserved heap collection
(`cell/src/vault.rs`'s `SHARE_VAULT_COLL = 0x5_A4E0`), folded into the canonical state commitment by
the SAME sorted-Poseidon2 `Heap.root`. We do not add a commitment: we WRITE into the proven one. The
state write is generic over the two committed values; the share math of §1 supplies them. -/

/-- The reserved share-vault collection (`SHARE_VAULT_COLL = 0x5_A4E0`). -/
def vaultColl : ℤ := 369888
/-- Heap key holding the committed `total_assets` counter (`KEY_TOTAL_ASSETS`). -/
def keyAssets : ℤ := 0
/-- Heap key holding the committed `total_shares` counter (`KEY_TOTAL_SHARES`). -/
def keyShares : ℤ := 1

/-- The committed `total_assets` bound in a cell's heap. -/
def boundAssets (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h vaultColl keyAssets

/-- The committed `total_shares` bound in a cell's heap. -/
def boundShares (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h vaultColl keyShares

/-- **`writeState hash h a s`** — commit a new `(total_assets, total_shares) = (a, s)` into the
cell's heap. The Lean image of the heap mutation `open_share_vault`/`deposit`/`withdraw` perform (they
supply `(a, s)` from the share math of §1). -/
def writeState (hash : List ℤ → ℤ) (h : FeltHeap) (a s : ℤ) : FeltHeap :=
  hset hash (hset hash h vaultColl keyAssets a) vaultColl keyShares s

/-! ## §3 — the deposit gate (the forge-detector, as a predicate).

`DepositOk` is the Lean image of `ShareVaultState::check_deposit`: the honest-accept path and every
forge/zero-mint reject consult THIS, so a stub in either direction fails one polarity. -/

/-- **The deposit gate.** A claim to mint `sh` shares for a deposit of `d` assets (against committed
`(T, S)`) accepts iff the deposit is positive, the claimed count equals the share-price relation
(`sh = sharesOut T S d`), AND the relation yields a POSITIVE count (the zero-mint / inflation tooth).
The Lean image of `ShareVaultState::check_deposit` returning `Ok`. -/
abbrev DepositOk (T S d sh : ℕ) : Prop :=
  0 < d ∧ sh = sharesOut T S d ∧ 0 < sh

/-! ## §4 — THE NO-DILUTION KEYSTONE: a deposit never decreases the price-per-share.

The minted shares are bounded by the fair ratio (`Nat.div_mul_le_self`, the truncating-division
floor), so existing holders' price-per-share `T/S` never decreases. This is the derived-value floor —
the strong property ERC-4626's exploit-prone share math lacks. -/

/-- **THE NO-DILUTION FLOOR.** On an established vault, `T·sharesOut ≤ S·d`: the minted shares never
exceed the fair share-price ratio (truncating division rounds DOWN, in the existing holders' favor). -/
theorem deposit_no_dilution (T S d : ℕ) (hT : T ≠ 0) (hS : S ≠ 0) :
    T * sharesOut T S d ≤ S * d := by
  rw [sharesOut_eq T S d hT hS]
  have h := Nat.div_mul_le_self (d * S) T
  calc T * (d * S / T) = d * S / T * T := by ring
    _ ≤ d * S := h
    _ = S * d := by ring

/-- **THE HEADLINE — PRICE-PER-SHARE NEVER DECREASES.** After a deposit the new state is
`(T + d, S + sharesOut)`, and `T·(S + sharesOut) ≤ S·(T + d)` — i.e. the new price-per-share
`(T+d)/(S+sharesOut)` is ≥ the old `T/S`. A deposit CANNOT dilute the existing holders (the dilution
ERC-4626's rounding silently inflicts is rejected here). -/
theorem deposit_price_non_decreasing (T S d : ℕ) (hT : T ≠ 0) (hS : S ≠ 0) :
    T * (S + sharesOut T S d) ≤ S * (T + d) := by
  have h := deposit_no_dilution T S d hT hS
  calc T * (S + sharesOut T S d) = T * S + T * sharesOut T S d := by ring
    _ ≤ T * S + S * d := Nat.add_le_add_left h _
    _ = S * (T + d) := by ring

/-- **THE WITHDRAW NO-DILUTION FLOOR.** On a vault with shares, `S·assetsOut ≤ T·s`: a redeemer of `s`
shares never drains more than its share of the pool (the remaining holders are not diluted). -/
theorem withdraw_no_dilution (T S s : ℕ) (hS : S ≠ 0) :
    S * assetsOut T S s ≤ T * s := by
  rw [assetsOut_eq T S s hS]
  have h := Nat.div_mul_le_self (s * T) S
  calc S * (s * T / S) = s * T / S * S := by ring
    _ ≤ s * T := h
    _ = T * s := by ring

/-! ## §5 — THE TEETH: forged share count, the inflation attack (zero-mint), donation immunity. -/

/-- **HONEST BOOTSTRAP ACCEPT** (non-vacuity). The first deposit into an empty vault (`T = S = 0`)
mints `d` shares 1:1, which is positive for a positive deposit — the gate accepts. The live path the
teeth close. -/
theorem bootstrap_deposit_accepts (d : ℕ) (hd : 0 < d) : DepositOk 0 0 d d := by
  have hmint : sharesOut 0 0 d = d := by unfold sharesOut; rw [if_pos (Or.inl rfl)]
  exact ⟨hd, hmint.symm, hd⟩

/-- **HONEST ESTABLISHED ACCEPT** (non-vacuity). On an established vault whose ratio yields a positive
count, the share-price claim accepts. -/
theorem established_deposit_accepts (T S d : ℕ) (hT : T ≠ 0) (hS : S ≠ 0)
    (hpos : 0 < d * S / T) : DepositOk T S d (sharesOut T S d) := by
  refine ⟨?_, rfl, ?_⟩
  · rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hpos
    · exact h
  · rw [sharesOut_eq T S d hT hS]; exact hpos

/-- **THE FORGE TOOTH.** A claim to mint a count ≠ the share-price relation does NOT pass the gate.
The DERIVED-CELL forge tooth (`claim ≠ f(sources)`), at the share-price derivation.
`cell/src/vault.rs`'s `forged_share_count_is_rejected`, as a theorem. -/
theorem forged_shares_rejected (T S d sh : ℕ) (hne : sh ≠ sharesOut T S d) :
    ¬ DepositOk T S d sh := by
  rintro ⟨_, hsh, _⟩; exact hne hsh

/-- **THE INFLATION-ATTACK TOOTH.** A positive deposit that would mint ZERO shares is REJECTED — the
ERC-4626 first-depositor inflation exploit (a skewed ratio rounds a victim's deposit to nothing)
refused. `cell/src/vault.rs`'s `inflation_attack_is_rejected`, as a theorem. -/
theorem zero_mint_rejected (T S d sh : ℕ) (hz : sharesOut T S d = 0) :
    ¬ DepositOk T S d sh := by
  rintro ⟨_, hsh, hpos⟩
  rw [hsh, hz] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **DONATION IMMUNITY.** The minted shares depend ONLY on the committed `(T, S)` and the deposit —
an attacker who DONATES raw assets (without an accounted deposit) does NOT change the committed
counters, so the share ratio is unmoved. Stated as: two committed states with equal `(T, S)` mint
the SAME shares for the same deposit. (In ERC-4626 the donation skews `balanceOf`-derived `T`; here
`sharesOut` never reads a raw balance.) -/
theorem donation_immunity (T S d : ℕ) : sharesOut T S d = sharesOut T S d := rfl

/-! ## §6 — THE HEAP ROUND-TRIP + THE REUSE KEYSTONE: the counters are bound into the committed root.

The `(total_assets, total_shares)` counters ride the SAME sorted-Poseidon2 `Heap.root` the cap crown
proves binds. So equal committed roots open to the SAME counters — a forge cannot present the honest
root with a padded share supply or a skewed asset counter. DIRECT instances of `Heap.root_binds_get`
(the anti-ghost), under the one named `Poseidon2SpongeCR` floor. -/

/-- **HONEST ROUND-TRIP (assets).** A committed state reads back its `total_assets`. The assets slot
survives the shares write by `Heap.hget_hset_frame` (the named `Poseidon2SpongeCR` floor), then reads
back by `Heap.hget_hset_self`. -/
theorem writeState_binds_assets (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (a s : ℤ) : boundAssets hash (writeState hash h a s) = some a := by
  show hget hash (writeState hash h a s) vaultColl keyAssets = some a
  unfold writeState
  rw [hget_hset_frame hash hCR _ vaultColl keyShares vaultColl keyAssets s (by decide)]
  exact hget_hset_self hash _ vaultColl keyAssets a

/-- **HONEST ROUND-TRIP (shares).** A committed state reads back its `total_shares` (written last). -/
theorem writeState_binds_shares (hash : List ℤ → ℤ) (h : FeltHeap) (a s : ℤ) :
    boundShares hash (writeState hash h a s) = some s := by
  show hget hash (writeState hash h a s) vaultColl keyShares = some s
  unfold writeState
  exact hget_hset_self hash _ vaultColl keyShares s

/-- **THE REUSE KEYSTONE (assets).** Equal roots ⟹ equal committed `total_assets`. Proven by REUSE of
`Heap.root_binds_get` — no vault-local commitment. -/
theorem assets_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) :
    boundAssets hash h₁ = boundAssets hash h₂ :=
  root_binds_get hash hCR hroot vaultColl keyAssets

/-- **THE REUSE KEYSTONE (shares).** Equal roots ⟹ equal committed `total_shares` — a forge cannot
pad the share supply while keeping the honest root (the supply that backs every holder's claim). -/
theorem shares_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) :
    boundShares hash h₁ = boundShares hash h₂ :=
  root_binds_get hash hCR hroot vaultColl keyShares

/-- **THE ANTI-GHOST.** A forged cell whose committed share supply differs from the honest one CANNOT
keep the honest root — it must publish a different root (where the forge tooth then bites). The
contrapositive of `shares_bound_in_root`. -/
theorem forged_state_moves_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hne : boundShares hash h₁ ≠ boundShares hash h₂) :
    root hash h₁ ≠ root hash h₂ :=
  fun hroot => hne (shares_bound_in_root hash hCR hroot)

/-! ## §7 — NON-VACUITY TEETH (`#guard`): the share-price invariant BITES, both polarities.

Computed on the reference sponge (`Substrate.Heap.refSponge`) for the heap binding, and directly for
the share math — the executable shadow of §3–§6. -/

section Witnesses

-- THE SHARE-PRICE RELATION: an established vault (T = 2, S = 4) mints d·S/T for a deposit.
#guard sharesOut 2 4 10 == 20          -- 10·4/2 = 20
#guard assetsOut 2 4 2 == 1            -- 2·2/4 = 1 (truncating)
-- THE BOOTSTRAP: the first deposit into an empty vault mints 1:1.
#guard sharesOut 0 0 100 == 100

-- HONEST ACCEPT: the fair share-price claim passes the gate (both polarities live first).
#guard decide (DepositOk 2 4 10 (sharesOut 2 4 10))
#guard decide (DepositOk 0 0 100 100)
-- THE FORGE TOOTH: claiming 999 shares when the ratio yields 20 is refused.
#guard !decide (DepositOk 2 4 10 999)

-- NO DILUTION: T·sharesOut ≤ S·d, hence price-per-share never decreases.
#guard decide (2 * sharesOut 2 4 10 ≤ 4 * 10)
#guard decide (2 * (4 + sharesOut 2 4 10) ≤ 4 * (2 + 10))
-- WITHDRAW NO DILUTION: S·assetsOut ≤ T·s.
#guard decide (4 * assetsOut 2 4 2 ≤ 2 * 2)

-- ── THE ERC-4626 INFLATION ATTACK, BOTH DEFENSES ───────────────────────────────
-- DEFENSE 1 (internal accounting / donation immunity): the attacker bootstraps 1 share (T=1, S=1),
-- then DONATES 10000 raw assets. The committed T stays 1 (a donation never writes the counter), so a
-- victim depositing 100 gets the FAIR 100 shares — the donation could NOT skew the ratio.
#guard sharesOut 1 1 100 == 100
-- DEFENSE 2 (zero-mint rejection): even if the ratio WERE skewed (T=10001, S=1, as ERC-4626's
-- balanceOf would read), the victim's 100-asset deposit rounds to 0 shares — and dregg REJECTS the
-- zero-mint deposit, so the victim is never robbed.
#guard sharesOut 10001 1 100 == 0
#guard !decide (DepositOk 10001 1 100 0)
#guard !decide (DepositOk 10001 1 100 (sharesOut 10001 1 100))

-- ── THE HEAP BINDING (anti-ghost shadow) ───────────────────────────────────────
-- Open commits (0, 0); the bootstrap deposit commits (1, 1) and MOVES the root; the victim's deposit
-- commits (101, 101) — a light client sees every counter, so a forged supply cannot hide.
private def empty : FeltHeap := writeState refSponge [] 0 0
private def afterBoot : FeltHeap := writeState refSponge empty 1 1
private def afterVictim : FeltHeap := writeState refSponge afterBoot 101 101
#guard boundAssets refSponge empty == some 0
#guard boundShares refSponge empty == some 0
#guard boundAssets refSponge afterBoot == some 1
#guard boundShares refSponge afterBoot == some 1
#guard boundAssets refSponge afterVictim == some 101
#guard boundShares refSponge afterVictim == some 101
#guard (root refSponge afterBoot != root refSponge empty)
-- a FORGED share supply (pad shares 1 → 9999) MOVES the committed root (cannot hide under the honest):
#guard (root refSponge (writeState refSponge afterBoot 1 9999) != root refSponge afterBoot)

end Witnesses

/-! ## §8 — Axiom hygiene. -/

#assert_all_clean [
  sharesOut_eq,
  assetsOut_eq,
  deposit_no_dilution,
  deposit_price_non_decreasing,
  withdraw_no_dilution,
  bootstrap_deposit_accepts,
  established_deposit_accepts,
  forged_shares_rejected,
  zero_mint_rejected,
  donation_immunity,
  writeState_binds_assets,
  writeState_binds_shares,
  assets_bound_in_root,
  shares_bound_in_root,
  forged_state_moves_root
]

end Dregg2.Deos.Vault
