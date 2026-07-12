/-
# Dregg2.Bridge.LightClientMpt — EVM state-inclusion (EIP-1186) verification RULES, PROVEN.

The per-chain lane for **EVM state inclusion**: the rules by which a light client, holding a
finality-verified execution `state_root`, checks an `eth_getProof` (EIP-1186) proof chain that
a holder holds `balance` of an ERC-20 `token` — formalized in Lean over
`Dregg2.Bridge.VerifiedLightClient`, with the three obligations (`NoForgery` / `FailClosed` /
`NonVacuous`) DISCHARGED, plus the binding theorem the Merkle-Patricia structure exists to
provide: under one state root, one holder has ONE provable balance (`mpt_balance_binding`) —
forging a second balance is a keccak collision.

THE RULES FORMALIZED (the Rust spec is `eth-lightclient/src/evm.rs`, `verify_erc20_holding`):

  1. **Account (state) trie** (`evm.rs:158-180`): `state_root --MPT--> keccak256(token) →
     account(nonce, balance, storageHash, codeHash)`. The account leaf binds ALL FOUR fields at
     once — in particular `storageHash`, the root of the contract's own storage trie.
  2. **Storage trie** (`evm.rs:182-197`): `storageHash --MPT--> keccak256(slot_key) →
     balance`, where `slot_key = keccak256(pad32(holder) ‖ pad32(balances_slot))`
     (`erc20_balance_slot_key`, `evm.rs:117-124`) — the Solidity `mapping(address ⇒ uint256)`
     slot for `balances[holder]`.
  3. **Nomad-law floor** (`evm.rs:154-156`): a zero claimed balance is REFUSED even when its
     proof verifies — a trivial/empty holding never mints a proven holding.

TWO LAYERS, kept honest:

  * RULES (this file, proven): the two-tier path walk, the hash-derived keys, the account→
    storageHash binding, the exact-value check, the zero floor, fail-closed on everything else.
  * CRYPTO (ONE leaf): **keccak256 collision resistance** — `hashCR : hash m₁ = hash m₂ →
    m₁ = m₂`, the foundation's `CryptoLeaf.hashCR` field. There is NO signature in this client
    (the `state_root`'s finality is the UPSTREAM sync-committee client's job; this lane's
    `CryptoLeaf.sigVerify` is the constant-`false` verifier, so its `sigSound` is vacuously
    proven and carries nothing). Every general theorem below takes the hash `H` and (where
    binding is needed) the CR fact `hCR` as EXPLICIT hypotheses — the assumption is visible at
    every use site, never a global axiom, never a laundered `def`. The shipped instance plugs
    `toyKeccak` (an injective model hash, injectivity PROVEN) so this file is genuinely
    axiom-clean; a production instance swaps in EverCrypt-realized keccak256 with `hashCR` as
    its single named library assumption, and ALL the theorems here apply unchanged.

MODELING FIDELITY (stated, not hidden): bytes are `Nat`s and byte-strings `List Nat`; the RLP
node/account encodings are modeled by `encodeNode`/`encAccount`, whose INJECTIVITY — RLP's
canonical-decodability, a rules-level fact — is PROVEN here (`encodeNode_injective`,
`encAccount_injective`), not assumed. The nibble path is a fixed 4-nibble unpack of the key
digest (`nibbles`) standing in for the 64-nibble `Nibbles::unpack(keccak256(·))`; MPT extension
nodes (pure path compression) are absorbed into leaf `keySuffix`. None of these shortenings
touches the load-bearing structure: hash-linked path steps, hash-derived keys, two-tier
storageHash binding, exact terminal value.

NON-VACUITY (the Nomad-law tooth, all under the SAME trusted state): the gate ACCEPTS the
genuine holding and REJECTS a forged balance, a tampered storage node, a wrong contract, a
foreign-path account proof, and an absent key (`mpt_gate_discriminates`); a ZERO holding whose
MPT proof genuinely verifies is still refused (`mpt_zero_balance_refused` — the floor does its
own work); the empty update is rejected for every trusted state (`mpt_failClosed`).

Kernel-clean: `#assert_axioms` hard-gates every theorem (only `propext`/`Classical.choice`/
`Quot.sound`).
-/
import Metatheory.Bridge.InterchainAdapter
import Dregg2.Bridge.VerifiedLightClient
import Mathlib.Data.Nat.Pairing
import Dregg2.Tactics

namespace Dregg2.Bridge.LightClientMpt

open Dregg2.Bridge.VerifiedLightClient

/-! ## §1 — The Merkle-Patricia trie model: nodes, injective encoding, path walk.

A node is a LEAF (remaining key nibbles + terminal value) or a BRANCH (children digests
indexed by nibble; `none` = absent child — the exclusion side). `encodeNode` models the RLP
node encoding; its injectivity is the canonical-decodability fact RLP provides, PROVEN here so
the only crypto assumption left is keccak collision resistance. -/

/-- An MPT node: `leaf keySuffix value` (terminal; extension nodes are absorbed as compressed
suffix) or `branch children` (per-nibble child digests; `none` = no child at that nibble). -/
inductive MptNode where
  | leaf (keySuffix : List Nat) (value : List Nat)
  | branch (children : List (Option Nat))
deriving DecidableEq, Repr

/-- Child-digest encoding for branch bodies: `none ↦ 0`, `some d ↦ d+1`. Injective. -/
def encOpt : Option Nat → Nat
  | none => 0
  | some d => d + 1

theorem encOpt_injective : ∀ {o₁ o₂ : Option Nat}, encOpt o₁ = encOpt o₂ → o₁ = o₂ := by
  intro o₁ o₂ h
  cases o₁ <;> cases o₂ <;> simp [encOpt] at h <;> simp [h]

theorem map_encOpt_injective :
    ∀ {cs₁ cs₂ : List (Option Nat)}, cs₁.map encOpt = cs₂.map encOpt → cs₁ = cs₂ := by
  intro cs₁
  induction cs₁ with
  | nil => intro cs₂ h; cases cs₂ with
    | nil => rfl
    | cons b t => simp at h
  | cons a t ih => intro cs₂ h; cases cs₂ with
    | nil => simp at h
    | cons b t' =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [encOpt_injective h.1, ih h.2]

/-- **The model RLP node encoding** (tag ‖ length-disambiguated body). What keccak256 is
applied to; `encodeNode_injective` below is RLP's canonical-decodability, proven. -/
def encodeNode : MptNode → List Nat
  | .leaf k v => 0 :: k.length :: (k ++ v)
  | .branch cs => 1 :: cs.map encOpt

/-- **Encoding injectivity (rules-level, PROVEN — not part of the crypto leaf).** Two nodes
with the same encoding are the same node; with `hashCR` this pins hash-equal nodes equal. -/
theorem encodeNode_injective : ∀ {n₁ n₂ : MptNode}, encodeNode n₁ = encodeNode n₂ → n₁ = n₂ := by
  intro n₁ n₂ h
  cases n₁ with
  | leaf k₁ v₁ => cases n₂ with
    | leaf k₂ v₂ =>
      simp only [encodeNode, List.cons.injEq] at h
      obtain ⟨_, hlen, happ⟩ := h
      obtain ⟨hk, hv⟩ := List.append_inj happ hlen
      rw [hk, hv]
    | branch cs => simp [encodeNode] at h
  | branch cs₁ => cases n₂ with
    | leaf k₂ v₂ => simp [encodeNode] at h
    | branch cs₂ =>
      simp only [encodeNode, List.cons.injEq, true_and] at h
      rw [map_encOpt_injective h]

/-- Branch child lookup: the digest at nibble `i`, `none` if out of range or absent. -/
def childAt (cs : List (Option Nat)) (i : Nat) : Option Nat :=
  match cs[i]? with
  | some (some d) => some d
  | _ => none

/-- **The Prop-level trie DENOTATION** — what "value `v` is genuinely committed at path `p`
under digest `d`" MEANS, independent of any supplied proof: there is a hash-linked node
structure from `d` down to a leaf carrying exactly `v` with exactly the remaining path. This
is the `ForeignValid` backbone; `NoForgery` lands accepted updates HERE. -/
inductive Commits (H : List Nat → Nat) : Nat → List Nat → List Nat → Prop where
  | leaf (k v : List Nat) : Commits H (H (encodeNode (.leaf k v))) k v
  | branch (cs : List (Option Nat)) (i d : Nat) (rest v : List Nat)
      (hc : childAt cs i = some d) (child : Commits H d rest v) :
      Commits H (H (encodeNode (.branch cs))) (i :: rest) v

/-- **THE EXECUTABLE PATH WALK** — the MPT verification rules (`alloy_trie::verify_proof`'s
job in `evm.rs:174/191`): walk the supplied nodes root-down; each node must hash to the digest
its parent (or the root) committed; a branch consumes one nibble through a PRESENT child; a
leaf must carry exactly the remaining path and exactly the expected value, with no trailing
proof junk. Everything else: `false`. -/
def verifyPath (H : List Nat → Nat) : Nat → List Nat → List Nat → List MptNode → Bool
  | _, _, _, [] => false
  | root, path, value, .leaf k v :: rest =>
      rest.isEmpty && (H (encodeNode (.leaf k v)) == root) && (k == path) && (v == value)
  | root, i :: p, value, .branch cs :: rest =>
      (H (encodeNode (.branch cs)) == root) &&
      (match childAt cs i with
       | some d => verifyPath H d p value rest
       | none => false)
  | _, [], _, .branch _ :: _ => false

/-- **Path-walk SOUNDNESS.** An accepted walk lands in the denotation: the value is genuinely
committed under the root. (No crypto needed — each check literally establishes its hash link;
CR is what makes the denotation BINDING, below.) -/
theorem verifyPath_sound (H : List Nat → Nat) :
    ∀ (nodes : List MptNode) (root : Nat) (path value : List Nat),
      verifyPath H root path value nodes = true → Commits H root path value := by
  intro nodes
  induction nodes with
  | nil => intro root path value h; simp [verifyPath] at h
  | cons n rest ih =>
    intro root path value h
    cases n with
    | leaf k v =>
      simp only [verifyPath, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨-, hroot⟩, hk⟩, hv⟩ := h
      subst hroot; subst hk; subst hv
      exact Commits.leaf k v
    | branch cs =>
      cases path with
      | nil => simp [verifyPath] at h
      | cons i p =>
        simp only [verifyPath, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hroot, hstep⟩ := h
        subst hroot
        cases hd : childAt cs i with
        | none => rw [hd] at hstep; simp at hstep
        | some d =>
          rw [hd] at hstep
          exact Commits.branch cs i d p value hd (ih d p value hstep)

/-! ## §2 — THE BINDING THEOREM (where keccak collision resistance is LOAD-BEARING).

Soundness says an accepted value is committed; BINDING says the root commits at most ONE value
per path — so a tampered node presenting a different value at the same slot requires a hash
collision. `hCR` is consumed at every level of the induction. This is the theorem the Merkle
structure exists to provide. -/

/-- **`commits_binding`** — one digest, one path, ONE value. The proof walks both derivations
together: equal digests + `hCR` ⇒ equal encodings ⇒ (`encodeNode_injective`) equal nodes ⇒
recurse into the equal child. Forging a second value at a committed slot IS a keccak collision. -/
theorem commits_binding (H : List Nat → Nat)
    (hCR : ∀ m₁ m₂, H m₁ = H m₂ → m₁ = m₂)
    {r₁ p₁ v₁} (h₁ : Commits H r₁ p₁ v₁) :
    ∀ {r₂ p₂ v₂}, Commits H r₂ p₂ v₂ → r₁ = r₂ → p₁ = p₂ → v₁ = v₂ := by
  induction h₁ with
  | leaf k v =>
    intro r₂ p₂ v₂ h₂ hr hp
    cases h₂ with
    | leaf k' v' =>
      have henc := encodeNode_injective (hCR _ _ hr)
      simp only [MptNode.leaf.injEq] at henc
      exact henc.2
    | branch cs' i' d' rest' v₂' hc' child' =>
      exact absurd (encodeNode_injective (hCR _ _ hr)) (by intro hcon; cases hcon)
  | branch cs i d rest v hc child ih =>
    intro r₂ p₂ v₂ h₂ hr hp
    cases h₂ with
    | leaf k' v' =>
      exact absurd (encodeNode_injective (hCR _ _ hr)) (by intro hcon; cases hcon)
    | branch cs' i' d' rest' v₂' hc' child' =>
      have henc := encodeNode_injective (hCR _ _ hr)
      simp only [MptNode.branch.injEq] at henc
      subst henc
      simp only [List.cons.injEq] at hp
      obtain ⟨hi, hrest⟩ := hp
      subst hi
      have hd : d = d' := Option.some.inj (hc.symm.trans hc')
      exact ih child' hd hrest

/-! ## §3 — The EVM (EIP-1186) rules over the trie model: keys, encodings, the two-tier gate. -/

/-- The token contract's claimed account fields — the four the RLP account leaf binds at once
(`evm.rs:66-72 AccountClaim`). `storageHash` is the root of the contract's storage trie. -/
structure AccountClaim where
  nonce : Nat
  balance : Nat
  storageHash : Nat
  codeHash : Nat
deriving DecidableEq, Repr

/-- The model RLP account encoding — the account-trie terminal VALUE
(`RLP([nonce, balance, storageHash, codeHash])`, `evm.rs:162-168`). Fixed arity ⇒ injective. -/
def encAccount (a : AccountClaim) : List Nat :=
  [a.nonce, a.balance, a.storageHash, a.codeHash]

theorem encAccount_injective {a₁ a₂ : AccountClaim}
    (h : encAccount a₁ = encAccount a₂) : a₁ = a₂ := by
  cases a₁; cases a₂; simp_all [encAccount]

/-- The storage-trie terminal value: the RLP of the uint256 balance (`evm.rs:186`). -/
def encBalance (b : Nat) : List Nat := [b]

theorem encBalance_injective {b₁ b₂ : Nat} (h : encBalance b₁ = encBalance b₂) : b₁ = b₂ := by
  simpa [encBalance] using h

/-- The Solidity mapping-slot preimage, `pad32(holder) ‖ pad32(balances_slot)`
(`erc20_balance_slot_key`, `evm.rs:117-124`): two fixed-width fields, modeled as the
fixed-arity list. -/
def slotKeyPreimage (holder mappingSlot : Nat) : List Nat := [holder, mappingSlot]

/-- The 4-nibble key unpack (models `Nibbles::unpack` of the 64-nibble key digest). -/
def nibbles (d : Nat) : List Nat := [d % 16, d / 16 % 16, d / 256 % 16, d / 4096 % 16]

/-- ACCOUNT-trie path: `Nibbles.unpack(keccak256(token))` (`evm.rs:169`). The account key is
DERIVED BY HASHING the contract address — a proof for another contract walks another path. -/
def accountPath (H : List Nat → Nat) (token : Nat) : List Nat := nibbles (H [token])

/-- STORAGE-trie path: `Nibbles.unpack(keccak256(slot_key))` with `slot_key =
keccak256(pad32(holder) ‖ pad32(slot))` (`evm.rs:184-185`) — the double hash, mirrored. -/
def storagePath (H : List Nat → Nat) (holder mappingSlot : Nat) : List Nat :=
  nibbles (H [H (slotKeyPreimage holder mappingSlot)])

/-- **TrustedState** — what the consumer already verified/configured: the finality-verified
execution `state_root` (from the sync-committee client, `evm.rs:127-133`), the watched ERC-20
contract, and its declared `balances` mapping slot. -/
structure MptState where
  stateRoot : Nat
  token : Nat
  mappingSlot : Nat
deriving DecidableEq, Repr

/-- **Update** — one claimed EIP-1186 holding: the anchor it opens against (checked against
the trusted one, as `evm.rs:53-57` demands of the consumer), the contract/holder/slot, the
claimed account fields, the claimed balance, and the two MPT node chains from `eth_getProof`. -/
structure MptUpdate where
  stateRoot : Nat
  token : Nat
  holder : Nat
  mappingSlot : Nat
  account : AccountClaim
  claimedBalance : Nat
  accountProof : List MptNode
  storageProof : List MptNode
deriving DecidableEq, Repr

/-- **THE RULES** (`verify_erc20_holding`, `evm.rs:142-206`): zero floor first; the update's
carried anchor/contract/slot must equal the TRUSTED ones; the account proof must open
`keccak(token)` to the claimed account under the state root; the storage proof must open the
holder's derived slot to the claimed balance under that account's OWN `storageHash`. Any
failing leg refuses (fail closed). -/
def mptVerify (H : List Nat → Nat) (ts : MptState) (u : MptUpdate) : Bool :=
  (u.claimedBalance != 0)
    && (u.stateRoot == ts.stateRoot)
    && (u.token == ts.token)
    && (u.mappingSlot == ts.mappingSlot)
    && verifyPath H u.stateRoot (accountPath H u.token) (encAccount u.account) u.accountProof
    && verifyPath H u.account.storageHash (storagePath H u.holder u.mappingSlot)
         (encBalance u.claimedBalance) u.storageProof

/-- **ForeignValid** — the chain's OWN validity notion for a claimed holding, stated in the
DENOTATION (no proof chains mentioned): the balance is nonzero, the claimed account is
genuinely committed at the token's hashed key under the carried state root, and the claimed
balance is genuinely committed at the holder's derived slot under that account's storageHash.
"A proven balance is genuinely committed under the state root at the right contract/slot." -/
def MptForeignValid (H : List Nat → Nat) (u : MptUpdate) : Prop :=
  u.claimedBalance ≠ 0
    ∧ Commits H u.stateRoot (accountPath H u.token) (encAccount u.account)
    ∧ Commits H u.account.storageHash (storagePath H u.holder u.mappingSlot)
        (encBalance u.claimedBalance)

/-- The empty / uninitialized update — the Nomad-law fail-closed probe. -/
def mptEmptyUpdate : MptUpdate :=
  { stateRoot := 0, token := 0, holder := 0, mappingSlot := 0,
    account := ⟨0, 0, 0, 0⟩, claimedBalance := 0, accountProof := [], storageProof := [] }

/-! ## §4 — The three obligations, DISCHARGED (parametric in the hash, so a real keccak
instance reuses these proofs verbatim). -/

/-- **NO FORGERY.** `mptVerify` accepts ⟹ the holding is genuinely committed: both tiers land
in the `Commits` denotation via `verifyPath_sound`, and the zero floor transfers. -/
theorem mpt_noForgery (H : List Nat → Nat) :
    NoForgery (mptVerify H) (MptForeignValid H) := by
  intro ts u h
  simp only [mptVerify, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨hnz, _⟩, _⟩, _⟩, hacct⟩, hstor⟩ := h
  exact ⟨hnz, verifyPath_sound H _ _ _ _ hacct, verifyPath_sound H _ _ _ _ hstor⟩

/-- **NO FORGERY, ANCHORED.** Acceptance additionally pins the update's carried anchor to the
TRUSTED state: the committed-under root IS `ts.stateRoot`, the contract IS `ts.token`, the
slot IS `ts.mappingSlot` — the full "committed under the verified state root at the right
contract/slot" statement. -/
theorem mpt_noForgery_anchored (H : List Nat → Nat) (ts : MptState) (u : MptUpdate)
    (h : mptVerify H ts u = true) :
    u.stateRoot = ts.stateRoot ∧ u.token = ts.token ∧ u.mappingSlot = ts.mappingSlot
      ∧ MptForeignValid H u := by
  have hv := mpt_noForgery H ts u h
  simp only [mptVerify, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hroot⟩, htok⟩, hslot⟩, _⟩, _⟩ := h
  exact ⟨hroot, htok, hslot, hv⟩

/-- **BALANCE BINDING — the keccak-CR theorem.** Under ONE trusted state, ONE holder has ONE
provable balance: two accepted updates for the same holder agree. The proof consumes `hCR`
through both tiers — account binding pins the account (hence `storageHash`,
`encAccount_injective`), then storage binding pins the balance. Forging a different balance
for a committed holder REQUIRES a keccak collision. This is the honest form of the crypto
leaf: an explicit hypothesis, discharged by collision resistance of the real keccak256. -/
theorem mpt_balance_binding (H : List Nat → Nat)
    (hCR : ∀ m₁ m₂, H m₁ = H m₂ → m₁ = m₂)
    (ts : MptState) (u₁ u₂ : MptUpdate)
    (h₁ : mptVerify H ts u₁ = true) (h₂ : mptVerify H ts u₂ = true)
    (hholder : u₁.holder = u₂.holder) :
    u₁.claimedBalance = u₂.claimedBalance := by
  obtain ⟨hr₁, ht₁, hs₁, _, hacct₁, hstor₁⟩ := mpt_noForgery_anchored H ts u₁ h₁
  obtain ⟨hr₂, ht₂, hs₂, _, hacct₂, hstor₂⟩ := mpt_noForgery_anchored H ts u₂ h₂
  -- Tier 1: same root (both = ts.stateRoot), same account path (both tokens = ts.token)
  -- ⟹ the committed account values agree ⟹ the accounts agree (encoding injective).
  have hAccEnc : encAccount u₁.account = encAccount u₂.account :=
    commits_binding H hCR hacct₁ hacct₂ (hr₁.trans hr₂.symm)
      (by rw [accountPath, accountPath, ht₁, ht₂])
  have hAcc : u₁.account = u₂.account := encAccount_injective hAccEnc
  -- Tier 2: same storage root (the SAME bound account's storageHash), same derived slot path
  -- (same holder, same trusted mapping slot) ⟹ the committed balances agree.
  have hBalEnc : encBalance u₁.claimedBalance = encBalance u₂.claimedBalance :=
    commits_binding H hCR hstor₁ hstor₂ (by rw [hAcc])
      (by rw [storagePath, storagePath, hholder, hs₁, hs₂])
  exact encBalance_injective hBalEnc

/-- **FAIL CLOSED.** The empty update is refused for EVERY trusted state — its zero balance
trips the Nomad-law floor before anything else is even consulted (and its empty proof chains
would fail the walk regardless: `verifyPath _ _ _ _ [] = false`). -/
theorem mpt_failClosed (H : List Nat → Nat) :
    FailClosed (mptVerify H) mptEmptyUpdate := by
  intro ts
  simp [mptVerify, mptEmptyUpdate]

/-! ## §5 — The model keccak leaf (injectivity PROVEN ⇒ this file is axiom-clean), and the
concrete two-tier example trie the discriminators run on. -/

/-- The model keccak: an injective `List Nat → Nat` fold over `Nat.pair` (with `+1` separating
every cons from `nil`). Kernel-computable, so the discriminators run by `decide`. A production
instance replaces this with EverCrypt-realized keccak256, carrying `hashCR` as its ONE named
assumption; every §4 theorem applies to it verbatim (they take `H`/`hCR` as hypotheses). -/
def toyKeccak : List Nat → Nat
  | [] => 0
  | a :: rest => Nat.pair a (toyKeccak rest) + 1

/-- **The CR leaf, PROVED for the model hash** — exactly the `CryptoLeaf.hashCR` shape. -/
theorem toyKeccak_injective : ∀ m₁ m₂, toyKeccak m₁ = toyKeccak m₂ → m₁ = m₂ := by
  intro m₁
  induction m₁ with
  | nil => intro m₂ h; cases m₂ with
    | nil => rfl
    | cons b t => simp [toyKeccak] at h
  | cons a t ih => intro m₂ h; cases m₂ with
    | nil => simp [toyKeccak] at h
    | cons b t' =>
      simp only [toyKeccak, Nat.add_right_cancel_iff] at h
      obtain ⟨ha, ht⟩ := Nat.pair_eq_pair.mp h
      rw [ha, ih t' ht]

/-- **The `CryptoLeaf` for this lane** — keccak CR is the ONLY live crypto assumption. The
signature slot is the constant-`false` verifier (an EVM inclusion proof carries NO signature;
finality of the state root is the upstream sync-committee client's leaf), so `sigSound` is
vacuously proven and can carry nothing. `hash`/`hashCR` are the model keccak and its PROVEN
injectivity — the field a production instance swaps for keccak256 + its named CR assumption. -/
def mptLeaf : CryptoLeaf where
  PubKey := Unit
  Msg := List Nat
  Sig := Unit
  Digest := Nat
  sigVerify := fun _ _ _ => false
  hash := toyKeccak
  Signed := fun _ _ => False
  sigSound := fun _ _ _ h => by simp at h
  hashCR := fun m₁ m₂ h => toyKeccak_injective m₁ m₂ h

-- The concrete two-tier example: token 1, holder 2, mapping slot 0, balance 5.
-- Storage tier exercises a BRANCH step (the derived storage path starts with nibble 9).

/-- The genuine balance leaf: remaining path `[4,0,0]` after the branch consumes nibble 9. -/
def exBalLeaf : MptNode := .leaf [4, 0, 0] (encBalance 5)
def exBalDigest : Nat := toyKeccak (encodeNode exBalLeaf)
/-- The storage-trie root branch: child at nibble 9 → the balance leaf. -/
def exStorBranch : MptNode := .branch (List.replicate 9 none ++ [some exBalDigest])
def exStorRoot : Nat := toyKeccak (encodeNode exStorBranch)
/-- The token contract's account: its `storageHash` IS the storage-trie root. -/
def exAccount : AccountClaim := ⟨1, 0, exStorRoot, 0⟩
def exAcctLeaf : MptNode := .leaf (accountPath toyKeccak 1) (encAccount exAccount)
def exStateRoot : Nat := toyKeccak (encodeNode exAcctLeaf)
/-- The trusted state: the verified root, watching token 1's mapping at slot 0. -/
def exState : MptState := ⟨exStateRoot, 1, 0⟩
/-- The genuine update: holder 2 holds 5, with both proof chains. -/
def exUpdate : MptUpdate :=
  { stateRoot := exStateRoot, token := 1, holder := 2, mappingSlot := 0,
    account := exAccount, claimedBalance := 5,
    accountProof := [exAcctLeaf], storageProof := [exStorBranch, exBalLeaf] }

/-- **NON-VACUOUS.** Under the SAME trusted state, `mptVerify` accepts the genuine holding and
rejects the forged-balance variant (same proofs, claimed balance 6) — the rules discriminate. -/
theorem mpt_nonVacuous : NonVacuous (mptVerify toyKeccak) :=
  ⟨exState, exUpdate, { exUpdate with claimedBalance := 6 }, by decide, by decide⟩

/-! ## §6 — THE DISCRIMINATORS BITE (all under the SAME trusted state `exState`). -/

/-- **THE GATE DISCRIMINATES, five ways** (the Nomad-law teeth, concrete): the genuine holding
is ACCEPTED; a forged balance (6 ≠ committed 5) is REJECTED; a tampered storage leaf carrying
6 is REJECTED (its hash breaks the branch's committed child link — swapping the value needs a
keccak collision); a wrong contract (token 3) is REJECTED; a wrong holder (4) is REJECTED —
its derived slot key walks to an ABSENT branch child (the exclusion side). -/
theorem mpt_gate_discriminates :
    mptVerify toyKeccak exState exUpdate = true
    ∧ mptVerify toyKeccak exState { exUpdate with claimedBalance := 6 } = false
    ∧ mptVerify toyKeccak exState
        { exUpdate with
            claimedBalance := 6,
            storageProof := [exStorBranch, .leaf [4, 0, 0] (encBalance 6)] } = false
    ∧ mptVerify toyKeccak exState { exUpdate with token := 3 } = false
    ∧ mptVerify toyKeccak exState { exUpdate with holder := 4 } = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **A FOREIGN-PATH ACCOUNT PROOF IS REJECTED**: an account proof whose leaf sits at ANOTHER
contract's hashed key (token 3's path) does not open under the trusted root even when the
update's carried token matches — the account key is hash-derived, so pointing the proof at the
wrong contract fails closed (`evm.rs:79-80 AccountProofInvalid`). -/
theorem mpt_wrong_contract_path_rejected :
    mptVerify toyKeccak exState
      { exUpdate with accountProof := [.leaf (accountPath toyKeccak 3) (encAccount exAccount)] }
      = false := by decide

-- The zero-holding trie: identical shape, committed balance 0 — its proofs VERIFY,
-- and the gate still refuses (the floor does its own work, evm.rs:87-91 ZeroBalance).
def exZeroLeaf : MptNode := .leaf [4, 0, 0] (encBalance 0)
def exZeroBranch : MptNode := .branch (List.replicate 9 none ++ [some (toyKeccak (encodeNode exZeroLeaf))])
def exZeroAccount : AccountClaim := ⟨1, 0, toyKeccak (encodeNode exZeroBranch), 0⟩
def exZeroAcctLeaf : MptNode := .leaf (accountPath toyKeccak 1) (encAccount exZeroAccount)
def exZeroState : MptState := ⟨toyKeccak (encodeNode exZeroAcctLeaf), 1, 0⟩
def exZeroUpdate : MptUpdate :=
  { stateRoot := toyKeccak (encodeNode exZeroAcctLeaf), token := 1, holder := 2, mappingSlot := 0,
    account := exZeroAccount, claimedBalance := 0,
    accountProof := [exZeroAcctLeaf], storageProof := [exZeroBranch, exZeroLeaf] }

/-- **THE ZERO FLOOR DOES ITS OWN WORK.** The zero holding's storage proof GENUINELY VERIFIES
(second conjunct — the walk accepts it), and the gate still REFUSES the update (first
conjunct): a trivial/empty holding never mints a proven holding, even fully committed. -/
theorem mpt_zero_balance_refused :
    mptVerify toyKeccak exZeroState exZeroUpdate = false
    ∧ verifyPath toyKeccak exZeroUpdate.account.storageHash (storagePath toyKeccak 2 0)
        (encBalance 0) exZeroUpdate.storageProof = true := by
  exact ⟨by decide, by decide⟩

/-! ## §7 — The bundled `ForeignLightClient` instance, and the InterchainAdapter discharge. -/

/-- **The EVM-state-inclusion `ForeignLightClient`.** All three obligations are the §4/§5
theorems; the leaf is `mptLeaf` (keccak CR the only live assumption, PROVEN for the model
hash). A production instance changes exactly one thing: the hash + its named CR discharge. -/
def mptClient : ForeignLightClient where
  leaf := mptLeaf
  Update := MptUpdate
  TrustedState := MptState
  ForeignValid := MptForeignValid toyKeccak
  verify := mptVerify toyKeccak
  emptyUpdate := mptEmptyUpdate
  noForgery := mpt_noForgery toyKeccak
  failClosed := mpt_failClosed toyKeccak
  nonVacuous := mpt_nonVacuous

/-- The inclusion relation for the adapter: the cross-chain EVENT "holder `ev.1` holds
`ev.2`" is included in an update that claims exactly that. -/
def mptIncl : Nat × Nat → MptUpdate → Prop :=
  fun ev u => ev.1 = u.holder ∧ ev.2 = u.claimedBalance

/-- The `InterchainAdapter` this light client PRODUCES at the verified anchor: `foreignFinal`
is the DECIDABLE verify verdict on the `proof` rung — the adapter's finality hypothesis is
discharged by the rules, not assumed. -/
def mptAdapter : Metatheory.Bridge.InterchainAdapter MptUpdate (Nat × Nat) :=
  toAdapter mptClient exState mptIncl

/-- **END-TO-END DISCHARGE.** The adapter ACCEPTS the genuine holding event `(holder 2, 5)`,
and that acceptance ENTAILS a foreign-VALID update including it (`NoForgery` through
`toAdapter_accepts_entails_valid`) — proof-of-holding, discharged to the denotation. -/
theorem mpt_adapter_accepts_and_discharges :
    mptAdapter.accepts (2, 5)
    ∧ ∃ u, MptForeignValid toyKeccak u ∧ mptIncl (2, 5) u := by
  have hacc : mptAdapter.accepts (2, 5) :=
    ⟨exUpdate, (by decide : mptVerify toyKeccak exState exUpdate = true), rfl, rfl⟩
  exact ⟨hacc, toAdapter_accepts_entails_valid mptClient exState mptIncl (2, 5) hacc⟩

/-- **The empty update is rejected at the adapter boundary** — `FailClosed`, lifted. -/
theorem mpt_adapter_rejects_empty : ¬ mptAdapter.foreignFinal mptClient.emptyUpdate :=
  toAdapter_rejects_empty mptClient exState mptIncl

/-! ### It runs (`#guard`): the derived paths and the gate, on concrete data. -/

#guard storagePath toyKeccak 2 0 == [9, 4, 0, 0]   -- holder 2's derived slot path
#guard storagePath toyKeccak 4 0 == [11, 15, 1, 0] -- holder 4 walks a DIFFERENT path
#guard mptVerify toyKeccak exState exUpdate == true
#guard mptVerify toyKeccak exState { exUpdate with claimedBalance := 6 } == false
#guard mptVerify toyKeccak exState mptEmptyUpdate == false
#guard mptVerify toyKeccak exZeroState exZeroUpdate == false

/-! ## §8 — Axiom hygiene: every theorem kernel-clean. The model leaf is PROVED
(`toyKeccak_injective`), so nothing rests on an unproven crypto assumption; a production
instance's `noForgery`/`binding` would rest on its VISIBLE, NAMED `hashCR` hypothesis —
invisible to `#assert_axioms` by design, which is why it is an explicit structure field /
theorem hypothesis an auditor reads at the instance site. -/

#assert_all_clean [encOpt_injective, map_encOpt_injective, encodeNode_injective,
  verifyPath_sound, commits_binding, encAccount_injective, encBalance_injective,
  mpt_noForgery, mpt_noForgery_anchored, mpt_balance_binding, mpt_failClosed,
  toyKeccak_injective, mpt_nonVacuous, mpt_gate_discriminates,
  mpt_wrong_contract_path_rejected, mpt_zero_balance_refused,
  mpt_adapter_accepts_and_discharges, mpt_adapter_rejects_empty]

#print axioms mpt_balance_binding
#print axioms mpt_gate_discriminates

end Dregg2.Bridge.LightClientMpt
