/-
# `Dregg2.Crypto.HashSigMerkle` — the MANY-TIME hash-based signature: a Merkle root over N
one-time keys (the SLH-DSA / SPHINCS+ shape).

`Dregg2.Crypto.HashSig` proved the ATOM — the Lamport one-time signature (correctness + the
forgery tooth, both reducing only to the hash). This file lifts it to MANY-TIME exactly the way
its header promised: a Merkle tree over `N` one-time public keys, reusing
`Dregg2.Lightclient.MMR` — whose root already `#assert_axioms`-cleanly binds its leaves
(`mroot_injective`) under the SAME single CR floor (`Poseidon2SpongeCR`) the STARK layer carries.

* The **master public key** is `mroot` over the log whose `j`-th leaf is the hash of the `j`-th
  OTS public key (`pkLeaf`).
* A **signature at index `i`** is `(i, claimed OTS pubkey, OTS signature, opening)`. At the wire
  the opening is the Merkle authentication path; at the model — MMR's own discipline
  (`Opens`' docstring) — it is a log recomposing the root, pinned by `mroot_injective`.
* **Verify** = the opening places the claimed pubkey's leaf at index `i` under the master root,
  AND `HashSig.verify` accepts the OTS signature under that pubkey.

Proved: `merkle_ots_correct` (a genuine signature at any index verifies — `lamport_correct`
composed with the opening's correctness) and `merkle_ots_binds_index` (THE BINDING TOOTH: any
verifying signature's OTS pubkey IS the one committed at that index — you cannot swap keys —
so its OTS layer verifies under the GENUINE key and `lamport_forgery_breaks_hash` applies to it).

The hash carriers stay HYPOTHESES (`Poseidon2SpongeCR hash`), never Lean axioms. §Non-vacuity
witnesses TRUE (a concrete 2-key instance verifies, by `decide`) and FALSE (a swapped-in wrong
key at an index is REJECTED; an honest index-1 signature REPLAYED at index 0 is REJECTED).
-/
import Dregg2.Crypto.HashSig
import Dregg2.Lightclient.MMR

namespace Dregg2.Crypto.HashSigMerkle

open Dregg2.Crypto.HashSig
open Dregg2.Lightclient.MMR (mroot mroot_injective Opens)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Substrate.Heap (refSponge)

/-! ## §1 — committing an OTS public key as one MMR leaf.

The OTS domain is `ℤ` (the felt domain the MMR log carries). A Lamport public key
`Fin ℓ → Bool → ℤ` flattens to the list of its `false`-branch hashes followed by its
`true`-branch hashes; the leaf is one sponge call over that list. -/

/-- Flatten an OTS public key: the `false` column then the `true` column, position order. -/
def pkEncode {ℓ : ℕ} (pk : Fin ℓ → Bool → ℤ) : List ℤ :=
  ((List.finRange ℓ).map fun i => pk i false) ++ ((List.finRange ℓ).map fun i => pk i true)

/-- The committed leaf for one OTS public key: one sponge call over the flattened key. -/
def pkLeaf (hash : List ℤ → ℤ) {ℓ : ℕ} (pk : Fin ℓ → Bool → ℤ) : ℤ :=
  hash (pkEncode pk)

/-- `finRange` reads back its own index (the positional handle every opening below uses). -/
theorem finRange_getElem? {n : ℕ} (i : Fin n) : (List.finRange n)[i.val]? = some i := by
  simp

/-- **The encoding is injective** — equal flattenings force equal public keys (split the
concat by the equal-length halves, then read each column back at its position). -/
theorem pkEncode_injective {ℓ : ℕ} {pk pk' : Fin ℓ → Bool → ℤ}
    (h : pkEncode pk = pkEncode pk') : pk = pk' := by
  unfold pkEncode at h
  obtain ⟨hf, ht⟩ := List.append_inj h (by simp)
  funext i b
  cases b
  · have := congrArg (fun l => l[i.val]?) hf
    simpa [finRange_getElem?] using this
  · have := congrArg (fun l => l[i.val]?) ht
    simpa [finRange_getElem?] using this

#assert_axioms finRange_getElem?
#assert_axioms pkEncode_injective

/-! ## §2 — the many-time scheme: key log, master root, sign, verify. -/

/-- The key log: leaf `j` commits the `j`-th one-time public key. -/
def keyLog (hash : List ℤ → ℤ) (H : ℤ → ℤ) {ℓ N : ℕ} (sks : Fin N → SecretKey ℤ ℓ) :
    List ℤ :=
  (List.finRange N).map fun j => pkLeaf hash (publicKey H (sks j))

/-- **THE MASTER PUBLIC KEY** — the MMR root over the `N` committed OTS public keys. One felt;
everything a verifier ever holds. -/
def masterKey (hash : List ℤ → ℤ) (H : ℤ → ℤ) {ℓ N : ℕ} (sks : Fin N → SecretKey ℤ ℓ) : ℤ :=
  mroot hash (keyLog hash H sks)

/-- The key log reads back leaf `i`: the committed hash of the `i`-th genuine public key. -/
theorem keyLog_getElem? (hash : List ℤ → ℤ) (H : ℤ → ℤ) {ℓ N : ℕ}
    (sks : Fin N → SecretKey ℤ ℓ) (i : Fin N) :
    (keyLog hash H sks)[i.val]? = some (pkLeaf hash (publicKey H (sks i))) := by
  simp [keyLog]

/-- A many-time signature: the index, the claimed OTS public key, the OTS signature, and the
opening material. At the wire `openLog` is the Merkle authentication path; at the model (MMR's
own discipline) it is a log the verifier checks recomposes the master root — `mroot_injective`
pins it to the genuine key log. -/
structure Sig (ℓ : ℕ) where
  idx : ℕ
  pk : Fin ℓ → Bool → ℤ
  ots : Fin ℓ → ℤ
  openLog : List ℤ

/-- **Sign** message `m` with the `i`-th one-time key: the honest OTS signature under `sks i`,
the genuine public key, the genuine opening. (Index discipline — never reuse an `i` — is the
signer's statekeeping, exactly as in XMSS/SPHINCS+; the theorems below are per-index.) -/
def msign (hash : List ℤ → ℤ) (H : ℤ → ℤ) {ℓ N : ℕ} (sks : Fin N → SecretKey ℤ ℓ)
    (i : Fin N) (m : Fin ℓ → Bool) : Sig ℓ :=
  { idx := i.val
    pk := publicKey H (sks i)
    ots := sign (sks i) m
    openLog := keyLog hash H sks }

/-- **Verify** against the master root: (1) the opening recomposes the root, (2) it places the
claimed pubkey's leaf at the signature's index, (3) the OTS signature verifies under the claimed
pubkey. -/
def mverify (hash : List ℤ → ℤ) (H : ℤ → ℤ) (root : ℤ) {ℓ : ℕ} (m : Fin ℓ → Bool)
    (s : Sig ℓ) : Prop :=
  mroot hash s.openLog = root
    ∧ Opens s.openLog s.idx (pkLeaf hash s.pk)
    ∧ verify H s.pk m s.ots

instance (hash : List ℤ → ℤ) (H : ℤ → ℤ) (root : ℤ) {ℓ : ℕ} (m : Fin ℓ → Bool) (s : Sig ℓ) :
    Decidable (mverify hash H root m s) := by
  unfold mverify Dregg2.Crypto.HashSig.verify; infer_instance

/-! ## §3 — the two theorems. -/

/-- **CORRECTNESS (`merkle_ots_correct`).** A genuine many-time signature — the honest OTS
signature at any index `i`, carried with the real opening — VERIFIES against the master key.
Unconditional (no carrier needed): `lamport_correct` composed with the key log reading back its
own leaf. This is the positive pole: the acceptance predicate is satisfiable at EVERY index. -/
theorem merkle_ots_correct (hash : List ℤ → ℤ) (H : ℤ → ℤ) {ℓ N : ℕ}
    (sks : Fin N → SecretKey ℤ ℓ) (i : Fin N) (m : Fin ℓ → Bool) :
    mverify hash H (masterKey hash H sks) m (msign hash H sks i m) :=
  ⟨rfl, keyLog_getElem? hash H sks i, lamport_correct H (sks i) m⟩

/-- **THE BINDING TOOTH (`merkle_ots_binds_index`).** ANY verifying signature at index `i` —
whatever pubkey and opening the adversary supplied — carries EXACTLY the OTS public key
committed at index `i` when the master key was minted, and its OTS layer verifies under that
GENUINE key. So a key swap at an index is impossible under the one CR floor: `mroot_injective`
pins the opened log to the genuine key log, the leaf at `i` pins the pubkey hash, CR peels the
sponge, `pkEncode_injective` recovers the key. Consequence: a verifying forgery at index `i` on
a fresh message IS a verifying Lamport forgery against `sks i` — `lamport_forgery_breaks_hash`
applies verbatim to the second conjunct, closing the many-time reduction onto the one-time atom.
Genuinely refutable: for a `pk` different from the committed one the first conjunct is FALSE
(witnessed at §4, `demo_wrong_key_rejected`). -/
theorem merkle_ots_binds_index (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (H : ℤ → ℤ) {ℓ N : ℕ} (sks : Fin N → SecretKey ℤ ℓ) (i : Fin N)
    {m : Fin ℓ → Bool} {s : Sig ℓ} (hidx : s.idx = i.val)
    (hv : mverify hash H (masterKey hash H sks) m s) :
    s.pk = publicKey H (sks i) ∧ verify H (publicKey H (sks i)) m s.ots := by
  obtain ⟨hroot, hopen, hver⟩ := hv
  -- the opening's log recomposes the master root ⇒ it IS the genuine key log:
  have hlog : s.openLog = keyLog hash H sks := mroot_injective hash hCR hroot
  rw [hlog, hidx] at hopen
  -- leaf `i` of the genuine log is the committed pubkey's hash; the opening placed the
  -- claimed pubkey's hash there:
  have hleaf : pkLeaf hash s.pk = pkLeaf hash (publicKey H (sks i)) :=
    Option.some.inj ((hopen : _ = some _).symm.trans (keyLog_getElem? hash H sks i))
  -- CR peels the sponge, the encoding peels the flattening:
  have hpk : s.pk = publicKey H (sks i) := pkEncode_injective (hCR _ _ hleaf)
  exact ⟨hpk, hpk ▸ hver⟩

#assert_axioms merkle_ots_correct
#assert_axioms merkle_ots_binds_index

/-! ## §4 — NON-VACUITY: witnesses TRUE and FALSE on a concrete 2-key instance.

`ℓ = 1`, `N = 2`, on the computable Horner toy sponge `refSponge` (NOT real crypto; deployment
= p3 Poseidon2 behind the CR floor) with `H := refSponge ∘ singleton`. TRUE: the honest
signature at index 0 verifies, by `decide` — the acceptance predicate is computably satisfied,
so neither theorem is vacuous. FALSE: swapping key 1's material in at index 0 is REJECTED
(exactly the situation `merkle_ots_binds_index` forbids — its conclusion `s.pk = publicKey H
(sks 0)` is FALSE for this `s`, and indeed verification fails); replaying an honest index-1
signature at index 0 is REJECTED. -/

/-- Two demo one-time keys: key `j`'s preimages are `10(j+1) + bit`. All four distinct. -/
def demoSks : Fin 2 → SecretKey ℤ 1 := fun j =>
  ⟨fun _ b => 10 * ((j : ℤ) + 1) + (if b then 1 else 0)⟩

/-- The demo bit-hash: one sponge call per felt. -/
def demoH : ℤ → ℤ := fun d => refSponge [d]

/-- The demo message: the single bit `true`. -/
def demoM : Fin 1 → Bool := fun _ => true

/-- **Witness TRUE** — the honest signature at index 0 VERIFIES, computably (`decide` runs the
whole pipeline: key log, MMR root, opening, Lamport check). -/
theorem demo_honest_verifies :
    mverify refSponge demoH (masterKey refSponge demoH demoSks) demoM
      (msign refSponge demoH demoSks 0 demoM) := by decide

/-- The key-swap forgery: index 0, but carrying key 1's public key and key 1's OTS signature
(with the genuine log as opening — the best the adversary can do, since any other log moves the
root). This is the exact object the binding tooth outlaws. -/
def demoSwappedSig : Sig 1 :=
  { idx := 0
    pk := publicKey demoH (demoSks 1)
    ots := sign (demoSks 1) demoM
    openLog := keyLog refSponge demoH demoSks }

/-- **Witness FALSE #1 — the key swap is REJECTED.** The wrong pubkey's leaf does not open at
index 0 (leaf 0 commits key 0). The binding theorem's conclusion is FALSE of this signature
(`publicKey demoH (demoSks 1) ≠ publicKey demoH (demoSks 0)` — the keys are distinct), and
verification indeed fails: the tooth bites. -/
theorem demo_wrong_key_rejected :
    ¬ mverify refSponge demoH (masterKey refSponge demoH demoSks) demoM demoSwappedSig := by
  decide

/-- The two committed public keys really differ (so the binding conclusion is a nontrivial
constraint — `demoSwappedSig.pk = publicKey demoH (demoSks 0)` is genuinely false). -/
theorem demo_keys_distinct : publicKey demoH (demoSks 1) ≠ publicKey demoH (demoSks 0) := by
  intro h
  have := congrFun (congrFun h 0) true
  simp [publicKey, demoSks, demoH, refSponge] at this

/-- **Witness FALSE #2 — cross-index replay is REJECTED.** An HONEST signature minted at index
1, re-presented with `idx := 0`: every component is genuine except the index, and the opening
check kills it (leaf 0 does not commit key 1). Index is part of what the root binds. -/
theorem demo_replay_rejected :
    ¬ mverify refSponge demoH (masterKey refSponge demoH demoSks) demoM
      { msign refSponge demoH demoSks 1 demoM with idx := 0 } := by
  decide

#assert_axioms demo_honest_verifies
#assert_axioms demo_wrong_key_rejected
#assert_axioms demo_keys_distinct
#assert_axioms demo_replay_rejected

end Dregg2.Crypto.HashSigMerkle
