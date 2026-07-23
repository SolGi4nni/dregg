/-
# `Dregg2.Crypto.HashSigMerkleRegrounded` — the SLH-DSA / SPHINCS+ MANY-TIME hash-signature KEY-SWAP
binding, as a SECURITY REDUCTION to a collision game at a class with content.

## The gap this closes

`HashSigMerkle.merkle_ots_binds_index` is the BINDING floor of the many-time hash signature (a Merkle
root over `N` one-time keys — the SLH-DSA / SPHINCS+ shape): any verifying signature at index `i`
carries EXACTLY the OTS public key committed at `i` (no key swap), so a verifying forgery is a genuine
Lamport forgery on the committed key. It is conditioned on `Poseidon2Binding.Poseidon2SpongeCR hash` —
the injective sponge floor `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE (a
compressing sponge has collisions by pigeonhole). At the deployed p3 Poseidon2 sponge the key-swap
binding is therefore VACUOUSLY TRUE.

## ⚑ WHAT THIS FILE USED TO EXPORT, AND WHY IT IS GONE

The previous export was

    theorem merkle_ots_binds_advantage_bound (hCR : CollisionResistant F) (leafSwap : CollisionFinder F)
      : Negl (collisionAdv F leafSwap)

which is the SAME DISEASE one costume along. `FloorGames.collisionResistant_iff_hashCRHardQuant_top`
proves `CollisionResistant F` is definitionally the collision floor at the UNRESTRICTED adversary
class, and `collisionResistant_false_of_compressing` proves THAT false for any compressing family —
the deployed sponge included. So the replacement hypothesis was refuted at deployed parameters exactly
like the one it replaced, and the theorem transported no security. It is DELETED, not kept beside the
repair.

Its `_eff` sibling was better (a floor at an explicit class) but still not a reduction: it took a
`CollisionFinder F` and applied the floor to it. Hypothesis and conclusion were the same object, so
there was no game about the KEY SWAP at all — the forgery never appeared in a `Prop`.

## What replaces them (§2–§4)

  * **§2 — the key swap is a first-class `Game`.** `keySwapGame` hands the adversary a sampled
    domain-separation tag; it WINS iff it outputs a key set, an index, a message and a signature such
    that the signature VERIFIES against the master root at that index (the deployed `mverify`, read off
    the real `masterKey`) while carrying a public key DIFFERENT from the one committed there. The
    forgery is IN the win relation, on the deployed acceptance predicate.
  * **§3 — the extractor is a map of adversaries.** `keySwapToFinder` returns
    `(pkEncode s.pk, pkEncode (publicKey H (sks i)))`. `keySwap_wins_imp` proves that pair is a GENUINE
    sponge collision: the opening places the claimed key's leaf where the committed key's leaf is, so
    the two encodings hash equal, and `pkEncode_injective` contraposed makes them distinct. This is
    exactly the step `merkle_ots_binds_index` spends its (false) injectivity hypothesis on.
  * **§4 — the bound, and its `hEff` DISCHARGED.** `keySwap_binds_advantage_bound` is the reduction at
    an arbitrary class; `merkle_ots_binds_from_polyTime` proves the extracted finder efficient at
    `Eff := IsPolyTime` (`CostAdversary`) instead of assuming it, so nothing floats.

## ⚑ THE NAMED, SEPARATELY-PRICED RESIDUAL — say it out loud

`merkle_ots_binds_index` spends its sponge floor TWICE: once on the leaf (closed here) and once on
`MMR.mroot_injective`, which peels the whole `bag`/`hashOf` forest to conclude the opened log IS the
genuine key log. The key-swap game carries `openLog = keyLog …` as an explicit SIDE CONDITION, so this
file closes the LEAF leg only. **The MMR root leg is NOT closed and is not pretended to be:**
`MMR.bag_injective` / `MMR.mroot_injective` still ride the refuted injective `Poseidon2SpongeCR` and
have no extractor. That is a real open carrier, named here so it is countable rather than absorbed.

## Non-fake

The break game is refutable (§5: on the constant-`0` sponge a key swap succeeds at every tag), the
canary refuses the floor applied at ANOTHER finder, and both poles of the class are priced. No `sorry`,
no fresh `axiom`, no `native_decide`.
-/
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Dregg2.Crypto.HashSigMerkle

namespace Dregg2.Crypto.HashSigMerkleRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv idFamily idFamily_CR
   brokenFamily brokenFamily_not_CR)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit hashGame finderToAdv HashCRHardQuant Hard
   collisionAdv_eq_gameAdv collisionResistant_iff_hashCRHardQuant_top hard_bot_vacuous
   not_hard_top_of_always_solvable)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited idAdv)
open Dregg2.Crypto.HashSig (SecretKey publicKey verify)
open Dregg2.Crypto.HashSigMerkle
  (pkEncode pkLeaf pkEncode_injective keyLog masterKey keyLog_getElem? Sig mverify msign
   merkle_ots_correct)

set_option autoImplicit false

/-! ## §1 — the deployed sponge, as a KEYED family.

The deployed p3 Poseidon2 sponge is UNKEYED; its domain separation is the effective key, which is what
a `KeyedHashFamily`'s `Key` is for (`HashFloorHonesty` §2). `SpongeDeployment` carries the tag space the
collision game samples and the sponge at each tag, and asserts NOTHING false about the sponge — in
particular no injectivity field, which is what made the old carrier uninhabitable at real parameters. -/

/-- **THE DEPLOYED SPONGE, KEYED — carrying NO CR field.** At `deployedTag` this IS the p3 Poseidon2
sponge the hash-signature Merkle log absorbs through. -/
structure SpongeDeployment where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The keyed sponge; at `deployedTag` this IS the deployed Poseidon2 sponge. -/
  hashAt : Tag → List ℤ → ℤ
  /-- The specific tag the deployment computes at this use site. -/
  deployedTag : Tag

/-- **`spongeFamily D`** — the deployed sponge lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. Input `List ℤ` (the absorbed block), output `ℤ` (the squeezed felt). -/
def spongeFamily (D : SpongeDeployment) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List ℤ
  Out := ℤ
  H := fun _ t xs => D.hashAt t xs
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The DEPLOYED fixed sponge IS the family's instance at the deployed tag — a
definitional equality, no idealization. So the collision game below is a game about the very function
the hash-signature log absorbs through. -/
theorem deployedSponge_is_family_instance (D : SpongeDeployment) (n : ℕ) :
    D.hashAt D.deployedTag = (spongeFamily D).H n D.deployedTag := rfl

/-- **THE OLD-FLOOR ⟹ NEW-FLOOR BRIDGE.** If the injective sponge floor held at every tag it would
discharge `CollisionResistant (spongeFamily D)` — the collision floor at the UNRESTRICTED class. So the
deleted carrier was STRICTLY STRONGER than even the ⊤-class floor, and being false at deployed
parameters it was an EMPTY hypothesis. Recorded so the deletion is auditable, not asserted. -/
theorem spongeFamily_CR_of_injective (D : SpongeDeployment)
    (hinj : ∀ t : D.Tag, Function.Injective (D.hashAt t)) :
    CollisionResistant (spongeFamily D) :=
  Dregg2.Circuit.HashFloorHonesty.injective_family_CR (spongeFamily D) (fun _ t => hinj t)

/-! ## §2 — the KEY SWAP, as a first-class game. -/

/-- The object a key-swap forger exhibits: a key set, the index it attacks, the message, and the
signature it presents. Everything the deployed `mverify` reads. -/
structure KeySwap (ℓ N : ℕ) where
  /-- The one-time key set whose master root is published. -/
  sks : Fin N → SecretKey ℤ ℓ
  /-- The index the swap is performed at. -/
  i : Fin N
  /-- The message the forged signature is presented on. -/
  m : Fin ℓ → Bool
  /-- The presented signature (its `pk` field is the SWAPPED key). -/
  s : Sig ℓ

/-- **THE KEY-SWAP GAME.** The adversary is handed a sampled domain-separation tag and WINS iff it
presents a signature that

  1. is at the attacked index (`s.idx = i`),
  2. VERIFIES against the master root — the deployed `mverify` at the real `masterKey`, not a
     paraphrase of it,
  3. opens along the GENUINE key log (the explicitly-priced side condition — see the header: the
     complementary case is the MMR root leg, `MMR.mroot_injective`, NOT closed here), and
  4. nonetheless carries a public key DIFFERENT from the one committed at that index.

A win is exactly the key swap `HashSigMerkle.merkle_ots_binds_index` denies: a verifying many-time
signature whose OTS layer runs under a key the master root never committed. The forgery is IN the win
relation. (`winsDec` is classical: the win quantifies over `verify`'s `∀ i` at an arbitrary `ℓ`, and
the instance space — not the answer space — is what the counting needs finite.) -/
noncomputable def keySwapGame (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => KeySwap ℓ N
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t a =>
    a.s.idx = a.i.val ∧
      mverify (D.hashAt t) H (masterKey (D.hashAt t) H a.sks) a.m a.s ∧
      a.s.openLog = keyLog (D.hashAt t) H a.sks ∧
      a.s.pk ≠ publicKey H (a.sks a.i)
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — a win unfolds, by `Iff.rfl`, to a verifying signature at an
index carrying the wrong OTS public key. Not a docstring: the `Prop` itself. -/
theorem keySwapGame_wins_iff (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ) (n : ℕ) (t : D.Tag)
    (a : KeySwap ℓ N) :
    (keySwapGame D H ℓ N).wins n t a ↔
      (a.s.idx = a.i.val ∧
        mverify (D.hashAt t) H (masterKey (D.hashAt t) H a.sks) a.m a.s ∧
        a.s.openLog = keyLog (D.hashAt t) H a.sks ∧
        a.s.pk ≠ publicKey H (a.sks a.i)) :=
  Iff.rfl

/-! ## §3 — the reduction: a key swapper IS a sponge collision finder. -/

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A key swapper becomes a sponge-collision finder by
handing back the two FLATTENED public keys — the one it swapped in and the one the master root
committed. This is not a rename: the swapper's leverage is the whole verifying signature, and the
finder sees only the two encodings; the collision has to be RE-DERIVED on the other side
(`keySwap_wins_imp`). -/
def keySwapToFinder (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ)
    (A : Adversary (keySwapGame D H ℓ N)) : Adversary (hashGame (spongeFamily D)) where
  run := fun n t =>
    let a := A.run n t
    (pkEncode a.s.pk, pkEncode (publicKey H (a.sks a.i)))

/-- **⚑ WIN-PRESERVATION — and this IS `merkle_ots_binds_index`'s crypto step, contraposed.** Wherever
the swapper wins, the two flattened keys are a GENUINE sponge collision. The derivation is the one the
old keystone ran under the false injectivity hypothesis: the opening places the CLAIMED key's leaf at
the attacked index, the genuine key log places the COMMITTED key's leaf there, so the two `pkLeaf`s —
i.e. the sponge at the two encodings — are EQUAL; and `pkEncode_injective` contraposed against the win's
`pk ≠ committed pk` makes the two encodings DISTINCT. Injectivity used to consume this equality; here it
is handed to the collision floor instead. -/
theorem keySwap_wins_imp (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ)
    (A : Adversary (keySwapGame D H ℓ N)) (n : ℕ) (t : D.Tag)
    (hwin : (keySwapGame D H ℓ N).wins n t (A.run n t)) :
    (hashGame (spongeFamily D)).wins n t ((keySwapToFinder D H ℓ N A).run n t) := by
  obtain ⟨hidx, hv, hlog, hne⟩ := hwin
  obtain ⟨_, hopen, _⟩ := hv
  rw [hlog, hidx] at hopen
  have hleaf : pkLeaf (D.hashAt t) (A.run n t).s.pk
      = pkLeaf (D.hashAt t) (publicKey H ((A.run n t).sks (A.run n t).i)) :=
    Option.some.inj ((hopen : _ = some _).symm.trans
      (keyLog_getElem? (D.hashAt t) H (A.run n t).sks (A.run n t).i))
  exact ⟨fun henc => hne (pkEncode_injective henc), hleaf⟩

/-- **THE ADVANTAGE INEQUALITY.** The key swapper's advantage is at most the extracted sponge-collision
finder's, at every parameter — both play over the SAME sampled tag space, and every tag the swapper wins
the extracted finder wins. Unconditional: no adversary class appears. -/
theorem keySwap_adv_le (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ)
    (A : Adversary (keySwapGame D H ℓ N)) (n : ℕ) :
    gameAdv (keySwapGame D H ℓ N) A n
      ≤ gameAdv (hashGame (spongeFamily D)) (keySwapToFinder D H ℓ N A) n := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact keySwap_wins_imp D H ℓ N A n t ht

/-- **⚑ RE-GROUNDED `HashSigMerkle.merkle_ots_binds_index` — from the sponge's collision floor, VIA the
reduction.**

Under the DEPLOYED sponge's collision floor at the class `Eff`, a key swapper whose extracted finder is
in that class has NEGLIGIBLE advantage: a verifying many-time signature carries the OTS public key the
master root committed EXCEPT with negligible probability, so `lamport_forgery_breaks_hash` applies to
the genuine key except with that advantage. The Boolean "no key swap", which needed the FALSE injective
sponge floor, becomes an honest advantage bound on a hypothesis a real sponge can satisfy.

`hEff` is a parameter here because this is the statement at an ARBITRARY class; §4 discharges it. -/
theorem keySwap_binds_advantage_bound (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (keySwapGame D H ℓ N))
    (hEff : Eff (keySwapToFinder D H ℓ N A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (keySwapGame D H ℓ N) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (keySwapGame D H ℓ N) A n).1)
    (keySwap_adv_le D H ℓ N A) (hCR _ hEff)

/-! ## §4 — `hEff` DISCHARGED at `Eff := IsPolyTime`.

The extractor is a pure output reshaping with the sampled tag passed through — an `Adversary.postMap` —
so `isPolyTime_postMap` turns `hEff` into a consequence of "the key swapper is efficient". The one
per-site fact is the extractor's output size, and it is PROVED: `pkEncode` flattens a `Fin ℓ → Bool → ℤ`
into exactly `2ℓ` felts, whatever the key, so the finder writes `4ℓ` felts — a CONSTANT at fixed
parameters. -/

/-- `pkEncode` emits exactly `2ℓ` felts — the two columns of the Lamport key, in position order. -/
theorem pkEncode_length {ℓ : ℕ} (pk : Fin ℓ → Bool → ℤ) : (pkEncode pk).length = 2 * ℓ := by
  simp only [pkEncode, List.length_append, List.length_map, List.length_finRange]
  omega

/-- **THE KEY-SWAP GAME'S ANSWER ENCODING** — the key set, the index, the message and the signature.
Concrete on purpose: the size measure belongs to the GAME (`CostAdversary` design commitment 4). -/
noncomputable def keySwapAnsSize (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ) :
    AnsSize (keySwapGame D H ℓ N) :=
  fun _ (a : KeySwap ℓ N) => 2 * ℓ * N + 2 * ℓ + a.s.openLog.length + 1

/-- **THE COLLISION GAME'S ANSWER ENCODING** — the two claimed absorbed blocks. -/
def spongeAnsSize (D : SpongeDeployment) : AnsSize (hashGame (spongeFamily D)) :=
  fun _ (p : List ℤ × List ℤ) => p.1.length + p.2.length

/-- **⚑ `hEff` DISCHARGED — the many-time key-swap binding with NO floating efficiency parameter.** A
key swapper that is EFFICIENT at the game's own answer encoding, put through the flattening extractor,
yields a sponge-collision finder that is STILL efficient — so the collision floor at `Eff := IsPolyTime`
applies to IT, and a key swap at an index succeeds only with negligible advantage.

What remains supplied is the reshaper's declared work `(cw, bw)` — a Lean `fun` has no runtime, so that
number is CHARGED in the program's syntax rather than derived. The output growth `(0, 4ℓ)` is PROVED
from `pkEncode_length`, and no `PolyBoundedNat` overhead hypothesis is taken. -/
theorem merkle_ots_binds_from_polyTime (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ)
    (A : Adversary (keySwapGame D H ℓ N)) (hA : IsPolyTime (keySwapAnsSize D H ℓ N) A) (cw bw : ℕ)
    (hCR : HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (keySwapGame D H ℓ N) A) := by
  have hEff : IsPolyTime (spongeAnsSize D) (keySwapToFinder D H ℓ N A) := by
    poly_time (keySwapAnsSize D H ℓ N) (spongeAnsSize D)
      (fun _ _ (a : KeySwap ℓ N) => (pkEncode a.s.pk, pkEncode (publicKey H (a.sks a.i))))
      cw bw 0 (4 * ℓ) hA
    intro n t a
    show (pkEncode a.s.pk).length + (pkEncode (publicKey H (a.sks a.i))).length
      ≤ 0 * (keySwapAnsSize D H ℓ N n a) + 4 * ℓ
    rw [pkEncode_length, pkEncode_length]
    omega
  exact keySwap_binds_advantage_bound D H ℓ N (IsPolyTime (spongeAnsSize D)) A hEff hCR

/-- **(TOOTH — the class the floor is instantiated at is NOT EMPTY.)** `HashCRHardQuant (spongeFamily D)
(IsPolyTime (spongeAnsSize D))` is not the vacuous `Eff := ⊥` floor: the constant finder is in the
class, because the answer it writes has size `0` under the game's own encoding. Together with
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness is excluded) this pins the instantiated
floor strictly between §5's two poles. -/
theorem spongeFloor_isPolyTime_inhabited (D : SpongeDeployment) :
    IsPolyTime (spongeAnsSize D)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [spongeAnsSize]⟩

/-! ## §5 — the poles, the canary, and the positive pole. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at a compressing sponge family.)** The bare-CR floor at the
constant-`0` `brokenFamily` is refuted (`brokenFamily_not_CR`), and it IS `HashCRHardQuant brokenFamily
⊤` (`collisionResistant_iff_hashCRHardQuant_top`) — so the `⊤` class is FALSE. This is the price of
restricting the class, stated as a theorem, and it is precisely why the DELETED
`merkle_ots_binds_advantage_bound` (which took `CollisionResistant F`) bought nothing. -/
theorem merkle_ots_eff_top_false : ¬ HashCRHardQuant brokenFamily (fun _ => True) :=
  fun h => brokenFamily_not_CR ((collisionResistant_iff_hashCRHardQuant_top _).mpr h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY
sponge family, including a completely broken one. Both poles together are what make `Eff` a dial. -/
theorem merkle_ots_eff_bot_vacuous {F : KeyedHashFamily} : HashCRHardQuant F (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — the key-swap bound does NOT follow from the floor applied at ANOTHER finder.)** Strip
the reduction: try to conclude the swapper's negligibility from the sponge floor applied at some OTHER
finder `B`, not the one EXTRACTED from it. It does not go through — `hCR B hB` proves `Negl` of the
WRONG advantage, and only `keySwap_adv_le` connects the extracted finder to the key-swap game. This
tooth was UNWRITABLE against the deleted export, whose hypothesis and conclusion were the same object;
it compiles now, and reds if a future edit reconnects the games. -/
example (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (keySwapGame D H ℓ N))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (keySwapGame D H ℓ N) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With the sponge collision floor at the EXTRACTED finder the keystone
fires. Refusal is discrimination only if acceptance still happens. -/
theorem the_reduced_keySwap_bound_fires (D : SpongeDeployment) (H : ℤ → ℤ) (ℓ N : ℕ)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (keySwapGame D H ℓ N))
    (hEff : Eff (keySwapToFinder D H ℓ N A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (keySwapGame D H ℓ N) A) :=
  keySwap_binds_advantage_bound D H ℓ N Eff A hEff hCR

/-- **(TOOTH — the FLOOR IS LOAD-BEARING.)** On the constant-`0` sponge family collision-resistance
FAILS, so no bound is derivable there — a broken sponge admits a key swap. The floor is a genuine
constraint, exactly as `merkle_ots_binds_index` needs the sponge collision-resistant to forbid the
swap. -/
theorem merkle_ots_binds_floor_load_bearing : ¬ CollisionResistant brokenFamily :=
  brokenFamily_not_CR

/-- **(TOOTH — the ACCEPTANCE side is satisfiable, so the game is not bounding an empty event by
accident.)** The honest signature at any index verifies against the master root — `merkle_ots_correct`,
unconditional. So the win relation's conjuncts 1–3 are reachable and only conjunct 4 (the swap) is what
the floor must forbid. -/
theorem keySwapGame_acceptance_reachable (D : SpongeDeployment) (H : ℤ → ℤ) {ℓ N : ℕ}
    (sks : Fin N → SecretKey ℤ ℓ) (i : Fin N) (m : Fin ℓ → Bool) (t : D.Tag) :
    mverify (D.hashAt t) H (masterKey (D.hashAt t) H sks) m (msign (D.hashAt t) H sks i m) ∧
      (msign (D.hashAt t) H sks i m).openLog = keyLog (D.hashAt t) H sks ∧
      (msign (D.hashAt t) H sks i m).idx = i.val :=
  ⟨merkle_ots_correct (D.hashAt t) H sks i m, rfl, rfl⟩

#assert_all_clean [
  deployedSponge_is_family_instance,
  spongeFamily_CR_of_injective,
  keySwapGame_wins_iff,
  keySwap_wins_imp,
  keySwap_adv_le,
  keySwap_binds_advantage_bound,
  pkEncode_length,
  merkle_ots_binds_from_polyTime,
  spongeFloor_isPolyTime_inhabited,
  merkle_ots_eff_top_false,
  merkle_ots_eff_bot_vacuous,
  the_reduced_keySwap_bound_fires,
  merkle_ots_binds_floor_load_bearing,
  keySwapGame_acceptance_reachable
]

end Dregg2.Crypto.HashSigMerkleRegrounded
