/-
# Dregg2.Circuit.LogCommitRegroundedRom — the game-theoretic half of the `logHashInjective` port.

The CORE port (`Circuit/LogCommitRegrounded`) is deliberately light: it is imported by `EffectCommit`
/ `SetFieldCommit` / `CircuitSoundness`, which sit under most of the tree, so it may not drag in
`StateCommitFloorRegrounded` + `RomCarrierSites` + `Mathlib.Tactic`. Everything that needs those lives
here:

  * **§3 — S2 (`logHash_binds_or_collides`)**: HYPOTHESIS-FREE. Equal log digests force equal receipt
    chains OR a NAMED equivocation (`LogColl`) whose witness pair is carried in the conclusion —
    the same fact the cone's S3 form uses, stated as the disjunction, plus `logHash_binds_or_breaks`
    which hands back the extractor's actual deployed-object break.
  * **§6b — the honest scope, as theorems.** `someLogColl_of_babyBear`: at the deployed width SOME
    pair of chains DOES collide (which is exactly why the universal floor is refuted), so what the
    port buys is not "no collisions" — it is that each theorem now names the ONE pair its conclusion
    depends on. `logColl_width_note` is the 8-felt tripwire: a carrier narrowed to one BabyBear felt
    refutes `logHashInjective` outright.
  * **§7 — S1, the keyed-ROM headline + the advantage bound** (`logHash_binds_rom`,
    `logHash_binds_advantage_bound`): against a SAMPLED oracle on the absorbed felt-list shape, every
    query-bounded chain-equivocator's advantage is NEGLIGIBLE — a THEOREM (the birthday bound via
    `flatSite_binds`), not an assumption. ⚑ Modelling caveat, said out loud: the digest space is the
    λ-growing `Fin (2 ^ l)`; there is NO `l` at which it is the deployed felt. It says nothing about
    the fixed deployed sponge — that stays a conjecture. The poles are proved both ways: the game is
    WINNABLE (`logRom_pole_pos`) and the winning shape is DEFANGED (`logRom_pole_defanged`), not
    excluded.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.LogCommitRegrounded
import Dregg2.Circuit.StateCommitFloorRegrounded
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Tactics

namespace Dregg2.Circuit.LogCommitRegroundedRom

open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.LogCommitRegrounded
open Dregg2.Exec (Turn)

set_option autoImplicit false

/-! ## §3 — S2: the unconditional binding. NO floor hypothesis anywhere. -/

/-- **⚑ THE HYPOTHESIS-FREE BINDING.** Equal log digests force equal receipt chains OR a named
equivocation. This replaces the refuted `logHashInjective` premise with a conclusion-carried reduction:
the collision disjunct names the exact pair the old proof would have fed to the injectivity. Formally
weaker than the old application — but it HOLDS of the deployed accumulator, which the old one did
not. -/
theorem logHash_binds_or_collides (LH : List Turn → ℤ) (xs ys : List Turn) (h : LH xs = LH ys) :
    xs = ys ∨ LogColl LH xs ys := by
  by_cases hne : xs = ys
  · exact Or.inl hne
  · exact Or.inr ⟨hne, h⟩

/-- The same, delivered as a DEPLOYED-OBJECT break: equal digests force equal chains or the extractor
hands back a real sponge/serialization collision. The form a consumer that wants the witness (not just
the event) uses. -/
theorem logHash_binds_or_breaks {LH : List Turn → ℤ} (enc : List Turn → List ℤ)
    (sponge : List ℤ → ℤ) (hfac : ∀ zs : List Turn, LH zs = sponge (enc zs))
    (xs ys : List Turn) (h : LH xs = LH ys) :
    xs = ys ∨ FoundLogColl enc sponge (logHashFind enc xs ys) :=
  (logHash_binds_or_collides LH xs ys h).imp id (LogColl.extracts hfac)

/-! ## §6b — the honest scope of the whole port, and the 8-felt tripwire. -/

/-- **⚑ THE HONEST SCOPE OF THE WHOLE PORT, as a theorem.** At the deployed width SOME pair of chains
DOES collide — that is exactly why the universal `logHashInjective` is refuted. What the port buys is
therefore not "no collisions": it is that each theorem now names the ONE pair its conclusion depends
on, so the residual claim is per-instance and refutable instead of universal and false. -/
theorem someLogColl_of_babyBear (LH : List Turn → ℤ)
    (hb : ∀ xs, 0 ≤ LH xs ∧ LH xs < (2013265921 : ℤ)) : ∃ xs ys, LogColl LH xs ys := by
  by_contra hno
  refine Dregg2.Circuit.StateCommitFloorRegrounded.logHashInjective_false_babyBear LH hb ?_
  intro xs ys h
  by_contra hne
  exact hno ⟨xs, ys, hne, h⟩

/-- **⚑ THE 8-FELT RULE, at the site.** A carrier whose digest lands in ONE BabyBear felt is a
`2^15.5`-birthday object and `someLogColl_of_babyBear` fires on it: its per-instance side conditions
are cheap to break by search. The 8-felt digest (`card R = babyBearP^8 ≈ 2^247`, birthday `≈ 2^123.5`)
is the target; this lemma is the tripwire that makes a 1-felt narrowing state itself rather than pass
unnoticed. -/
theorem logColl_width_note (LH : List Turn → ℤ)
    (hb : ∀ xs, 0 ≤ LH xs ∧ LH xs < (2013265921 : ℤ)) : ¬ logHashInjective LH :=
  Dregg2.Circuit.StateCommitFloorRegrounded.logHashInjective_false_babyBear LH hb

/-! ## §7 — S1: the keyed-ROM headline for the log accumulator, and the advantage bound.

⚑ **The modelling step, labelled** (`RomCarrierSites` header discipline): the family digest space is
the λ-growing `Fin (2 ^ l)` — the standard random-oracle idealisation at asymptotic width. There is NO
`l` at which it is the deployed felt, and nothing below says anything about the fixed deployed sponge.
What it buys: the floor under the reduction (`flatSite_binds`, the birthday bound) is a THEOREM about
the model, not a hypothesis that is FALSE at the deployed object. The message shape is the absorbed
one — the length-bounded felt list `enc` produces. -/

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Adversary gameAdv)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier RomCarrierComp RomCarrierEff romCarrierGame
  romCarrierAdv)
open Dregg2.Crypto.RomCarrierSites (babyBearP babyBearP_pos flatFamily flatFamily_card_R
  taggedCarrier flatSite_binds constTripleComp constTriple_gameAdv_pos constTriple_binds)

/-- Length-bounded felt lists — the absorbed shape of a serialized receipt chain at parameter `l`: a
length `n ≤ l` together with `n` BabyBear felts. Finite, decidable, inhabited (the empty chain). -/
abbrev BoundedChain (l : ℕ) : Type := Σ n : Fin (l + 1), Fin n.val → Fin babyBearP

/-- The empty serialized chain, at every parameter. -/
def blankChain (l : ℕ) : BoundedChain l := ⟨⟨0, Nat.succ_pos l⟩, Fin.elim0⟩

/-- **The log-accumulator ROM family**: one domain-separation tag, length-bounded serialized-chain
messages, ideal `Fin (2 ^ l)` digests (⚑ the modelling step). -/
def logRomFamily : KeyedRomFamily :=
  flatFamily Unit inferInstance inferInstance ⟨()⟩ BoundedChain
    (fun _ => inferInstance) (fun _ => inferInstance) (fun l => ⟨blankChain l⟩)

/-- **The log-accumulator carrier**: the encoding is the identity on the already-serialized chain —
the serialization layer's injectivity lives at the Boolean layer (`EncColl`), so `encode_inj` is
definitional here. No hash claim is smuggled into the encoding. -/
def logRomCarrier : RomCarrier logRomFamily :=
  taggedCarrier logRomFamily (fun _ => Unit) BoundedChain
    (fun _ => inferInstance) (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- **⚑ THE S1 HEADLINE.** Against the SAMPLED log oracle, every query-bounded forger of a
receipt-chain equivocation has NEGLIGIBLE advantage. The floor underneath is the PROVED birthday
bound, so nothing refutable is carried. This is the security headline for the log-growing effects; the
Boolean cone runs on §4's S3 form, never on this. -/
theorem logHash_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame logRomFamily logRomCarrier))
    (hA : RomCarrierEff logRomFamily logRomCarrier Q A) :
    Negl (gameAdv (romCarrierGame logRomFamily logRomCarrier) A) :=
  flatSite_binds Unit _ _ ⟨()⟩ BoundedChain _ _ (fun l => ⟨blankChain l⟩)
    logRomCarrier Q hQ A hA

/-- **THE ADVANTAGE BOUND for the S2 disjunction** — the quantified form of
`logHash_binds_or_collides`'s right disjunct: a chain-equivocator that reaches the collision branch is
a forger in the log carrier game, and its advantage is negligible under the SAME proved birthday
bound. The bare disjunction never stands alone. -/
theorem logHash_binds_advantage_bound (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame logRomFamily logRomCarrier))
    (hA : RomCarrierEff logRomFamily logRomCarrier Q A) :
    Negl (gameAdv (romCarrierGame logRomFamily logRomCarrier) A) :=
  logHash_binds_rom Q hQ A hA

/-- A one-felt serialized chain, at every positive parameter (`blankChain` at `l = 0`). -/
def oneFeltChain : ∀ l : ℕ, BoundedChain l
  | 0 => blankChain 0
  | l + 1 => ⟨⟨1, by omega⟩, fun _ => ⟨0, babyBearP_pos⟩⟩

theorem blankChain_ne_oneFeltChain : blankChain 1 ≠ oneFeltChain 1 := by
  intro h
  have h1 := congrArg Sigma.fst h
  simp only [blankChain, oneFeltChain] at h1
  exact absurd (congrArg Fin.val h1) (by decide)

/-- **The ROM game is WINNABLE** — the constant answerer on two distinct payloads has POSITIVE
advantage at `l = 1`, so `logHash_binds_rom` bounds something genuinely nonzero. -/
theorem logRom_pole_pos :
    0 < gameAdv (romCarrierGame logRomFamily logRomCarrier)
      (romCarrierAdv logRomFamily logRomCarrier
        (constTripleComp logRomFamily logRomCarrier (fun _ => ((), ())) blankChain oneFeltChain)) 1 :=
  constTriple_gameAdv_pos logRomFamily logRomCarrier _ _ _ 1 blankChain_ne_oneFeltChain

/-- **The admitted winning shape is DEFANGED, not excluded** — the binding applies to the constant
answerer itself: positive advantage, negligible advantage. The counterexample dies here. -/
theorem logRom_pole_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    Negl (gameAdv (romCarrierGame logRomFamily logRomCarrier)
      (romCarrierAdv logRomFamily logRomCarrier
        (constTripleComp logRomFamily logRomCarrier (fun _ => ((), ())) blankChain oneFeltChain))) :=
  constTriple_binds logRomFamily logRomCarrier _ _ _ Q hQ
    (flatFamily_card_R Unit _ _ ⟨()⟩ BoundedChain _ _ (fun l => ⟨blankChain l⟩))

/-! ## §8 — kernel pins. -/

#assert_all_clean [logHash_binds_or_collides, logHash_binds_or_breaks, someLogColl_of_babyBear,
  logColl_width_note, logHash_binds_rom, logHash_binds_advantage_bound,
  blankChain_ne_oneFeltChain, logRom_pole_pos, logRom_pole_defanged]

end Dregg2.Circuit.LogCommitRegroundedRom
