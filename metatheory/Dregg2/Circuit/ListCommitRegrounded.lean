/-
# Dregg2.Circuit.ListCommitRegrounded — the `ListDigestBindsList` endpoint, re-grounded.

`ListCommit.ListDigestBindsList` concludes `xs = ys` from TWO carried ∀-injectivities:
`compressNInjective cN` (an infinite-domain injectivity into ONE felt — FALSE at deployed BabyBear
parameters, the refuted floor) and `listLeafInjective LE`. Every theorem that threads those binders is
conditional on a refuted premise. This module is the S2/S3 port of that endpoint, plus the keyed-ROM
S1 headline:

  * **S2 (`listDigest_binds_or_collides`)** — HYPOTHESIS-FREE: equal digests force equal lists OR a
    NAMED collision (`ListColl`) whose witness pair is carried in the conclusion. The extractor is
    total and trivial here: the colliding `cN` pair IS `(xs.map LE, ys.map LE)`; the colliding leaf
    pair is extracted by `LeafColl.extracts`. Distinctness is part of the collision predicate, so
    `¬ ListColl` can never be trivially true on a genuine equivocation.
  * **S3 (`listDigest_binds_of_noColl` / `_of_noCNColl` / `_of_noLeafColl`)** — the SAME conclusion
    as the old endpoint, with the refuted universal replaced by a per-instance, refutable side
    condition about ONE named pair. These are what the mechanical cone port (`Tools/ConePort`)
    re-points threaders onto. HONEST-BUT-CONDITIONAL: at 1-felt widths the side condition is a
    ~2^15.5-breakable claim about the deployed hash at these named points — visible, refutable,
    never universal.
  * **No strength lost** (`listDigest_binds_of_carriers`): the old endpoint's exact statement is the
    injective special case of the port. What is given up is only the pretence that the deployed
    sponge satisfies the injectivity.
  * **S1 (`listDigestRom_binds`)** — the keyed-ROM headline for the list sponge: over a SAMPLED
    oracle on length-bounded felt-lists, every query-bounded forger's advantage is NEGLIGIBLE — a
    THEOREM (the birthday bound via `keyedRom_hard`), not an assumption. ⚑ Modelling caveat, said
    out loud (the `RomCarrierSites` header discipline): the digest space is the λ-growing
    `Fin (2 ^ l)`; there is NO `l` at which it is the deployed ~31-bit BabyBear felt. This says
    nothing about the fixed deployed sponge — that stays a conjecture.

Teeth: `canary_drop_moves_digest_or_collides` (the left disjunct BITES — no collision available at
the named points, so S2 genuinely forces inequality of digests), `listDigest_binds_unconditional_false`
(the side condition is LOAD-BEARING: dropping it is refuted), `listColl_refutable` /
`noColl_satisfiable` (the new predicate is refutable AND satisfiable — the `demoRoot_CR`/`badRoot_not_CR`
witness-pair shape), `listRom_pole_pos` / `listRom_pole_defanged` (the ROM game is winnable and the
winning shape is defanged, not excluded).

No `sorry`, no `axiom`, no `native_decide`; `decide` only on concrete closed instances.
-/
import Dregg2.Circuit.ListCommit
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Tactics

namespace Dregg2.Circuit.ListCommitRegrounded

open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.ListCommit

set_option autoImplicit false

universe u

/-! ## §1 — the NAMED collision events (the S2 raw material). Distinctness is INSIDE the
predicate, so the side condition `¬ Coll` is never satisfied vacuously by an equal pair. -/

/-- **`CNColl LE cN xs ys`** — the two mapped leaf-lists are a GENUINE collision of the list sponge
`cN`: distinct inputs, equal digests. The extractor for this event is the identity — the colliding
pair IS `(xs.map LE, ys.map LE)`, named in the predicate. -/
def CNColl {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ) (xs ys : List α) : Prop :=
  xs.map LE ≠ ys.map LE ∧ cN (xs.map LE) = cN (ys.map LE)

/-- **`LeafColl LE xs ys`** — the lists differ but their leaf images agree: a genuine collision of
the leaf encoder `LE`, at list granularity (`LeafColl.extracts` names the colliding element pair). -/
def LeafColl {α : Type u} (LE : α → ℤ) (xs ys : List α) : Prop :=
  xs ≠ ys ∧ xs.map LE = ys.map LE

/-- **`ListColl LE cN xs ys`** — a `listDigest` equivocation at `(xs, ys)` broke ONE of the two
deployed objects: the sponge or the leaf encoder. -/
def ListColl {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ) (xs ys : List α) : Prop :=
  CNColl LE cN xs ys ∨ LeafColl LE xs ys

/-- The `CNColl` pair is a genuine `cN` collision (distinctness is intrinsic). -/
theorem CNColl.extracts {α : Type u} {LE : α → ℤ} {cN : List ℤ → ℤ} {xs ys : List α}
    (h : CNColl LE cN xs ys) : ∃ a b : List ℤ, a ≠ b ∧ cN a = cN b :=
  ⟨xs.map LE, ys.map LE, h.1, h.2⟩

private theorem map_eq_of_ne_extracts {α : Type u} {LE : α → ℤ} :
    ∀ (xs ys : List α), xs ≠ ys → xs.map LE = ys.map LE → ∃ x y, x ≠ y ∧ LE x = LE y
  | [], [], hne, _ => absurd rfl hne
  | [], _ :: _, _, hmap => by simp at hmap
  | _ :: _, [], _, hmap => by simp at hmap
  | x :: xs, y :: ys, hne, hmap => by
    simp only [List.map_cons, List.cons.injEq] at hmap
    by_cases hxy : x = y
    · subst hxy
      exact map_eq_of_ne_extracts xs ys (fun h => hne (by rw [h])) hmap.2
    · exact ⟨x, y, hxy, hmap.1⟩

/-- The `LeafColl` event yields a NAMED element-level collision of `LE`: two distinct leaves with
equal encodings. Without this, `¬ LeafColl` could be mistaken for content it does not have. -/
theorem LeafColl.extracts {α : Type u} {LE : α → ℤ} {xs ys : List α}
    (h : LeafColl LE xs ys) : ∃ x y, x ≠ y ∧ LE x = LE y :=
  map_eq_of_ne_extracts xs ys h.1 h.2

/-- The umbrella extraction: a `ListColl` is a genuine collision of ONE of the two deployed
objects. -/
theorem ListColl.extracts {α : Type u} {LE : α → ℤ} {cN : List ℤ → ℤ} {xs ys : List α}
    (h : ListColl LE cN xs ys) :
    (∃ a b : List ℤ, a ≠ b ∧ cN a = cN b) ∨ (∃ x y, x ≠ y ∧ LE x = LE y) :=
  h.elim (fun hc => Or.inl hc.extracts) (fun hl => Or.inr hl.extracts)

/-! ## §2 — S2: the unconditional trichotomy. NO floor hypothesis anywhere. -/

/-- **⚑ THE HYPOTHESIS-FREE BINDING (`_or_collides`).** Equal list digests force equal lists OR a
named collision. This replaces `ListDigestBindsList`'s refuted `compressNInjective` premise with a
conclusion-carried reduction: the collision disjunct names the exact pair the old proof would have
fed to the injectivity. Formally weaker than the old endpoint — but it HOLDS of the deployed sponge,
which the old one did not. -/
theorem listDigest_binds_or_collides {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ)
    (xs ys : List α) (h : listDigest LE cN xs = listDigest LE cN ys) :
    xs = ys ∨ ListColl LE cN xs ys := by
  by_cases hmap : xs.map LE = ys.map LE
  · by_cases hxy : xs = ys
    · exact Or.inl hxy
    · exact Or.inr (Or.inr ⟨hxy, hmap⟩)
  · exact Or.inr (Or.inl ⟨hmap, h⟩)

/-! ## §3 — S3: the conclusion-stable restorations. The SAME conclusion as the old endpoint; the
refuted ∀-injectivity binder is swapped for a per-instance `¬ Coll` about ONE named pair. Three
variants, one per pattern of which of the two old binders was floor-carried at a use site. -/

/-- **S3, both carriers floor-borne** — replaces `(hN : compressNInjective cN)` AND
`(hLE : listLeafInjective LE)` with one refutable side condition. -/
theorem listDigest_binds_of_noColl {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ)
    (xs ys : List α) (hno : ¬ ListColl LE cN xs ys)
    (h : listDigest LE cN xs = listDigest LE cN ys) : xs = ys :=
  (listDigest_binds_or_collides LE cN xs ys h).resolve_right hno

/-- **S3, sponge-side only** — for sites whose leaf injectivity is a PROVED lemma (e.g.
`noteLeaf_injective : Nat.cast` is genuinely injective), only the sponge floor is replaced. -/
theorem listDigest_binds_of_noCNColl {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ)
    (hLE : listLeafInjective LE) (xs ys : List α) (hno : ¬ CNColl LE cN xs ys)
    (h : listDigest LE cN xs = listDigest LE cN ys) : xs = ys := by
  rcases listDigest_binds_or_collides LE cN xs ys h with heq | hcn | ⟨hne, hmap⟩
  · exact heq
  · exact absurd hcn hno
  · exact absurd (List.map_injective_iff.mpr hLE hmap) hne

/-- **S3, leaf-side only** — the dual, for a site with a genuinely proved sponge injectivity (e.g. a
positional Horner fold) but a floor-borne leaf encoder. -/
theorem listDigest_binds_of_noLeafColl {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (xs ys : List α) (hno : ¬ LeafColl LE xs ys)
    (h : listDigest LE cN xs = listDigest LE cN ys) : xs = ys := by
  rcases listDigest_binds_or_collides LE cN xs ys h with heq | hcn | hlf
  · exact heq
  · exact absurd (hN _ _ hcn.2) hcn.1
  · exact absurd hlf hno

/-! ## §4 — no strength lost: the old endpoint is the injective special case of the port. -/

/-- The carried injectivities kill both collision disjuncts. -/
theorem noColl_of_carriers {α : Type u} {LE : α → ℤ} {cN : List ℤ → ℤ}
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (xs ys : List α) :
    ¬ ListColl LE cN xs ys := by
  rintro (⟨hne, heq⟩ | ⟨hne, hmap⟩)
  · exact hne (hN _ _ heq)
  · exact hne (List.map_injective_iff.mpr hLE hmap)

/-- **The deleted-shape bridge**: `ListDigestBindsList`'s exact statement, re-derived THROUGH the
port. Nothing genuinely proved was given up — only the pretence that the deployed sponge satisfies
`compressNInjective`. Deliberately a standalone bridge, never a hypothesis on a keystone. -/
theorem listDigest_binds_of_carriers {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (xs ys : List α)
    (h : listDigest LE cN xs = listDigest LE cN ys) : xs = ys :=
  listDigest_binds_of_noColl LE cN xs ys (noColl_of_carriers hN hLE xs ys) h

/-! ## §4b — the CUTOVER bridges. After the in-place cutover
(`Tools/ConeCutover` + `Tools/ConeCutoverListCommit`) a threader that STILL carries the refuted
floor binder discharges its callee's per-instance side condition through exactly one of these.
That makes the remaining floor use UNIFORM: every not-yet-ported consumer's floor flows into ONE
bridge application, so the NEXT cone level is portable by ConePort with the single bridge
`AppRule` (`orig := noCNColl_of_inj, repl := noCNColl_self` — the composition rule that closes
the level-2 gap), never a per-theorem rule table. -/

/-- Sponge-side bridge: the (refuted) universal injectivity kills the per-instance `CNColl`.
Instance args implicit so a rewired call site is exactly `(noCNColl_of_inj hN)`. -/
theorem noCNColl_of_inj {α : Type u} {LE : α → ℤ} {cN : List ℤ → ℤ}
    (hN : compressNInjective cN) {xs ys : List α} : ¬ CNColl LE cN xs ys :=
  fun hc => hc.1 (hN _ _ hc.2)

/-- The identity carrier for the bridge's side condition — the constant-headed replacement the
ConePort `AppRule` shape needs so a level-2 threader's `noCNColl_of_inj hN` application can be
mechanically rewritten into a passed-through `hno` binder. -/
theorem noCNColl_self {α : Type u} {LE : α → ℤ} {cN : List ℤ → ℤ} {xs ys : List α}
    (hno : ¬ CNColl LE cN xs ys) : ¬ CNColl LE cN xs ys := hno

/-- The `ListColl` twin of `noCNColl_self`, for sites bridged by `noColl_of_carriers`. -/
theorem noListColl_self {α : Type u} {LE : α → ℤ} {cN : List ℤ → ℤ} {xs ys : List α}
    (hno : ¬ ListColl LE cN xs ys) : ¬ ListColl LE cN xs ys := hno

/-! ## §5 — TEETH: the port is not vacuous, the side condition is load-bearing, refutable, and
satisfiable. Concrete carriers: the injective `Nat` leaf + the positional Horner fold (the same
demo pair `ListCommit` §3 uses), and a CONSTANT sponge as the refuted pole. -/

private def leafD : Nat → ℤ := fun n => (n : ℤ)
private def cND : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000000 + x) (xs.length : ℤ)
private def constCN : List ℤ → ℤ := fun _ => 0

/-- **The side condition is SATISFIABLE** at deployed-shaped instances: no collision at these two
named points of the Horner sponge. (`demoRoot_CR` half of the witness pair.) -/
theorem noColl_satisfiable : ¬ ListColl leafD cND [7, 1] [7, 3, 1] := by
  unfold ListColl CNColl LeafColl
  decide

/-- **The side condition is REFUTABLE** — at a constant sponge the collision event FIRES. The new
predicate commits to something that a bad instantiation genuinely violates (`badRoot_not_CR` half). -/
theorem listColl_refutable : ListColl leafD constCN [0] [1] :=
  Or.inl ⟨by decide, rfl⟩

/-- **⚑ THE LEFT DISJUNCT BITES** (the `canary_tamper_moves_commit8_or_collides` shape): at the
named points there is no collision available, so S2 forces a DROP to move the digest — the gate
genuinely rejects, with no injectivity floor anywhere in the argument. -/
theorem canary_drop_moves_digest_or_collides :
    listDigest leafD cND [7, 1] ≠ listDigest leafD cND [7, 3, 1] := by
  intro h
  rcases listDigest_binds_or_collides leafD cND _ _ h with heq | hcoll
  · exact absurd heq (by decide)
  · exact absurd hcoll noColl_satisfiable

/-- **⚑ THE SIDE CONDITION IS LOAD-BEARING** — the S3 statement with `hno` DELETED is FALSE (at the
constant sponge every digest collides). A ported theorem that dropped the side condition would not
be a port; it would be refuted. This is the mutation canary for the whole S3 family. -/
theorem listDigest_binds_unconditional_false :
    ¬ ∀ (xs ys : List Nat),
        listDigest leafD constCN xs = listDigest leafD constCN ys → xs = ys := by
  intro hall
  exact absurd (hall [0] [] rfl) (by decide)

/-! ## §6 — S1: the keyed-ROM headline for the list sponge.

⚑ **The modelling step, labelled** (`RomCarrierSites` header discipline): the family digest space is
the λ-growing `Fin (2 ^ l)` — the standard random-oracle idealisation at asymptotic width. There is
NO `l` at which it is the deployed ~31-bit BabyBear felt, and nothing below says anything about the
fixed deployed sponge. What it buys: the floor under the reduction (`keyedRom_hard`, the birthday
bound) is a THEOREM about the model, not a hypothesis that is false at the deployed object. The
message shape is the length-`≤ l` felt-list — the leaf-encoded absorbed shape of `listDigest`; a
query-bounded forger emits polynomially many felts, so the bound is part of the same idealisation. -/

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier RomCarrierComp RomCarrierEff romCarrierGame
  romCarrierAdv)
open Dregg2.Crypto.RomCarrierSites (babyBearP flatFamily flatFamily_card_R taggedCarrier
  flatSite_binds constTripleComp constTriple_gameAdv_pos constTriple_binds)

/-- Length-bounded felt lists — the absorbed message shape at parameter `l`: a length `n ≤ l`
together with `n` BabyBear felts. Finite, decidable, inhabited (the empty list). -/
abbrev BoundedFeltList (l : ℕ) : Type := Σ n : Fin (l + 1), Fin n.val → Fin babyBearP

/-- The empty felt-list, at every parameter. -/
def blankFelts (l : ℕ) : BoundedFeltList l := ⟨⟨0, Nat.succ_pos l⟩, Fin.elim0⟩

/-- **The list-sponge ROM family**: one tag, length-bounded felt-list messages, ideal `Fin (2 ^ l)`
digests (⚑ the modelling step). -/
def listRomFamily : KeyedRomFamily :=
  flatFamily Unit inferInstance inferInstance ⟨()⟩ BoundedFeltList
    (fun _ => inferInstance) (fun _ => inferInstance) (fun l => ⟨blankFelts l⟩)

/-- **The list-sponge carrier**: the encoding is the identity on the leaf-encoded list — the leaf
layer's injectivity lives at the Boolean layer (`LeafColl`), so `encode_inj` is definitional here.
No hash claim is smuggled into the encoding. -/
def listRomCarrier : RomCarrier listRomFamily :=
  taggedCarrier listRomFamily (fun _ => Unit) BoundedFeltList
    (fun _ => inferInstance) (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- **⚑ THE S1 HEADLINE (`listDigestRom_binds`).** Against the SAMPLED list-sponge oracle, every
query-bounded forger of a list-digest equivocation has NEGLIGIBLE advantage. The floor underneath is
`keyedRom_hard` — a PROVED birthday bound — so nothing refutable is carried. This is the security
headline for the ~12 list-side-table effects; the Boolean cone runs on §3's S3 forms, never on
this. -/
theorem listDigestRom_binds (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame listRomFamily listRomCarrier))
    (hA : RomCarrierEff listRomFamily listRomCarrier Q A) :
    Negl (gameAdv (romCarrierGame listRomFamily listRomCarrier) A) :=
  flatSite_binds Unit _ _ ⟨()⟩ BoundedFeltList _ _ (fun l => ⟨blankFelts l⟩)
    listRomCarrier Q hQ A hA

/-- A one-felt list, at every positive parameter (`blankFelts` at `l = 0`). -/
def oneFelt : ∀ l : ℕ, BoundedFeltList l
  | 0 => blankFelts 0
  | l + 1 => ⟨⟨1, by omega⟩, fun _ => ⟨0, Dregg2.Crypto.RomCarrierSites.babyBearP_pos⟩⟩

theorem blankFelts_ne_oneFelt : blankFelts 1 ≠ oneFelt 1 := by
  intro h
  have h1 := congrArg Sigma.fst h
  simp only [blankFelts, oneFelt] at h1
  exact absurd (congrArg Fin.val h1) (by decide)

/-- **The ROM game is WINNABLE** — the constant answerer on two distinct payloads has POSITIVE
advantage at `l = 1`, so `listDigestRom_binds` bounds something genuinely nonzero. -/
theorem listRom_pole_pos :
    0 < gameAdv (romCarrierGame listRomFamily listRomCarrier)
      (romCarrierAdv listRomFamily listRomCarrier
        (constTripleComp listRomFamily listRomCarrier (fun _ => ((), ())) blankFelts oneFelt)) 1 :=
  constTriple_gameAdv_pos listRomFamily listRomCarrier _ _ _ 1 blankFelts_ne_oneFelt

/-- **The admitted winning shape is DEFANGED, not excluded** — the binding applies to the constant
answerer itself: positive advantage, negligible advantage. The counterexample dies here. -/
theorem listRom_pole_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    Negl (gameAdv (romCarrierGame listRomFamily listRomCarrier)
      (romCarrierAdv listRomFamily listRomCarrier
        (constTripleComp listRomFamily listRomCarrier (fun _ => ((), ())) blankFelts oneFelt))) :=
  constTriple_binds listRomFamily listRomCarrier _ _ _ Q hQ
    (flatFamily_card_R Unit _ _ ⟨()⟩ BoundedFeltList _ _ (fun l => ⟨blankFelts l⟩))

/-! ## §7 — kernel pins. -/

#assert_all_clean [listDigest_binds_or_collides, listDigest_binds_of_noColl,
  listDigest_binds_of_noCNColl, listDigest_binds_of_noLeafColl, listDigest_binds_of_carriers,
  noCNColl_of_inj, noCNColl_self, noListColl_self,
  ListColl.extracts, canary_drop_moves_digest_or_collides, listDigest_binds_unconditional_false,
  listDigestRom_binds, listRom_pole_pos, listRom_pole_defanged]

end Dregg2.Circuit.ListCommitRegrounded
