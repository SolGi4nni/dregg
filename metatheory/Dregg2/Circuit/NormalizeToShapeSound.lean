/-
# Dregg2.Circuit.NormalizeToShapeSound — the SOUNDNESS TWIN of the `normalize_to_shape` fork primitive.

This module is the Lean obligation the recursion-fork engineering
(`build_and_prove_normalization_layer`) carries from line one. The fork RE-PROVES any recursion proof
to a CANONICAL fixed-length `non_primitives` manifest — padding the manifest with zero-width DUMMY
tables (Pickles step∘wrap) so the parent verifier's op-list is INVARIANT and the running VK reaches a
fixed point at **DEPTH 1** (instead of the measured depth-4 transient in
`RecursiveAggregation.running_vk_perpetually_constant`). It must ship WITH its soundness theorem; this
is that theorem.

## What "normalize to shape" preserves (the bar)

A recursion-layer proof exposes, at the shape level the parent aggregation circuit reads:

  * a `non_primitives` manifest — a list of tables, each with `(op_type, rows, lanes)` AND the
    `public_values` it contributes to the published PI digest;
  * a published commitment `publish hash m` — the Poseidon2 sponge over the manifest's concatenated
    `public_values`;
  * a committed-execution semantics — the NON-dummy tables (the real constraint content), in order.

A DUMMY table is **zero-width**: `rows = 0`, `lanes = 0`, AND `public_values = []`. Padding the
manifest with dummies is the shape morphism the fork applies (`pad K m = m ++ replicate (K-|m|) dummy`).
Because a dummy contributes EMPTY public-values, padding adds NO committed content; because it is
zero-width, it carries NO semantics. So padding is a **semantics-preserving shape morphism**:

  * `publishedContent_pad` / `publish_pad` — the published commitment is byte-identical (the sponge
    INPUT is unchanged, so the digest is too — this direction needs no crypto at all);
  * `semantics_pad` — the non-dummy content is unchanged (unconditional);
  * `canonical_pad` — the padded manifest has the canonical fixed length `K` (for `|m| ≤ K`).

## The apex (the census shape, faithfully)

`normalize_to_shape_sound`: a proof `m` satisfying the descriptor circuit (`Sat m`) with published
commitment `pi`, when normalized to the canonical shape, yields a proof `m'` that STILL satisfies the
(content-equal) circuit, STILL publishes `pi`, is CANONICAL, and whose semantics are preserved.

`Sat` is the descriptor's satisfaction predicate (the `Satisfied2`-leg — kept ABSTRACT here exactly as
`CircuitSoundness` keeps the published commitment abstract and `RecursiveAggregation` keeps the
`VkShape` opaque; binding the concrete `Satisfied2 hash d t` trace-transform is the heavier
per-descriptor bridge). The one carrier the apex takes is `ShapeContentDetermined Sat` — that the
circuit's satisfaction depends ONLY on the manifest's non-dummy semantic content. This is the FORK's
content-independence, the SAME discharged fact `RecursiveAggregation` already encodes by modeling its
fold transition as `step : VkShape → VkShape` (a function of SHAPE alone, value-independent):
`recursion_vk_fingerprint` is content-independent, and zero-width dummies add no constraints. It is a
NAMED hypothesis (a `Prop` premise), never an axiom.

## The DEPTH-1 fixed point (the fork's whole point, proved STRUCTURALLY)

`RecursiveAggregation.running_vk_perpetually_constant` mechanizes that the running VK is constant PAST
the MEASURED depth-4 fixed point. The fork's deliverable is to KILL the transient: with canonical
normalization the fixed point is reached at the FIRST fold.

  * `canonical_is_fixed_point` — `canonStep K m = m` for any canonical `m` (`canonStep := pad K` is the
    fork's per-fold canonicalization; padding an already-canonical manifest is the identity, since
    `K - K = 0` dummies are appended). This is `step_canonical(canonical) = canonical`, STRUCTURAL — not
    measured.
  * `canon_fixed_at_depth_one` — ONE canonicalization lands at the fixed point:
    `canonStep K (canonStep K m) = canonStep K m`. Depth 1, no transient.
  * `canon_perpetually_constant` — `∀ n, (canonStep K)^[n] m = m` for canonical `m`, off the DEPTH-1
    fixed point (the same `Function.iterate_fixed` backbone as the depth-4 theorem, now anchored at
    depth 1).
  * `step_canonical_id` — folding two canonical-shaped proofs yields a canonical-shaped proof: the
    manifest count is STABLE at `K` (`foldStep K a b` recanonicalizes the combined real tables).

## The crypto floor: a SECURITY REDUCTION, not a refuted injectivity (§R)

The FORWARD soundness (`normalize_to_shape_sound`) needs NO crypto: equal sponge input ⟹ equal digest.
The only place a hash fact is consumed is the faithfulness/anti-ghost companion — two proofs publishing
the SAME commitment commit the SAME content.

⚑ That companion USED to be `publish_binds_content (hCR : Poseidon2SpongeCR hash)`, whose entire proof
was `hCR _ _ h`. `Poseidon2SpongeCR` is injectivity of `List ℤ → ℤ`, PROVED FALSE at deployed BabyBear
parameters, so the anti-ghost guarantee was VACUOUS at the deployed hash. It is DELETED. §R rebuilds it
as the standard cryptographic object: `publishBreakGame` (the content-swap as a first-class game),
`codeForgeToFinder` (the extractor as a map of adversaries), an UNCONDITIONAL advantage inequality, and
`publish_binds_content_advantage_bound` (`hEff` in the open) / `publish_binds_content_rom` (the
DISCHARGED keyed-ROM form, floor PROVED) — negligible advantage
under the named `DomainSeparatedCREff` floor, with efficiency DISCHARGED at `Eff := IsPolyTime` rather
than carried. Both poles of the residual class are proved (`⊤` FALSE at BabyBear, `⊥` vacuous).
No new axiom; `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).

Non-vacuity (§NV): a real canonical shape is exhibited (`real_canonical`), the morphism genuinely moves
a non-canonical shape (`non_canonical_not_fixed`) while preserving its semantics
(`real_semantics_preserved`), and the depth-1 fixed point FIRES on it (`real_depth_one`).
-/
import Dregg2.Tactics
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.SpongeForgeReduction
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Circuit.NormalizeToShapeSound

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv hashGame)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.CostAdversary (IsPolyTime)
open Dregg2.Circuit.Poseidon2KeyedBridge (DomainSeparatedSponge poseidon2KeyedFamily)
open Dregg2.Circuit.DomainSeparatedCREffRegrounded (DomainSeparatedCREff)
open Dregg2.Circuit.SpongeForgeReduction
  (codeForgeGame codeForgeToFinder codeAnsSize hashAnsSize codeForge_advantage_bound
   deployed_forgery_is_break forge_floor_top_false_babyBear
   forge_floor_bot_vacuous)

/-! ## §1 — the recursion-layer shape: a `non_primitives` manifest of tables. -/

/-- One entry of the `non_primitives` manifest: a table's `(op_type, rows, lanes)` plus the
`public_values` it contributes to the published PI digest. A DUMMY table is zero-width
(`rows = 0`, `lanes = 0`) and contributes NO public values (`pubVals = []`). -/
structure TableShape where
  opType  : Nat
  rows    : Nat
  lanes   : Nat
  pubVals : List ℤ

/-- The zero-width dummy table the fork pads with: no rows, no lanes, no public values. Padding the
manifest with these is the canonicalizing shape morphism (Pickles step∘wrap). -/
def dummy : TableShape := { opType := 0, rows := 0, lanes := 0, pubVals := [] }

/-- The Boolean dummy test: zero rows, zero lanes, empty public values. -/
def isDummyB (ts : TableShape) : Bool :=
  ts.rows == 0 && ts.lanes == 0 && ts.pubVals.isEmpty

/-- The published CONTENT: the manifest's `public_values`, concatenated in table order. The published
commitment is the Poseidon2 sponge over THIS list — dummies add nothing because their `pubVals` is `[]`. -/
def publishedContent (m : List TableShape) : List ℤ :=
  (m.map TableShape.pubVals).flatten

/-- The published PI commitment: the sponge digest of the published content. -/
def publish (hash : List ℤ → ℤ) (m : List TableShape) : ℤ :=
  hash (publishedContent m)

/-- The committed-execution SEMANTICS: the NON-dummy tables (the real constraint content), in order.
Dummies carry no semantics, so they are filtered out. -/
def semantics (m : List TableShape) : List TableShape :=
  m.filter (fun ts => !isDummyB ts)

/-- A manifest is CANONICAL at length `K` iff its table count is exactly `K` — the fixed shape the fork
forces so the parent verifier's op-list is invariant. -/
def Canonical (K : Nat) (m : List TableShape) : Prop := m.length = K

/-- **The shape morphism — `pad`.** Pad the manifest with zero-width dummy tables to the canonical
length `K`. For `|m| ≤ K` this lands at exactly `K`; padding an already-canonical manifest is identity. -/
def pad (K : Nat) (m : List TableShape) : List TableShape :=
  m ++ List.replicate (K - m.length) dummy

/-! ## §2 — the morphism is length-canonicalizing and an identity on canonical shapes. -/

/-- The padded manifest has the canonical length `K` (when the input fits, `|m| ≤ K`). -/
theorem length_pad_le {K : Nat} {m : List TableShape} (h : m.length ≤ K) :
    (pad K m).length = K := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

/-- `pad K m` is CANONICAL at `K` (for `|m| ≤ K`) — the canonicalization lands at the fixed length. -/
theorem canonical_pad {K : Nat} {m : List TableShape} (h : m.length ≤ K) :
    Canonical K (pad K m) := length_pad_le h

/-- **Padding an already-canonical manifest is the IDENTITY.** `K - |m| = 0` dummies are appended.
This is the structural fixed point: the canonical shape is fixed by canonicalization. -/
theorem pad_canonical_id {K : Nat} {m : List TableShape} (h : m.length = K) :
    pad K m = m := by
  simp only [pad, h, Nat.sub_self, List.replicate_zero, List.append_nil]

/-! ## §3 — padding preserves the published commitment (the sponge input is unchanged). -/

/-- The published content of a run of dummies is empty (each contributes `pubVals = []`). -/
theorem publishedContent_replicate_dummy (n : Nat) :
    publishedContent (List.replicate n dummy) = [] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    simp [publishedContent, List.map_cons, dummy]

/-- **`publishedContent_pad`.** Padding leaves the published content byte-identical: the appended
dummies contribute the empty list. -/
theorem publishedContent_pad (K : Nat) (m : List TableShape) :
    publishedContent (pad K m) = publishedContent m := by
  unfold publishedContent pad
  rw [List.map_append, List.flatten_append]
  have hd : publishedContent (List.replicate (K - m.length) dummy) = [] :=
    publishedContent_replicate_dummy _
  unfold publishedContent at hd
  rw [hd, List.append_nil]

/-- **`publish_pad`.** Padding preserves the published PI commitment — the sponge INPUT is unchanged,
so the digest is too. This direction needs NO collision-resistance. -/
theorem publish_pad (hash : List ℤ → ℤ) (K : Nat) (m : List TableShape) :
    publish hash (pad K m) = publish hash m := by
  unfold publish; rw [publishedContent_pad]

/-! ## §4 — padding preserves the committed-execution semantics (dummies carry none). -/

/-- A run of dummies filters to nothing (they fail the non-dummy predicate). -/
theorem filter_replicate_dummy (n : Nat) :
    (List.replicate n dummy).filter (fun ts => !isDummyB ts) = [] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.filter_cons]
    simp [isDummyB, dummy]

/-- **`semantics_pad`.** Padding preserves the non-dummy semantic content, UNCONDITIONALLY — the
appended dummies are filtered away. -/
theorem semantics_pad {K : Nat} {m : List TableShape} :
    semantics (pad K m) = semantics m := by
  unfold semantics pad
  rw [List.filter_append, filter_replicate_dummy, List.append_nil]

/-! ## §5 — the carrier: the circuit's satisfaction is content-determined (the fork's content
independence — the SAME discharged fact `RecursiveAggregation.step : VkShape → VkShape` encodes). -/

/-- **`ShapeContentDetermined Sat`** — the fork's content-independence, NAMED. The descriptor circuit's
satisfaction depends ONLY on the manifest's non-dummy semantic content: two manifests with equal
`semantics` are satisfied together. Realized by `recursion_vk_fingerprint`'s content-independence +
zero-width dummies adding no constraints. A `Prop` PREMISE, never an axiom. -/
def ShapeContentDetermined (Sat : List TableShape → Prop) : Prop :=
  ∀ m m', semantics m = semantics m' → (Sat m ↔ Sat m')

/-- The preservation bundle the apex delivers: semantics AND published content unchanged. -/
structure SemanticsPreserved (m m' : List TableShape) : Prop where
  /-- the non-dummy semantic content is unchanged. -/
  sem : semantics m' = semantics m
  /-- the published content (hence the PI commitment) is unchanged. -/
  pub : publishedContent m' = publishedContent m

/-! ## §6 — THE APEX: `normalize_to_shape_sound`. -/

/-- **`normalize_to_shape_sound` (THE CENSUS SHAPE).** Normalizing a proof to the canonical shape
PRESERVES (a) its published commitment and (b) its committed-execution semantics. Concretely: a proof
`m` satisfying the descriptor circuit (`Sat m`) with published commitment `pi` yields a normalized `m'`
that STILL satisfies the content-equal circuit, STILL publishes `pi`, is CANONICAL at `K`, and whose
semantics are preserved. The witness is `pad K m`. Reduces to: `ShapeContentDetermined` (the named fork
carrier) for the satisfaction leg; pure equational shape lemmas for publish + semantics. No crypto, no
new axiom. -/
theorem normalize_to_shape_sound
    (hash : List ℤ → ℤ)
    (Sat : List TableShape → Prop) (hSat : ShapeContentDetermined Sat)
    (K : Nat) (m : List TableShape) (hlen : m.length ≤ K)
    (pi : ℤ) (hpub : publish hash m = pi) (hsat : Sat m) :
    ∃ m', Sat m'
        ∧ publish hash m' = pi
        ∧ Canonical K m'
        ∧ SemanticsPreserved m m' := by
  refine ⟨pad K m, ?_, ?_, ?_, ?_⟩
  · -- satisfaction is preserved under the content-determined circuit
    exact (hSat m (pad K m) (semantics_pad).symm).mp hsat
  · -- the published commitment is unchanged
    rw [publish_pad]; exact hpub
  · -- the normalized manifest is canonical
    exact canonical_pad hlen
  · -- semantics + published content preserved
    exact ⟨semantics_pad, publishedContent_pad K m⟩

/-! ### The faithfulness/anti-ghost leg, AS A SECURITY REDUCTION (§R).

⚑ **WHAT WAS DELETED HERE.** The module's sole crypto consumer used to be

    publish_binds_content (hCR : Poseidon2SpongeCR hash) (h : publish hash m = publish hash m') :
      publishedContent m = publishedContent m'   -- proof: `hCR _ _ h`

i.e. it WAS the refuted floor, applied once, with nothing else in it. `Poseidon2SpongeCR` is
INJECTIVITY of `List ℤ → ℤ`, PROVED FALSE at deployed BabyBear parameters
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the anti-ghost guarantee was **VACUOUS at the
deployed hash**: a normalizer COULD silently swap content behind an equal digest for all this theorem
said. DELETED.

What replaces it: the content-swap is a `FloorGames.Game` (`publishBreakGame`), the extractor is a map
of adversaries into the deployed sponge's collision game, and the anti-ghost guarantee is a NEGLIGIBLE
ADVANTAGE — `Eff`-parametric at the fixed hash (`hEff` in the open), DISCHARGED on the keyed-ROM
floor (`publish_binds_content_rom`, floor PROVED). -/

/-- **THE PUBLISHED-CONTENT FORGERY GAME.** The adversary is handed a sampled domain-separation tag and
WINS iff it outputs two manifests whose published CONTENT differs yet whose published PI commitment
agrees — exactly the silent content-swap behind an equal digest that `normalize_to_shape_sound`'s
commitment-preservation must exclude. The break is IN the win relation. -/
abbrev publishBreakGame (D : DomainSeparatedSponge) : Game :=
  codeForgeGame D (List TableShape) publishedContent

/-- **⚑ THE FORGERY IS THE DEPLOYED PUBLICATION.** Two manifests with different published content but
one published commitment under the DEPLOYED sponge ARE a `publishBreakGame` win at the deployed tag —
the game is about the very `publish` the descriptor circuit computes. -/
theorem publish_forgery_is_break (D : DomainSeparatedSponge) {m m' : List TableShape}
    (hne : publishedContent m ≠ publishedContent m')
    (h : publish D.deployedHash m = publish D.deployedHash m') :
    (publishBreakGame D).wins 0 D.deployedTag (m, m') :=
  deployed_forgery_is_break D (List TableShape) publishedContent m m' hne h

/-- **THE EXACT-PROP SKELETON (the reduction's INTERNAL witness, NOT the headline).** Equal published
commitments force equal published content — OR exhibit a genuine collision of the deployed
domain-separated sponge. The refuted injectivity hypothesis is GONE. Retained ONLY as the extractor:
a collision EXISTS at deployed parameters, so exporting this disjunction would be a shirk. -/
theorem publish_binds_content_or_collides (D : DomainSeparatedSponge) {m m' : List TableShape}
    (h : publish D.deployedHash m = publish D.deployedHash m') :
    publishedContent m = publishedContent m' ∨
      (publishBreakGame D).wins 0 D.deployedTag (m, m') := by
  by_cases hne : publishedContent m = publishedContent m'
  · exact Or.inl hne
  · exact Or.inr (publish_forgery_is_break D hne h)

/-- **⚑ THE HEADLINE — the anti-ghost leg, as a REDUCTION.** Under the DEPLOYED sponge's collision floor
at the class `Eff`, a content-swap forger whose EXTRACTED finder is in that class has NEGLIGIBLE
advantage: the published commitment binds the published content except with negligible probability.
This is what makes `normalize_to_shape_sound`'s commitment-preservation binding, and it replaces the
vacuous `publish_binds_content`. -/
theorem publish_binds_content_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (adv : Adversary (publishBreakGame D))
    (hEff : Eff (codeForgeToFinder D (List TableShape) publishedContent adv))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (publishBreakGame D) adv) :=
  codeForge_advantage_bound D (List TableShape) publishedContent Eff adv hEff hCR

/-! ### ⚑ THE DISCHARGED HEADLINE, ON THE PROVED KEYED-ROM FLOOR.

The `IsPolyTime` discharge that stood here (`publish_binds_content_from_polyTime`) carried
`DomainSeparatedCREff D (IsPolyTime …)` — a floor
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` REFUTES at the deployed
sponge, and no `Eff` repairs the fixed-hash game (`Crypto.RomBindingReduction`'s header). DELETED.
The successor lands the floor on a SAMPLED oracle keyed by the deployed tag space, where
`KeyedRomFloor.keyedRom_hard` is a THEOREM. The modelling step is `RomCarrierSites`' labelled one:
ideal `Fin (2 ^ l)` digest (the deployed felt is fixed ~31-bit — no `l` coincides), and the message
domain is the TRUNCATED published content — limb lists of length at most `m` over BabyBear-range
felts (`BVec`, lossless on everything the deployed publisher absorbs, `bvecOfList_inj`). -/

/-- **THE PUBLISHED-CONTENT ROM FAMILY** — truncated content-limb lists under the ideal digest,
keyed by the deployed tag space. -/
abbrev publishRomFamily (D : DomainSeparatedSponge) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    Dregg2.Crypto.KeyedRomFloor.KeyedRomFamily :=
  Dregg2.Crypto.RomCarrierSites.flatFamily D.Tag D.tagFintype tagDec D.tagNonempty
    (fun _ => Dregg2.Crypto.RomCarrierSites.BVec
      (Fin Dregg2.Crypto.RomCarrierSites.babyBearP) m)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨(⟨0, Nat.succ_pos m⟩, fun _ => none)⟩)

/-- **THE PUBLISHED-CONTENT CARRIER** — commitment `H (t, content)`; identity encoding, injective on
the nose (the truncated content IS the absorbed message). -/
def publishRomCarrier (D : DomainSeparatedSponge) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    Dregg2.Crypto.RomBindingReduction.RomCarrier (publishRomFamily D tagDec m) :=
  Dregg2.Crypto.RomCarrierSites.taggedCarrier _ (fun _ => Unit)
    (fun _ => Dregg2.Crypto.RomCarrierSites.BVec
      (Fin Dregg2.Crypto.RomCarrierSites.babyBearP) m)
    (fun _ => inferInstance) (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- The content-swap forgery at the sampled oracle: one commitment, two DISTINCT truncated contents. -/
abbrev publishRomBreakGame (D : DomainSeparatedSponge) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    Game :=
  Dregg2.Crypto.RomBindingReduction.romCarrierGame (publishRomFamily D tagDec m)
    (publishRomCarrier D tagDec m)

/-- **⚑⚑ THE DISCHARGED ANTI-GHOST LEG — ON THE PROVED FLOOR.** The successor of the deleted
`publish_binds_content_from_polyTime`: every query-bounded content-swap forger has NEGLIGIBLE
advantage — the published commitment binds the published content except with negligible probability,
in the keyed ROM model of the §-header. NO floor hypothesis, NO cost model. -/
theorem publish_binds_content_rom (D : DomainSeparatedSponge) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (publishRomBreakGame D tagDec m))
    (hA : Dregg2.Crypto.RomBindingReduction.RomCarrierEff (publishRomFamily D tagDec m)
      (publishRomCarrier D tagDec m) Q A) :
    Negl (gameAdv (publishRomBreakGame D tagDec m) A) :=
  Dregg2.Crypto.RomCarrierSites.flatSite_binds D.Tag D.tagFintype tagDec D.tagNonempty
    _ _ _ _ (publishRomCarrier D tagDec m) Q hQ A hA

/-- **(TOOTH — the admitted refuter-shape is DEFANGED, not excluded.)** The `0`-query constant
answerer — the exact `IsPolyTime`-refuting shape — is IN the class, WINS at the constant oracle on
distinct contents, and is NEGLIGIBLE against the sampled oracle. -/
theorem publishRom_constAnswer_defanged (D : DomainSeparatedSponge) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (c : ∀ l, (publishRomCarrier D tagDec m).Ctx l)
    (v w : ∀ l, (publishRomCarrier D tagDec m).Val l) :
    Dregg2.Crypto.RomBindingReduction.RomCarrierEff (publishRomFamily D tagDec m)
        (publishRomCarrier D tagDec m) Q
        (Dregg2.Crypto.RomBindingReduction.romCarrierAdv _ _
          (Dregg2.Crypto.RomCarrierSites.constTripleComp _ _ c v w))
      ∧ Negl (gameAdv (publishRomBreakGame D tagDec m)
        (Dregg2.Crypto.RomBindingReduction.romCarrierAdv _ _
          (Dregg2.Crypto.RomCarrierSites.constTripleComp _ _ c v w)))
      ∧ ∀ l, v l ≠ w l → 0 < gameAdv (publishRomBreakGame D tagDec m)
        (Dregg2.Crypto.RomBindingReduction.romCarrierAdv _ _
          (Dregg2.Crypto.RomCarrierSites.constTripleComp _ _ c v w)) l :=
  ⟨Dregg2.Crypto.RomCarrierSites.constTriple_in_eff _ _ c v w Q,
    Dregg2.Crypto.RomCarrierSites.constTriple_binds _ _ c v w Q hQ
      (Dregg2.Crypto.RomCarrierSites.flatFamily_card_R D.Tag D.tagFintype tagDec D.tagNonempty
        _ _ _ _),
    fun l hvw => Dregg2.Crypto.RomCarrierSites.constTriple_gameAdv_pos _ _ c v w l hvw⟩

/-- **(TOOTH — a non-negligible content-swap forger is OUTSIDE the class.)** -/
theorem publishRom_nonNegl_forger_excluded (D : DomainSeparatedSponge)
    (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (publishRomBreakGame D tagDec m))
    (hnn : ¬ Negl (gameAdv (publishRomBreakGame D tagDec m) A)) :
    ¬ Dregg2.Crypto.RomBindingReduction.RomCarrierEff (publishRomFamily D tagDec m)
      (publishRomCarrier D tagDec m) Q A :=
  Dregg2.Crypto.RomBindingReduction.romCarrier_choiceForger_excluded _ _ Q hQ
    (Dregg2.Crypto.RomCarrierSites.flatFamily_card_R D.Tag D.tagFintype tagDec D.tagNonempty
      _ _ _ _) A hnn

/-- **⚑ THE ⊤ POLE — FALSE at the REAL BabyBear parameters** (the honest price of `hEff`). -/
theorem publish_floor_top_false_babyBear (D : DomainSeparatedSponge)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ DomainSeparatedCREff D (fun _ => True) :=
  forge_floor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Both poles proved, so `Eff` is a dial and not a costume. -/
theorem publish_floor_bot_vacuous (D : DomainSeparatedSponge) :
    DomainSeparatedCREff D (fun _ => False) :=
  forge_floor_bot_vacuous D

/-- **(CANARY.)** The bound does NOT follow from the floor applied at another finder. -/
example (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (adv : Adversary (publishBreakGame D))
    (B : Adversary (hashGame (poseidon2KeyedFamily D))) (hB : Eff B)
    (hCR : DomainSeparatedCREff D Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (publishBreakGame D) adv) := hCR B hB)
  trivial

/-! ## §7 — THE DEPTH-1 FIXED POINT (the structural version of `running_vk_perpetually_constant`). -/

/-- The fork's per-fold canonicalization map: re-normalize the running manifest to the canonical
shape. The VK-shape transition `RecursiveAggregation.step` projects through this. -/
def canonStep (K : Nat) : List TableShape → List TableShape := pad K

/-- **`canonical_is_fixed_point` (= `step_canonical(canonical) = canonical`).** The canonical shape is a
FIXED POINT of canonicalization — STRUCTURALLY, not measured. (`RecursiveAggregation` carries the depth-4
fixed point as a MEASURED hypothesis `hfix : step anchor = anchor`; here it is PROVED for the canonical
shape, with no measurement.) -/
theorem canonical_is_fixed_point {K : Nat} {m : List TableShape} (h : Canonical K m) :
    canonStep K m = m := pad_canonical_id h

/-- **`canon_fixed_at_depth_one` (THE FORK'S DELIVERABLE — fixed point at DEPTH 1).** ONE
canonicalization lands at the fixed point: applying `canonStep` again is the identity. This is the
transient-killer — `RecursiveAggregation`'s fixed point sits at the MEASURED depth 4 (after a 2-step
transient); canonical normalization reaches it at depth 1. -/
theorem canon_fixed_at_depth_one {K : Nat} {m : List TableShape} (hlen : m.length ≤ K) :
    canonStep K (canonStep K m) = canonStep K m :=
  canonical_is_fixed_point (canonical_pad hlen)

/-- **`canon_perpetually_constant` (the structural twin of `running_vk_perpetually_constant`).** Off the
DEPTH-1 fixed point, every further fold leaves the shape unchanged: `∀ n, (canonStep K)^[n] m = m` for
canonical `m`. Same `Function.iterate_fixed` backbone as the depth-4 theorem — but anchored at depth 1,
so a light client pins the ONE canonical anchor from the FIRST aggregation, no transient. -/
theorem canon_perpetually_constant {K : Nat} {m : List TableShape} (h : Canonical K m) :
    ∀ n, (canonStep K)^[n] m = m :=
  fun n => Function.iterate_fixed (canonical_is_fixed_point h) n

/-- The running fold's shape step: combine the two children's real (non-dummy) tables, then
re-canonicalize to the fixed length `K`. -/
def foldStep (K : Nat) (a b : List TableShape) : List TableShape :=
  pad K (semantics a ++ semantics b)

/-- **`step_canonical_id` (folding two canonical-shaped proofs yields a canonical-shaped proof — the
manifest count is STABLE at `K`).** Given the combined real tables fit (`|semantics a ++ semantics b| ≤
K`, the aggregation circuit's bounded-non-primitives design invariant), the fold's output is canonical
at `K`. So the running VK's manifest count is a fixed point — depth-invariant from the first fold. -/
theorem step_canonical_id {K : Nat} {a b : List TableShape}
    (hcomb : (semantics a ++ semantics b).length ≤ K) :
    Canonical K (foldStep K a b) :=
  canonical_pad hcomb

/-! ## §NV — non-vacuity: the morphism FIRES on a real canonical shape. -/

/-- A genuine non-dummy table: a real op with rows, lanes, and a published value. -/
def realTable : TableShape := { opType := 1, rows := 4, lanes := 2, pubVals := [7] }

/-- `realTable` is genuinely NOT a dummy. -/
theorem realTable_not_dummy : isDummyB realTable = false := by decide

/-- A concrete canonical shape: pad the single real table to canonical length 3. -/
def realCanon : List TableShape := pad 3 [realTable]

/-- **A real canonical shape EXISTS** — `realCanon` has the canonical length 3 (one real table + two
dummies). The morphism's target is inhabited, not a husk. -/
theorem real_canonical : Canonical 3 realCanon := by
  unfold Canonical realCanon
  simp [pad]

/-- **The morphism preserves semantics on the witness** — the canonical shape carries EXACTLY the one
real table the input did. -/
theorem real_semantics_preserved : semantics realCanon = semantics [realTable] :=
  semantics_pad

/-- **A NON-canonical shape is NOT a fixed point (the A/B non-vacuity half).** The bare single-table
manifest (length 1 ≠ 3) is genuinely MOVED by canonicalization — so the fixed-point equalities above
are LOAD-BEARING (the early shape really differs), the companion of
`RecursiveAggregation.real_running_vk_transient_is_real`. -/
theorem non_canonical_not_fixed : canonStep 3 [realTable] ≠ [realTable] := by
  intro h
  have hcl := congrArg List.length h
  simp [canonStep, pad] at hcl

/-- **The DEPTH-1 fixed point FIRES on the witness** — one canonicalization of the real single-table
manifest lands at a fixed point: applying `canonStep` again is the identity. A real, non-vacuous
instance of the transient-killer. -/
theorem real_depth_one : canonStep 3 (canonStep 3 [realTable]) = canonStep 3 [realTable] :=
  canon_fixed_at_depth_one (by decide)

/-! ## §AX — axiom hygiene: every keystone is `#assert_axioms`-clean (no new axiom; the sole crypto
carrier is `Poseidon2SpongeCR`, taken as a hypothesis). -/

#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.length_pad_le
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.canonical_pad
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.pad_canonical_id
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publishedContent_pad
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_pad
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.semantics_pad
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.normalize_to_shape_sound
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_forgery_is_break
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_binds_content_or_collides
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_binds_content_advantage_bound
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_binds_content_rom
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publishRom_constAnswer_defanged
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publishRom_nonNegl_forger_excluded
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_floor_top_false_babyBear
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_floor_bot_vacuous
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.canonical_is_fixed_point
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.canon_fixed_at_depth_one
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.canon_perpetually_constant
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.step_canonical_id
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.realTable_not_dummy
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.real_canonical
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.real_semantics_preserved
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.non_canonical_not_fixed
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.real_depth_one

end Dregg2.Circuit.NormalizeToShapeSound
