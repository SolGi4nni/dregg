/-
# Market.DarkBazaarCollectiveOpening — the Tier-0 NO-SINGLE-VIEWER piece (roadmap 3.3):
# the COLLECTIVE opening is sound, and it hides from every (n−1)-coalition.

**What this file is for.** The apex relation (`Market.DarkBazaarSameOpening.SameOpening`) and its
crypto core (`Market.DarkBazaarDecryptConsistency`) are stated over ONE phase — as if a single
holder of the secret key decrypted. The deployed system has NO such holder: the collective secret
is `s = Σ sᵢ` over n parties and is NEVER assembled (`fhegg-fhe/src/threshold.rs`: each party
partial-decrypts `hᵢ = sᵢ·c1 + eᵢ`, combine sums `c0' = c0 + Σ hᵢ`). This file states and proves,
in the same scalar `Bfv` phase model:

  1. **`CollectiveOpensTo`** — the collective decryption (the sum of the n party partial-phases,
     combined with the public component) opens the ciphertext to `m`: the collective analogue of
     `BfvOpensTo`, and DEFINITIONALLY `DecryptConsistent` at the combined phase
     (`collective_is_decryptConsistent`, `collective_is_bfvOpensTo` — both `Iff.rfl`, so the
     collective relation is the apex relation's shape, not a parallel construction).
  2. **`collective_decrypt_unique`** — the collective form still UNIQUELY determines `m` under the
     noise bound, by composing `DarkBazaarDecryptConsistency.decryptConsistent_unique` over the
     summed shares. `collective_decrypts`: the unique message is what the REAL decoder computes on
     the combined phase (the threshold.rs combine→scale→round path). `collective_book_unique`:
     one transcript, one ORDER BOOK.
  3. **The no-single-viewer link** (`CoalitionViewHides`) — an (n−1)-coalition's residual view of
     the honest party's share, WITH smudging at the `Bfv.Smudging` bound, is statistically
     near-independent of the book (`≤ 2^-48` on the deployed numbers) — stated as a relation and
     discharged by INSTANTIATING `Bfv.Smudging.deployed_smudge_hides` / `partial_decrypt_hides`
     (the connection is proved; smudging is NOT re-proved here).
  4. **FAILING SIDES, all proved:**
     * `single_tampered_share_breaks_opening` — combine is BLIND to share validity: ONE party
       shifting its share by `Δ·k` retargets the collective opening to `m + k`, and uniqueness then
       REFUSES `m`. Malicious-share validity (roadmap 3.2) is an open obligation as a THEOREM.
     * `coalitionViewHides_fails_below_floor` — below the smudge bound the hiding RELATION is
       FALSE for every ε < 1, witnessed on the real descriptor books (`fixtureWitness` vs
       `tamperedOrderWitness`) — the collective mirror of `deployed_smudge_floor_leaks`.
     * `coalition_decoder_recovers_book` — the leak is CONSTRUCTIVE: under a sub-bound smudge an
       explicit coalition decoder returns the true book (hence `packedBook`, hence every order)
       from every positive-probability observation. `no_smudge_coalition_distinguishes_books`:
       with NO smudge, any two distinct noise fingerprints are distinguished with certainty.

## The model, honest (what IS and is NOT proved)

  * **Scalar phase model**, inherited from `Bfv.Noise`/`Bfv.Smudging`: one integer phase per
    coefficient, ℤ not mod-q. Same NAMED gaps, not widened. `keyTerm i` models the party's RNS
    key term `sᵢ·c1`; that the real `(c0, c1)` has this RLWE shape under the collective key is
    beyond the phase model (same residual as the SameOpeningGadget names).
  * **The collective secret is never assembled, in-model:** no definition below ever forms
    `Σ sᵢ` as any party's possession. The key terms cancel only inside the PUBLIC combine sum
    (`combine_cancels_keys`), which is the n-of-n structure.
  * **What "independent of m" means, precisely.** The coalition channel proved here is the NOISE
    channel of a published honest share: the fold noise of the encrypted book is a book-dependent
    fingerprint, and smudging floods it (this is exactly `Bfv.Smudging`'s coalition model, at the
    book level). The DIRECT `Δ·m` channel for a sub-quorum coalition (no honest share published)
    is masked by the missing key term `sₙ·c1` — that is RLWE hardness, class B, an estimator
    artifact and NEVER a Lean theorem (`Bfv.Smudging` scope note). Stated, not smuggled.
  * **Per-coefficient, per-share:** transcript-wide composition (4096 coefficients × parties ×
    sessions) is `Bfv.Smudging`'s §6 `TranscriptHybridLedger` — referenced, not re-proved, and
    its hybrid-certificate obligation is NOT discharged here.
-/
import Bfv.Noise
import Bfv.Smudging
import Market.DarkBazaarDecryptConsistency
import Market.DarkBazaarSameOpening
import Dregg2.Tactics

namespace Market.DarkBazaarCollectiveOpening

open Bfv Bfv.Smudging Market.DarkBazaarPrivateDescriptor
open Market.DarkBazaarDecryptConsistency Market.DarkBazaarSameOpening

set_option autoImplicit false

/-! ## 1. The collective objects: combine, and the collective opening relation. -/

/-- The threshold combine, phase model: the public component plus the SUM of the n party
partial-phases (`threshold.rs`: `c0' = c0 + Σ hᵢ`). No individual share is privileged; no
assembled secret appears. -/
def combinePhase {n : ℕ} (c0 : ℤ) (shares : Fin n → ℤ) : ℤ :=
  c0 + ∑ i, shares i

/-- **COLLECTIVE-OPENS-TO** — the collective decryption opens the ciphertext to `m`: the combined
phase is decrypt-consistent at `m`. This is the collective analogue of `BfvOpensTo`, defined
THROUGH the proven core relation so the two stories cannot drift. -/
def CollectiveOpensTo (P : Params) {n : ℕ} (c0 : ℤ) (shares : Fin n → ℤ) (m : ℤ) : Prop :=
  DecryptConsistent P (combinePhase c0 shares) m

/-- The collective relation IS the core relation at the combined phase — definitional. -/
theorem collective_is_decryptConsistent (P : Params) {n : ℕ} (c0 : ℤ) (shares : Fin n → ℤ)
    (m : ℤ) :
    CollectiveOpensTo P c0 shares m ↔ DecryptConsistent P (combinePhase c0 shares) m :=
  Iff.rfl

/-- The collective relation IS the apex file's `BfvOpensTo` on the combined-phase ciphertext —
definitional. So everything the apex/`SameOpening` layer proves about `BfvOpensTo` applies to
the collective decrypt verbatim; the collective form is a refinement, not a fork. -/
theorem collective_is_bfvOpensTo (P : Params) {n : ℕ} (c0 : ℤ) (shares : Fin n → ℤ) (m : ℤ) :
    CollectiveOpensTo P c0 shares m ↔ BfvOpensTo P ⟨combinePhase c0 shares⟩ m :=
  Iff.rfl

/-! ## 2. Uniqueness: the collective decrypt is as sound as the single-key decrypt. -/

/-- **THE COLLECTIVE KEYSTONE — the collective form still uniquely determines `m`.** One combined
transcript cannot safely open to two messages: `decryptConsistent_unique` composed over the summed
shares. The n-of-n split costs NOTHING in decrypt soundness. -/
theorem collective_decrypt_unique {P : Params} {n : ℕ} {c0 : ℤ} {shares : Fin n → ℤ}
    {m m₂ : ℤ} (h : CollectiveOpensTo P c0 shares m) (h₂ : CollectiveOpensTo P c0 shares m₂) :
    m = m₂ :=
  decryptConsistent_unique h h₂

/-- The unique collective message is what the REAL decoder returns on the combined phase — the
`threshold.rs` combine-then-`decryptPhase` path, via `decryptConsistent_decrypts`. -/
theorem collective_decrypts {P : Params} {n : ℕ} {c0 : ℤ} {shares : Fin n → ℤ}
    (m : ℕ) (hm : m < P.t) (h : CollectiveOpensTo P c0 shares (m : ℤ)) :
    decryptPhase P (combinePhase c0 shares) = m :=
  decryptConsistent_decrypts m hm h

/-- One collective transcript, one ORDER BOOK: a combined phase that safely opens to two packed
books forces the same orders (through the real 28-bit injective packing). Exactly the
well-definedness `SameOpening` needs, now for the collective decrypt. -/
theorem collective_book_unique {P : Params} {n : ℕ} {c0 : ℤ} {shares : Fin n → ℤ}
    {w w₂ : PrivateWitness}
    (h : CollectiveOpensTo P c0 shares (packedBook w))
    (h₂ : CollectiveOpensTo P c0 shares (packedBook w₂)) :
    w.orders = w₂.orders :=
  packedBook_openings_agree h h₂

/-! ## 3. GREEN — the honest n-of-n transcript opens, and on the deployed numbers it decrypts. -/

/-- The honest n-party transcript, phase model: message `m`, ciphertext (fold) noise `eCt`, each
party's key term (`sᵢ·c1` in the RNS machine) and smudge. The public component `c0` carries the
key MASK `− Σ keyTerm` — the model shape of an encryption under the collective key. No field
holds an assembled secret. -/
structure HonestTranscript (P : Params) (n : ℕ) where
  /-- The plaintext the ciphertext carries (packed book / clearing output). -/
  m : ℕ
  /-- The ciphertext noise (the fold envelope's `e_ct`). -/
  eCt : ℤ
  /-- Party `i`'s key term (`sᵢ·c1`): the coalition-unpredictable mask contribution. -/
  keyTerm : Fin n → ℤ
  /-- Party `i`'s smudging noise (deployed sampler: uniform on `[-2^80, 2^80]`). -/
  smudge : Fin n → ℤ

/-- The public component under the collective key: `Δ·m + eCt − Σᵢ keyTerm i`. -/
def HonestTranscript.c0 {P : Params} {n : ℕ} (t : HonestTranscript P n) : ℤ :=
  (P.Δ : ℤ) * t.m + t.eCt - ∑ i, t.keyTerm i

/-- Party `i`'s published partial decryption: `hᵢ = keyTermᵢ + smudgeᵢ` (threshold.rs share). -/
def HonestTranscript.share {P : Params} {n : ℕ} (t : HonestTranscript P n) (i : Fin n) : ℤ :=
  t.keyTerm i + t.smudge i

/-- **The n-of-n cancellation**: the combine sums the key terms away EXACTLY — the combined phase
is `Δ·m + (eCt + Σ smudge)`, with no key term surviving and no assembled secret ever formed. This
is the structural fact that makes the collective decrypt a `DecryptConsistent` instance. -/
theorem combine_cancels_keys {P : Params} {n : ℕ} (t : HonestTranscript P n) :
    combinePhase t.c0 t.share = (P.Δ : ℤ) * t.m + (t.eCt + ∑ i, t.smudge i) := by
  unfold combinePhase HonestTranscript.c0 HonestTranscript.share
  rw [Finset.sum_add_distrib]
  ring

/-- GREEN (non-vacuity): the honest transcript satisfies `CollectiveOpensTo` whenever its total
noise (fold noise + all smudges) is inside the margin. -/
theorem honest_collective_opens {P : Params} {n : ℕ} (t : HonestTranscript P n)
    (hsafe : SafeNoise P |t.eCt + ∑ i, t.smudge i|) :
    CollectiveOpensTo P t.c0 t.share (t.m : ℤ) :=
  ⟨t.eCt + ∑ i, t.smudge i, hsafe, combine_cancels_keys t⟩

/-- Triangle over the share sum: n per-party bounds give an `n·S` sum bound. -/
theorem abs_sum_le_card_mul {n : ℕ} (f : Fin n → ℤ) (S : ℤ) (h : ∀ i, |f i| ≤ S) :
    |∑ i, f i| ≤ (n : ℤ) * S :=
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, S := Finset.sum_le_sum fun i _ => h i
    _ = (n : ℤ) * S := by
        simp [Finset.sum_const, Finset.card_univ]

/-- **Deployed GREEN pin (opens)**: 16 parties on the real fhe.rs degree-4096 numbers — fold
noise inside the `2^32` envelope, every smudge inside the `2^80` bound — satisfy
`CollectiveOpensTo`. The margin fact is `Bfv.Smudging.deployed_smudge_margin` (kernel-checked on
the 109-bit `q`), so the hiding-level smudge and collective-opening correctness hold at the SAME
deployed parameters. -/
theorem deployed_honest_collective_opens (t : HonestTranscript fheRs4096 16)
    (he : |t.eCt| ≤ 2 ^ 32) (hu : ∀ i, |t.smudge i| ≤ 2 ^ 80) :
    CollectiveOpensTo fheRs4096 t.c0 t.share (t.m : ℤ) := by
  apply honest_collective_opens
  have hsum : |∑ i, t.smudge i| ≤ ((16 : ℕ) : ℤ) * 2 ^ 80 :=
    abs_sum_le_card_mul t.smudge (2 ^ 80) hu
  have habs : |t.eCt + ∑ i, t.smudge i| ≤ 2 ^ 32 + 16 * 2 ^ 80 := by
    have h1 : |t.eCt + ∑ i, t.smudge i| ≤ |t.eCt| + |∑ i, t.smudge i| := abs_add_le _ _
    have h2 : ((16 : ℕ) : ℤ) * 2 ^ 80 = 16 * 2 ^ 80 := by norm_num
    linarith [h1, h2 ▸ hsum]
  refine SafeNoise.mono ?_ (marginHolds_safe fheRs4096 1
    (2 ^ 32 + Bfv.Smudging.maxPartiesPinned * Bfv.Smudging.smudgeBound)
    Bfv.Smudging.deployed_smudge_margin)
  simp only [Bfv.Smudging.maxPartiesPinned, Bfv.Smudging.smudgeBound, Bfv.Smudging.smudgeBits]
  push_cast
  linarith [habs]

/-- **Deployed GREEN pin (decrypts)**: the same 16-party honest transcript DECRYPTS to exactly
`m` through the real decoder — `combine_cancels_keys` chained with
`Bfv.Smudging.deployed_smudged_decrypt_exact` (the correctness jaw of the smudging vise). Hiding
at `2^80` and collective exact decryption are simultaneously live, per-transcript. -/
theorem deployed_honest_collective_decrypts (t : HonestTranscript fheRs4096 16)
    (hm : t.m < fheRs4096.t)
    (he : |t.eCt| ≤ 2 ^ 32) (hu : ∀ i, |t.smudge i| ≤ 2 ^ 80) :
    decryptPhase fheRs4096 (combinePhase t.c0 t.share) = t.m := by
  rw [combine_cancels_keys]
  apply Bfv.Smudging.deployed_smudged_decrypt_exact t.m t.eCt (∑ i, t.smudge i) hm he
  have hsum : |∑ i, t.smudge i| ≤ ((16 : ℕ) : ℤ) * 2 ^ 80 :=
    abs_sum_le_card_mul t.smudge (2 ^ 80) hu
  have hcast : ((Bfv.Smudging.maxPartiesPinned : ℤ) * (Bfv.Smudging.smudgeBound : ℤ))
      = ((16 : ℕ) : ℤ) * 2 ^ 80 := by
    simp only [Bfv.Smudging.maxPartiesPinned, Bfv.Smudging.smudgeBound, Bfv.Smudging.smudgeBits]
    push_cast
  rwa [← hcast] at hsum

/-! ## 4. RED — combine is BLIND to share validity (roadmap 3.2, as a theorem). -/

/-- Party `i₀`'s share shifted by `δ`; every other share untouched. -/
def tamperedShares {n : ℕ} (shares : Fin n → ℤ) (i₀ : Fin n) (δ : ℤ) : Fin n → ℤ :=
  fun j => shares j + if j = i₀ then δ else 0

/-- The combine sees exactly the shift: tampering one share by `δ` moves the combined phase
by `δ`. -/
theorem tampered_combine {n : ℕ} (c0 : ℤ) (shares : Fin n → ℤ) (i₀ : Fin n) (δ : ℤ) :
    combinePhase c0 (tamperedShares shares i₀ δ) = combinePhase c0 shares + δ := by
  unfold combinePhase tamperedShares
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i₀ (fun _ => δ)]
  simp only [Finset.mem_univ, if_true]
  ring

/-- **RED — a single malicious share retargets the collective opening.** If the honest transcript
opens to `m`, then ONE party shifting its share by `Δ·k` produces a transcript that (a) opens to
`m + k` with the SAME noise, and (b) provably does NOT open to `m` (uniqueness refuses). Combine
sums shares blindly; nothing in the collective decrypt authenticates a share. Malicious-share
validity (VSS / share same-opening — roadmap 3.2) is a REAL open obligation, here as a theorem
with a failing side, not prose. -/
theorem single_tampered_share_breaks_opening {P : Params} {n : ℕ} {c0 : ℤ}
    {shares : Fin n → ℤ} {m : ℤ} (i₀ : Fin n) (k : ℤ) (hk : k ≠ 0)
    (h : CollectiveOpensTo P c0 shares m) :
    CollectiveOpensTo P c0 (tamperedShares shares i₀ ((P.Δ : ℤ) * k)) (m + k)
      ∧ ¬ CollectiveOpensTo P c0 (tamperedShares shares i₀ ((P.Δ : ℤ) * k)) m := by
  obtain ⟨e, he, hp⟩ := h
  have hshift : CollectiveOpensTo P c0 (tamperedShares shares i₀ ((P.Δ : ℤ) * k)) (m + k) :=
    ⟨e, he, by rw [tampered_combine, hp]; ring⟩
  refine ⟨hshift, fun hbad => ?_⟩
  have := collective_decrypt_unique hbad hshift
  omega

/-! ## 5. The NO-SINGLE-VIEWER link: the coalition view hides the book — at the Smudging bound,
and provably NOT below it.

The coalition model is `Bfv.Smudging`'s (its §model note): an (n−1)-coalition knowing the
candidate plaintext computes the honest party's share up to `secret + smudge`; the residual
observable is distributed as `shareMass S (pub + secret)`. At the COLLECTIVE level the secret
residual is the fold noise of the encrypted book — a book-dependent fingerprint (`foldNoise` below
is universally quantified: the hiding holds for EVERY such channel inside the envelope). The
DIRECT `Δ·m` channel of a sub-quorum view is masked by the missing key term — RLWE, class B,
NAMED as out of scope (never a Lean theorem). -/

/-- **The coalition-view hiding relation**: with smudge radius `S` and noise envelope `B`, every
book-noise channel inside the envelope presents, for every pair of candidate books, coalition
views within `ε` statistical distance. This is the (n−1)-coalition "~independent of `m`"
statement, as a relation with real parameters — it can FAIL (and provably does, below the
bound). -/
def CoalitionViewHides (S : ℕ) (B : ℤ) (ε : ℚ) : Prop :=
  ∀ (pub : ℤ) (foldNoise : PrivateWitness → ℤ), (∀ v, |foldNoise v| ≤ B) →
    ∀ w w' : PrivateWitness,
      Bfv.Smudging.sd S (pub + foldNoise w) (pub + foldNoise w') ≤ ε

/-- The general bound: any smudge radius `S` against any envelope `B` hides the book channel to
`2B/(2S+1)` — `Bfv.Smudging.partial_decrypt_hides` instantiated at the collective book level
(the connection theorem; smudging not re-proved). -/
theorem coalition_view_hides_of_bound (S : ℕ) (B : ℤ) :
    CoalitionViewHides S B (2 * (B : ℚ) / (2 * (S : ℚ) + 1)) :=
  fun pub foldNoise henv w w' =>
    Bfv.Smudging.partial_decrypt_hides S pub (foldNoise w) (foldNoise w') B (henv w) (henv w')

/-- **NO-SINGLE-VIEWER, deployed**: at the `Bfv.Smudging` bound (`S = 2^80`) against the deployed
fold envelope (`B = 2^32`), the coalition's residual views under ANY two candidate books are
within `2^-48` — statistically near-independent of the book. Direct instantiation of
`Bfv.Smudging.deployed_smudge_hides`. -/
theorem deployed_coalition_view_hides :
    CoalitionViewHides Bfv.Smudging.smudgeBound Bfv.Smudging.deployedCtNoise (1 / 2 ^ 48) :=
  fun pub foldNoise henv w w' =>
    Bfv.Smudging.deployed_smudge_hides pub (foldNoise w) (foldNoise w') (henv w) (henv w')

/-- Books really do differ on the deployed fixtures (kernel-evaluated): the leak witnesses below
are two DISTINCT real books, not a degenerate pair. -/
theorem deployed_fixture_books_differ :
    packedBook tamperedOrderWitness ≠ packedBook fixtureWitness := by decide

/-- **RED (required failing side) — below the bound, the hiding RELATION is FALSE.** For EVERY
`ε < 1`, a `2^15` smudge against the deployed `2^32` envelope refutes `CoalitionViewHides`:
witnessed by the real descriptor books (`fixtureWitness` vs `tamperedOrderWitness`) under an
in-envelope noise channel separating them, where the coalition views sit at distance EXACTLY 1
(`Bfv.Smudging.deployed_smudge_floor_leaks`, mirrored at the collective level). Without the
smudge bound the no-single-viewer property is not degraded but GONE. -/
theorem coalitionViewHides_fails_below_floor (ε : ℚ) (hε : ε < 1) :
    ¬ CoalitionViewHides (2 ^ 15) Bfv.Smudging.deployedCtNoise ε := by
  intro h
  have hne : packedBook tamperedOrderWitness ≠ packedBook fixtureWitness :=
    deployed_fixture_books_differ
  have henv : ∀ v : PrivateWitness,
      |(if packedBook v = packedBook fixtureWitness then (0 : ℤ) else 2 ^ 32)|
        ≤ Bfv.Smudging.deployedCtNoise := by
    intro v
    unfold Bfv.Smudging.deployedCtNoise
    split <;> norm_num
  have hb := h 0 (fun v => if packedBook v = packedBook fixtureWitness then (0 : ℤ) else 2 ^ 32)
    henv fixtureWitness tamperedOrderWitness
  rw [if_pos rfl, if_neg hne] at hb
  have hleak := Bfv.Smudging.deployed_smudge_floor_leaks 0
  simp only [zero_add] at hb hleak
  rw [hleak] at hb
  linarith

/-- **With NO smudging the fingerprint is exposed EXACTLY**: any two books whose noise
fingerprints differ at all are distinguished with certainty (`sd = 1`) at smudge radius 0. -/
theorem no_smudge_coalition_distinguishes_books (pub : ℤ) (foldNoise : PrivateWitness → ℤ)
    (w w' : PrivateWitness) (hne : foldNoise w ≠ foldNoise w') :
    Bfv.Smudging.sd 0 (pub + foldNoise w) (pub + foldNoise w') = 1 := by
  apply Bfv.Smudging.smudge_too_small_leaks
  have heq : (pub + foldNoise w) - (pub + foldNoise w') = foldNoise w - foldNoise w' := by ring
  rw [heq]
  have hd : foldNoise w - foldNoise w' ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (1 : ℤ) ≤ |foldNoise w - foldNoise w'| := by
    rcases lt_or_gt_of_ne hd with hlt | hgt
    · rw [abs_of_neg hlt]; omega
    · rw [abs_of_pos hgt]; omega
  simpa using h1

/-- The coalition's explicit book decoder against an under-smudged share: if the observation lands
in candidate `w`'s support interval, answer `w`, else `w'`. -/
def coalitionDecode (S : ℕ) (pub : ℤ) (foldNoise : PrivateWitness → ℤ)
    (w w' : PrivateWitness) (x : ℤ) : PrivateWitness :=
  if x ∈ Bfv.Smudging.supp S (pub + foldNoise w) then w else w'

/-- **RED, constructive — the (n−1)-coalition RECOVERS the book.** When the smudge interval is
smaller than the fingerprint gap, `coalitionDecode` returns the TRUE book on EVERY observation of
positive probability — whichever of the two candidates the transcript actually encrypts. The
recovered witness carries `packedBook` and every private order: this is full plaintext recovery
through the noise channel, not a distinguishing bit. (Engine: `smudge_too_small_distinguishes` —
the supports are disjoint, so one observation determines the secret.) -/
theorem coalition_decoder_recovers_book (S : ℕ) (pub : ℤ) (foldNoise : PrivateWitness → ℤ)
    (w w' : PrivateWitness)
    (hgap : 2 * (S : ℤ) + 1 ≤ |(pub + foldNoise w) - (pub + foldNoise w')|) :
    (∀ x : ℤ, Bfv.Smudging.shareMass S (pub + foldNoise w) x ≠ 0 →
        coalitionDecode S pub foldNoise w w' x = w)
    ∧ (∀ x : ℤ, Bfv.Smudging.shareMass S (pub + foldNoise w') x ≠ 0 →
        coalitionDecode S pub foldNoise w w' x = w') := by
  constructor
  · intro x hx
    have hmem : x ∈ Bfv.Smudging.supp S (pub + foldNoise w) := by
      by_contra hxm
      exact hx (by simp [Bfv.Smudging.shareMass, hxm])
    simp [coalitionDecode, hmem]
  · intro x hx
    have hnot : x ∉ Bfv.Smudging.supp S (pub + foldNoise w) := by
      intro hxm
      have hmass : Bfv.Smudging.shareMass S (pub + foldNoise w) x ≠ 0 := by
        simp only [Bfv.Smudging.shareMass, if_pos hxm]
        exact inv_ne_zero (by positivity : (0 : ℚ) < 2 * (S : ℚ) + 1).ne'
      exact hx (Bfv.Smudging.smudge_too_small_distinguishes S _ _ x hgap hmass)
    simp [coalitionDecode, hnot]

/-- The deployed floor-leak pair lives INSIDE the legitimate envelope: fingerprints `0` and
`2^32` are both admissible deployed fold noises, and at the `2^15` floor their coalition views
are at distance exactly 1 — the leak cannot be dismissed as an out-of-envelope pathology. -/
theorem deployed_floor_leak_in_envelope :
    |(0 : ℤ)| ≤ Bfv.Smudging.deployedCtNoise
      ∧ |(2 ^ 32 : ℤ)| ≤ Bfv.Smudging.deployedCtNoise
      ∧ ∀ pub : ℤ, Bfv.Smudging.sd (2 ^ 15) (pub + 0) (pub + 2 ^ 32) = 1 := by
  refine ⟨by norm_num [Bfv.Smudging.deployedCtNoise],
    by norm_num [Bfv.Smudging.deployedCtNoise], fun pub => ?_⟩
  simpa using Bfv.Smudging.deployed_smudge_floor_leaks pub

/-! ## 6. NAMED, not proved (the honest boundary — none of these are faked above)

  1. **Malicious-share validity** (roadmap 3.2). `single_tampered_share_breaks_opening` PROVES
     combine is blind to share validity; what is open is the fix — a malicious-secure share
     validity proof (VSS / same-opening between live shares and commitments, attributable
     refusal). Nothing here authenticates a share.
  2. **Distributed witness production** (roadmap 3.3). `CollectiveOpensTo` covers the collective
     DECRYPT; collaborative PROVING so that no single prover reconstructs the book (the
     share-native backend, corrupt-partial-fold attribution) is untouched here.
  3. **RLWE masking of the direct channel.** The sub-quorum coalition's inability to read `Δ·m`
     out of `c0` without the missing key term is RLWE hardness — class B, an estimator artifact,
     never a Lean theorem (`Bfv.Smudging` scope). The theorems above are the NOISE-channel
     statement plus per-transcript soundness; they do not claim computational hiding.
  4. **Scalar model, per-coefficient, per-share** — inherited from `Bfv.Noise`/`Bfv.Smudging`
     (ℤ-phase not mod-q, no polynomial ring, the mbfv view reduction is a model step). Transcript-
     wide accounting is `Bfv.Smudging.TranscriptHybridLedger`; its hybrid certificate for the
     real RLWE/RNS transcript remains the named missing bridge, and nothing here discharges it.
  5. **`keyTerm`/`c0` shape.** That the real `(c0, c1)` is a well-formed encryption under the
     collective key with short randomness is the SameOpeningGadget's named collective-key
     residual — the model ASSUMES the shape for the GREEN side only (the REDs and uniqueness do
     not depend on it).
-/

#assert_all_clean [Market.DarkBazaarCollectiveOpening.collective_is_decryptConsistent,
  Market.DarkBazaarCollectiveOpening.collective_is_bfvOpensTo,
  Market.DarkBazaarCollectiveOpening.collective_decrypt_unique,
  Market.DarkBazaarCollectiveOpening.collective_decrypts,
  Market.DarkBazaarCollectiveOpening.collective_book_unique,
  Market.DarkBazaarCollectiveOpening.combine_cancels_keys,
  Market.DarkBazaarCollectiveOpening.honest_collective_opens,
  Market.DarkBazaarCollectiveOpening.deployed_honest_collective_opens,
  Market.DarkBazaarCollectiveOpening.deployed_honest_collective_decrypts,
  Market.DarkBazaarCollectiveOpening.single_tampered_share_breaks_opening,
  Market.DarkBazaarCollectiveOpening.coalition_view_hides_of_bound,
  Market.DarkBazaarCollectiveOpening.deployed_coalition_view_hides,
  Market.DarkBazaarCollectiveOpening.deployed_fixture_books_differ,
  Market.DarkBazaarCollectiveOpening.coalitionViewHides_fails_below_floor,
  Market.DarkBazaarCollectiveOpening.no_smudge_coalition_distinguishes_books,
  Market.DarkBazaarCollectiveOpening.coalition_decoder_recovers_book,
  Market.DarkBazaarCollectiveOpening.deployed_floor_leak_in_envelope]

end Market.DarkBazaarCollectiveOpening
