/-
# Dregg2.Lightclient.ReceiptChain8 — the receipt-log root that rides the SIGNED anchor, at EIGHT LANES.

THE OBJECT THIS FILE IS ABOUT IS `turn::rotation_witness::iroot`, and the first thing to say is
what that function is NOT.

`rotation_witness.rs`'s header called it "the Rust twin of the Lean MMR whose root `mroot_injective`
makes tamper/truncate/extend/reorder all move (`MMR.lean:313`)", and BOTH halves of that sentence
were false on 2026-08-01:

* **`mroot_injective` does not exist.** It was DELETED on 2026-07-28 (`ed616d24c`) as pigeonhole-false
  — false premise AND false conclusion, see `MMR.lean` §3¼. Its honest successor is
  `MMR.mroot_binds_or_collides`, whose residual `MMR.lean`'s own header prices at **~2^15.5 queries,
  a break, not a bound**.
* **`iroot` is not an MMR.** `Lightclient.MMR` is a peak forest bagged youngest-outward
  (`mroot = bag (peaksOf L)`, a binary carry). `iroot` is a flat LEFT-LEANING CHAIN —
  `root := hash [root, leaf i]` in chronological order. Those are different folds; no theorem about
  one was ever a theorem about the other. The genuine MMR realization lives in `dregg-query/src/mmr.rs`
  (BLAKE3, 32-byte digests) and is a different consumer.

So this module states and proves the binding of **the fold that is actually deployed**, at the width
it must have. It is deliberately NOT a widening of `MMR.lean`: widening a structure the producer does
not emit would have reproduced the very defect being repaired.

## §0 — what was wrong with the width, and what it bought an attacker

The retired producer was, verbatim:

```text
  root : BabyBear := 0
  for (i, rh) in log:                       -- rh : 32 bytes, a TurnReceipt::receipt_hash()
      leaf := hash_many [ i, hash_bytes rh ]     -- hash_bytes : bytes -> ONE felt
      root := hash_many [ root, leaf ]           -- root      :        ONE felt
```

TWO independent one-felt waists, and the OUTER one is not even the cheaper:

* **the leaf preimage** `hash_bytes rh` squeezes a 32-byte receipt hash onto one felt. `log₂ p =
  30.906891`, so a birthday search on THAT alone costs `2^(30.906891/2) = 2^15.4534 ≈ 44,900`
  evaluations. It was MEASURED at **71,133 evaluations / 0.86 s** on one debug-build core
  (`turn/tests/iroot_wide_old_admits_new_rejects.rs`), and a collision there swaps one receipt for a
  DIFFERENT receipt at ANY position of ANY log, leaving the whole fold fixed.
* **the running root** is one felt at every step, so even a leaf-injective encoding would leave the
  fold itself collidable at the same `2^15.45`.

`iroot` is absorbed LAST into `wireCommitR8` / `wire_commit_8_chip`, whose every intermediate carrier
is EIGHT felts. So the deployed chain threaded ~2^123.6 of state and then admitted a ~2^15.5 limb at
its final site. A chain is no stronger than what it absorbs.

⚑ **WHERE THAT REACHED, CONCRETELY.** Not the classical executor path: `state_commit::consensus_ctx`
pins `iroot` to a constant (it was `BabyBear::ZERO`; it is now the domain-separated empty root), so
`TurnReceipt::{pre,post}_state_hash` on the ordinary path does not depend on the receipt log at all.
It reached the **sovereign proof-carrying path**: `sdk::cipherclerk` folds the agent's REAL receipt
chain (`self.receipt_chain.iter().map(|r| r.receipt_hash())`) into `before_w.iroot`/`after_w.iroot`,
those ride the published wide commit PIs, and `executor::atomic.rs:992-993` writes the resulting
commitments STRAIGHT INTO `TurnReceipt::{pre_state_hash, post_state_hash}` — which
`receipt_hash` absorbs and the executor signature signs. Two different receipt histories therefore
produced one byte-identical signed anchor, for ~71k offline Poseidon2 evaluations and no chain
interaction.

## §1 — the number this file delivers, DERIVED

The widened fold is `Digest8`-valued at every step — leaf and root alike — over the deployed
arity-tagged chip absorb. The relevant bound is **COLLISION**, not second-preimage: an MMR/chain root
is a fold over a log, and what an equivocating prover needs is two logs with one root, which is a
birthday event over the image.

```text
  image   = p^8,      p = 2013265921,     log₂ p = 30.906891
  log₂|R| = 8 · 30.906891 = 247.255128 bits
  birthday collision ≈ 2^(247.255128 / 2) = 2^123.627564
```

**2^123.63.** The second-preimage figure for the same object is ~2^247.3 and is NOT the number that
governs here; quoting it would be the flattering half of a pair. The retired object's matching
collision figure is `2^(30.906891/2) = 2^15.45`.

## §2 — the discipline this file is held to (and it is not injectivity)

Every binding here is `binding ∨ Coll8 chipAbsorb8 (the pair a TOTAL extractor returned)`. In
particular:

* **No `Compress8CR` / `Poseidon2SpongeCR` hypothesis anywhere.** Both are PROVED FALSE at deployed
  parameters (`VacuitySweepTeeth.compress8CR_false_babyBear`); a theorem carrying one says nothing
  about the deployed system, which is exactly how `mroot_injective` came to be cited in a Rust header
  for three days after it was deleted.
* **No `∃ a b, a ≠ b ∧ f a = f b` disjunct.** At BabyBear that is unconditionally TRUE by pigeonhole,
  so it would carry no more content than `True`. The disjunct names the SPECIFIC pair the extractor
  hands back.
* **The residual has all four poles** (§5): DECIDABLE, DISCHARGEABLE by the honest prover with no
  cryptographic assumption, REFUTABLE at a colliding chip (so it is not `True` in disguise), and
  REFUTING of `Compress8CR` (so every port is a strict weakening).
* **Width is not the same job as injectivity.** `cells_root`'s key needed an INJECTION (sixteen `u16`
  limbs, `2^256` on the nose) because two distinct ids must not share a leaf AT ALL. This is a HASH
  NODE over a log; it needs collision resistance, priced by the birthday bound over its image. The
  nine-lane key encodings are the wrong tool here and the two numbers do not transfer.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem below.
-/
import Dregg2.Lightclient.MMR
import Dregg2.Circuit.DeployedCapTree

namespace Dregg2.Lightclient.ReceiptChain8

open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8 Compress8CR)

/-! ## §3 — the scheme, the packing, and the two preimage shapes.

ONE carrier: the 8-output arity-tagged chip absorb (`descriptor_ir2::chip_absorb_all_lanes`, all
eight squeezed lanes — the Rust `poseidon2::hash_many_8`). Three preimage LENGTHS ride it and they
are mutually disjoint, so the three domains separate for free with no tag felt:

  * `emptyPre`      — length  2 — the EMPTY-LOG root, domain-tagged;
  * `leafPre i v`   — length  9 — `position ‖ entry8`;
  * `packR8 a b`    — length 16 — `runningRoot8 ‖ leaf8`, the `node8` block.

⚠ **THE EMPTY PREIMAGE IS `[tag, 0]`, NOT `[]`, AND THAT IS A MEASURED CORRECTION.** This file first
used the arity-0 absorb `chipAbsorb8 []`, mirroring `MMR.lean`'s `bag hash [] = hash []`. At the
DEPLOYED instantiation that is degenerate: `poseidon2::hash_many_8` absorbs in rate-4 chunks, and an
EMPTY input has no chunks, so the permutation never runs and lanes 0..3 of the result are literally
ZERO. The empty receipt root would have been a zero sentinel in exactly the lane the wire carries —
the thing the tagged empty root exists to avoid. Caught by
`turn/src/rotation_witness.rs::iroot_binds_the_whole_log`, which asserts the empty root is not zero.
Arity 2 is also an admitted chip arity (`CHIP_ADMITTED_ARITIES = [0,2,3,4,7,11,16]`), so the choice
survives the in-circuit cutover.

⚑ This is STRICTLY better separated than the narrow model it replaces: `MMR.lean`'s `bag`-cons and
`PTree.node` are BOTH arity 2 and are told apart only by position, whereas 2 / 9 / 16 are told apart
by length alone. -/

/-- The receipt-chain hash carrier: the single 8-output chip absorb. ONE field, and it is
INHABITED — no `Compress8CR` field, because a structure carrying a false field is uninhabitable and
every theorem quantifying over it is vacuous (the wound `Cap8Scheme` took and shed). -/
structure RChain8Scheme where
  /-- The 8-output arity-tagged chip absorb (`poseidon2::hash_many_8`). -/
  chipAbsorb8 : List ℤ → Digest8

namespace RChain8Scheme

variable (S8 : RChain8Scheme)

/-- Pack the running 8-felt root and the 8-felt leaf into the arity-16 `node8` input block
`ROOT8 ‖ LEAF8`. -/
def packR8 (l r : Digest8) : List ℤ := List.ofFn l ++ List.ofFn r

/-- `packR8` is injective in both halves — equal lengths split the append uniquely and `List.ofFn`
is injective. -/
theorem packR8_inj {l₁ r₁ l₂ r₂ : Digest8} (h : packR8 l₁ r₁ = packR8 l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  unfold packR8 at h
  have hlen : (List.ofFn l₁).length = (List.ofFn l₂).length := by simp
  obtain ⟨hl, hr⟩ := List.append_inj h hlen
  exact ⟨List.ofFn_inj.mp hl, List.ofFn_inj.mp hr⟩

@[simp] theorem packR8_length (l r : Digest8) : (packR8 l r).length = 16 := by
  simp [packR8]

/-- The EMPTY-LOG domain tag — ASCII `RCE2` ("receipt chain, empty, v2"), the same 4-byte-tag
convention the sibling accumulators use (`FLI2`/`FLN2`/`FLE2`). -/
def rchainEmptyTag : ℤ := 0x52434532

/-- The EMPTY-LOG PREIMAGE — length 2, so it is distinct from a leaf (9) and a node (16) by length
alone, and non-degenerate at the deployed absorb (see the ⚠ in §3). -/
def emptyPre : List ℤ := [rchainEmptyTag, 0]

@[simp] theorem emptyPre_length : emptyPre.length = 2 := rfl

/-- The leaf PREIMAGE — `position ‖ entry8`, length 9. The position felt is what makes a REORDER
move the root even when the multiset of entries is unchanged. -/
def leafPre (i : ℕ) (v : Digest8) : List ℤ := (i : ℤ) :: List.ofFn v

@[simp] theorem leafPre_length (i : ℕ) (v : Digest8) : (leafPre i v).length = 9 := by
  simp [leafPre]

/-- Distinct entries at the same position have distinct leaf PREIMAGES — so a leaf equivocation is
always extractable as a chip collision rather than silently absorbed. -/
theorem leafPre_ne_of_ne {i : ℕ} {v w : Digest8} (h : v ≠ w) : leafPre i v ≠ leafPre i w := by
  intro hc
  exact h (List.ofFn_inj.mp (by simpa [leafPre] using hc))

/-- **THE LEAF** — the 8-felt digest of one log position: `chipAbsorb8 (position ‖ entry8)`. -/
def rleaf8 (i : ℕ) (v : Digest8) : Digest8 := S8.chipAbsorb8 (leafPre i v)

/-! ## §4 — the fold, and the extractor that makes its binding unconditional.

The deployed producer walks the log CHRONOLOGICALLY and folds left. Read from the outside in, that is
exactly a structural recursion on the log REVERSED (youngest-first) — the same shape `MMR.lean`'s
`bag` has, which is what makes the extractor a plain structural walk with no `Classical.choice` and
no well-founded recursion.

`rchainR8` is that recursion; `rchain8` is the chronological wrapper the producer calls. The
`rest.length` in the cons case IS the chronological index of `v`, because `rest` is everything OLDER
than `v`. -/

/-- The fold over a YOUNGEST-FIRST log. Empty ↦ the arity-0 chip image; cons ↦ the arity-16 node over
(older root, this position's leaf). -/
def rchainR8 : List Digest8 → Digest8
  | [] => S8.chipAbsorb8 emptyPre
  | v :: rest => S8.chipAbsorb8 (packR8 (rchainR8 rest) (S8.rleaf8 rest.length v))

/-- **THE ROOT** — the deployed `iroot`, over a CHRONOLOGICAL log (oldest first). -/
def rchain8 (L : List Digest8) : Digest8 := S8.rchainR8 L.reverse

/-- ⚑ **THE EMPTY ROOT IS A CHIP IMAGE, NOT ZERO — and that is a repair, not an incidental.**

The retired producer seeded the fold with `BabyBear::ZERO`, so `iroot [] = 0`. Two costs: the empty
root was not domain-separated from any other accumulator's zero sentinel (every sibling in this tree
— `empty_nullifier_root_8`, `empty_commitments_root_8`, `empty_revoked_root_8` — is deliberately a
DISTINCT tagged image for exactly this reason), and the extractor below could not be TOTAL, because
`0 = chipAbsorb8 (packR8 …)` names no colliding preimage pair. `chipAbsorb8 emptyPre` fixes both.
⚠ And `chipAbsorb8 []` would have fixed only the second — see the ⚠ in §3. -/
theorem rchain8_nil : S8.rchain8 [] = S8.chipAbsorb8 emptyPre := rfl

theorem rchain8_snoc (L : List Digest8) (v : Digest8) :
    S8.rchain8 (L ++ [v]) = S8.chipAbsorb8 (packR8 (S8.rchain8 L) (S8.rleaf8 L.length v)) := by
  simp [rchain8, rchainR8]

/-- **THE COLLISION EXTRACTOR (TOTAL).** The walk the deleted injectivity performed, written as a
FUNCTION over youngest-first logs. Three ways to bottom out, and each one NAMES a preimage pair:

  * one log empty and the other not — length 0 against length 16 IS the collision;
  * the two arity-16 node blocks differ — those blocks ARE the collision;
  * the blocks agree, the older tails agree, but the newest ENTRIES differ — the two arity-9 leaf
    preimages ARE the collision.

Otherwise peel one position and recurse. No search; the branch tests are decidable equalities. -/
def rchainR8Find : List Digest8 → List Digest8 → List ℤ × List ℤ
  | [], [] => (emptyPre, emptyPre)
  | [], (w :: r₂) => (emptyPre, packR8 (S8.rchainR8 r₂) (S8.rleaf8 r₂.length w))
  | (v :: r₁), [] => (packR8 (S8.rchainR8 r₁) (S8.rleaf8 r₁.length v), emptyPre)
  | (v :: r₁), (w :: r₂) =>
      if packR8 (S8.rchainR8 r₁) (S8.rleaf8 r₁.length v)
           ≠ packR8 (S8.rchainR8 r₂) (S8.rleaf8 r₂.length w) then
        (packR8 (S8.rchainR8 r₁) (S8.rleaf8 r₁.length v),
         packR8 (S8.rchainR8 r₂) (S8.rleaf8 r₂.length w))
      else if r₁ ≠ r₂ then rchainR8Find r₁ r₂
      else (leafPre r₁.length v, leafPre r₂.length w)

/-- **⚑ THE BINDING, UNCONDITIONAL (youngest-first form).** Equal roots force equal logs OR the
extractor hands back a genuine collision of the deployed chip. No floor of any kind. -/
theorem rchainR8_binds_or_collides :
    ∀ R₁ R₂ : List Digest8, S8.rchainR8 R₁ = S8.rchainR8 R₂ →
      R₁ = R₂ ∨ Coll8 S8.chipAbsorb8 (S8.rchainR8Find R₁ R₂) := by
  intro R₁
  induction R₁ with
  | nil =>
    intro R₂ h
    cases R₂ with
    | nil => exact Or.inl rfl
    | cons w r₂ =>
      refine Or.inr ?_
      simp only [rchainR8Find]
      refine ⟨?_, h⟩
      intro hc
      have : (2 : ℕ) = 16 := by
        simpa using congrArg List.length hc
      exact absurd this (by decide)
  | cons v r₁ ih =>
    intro R₂ h
    cases R₂ with
    | nil =>
      refine Or.inr ?_
      simp only [rchainR8Find]
      refine ⟨?_, h⟩
      intro hc
      have : (16 : ℕ) = 2 := by
        simpa using congrArg List.length hc
      exact absurd this (by decide)
    | cons w r₂ =>
      by_cases houter :
          packR8 (S8.rchainR8 r₁) (S8.rleaf8 r₁.length v)
            ≠ packR8 (S8.rchainR8 r₂) (S8.rleaf8 r₂.length w)
      · refine Or.inr ?_
        simp only [rchainR8Find, if_pos houter]
        exact ⟨houter, h⟩
      · have hcond := houter
        rw [not_not] at houter
        obtain ⟨hroot, hleaf⟩ := packR8_inj houter
        by_cases hr : r₁ = r₂
        · subst hr
          simp only [rchainR8Find, if_neg hcond, if_neg (by simp : ¬ (r₁ ≠ r₁))]
          by_cases hv : v = w
          · exact Or.inl (by rw [hv])
          · refine Or.inr ⟨leafPre_ne_of_ne hv, hleaf⟩
        · refine Or.inr ?_
          simp only [rchainR8Find, if_neg hcond, if_pos hr]
          exact (ih r₂ hroot).resolve_left hr

/-- The chronological extractor. -/
def rchain8Find (L₁ L₂ : List Digest8) : List ℤ × List ℤ :=
  S8.rchainR8Find L₁.reverse L₂.reverse

/-- **⚑ `rchain8_binds_or_collides` — THE ROOT BINDS THE WHOLE RECEIPT LOG, UNCONDITIONALLY, AT EIGHT
LANES.** Two logs with equal roots are EITHER equal — so a prover cannot keep the published root while
TAMPERING with, TRUNCATING, EXTENDING or REORDERING any receipt position — OR the pair `rchain8Find`
returns is a genuine collision of the deployed 8-output chip absorb, which costs `2^123.63` (§1).

This is the statement `rotation_witness.rs` was citing `mroot_injective` for. That theorem did not
exist, did not cover this fold, and at one felt its conclusion was refutable in 0.86 s. -/
theorem rchain8_binds_or_collides {L₁ L₂ : List Digest8}
    (h : S8.rchain8 L₁ = S8.rchain8 L₂) :
    L₁ = L₂ ∨ Coll8 S8.chipAbsorb8 (S8.rchain8Find L₁ L₂) := by
  rcases rchainR8_binds_or_collides S8 L₁.reverse L₂.reverse h with hr | hc
  · exact Or.inl (by simpa using congrArg List.reverse hr)
  · exact Or.inr hc

/-! ### §4½ — the four ANTI-OMISSION corollaries, spelled out.

`rchain8_binds_or_collides` is the whole content, but the four moves a receipt-log root exists to
refuse are worth naming individually, because these are the sentences the Rust header made and
could not back. Each is the contrapositive at a discharged residual. -/

/-- **TAMPER / TRUNCATE / EXTEND / REORDER all MOVE the root** — stated once, as the contrapositive:
distinct logs have distinct roots unless the named pair genuinely collides. Every one of the four
attacks produces a log distinct from the honest one, so each is refused at `2^123.63`. -/
theorem rchain8_ne_of_ne {L₁ L₂ : List Digest8} (hne : L₁ ≠ L₂)
    (hres : ¬ Coll8 S8.chipAbsorb8 (S8.rchain8Find L₁ L₂)) :
    S8.rchain8 L₁ ≠ S8.rchain8 L₂ :=
  fun h => (rchain8_binds_or_collides S8 h).elim hne hres

/-- A PROPER PREFIX (the truncation attack) is a distinct log whenever something was dropped. -/
theorem rchain8_truncation_moves {L M : List Digest8} (hM : M ≠ [])
    (hres : ¬ Coll8 S8.chipAbsorb8 (S8.rchain8Find (L ++ M) L)) :
    S8.rchain8 (L ++ M) ≠ S8.rchain8 L := by
  refine rchain8_ne_of_ne S8 ?_ hres
  intro hc
  have : L.length + M.length = L.length := by simpa using congrArg List.length hc
  exact hM (List.eq_nil_of_length_eq_zero (by omega))

end RChain8Scheme

/-! ## §5 — the residual, and its four poles.

`RChainColl8` is the ONE named side condition every consumer of §4 carries. It is deliberately the
collision AT THE PAIR the extractor hands back for the two logs in play — not a global floor (refuted)
and not a bare existential (unconditionally true). A side condition that can never fail is `True` in
disguise; one that can never be discharged is a broken keystone. Both are ruled out below. -/

/-- The per-instance residual: the deployed chip genuinely collides at the ONE pair the root
extractor returns for these two receipt logs. -/
def RChainColl8 (S8 : RChain8Scheme) (L₁ L₂ : List Digest8) : Prop :=
  Coll8 S8.chipAbsorb8 (S8.rchain8Find L₁ L₂)

/-- **POLE 1 — DECIDABLE per instance**, which a global injectivity floor never was. -/
instance decidableRChainColl8 (S8 : RChain8Scheme) (L₁ L₂ : List Digest8) :
    Decidable (RChainColl8 S8 L₁ L₂) := by
  unfold RChainColl8
  infer_instance

theorem rchainR8Find_self_eq (S8 : RChain8Scheme) :
    ∀ R : List Digest8, (S8.rchainR8Find R R).1 = (S8.rchainR8Find R R).2 := by
  intro R
  induction R with
  | nil => rfl
  | cons v r _ =>
    simp only [RChain8Scheme.rchainR8Find,
      if_neg (by simp : ¬ (RChain8Scheme.packR8 (S8.rchainR8 r) (S8.rleaf8 r.length v)
        ≠ RChain8Scheme.packR8 (S8.rchainR8 r) (S8.rleaf8 r.length v))),
      if_neg (by simp : ¬ (r ≠ r))]

theorem rchain8Find_self_eq (S8 : RChain8Scheme) (L : List Digest8) :
    (S8.rchain8Find L L).1 = (S8.rchain8Find L L).2 :=
  rchainR8Find_self_eq S8 L.reverse

/-- **POLE 2 — DISCHARGEABLE.** The honest prover, who commits ONE receipt log, discharges the
residual for EVERY chip, with no cryptographic assumption whatsoever. This is precisely what the
deleted floor could never do: `Compress8CR` is unavailable at the deployed chip even to an honest
party, so a keystone conditioned on it was unusable in the direction that matters. -/
theorem rchainColl8_dischargeable (S8 : RChain8Scheme) (L : List Digest8) :
    ¬ RChainColl8 S8 L L :=
  fun hc => hc.1 (rchain8Find_self_eq S8 L)

/-- The constant chip — every input to the all-zero digest. Used ONLY as the refutability canary. -/
def constChip : RChain8Scheme := ⟨fun _ => fun _ => 0⟩

/-- **POLE 3 — REFUTABLE.** At a colliding chip the extractor really does hand back a colliding pair,
so `¬ RChainColl8` is not free and the residual is not `True` in disguise. Two ONE-ENTRY logs whose
entries differ suffice. -/
theorem rchainColl8_refutable :
    RChainColl8 constChip [fun _ => 0] [fun _ => 1] := by
  constructor
  · decide
  · rfl

/-- **POLE 4 — A REFUTATION, NOT A NEW FLOOR.** Exhibiting the residual REFUTES `Compress8CR`
outright, so every consumer of §4 is a strict WEAKENING of the premise it replaces. Stated
contrapositively, so it assumes no floor content. -/
theorem rchainColl8_refutes_compress8CR {S8 : RChain8Scheme} {L₁ L₂ : List Digest8}
    (hc : RChainColl8 S8 L₁ L₂) : ¬ Compress8CR S8.chipAbsorb8 :=
  fun hCR => hc.1 (hCR _ _ hc.2)

/-! ## §6 — ⚑ THE RETIRED ONE-FELT FOLD, AND WHY ITS CONCLUSION IS REFUTED (not only its premise).

`MMR.lean` §3¼ taught the lesson this section applies: **check the CONCLUSION, not only the
hypothesis.** `mroot_injective` was retained for three days as a "strength bridge" after its premise
was refuted, and was then deleted because its CONCLUSION is false at the deployed sponge too.

`rchain1` below is the RETIRED producer, modeled exactly: a zero-seeded left-leaning chain over
one-felt leaves. `rchain1_not_injective_of_leaf_collision` turns ONE sponge collision at two leaf
preimages into a refutation of the property the Rust header asserted — "tamper/truncate/extend/reorder
all move the root". They did not, for `2^15.45`.

⚠ And this understates it. In the deployed composition the log ENTRIES were themselves
`hash_bytes rh` — a 32-byte receipt hash squeezed onto one felt BEFORE reaching the fold — so two
distinct receipts produced a literally IDENTICAL `L`, and no property of the fold could ever have
separated them. That is the collision measured at 71,133 evaluations. Both waists are closed by
`rchain8`: the entry is `Digest8` and every intermediate is `Digest8`. -/

/-- The RETIRED one-felt fold, youngest-first, modeled verbatim (`root := hash [root, leaf]`, seeded
at ZERO, leaves `hash [position, entry]`). -/
def rchainR1 (hash : List ℤ → ℤ) : List ℤ → ℤ
  | [] => 0
  | v :: rest => hash [rchainR1 hash rest, hash [(rest.length : ℤ), v]]

/-- The RETIRED `iroot`, chronological. -/
def rchain1 (hash : List ℤ → ℤ) (L : List ℤ) : ℤ := rchainR1 hash L.reverse

/-- **⚑ ONE LEAF COLLISION REFUTES THE RETIRED FOLD'S EXACT CLAIM.** At any sponge that collides on
two distinct position-0 leaf preimages, the two ONE-ENTRY logs `[a]` and `[b]` are a counterexample to
"distinct logs have distinct roots". This is the sentence `rotation_witness.rs` made, and it was
false of the deployed Poseidon2 at a cost of well under a second. -/
theorem rchain1_not_injective_of_leaf_collision (hash : List ℤ → ℤ) {a b : ℤ}
    (hne : a ≠ b) (hcoll : hash [(0 : ℤ), a] = hash [(0 : ℤ), b]) :
    ¬ (∀ L₁ L₂ : List ℤ, rchain1 hash L₁ = rchain1 hash L₂ → L₁ = L₂) := by
  intro hinj
  have hr : rchain1 hash [a] = rchain1 hash [b] := by
    simp only [rchain1, List.reverse_cons, List.reverse_nil, List.nil_append, rchainR1,
      List.length_nil, Nat.cast_zero, hcoll]
  have := hinj _ _ hr
  exact hne (by simpa using this)

/-- The same collision refutes it at EVERY position and EVERY log length, not only at a one-entry
log — the swap is local, so no amount of surrounding honest history repairs it. -/
theorem rchain1_not_injective_at_depth (hash : List ℤ → ℤ) {a b : ℤ} (older : List ℤ)
    (hne : a ≠ b) (hcoll : hash [(older.length : ℤ), a] = hash [(older.length : ℤ), b]) :
    rchainR1 hash (a :: older) = rchainR1 hash (b :: older) ∧ (a :: older) ≠ (b :: older) := by
  refine ⟨by simp only [rchainR1, hcoll], ?_⟩
  intro hc
  exact hne (by simpa using hc)

/-! ## §7 — NON-VACUITY.

A binding theorem whose fold cannot tell any two logs apart is `True` wearing a disjunction. The
witnesses below are UNCONDITIONAL — none is conditioned on a floor — and they fire at a chip that is
explicitly NOT the deployed one, because the point is that the STRUCTURE separates, independently of
any assumption about Poseidon2. -/

/-- A reference chip that separates by (length, EVERY element) — enough to exhibit the fold moving.
It is not injective and is not claimed to be; it is a probe.

⚠ The first probe written here read only `l.getD i.val 0`, and at lane 0 that is the RUNNING ROOT's
lane 0 — never the leaf. `ref_tamper_moves` and `ref_reorder_moves` came back FALSE, correctly: the
probe could not see the entry at all. A non-vacuity witness that cannot observe the thing it claims
to distinguish is the vacuity it was written to rule out, so the probe folds over the whole list. -/
def refChip : RChain8Scheme :=
  ⟨fun l => fun i => l.foldl (fun acc x => acc * 5 + x) ((l.length : ℤ) + 1) + (i.val : ℤ)⟩

/-- **TAMPER moves the root** — one entry changed, at a fixed length. -/
theorem ref_tamper_moves :
    refChip.rchain8 [fun _ => 5] 0 ≠ refChip.rchain8 [fun _ => 6] 0 := by decide

/-- **EXTEND moves the root** — an appended receipt is visible. -/
theorem ref_extend_moves :
    refChip.rchain8 [fun _ => 5] 0 ≠ refChip.rchain8 [fun _ => 5, fun _ => 6] 0 := by decide

/-- **TRUNCATE moves the root** — dropping the newest receipt is visible (the converse direction of
the same pair, stated separately because truncation is the omission attack a light client actually
faces). -/
theorem ref_truncate_moves :
    refChip.rchain8 [fun _ => 5, fun _ => 6] 0 ≠ refChip.rchain8 [fun _ => 5] 0 := by decide

/-- **REORDER moves the root** — the same multiset of receipts in a different order. This is the one
the POSITION felt in `leafPre` buys; without it the fold would be order-blind at equal length. -/
theorem ref_reorder_moves :
    refChip.rchain8 [fun _ => 5, fun _ => 6] 0 ≠ refChip.rchain8 [fun _ => 6, fun _ => 5] 0 := by
  decide

/-- **THE EMPTY ROOT IS NOT A ZERO SENTINEL.** At the reference chip the empty log's root differs
from a one-entry log's — and, more to the point, it is a chip IMAGE, which is what makes the
extractor total (§4). -/
theorem ref_empty_distinct :
    refChip.rchain8 [] 0 ≠ refChip.rchain8 [fun _ => 0] 0 := by decide

#assert_axioms RChain8Scheme.packR8_inj
#assert_axioms RChain8Scheme.leafPre_ne_of_ne
#assert_axioms RChain8Scheme.rchain8_snoc
#assert_axioms RChain8Scheme.rchainR8_binds_or_collides
#assert_axioms RChain8Scheme.rchain8_binds_or_collides
#assert_axioms RChain8Scheme.rchain8_ne_of_ne
#assert_axioms RChain8Scheme.rchain8_truncation_moves
#assert_axioms rchainR8Find_self_eq
#assert_axioms rchain8Find_self_eq
#assert_axioms rchainColl8_dischargeable
#assert_axioms rchainColl8_refutable
#assert_axioms rchainColl8_refutes_compress8CR
#assert_axioms rchain1_not_injective_of_leaf_collision
#assert_axioms rchain1_not_injective_at_depth
#assert_axioms ref_tamper_moves
#assert_axioms ref_extend_moves
#assert_axioms ref_truncate_moves
#assert_axioms ref_reorder_moves
#assert_axioms ref_empty_distinct

end Dregg2.Lightclient.ReceiptChain8
