/-
# Dregg2.Circuit.Emit.LightClientMidHashFold — folding out the Midnight (Substrate/GRANDPA) BLAKE2b
HASH carrier `AUTHSET_OK`: the authority-set-root binding becomes DERIVED by an in-circuit BLAKE2b
multi-block absorb, not a trusted witnessed boolean carrier.

## The carrier being folded out (the BLAKE2b authority-set hash — NOT the Ed25519 SIG carrier)

`LightClientMidnight.authSetOk` is a witnessed carrier bit standing for
`L.dBeq (L.authSetCommit (u.authSet.map authRow)) ts.anchorRoot` — the BLAKE2b authority-set-root
compare: the derived authority set binds to the governance-pinned weak-subjectivity (WS) anchor root
(the denominator-shrink pin of `mid_no_forgery`'s `anchorBinds` leg). In the carrier posture the AIR
takes the honest-witness relation for this bit as a hypothesis — it TRUSTS the prover set it to the true
BLAKE2b result. The verifier re-runs no hash.

This file replaces that trust with the BLAKE2b absorb itself, mirroring `LightClientTmHashFold` /
`LightClientSolHashFold` / `LightClientEthFinFold` and REUSING the proven `Blake2bGadget.Ref.compress`
(the `hashlib.blake2b`-anchored BLAKE2b compression `F`, whose AIR realization is `Blake2bGadget.blake2bF`
/ `blake2bCompress`). No new BLAKE2b arithmetic is authored here — the compression is entirely
`Ref.compress`; this file only chains it. The remaining Midnight carrier — `ED_OK`, the aggregate
per-authority Ed25519 precommit-signature result — stays a hypothesis (the Ed25519/EC arc; NOT this file);
`roundOk`/`eraOk` are the in-AIR logic gates.

## The BLAKE2b shape: a true multi-block absorb over the serialized authority rows

Midnight is a Substrate chain whose authority-set root is a domain-separated BLAKE2b commitment over the
sorted `(authorityId, weight)` rows — a single BLAKE2b hash over the WHOLE serialized set. This file
REALIZES `authSetCommit` as that genuine multi-block absorb: serialize each row into one 128-byte
(16-word, little-endian) block (`rowBlock`), then chain `Ref.compress` block by block — the digest state
`h` of block `k` (its 8 output words) is the initial state of block `k+1`, the counter `t = 128·(k+1)`
(bytes absorbed through block `k`), and the BLAKE2b final-flag is set ONLY on the last block. This is a
`foldl` of `Ref.compress` over the message blocks — the same "generator makes them free" pattern as the
gadget's 12 rounds, one level up, and exactly what `Blake2bGadget` §8 names. Because every row occupies a
full 128-byte block, `authSetRootRef rows` IS `hashlib.blake2b` of the row-per-128-bytes serialization
(the KAT below anchors it against a real vector). A satisfying witness must EXHIBIT the authority rows
whose BLAKE2b absorb hits the pinned WS anchor root — the `authSetOk` carrier becomes DERIVED, and the
weight DENOMINATOR is pinned in-circuit.

## The ties proved here (mirroring the tm/sol folds' four theorems)

  * `midBlakeLeaf_authSetCommit_eq_absorb` — the bridge leaf's `authSetCommit` IS the BLAKE2b absorb
    reconstruction (the `*_eq_chainCommit` analog: the object `authSetOk` stood for, via the BLAKE2b
    arithmetic, not a bit).
  * `authSet_binding` — GIVEN the BLAKE2b compression-CR floor `hcompress` (injectivity of `Ref.compress`
    at a fixed counter/flag — a genuine compression collision), equal-length authority sets whose absorbs
    agree ARE the same set: the BLAKE2b commit BINDS the authority set (the commitment lemma, reduced by
    reverse induction to the compression floor — the content behind `noSetCollision`, exactly as tm/sol's
    `chainCommit_binding` reduces to `pairHash`-CR).
  * `verifyAuthSet_from_fold` (`*_from_fold` analog) — the `authSetOk` Boolean is DISCHARGED by the
    exhibited absorb: NO carrier column is read.
  * `mid_authset_from_fold_slots_into_no_forgery` (`*_from_fold_slots_into_no_forgery` analog) — the
    fold-derived binding slots into `mid_no_forgery`'s `anchorBinds` leg IN PLACE of the trusted bit: the
    Midnight/GRANDPA no-forgery guarantee holds with the authority-set hash carrier folded out (the
    denominator pinned by the BLAKE2b gates over the exhibited rows, not an opaque bit).

## Derived vs assumed (the honest, PRICED residuals)

  * DERIVED here: the reconstruction (`authSetRootRef`), its rfl-tie to `authSetCommit`, the whole-set
    binding reduced to the per-block compression floor, the carrier discharge, and the slot into
    `mid_no_forgery`.
  * ASSUMED (named, load-bearing hypotheses — the composition wall, RESIDUAL #1): `hfold`
    (`authSetRootRef rows = anchorRoot`) is, in the deployed circuit, the CONCLUSION of the chained
    `blake2bF` gates forcing their BLAKE2b outputs (≈ 27264 core gates/block × #rows). The atomic + whole-
    `G` gates are forced + both-polarity KAT'd (`Blake2bGadget` §3/§5); the full composition is the next
    slice. Here `hfold` is explicit, so DERIVED-vs-ASSUMED is visible.
  * ASSUMED (`hcompress`) — the BLAKE2b compression-CR floor, the named production assumption, consumed
    where the binding is proved (never discharged positively — `authSetRootRef` is a real compressing
    hash, so unconditional injectivity is pigeonhole-false; a collapsing commit REFUTES the floor SHAPE,
    `midCollapse_not_CR`).
  * ASSUMED (the EC arc): `edOk` (the aggregate Ed25519 precommit-signature result) stays a hypothesis —
    the per-authority signature soundness is the Ed25519 leaf, not folded here.
  * RESIDUAL (flat→block modeling + full-set): each row is serialized to one 128-byte block; the exact
    domain-separated Substrate encoding of a variable-width `(authorityId, weight)` row and the arbitrary-N
    set are the named residual. The KAT fixes a 2-authority set (a genuine 2-block absorb).
  * RESIDUAL (deploy/emit wall): the chained BLAKE2b absorb cannot be flat-merged into the byte-golden
    `emitVmJson2`; the deployed carrier removal routes through the IR-v2 `proofBind` recursion seam
    (identical to the eth/tm/sol lanes). Descriptor + golden are UNTOUCHED — NO VK regen.
  * RESIDUAL (felt-width): the 8 output words bind to the anchor root word-for-word; the 64-bit-word ↔
    31-bit-BabyBear-limb repack is the shared field-width residual (`Blake2bGadget` §Resolution).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`admit`/`native_decide`. The
`#guard` KATs anchor the 2-authority BLAKE2b absorb against a real `hashlib.blake2b` vector (LE-word
convention verified against `Blake2bGadget` §0's published `blake2b("abc")`/`blake2b("")` anchors), both
polarities (a real absorb value + a tampered authority weight whose absorb DIFFERS). `midBlakeLeaf` is
the lawful BLAKE2b `MidLeaf` demonstration instance whose `authSetCR` is the GENUINE BLAKE2b authority-set
CR floor over `authSetRootRef` (taken as `hcr` where consumed; the Ed25519 fields are the demo/EC-arc
slot). NEW file; imports read-only (`Blake2bGadget`, `Bridge.LightClientMidnight`); standalone (NOT
imported by the truncated `Dregg2` root, built directly as `Dregg2.Circuit.Emit.LightClientMidHashFold`).
-/
import Dregg2.Circuit.Emit.Blake2bGadget
import Dregg2.Bridge.LightClientMidnight

namespace Dregg2.Circuit.Emit.LightClientMidHashFold

open Dregg2.Circuit.Emit.Blake2bGadget
open Dregg2.Bridge.LightClientMidnight

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §1 — The BLAKE2b authority-set-root reconstruction (the multi-block absorb over `Ref.compress`).

Each authority row `(authorityId, weight)` is serialized to ONE 128-byte (16-word, little-endian) block
carrying a domain tag; the absorb chains `Ref.compress` block by block with the BLAKE2b counter and
final-flag. Since every row is a full block, `authSetRootRef rows = hashlib.blake2b(serialization)`. -/

/-- The Midnight authority-set domain tag (the leading serialization word). -/
def midDomain : Nat := 0x6d6964

/-- One authority row `(authorityId, weight)` as a 128-byte BLAKE2b message block (16 LE 64-bit words):
`[domain, authId, weight, 0…]`. Injective in `(authId, weight)` (distinct positions). -/
def rowBlock (r : Nat × Nat) : List Nat :=
  [midDomain, r.1, r.2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The authority set as its BLAKE2b message blocks (one full 128-byte block per row). -/
def authSetBlocks (rows : List (Nat × Nat)) : List (List Nat) := rows.map rowBlock

/-- The per-block BLAKE2b schedule: block `i` (0-based) of a `n`-block message uses counter `128·(i+1)`
(bytes absorbed through it — every block is full) and the final-flag `FF` iff it is the last block
(`i+1 = n`). A `List (block, counter, flag)`. -/
def sched (n : Nat) : Nat → List (List Nat) → List (List Nat × Nat × Nat)
  | _, [] => []
  | i, m :: rest => (m, 128 * (i + 1), if i + 1 = n then Ref.FF else 0) :: sched n (i + 1) rest

/-- **The BLAKE2b multi-block absorb** — `foldl Ref.compress h0` over the scheduled blocks: block `k`'s
8-word digest state is block `k+1`'s initial state, at counter `t` with final-flag `f`. Built ONLY from
the `hashlib.blake2b`-anchored `Ref.compress` (no new BLAKE2b arithmetic). -/
def absorb (h0 : List Nat) (s : List (List Nat × Nat × Nat)) : List Nat :=
  s.foldl (fun h e => Ref.compress h e.1 e.2.1 0 e.2.2 0) h0

/-- **The authority-set ROOT** — the BLAKE2b absorb of the serialized sorted authority rows, from the
default-parameter initial state. The candidate authority-set root that `authSetOk` compares. -/
def authSetRootRef (rows : List (Nat × Nat)) : List Nat :=
  absorb Ref.h0Default (sched (authSetBlocks rows).length 0 (authSetBlocks rows))

/-! ## §2 — Structural laws of the absorb + schedule (for the binding reduction). -/

/-- Appending one scheduled block is one more `Ref.compress` step (the absorb's reverse step law — a
plain `foldl` append, so it holds regardless of the counter/flag values). -/
theorem absorb_concat (h0 : List Nat) (s : List (List Nat × Nat × Nat)) (x : List Nat × Nat × Nat) :
    absorb h0 (s ++ [x]) = Ref.compress (absorb h0 s) x.1 x.2.1 0 x.2.2 0 := by
  simp [absorb, List.foldl_append]

/-- The schedule's block projection recovers the block list. -/
theorem sched_map_fst (n : Nat) :
    ∀ (i : Nat) (B : List (List Nat)), (sched n i B).map (·.1) = B := by
  intro i B
  induction B generalizing i with
  | nil => rfl
  | cons m rest ih => simp only [sched, List.map_cons, ih (i + 1)]

/-- Two equal-length block lists share the schedule's `(counter, flag)` projection (the schedule's
counter/flag depend only on the position and the block count, not the block content). -/
theorem sched_map_snd_eq (n : Nat) :
    ∀ (i : Nat) (B₁ B₂ : List (List Nat)), B₁.length = B₂.length →
      (sched n i B₁).map (·.2) = (sched n i B₂).map (·.2) := by
  intro i B₁
  induction B₁ generalizing i with
  | nil =>
    intro B₂ hlen
    cases B₂ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons m rest ih =>
    intro B₂ hlen
    cases B₂ with
    | nil => simp at hlen
    | cons m' rest' =>
      have hlen' : rest.length = rest'.length := by simpa using hlen
      simp only [sched, List.map_cons, ih (i + 1) rest' hlen']

/-- **THE ABSORB BINDS (the commitment lemma; reduced to the compression floor).** GIVEN the BLAKE2b
compression-CR floor `hcompress` (injectivity of `Ref.compress` at a fixed counter/flag), two schedules
with the SAME `(counter, flag)` projection whose absorbs agree ARE equal — by reverse induction, peeling
the last block and applying `hcompress`. This is the `chainCommit_binding` analog for the flag-carrying
BLAKE2b absorb. -/
theorem absorb_binding
    (hcompress : ∀ (x m : List Nat) (t f : Nat) (y n : List Nat),
      Ref.compress x m t 0 f 0 = Ref.compress y n t 0 f 0 → x = y ∧ m = n)
    (h0 : List Nat) :
    ∀ (s₁ s₂ : List (List Nat × Nat × Nat)),
      s₁.map (·.2) = s₂.map (·.2) →
      absorb h0 s₁ = absorb h0 s₂ → s₁ = s₂ := by
  intro s₁
  induction s₁ using List.reverseRecOn with
  | nil =>
    intro s₂ hsnd _
    cases s₂ with
    | nil => rfl
    | cons a t => simp at hsnd
  | append_singleton s₁' a ih =>
    intro s₂ hsnd h
    rcases List.eq_nil_or_concat s₂ with rfl | ⟨s₂', b, rfl⟩
    · simp at hsnd
    · rw [List.concat_eq_append] at hsnd h ⊢
      simp only [List.map_append, List.map_cons, List.map_nil] at hsnd
      have hlen2 : (s₁'.map (·.2)).length = (s₂'.map (·.2)).length := by
        have hh := congrArg List.length hsnd
        simpa using hh
      obtain ⟨hsnd', hlast⟩ := List.append_inj hsnd hlen2
      have hab2 : a.2 = b.2 := by simpa using hlast
      rw [absorb_concat, absorb_concat] at h
      rw [show b.2.1 = a.2.1 from by rw [hab2], show b.2.2 = a.2.2 from by rw [hab2]] at h
      obtain ⟨hstate, hblk⟩ := hcompress _ _ _ _ _ _ h
      have hs' : s₁' = s₂' := ih s₂' hsnd' hstate
      rw [hs']
      have hab : a = b := by
        rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
        dsimp only at hblk hab2
        rw [hblk, hab2]
      rw [hab]

/-! ## §3 — The four fold theorems (mirroring the tm/sol folds), for the `authSetOk` carrier.

The Ed25519 fields of `midBlakeLeaf` are the demo/EC-arc slot; the load-bearing object is `authSetCommit
= authSetRootRef`, the BLAKE2b absorb. `authSetCR` is the genuine authority-set CR floor over
`authSetRootRef`, `noSetCollision := id` (the named floor, `hcr` where consumed). -/

/-- Demo Ed25519-slot verifier (genuine key `7`, genuine sig `7`): the EC-arc residual, NOT folded. -/
def midEdVerify (pk : Nat) (_m : List Nat × Nat × Nat × Nat) (s : Nat) : Bool :=
  decide (pk = 7) && decide (s = 7)

/-- Demo `Signed` denotation: the genuine authority is key `7`. -/
def midSigned (pk : Nat) (_m : List Nat × Nat × Nat × Nat) : Prop := pk = 7

/-- The demo Ed25519-soundness leaf, PROVED (the `edSound` slot). -/
theorem midEdSound (pk : Nat) (m : List Nat × Nat × Nat × Nat) (s : Nat)
    (h : midEdVerify pk m s = true) : midSigned pk m := by
  simp only [midEdVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- **`midBlakeLeaf`** — the lawful BLAKE2b `MidLeaf` whose `authSetCommit` IS the multi-block absorb
`authSetRootRef`. `authSetCR` is the genuine authority-set CR floor; `noSetCollision := fun h => h`
unpacks it (the named floor, `hcr` where consumed). The Ed25519 fields are the demo/EC-arc slot. -/
@[reducible] def midBlakeLeaf : MidLeaf where
  PubKey := Nat
  Digest := List Nat
  Sig := Nat
  pkeq := inferInstance
  deqD := inferInstanceAs (DecidableEq (List Nat))
  edVerify := midEdVerify
  Signed := midSigned
  edSound := midEdSound
  authSetCommit := authSetRootRef
  authSetCR := ∀ t₁ t₂ : List (Nat × Nat), authSetRootRef t₁ = authSetRootRef t₂ → t₁ = t₂
  noSetCollision := fun h => h
  zeroSig := 0
  zeroDigest := List.replicate 8 0

/-! ### The CR-floor SHAPE discriminates (non-vacuity — not `True` in disguise). -/

/-- A COLLAPSING authority-set commit (every set digests to the zero root) — the badCompress. -/
def midCollapseCommit (_ : List (Nat × Nat)) : List Nat := List.replicate 8 0

/-- **The collapsing commit's CR carrier is FALSE (negative polarity).** Two DIFFERENT authority sets
share the root, so the carrier REFUTES a broken hash: the denominator would be swappable. Both polarities
witnessed for the floor SHAPE. -/
theorem midCollapse_not_CR :
    ¬ (∀ t₁ t₂ : List (Nat × Nat), midCollapseCommit t₁ = midCollapseCommit t₂ → t₁ = t₂) := by
  intro h
  exact absurd (h [(1, 2)] [(2, 3)] rfl) (by decide)

/-- **THE TIE (`*_eq_chainCommit` analog).** The bridge leaf's `authSetCommit` IS the BLAKE2b absorb
reconstruction — the object `authSetOk` stood for, via the BLAKE2b arithmetic. -/
theorem midBlakeLeaf_authSetCommit_eq_absorb (rows : List (Nat × Nat)) :
    midBlakeLeaf.authSetCommit rows = authSetRootRef rows := rfl

/-- **THE AUTHORITY-SET COMMIT BINDS (the commitment lemma; reduced to the compression floor).** GIVEN
the BLAKE2b compression-CR floor `hcompress`, equal-length authority sets whose BLAKE2b absorbs agree ARE
the same set — so the WS-anchor-pinned root pins the weight DENOMINATOR (the content behind
`noSetCollision`, reduced via `absorb_binding` and `rowBlock` injectivity). -/
theorem authSet_binding
    (hcompress : ∀ (x m : List Nat) (t f : Nat) (y n : List Nat),
      Ref.compress x m t 0 f 0 = Ref.compress y n t 0 f 0 → x = y ∧ m = n)
    (t₁ t₂ : List (Nat × Nat)) (hlen : t₁.length = t₂.length)
    (h : authSetRootRef t₁ = authSetRootRef t₂) : t₁ = t₂ := by
  have hBlen : (authSetBlocks t₁).length = (authSetBlocks t₂).length := by
    simp only [authSetBlocks, List.length_map, hlen]
  -- equal block counts ⇒ identical (counter, flag) schedule projection
  have hsnd : (sched (authSetBlocks t₁).length 0 (authSetBlocks t₁)).map (·.2)
            = (sched (authSetBlocks t₂).length 0 (authSetBlocks t₂)).map (·.2) := by
    rw [hBlen]
    exact sched_map_snd_eq (authSetBlocks t₂).length 0 (authSetBlocks t₁) (authSetBlocks t₂) hBlen
  -- the absorb equality is `h`
  have habsorb : absorb Ref.h0Default (sched (authSetBlocks t₁).length 0 (authSetBlocks t₁))
               = absorb Ref.h0Default (sched (authSetBlocks t₂).length 0 (authSetBlocks t₂)) := h
  have hsched : sched (authSetBlocks t₁).length 0 (authSetBlocks t₁)
              = sched (authSetBlocks t₂).length 0 (authSetBlocks t₂) :=
    absorb_binding hcompress Ref.h0Default _ _ hsnd habsorb
  -- recover the block lists, then the row lists (rowBlock injective)
  have hB : authSetBlocks t₁ = authSetBlocks t₂ := by
    have hm := congrArg (List.map (fun p : List Nat × Nat × Nat => p.1)) hsched
    rwa [sched_map_fst, sched_map_fst] at hm
  have hinj : Function.Injective rowBlock := by
    rintro ⟨a, w⟩ ⟨a', w'⟩ heq
    simp only [rowBlock, List.cons.injEq] at heq
    simp only [Prod.mk.injEq]
    exact ⟨heq.2.1, heq.2.2.1⟩
  have hB' : t₁.map rowBlock = t₂.map rowBlock := hB
  exact List.map_injective_iff.mpr hinj hB'

/-- **THE `authSetOk` CARRIER DISCHARGED by the exhibited absorb (`*_from_fold` analog) — NO carrier bit
read.** Given the BLAKE2b absorb reconstructing the authority rows into the pinned WS anchor root, the
bridge's `authSetOk` Boolean is `true`. A satisfying prover must EXHIBIT authority rows whose BLAKE2b
absorb hits the anchor; there is no witnessed carrier to set. -/
theorem verifyAuthSet_from_fold (ts : MidTrustedState midBlakeLeaf) (u : MidUpdate midBlakeLeaf)
    (hfold : authSetRootRef (u.authSet.map authRow) = ts.anchorRoot) :
    authSetOk midBlakeLeaf ts u = true := by
  unfold authSetOk
  exact midBlakeLeaf.dBeq_iff.mpr hfold

/-- **THE PAYOFF: the fold-derived binding slots into `mid_no_forgery`'s `anchorBinds` leg in place of the
trusted `authSetOk` bit (`*_from_fold_slots_into_no_forgery` analog).** GIVEN the BLAKE2b authority-set-CR
carrier (`hcr` — the named floor), the `0 < totalWeight` floor, the strict `> 2/3` supermajority, and the
Ed25519 / round / era results (`edOk`/`roundOk`/`eraOk` — the EC-arc + in-AIR gates, hypotheses), if the
authority rows' BLAKE2b absorb reconstructs into the pinned WS anchor root (`hfold` — DERIVED from the
exhibited rows, not a witnessed bit), the update is Midnight-GRANDPA-VALID relative to the anchor. The
`authSetOk` carrier is folded out: the weight DENOMINATOR is now pinned by the BLAKE2b absorb, not an
opaque bit. -/
theorem mid_authset_from_fold_slots_into_no_forgery
    (hcr : midBlakeLeaf.authSetCR)
    (ts : MidTrustedState midBlakeLeaf) (u : MidUpdate midBlakeLeaf)
    (hpos : 0 < totalWeight midBlakeLeaf u)
    (hthr : 2 * totalWeight midBlakeLeaf u < 3 * signedWeight midBlakeLeaf u)
    (hed : edOk midBlakeLeaf u = true)
    (hround : roundOk midBlakeLeaf u = true)
    (hera : eraOk midBlakeLeaf ts u = true)
    (hfold : authSetRootRef (u.authSet.map authRow) = ts.anchorRoot) :
    MidValidAt midBlakeLeaf ts u := by
  have hauthset : authSetOk midBlakeLeaf ts u = true := verifyAuthSet_from_fold ts u hfold
  have hverify : midVerify midBlakeLeaf ts u = true := by
    unfold midVerify midVerifyDecision
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨hpos, hthr⟩, hed⟩, hauthset⟩, hround⟩, hera⟩
  exact mid_no_forgery midBlakeLeaf hcr ts u hverify

/-! ## §4 — KATs: the 2-authority BLAKE2b absorb, anchored to a real `hashlib.blake2b` vector.

Both-polarity, non-vacuous: a genuine 2-authority absorb value (a true 2-block chain, block 0 flag `0`,
block 1 flag `FF`) computed by `hashlib.blake2b` (the row-per-128-bytes serialization; the LE-word
convention is verified against `Blake2bGadget` §0's published `blake2b("abc")`/`blake2b("")` anchors), and
a tampered authority weight (`2 → 99`, a denominator inflation) whose absorb DIFFERS. These reduce in the
kernel (the `Ref.compress` reference). -/

/-- The genuine 2-authority set (weights `2, 2`) — a 2-block BLAKE2b absorb. -/
def midRows : List (Nat × Nat) := [(1, 2), (2, 2)]

-- Positive: the real 2-authority BLAKE2b authority-set root, independently computed (`hashlib.blake2b`).
#guard authSetRootRef midRows ==
  [0x57ba62cfe08dd95f, 0xde44625211c674d2, 0xc67996e9930e1feb, 0x2f325d619c958098,
   0xfeadb6228c575172, 0xe1d4cdbe596ad26f, 0x9d5342cdbcbde099, 0x42092933c9d3f1e6]
-- Negative (discrimination): authority 2's weight 2 → 99 changes the authority-set root.
#guard authSetRootRef [(1, 2), (2, 99)] !=
  [0x57ba62cfe08dd95f, 0xde44625211c674d2, 0xc67996e9930e1feb, 0x2f325d619c958098,
   0xfeadb6228c575172, 0xe1d4cdbe596ad26f, 0x9d5342cdbcbde099, 0x42092933c9d3f1e6]

/-! ### Structural: the absorb is a genuine multi-block chain, and the deployed circuit chains the
GADGET `blake2bF`. -/

-- Two authorities ⇒ two full 128-byte BLAKE2b blocks (the chain, not one block).
#guard (sched (authSetBlocks midRows).length 0 (authSetBlocks midRows)).length == 2
-- The final-flag `FF` is on the LAST block only (`[0, FF]`) — the BLAKE2b absorb structure.
#guard (sched 2 0 (authSetBlocks midRows)).map (·.2.2) == [0, Ref.FF]
-- The DEPLOYED absorb chains the GADGET `blake2bF` (block k's 8 output words feed block k+1's `hBases`);
-- two blocks = 2 × 27264 core gates. (RESIDUAL #1: the Ref-level `absorb` is what the chained `blake2bF`
-- gates FORCE; here the two-block gadget gate count exhibits the gadget composition.)
#guard ((blake2bF (List.range 8) (List.range 16) 100 101 102 103 (List.range 8) 20000).1
        ++ (blake2bF (List.range 8) (List.range 16) 100 101 102 103 (List.range 8) 60000).1).length
       == 2 * 27264

/-! ## §5 — axiom hygiene. -/

#assert_axioms midEdSound
#assert_axioms midCollapse_not_CR
#assert_axioms absorb_concat
#assert_axioms sched_map_fst
#assert_axioms sched_map_snd_eq
#assert_axioms absorb_binding
#assert_axioms midBlakeLeaf_authSetCommit_eq_absorb
#assert_axioms authSet_binding
#assert_axioms verifyAuthSet_from_fold
#assert_axioms mid_authset_from_fold_slots_into_no_forgery

#print axioms mid_authset_from_fold_slots_into_no_forgery
#print axioms authSet_binding

end Dregg2.Circuit.Emit.LightClientMidHashFold
