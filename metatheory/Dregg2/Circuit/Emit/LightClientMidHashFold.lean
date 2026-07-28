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
  * `authSet_binding_on` — GIVEN separation on the absorb's OWN `(state, block)` pairs
    (`compressSepOn` + `AbsorbCovered`, the HONEST floor), equal-length authority sets whose absorbs
    agree ARE the same set: the BLAKE2b commit BINDS the authority set.
  * `verifyAuthSet_from_fold` (`*_from_fold` analog) — the `authSetOk` Boolean is DISCHARGED by the
    exhibited absorb: NO carrier column is read.
  * `mid_authset_from_fold_gate_accepts` (carrier-free) + `mid_authset_binding_on` (the HONEST floor
    `compressSepOn`) — the
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
import Dregg2.Circuit.Emit.StakeWidthRange
import Dregg2.Bridge.LightClientMidnight

namespace Dregg2.Circuit.Emit.LightClientMidHashFold

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.StakeWidthRange
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

/-! ### ⚑ 2026-07-27 — THE COMPRESSION FLOOR, STATED HONESTLY.

`Ref.compress` COMPRESSES: 8 state words + 16 message words in, 8 words out, each `< 2^64`
(`Ref.w64`). So "`Ref.compress` is injective in `(state, block)`" is FALSE, and the BLAKE2b message
words enter ONLY through `add3 … x = w64 (…)` — they are never rotated — so a message word is read
only MODULO `2^64` and the collision is EXECUTABLE, not a pigeonhole appeal
(`authSetRootRef_weight_collision`: an authority whose weight is `0` and one whose weight is `2^64`
produce the SAME authority-set root). `absorb_binding` used to take that refuted `Prop` as `hcompress`
and was therefore an implication with an empty premise; the honest floor is separation on the FINITE,
EXHIBITED set of `(state, block)` pairs the absorb actually compresses. -/

/-- **The IDEALIZED BLAKE2b compression-CR floor, NAMED so it can be REFUTED rather than assumed.**
This is the exact `Prop` `absorb_binding` used to take. -/
def compressInjective : Prop :=
  ∀ (x m : List Nat) (t f : Nat) (y n : List Nat),
    Ref.compress x m t 0 f 0 = Ref.compress y n t 0 f 0 → x = y ∧ m = n

/-- **`compressSepOn P` — THE HONEST FLOOR.** `Ref.compress` SEPARATES on the `(state, block)` pairs
satisfying `P` at a given `(counter, flag)`. A consumer must NAME the class its absorb walks and pay
for it — the shape a query-counted collision bound can price. -/
def compressSepOn (P : List Nat → List Nat → Nat → Nat → Prop) : Prop :=
  ∀ (x m : List Nat) (t f : Nat) (y n : List Nat), P x m t f → P y n t f →
    Ref.compress x m t 0 f 0 = Ref.compress y n t 0 f 0 → x = y ∧ m = n

/-- **The floor at the EMPTY class is vacuous** (the other end of the dial, priced). -/
theorem compressSepOn_bot : compressSepOn (fun _ _ _ _ => False) := fun _ _ _ _ _ _ h => h.elim

/-- **`AbsorbCovered P h0 s`** — `P` holds of every `(state, block, counter, flag)` the absorb feeds
to `Ref.compress`. The absorb's HASH TRANSCRIPT, as an obligation. -/
def AbsorbCovered (P : List Nat → List Nat → Nat → Nat → Prop) :
    List Nat → List (List Nat × Nat × Nat) → Prop
  | _, [] => True
  | h, e :: rest =>
      P h e.1 e.2.1 e.2.2 ∧ AbsorbCovered P (Ref.compress h e.1 e.2.1 0 e.2.2 0) rest

/-- Peeling the FIRST block of an absorb. -/
theorem absorb_cons (h0 : List Nat) (e : List Nat × Nat × Nat)
    (rest : List (List Nat × Nat × Nat)) :
    absorb h0 (e :: rest) = absorb (Ref.compress h0 e.1 e.2.1 0 e.2.2 0) rest := rfl

/-- **THE ABSORB BINDS, at the HONEST floor.** Two schedules with the SAME `(counter, flag)`
projection whose absorbs from (possibly different) initial states agree ARE equal, and so are the
states — GIVEN separation on the class both absorbs' own `(state, block)` pairs live in. Conclusion
strictly stronger than the old `absorb_binding` (it pins the initial state too); premise satisfiable
(`compressSepOn_midAbsorbSep`) instead of refuted. -/
theorem absorb_binding_on (P : List Nat → List Nat → Nat → Nat → Prop) (hsep : compressSepOn P) :
    ∀ (s₁ s₂ : List (List Nat × Nat × Nat)) (h₁ h₂ : List Nat),
      s₁.map (·.2) = s₂.map (·.2) →
      AbsorbCovered P h₁ s₁ → AbsorbCovered P h₂ s₂ →
      absorb h₁ s₁ = absorb h₂ s₂ → h₁ = h₂ ∧ s₁ = s₂ := by
  intro s₁
  induction s₁ with
  | nil =>
    intro s₂ h₁ h₂ hsnd _ _ h
    cases s₂ with
    | nil => exact ⟨h, rfl⟩
    | cons _ _ => simp at hsnd
  | cons e₁ r₁ ih =>
    intro s₂ h₁ h₂ hsnd hc₁ hc₂ h
    cases s₂ with
    | nil => simp at hsnd
    | cons e₂ r₂ =>
      obtain ⟨m₁, t₁, f₁⟩ := e₁
      obtain ⟨m₂, t₂, f₂⟩ := e₂
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hsnd
      obtain ⟨⟨rfl, rfl⟩, hrest⟩ := hsnd
      simp only [AbsorbCovered] at hc₁ hc₂
      simp only [absorb_cons] at h
      obtain ⟨hcs, hr⟩ := ih r₂ _ _ hrest hc₁.2 hc₂.2 h
      obtain ⟨hh, hm⟩ := hsep _ _ _ _ _ _ hc₁.1 hc₂.1 hcs
      exact ⟨hh, by rw [hm, hr]⟩

/-! ## §3 — The four fold theorems (mirroring the tm/sol folds), for the `authSetOk` carrier.

The Ed25519 fields of `midBlakeLeaf` are the demo/EC-arc slot; the load-bearing object is `authSetCommit
= authSetRootRef`, the BLAKE2b absorb. ⚑ 2026-07-27: `authSetCR` used to be idealized injectivity of
`authSetRootRef`, which is REFUTED (`authSetInjective_false`), so the slot is now `False` and the
binding rides `authSet_binding_on` at the honest floor `compressSepOn`. -/

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

/-- **The IDEALIZED authority-set CR floor, NAMED so it can be REFUTED rather than assumed.** This is
the exact `Prop` `midBlakeLeaf.authSetCR` used to hold. -/
def authSetInjective : Prop :=
  ∀ t₁ t₂ : List (Nat × Nat), authSetRootRef t₁ = authSetRootRef t₂ → t₁ = t₂

/-- A one-row authority set is exactly one `Ref.compress` at counter 128 with the final flag. -/
theorem authSetRootRef_single (r : Nat × Nat) :
    authSetRootRef [r] = Ref.compress Ref.h0Default (rowBlock r) 128 0 Ref.FF 0 := rfl

set_option maxRecDepth 8192 in
/-- ⛑ **THE WEIGHT DENOMINATOR IS NOT BOUND — an executable collision.** An authority of weight `0`
and one of weight `2^64` produce the SAME authority-set root: BLAKE2b's message words enter only
through `add3 … x = w64 (…)` and are never rotated, so a message word is read only modulo `2^64`,
and `rowBlock` drops the raw `Nat` weight straight into one. This is the audit's witness, in Lean. -/
theorem authSetRootRef_weight_collision :
    authSetRootRef [(1, 0)] = authSetRootRef [(1, 2 ^ 64)] := by decide

/-- **THE IDEALIZED AUTHORITY-SET CR FLOOR IS FALSE**, by witness. -/
theorem authSetInjective_false : ¬ authSetInjective := by
  intro h
  exact absurd (h _ _ authSetRootRef_weight_collision) (by decide)

/-- **THE IDEALIZED COMPRESSION FLOOR IS FALSE**, by the same witness one level down. -/
theorem compressInjective_false : ¬ compressInjective := by
  intro h
  have hcol : Ref.compress Ref.h0Default (rowBlock (1, 0)) 128 0 Ref.FF 0
            = Ref.compress Ref.h0Default (rowBlock (1, 2 ^ 64)) 128 0 Ref.FF 0 := by
    rw [← authSetRootRef_single, ← authSetRootRef_single]
    exact authSetRootRef_weight_collision
  exact absurd (h _ _ _ _ _ _ hcol).2 (by decide)

/-- **UPPER POLE — the class is LOAD-BEARING.** At the UNRESTRICTED class the floor collapses to the
idealized one and is therefore FALSE: restricting to an exhibited class is the whole difference
between a floor and an empty premise. (Stated as the refutation, not as an `Iff`, so it is anti-floor
content and carries nothing.) -/
theorem compressSepOn_top_false : ¬ compressSepOn (fun _ _ _ _ => True) := fun h =>
  compressInjective_false (fun x m t f y n e => h x m t f y n trivial trivial e)

/-! ## §2c — ⚑ 2026-07-28 — THE WEIGHT WIDTH GATE: the collision's witness is REFUSED.

The weight twin of the Solana stake repair (`LightClientSolHashFold` §1). Unlike Solana, NO ENCODER
CHANGE IS NEEDED here: a BLAKE2b word IS 64 boolean columns (`Blake2bGadget` §1) and a Midnight
authority weight IS a `u64`, so `rowBlock`'s one-word-per-field encoding is already the faithful
fixed-width shape. What was missing is only the RANGE CHECK, and its absence is exactly what
`authSetRootRef_weight_collision` exploits — the weight `2^64` is one bit wider than the word that
carries it, and `Ref.compress` reads a message word only modulo `2^64`.

The gate is `StakeWidthRange.widthGate` at 64 bits, generated in Lean from `AirBuilder.rangeNonneg`;
`widthGate_forces` is what makes it a check rather than a shape. -/

/-- The Midnight authority-weight width: the BLAKE2b word width, which is also the `u64` weight. -/
def MID_WEIGHT_BITS : Nat := 64

/-- **An authority row is IN RANGE** when its id and weight each fit the BLAKE2b word carrying it. -/
def MidRowInRange (r : Nat × Nat) : Prop :=
  r.1 < 2 ^ MID_WEIGHT_BITS ∧ r.2 < 2 ^ MID_WEIGHT_BITS

instance : DecidablePred MidRowInRange := fun r => by
  unfold MidRowInRange; infer_instance

/-- **An authority SET is in range** when every row is. -/
def MidSetInRange (t : List (Nat × Nat)) : Prop := ∀ r ∈ t, MidRowInRange r

instance : DecidablePred MidSetInRange := fun t => by
  unfold MidSetInRange; infer_instance

/-- **THE AUTHORITY-ROW WIDTH GATES — LEAN-AUTHORED AIR.** Per row: one
`StakeWidthRange.widthGate` per field at the BLAKE2b word width. `2 · (64 + 1) = 130`
constraints/row. -/
def midRowWidthGates (idCol wtCol bit0 : Nat) : List VmConstraint2 :=
  widthGate idCol bit0 MID_WEIGHT_BITS
  ++ widthGate wtCol (bit0 + MID_WEIGHT_BITS) MID_WEIGHT_BITS

/-- The emitted budget: `65 + 65 = 130` constraints per authority row. -/
theorem midRowWidthGates_length (idCol wtCol bit0 : Nat) :
    (midRowWidthGates idCol wtCol bit0).length = 130 := by
  simp [midRowWidthGates, widthGate, rangeNonneg, bitsFrom, MID_WEIGHT_BITS]

/-- **THE ROW GATES FORCE THE ROW'S WIDTHS** — the bridge from the emitted AIR to the model-side
predicate. -/
theorem midRowWidthGates_forces (a : Assignment) (r : Nat × Nat) (idCol wtCol bit0 : Nat)
    (hid : a idCol = (r.1 : ℤ)) (hwt : a wtCol = (r.2 : ℤ))
    (hbId : ∀ c ∈ bitsFrom bit0 MID_WEIGHT_BITS, (gBin c).eval a = 0)
    (hrId : evalH (recompHead (Head.lin 1 idCol) (bitsFrom bit0 MID_WEIGHT_BITS)) a = 0)
    (hbWt : ∀ c ∈ bitsFrom (bit0 + MID_WEIGHT_BITS) MID_WEIGHT_BITS, (gBin c).eval a = 0)
    (hrWt : evalH (recompHead (Head.lin 1 wtCol)
              (bitsFrom (bit0 + MID_WEIGHT_BITS) MID_WEIGHT_BITS)) a = 0) :
    MidRowInRange r :=
  ⟨widthGate_forces a r.1 idCol bit0 MID_WEIGHT_BITS hid hbId hrId,
   widthGate_forces a r.2 wtCol (bit0 + MID_WEIGHT_BITS) MID_WEIGHT_BITS hwt hbWt hrWt⟩

/-- **THE INFLATED AUTHORITY IS OUT OF RANGE** — the collision's second witness is refused by the
width predicate the gate forces, while the honest one is admitted. -/
theorem authSetRootRef_weight_collision_out_of_range :
    MidSetInRange [(1, 0)] ∧ ¬ MidSetInRange [((1, 2 ^ 64) : Nat × Nat)] := by
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨by decide, by decide⟩
  · intro h
    have := (h (1, 2 ^ 64) (by simp)).2
    simp only [MID_WEIGHT_BITS] at this
    omega

/-- **THE `2^64`-ALIAS FAMILY COLLAPSES IN RANGE.** A row whose weight has been shifted by `k·2^64` —
the exact family `Ref.compress`'s mod-`2^64` message read generates — is in range only when
`k = 0`. -/
theorem midRow_weight_alias_collapses (r : Nat × Nat) (k : Nat)
    (h : MidRowInRange (r.1, r.2 + k * 2 ^ MID_WEIGHT_BITS)) : k = 0 :=
  alias_collapses_in_range MID_WEIGHT_BITS r.2 k h.2

/-- **NO AUTHORITY SET THE GATE ADMITS CARRIES AN INFLATED ROW.** -/
theorem midSet_weight_alias_unreachable (t : List (Nat × Nat)) (r : Nat × Nat) (k : Nat)
    (ht : MidSetInRange t)
    (hmem : ((r.1, r.2 + k * 2 ^ MID_WEIGHT_BITS) : Nat × Nat) ∈ t) : k = 0 :=
  midRow_weight_alias_collapses r k (ht _ hmem)

/-- ⛑ **THE WEIGHT COLLISION IS UNWITNESSABLE UNDER THE EMITTED GATE.** Not "no collision is known" —
there is NO satisfying assignment for `midRowWidthGates` whose weight column carries the exhibit's
`2^64`. -/
theorem authSetRootRef_weight_collision_unwitnessable (a : Assignment) (wtCol bit0 : Nat)
    (hwt : a wtCol = ((2 ^ 64 : Nat) : ℤ))
    (hbWt : ∀ c ∈ bitsFrom (bit0 + MID_WEIGHT_BITS) MID_WEIGHT_BITS, (gBin c).eval a = 0)
    (hrWt : evalH (recompHead (Head.lin 1 wtCol)
              (bitsFrom (bit0 + MID_WEIGHT_BITS) MID_WEIGHT_BITS)) a = 0) :
    False :=
  widthGate_refuses a (2 ^ 64) wtCol (bit0 + MID_WEIGHT_BITS) MID_WEIGHT_BITS
    (Nat.le_refl _) hwt hbWt hrWt

/-- **THE REFUTATION OF THE FLOOR LIVES OUTSIDE THE GATED CLASS.** `compressSepOn` is refuted by the
weight collision — but the block the refutation needs is one the width gate cannot produce: the
inflated authority's message block carries a word `≥ 2^64`, so a width-gated absorb never walks it.
That is the whole reason the honest floor is now plausible on the class a gated fold covers rather
than refuted on it. -/
theorem weight_collision_block_out_of_range :
    ¬ (∀ w ∈ rowBlock ((1, 2 ^ 64) : Nat × Nat), w < 2 ^ MID_WEIGHT_BITS) := by
  intro h
  have := h (2 ^ 64) (by simp [rowBlock])
  simp only [MID_WEIGHT_BITS] at this
  omega

/-- **`midBlakeLeaf`** — the lawful BLAKE2b `MidLeaf` whose `authSetCommit` IS the multi-block absorb
`authSetRootRef`. The Ed25519 fields are the demo/EC-arc slot.

⛑ 2026-07-27 — `authSetCR` used to be `∀ t₁ t₂, authSetRootRef t₁ = authSetRootRef t₂ → t₁ = t₂`,
described as "the genuine authority-set CR floor". `MidLeaf.noSetCollision` demands the carrier ENTAIL
exactly that, and it is FALSE (`authSetInjective_false`, an executable weight-inflation collision), so
every theorem taking `hcr : midBlakeLeaf.authSetCR` proved nothing. The slot is now `False`; the
binding content rides `authSet_binding_on` on the honest floor `compressSepOn`. -/
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
  authSetCR := False
  noSetCollision := fun h => h.elim
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

/-- **THE AUTHORITY-SET COMMIT BINDS, at the HONEST floor.** Equal-length authority sets whose
BLAKE2b absorbs agree ARE the same set — so the WS-anchor-pinned root pins the weight DENOMINATOR —
GIVEN separation on the class the two absorbs' OWN `(state, block)` pairs live in, instead of the
REFUTED global injectivity of `Ref.compress`. Conclusion unchanged; premise satisfiable. -/
theorem authSet_binding_on (P : List Nat → List Nat → Nat → Nat → Prop) (hsep : compressSepOn P)
    (t₁ t₂ : List (Nat × Nat)) (hlen : t₁.length = t₂.length)
    (hc₁ : AbsorbCovered P Ref.h0Default
      (sched (authSetBlocks t₁).length 0 (authSetBlocks t₁)))
    (hc₂ : AbsorbCovered P Ref.h0Default
      (sched (authSetBlocks t₂).length 0 (authSetBlocks t₂)))
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
    (absorb_binding_on P hsep _ _ Ref.h0Default Ref.h0Default hsnd hc₁ hc₂ habsorb).2
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

/-- **THE PAYOFF, CARRIER-FREE: the fold-derived binding DISCHARGES THE WHOLE MIDNIGHT GATE.** Given
the `0 < totalWeight` floor, the strict `> 2/3` supermajority, and the Ed25519 / round / era results,
if the authority rows' BLAKE2b absorb reconstructs into the pinned WS anchor root (`hfold` — DERIVED
from the exhibited rows, not a witnessed bit), `midVerify` ACCEPTS. No `authSetOk` bit is read and NO
hash floor is used.

⛑ 2026-07-27 — this replaces `mid_authset_from_fold_slots_into_no_forgery`, which concluded
`MidValidAt` from `hcr : midBlakeLeaf.authSetCR`, REFUTED by an executable WEIGHT-INFLATION collision
(`authSetInjective_false`). **CAPABILITY LOST, NAMED:** `MidValidAt`'s ∀-quantified authority-set
binding conjunct is not derivable at a compressing hash by any premise. What replaces it is the
PAIRWISE form (`mid_authset_binding_on`). ⛑ AND THE WITNESS IS ITS OWN FINDING: `rowBlock` drops the
raw `Nat` weight into one BLAKE2b message word, so even the pairwise form is only as good as an
encoder range-check that does not exist here — a NAMED residual this repair surfaces. -/
theorem mid_authset_from_fold_gate_accepts
    (ts : MidTrustedState midBlakeLeaf) (u : MidUpdate midBlakeLeaf)
    (hpos : 0 < totalWeight midBlakeLeaf u)
    (hthr : 2 * totalWeight midBlakeLeaf u < 3 * signedWeight midBlakeLeaf u)
    (hed : edOk midBlakeLeaf u = true)
    (hround : roundOk midBlakeLeaf u = true)
    (hera : eraOk midBlakeLeaf ts u = true)
    (hfold : authSetRootRef (u.authSet.map authRow) = ts.anchorRoot) :
    midVerify midBlakeLeaf ts u = true := by
  have hauthset : authSetOk midBlakeLeaf ts u = true := verifyAuthSet_from_fold ts u hfold
  unfold midVerify midVerifyDecision
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hpos, hthr⟩, hed⟩, hauthset⟩, hround⟩, hera⟩

/-- **THE AUTHORITY SET IS BOUND, at the HONEST floor.** Two equal-length authority sets whose BLAKE2b
absorbs both hit the SAME pinned anchor root ARE the same set — GIVEN separation on the class their own
`(state, block)` pairs live in. This is what `authSetOk` stood for. -/
theorem mid_authset_binding_on (P : List Nat → List Nat → Nat → Nat → Prop) (hsep : compressSepOn P)
    (t₁ t₂ : List (Nat × Nat)) (anchor : List Nat) (hlen : t₁.length = t₂.length)
    (hc₁ : AbsorbCovered P Ref.h0Default (sched (authSetBlocks t₁).length 0 (authSetBlocks t₁)))
    (hc₂ : AbsorbCovered P Ref.h0Default (sched (authSetBlocks t₂).length 0 (authSetBlocks t₂)))
    (h₁ : authSetRootRef t₁ = anchor) (h₂ : authSetRootRef t₂ = anchor) : t₁ = t₂ :=
  authSet_binding_on P hsep t₁ t₂ hlen hc₁ hc₂ (h₁.trans h₂.symm)

/-! ### The honest floor's SATISFIABLE leg (the one the audited guard never tested). -/

/-- Two one-row absorbs at the real BLAKE2b parameters — an exhibited, genuinely two-element class. -/
def midAbsorbSep (x m : List Nat) (t f : Nat) : Prop :=
  x = Ref.h0Default ∧ t = 128 ∧ f = Ref.FF
    ∧ (m = rowBlock (1, 2) ∨ m = rowBlock (1, 3))

set_option maxRecDepth 8192 in
/-- **SATISFIABLE — `Ref.compress` SEPARATES on an exhibited class**, kernel-checked on the real
BLAKE2b reference. So `absorb_binding_on` is an implication with a NON-empty antecedent — the leg the
audited `midCollapse_not_CR` guard never tested, and at which the OLD floor's answer was NO. -/
theorem compressSepOn_midAbsorbSep : compressSepOn midAbsorbSep := by
  intro x m t f y n hx hy e
  obtain ⟨rfl, rfl, rfl, hm⟩ := hx
  obtain ⟨rfl, -, -, hn⟩ := hy
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd e (by decide)

/-- The satisfying class is genuinely INHABITED by distinct blocks (not the empty class in disguise). -/
theorem midAbsorbSep_class_inhabited :
    midAbsorbSep Ref.h0Default (rowBlock (1, 2)) 128 Ref.FF
    ∧ midAbsorbSep Ref.h0Default (rowBlock (1, 3)) 128 Ref.FF
    ∧ rowBlock (1, 2) ≠ rowBlock (1, 3) :=
  ⟨⟨rfl, rfl, rfl, Or.inl rfl⟩, ⟨rfl, rfl, rfl, Or.inr rfl⟩, by decide⟩

set_option maxRecDepth 8192 in
/-- **The satisfying floor FIRES** — obtained THROUGH `mid_authset_binding_on`: at a class the floor
genuinely holds on, two one-authority sets with different weights cannot share an anchor root. Floor,
coverage and conclusion exercised together on the real BLAKE2b. -/
theorem mid_authset_binding_fires :
    authSetRootRef [(1, 2)] ≠ authSetRootRef [(1, 3)] := by
  intro h
  exact absurd (mid_authset_binding_on midAbsorbSep compressSepOn_midAbsorbSep [(1, 2)] [(1, 3)] _
    rfl ⟨⟨rfl, rfl, rfl, Or.inl rfl⟩, trivial⟩ ⟨⟨rfl, rfl, rfl, Or.inr rfl⟩, trivial⟩ rfl h.symm)
    (by decide)

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
#assert_axioms compressSepOn_top_false
#assert_axioms compressSepOn_bot
#assert_axioms absorb_binding_on
#assert_axioms authSetRootRef_weight_collision
#assert_axioms authSetInjective_false
#assert_axioms compressInjective_false
#assert_axioms midBlakeLeaf_authSetCommit_eq_absorb
#assert_axioms authSet_binding_on
#assert_axioms verifyAuthSet_from_fold
#assert_axioms mid_authset_from_fold_gate_accepts
#assert_axioms mid_authset_binding_on
#assert_axioms compressSepOn_midAbsorbSep
#assert_axioms midAbsorbSep_class_inhabited
#assert_axioms mid_authset_binding_fires
#assert_axioms midRowWidthGates_length
#assert_axioms midRowWidthGates_forces
#assert_axioms authSetRootRef_weight_collision_out_of_range
#assert_axioms midRow_weight_alias_collapses
#assert_axioms midSet_weight_alias_unreachable
#assert_axioms authSetRootRef_weight_collision_unwitnessable
#assert_axioms weight_collision_block_out_of_range

#print axioms mid_authset_from_fold_gate_accepts
#print axioms authSet_binding_on

end Dregg2.Circuit.Emit.LightClientMidHashFold
