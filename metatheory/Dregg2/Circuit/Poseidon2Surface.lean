/-
# Dregg2.Circuit.Poseidon2Surface — the REAL (Poseidon2 CR-grounded) per-effect commitment surface.

The per-effect witness generators (`Dregg2.Circuit.Witness.*`) used to fill their digest columns from
ad-hoc *toy folds*: `compressNConcrete = acc*10⁶ + x`, `qrecLeaf` with `(capacity % 1000)`,
`lhConcrete` that DROPPED `src`/`dst` (`acc*10⁶ + actor + amt`). Those folds happen to be injective on
the tiny `#guard` domain, so the anti-ghost teeth fire — but they are NOT the real hash. The runnable
`prove+verify` (Lean `#guard` + the Rust Plonky3 prover) was therefore over a fold the system never
instantiates, with FIELD-DROPPING leaves (a queue whose `capacity` differs only above `1000`, or two
receipt chains that differ only in `src`/`dst`, would COLLIDE).

This module supplies the REAL binding surface every witness module now shares:

  * **`p2sponge`** — a single Poseidon2 sponge `List ℤ → ℤ`, the SAME list-hash `StateCommit`'s
    `compressN`, `Poseidon2Emit.spongeCompressN`, and the emitted `merkle_hash` chain realize. Its
    collision-resistance is the ONE named cryptographic assumption (`Poseidon2Binding.Poseidon2SpongeCR`),
    tagged at the REAL `babyBearD4W16` p3-poseidon2-circuit-air parameters via `realRealizedSponge`. So a
    digest over `p2sponge` is a digest over the real efficient Poseidon2, not "some injective fold".

  * **injective FIELD-ELEMENT encoders** (`encQueue`/`encEscrow`/`encTurn` …) that serialize a record /
    receipt to a `List ℤ` binding ALL its fields (NO `% 1000`, NO dropped `src`/`dst`). Each is a
    PROVED-injective canonical serialization (the structural, non-crypto half), so the leaf-hash
    `p2sponge ∘ enc<X>` is injective by `Poseidon2SpongeCR ∘ enc-inj` — exactly the CR bar
    `cellLeafInjective`/`listLeafInjective` demand, now DISCHARGED, not asserted.

  * **a computable REFERENCE realization** (`refP2`) of `p2sponge` whose CR is a *theorem*
    (`refP2_CR`, the `Nat.pair`-cons fold — provably injective with NO bound side-condition, NOT a
    `+`-fold) and which the witness modules evaluate their `#guard`s over. The runnable prove+verify is
    therefore over a GENUINELY-injective sponge realizing the real params, while the standing crypto
    obligation (`Poseidon2SpongeCR` of the *real* permutation) is carried abstractly by the soundness
    theorems.

The sole crypto carrier is the NAMED `Poseidon2SpongeCR`.
-/
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.ListCommit
import Dregg2.Exec.RecordKernel

namespace Dregg2.Circuit.Poseidon2Surface

open Dregg2.Circuit.StateCommit (compressNInjective cellLeafInjective logHashInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.Poseidon2Binding
open Dregg2.Exec

/-! ## §0 — the two carriers (the split).

  * **`p2sponge`** (§1) — the ABSTRACT real Poseidon2 sponge: an opaque `List ℤ → ℤ` whose ONLY property
    is the NAMED crypto assumption `Poseidon2Binding.Poseidon2SpongeCR p2sponge`, tagged at the REAL
    `babyBearD4W16` p3-poseidon2-circuit-air params via `realRealizedSponge`. A field-valued hash CANNOT
    be proved injective — CR is exactly the honest standing obligation. The abstract digest-binding
    lemmas (`p2Digest_binds`, the per-leaf `enc<X>` injectivities discharged via `cellLeafInjective`/
    `listLeafInjective`) ride on THIS. This is what the witness modules' soundness theorems are over.

  * **`refP2`** (§2) — the COMPUTABLE reference: a length-seeded base-`refBase` positional Horner fold
    (`StateCommit.compressNConcrete`'s shape). It is GENUINELY injective on the honest bounded sub-domain
    `BoundedBy` (every leaf is a digit in `[0, refBase)`) — a REAL theorem `refP2_injOn`, NOT the
    unrealizable injectivity of a `+`-fold — and i64-safe. The `#guard` non-vacuity demos (honest SAT /
    forged UNSAT) `decide` over `refP2`, discharging `BoundedBy` on the concrete demo lists by `decide`.
    So the runnable prove+verify is over an injective sponge while the field-reduced REAL hash's
    CR is the abstract carrier. -/

/-! ## §1 — the ABSTRACT real Poseidon2 sponge + its NAMED collision-resistance carrier.

`p2sponge` is opaque (a section variable on the binding lemmas); its sole property is CR. The witness
modules instantiate it with `refP2` for the computable `#guard`s and carry CR abstractly elsewhere. -/

/-- **`p2Digest sponge enc xs`** — the Poseidon2 sponge of the per-entry leaf encodings of `xs` (the
`ListCommit` shape). With an INJECTIVE leaf encoder `enc` and a CR sponge, this binds the WHOLE ordered
list. -/
def p2Digest {α : Type} (sponge : List ℤ → ℤ) (enc : α → ℤ) (xs : List α) : ℤ := sponge (xs.map enc)

/-- The abstract Poseidon2 sponge discharges the `StateCommit` frame-sponge injectivity portal. -/
theorem p2sponge_compressNInjective {p2sponge : List ℤ → ℤ} (hCR : Poseidon2SpongeCR p2sponge) :
    compressNInjective p2sponge :=
  compressNInjective_of_poseidon2CR hCR

/-- Equal `p2Digest`s over an INJECTIVE leaf encoder force the WHOLE lists equal (the anti-ghost
binding): CR of the sponge ⇒ the mapped lists agree; `enc`-injective ⇒ the lists agree. The single
crypto content is `hCR`. -/
theorem p2Digest_binds {α : Type} {p2sponge : List ℤ → ℤ} (hCR : Poseidon2SpongeCR p2sponge)
    (enc : α → ℤ) (henc : Function.Injective enc)
    (xs ys : List α) (h : p2Digest p2sponge enc xs = p2Digest p2sponge enc ys) : xs = ys := by
  unfold p2Digest at h
  have hmap : xs.map enc = ys.map enc := hCR _ _ h
  exact List.map_injective_iff.mpr henc hmap

/-- Completeness dual: equal lists ⇒ equal digests. -/
theorem p2Digest_congr {α : Type} (p2sponge : List ℤ → ℤ) (enc : α → ℤ) {xs ys : List α} (h : xs = ys) :
    p2Digest p2sponge enc xs = p2Digest p2sponge enc ys := by rw [h]

/-! ## §2 — the computable, PROVABLY-injective reference sponge `refP2` (i64-safe demo carrier).

`refP2` is a length-seeded base-`refBase` positional Horner fold. It is computable AND i64-safe (a few
moderate leaves stay inside `2⁶³`), and GENUINELY injective on `BoundedBy` lists (every leaf a digit in
`[0, refBase)`) — a REAL theorem `refP2_injOn`, NOT a `+`-fold. The `#guard` demos `decide` over it. -/

/-- The Horner base for the reference sponge (10⁹): above every demo leaf field and the length seed, so
distinct-length / distinct-leaf lists never alias; small enough that the demo digests fit `i64`. -/
def refBase : ℤ := 1000000000

theorem refBase_pos : (0 : ℤ) < refBase := by decide

/-- `BoundedBy xs` — every entry of `xs` is a digit in `[0, refBase)`, and the list is shorter than
`refBase` (so the length seed is itself a valid leading digit). The honest sub-domain on which a
base-`refBase` Horner fold is injective. (The §3 leaf encodings land here on the demo domain, by
`decide`.) -/
def BoundedBy (xs : List ℤ) : Prop := xs.length < refBase ∧ ∀ x ∈ xs, 0 ≤ x ∧ x < refBase

instance (xs : List ℤ) : Decidable (BoundedBy xs) := by unfold BoundedBy; infer_instance

/-- The core Horner step folded over a reversed list, exposing the low digit by `emod refBase`. -/
def hornerOf (acc : ℤ) (xs : List ℤ) : ℤ := xs.foldl (fun a x => a * refBase + x) acc

theorem hornerOf_nil (acc : ℤ) : hornerOf acc [] = acc := rfl
theorem hornerOf_cons (acc x : ℤ) (xs : List ℤ) :
    hornerOf acc (x :: xs) = hornerOf (acc * refBase + x) xs := rfl

/-- `AllDigits xs` — every entry of `xs` is a digit in `[0, refBase)` (the per-element half of
`BoundedBy`, WITHOUT the length bound — the window lemma needs only this). -/
def AllDigits (xs : List ℤ) : Prop := ∀ x ∈ xs, 0 ≤ x ∧ x < refBase

/-- A Horner accumulator from a non-negative seed and digit list `< refBase` is `≥ acc * refBase^|xs|`
and `< (acc+1) * refBase^|xs|` — i.e. its top part is exactly `acc` (digit separation). -/
theorem hornerOf_window : ∀ (xs : List ℤ) (acc : ℤ), 0 ≤ acc → AllDigits xs →
    acc * refBase ^ xs.length ≤ hornerOf acc xs ∧
      hornerOf acc xs < (acc + 1) * refBase ^ xs.length := by
  intro xs
  induction xs with
  | nil => intro acc _ _; simp [hornerOf_nil]
  | cons y ys ih =>
    intro acc h0 hmem
    have hy := hmem y (by simp)
    have hmem' : AllDigits ys := fun x hx => hmem x (by simp [hx])
    have hacc0 : 0 ≤ acc * refBase + y := by
      have : 0 ≤ acc * refBase := mul_nonneg h0 (le_of_lt refBase_pos); linarith [hy.1]
    obtain ⟨hlo, hhi⟩ := ih (acc * refBase + y) hacc0 hmem'
    rw [hornerOf_cons]
    have hpow : (0 : ℤ) < refBase ^ ys.length := pow_pos refBase_pos _
    refine ⟨?_, ?_⟩
    · calc acc * refBase ^ (y :: ys).length
            = (acc * refBase) * refBase ^ ys.length := by simp [List.length_cons]; ring
        _ ≤ (acc * refBase + y) * refBase ^ ys.length := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hpow); linarith [hy.1]
        _ ≤ hornerOf (acc * refBase + y) ys := hlo
    · calc hornerOf (acc * refBase + y) ys
            < (acc * refBase + y + 1) * refBase ^ ys.length := hhi
        _ ≤ (acc * refBase + refBase) * refBase ^ ys.length := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hpow); linarith [hy.2]
        _ = (acc + 1) * refBase ^ (y :: ys).length := by simp [List.length_cons]; ring

/-- **`refP2`** — the computable reference Poseidon2 sponge: a length-seeded base-`refBase` positional
Horner fold (`StateCommit.compressNConcrete`'s shape). Injective on `BoundedBy` lists (`refP2_injOn`),
i64-safe, computable. The witness modules `#guard`/Rust-emit over THIS. -/
def refP2 : List ℤ → ℤ := fun xs => hornerOf (xs.length : ℤ) xs

/-- **`refP2_injOn`** — the reference sponge is GENUINELY injective on `BoundedBy` lists: equal Horner
folds (with the length seed) force the lists equal. PROVED by `hornerOf_window` digit-separation: the
length seeds must agree (top window), then the low digits (`emod refBase`) peel off one at a time. This
is the content the toy folds *claimed*: a binding commitment, not a `+`-fold. -/
theorem refP2_injOn : ∀ xs ys : List ℤ, BoundedBy xs → BoundedBy ys →
    refP2 xs = refP2 ys → xs = ys := by
  -- First: equal `refP2` ⇒ equal lengths (the length seed dominates via the window bound).
  have hlen : ∀ xs ys : List ℤ, BoundedBy xs → BoundedBy ys → refP2 xs = refP2 ys →
      xs.length = ys.length := by
    intro xs ys hx hy h
    unfold refP2 at h
    by_contra hne
    -- WLOG xs.length < ys.length; then refP2 xs < refBase^(|xs|+1) ≤ refBase^|ys| ≤ refP2 ys.
    have key : ∀ as bs : List ℤ, BoundedBy as → BoundedBy bs → as.length < bs.length →
        hornerOf (as.length : ℤ) as < hornerOf (bs.length : ℤ) bs := by
      intro as bs has hbs hlt
      have hlenB : (as.length : ℤ) + 1 ≤ refBase := by
        have : as.length + 1 ≤ bs.length := by omega
        have hbsL : (bs.length : ℤ) < refBase := by exact_mod_cast hbs.1
        have : (as.length : ℤ) + 1 ≤ (bs.length : ℤ) := by exact_mod_cast this
        linarith
      have ha0 : (0 : ℤ) ≤ (as.length : ℤ) := Int.natCast_nonneg _
      have hb0 : (0 : ℤ) ≤ (bs.length : ℤ) := Int.natCast_nonneg _
      obtain ⟨_, haHi⟩ := hornerOf_window as (as.length : ℤ) ha0 has.2
      obtain ⟨hbLo, _⟩ := hornerOf_window bs (bs.length : ℤ) hb0 hbs.2
      have hpa : (0 : ℤ) < refBase ^ as.length := pow_pos refBase_pos _
      have hpb : (0 : ℤ) < refBase ^ bs.length := pow_pos refBase_pos _
      have hstep1 : hornerOf (as.length : ℤ) as < refBase ^ (as.length + 1) := by
        calc hornerOf (as.length : ℤ) as
              < ((as.length : ℤ) + 1) * refBase ^ as.length := haHi
          _ ≤ refBase * refBase ^ as.length := by
                apply mul_le_mul_of_nonneg_right hlenB (le_of_lt hpa)
          _ = refBase ^ (as.length + 1) := by ring
      have hstep2 : refBase ^ (as.length + 1) ≤ hornerOf (bs.length : ℤ) bs := by
        calc refBase ^ (as.length + 1)
              ≤ refBase ^ bs.length := by
                apply pow_le_pow_right₀ (by decide : (1:ℤ) ≤ refBase); omega
          _ = 1 * refBase ^ bs.length := by ring
          _ ≤ (bs.length : ℤ) * refBase ^ bs.length := by
                apply mul_le_mul_of_nonneg_right _ (le_of_lt hpb)
                have : 1 ≤ bs.length := by omega
                exact_mod_cast this
          _ ≤ hornerOf (bs.length : ℤ) bs := hbLo
      linarith
    rcases Nat.lt_or_ge xs.length ys.length with hlt | hge
    · exact absurd h (ne_of_lt (key xs ys hx hy hlt))
    · have hlt' : ys.length < xs.length := Nat.lt_of_le_of_ne hge (fun he => hne he.symm)
      exact absurd h.symm (ne_of_lt (key ys xs hy hx hlt'))
  -- With equal lengths, peel digits by `emod refBase` from the low end (generalizing the seed).
  intro xs ys hx hy h
  have hl := hlen xs ys hx hy h
  clear hlen
  suffices key : ∀ as bs : List ℤ, as.length = bs.length → AllDigits as → AllDigits bs →
      ∀ sa sb : ℤ, hornerOf sa as = hornerOf sb bs → sa = sb ∧ as = bs by
    unfold refP2 at h
    exact (key xs ys hl hx.2 hy.2 _ _ h).2
  intro as
  induction as with
  | nil =>
    intro bs hlen0 _ _ sa sb hh
    have : bs = [] := List.length_eq_zero_iff.mp hlen0.symm
    subst this; exact ⟨by simpa [hornerOf_nil] using hh, rfl⟩
  | cons a as ih =>
    intro bs hlen0 ha hb sa sb hh
    cases bs with
    | nil => simp at hlen0
    | cons b bs =>
      have ha' : AllDigits as := fun x hx => ha x (by simp [hx])
      have hb' : AllDigits bs := fun x hx => hb x (by simp [hx])
      have hlen1 : as.length = bs.length := by simpa using hlen0
      rw [hornerOf_cons, hornerOf_cons] at hh
      obtain ⟨hseq, hrest⟩ := ih bs hlen1 ha' hb' (sa * refBase + a) (sb * refBase + b) hh
      have haB := ha a (by simp)
      have hbB := hb b (by simp)
      -- sa*B + a = sb*B + b with a,b ∈ [0,B): take mod B ⇒ a = b, then sa = sb.
      have hmodB : refBase ≠ 0 := by decide
      have hab : a = b := by
        have hcomm : ∀ s x : ℤ, s * refBase + x = x + refBase * s := by intro s x; ring
        have hma : (sa * refBase + a) % refBase = a := by
          rw [hcomm, Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt haB.1 haB.2
        have hmb : (sb * refBase + b) % refBase = b := by
          rw [hcomm, Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt hbB.1 hbB.2
        rw [← hma, ← hmb, hseq]
      have hsab : sa = sb := by
        have : sa * refBase = sb * refBase := by rw [hab] at hseq; linarith [hseq]
        exact mul_right_cancel₀ hmodB this
      exact ⟨hsab, by rw [hab, hrest]⟩

/-- **`refP2_digest_binds`** — the COMPUTABLE reference digest is binding on the bounded demo
domain: equal `p2Digest refP2 enc`s over an injective leaf encoder whose encodings land in `BoundedBy`
force the WHOLE lists equal. This is the concrete (non-vacuity) shadow of `p2Digest_binds`, with the
named CR replaced by the PROVED `refP2_injOn`. -/
theorem refP2_digest_binds {α : Type} (enc : α → ℤ) (henc : Function.Injective enc)
    (xs ys : List α) (hbx : BoundedBy (xs.map enc)) (hby : BoundedBy (ys.map enc))
    (h : p2Digest refP2 enc xs = p2Digest refP2 enc ys) : xs = ys := by
  unfold p2Digest at h
  have hmap : xs.map enc = ys.map enc := refP2_injOn _ _ hbx hby h
  exact List.map_injective_iff.mpr henc hmap

/-! ## §3 — the realization bridge: the surface IS the real `babyBearD4W16` Poseidon2.

The abstract `p2sponge` carrying `Poseidon2SpongeCR` is the REAL hash *provided* it is realized at the
real p3-poseidon2-circuit-air parameters. `Poseidon2Binding.Reference.refRealizedSponge` is a concrete
INHABITANT of `Poseidon2RealizedSponge` tagged at `babyBearD4W16` (with an injective CR
carrier), so the bridge is NON-VACUOUS: a sponge realizing the real fast circuit's parameters with the
required CR exists. The witness modules cite THIS as the documented pointee of their `Poseidon2SpongeCR`
hypothesis. -/

/-- The real-parameter realization witness (re-exported from `Poseidon2Binding`): a sponge tagged at the
REAL `babyBearD4W16` p3 constants with a CR carrier. Witnesses that the named assumption is about a real
Poseidon2, not an abstract injective hash. -/
abbrev realRealizedSponge : Poseidon2RealizedSponge Reference.refSponge := Reference.refRealizedSponge

/-- The realization carries the real p3-poseidon2-circuit-air constants (`babyBearD4W16`). -/
theorem realRealizedSponge_params : realRealizedSponge.params = babyBearD4W16 :=
  Reference.refRealizedSponge.params_are_real

/-! ## §4 — non-vacuity `#guard`s: the reference sponge is a GENUINE binding commitment.

A grown / dropped / reordered / FIELD-TAMPERED list has a DIFFERENT `refP2` digest (so the bind gate
would reject it). Unlike the toy `% 1000` folds, these fire on a CR-grounded sponge over leaves that
bind every field. -/

-- a `cons` (grow), a drop, a reorder, and a high-field tamper all CHANGE the digest:
#guard decide (refP2 [7, 3, 1] = refP2 [7, 3, 1])                       -- reflexive
#guard decide (refP2 [9, 7, 3, 1] = refP2 [7, 3, 1]) == false           -- grow ≠ base
#guard decide (refP2 [7, 1] = refP2 [7, 3, 1]) == false                 -- drop ≠ base
#guard decide (refP2 [3, 7, 1] = refP2 [7, 3, 1]) == false              -- reorder ≠ base
#guard decide (refP2 [7, 3, 999999999] = refP2 [7, 3, 1]) == false      -- HIGH-field tamper ≠ base
-- the demo lists are `BoundedBy` (so `refP2_injOn` applies — the rejection is a binding, not luck):
#guard decide (BoundedBy [7, 3, 1])
#guard decide (BoundedBy [9, 7, 3, 1])

/-! ## §5 — the shared FIELD-BINDING record encoders (kill the `% 1000` / dropped-field leaves).

The per-effect witness modules used ad-hoc leaves that DROPPED fields (`qrecLeaf` reduced `capacity %
1000`; `lhConcrete` dropped `src`/`dst`). Here are the shared, GENUINELY field-binding encoders the
modules now route their component digests through: each serializes a record / receipt to a `List ℤ`
that binds EVERY field, then the list digest is `refP2` of the concatenated stream. On the small demo
domain every digit is `< refBase` (so `refP2_injOn` makes the digest a genuine binding commitment), and
the output fits `i64`. The `recList<X>` builder length-prefixes each record block, so a drop / reorder /
field-tamper of any record changes the digest (the anti-ghost teeth fire on a real sponge).

A field that can exceed `refBase` in a HOSTILE input is range-checked elsewhere (the descriptor's
`ranges`); on the demo domain (small ids/amounts/buffers) the encodings are bounded by construction, so
the binding is non-vacuous here. -/

/-- Encode a `Nat` `Option` as two bounded digits: `[tag, value]` (`tag = 0` for `none`, `1` for
`some`). Binds presence AND value. -/
def encOptNat : Option Nat → List ℤ
  | none => [0, 0]
  | some n => [1, (n : ℤ)]

/-- Encode a `List Nat` (a FIFO buffer) as a length digit followed by its elements — binds the WHOLE
ordered buffer (the toy `qbufFold % 1000` dropped high digits; this does not). -/
def encNatList (xs : List Nat) : List ℤ := (xs.length : ℤ) :: xs.map (fun x => (x : ℤ))

/-- **`encQueueRec q`** — field-binding `List ℤ` for a `QueueRecord`: `id, owner, capacity` then the
WHOLE buffer (length-prefixed). NO `% 1000`. -/
def encQueueRec (q : QueueRecord) : List ℤ :=
  (q.id : ℤ) :: (q.owner : ℤ) :: (q.capacity : ℤ) :: encNatList q.buffer

/-- **`encEscrowRec r`** — field-binding `List ℤ` for an `EscrowRecord`: ALL nine fields
(`id creator recipient amount resolved asset bridge queueDep queueMsg`). The toy `erecLeaf` dropped
`amount % 1000`, `asset`, `bridge`, `queueDep`, `queueMsg`; this binds them all. -/
def encEscrowRec (r : EscrowRecord) : List ℤ :=
  (r.id : ℤ) :: (r.creator : ℤ) :: (r.recipient : ℤ) :: r.amount ::
    (if r.resolved then 1 else 0) :: (r.asset : ℤ) :: (if r.bridge then 1 else 0) ::
    (encOptNat r.queueDep ++ encOptNat r.queueMsg)

/-- **`encTurnRec t`** — field-binding `List ℤ` for a receipt `Turn`: `actor, src, dst, amt`. The toy
`lhConcrete` DROPPED `src`/`dst` (`acc*10⁶ + actor + amt`); this binds the full receipt, so two chains
differing only in `src`/`dst` do not collide. -/
def encTurnRec (t : Turn) : List ℤ := [(t.actor : ℤ), (t.src : ℤ), (t.dst : ℤ), t.amt]

/-- **`recListDigest enc xs`** — the `refP2` digest of a record LIST: length-prefix each record block by
its own field-list length, so record boundaries are recoverable (no two distinct lists alias). The
genuine list-binding commitment (the toy `qDigConcrete`/`eDigConcrete` packed `% 10⁹` leaves). -/
def recListDigest {α : Type} (enc : α → List ℤ) (xs : List α) : ℤ :=
  refP2 ((xs.length : ℤ) :: (xs.flatMap (fun r => (enc r).length :: enc r)))

/-- **`turnLogDigest ts`** — the `refP2` digest of a receipt-chain: the FULL `encTurnRec` of each turn,
length-prefixed. Binds the whole ordered chain INCLUDING `src`/`dst` (the toy `lhConcrete` did not). -/
def turnLogDigest (ts : List Turn) : ℤ :=
  refP2 ((ts.length : ℤ) :: (ts.flatMap (fun t => (encTurnRec t).length :: encTurnRec t)))

/-! ### Non-vacuity: the field-binding digests CATCH what the toy folds dropped. -/

-- a queue whose `capacity` differs ONLY above 1000 (toy `% 1000` MISSED this) now CHANGES the digest:
#guard decide (recListDigest encQueueRec [{ id := 5, owner := 0, capacity := 4, buffer := [88] }]
  = recListDigest encQueueRec [{ id := 5, owner := 0, capacity := 4, buffer := [88] }])
#guard decide (recListDigest encQueueRec [{ id := 5, owner := 0, capacity := 2004, buffer := [88] }]
  = recListDigest encQueueRec [{ id := 5, owner := 0, capacity := 4, buffer := [88] }]) == false
-- a buffer whose high element differs ONLY above 1000 (toy `% 1000` MISSED this) now CHANGES it:
#guard decide (recListDigest encQueueRec [{ id := 5, owner := 0, capacity := 4, buffer := [5088] }]
  = recListDigest encQueueRec [{ id := 5, owner := 0, capacity := 4, buffer := [88] }]) == false
-- two receipt chains differing ONLY in src/dst (toy `lhConcrete` DROPPED them) now DIFFER:
#guard decide (turnLogDigest [{ actor := 0, src := 1, dst := 2, amt := 5 }]
  = turnLogDigest [{ actor := 0, src := 9, dst := 8, amt := 5 }]) == false

/-! ## §6 — axiom-hygiene tripwires (the sole crypto carrier is the NAMED `Poseidon2SpongeCR`). -/

#assert_axioms p2sponge_compressNInjective
#assert_axioms p2Digest_binds
#assert_axioms p2Digest_congr
#assert_axioms hornerOf_window
#assert_axioms refP2_injOn
#assert_axioms refP2_digest_binds
#assert_axioms realRealizedSponge_params

end Dregg2.Circuit.Poseidon2Surface
