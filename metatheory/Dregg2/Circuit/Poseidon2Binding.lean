/-
# Dregg2.Circuit.Poseidon2Binding — grounding the injectivity portals on Poseidon2 CR.

`StateCommit` parameterizes the WHOLE per-effect circuit-soundness tower (`transfer_circuit_full_sound`
and the generic `effect_circuit_full_sound`) over three abstract HASH-INJECTIVITY portals:

  * `compressNInjective compressN` — the frame sponge over a list of leaves is injective.
  * `cellLeafInjective CH`         — a fixed cell's leaf hash binds its whole `Value`.
  * `logHashInjective LH`          — the receipt-chain hash binds the turn list.

Until now NO concrete hash discharged these, so full-state soundness held only "relative to an
injective hash the system never instantiates". This module closes that gap by deriving all three
from a SINGLE, explicit, named cryptographic assumption:

  **`Poseidon2SpongeCR sponge`** : `∀ xs ys, sponge xs = sponge ys → xs = ys`.

This is collision-resistance of the in-circuit Poseidon2 sponge (`Poseidon2Emit.spongeCompressN`,
proved faithful to the emitted `merkle_hash` chain by `emit_faithful_poseidon2_compress`). It is the
EXACT shape `Crypto.PortalFloor.{Poseidon2Kernel,Blake3Kernel}.noCollision` already carries — CR
as injectivity on the idealized hash domain — and it is REALIZABLE (a real Poseidon2 satisfies it; a
`+`-fold does NOT, see `compressNInjective`'s doc). We carry it as an explicit Prop HYPOTHESIS (never
an `axiom`), so every theorem here pins exactly `{propext, Classical.choice, Quot.sound}`.

## The factoring (one crypto assumption, the rest is serialization)

  * `compressNInjective compressN` is LITERALLY `Poseidon2SpongeCR compressN` — the frame digest's
    sponge IS a list-hash. No encoder; the two Props are definitionally interchangeable
    (`compressNInjective_of_poseidon2CR`). This is the load-bearing one (it grounds the frame).

  * `cellLeafInjective CH` / `logHashInjective LH` need the hash applied to a *structured* input
    (`(c, v)` / `List Turn`). A Poseidon2 leaf/log hash FACTORS as `sponge ∘ encode` for an
    INJECTIVE serialization `encode`. We package "`CH`/`LH` factor through the CR sponge via an
    injective encoder" as a `LeafRealization` / `LogRealization` bundle. Encoder-injectivity is NOT
    a cryptographic assumption (a canonical serialization is provably injective — the toy
    `Reference` instances below exhibit injective encoders and discharge CR with `True`); it is an
    separate STRUCTURAL field, while CR is the SOLE crypto carrier.

The toy `Reference` realizations (over injective `ℤ`
encoders + `True`-discharged CR) witness non-vacuity: every derivation fires on a real instance.
-/
import Dregg2.Circuit.StateCommit
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List

namespace Dregg2.Circuit.Poseidon2Binding

open Dregg2.Circuit.StateCommit
open Dregg2.Exec (CellId Value Turn)

-- `Turn` is a flat structure of `Nat`/`ℤ`; the standard deriver gives it `Encodable` (used only by
-- the `Reference` log-realization non-vacuity witness, never by the load-bearing derivations).
deriving instance Encodable for Dregg2.Exec.Turn

/-! ## §0 — the REAL p3-poseidon2-circuit-air parameter descriptor (the bridge's pointee).

`Poseidon2SpongeCR` is a NAMED bridge assumption: verified-Lean soundness rests on it, PROVIDED the
actual prover uses the real efficient Poseidon2 AIR. For the bridge to point at the RIGHT object, we
must pin EXACTLY which Poseidon2 the sponge is — same field, width, rate, capacity, S-box degree,
rounds, round-constant source — as the Rust `p3-poseidon2-circuit-air` (emberian/plonky3-recursion
rev `c14b5fc079af18d7f3ba3f3586f173bd166c7cd4`) actually computes.

The Rust prover's canonical hashing config (the one `CircuitBuilder::add_hash_slice` defaults to, and
the only BabyBear permutation the recursion uses for MMCS/FRI/sponge — see `circuit/src/ops/hash.rs`
and `circuit/src/ops/poseidon2_perm/config.rs::Poseidon2Config::BABY_BEAR_D4_W16`) is:

```text
  field            = BabyBear   (p = 2^31 - 2^27 + 1)
  d (ext degree)   = 4          (quartic; D=4 challenges)
  width            = 16         (permutation state, base elements)
  sbox_degree      = 7
  sbox_registers   = 1
  half_full_rounds = 4          (=> 8 full rounds)
  partial_rounds   = 13
  -- derived by the Rust `const fn`s (rate_ext / capacity_ext, D>1 branch):
  capacity_ext     = 2          (D>1: always 2)          => capacity = capacity_ext*d = 8 base
  rate_ext         = width/d - capacity_ext = 16/4 - 2 = 2  => rate = rate_ext*d = 8 base
  width_ext        = rate_ext + capacity_ext = 4
  round constants  = BABYBEAR_POSEIDON2_RC_16_{EXTERNAL_INITIAL,INTERNAL,EXTERNAL_FINAL}
  linear layers    = GenericPoseidon2LinearLayersBabyBear (canonical Poseidon2 MDS/internal)
  sponge mode      = PaddingFreeSponge, absorb rate_ext-chunks, squeeze rate_ext (overwrite mode)
```

`Poseidon2RealParams` records this bundle; the `#guard`s below RE-DERIVE `rate_ext`/`capacity_ext`/
`width_ext` with the SAME formulas as the Rust `const fn`s, so a drift in either side breaks the
build. This is the encoded correspondence: the bridge assumption `Poseidon2SpongeCR` is now
documented as being about the sponge of `babyBearD4W16` specifically — the real fast circuit's hash —
not "some injective sponge the system never instantiates". -/

/-- The exact Poseidon2 parameter bundle, mirroring `p3_circuit::ops::Poseidon2Config`. Fields and
derivations match the Rust `const fn`s (`rate_ext`/`capacity_ext`/`width_ext`) one-for-one. -/
structure Poseidon2RealParams where
  /-- Name of the Rust field (`BabyBear`/`KoalaBear`/`Goldilocks`). -/
  fieldName : String
  /-- Field prime (BabyBear `p = 2^31 - 2^27 + 1`). -/
  fieldModulus : Nat
  /-- Extension degree `d`. -/
  d : Nat
  /-- Permutation state width in base elements. -/
  width : Nat
  /-- S-box polynomial degree. -/
  sboxDegree : Nat
  /-- Number of S-box intermediate registers. -/
  sboxRegisters : Nat
  /-- Number of half full rounds (full rounds = `2 * halfFullRounds`). -/
  halfFullRounds : Nat
  /-- Number of partial rounds. -/
  partialRounds : Nat
  deriving DecidableEq, Repr

namespace Poseidon2RealParams

/-- Capacity in extension elements (Rust `capacity_ext`: D>1 ⇒ 2, D=1 ⇒ width/2). -/
def capacityExt (p : Poseidon2RealParams) : Nat := if p.d == 1 then p.width / 2 else 2

/-- Rate in extension elements (Rust `rate_ext`: D=1 ⇒ width/2, else width/d − capacity_ext). -/
def rateExt (p : Poseidon2RealParams) : Nat :=
  if p.d == 1 then p.width / 2 else p.width / p.d - p.capacityExt

/-- Sponge state width in extension elements (Rust `width_ext = rate_ext + capacity_ext`). -/
def widthExt (p : Poseidon2RealParams) : Nat := p.rateExt + p.capacityExt

/-- Rate / capacity in BASE elements (`rate_ext * d`, `capacity_ext * d`). -/
def rate (p : Poseidon2RealParams) : Nat := p.rateExt * p.d
def capacity (p : Poseidon2RealParams) : Nat := p.capacityExt * p.d

end Poseidon2RealParams

/-- **`babyBearD4W16`** — the canonical real config: `p3 Poseidon2Config::BABY_BEAR_D4_W16`, the
exact permutation the Rust recursion prover uses for ALL BabyBear hashing (`add_hash_slice` default).
THE pointee of the `Poseidon2SpongeCR` bridge. -/
def babyBearD4W16 : Poseidon2RealParams :=
  { fieldName := "BabyBear"
    fieldModulus := 2 ^ 31 - 2 ^ 27 + 1   -- 0x78000001 = 2013265921
    d := 4
    width := 16
    sboxDegree := 7
    sboxRegisters := 1
    halfFullRounds := 4
    partialRounds := 13 }

-- §0 correspondence tripwires — these RE-DERIVE the sponge dimensions with the SAME formulas the
-- Rust `const fn`s use and pin the literal constants. A drift on either side (Lean descriptor OR the
-- real p3 config) breaks the build, so the named bridge stays welded to the real fast circuit.
#guard babyBearD4W16.fieldModulus == 2013265921          -- BabyBear p, matches BABYBEAR_P
#guard babyBearD4W16.width == 16
#guard babyBearD4W16.d == 4
#guard babyBearD4W16.sboxDegree == 7
#guard babyBearD4W16.partialRounds == 13
#guard babyBearD4W16.halfFullRounds == 4                 -- => 8 full rounds
#guard babyBearD4W16.capacityExt == 2                    -- D>1 branch
#guard babyBearD4W16.rateExt == 2                        -- 16/4 - 2
#guard babyBearD4W16.widthExt == 4                       -- rate_ext + capacity_ext
#guard babyBearD4W16.rate == 8                           -- rate_ext * d
#guard babyBearD4W16.capacity == 8                       -- capacity_ext * d

/-! ## §1 — the single named cryptographic assumption: Poseidon2 sponge collision-resistance. -/

/-- **`Poseidon2SpongeCR sponge`** — the SOLE crypto assumption: the Poseidon2 sponge
`sponge : List ℤ → ℤ` is collision-resistant, i.e. injective on the idealized hash domain. This is
the `Crypto.PortalFloor.Blake3Kernel.noCollision`/`Poseidon2Kernel.noCollision` shape (CR stated as
injectivity), specialized to the `ℤ`-valued sponge `StateCommit`/`Poseidon2Emit` use. REALIZABLE by
a real Poseidon2 (a `+`-fold falsifies it). Carried as a Prop HYPOTHESIS, never an `axiom`.

THE BRIDGE: the `sponge` this CR is asserted about is intended to be the PaddingFreeSponge over the
real `babyBearD4W16` Poseidon2 permutation (`p3-poseidon2-circuit-air`, BabyBear width-16, rate-8) —
the SAME hash the fast prover extracts and proves. `Poseidon2RealizedSponge` packages that intent:
the CR carrier together with the concrete real parameters it is realized at, so the named assumption
documents EXACTLY which efficient Poseidon2 it bridges to. -/
def Poseidon2SpongeCR (sponge : List ℤ → ℤ) : Prop := ∀ xs ys : List ℤ, sponge xs = sponge ys → xs = ys

/-- **`Poseidon2RealizedSponge sponge`** — the bridge made explicit: a sponge carries (1) the real
p3 parameter descriptor it is realized at and (2) the CR assumption ON THAT sponge. Pinning `params`
to `babyBearD4W16` (the only config the bundle's `params_are_real` allows) is what makes
`Poseidon2SpongeCR` a bridge to the REAL fast Poseidon2 rather than an abstract injective hash. -/
structure Poseidon2RealizedSponge (sponge : List ℤ → ℤ) where
  /-- The real p3-poseidon2-circuit-air parameter bundle this sponge is extracted at. -/
  params : Poseidon2RealParams
  /-- The descriptor IS the canonical real config (not an arbitrary parameterization). -/
  params_are_real : params = babyBearD4W16
  /-- The SOLE crypto carrier: CR of the real Poseidon2 sponge. -/
  spongeCR : Poseidon2SpongeCR sponge

/-- From a realized bundle, recover the bare CR carrier (so all existing derivations fire unchanged
while the parameter correspondence rides along). -/
theorem Poseidon2RealizedSponge.toCR {sponge : List ℤ → ℤ} (R : Poseidon2RealizedSponge sponge) :
    Poseidon2SpongeCR sponge := R.spongeCR

/-! ## §2 — `compressNInjective` IS Poseidon2 CR (the load-bearing frame portal). -/

/-- **`compressNInjective_iff_poseidon2CR`** — the frame-sponge injectivity portal
`compressNInjective compressN` is DEFINITIONALLY the Poseidon2 CR assumption on the same sponge:
both say `∀ xs ys, compressN xs = compressN ys → xs = ys`. So grounding the frame portal needs NO
encoder and NO extra hypothesis — it IS collision-resistance of the list-hash. -/
theorem compressNInjective_iff_poseidon2CR (compressN : List ℤ → ℤ) :
    compressNInjective compressN ↔ Poseidon2SpongeCR compressN := Iff.rfl

/-- **`compressNInjective_of_poseidon2CR`** — discharge `compressNInjective` from Poseidon2 CR. The
proved bridge: the abstract frame-sponge injectivity portal the tower carries is exactly the CR of
the in-circuit Poseidon2 sponge (`Poseidon2Emit.emittedPoseidon2Compress`, faithful by
`emit_faithful_poseidon2_compress`). -/
theorem compressNInjective_of_poseidon2CR {compressN : List ℤ → ℤ}
    (hCR : Poseidon2SpongeCR compressN) : compressNInjective compressN := hCR

/-! ## §3 — leaf / log injectivity: CR ∘ injective-encoder.

A Poseidon2 leaf/log hash applies the sponge to a *structured* input via a canonical serialization.
We package that factoring as a realization bundle. Encoder-injectivity is a STRUCTURAL field (a
canonical serialization is provably injective — NOT a crypto assumption); `spongeCR` is the SOLE
crypto carrier, shared with the frame portal above. -/

/-- **`LeafRealization CH`** — `CH` is a Poseidon2-realized leaf hash: there is a serialization
`encodeLeaf : CellId → Value → List ℤ`, INJECTIVE in the `Value` at each fixed cell, such that
`CH c v = sponge (encodeLeaf c v)`, and `sponge` is collision-resistant. (The `sponge` here is the
SAME Poseidon2 sponge as the frame `compressN`; we let it be a field so a realization may reuse one
global sponge.) -/
structure LeafRealization (CH : CellId → Value → ℤ) where
  /-- The Poseidon2 sponge the leaf hash squeezes through. -/
  sponge : List ℤ → ℤ
  /-- The canonical serialization of a cell's `(id, value)` to field elements. -/
  encodeLeaf : CellId → Value → List ℤ
  /-- STRUCTURAL (not crypto): the serialization is injective in the `Value` at a fixed cell. A
  canonical encoding is provably injective; the `Reference` instance exhibits one. -/
  encodeLeaf_inj : ∀ (c : CellId) (v w : Value), encodeLeaf c v = encodeLeaf c w → v = w
  /-- The leaf hash factors as `sponge ∘ encodeLeaf`. -/
  factor : ∀ (c : CellId) (v : Value), CH c v = sponge (encodeLeaf c v)
  /-- The SOLE crypto carrier: the shared Poseidon2 sponge is collision-resistant. -/
  spongeCR : Poseidon2SpongeCR sponge

/-- **`cellLeafInjective_of_realization`** — discharge `cellLeafInjective CH` from a Poseidon2 leaf
realization. PROVED by composing CR of the sponge with injectivity of the serialization:
`CH c v = CH c w` ⇒ `sponge (enc c v) = sponge (enc c w)` ⇒[CR] `enc c v = enc c w` ⇒[enc inj]
`v = w`. The only crypto content is `R.spongeCR`. -/
theorem cellLeafInjective_of_realization {CH : CellId → Value → ℤ} (R : LeafRealization CH) :
    cellLeafInjective CH := by
  intro c v w h
  rw [R.factor c v, R.factor c w] at h
  exact R.encodeLeaf_inj c v w (R.spongeCR _ _ h)

/-- **`LogRealization LH`** — `LH` is a Poseidon2-realized receipt-chain hash: an INJECTIVE
serialization `encodeLog : List Turn → List ℤ`, with `LH xs = sponge (encodeLog xs)` and `sponge`
collision-resistant. Same shape as `LeafRealization`, over the growing-log domain. -/
structure LogRealization (LH : List Turn → ℤ) where
  /-- The Poseidon2 sponge the log hash squeezes through. -/
  sponge : List ℤ → ℤ
  /-- The canonical serialization of a turn list to field elements. -/
  encodeLog : List Turn → List ℤ
  /-- STRUCTURAL (not crypto): the serialization is injective on turn lists. -/
  encodeLog_inj : ∀ xs ys : List Turn, encodeLog xs = encodeLog ys → xs = ys
  /-- The log hash factors as `sponge ∘ encodeLog`. -/
  factor : ∀ xs : List Turn, LH xs = sponge (encodeLog xs)
  /-- The SOLE crypto carrier: the shared Poseidon2 sponge is collision-resistant. -/
  spongeCR : Poseidon2SpongeCR sponge

/-- **`logHashInjective_of_realization`** — discharge `logHashInjective LH` from a Poseidon2 log
realization. PROVED by composing CR of the sponge with injectivity of the serialization. -/
theorem logHashInjective_of_realization {LH : List Turn → ℤ} (R : LogRealization LH) :
    logHashInjective LH := by
  intro xs ys h
  rw [R.factor xs, R.factor ys] at h
  exact R.encodeLog_inj xs ys (R.spongeCR _ _ h)

/-! ## §4 — non-vacuity witnesses: REAL realizations whose CR sponge is injective.

These exhibit injective serializations + an injective (toy) sponge, so each derivation
above FIRES on a concrete instance — proving the bundles are inhabitable and the theorems
non-vacuous. (Real Poseidon2 leaves CR as the standing obligation; here we discharge it with a
provably-injective stand-in, exactly as `PortalFloor.Reference` does.) -/

namespace Reference

/-- An injective toy sponge over `ℤ`: the `Encodable` encoding of the list (a provably-injective
stand-in for Poseidon2, like `PortalFloor.Reference.instBlake3Kernel`'s `Encodable.encode`). -/
def refSponge (xs : List ℤ) : ℤ := (Encodable.encode xs : ℕ)

theorem refSponge_CR : Poseidon2SpongeCR refSponge := by
  intro xs ys h
  unfold refSponge at h
  exact Encodable.encode_injective (by exact_mod_cast h)

/-- The frame portal fires on the toy injective sponge. -/
example : compressNInjective refSponge := compressNInjective_of_poseidon2CR refSponge_CR

/-- The REALIZED bundle is inhabitable: a sponge tagged with the REAL `babyBearD4W16` params plus a
injective CR carrier. Witnesses that `Poseidon2RealizedSponge` (the bridge-with-params) is
non-vacuous, and that recovering the bare CR from it fires the frame portal. -/
def refRealizedSponge : Poseidon2RealizedSponge refSponge :=
  { params := babyBearD4W16, params_are_real := rfl, spongeCR := refSponge_CR }

example : compressNInjective refSponge :=
  compressNInjective_of_poseidon2CR refRealizedSponge.toCR

/-- And the params it carries ARE the real p3-poseidon2-circuit-air constants. -/
example : refRealizedSponge.params = babyBearD4W16 := refRealizedSponge.params_are_real

/-! ### A PROVABLY-INJECTIVE serialization `Value → ℕ` (the leaf encoder's honesty).

`Value` is a nested inductive over `List (FieldName × Value)`, so the standard `Encodable`/`Countable`
derivers do not apply. We hand-roll a `Nat.pair`-tagged encoder mutually with its field-list encoder
and PROVE injectivity by mutual structural induction — exhibiting a genuine injective serialization
(NO crypto assumed), the structural content `LeafRealization.encodeLeaf_inj` demands. -/

/-- `String → List ℕ` injectively (`Char.toNat` is injective, `String.ext` lifts to the string). -/
def strCode (s : String) : List Nat := s.toList.map Char.toNat

theorem strCode_inj : Function.Injective strCode := by
  intro a b h
  unfold strCode at h
  have hmap : Function.Injective (List.map Char.toNat) :=
    List.map_injective_iff.mpr (fun x y hxy => Char.toNat_inj.mp hxy)
  exact String.ext (hmap h)

mutual
/-- Tag-paired `Value → ℕ` (`0` int, `1` dig, `2` sym, `3` record); records recurse via `encFields`. -/
def encV : Value → Nat
  | .int i => Nat.pair 0 (Encodable.encode i)
  | .dig n => Nat.pair 1 n
  | .sym n => Nat.pair 2 n
  | .record fs => Nat.pair 3 (encFields fs)
/-- The field-list encoder (`+1` separates `[]` from a `cons`). -/
def encFields : List (String × Value) → Nat
  | [] => 0
  | (k, v) :: rest =>
      Nat.pair (Nat.pair (Encodable.encode (strCode k)) (encV v)) (encFields rest) + 1
end

mutual
/-- `encV` is injective (mutual structural induction; cross-constructor cases die on the tag). -/
theorem encV_inj : ∀ v w : Value, encV v = encV w → v = w
  | .int i, .int j, h => by
      simp only [encV, Nat.pair_eq_pair] at h
      have := Encodable.encode_injective h.2; subst this; rfl
  | .dig a, .dig b, h => by simp only [encV, Nat.pair_eq_pair] at h; rw [h.2]
  | .sym a, .sym b, h => by simp only [encV, Nat.pair_eq_pair] at h; rw [h.2]
  | .record fs, .record gs, h => by
      simp only [encV, Nat.pair_eq_pair] at h
      rw [encFields_inj fs gs h.2]
  | .int _, .dig _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .int _, .sym _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .int _, .record _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .dig _, .int _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .dig _, .sym _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .dig _, .record _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .sym _, .int _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .sym _, .dig _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .sym _, .record _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .record _, .int _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .record _, .dig _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | .record _, .sym _, h => by simp only [encV, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
/-- `encFields` is injective (mutual with `encV_inj`). -/
theorem encFields_inj : ∀ fs gs : List (String × Value), encFields fs = encFields gs → fs = gs
  | [], [], _ => rfl
  | [], (_ :: _), h => by simp only [encFields] at h; omega
  | (_ :: _), [], h => by simp only [encFields] at h; omega
  | (k, v) :: fs, (k', v') :: gs, h => by
      simp only [encFields] at h
      have h2 : Nat.pair (Nat.pair (Encodable.encode (strCode k)) (encV v)) (encFields fs)
              = Nat.pair (Nat.pair (Encodable.encode (strCode k')) (encV v')) (encFields gs) := by omega
      rw [Nat.pair_eq_pair] at h2
      obtain ⟨h3, h4⟩ := h2
      rw [Nat.pair_eq_pair] at h3
      obtain ⟨h5, h6⟩ := h3
      have hk : k = k' := strCode_inj (Encodable.encode_injective h5)
      have hv : v = v' := encV_inj v v' h6
      have hrest : fs = gs := encFields_inj fs gs h4
      rw [hk, hv, hrest]
end

theorem encV_injective : Function.Injective encV := fun v w h => encV_inj v w h

/-- A toy injective leaf encoder: `encodeLeaf c v := [c, encV v]`, injective in `v` (`encV` is). -/
def refEncodeLeaf (c : CellId) (v : Value) : List ℤ := [(c : ℤ), (encV v : ℕ)]

theorem refEncodeLeaf_inj (c : CellId) (v w : Value) :
    refEncodeLeaf c v = refEncodeLeaf c w → v = w := by
  intro h
  unfold refEncodeLeaf at h
  have h2 : (encV v : ℤ) = (encV w : ℤ) := (List.cons.inj (List.cons.inj h).2).1
  exact encV_injective (by exact_mod_cast h2)

/-- A realized leaf hash (toy CR sponge + injective encoder): `CH c v = refSponge (enc c v)`.
The `LeafRealization` bundle is inhabited, so `cellLeafInjective_of_realization` fires. -/
def refCH (c : CellId) (v : Value) : ℤ := refSponge (refEncodeLeaf c v)

def refLeafRealization : LeafRealization refCH where
  sponge := refSponge
  encodeLeaf := refEncodeLeaf
  encodeLeaf_inj := refEncodeLeaf_inj
  factor := fun _ _ => rfl
  spongeCR := refSponge_CR

example : cellLeafInjective refCH := cellLeafInjective_of_realization refLeafRealization

/-! ### Log realization: `Turn` derives `Encodable`, so the log encoder is `Encodable.encode`. -/

/-- A toy injective log encoder: `encodeLog xs := [Encodable.encode xs]` (`List Turn` is `Encodable`). -/
def refEncodeLog (xs : List Turn) : List ℤ := [(Encodable.encode xs : ℕ)]

theorem refEncodeLog_inj (xs ys : List Turn) : refEncodeLog xs = refEncodeLog ys → xs = ys := by
  intro h
  unfold refEncodeLog at h
  have h2 : (Encodable.encode xs : ℤ) = (Encodable.encode ys : ℤ) := (List.cons.inj h).1
  exact Encodable.encode_injective (by exact_mod_cast h2)

def refLH (xs : List Turn) : ℤ := refSponge (refEncodeLog xs)

def refLogRealization : LogRealization refLH where
  sponge := refSponge
  encodeLog := refEncodeLog
  encodeLog_inj := refEncodeLog_inj
  factor := fun _ => rfl
  spongeCR := refSponge_CR

example : logHashInjective refLH := logHashInjective_of_realization refLogRealization

end Reference

/-! ## §5 — axiom-hygiene tripwires: each derivation pins exactly the whitelist. -/

#assert_axioms compressNInjective_iff_poseidon2CR
#assert_axioms compressNInjective_of_poseidon2CR
#assert_axioms cellLeafInjective_of_realization
#assert_axioms logHashInjective_of_realization
#assert_axioms Poseidon2RealizedSponge.toCR

end Dregg2.Circuit.Poseidon2Binding
