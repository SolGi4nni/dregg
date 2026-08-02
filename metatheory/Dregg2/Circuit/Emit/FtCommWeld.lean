import Dregg2.Circuit.Emit.MinaWrapGroupGate
import Dregg2.Circuit.Emit.PicklesFinalize
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaBasePrime
import Dregg2.Circuit.Emit.PastaScalarPrime
/-!
# Dregg2.Circuit.Emit.FtCommWeld — the THREE `ftComm`s, named, and welded where a weld exists.

## The wound

Measured 2026-08-02. This tree contains **three different objects** whose names all say `ftComm`,
carrying **eight theorems between them**, and until this file **nothing related any two of them**.
A reader who saw `ftComm_reproduces_kimchi` next to `ftComm_kat` next to
`ftComm_forgery_moves_it` would read seven theorems about `KimchiVerify.ftComm`. There was one,
and it was at `ℚ`.

This is the `a-display-name-is-not-a-key` class: a display name is not a key, and a shared prefix
is not a relationship.

### Object 1 — `Dregg2.Circuit.Emit.KimchiVerify.ftComm` (`KimchiVerify.lean:390`)

    ftComm {G} [AddCommGroup G] [Module F G] (n : Nat) (zeta : F) (fComm tComm : G) : G
      := fComm - (zeta ^ n - 1) • tComm

Maller's ft-commitment, module-generic, the SHIPPED C7 definition (`verifier.rs:958-965`).
**Its entire theorem-level evidence was `ftComm_kat` (`KimchiVerify.lean:1376`): one instance at
`G = F = ℚ`, `55 = 100 − 15·3`.** §5 below gives it evidence at the two DEPLOYED fields, including
one fact — the on-domain degeneracy — that a `ℚ` KAT cannot express at all.

### Object 2 — `Dregg2.Circuit.Emit.PicklesFinalize.picklesFtComm` (`PicklesFinalize.lean:750`)

    picklesFtComm [CommRing R] (zetaToSrsLength zetaToDomainSize fComm : R) (tChunks : List R) : R
      := let t := picklesChunkedTComm zetaToSrsLength tChunks;  fComm + t - zetaToDomainSize * t

Pickles' IN-CIRCUIT assembly (`wrap.rs:1372-1396`, `step.rs:1093-1106`), a DIFFERENT expression:
it reads an EXPOSED `zeta_to_domain_size` slot and adds `+T` back, where object 1 recomputes
`ζⁿ − 1`. The five `ftComm_*` theorems at `PicklesFinalize.lean:754-808` are about THIS, not about
object 1, and they are exactly the statements of the forgery split for that exposed slot.
**§2 welds it to object 1**: at the honest `zeta_to_domain_size` the two expressions are equal, for
every `[Field F]`. That is what makes the shared `ftComm_` prefix earned instead of coincidental.

### Object 3 — `Dregg2.Circuit.Emit.MinaWrapGroupGate.ftCommOf` / `.ftComm`
(`MinaWrapGroupGate.lean:100` / `:176`)

    ftCommOf (zSrs zDomM1 : Nat) (fTerms : List (Nat × Pt)) (tChunks : List Pt) : Pt

Concrete PROJECTIVE PALLAS POINTS (`Pt = Nat × Nat × Nat`), on Mina devnet block 539508, over K4a's
RCB complete add and K4b's 255-bit ladder. `ftComm_reproduces_kimchi` / `ftComm_is_a_finite_point`
(`:216`, `:220`) are about this. It is object 1's SHAPE — `chunk(f) − (ζⁿ−1)·chunk(t)` — but it is
not object 1, and §6 says precisely what is missing.

## What this file establishes

* **§2 — WELD A, generic.** `picklesFtComm` at the honest slot **IS** `KimchiVerify.ftComm`, over
  any `[Field F]`. Objects 1 and 2 are one map wherever the exposed slot is honest.
* **§3 — WELD B, generic.** kimchi's `chunk_commitment` Horner-over-reversed fold and Pickles'
  `reduce`-shaped fold are the SAME polynomial in the chunks. The two implementations reach the
  chunked `t_comm` by visibly different recursions and nothing said they agreed.
* **§4 — WELD C, an INSTANCE differential on block 539508.** Object 2's assembly, spelled on real
  Pallas points, reproduces the `ft_comm` that **o1-labs' own `SRS::verify` accepts** against this
  block's opening proof. `PicklesFinalize.lean:748` says of `picklesFtComm` that "it has never been
  evaluated on points"; `MinaWrapGroupGate.lean:24` repeats it. It has now.
  ⚑ And the input that makes it work is DERIVED, not chosen: `zeta_to_domain_size` is
  `ZETA_DOM_M1 + 1`, and `block_zeta_powers_are_consistent` checks that squaring it in the Pallas
  SCALAR field gives `ZETA_SRS` — i.e. `(ζ^2¹⁴)² = ζ^2¹⁵`, two independently extracted block
  constants agreeing. Nothing in the tree checked that before.
  ⚠ Note the sharpest consequence: `ZETA_DOM_M1 + 1` is a **tamper** in object 3's slot
  (`MinaWrapGroupGate.tamper_zeta_to_domain_size`) and the **honest** value in object 2's. Same
  number, two slots, opposite meanings — which is exactly the `+T − zTDS·T` vs `−(ζⁿ−1)·T`
  difference, and why welding them was worth doing rather than assuming.
* **§5 — object 1 at the DEPLOYED fields**, replacing "one KAT at `ℚ`".
* **§6 — what is NOT welded**, named exactly rather than left to a shared prefix.

Axiom-clean: `decide` / `simp` / `ring` only; no `sorry`, no `native_decide`.
-/

namespace Dregg2.Circuit.Emit.FtCommWeld

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projEqM isInfM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate
  (Pt padd pneg smul chunkedComm fComm chunkedT ftCommOf
   ZETA_SRS ZETA_DOM_M1 TCHUNKS CHUNKED_T_GOLD F_COMM_GOLD FT_COMM_GOLD)
open Dregg2.Circuit.Emit.PicklesFinalize (picklesChunkedTComm picklesFtComm zetaToDomainSizeR)

set_option autoImplicit false
set_option maxRecDepth 4000000

/-! ## §2 — WELD A: objects 1 and 2 are one map at the honest slot. -/

/-- **`picklesFtComm_is_kimchi_ftComm`** — Pickles' in-circuit `ft_comm`, fed its own
`derive_plonk` value for the exposed `zeta_to_domain_size` slot, IS `KimchiVerify.ftComm` — the
shipped module-generic Maller form — applied to the chunk-folded `t_comm`.

This is the weld the `ftComm_*` prefix on `PicklesFinalize.lean:754-808` was asserting by name and
nothing was proving. With it, those five theorems ARE about object 1 wherever the slot is honest;
without it they were about a same-named stranger.

Stated over `[Field F]` because object 1 is (`KimchiVerify`'s `variable {F} [Field F]`), and it is
INSTANTIABLE at both Pasta fields — see §5. -/
theorem picklesFtComm_is_kimchi_ftComm {F : Type} [Field F]
    (n : Nat) (zeta zTSL fCommV : F) (tChunks : List F) :
    picklesFtComm zTSL (zetaToDomainSizeR n zeta) fCommV tChunks
      = KimchiVerify.ftComm (F := F) (G := F) n zeta fCommV
          (picklesChunkedTComm zTSL tChunks) := by
  simp only [picklesFtComm, zetaToDomainSizeR, KimchiVerify.ftComm, smul_eq_mul]
  ring

/-- **`picklesFtComm_forged_slot_is_kimchi_ftComm_displaced`** — and a FORGED slot does not fall
outside object 1's language: it is object 1 displaced by exactly `(forged − ζⁿ)·T`. So
`PicklesFinalize.ftComm_forgery_moves_it` is a statement about `KimchiVerify.ftComm` too, and the
displacement is named rather than merely "different". -/
theorem picklesFtComm_forged_slot_is_kimchi_ftComm_displaced {F : Type} [Field F]
    (n : Nat) (zeta zTSL zTDS fCommV : F) (tChunks : List F) :
    picklesFtComm zTSL zTDS fCommV tChunks
      = KimchiVerify.ftComm (F := F) (G := F) n zeta fCommV
            (picklesChunkedTComm zTSL tChunks)
        - (zTDS - zeta ^ n) * picklesChunkedTComm zTSL tChunks := by
  simp only [picklesFtComm, KimchiVerify.ftComm, smul_eq_mul]
  ring

/-! ## §3 — WELD B: the two chunk folds are one polynomial.

`MinaWrapGroupGate.chunkedComm` transcribes `PolyComm::chunk_commitment`
(`poly-commitment/src/commitment.rs:55`): Horner over the chunks in REVERSE order,
`res := res·z + chunk`, starting from the identity. `PicklesFinalize.picklesChunkedTComm`
transcribes `wrap.rs:1379-1387`: a `reduce` over the reversed chunk list, which is a *forward*
recursion with a singleton base case and no identity element at all.

Two different recursions, transcribed from two different sources, feeding the same `ft_comm`. That
they compute the same polynomial was assumed by every statement that mentioned both. -/

/-- **`kimchi_horner_fold_is_pickles_reduce_fold`** — `chunk_commitment`'s Horner-over-reversed
fold and Pickles' `reduce` fold agree at every chunk list, over any commutative ring.

⚑ The base cases are where they could have differed and do not: `reduce` on a SINGLETON never
applies its step (which is exactly what `PicklesFinalize.ftComm_srs_length_unused_at_one_chunk`
is about), while the Horner fold does apply it, to the identity. The statement is written on the
fold expression itself rather than through a fresh mirror definition, so it is about
`chunkedComm`'s own shape and not about a copy of it. -/
theorem kimchi_horner_fold_is_pickles_reduce_fold {R : Type} [CommRing R] (z : R) (cs : List R) :
    cs.reverse.foldl (fun acc c => z * acc + c) 0 = picklesChunkedTComm z cs := by
  induction cs with
  | nil => simp [picklesChunkedTComm]
  | cons c rest ih =>
    cases rest with
    | nil => simp [picklesChunkedTComm]
    | cons d drest =>
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
      rw [ih]
      simp only [picklesChunkedTComm]
      ring

/-! ## §4 — WELD C: object 2's assembly, on block 539508's real Pallas points.

The point-level spellings below mirror `picklesChunkedTComm` / `picklesFtComm` clause for clause,
with `+ ↦ padd`, `· ↦ smul`, `0 ↦ Oproj`, `− ↦ pneg`. They are the Pickles shape, not kimchi's:
`picklesFtCommPt` reads a `zeta_to_domain_size` and adds `+T` back; `ftCommOf` reads `ζⁿ − 1` and
does not. -/

/-- Pickles' `reduce` chunk fold, on Pallas points. -/
def picklesChunkedTCommPt (z : Nat) : List Pt → Pt
  | [] => Oproj
  | c :: rest => match rest with
    | [] => c
    | _ :: _ => padd c (smul z (picklesChunkedTCommPt z rest))

/-- Pickles' in-circuit `ft_comm`, on Pallas points: `f_comm + T − zeta_to_domain_size·T`. -/
def picklesFtCommPt (zSrs zDomSize : Nat) (fCommV : Pt) (tChunks : List Pt) : Pt :=
  let t := picklesChunkedTCommPt zSrs tChunks
  padd (padd fCommV t) (pneg (smul zDomSize t))

/-- The block's honest `zeta_to_domain_size` = `ζ^(2¹⁴)`. `MinaWrapGroupGate` carries only
`ζ^(2¹⁴) − 1`, because kimchi's Maller form is the only one it needed. -/
def ZETA_DOM_SIZE : Nat := ZETA_DOM_M1 + 1

/-- **`block_zeta_powers_are_consistent`** — `(ζ^2¹⁴)² = ζ^2¹⁵` in the Pallas SCALAR field: the
block's `ZETA_DOM_M1` and `ZETA_SRS` were extracted independently and this is the first thing that
checks they are powers of one ζ. It is also what makes §4's `zeta_to_domain_size` input DERIVED
rather than guessed. -/
theorem block_zeta_powers_are_consistent :
    ZETA_DOM_SIZE * ZETA_DOM_SIZE % qN = ZETA_SRS := by decide

/-- **`picklesFold_reproduces_kimchi_chunking_on_539508`** — WELD B's ring statement, discharged
on the group: Pickles' `reduce` fold over the block's **seven real `t_comm` Pallas points**
produces `PolyComm::chunk_commitment`'s own output. Six 255-bit ladders and six complete adds. -/
theorem picklesFold_reproduces_kimchi_chunking_on_539508 :
    projEqM pN (picklesChunkedTCommPt ZETA_SRS TCHUNKS) CHUNKED_T_GOLD = true := by decide

/-- **`picklesFtComm_reproduces_o1labs_ft_comm_on_539508`** — ⚑ THE RUNG. Pickles' in-circuit
`ft_comm` — the `f_comm + T − zeta_to_domain_size·T` shape, with the exposed slot at its honest
value — reproduces the `ft_comm` that **o1-labs' own `SRS::verify` accepts** against block 539508's
opening proof.

`PicklesFinalize.lean:748` and `MinaWrapGroupGate.lean:24` both state that `picklesFtComm` "has
never been evaluated on points". This is that evaluation, and it is the group-side instance of
`PicklesFinalize.ftComm_honest_agrees`: the theorem says the two expressions agree at the honest
slot, and here they agree ON THE DEPLOYED DATA, against a value o1-labs' verifier signed off. -/
theorem picklesFtComm_reproduces_o1labs_ft_comm_on_539508 :
    projEqM pN (picklesFtCommPt ZETA_SRS ZETA_DOM_SIZE fComm TCHUNKS) FT_COMM_GOLD = true := by
  decide

/-- **`picklesFtComm_is_not_ftCommOf_at_the_same_slot_value`** — ⚠ the two assemblies are NOT
interchangeable, and this is the pole that says so. Feeding object 2's assembly the number object 3
takes (`ζⁿ − 1`, the Maller factor) instead of `ζⁿ` produces a DIFFERENT point. So the agreement
above is about the honest-slot weld and not about the two shapes being the same expression. -/
theorem picklesFtComm_is_not_ftCommOf_at_the_same_slot_value :
    projEqM pN (picklesFtCommPt ZETA_SRS ZETA_DOM_M1 fComm TCHUNKS) FT_COMM_GOLD = false := by
  decide

/-- **`picklesFtComm_is_a_finite_point_on_539508`** — and the agreement is not `projEqM`'s `Z = 0`
degeneracy. -/
theorem picklesFtComm_is_a_finite_point_on_539508 :
    isInfM pN (picklesFtCommPt ZETA_SRS ZETA_DOM_SIZE fComm TCHUNKS) = false := by decide

/-! ## §5 — object 1 at the DEPLOYED fields (it had one KAT, at `ℚ`).

`Fact (Nat.Prime pN)` (`PastaBasePrime.lean:122`, 2026-07-29) and `Fact (Nat.Prime qN)`
(`PastaScalarPrime.lean`, today) make `ZMod pN` and `ZMod qN` genuine `Field`s, so `ftComm` — a
`[Field F]`-typed definition — is instantiable at both for the first time. -/

/-- **`ftComm_ignores_tComm_on_the_domain`** — ⚑ the fact a `ℚ` KAT cannot state. Wherever
`ζⁿ = 1`, Maller's assembly returns `f_comm` **for every `t_comm`**: the quotient commitment drops
out of `ft_comm` entirely. Over `ℚ` the only such ζ are `±1`; over a finite field it is every point
of the evaluation domain, which is where a ζ chosen rather than squeezed would sit.

This is the commitment-side sibling of the `publicEval` on-domain collapse the cross-implementation
differential measures, and it is why ζ coming out of a sponge is load-bearing. -/
theorem ftComm_ignores_tComm_on_the_domain {F : Type} [Field F] {G : Type} [AddCommGroup G]
    [Module F G] (n : Nat) (zeta : F) (hz : zeta ^ n = 1) (fCommV tCommV : G) :
    KimchiVerify.ftComm n zeta fCommV tCommV = fCommV := by
  simp [KimchiVerify.ftComm, hz]

-- The `ftComm_kat` arithmetic (`55 = 100 − 15·3`), at the DEPLOYED base field rather than at `ℚ`.
#guard KimchiVerify.ftComm (F := ZMod pN) (G := ZMod pN) 4 2 100 3 == 55
-- …and at the DEPLOYED SCALAR field, which became typeable only with `Fact (Nat.Prime qN)`.
#guard KimchiVerify.ftComm (F := ZMod qN) (G := ZMod qN) 4 2 100 3 == 55
-- The on-domain collapse, at a NON-TRIVIAL 4th root of unity in each field (`5^((m−1)/4)`), where
-- `t_comm` is discarded: unreachable over `ℚ`, whose only roots of unity are `±1`.
#guard KimchiVerify.ftComm (F := ZMod pN) (G := ZMod pN) 4
  24760239192664116622385963963284001971067308018068707868888628426778644166363 100 3 == 100
#guard KimchiVerify.ftComm (F := ZMod qN) (G := ZMod qN) 4
  24682508875525884897641270952488416149830453149035712389703207095981135804695 100 3 == 100
-- …and off the domain the `t_comm` term is live at the same inputs, so the two `#guard`s above are
-- not both true for a trivial reason.
#guard KimchiVerify.ftComm (F := ZMod qN) (G := ZMod qN) 4
  24682508875525884897641270952488416149830453149035712389703207095981135804694 100 3 != 100

/-- **`the block's own Maller scalar, in the field it lives in`** — object 1's scale factor
`ζⁿ − 1`, evaluated in `ZMod qN` at the block's `zeta_to_domain_size`, is the block's
`ZETA_DOM_M1`. This is the only place object 1's SCALAR meets the real block. -/
theorem kimchi_ftComm_scale_factor_is_the_blocks :
    KimchiVerify.ftComm (F := ZMod qN) (G := ZMod qN) 1 (ZETA_DOM_SIZE : ZMod qN) 0 1
      = - (ZETA_DOM_M1 : ZMod qN) := by
  simp only [KimchiVerify.ftComm, ZETA_DOM_SIZE, smul_eq_mul, pow_one, mul_one, zero_sub]
  push_cast
  ring

/-! ## §6 — what is NOT welded, and the exact missing ingredient.

**Objects 1 and 3 are not welded, and cannot be with what this tree has.**
`KimchiVerify.ftComm` requires `[AddCommGroup G] [Module F G]`. Instantiating it at the Pallas
point group with `F = ZMod qN` needs a `Module (ZMod qN) G` structure, which for an additive group
means `q • x = 0` for every point — i.e. **the fact that the Pallas group has order `qN`**. That is
a genuine mathematical input (Hasse plus the exact order), not a missing `import`, and nothing in
this tree proves it. `PastaGroupLaw` supplies the `AddCommGroup`; the `Module` is the gap.

What stands instead is a CHAIN, and it is weaker than a direct weld in a way worth stating:

    object 1  --(§2, GENERIC over every `[Field F]`)-->  object 2
    object 2  --(§4, ONE INSTANCE: Mina devnet block 539508)-->  object 3

So "object 3 computes object 1's function" is supported *generically* down to the scalar shape and
*at one block* on the group. That is the same standing `MinaWrapGroupGate`/`MinaWrapOpeningGate`
already have (`PastaMsmAir.lean:9` calls them instance differentials), stated rather than implied.

**The `ftcomm` differential pair is not here.** `kimchi::verifier::to_batch` is private and neither
reference exposes a standalone `ft_comm`; composing `PolyComm::chunk_commitment` / `scale` / `sub`
in a harness is the route `wrap_group_export.rs` already takes, and it is a real option — but the
Lean side would have to canonicalise projective output to affine per case. Named as work, not as a
blocker.
-/

#assert_axioms picklesFtComm_is_kimchi_ftComm
#assert_axioms picklesFtComm_forged_slot_is_kimchi_ftComm_displaced
#assert_axioms kimchi_horner_fold_is_pickles_reduce_fold
#assert_axioms block_zeta_powers_are_consistent
#assert_axioms picklesFold_reproduces_kimchi_chunking_on_539508
#assert_axioms picklesFtComm_reproduces_o1labs_ft_comm_on_539508
#assert_axioms picklesFtComm_is_not_ftCommOf_at_the_same_slot_value
#assert_axioms picklesFtComm_is_a_finite_point_on_539508
#assert_axioms ftComm_ignores_tComm_on_the_domain
#assert_axioms kimchi_ftComm_scale_factor_is_the_blocks

#assert_namespace_axioms Dregg2.Circuit.Emit.FtCommWeld

end Dregg2.Circuit.Emit.FtCommWeld
