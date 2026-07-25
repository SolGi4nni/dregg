/-
# `Dregg2.Crypto.Keccak.Fips202Claims` — the FIPS-202 stack's TEETH.

## Why this file exists

The six `Dregg2.Crypto.Keccak.Fips202*` modules (`Fips202Spec`, `Fips202Round`, `Fips202Sponge`,
`Fips202SpongeRefine`, `Fips202Refine`, `Fips202Lfsr`) carry the SHAKE→FIPS-202 floor closure. They
were rooted into the default `lake build` by `ebb0b9f9ae` — and that commit measured, correctly, that
rooting buys them COMPILATION coverage ONLY: between them the six contain ZERO `#assert_axioms`,
`#assert_all_clean` and ZERO `#guard`. Their axiom hygiene was asserted by nothing, in any file, in
any CI target. This file is where it is asserted.

Compilation coverage would not be enough here, for a reason specific to this stack: its headline
obligation `Fips202Refine.SpongeRefinesObligation` USED TO BE `True` — honestly labelled as such at
the time, while no FIPS 202 sponge specification existed anywhere in the tree. A `True` placeholder
compiles green, is kernel-clean, and satisfies every axiom pin that could ever be written about it.
An axiom net alone therefore cannot tell a discharged obligation from a restored placebo. So the
stack gets BOTH kinds of tooth:

  §1  AXIOM pins (`#assert_all_clean`) over the stack's kernel-clean keystones. Catches a keystone
      that grows a `native_decide` (`Lean.ofReduceBool` + `Lean.trustCompiler`) or inherits a
      `sorryAx` from anywhere in its proof closure.
  §2  STATEMENT pins (`example : ⟨the literal proposition⟩ := ⟨the theorem⟩`, plus one `rfl` on the
      obligation's own definition). Catches exactly what §1 cannot see: an obligation hollowed back
      out to `True`, or a `∀` quietly narrowed — a lost quantifier, a new hypothesis, a rate or
      output length specialized. The kernel checks the ascription, so statement drift is a build
      ERROR rather than a silently weaker claim that still passes every axiom pin.
  §3  ROUTING pins. The stack has exactly ONE declaration resting on a non-kernel axiom:
      `Fips202SpongeRefine.spec_SHAKE256_empty_cavp`, an evaluation anchor that transports the
      CAVP-cited `Keccak.shake256_empty_kat` (`native_decide`) across the refinement. `ebb0b9f9ae`
      asserts that anchor "is NOT load-bearing for a refinement theorem". §3 makes that MACHINE-
      CHECKED — `#assert_not_depends_on` on each refinement apex — carrying the `#assert_depends_on`
      positive control those rejectors require so they cannot pass blind.

Why the teeth live HERE and not in the six modules: `Fips202Spec` is deliberately import-free and the
others import only each other, so the `#assert_axioms` family (which lives in `Dregg2.Tactics`) is
not in scope in any of them. One importing module keeps that shape intact and keeps every pin in one
auditable place — the same arrangement as `Dregg2/Circuit/ListCommitCutoverCheck.lean`.

WHAT NO PIN IN THIS FILE COVERS, stated plainly: every theorem below refines the executable Lean
`Keccak.shake256` / `Keccak.keccakF` against a LEAN TRANSCRIPTION of FIPS 202
(`Fips202Spec` / `Fips202Sponge`). Fidelity of that transcription to the published NIST document is
human-checked, not proven, and nothing here can change that.
-/
import Dregg2.Tactics
import Dregg2.Crypto.Keccak.Fips202Spec
import Dregg2.Crypto.Keccak.Fips202Round
import Dregg2.Crypto.Keccak.Fips202Sponge
import Dregg2.Crypto.Keccak.Fips202SpongeRefine
import Dregg2.Crypto.Keccak.Fips202Refine
import Dregg2.Crypto.Keccak.Fips202Lfsr

namespace Dregg2.Crypto.Keccak.Fips202Claims

/-! ## §1 — AXIOM PINS

Every name here must rest on exactly `{propext, Classical.choice, Quot.sound}`. The first one that
does not throws, naming its offending axiom. A typo is an `unknownConstant` error, so the list cannot
silently drop a pin. -/

#assert_all_clean [
  -- the LFSR half: FIPS 202 §3.2.5 Algorithm 5+6 round constants, kernel-`decide`d (this is the
  -- `native_decide` that `2c3f531301` named as the Keccak chain's only non-standard axiom and
  -- `Fips202Lfsr` closed — the pin is what keeps it closed).
  Dregg2.Crypto.Keccak.Fips202Lfsr.rcBit_eq_rcBitRec,
  Dregg2.Crypto.Keccak.Fips202Lfsr.rcLaneOf_eq_rcLaneOfRec,
  Dregg2.Crypto.Keccak.Fips202Lfsr.rc_lanes_all,
  Dregg2.Crypto.Keccak.Fips202Lfsr.round_constants_are_lfsr,
  Dregg2.Crypto.Keccak.Fips202Refine.rc_lanes_eq_exec,
  -- the permutation half: the executable round, then Keccak-f[1600].
  Dregg2.Crypto.Keccak.Fips202Round.keccakRound_refines_spec,
  Dregg2.Crypto.Keccak.Fips202Round.keccakRound_refines_spec_RC,
  Dregg2.Crypto.Keccak.Fips202Round.keccakF_refines_spec,
  -- the sponge half: pad10*1, absorb, squeeze, then the two SHAKEs and the obligation's discharge.
  Dregg2.Crypto.Keccak.Fips202SpongeRefine.pad_refines_spec,
  Dregg2.Crypto.Keccak.Fips202SpongeRefine.absorb_refines_spec,
  Dregg2.Crypto.Keccak.Fips202SpongeRefine.squeeze_refines_spec,
  Dregg2.Crypto.Keccak.Fips202SpongeRefine.shake256_refines_SHAKE256,
  Dregg2.Crypto.Keccak.Fips202SpongeRefine.shake128_refines_SHAKE128,
  Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines
]

/-! ## §2 — STATEMENT PINS

The teeth an axiom pin cannot grow. Each `example` ascribes the proposition the stack ADVERTISES and
closes it with the stack's own theorem, so the kernel re-checks the claim's SHAPE on every build. -/

/-- The obligation's DEFINITION is the real conjunction of two `∀`s — not `True`, which is what it
was before a FIPS 202 sponge specification existed. `rfl` here fails the moment the definition is
weakened, at the definition site, with the definition named. -/
example :
    Fips202Refine.SpongeRefinesObligation =
      ((∀ (input : List UInt8) (outLen : Nat),
          Fips202.bitsOfBytes (Dregg2.Crypto.Keccak.shake256 input outLen)
            = Fips202.SHAKE256 (Fips202.bitsOfBytes input) (8 * outLen))
        ∧ (∀ (input : List UInt8) (outLen : Nat),
          Fips202.bitsOfBytes (Dregg2.Crypto.Keccak.shake128 input outLen)
            = Fips202.SHAKE128 (Fips202.bitsOfBytes input) (8 * outLen))) := rfl

/-- …and it is DISCHARGED at that strength. Independent of the `rfl` above: this one would red even
if the obligation `def` were deleted and inlined, because it pins the TYPE of the discharging
theorem. Universally quantified over EVERY input byte string and EVERY output length; no hypothesis,
no fixed rate, no fixed length. -/
example :
    (∀ (input : List UInt8) (outLen : Nat),
        Fips202.bitsOfBytes (Dregg2.Crypto.Keccak.shake256 input outLen)
          = Fips202.SHAKE256 (Fips202.bitsOfBytes input) (8 * outLen))
    ∧ (∀ (input : List UInt8) (outLen : Nat),
        Fips202.bitsOfBytes (Dregg2.Crypto.Keccak.shake128 input outLen)
          = Fips202.SHAKE128 (Fips202.bitsOfBytes input) (8 * outLen)) :=
  Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines

/-- Keccak-f[1600]: the executable 24-round permutation equals the spec permutation for EVERY
25-lane state, under the lane/bit abstraction. `a.size = 25` is the only side condition, and pinning
the statement is what keeps it the only one. -/
example :
    ∀ (a : Array UInt64), a.size = 25 →
      Fips202Refine.toSpec (Dregg2.Crypto.Keccak.keccakF a)
        = Fips202.keccakF (Fips202Refine.toSpec a) :=
  fun a ha => Dregg2.Crypto.Keccak.Fips202Round.keccakF_refines_spec a ha

/-- The round constants, in `∀` form: for every round Keccak-f actually performs and every bit
position, the executable's precomputed `RC[ir]` word agrees with the Algorithm-5 LFSR. This is the
`∀` the chain's last `native_decide` was standing in for; the pin is what stops it reverting to a
finite `= true` check over the 24 constants. -/
example :
    ∀ (ir : Nat), ir < 24 → ∀ (z : Fin 64),
      Fips202.rcLaneOf ir z = (Dregg2.Crypto.Keccak.RC[ir]!).toBitVec.getLsbD z.val :=
  fun ir hir z => Dregg2.Crypto.Keccak.Fips202Lfsr.round_constants_are_lfsr ir hir z

/-! ## §3 — ROUTING PINS: the CAVP anchor is not load-bearing

`Fips202SpongeRefine.spec_SHAKE256_empty_cavp` is the stack's only non-kernel declaration: it
transports `Keccak.shake256_empty_kat` (NIST CAVP `SHAKE256ShortMsg.rsp`, `Len = 0`, closed by
`native_decide`) across the refinement to witness that the SPEC sponge is not vacuous. It is an
anchor, not a `∀`, and the claim made about it is that no refinement theorem rides on it. That claim
is checked below rather than asserted — the walk is over the PROOF TERM closure, so a route restored
through the KAT by a later edit is a build error naming the path.

The `#assert_depends_on` is MANDATORY, not decoration: a rejector cannot detect its own blindness, so
if the closure walk ever stops seeing proof terms the three rejectors above would pass vacuously
while this control fails loudly. Do not delete it to get green. -/

#assert_not_depends_on Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines
  [Dregg2.Crypto.Keccak.shake256_empty_kat]
#assert_not_depends_on Dregg2.Crypto.Keccak.Fips202Round.keccakF_refines_spec
  [Dregg2.Crypto.Keccak.shake256_empty_kat]
#assert_not_depends_on Dregg2.Crypto.Keccak.Fips202Lfsr.round_constants_are_lfsr
  [Dregg2.Crypto.Keccak.shake256_empty_kat]

#assert_depends_on Dregg2.Crypto.Keccak.Fips202SpongeRefine.spec_SHAKE256_empty_cavp
  [Dregg2.Crypto.Keccak.shake256_empty_kat]

end Dregg2.Crypto.Keccak.Fips202Claims
