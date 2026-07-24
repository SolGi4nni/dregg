/-
# `Dregg2.Circuit.ChainDigestRomBinding` — the §8 chain-digest binding, DISCHARGED on the keyed,
query-counted random-oracle floor (the PROVED floor).

## What this replaces (the D-class drop)

`Circuit.chain_digest_binds` / `chain_digest_binds_indicator` / `false_chain_not_bound` /
`chain_digest_binds_chainOk` and `AirSoundness.committed_trace_pinned` carried `hcr : HashCR cr` —
pure INJECTIVITY of the digest hash, PROVED FALSE for every compressing digest by
`HashFloorHonesty.hashCR_false_of_compressing` (the deployed `CryptoKernel.hash` maps unbounded
framed chains into a fixed-width digest, so it IS compressing). All five are DELETED (same commit as
this file). Their deterministic content survives as the `¬ HashCR`-conclusion extractor witnesses
`Circuit.distinct_traces_break_hashcr` / `digest_collision_is_hash_collision`, never re-exported as
floors; THIS module is the discharged successor.

This is a separate leaf module (not a section of `Circuit.lean`) because the keyed-ROM kit's closure
(`Crypto.RomCarrierSites` → `Circuit.HashFloorHonesty` → `Poseidon2Binding` → `StateCommit` →
`Transfer`) imports `Dregg2.Circuit`, so the successor cannot live there without an import cycle.

## ⚑ The modelling step, stated (not smuggled)

Exactly `Crypto.RomCarrierSites`' header: the fixed deployed `CryptoKernel.hash` is idealised as a
SAMPLED keyed random oracle `H : Unit × Trace → Fin (2 ^ l)` at an ASYMPTOTIC digest width — a
deliberate labelled idealisation, NOT a derivation about the fixed hash. The trace is absorbed
VERBATIM as the oracle message (the injective length-framing `frame` of the fixed-hash model is
subsumed: the ROM message IS the trace). The message domain must be FINITE: a deployed unbounded
`List Turn` trace enters through the honest truncation `RomCarrierSites.BVec`/`bvecOfList`, lossless
at any pinned bound (`bvecOfList_inj`). What the move buys: the floor under the binding is
`KeyedRomFloor.keyedRom_hard` — the birthday bound, a THEOREM. What it does not buy: any statement
about the fixed public hash itself.

## Non-fake

The `0`-query hardcoded opener — the exact shape that refutes the injective floor with probability
`1` against the fixed hash — is IN the class, wins at the constant oracle (POSITIVE advantage), and
is DEFANGED (negligible) at the sampled oracle (`chainDigestRom_const_defanged`); a non-negligible
equivocator is OUTSIDE the class (`chainDigestRom_forger_excluded`). `#assert_all_clean` ⊆
{propext, Classical.choice, Quot.sound}; no `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Circuit
import Dregg2.Crypto.HermineRomBinding
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Circuit.ChainDigestRomBinding

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv)
open Dregg2.Crypto.RomCarrierSites (romOpenGame RomOpenEff rom_open_binds romOpenAdv constOpenComp
  constOpen_in_eff constOpen_gameAdv_pos constOpen_binds romOpen_forger_excluded)
open Dregg2.Crypto.HermineRomBinding (crRomFamily crRomCarrier crRomFamily_card_R)

set_option autoImplicit false

variable (Trace : Type) [Fintype Trace] [DecidableEq Trace] [Nonempty Trace]

/-- **THE CHAIN-DIGEST OPENING GAME AT THE SAMPLED ORACLE.** The adversary publishes a digest and
two traces; it WINS iff the traces are DISTINCT and BOTH open the published digest —
`Circuit.verifyDigest`'s break, with the published digest IN the win relation, checked against the
SAMPLED oracle. -/
abbrev chainDigestRomGame : Game :=
  romOpenGame (crRomFamily Unit Trace) (crRomCarrier Unit Trace)

/-- **THE DEPLOYED BREAK IS A WIN.** Two DISTINCT traces both opening one published digest at the
sampled oracle are a win — `Circuit.distinct_traces_break_hashcr`, restated at the sampled oracle. -/
theorem chainDigestRom_equivocation_is_break (l : ℕ) (H : (chainDigestRomGame Trace).Inst l)
    (dig : Fin (2 ^ l)) {tr tr' : Trace} (hne : tr ≠ tr')
    (h : H ((), tr) = dig) (h' : H ((), tr') = dig) :
    (chainDigestRomGame Trace).wins l H (dig, ((), ()), tr, tr') :=
  ⟨hne, h, h'⟩

/-- **AN INDICATOR-EQUIVOCATION IS A WIN** — the successor of the deleted
`chain_digest_binds_indicator` / `chain_digest_binds_chainOk`: two openings of one digest whose
traces DISAGREE on any indicator `ind` (in particular `Circuit.traceChainOk`, via
`Circuit.chainOk_ne_imp_trace_ne`) are a win of the opening game. -/
theorem chainDigestRom_indicator_break {β : Type*} (ind : Trace → β)
    (l : ℕ) (H : (chainDigestRomGame Trace).Inst l) (dig : Fin (2 ^ l)) {tr tr' : Trace}
    (hind : ind tr ≠ ind tr') (h : H ((), tr) = dig) (h' : H ((), tr') = dig) :
    (chainDigestRomGame Trace).wins l H (dig, ((), ()), tr, tr') :=
  ⟨fun hc => hind (congrArg ind hc), h, h'⟩

/-- **⚑⚑ THE §8 BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`chain_digest_binds` / `false_chain_not_bound` / `chain_digest_binds_chainOk` and of
`AirSoundness.committed_trace_pinned` (which instantiated `chain_digest_binds` at the AIR trace
type): every query-bounded adversary that opens one published chain digest with two distinct traces
has NEGLIGIBLE advantage, in the keyed ROM model of the header. The hypotheses are a polynomial
query budget and the forger's membership in the query class — nothing refutable. -/
theorem chain_digest_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (chainDigestRomGame Trace))
    (hA : RomOpenEff (crRomFamily Unit Trace) (crRomCarrier Unit Trace) Q A) :
    Negl (gameAdv (chainDigestRomGame Trace) A) :=
  rom_open_binds _ _ Q hQ (crRomFamily_card_R Unit Trace) A hA

/-- **(TOOTH — a non-negligible digest-equivocator is OUTSIDE the class.)** The refutation strategy
that killed the injective floor cannot produce a member of this one. -/
theorem chainDigestRom_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (chainDigestRomGame Trace))
    (hnn : ¬ Negl (gameAdv (chainDigestRomGame Trace) A)) :
    ¬ RomOpenEff (crRomFamily Unit Trace) (crRomCarrier Unit Trace) Q A :=
  romOpen_forger_excluded _ _ Q hQ (crRomFamily_card_R Unit Trace) A hnn

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage, and the admitted refuter-shape is
DEFANGED.)** The `0`-query hardcoded opener — the exact shape that refutes the injective floor with
probability `1` against the fixed hash — is in the class, wins at the constant oracle (positive
advantage), and its advantage against the SAMPLED oracle is NEGLIGIBLE. The counterexample dies by
keying, not by exclusion. -/
theorem chainDigestRom_const_defanged {tr tr' : Trace} (hne : tr ≠ tr') (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    (∀ l, 0 < gameAdv (chainDigestRomGame Trace)
        (romOpenAdv _ _ (constOpenComp (crRomFamily Unit Trace) (crRomCarrier Unit Trace)
          (fun l => ⟨0, by positivity⟩) (fun _ => ((), ())) (fun _ => tr) (fun _ => tr'))) l)
    ∧ Negl (gameAdv (chainDigestRomGame Trace)
        (romOpenAdv _ _ (constOpenComp (crRomFamily Unit Trace) (crRomCarrier Unit Trace)
          (fun l => ⟨0, by positivity⟩) (fun _ => ((), ())) (fun _ => tr) (fun _ => tr')))) :=
  ⟨fun l => constOpen_gameAdv_pos _ _ _ _ _ _ l hne,
    constOpen_binds _ _ _ _ _ _ Q hQ (crRomFamily_card_R Unit Trace)⟩

/-- **(CANARY — the bound does NOT follow from the floor applied at ANOTHER adversary.)** -/
example (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (chainDigestRomGame (Fin 5)))
    (B : Adversary (Dregg2.Crypto.KeyedRomFloor.keyedRomGame (crRomFamily Unit (Fin 5))))
    (hB : Dregg2.Crypto.KeyedRomFloor.KeyedRomEff (crRomFamily Unit (Fin 5)) Q B) : True := by
  fail_if_success
    (have : Negl (gameAdv (chainDigestRomGame (Fin 5)) A) :=
      Dregg2.Crypto.KeyedRomFloor.keyedRom_hard (crRomFamily Unit (Fin 5)) Q hQ
        (crRomFamily_card_R Unit (Fin 5)) B hB)
  trivial

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  chainDigestRom_equivocation_is_break,
  chainDigestRom_indicator_break,
  chain_digest_binds_rom,
  chainDigestRom_forger_excluded,
  chainDigestRom_const_defanged
]

end Dregg2.Circuit.ChainDigestRomBinding
