/-
# `Dregg2.Crypto.UcSignature` — a UNIVERSAL-COMPOSABILITY beachhead for the HYBRID signature.

`HybridCombiner.lean` proved the hybrid `ed25519 ∧ ML-DSA` signature is `EufCma`-unforgeable if EITHER
component is, grounded all the way down to `SchnorrDLHard ∨ MSISHard`. That is a GAME-BASED result. This
module opens the OTHER leg the composition story needs: the **universal-composability** statement that the
hybrid signature UC-REALIZES an ideal signature functionality `F_SIG`, so a protocol proven secure against
`F_SIG` stays secure when `F_SIG` is replaced by the real hybrid signature — *under concurrent execution*,
via the UC composition theorem.

The beachhead is minimal but REAL, and its load-bearing content is one equivalence:

  > **the hybrid signature UC-realizes `F_SIG` IFF it is `EufCma`** — and the ONLY distinguishing event
  > between the real protocol and the ideal (`F_SIG` + simulator `S`) is a FORGERY on an honest key,
  > which `S` cannot produce. So the environment's distinguishing advantage is exactly the `EufCma`
  > advantage, bounded (via `HybridCombiner.hybrid_secure_if_either_floor`) by `SchnorrDLHard ∨ MSISHard`.

## What is modelled (§-by-§)

  **§1 — the ideal functionality `F_SIG`, the real protocol, the environment.** `F_SIG` is the standard
  Canetti signature functionality collapsed to its observable content: it RECORDS the messages honest
  parties signed (`Recorded : Msg → Prop`) and VERIFIES a message iff it was recorded — *unforgeability
  by construction*, there is no forgery in the ideal world. We model `F_SIG` as a genuine `SigScheme`
  (`idealSig`) whose `verify` consults `Recorded` and ignores the signature, so the ideal is directly
  comparable to the real scheme. The REAL protocol runs the hybrid `SigScheme`. The environment `Z` is a
  distinguisher that submits a `(message, signature)` pair and reads the accept bit.

  **§2 — the realize relation and the distinguishing game.** `UcRealizes S pk Recorded` says the real
  accept bit never exceeds the ideal one: `∀ m σ, verify pk m σ → Recorded m`. `Distinguishes` is the
  environment's win: it submits `(m, σ)` that the REAL scheme accepts but `F_SIG` rejects. The two headline
  equivalences: `distinguishes_iff_forgery` (the distinguishing event IS a forgery on the honest key) and
  `ucRealizes_iff_eufCma` (realizing `F_SIG` IS the `EufCma` game — no slack, no laundering).

  **§3 — THE REDUCTION TO THE FLOOR (`hybrid_sig_uc_realizes`).** Composing the equivalence with
  `HybridCombiner.hybrid_secure_if_either_floor`: the hybrid signature UC-realizes `F_SIG` under
  `SchnorrDLHard ∨ MSISHard`, via the SAME forking reductions, introducing NO new hardness carrier. This is
  the composition payoff: the hybrid sig can be plugged into any protocol proven secure with `F_SIG`.

  **§4 — non-vacuity, both poles.** A scheme WITH `EufCma` (`secureToy`) realizes `F_SIG`; a scheme WITHOUT
  it (`brokenToy`, verifies everything) does NOT — a forgery is a distinguishing environment. The hybrid of
  a secure and a broken component realizes `F_SIG` from the single good half. So the `EufCma` hypothesis is
  LOAD-BEARING: realization is exactly what unforgeability buys and a forgeable scheme loses.

  **§5 — the simulator, made explicit.** For this functionality the simulator `S` is degenerate and named:
  it generates its own keypair and HONESTLY SIGNS each recorded message (`Correct` gives completeness), so
  the ideal-world signatures verify exactly as real ones; the only thing it cannot fake is a signature on a
  NON-recorded message, which is a forgery. `real_ideal_agree` proves the real and ideal accept bits
  coincide on every message under `EufCma` + completeness — the single-shot indistinguishability.

## HONEST BOUNDARY (named, not hidden — §6 `SigUCResidual`)

This is a MINIMAL UC beachhead, not the full framework. What it captures: the ideal functionality, a real
simulator, the realize relation, and the forgery-is-the-only-gap argument, for a DETERMINISTIC single-shot
signature-verification functionality — reduced to the floor with no new carrier. What it does NOT capture,
and is the continued frontier (carried as named `Prop` residues, never `axiom`s, mirroring
`LightClientUC.DynamicUCResidual` / `UCBridge.FComDischarge`):

  * `≈` as NEGLIGIBLE statistical/computational distance of probability ENSEMBLES indexed by the security
    parameter (here the distinguishing event is a `Prop`, the advantage collapsed to zero-or-one);
  * the simulator's PPT efficiency;
  * the full Canetti COMPOSITION THEOREM under an arbitrary environment with CONCURRENT multi-session
    execution (`ρ^π ≈ ρ^F`) — the apex `EpistemicConsensus §6` leaves open, discharged cross-system in
    CryptHOL for `F_com` (`UCBridge`), still open in general for `F_SIG`.

## No named-carrier laundering.

The only irreducible objects are the two cryptographic floors `SchnorrDLHard` / `MSISHard` (reached through
`HybridCombiner`) and the forking reductions (theorems of the existing forking machinery, passed as
hypotheses, never `axiom`s). `EufCma` is not re-asserted: it is the `HybridCombiner` game, and
`UcRealizes` is proved EQUIVALENT to it, so nothing about UC realization is assumed — it is derived.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}). Verified with
`lake env lean Dregg2/Crypto/UcSignature.lean`.

Cite: Canetti, *Universally Composable Security* (the `F_SIG` functionality + composition theorem);
the game-based ⟺ UC equivalence for signatures.
-/
import Dregg2.Crypto.HybridCombiner
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.UcSignature

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

/-! ## §1 — The ideal functionality `F_SIG`, the real protocol, the environment.

We reuse `HybridCombiner.SigScheme` as the interface, and its `Forgery`/`EufCma` games (the real
protocol's security). The IDEAL side is `Recorded : Msg → Prop`, the set of messages honest parties
signed; `F_SIG` accepts a message iff it is recorded. Modelling `F_SIG` as a `SigScheme` (`idealSig`,
whose `verify` consults `Recorded` and DISCARDS the signature) makes the ideal directly comparable to the
real scheme — and makes "unforgeability by construction" a theorem (`idealSig_no_forgery`). -/

/-- **`F_SIG` as an ideal `SigScheme`.** Keys are trivial (`Unit`), signatures carry no information
(`Unit`), and `verify _ m _ := Recorded m`: the ideal functionality accepts a message iff an honest party
recorded it, IGNORING the presented signature. This is the "unforgeability by construction" ideal — the
signature object is irrelevant, only the honest-record is consulted. -/
@[reducible] def idealSig {Msg : Type*} (Recorded : Msg → Prop) : SigScheme Unit Unit Msg Unit where
  pkOf _ := ()
  sign _ _ := ()
  verify _ m _ := Recorded m

/-- **UNFORGEABILITY BY CONSTRUCTION.** `F_SIG` admits NO forgery: a forgery is a fresh (`¬ Recorded m`)
verifying message, but `idealSig`'s `verify` on `m` is exactly `Recorded m`, so a forgery would require
`¬ Recorded m ∧ Recorded m`. The ideal world has no forgeries by definition — there is nothing for a
simulator to fake. -/
theorem idealSig_no_forgery {Msg : Type*} (Recorded : Msg → Prop) :
    EufCma (idealSig Recorded) () Recorded := by
  rintro ⟨m, _, hnr, hv⟩
  exact hnr hv

/-- **A UC ENVIRONMENT / distinguisher** for the signature functionality: it produces the `(message,
signature)` pair it will submit to the verifier and reads the accept bit. As with `LightClientUC.Env`,
there are no honest-party inputs to relay (the functionality is a one-shot verify oracle), so a bare
pair-producer is the dummy adversary and suffices. -/
abbrev Env (Msg Sig : Type*) : Type _ := Unit → Msg × Sig

/-! ## §2 — The realize relation and the distinguishing game.

`UcRealizes S pk Recorded` — the REAL scheme's accept bit never exceeds the IDEAL one: whenever the real
`verify pk m σ` accepts, the message was recorded. `Distinguishes` — the environment WINS: it submits a
pair the real scheme accepts but `F_SIG` rejects. The two equivalences are the beachhead's spine. -/

/-- **`UcRealizes S pk Recorded` — the real scheme UC-realizes `F_SIG`.** Whenever the real verifier
accepts a message under some signature, that message was recorded by an honest party (`Recorded m`). This
is the UC-indistinguishability of the real protocol from `F_SIG` for the deterministic single-shot verify
functionality, stated as the negation of the distinguishing event (the dummy-adversary form). -/
def UcRealizes {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    Prop :=
  ∀ (m : Msg) (σ : Sig), S.verify pk m σ → Recorded m

/-- **`Distinguishes S pk Recorded` — the environment DISTINGUISHES real from ideal.** There is an
environment `Z` whose submitted `(m, σ)` the real scheme ACCEPTS (`verify pk m σ`) though `F_SIG` REJECTS
it (`¬ Recorded m`). This is the bad event: the real and ideal worlds diverge on the accept bit. -/
def Distinguishes {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    Prop :=
  ∃ Z : Env Msg Sig, S.verify pk (Z ()).1 (Z ()).2 ∧ ¬ Recorded (Z ()).1

/-- **THE DISTINGUISHING EVENT IS A FORGERY.** `Distinguishes` and `Forgery` are the same proposition: an
environment that separates the real hybrid signature from `F_SIG` is precisely an adversary that produced
a verifying signature on a message no honest party signed. There is NO other way to tell the worlds apart
— the whole gap is a forgery on the honest key. -/
theorem distinguishes_iff_forgery {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    Distinguishes S pk Recorded ↔ Forgery S pk Recorded := by
  constructor
  · rintro ⟨Z, hv, hnr⟩; exact ⟨(Z ()).1, (Z ()).2, hnr, hv⟩
  · rintro ⟨m, σ, hnr, hv⟩; exact ⟨fun _ => (m, σ), hv, hnr⟩

/-- **REALIZING `F_SIG` IS EXACTLY `EufCma`.** `UcRealizes` and `EufCma` are logically equivalent: the
real scheme UC-realizes the ideal signature functionality iff it is existentially-unforgeable. This is the
load-bearing bridge — UC realization is not an extra assumption layered on top, it IS the game-based
security notion, so no UC content is laundered in. -/
theorem ucRealizes_iff_eufCma {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    UcRealizes S pk Recorded ↔ EufCma S pk Recorded := by
  constructor
  · intro h; rintro ⟨m, σ, hnr, hv⟩; exact hnr (h m σ hv)
  · intro h m σ hv; by_contra hnr; exact h ⟨m, σ, hnr, hv⟩

/-- **REAL ≈ IDEAL FAILS EXACTLY WHEN A FORGERY OCCURS.** `UcRealizes` is the negation of `Distinguishes`:
the real protocol is indistinguishable from `F_SIG` iff no environment can distinguish them, which by
`distinguishes_iff_forgery` happens iff no forgery exists. The `EufCma` hypothesis is thus load-bearing,
not decorative. -/
theorem ucRealizes_iff_not_distinguishes {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    UcRealizes S pk Recorded ↔ ¬ Distinguishes S pk Recorded := by
  rw [ucRealizes_iff_eufCma, distinguishes_iff_forgery]; rfl

/-! ## §3 — THE REDUCTION TO THE FLOOR: the hybrid signature UC-realizes `F_SIG` under `DL ∨ MSIS`. -/

/-- **`hybrid_sig_uc_realizes` — THE BEACHHEAD HEADLINE.** The hybrid `ed25519 × ML-DSA` signature
UC-realizes the ideal signature functionality `F_SIG` under `SchnorrDLHard ∨ MSISHard`. Given the two
forking reductions (a classical forgery ⟹ a `DLSolver`; a pq forgery ⟹ two SelfTargetMSIS solutions on a
shared commitment with distinct challenges — theorems of the existing forking machinery, NOT carriers),
whenever EITHER floor holds the hybrid is `EufCma` (`hybrid_secure_if_either_floor`), hence — by the
equivalence `ucRealizes_iff_eufCma` — UC-realizes `F_SIG`. So the hybrid signature can be plugged into any
protocol proven secure against `F_SIG`, and the composition survives down to `DL ∨ MSIS`. No new hardness
carrier is introduced: the reduction is the SAME as the game-based one. -/
theorem hybrid_sig_uc_realizes
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Recorded : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
    {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (dlFork : Forgery Cl pkc Recorded → DLSolver C G)
    (msisFork : Forgery Pq pkp Recorded →
      ∃ (w : N) (c c' : Rq) (z z' : M), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((β + β) + (β + β))) :
    UcRealizes (hybrid Cl Pq) (pkc, pkp) Recorded :=
  (ucRealizes_iff_eufCma _ _ _).2
    (hybrid_secure_if_either_floor Cl Pq pkc pkp Recorded C G A t β dlFork msisFork hfloor)

/-! ## §4 — NON-VACUITY, both poles: `EufCma` is what earns realization; a forgeable scheme loses it.

Reusing `HybridCombiner`'s toy schemes over `Unit` keys and `Bool` messages/signatures with the empty
signing transcript `noQueries` (every message fresh). `secureToy` verifies NOTHING (`EufCma` holds),
`brokenToy` verifies EVERYTHING (a forgery on any message). -/

/-- **(FIRES)** an `EufCma` scheme UC-realizes `F_SIG`: `secureToy` verifies nothing, so it never accepts an
unrecorded message — it realizes the ideal via the equivalence. The positive pole. -/
theorem secureToy_uc_realizes : UcRealizes secureToy () noQueries :=
  (ucRealizes_iff_eufCma _ _ _).2 secureToy_euf_cma

/-- **(BITES — a scheme WITHOUT `EufCma` does NOT realize `F_SIG`)** `brokenToy` verifies everything, so it
accepts the unrecorded message it never signed — a forgery, hence a distinguishing environment. The
negative pole: realization is genuinely violated when unforgeability fails. -/
theorem brokenToy_not_uc_realizes : ¬ UcRealizes brokenToy () noQueries := by
  intro h; exact (ucRealizes_iff_eufCma _ _ _).1 h brokenToy_forgeable

/-- The forgeable scheme is a DISTINGUISHING environment: `brokenToy` separates the real world from
`F_SIG`. The distinguishing event of §2 witnessed concretely — a forgery IS the separation. -/
theorem brokenToy_distinguishes : Distinguishes brokenToy () noQueries :=
  (distinguishes_iff_forgery _ _ _).2 brokenToy_forgeable

/-- **ONE SECURE COMPONENT SUFFICES.** The hybrid of a SECURE and a BROKEN component UC-realizes `F_SIG`,
delivered by the combiner from the single good half — even with a completely broken pq (or classical)
component the hybrid realizes the ideal. This is the composition payoff of "hybrid, not PQ-only". -/
theorem hybrid_secure_uc_realizes : UcRealizes (hybrid secureToy brokenToy) ((), ()) noQueries :=
  (ucRealizes_iff_eufCma _ _ _).2 hybrid_secure_via_left

/-- **THE LOAD-BEARING TOOTH.** If BOTH components are broken, the hybrid does NOT realize `F_SIG` — a
forgery goes through, distinguishing real from ideal. So the `EufCma` (⟸ `DL ∨ MSIS`) hypothesis in
`hybrid_sig_uc_realizes` is not vacuous: with neither floor holding, UC realization genuinely fails. -/
theorem hybrid_broken_not_uc_realizes : ¬ UcRealizes (hybrid brokenToy brokenToy) ((), ()) noQueries := by
  intro h; exact (ucRealizes_iff_eufCma _ _ _).1 h hybrid_broken_if_both

/-! ## §5 — THE SIMULATOR, made explicit (why the dummy adversary suffices).

For a UC realization one exhibits a simulator `S` such that for every environment `Z`, the real and ideal
executions are indistinguishable. For `F_SIG` the simulator is degenerate and named exactly, because the
functionality is a deterministic one-shot verify oracle:

  * **The simulator `S`.** It generates its OWN keypair `sk` and, when `F_SIG` records a message `m` (an
    honest party signed it), `S` produces the honest signature `S.sign sk m` and hands it to `Z`. By
    `Correct`, that signature VERIFIES — so recorded messages carry a verifying signature in the ideal
    world exactly as in the real world (completeness).
  * **Indistinguishability.** The only thing `S` cannot fake is a verifying signature on a NON-recorded
    message — that is a forgery, ruled out by `EufCma` (soundness). So the two worlds' observable (the
    accept bit) coincides on EVERY message iff `EufCma` holds; the distinguisher's advantage is exactly the
    `EufCma` advantage. We package the simulator as a real function and prove both obligations. -/

section Simulator

variable {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)

/-- **`simSign S sk m`** — the simulator's fabricated signature in the IDEAL world: the honest signature on
`m` under the simulator's own key `sk`. Built from what `F_SIG` reveals (the recorded message), touching no
real signer's secret. -/
def simSign (sk : SK) (m : Msg) : Sig := S.sign sk m

/-- **COMPLETENESS (the simulator's signature verifies).** Under `Correct S`, the simulator's fabricated
signature on ANY message verifies against its own public key — so every recorded message carries a
verifying signature in the ideal world, matching the real world. -/
theorem sim_complete (hc : Correct S) (sk : SK) (Recorded : Msg → Prop) :
    ∀ m, Recorded m → ∃ σ, S.verify (S.pkOf sk) m σ :=
  fun m _ => ⟨simSign S sk m, hc sk m⟩

/-- **REAL AND IDEAL ACCEPT BITS AGREE (the single-shot indistinguishability).** Under `EufCma` (soundness)
and the simulator's completeness, for EVERY message the real scheme's accept bit and `F_SIG`'s verdict
coincide: a message is accepted-under-some-signature in the real world iff it is accepted in the ideal
world. This is exactly the observable the environment reads, so no `Z` can distinguish — the realization is
witnessed at the accept-bit level, not merely as a one-directional soundness bound. -/
theorem real_ideal_agree (pk : PK) (Recorded : Msg → Prop)
    (hSound : EufCma S pk Recorded)
    (hComplete : ∀ m, Recorded m → ∃ σ, S.verify pk m σ) (m : Msg) :
    (∃ σ, S.verify pk m σ) ↔ (∃ u : Unit, (idealSig Recorded).verify () m u) := by
  constructor
  · rintro ⟨σ, hv⟩; exact ⟨(), (ucRealizes_iff_eufCma S pk Recorded).2 hSound m σ hv⟩
  · rintro ⟨_, hr⟩; exact hComplete m hr

end Simulator

/-! ## §6 — THE UC RESIDUAL, named (the HONEST BOUNDARY: what this beachhead does NOT yet give).

`hybrid_sig_uc_realizes` is a *static, single-functionality, deterministic* realization: the environment's
distinguishing advantage is a `Prop` (a forgery exists or not), collapsed to zero once `EufCma` holds. The
FULL Canetti UC theorem — realization under an arbitrary environment with CONCURRENT multi-session
execution, plus the composition theorem `ρ^π ≈ ρ^F` — additionally needs the probabilistic pieces below.
They live in CryptHOL (per `UCBridge`), not Lean's `Prop` world. We name them in a structure so the
residual is EXPLICIT (a labeled seam is work, not a wall), and DISCHARGE the one piece that IS a Lean
statement (the static realization, from `EufCma`). Mirrors `LightClientUC.DynamicUCResidual`. -/

/-- **`SigUCResidual S pk Recorded`** — the precise list of what a FULL dynamic-UC proof for `F_SIG` needs
beyond the static realization, each a named `Prop` carrier (never an `axiom`), TOGETHER with the one piece
discharged in Lean. Inhabiting it means: the static realization holds (PROVED here from `EufCma`), and the
probabilistic/compositional pieces hold (carried, cross-system). -/
structure SigUCResidual {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) where
  /-- DISCHARGED IN LEAN — the static realization: `EufCma ⟹ UcRealizes`. Filled by
  `ucRealizes_iff_eufCma`; the cheapest real sub-lemma, PROVED, not assumed. -/
  static_realize : EufCma S pk Recorded → UcRealizes S pk Recorded
  /-- CARRIED — the simulator is PPT (efficient). Lean's `EufCma` is a `Prop`; its efficiency is a
  complexity statement outside Lean's logic. -/
  simulator_ppt : Prop
  /-- CARRIED — `≈` is NEGLIGIBLE statistical/computational distance of ENSEMBLES indexed by the security
  parameter, not a Lean equality. The distinguishing advantage being negligible is the probabilistic
  content CryptHOL bounds. -/
  negligible_advantage : Prop
  /-- CARRIED — the Canetti composition theorem under CONCURRENT multi-session execution (`ρ^π ≈ ρ^F`): an
  arbitrary protocol calling the hybrid signature is indistinguishable from one calling `F_SIG`. The apex
  `EpistemicConsensus §6` leaves open; the genuine cross-system frontier. -/
  composes : Prop
  /-- The carried pieces hold (witnessed cross-system; operational content, FALSE for a broken floor). -/
  simulator_ppt_holds : simulator_ppt
  negligible_advantage_holds : negligible_advantage
  composes_holds : composes

/-- **`staticResidual` — the static half is ALWAYS constructible (PROVED).** The `static_realize` field is
discharged by `ucRealizes_iff_eufCma` for ANY `(S, pk, Recorded)`: this is the part of the dynamic-UC
obligation that is a real Lean theorem. The probabilistic fields are the explicit arguments a cross-system
discharge supplies — the structure cannot be built on `True`s alone, but its Lean core is genuine. -/
def staticResidual {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop)
    (ppt negl comp : Prop) (hppt : ppt) (hnegl : negl) (hcomp : comp) :
    SigUCResidual S pk Recorded where
  static_realize := (ucRealizes_iff_eufCma S pk Recorded).2
  simulator_ppt := ppt
  negligible_advantage := negl
  composes := comp
  simulator_ppt_holds := hppt
  negligible_advantage_holds := hnegl
  composes_holds := hcomp

/-- Non-vacuity of the residual: at the `secureToy` instance, with the probabilistic carriers discharged
trivially (the toy has no security parameter), the residual is inhabited AND its `static_realize` field
yields the real `UcRealizes` verdict from `EufCma`. The Lean core is genuine; only the toy's probabilistic
carriers are `True` (the REAL instance gets them cross-system). -/
def refResidual : SigUCResidual secureToy () noQueries :=
  staticResidual secureToy () noQueries True True True trivial trivial trivial

/-- The residual's discharged static field, applied to `secureToy`'s `EufCma`, IS the proved `UcRealizes` —
the UC-residual structure carries a REAL realization theorem, not a husk. -/
theorem refResidual_realizes : UcRealizes secureToy () noQueries :=
  refResidual.static_realize secureToy_euf_cma

/-! ## §7 — Teeth: `F_SIG` accepts recorded and rejects unrecorded; the toy schemes separate. -/

/-- A concrete recorded set over `Bool`: `true` is recorded, `false` is not — a decidable surrogate that
lets the `F_SIG` accept/reject behaviour be `decide`-checked. -/
@[reducible] def recTrue : Bool → Prop := fun b => b = true

-- `F_SIG` ACCEPTS a recorded message (`true`) — the ideal honours honest signatures…
#guard decide ((idealSig recTrue).verify () true ())
-- …and REJECTS an unrecorded message (`false`): NO forgery in the ideal, by construction.
#guard decide (¬ (idealSig recTrue).verify () false ())
-- An EUF-CMA scheme (`secureToy`) verifies NOTHING — it never accepts an unrecorded message (realizes).
#guard decide (¬ secureToy.verify () true false)
-- A non-EUF-CMA scheme (`brokenToy`) verifies EVERYTHING — a forgery, the distinguishing event.
#guard decide (brokenToy.verify () true false)
-- ONE secure half BLOCKS the hybrid: secure∧broken verification is FALSE — the hybrid realizes `F_SIG`.
#guard decide (¬ (hybrid secureToy brokenToy).verify ((), ()) true (true, false))
-- BOTH broken: the hybrid verification is TRUE — a forgery goes through, realization FAILS (load-bearing).
#guard decide ((hybrid brokenToy brokenToy).verify ((), ()) true (true, true))

#assert_all_clean [
  idealSig_no_forgery,
  distinguishes_iff_forgery,
  ucRealizes_iff_eufCma,
  ucRealizes_iff_not_distinguishes,
  hybrid_sig_uc_realizes,
  secureToy_uc_realizes,
  brokenToy_not_uc_realizes,
  brokenToy_distinguishes,
  hybrid_secure_uc_realizes,
  hybrid_broken_not_uc_realizes,
  sim_complete,
  real_ideal_agree,
  refResidual_realizes
]

end Dregg2.Crypto.UcSignature
