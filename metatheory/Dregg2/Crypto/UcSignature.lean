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

  **§6 — MULTI-SESSION `F̂_SIG` and the HYBRID ARGUMENT.** Many concurrent instances, each with its own key
  and honest record. The multi-session realize relation is per-session realization
  (`multiUcRealizes_iff_forall_session`); `multi_session_realization` proves the real scheme realizes `F̂_SIG`
  from per-session `EufCma`. The number-of-sessions factor is EXPLICIT: `worldVerify` is the hybrid chain
  `H_0 (all real) … H_n (all ideal)`, `worldVerify_step` one swap bounded by a single-session forgery, and
  `worldVerify_zero_le` chains exactly `n` of them (`multi_session_hybrid_telescope`). `hybrid_multi_session_uc_realizes`
  grounds it in `SchnorrDLHard ∨ MSISHard` per session.

  **§7 — THE UNIVERSAL COMPOSITION THEOREM.** A protocol `ρ` using `F_SIG` as a subroutine sees only its
  accept relation. Under `EufCma` + completeness the real and ideal accept relations are EQUAL
  (`accept_relations_agree`), so `uc_composition_theorem` gives `ρ^π = ρ^F` for ANY `ρ` into ANY output type
  — pure substitutivity, no restriction on `ρ`. `uc_composition_multi_session` is the full concurrent
  statement over `F̂_SIG`; `distinguishing_rho_yields_forgery` is the reduction the other way (a distinguishing
  `ρ` IS a forgery); `hybrid_sig_composes_under_floor` grounds composition in `DL ∨ MSIS`.

## HONEST BOUNDARY (named, not hidden — §8 `SigUCResidual`)

The Canetti UC theorem has three structural parts and ALL THREE are now DISCHARGED as real Lean theorems at
this model level: single-session realization (§2–§3), multi-session realization of `F̂_SIG` via the explicit
`n`-step hybrid (§6), and the universal composition theorem `ρ^π = ρ^F` (§7) — every one reduced to `EufCma`,
hence to `SchnorrDLHard ∨ MSISHard`, with no new carrier. What remains is NOT the composition argument but the
file-wide MODELLING LEVEL (carried as named `Prop` residues, never `axiom`s, mirroring
`LightClientUC.DynamicUCResidual` / `UCBridge.FComDischarge`):

  * `≈` is here EXACT `Prop`-equality — the collapse of statistical distance to 0/1 — rather than NEGLIGIBLE
    distance of probability ENSEMBLES indexed by the security parameter (the finer CryptHOL model);
  * the simulator's PPT efficiency (a complexity statement outside Lean's logic).

These are the SAME modelling abstractions the whole crypto tree operates at; they are not part of, and do not
weaken, the composition/multi-session reductions, which hold at distance 0 in this model.

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

/-! ## §6 — MULTI-SESSION `F̂_SIG` and the HYBRID ARGUMENT over sessions.

Canetti's UC runs MANY concurrent instances of a functionality. The multi-session signature functionality
`F̂_SIG` indexes each instance by a session id `i : SID`, with its OWN public key `pk i` and its OWN honest
record `Recorded i`. `F̂_SIG` accepts `(i, m, σ)` iff `Recorded i m`. The real world runs the SAME scheme `S`
in every session under `pk i`.

The multi-session realization is the standard HYBRID ARGUMENT: walk a chain of hybrid worlds `H_0, …, H_n`
where `H_j` runs the IDEAL functionality in sessions `< j` and the REAL scheme in sessions `≥ j`. `H_0` is
all-real, `H_n` is all-ideal, and each adjacent swap `H_j → H_{j+1}` flips exactly ONE session — bounded by
a SINGLE-session realization (i.e. no forgery in that session, `EufCma`). The number-of-sessions factor `n`
is therefore EXPLICIT: it is the length of the telescope (`worldVerify_zero_le` inducts `n` times), each
step discharged by one single-session `EufCma`. No union bound is smuggled into a carrier. -/

/-- **`MultiUcRealizes S pk Recorded`** — the multi-session realize relation: in EVERY session `i`, whenever
the real verifier accepts, the message was recorded in THAT session. This is the real ⊑ ideal statement for
`F̂_SIG`. -/
def MultiUcRealizes {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop) : Prop :=
  ∀ (i : SID) (m : Msg) (σ : Sig), S.verify (pk i) m σ → Recorded i m

/-- **`MultiForgery`** — a forgery in SOME session: a session `i` with a fresh (`¬ Recorded i m`) verifying
message. The multi-session distinguishing event. -/
def MultiForgery {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop) : Prop :=
  ∃ (i : SID) (m : Msg) (σ : Sig), ¬ Recorded i m ∧ S.verify (pk i) m σ

/-- **`MultiEufCma`** — no session has a forgery. The security of `F̂_SIG`'s real emulation. -/
def MultiEufCma {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop) : Prop :=
  ¬ MultiForgery S pk Recorded

/-- **THE UNION OVER SESSIONS, EXPLICIT.** A multi-session forgery is exactly a forgery in SOME single
session — the decomposition the hybrid argument sums over. In the probabilistic game this is the union bound
whose factor is the number of sessions; here it is a genuine `∃`-over-sessions, no carrier. -/
theorem multiForgery_iff_exists_session {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiForgery S pk Recorded ↔ ∃ i, Forgery S (pk i) (Recorded i) := by
  constructor
  · rintro ⟨i, m, σ, hnr, hv⟩; exact ⟨i, m, σ, hnr, hv⟩
  · rintro ⟨i, m, σ, hnr, hv⟩; exact ⟨i, m, σ, hnr, hv⟩

/-- `MultiEufCma` IS per-session `EufCma` in every session — the security of the multi-session functionality
factors through the single-session game, session by session. -/
theorem multiEufCma_iff_forall_session {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiEufCma S pk Recorded ↔ ∀ i, EufCma S (pk i) (Recorded i) := by
  unfold MultiEufCma EufCma
  rw [multiForgery_iff_exists_session]
  exact not_exists

/-- Multi-session realization IS multi-session `EufCma` — the multi-session analogue of
`ucRealizes_iff_eufCma`, no UC content laundered. -/
theorem multiUcRealizes_iff_multiEufCma {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiUcRealizes S pk Recorded ↔ MultiEufCma S pk Recorded := by
  rw [multiEufCma_iff_forall_session]
  constructor
  · intro h i; exact (ucRealizes_iff_eufCma _ _ _).1 (fun m σ hv => h i m σ hv)
  · intro h i m σ hv; exact (ucRealizes_iff_eufCma _ _ _).2 (h i) m σ hv

/-- Multi-session realization IS per-session realization — `F̂_SIG` is realized iff every session is. -/
theorem multiUcRealizes_iff_forall_session {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiUcRealizes S pk Recorded ↔ ∀ i, UcRealizes S (pk i) (Recorded i) := by
  constructor
  · intro h i m σ hv; exact h i m σ hv
  · intro h i m σ hv; exact h i m σ hv

/-- **`MULTI_SESSION_REALIZATION`.** If every session is single-session-`EufCma`, the real scheme realizes
the multi-session functionality `F̂_SIG`. This is the multi-session UC realization; the per-session `EufCma`
is exactly what each hybrid swap needs. -/
theorem multi_session_realization {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop)
    (h : ∀ i, EufCma S (pk i) (Recorded i)) : MultiUcRealizes S pk Recorded :=
  (multiUcRealizes_iff_forall_session S pk Recorded).2
    (fun i => (ucRealizes_iff_eufCma _ _ _).2 (h i))

/-! ### The hybrid chain `H_0 … H_n` over `Fin n` sessions — the number-of-sessions factor made a THEOREM.

`worldVerify … j` is the hybrid world `H_j`: sessions with index `< j` answer with the IDEAL functionality
(`Recorded i m`, the signature discarded), sessions `≥ j` answer with the REAL scheme. `H_0` is all-real,
`H_n` is all-ideal. `worldVerify_step` is ONE swap `H_j → H_{j+1}`, valid because the single flipped session
`j` realizes (real ⟹ ideal). `worldVerify_zero_le` chains `n` such swaps by induction; the count of
reductions is literally the induction length. -/

/-- The hybrid world `H_j`: ideal below the threshold `j`, real at/above it. -/
def worldVerify {n : ℕ} {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : Fin n → PK) (Recorded : Fin n → Msg → Prop) (j : ℕ)
    (i : Fin n) (m : Msg) (σ : Sig) : Prop :=
  if (i : ℕ) < j then Recorded i m else S.verify (pk i) m σ

/-- **ONE HYBRID SWAP.** If every session realizes, `H_j` accept implies `H_{j+1}` accept: the only session
that changes between the worlds is the one with index value `j`, where the world flips from the real verifier
to the ideal record — bounded by that session's realization (real ⟹ ideal). All other sessions are
identical. -/
theorem worldVerify_step {n : ℕ} {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : Fin n → PK) (Recorded : Fin n → Msg → Prop) (j : ℕ)
    (hj : ∀ i : Fin n, UcRealizes S (pk i) (Recorded i))
    (i : Fin n) (m : Msg) (σ : Sig) :
    worldVerify S pk Recorded j i m σ → worldVerify S pk Recorded (j + 1) i m σ := by
  simp only [worldVerify]
  rcases Nat.lt_trichotomy (i : ℕ) j with hlt | heq | hgt
  · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]; exact id
  · rw [if_neg (by omega), if_pos (by omega)]; intro hv; exact hj i m σ hv
  · rw [if_neg (by omega), if_neg (by omega)]; exact id

/-- **THE TELESCOPE.** Chaining `worldVerify_step` from `0` up to any `j` (induction on `j`): the all-real
world `H_0` accept implies `H_j` accept. Exactly `j` single-session swaps, each discharged by one session's
realization — the hybrid argument with the session count EXPLICIT as the recursion depth. -/
theorem worldVerify_zero_le {n : ℕ} {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : Fin n → PK) (Recorded : Fin n → Msg → Prop)
    (hj : ∀ i : Fin n, UcRealizes S (pk i) (Recorded i)) :
    ∀ (j : ℕ) (i : Fin n) (m : Msg) (σ : Sig),
      worldVerify S pk Recorded 0 i m σ → worldVerify S pk Recorded j i m σ := by
  intro j
  induction j with
  | zero => intro i m σ h; exact h
  | succ k ih => intro i m σ h; exact worldVerify_step S pk Recorded k hj i m σ (ih i m σ h)

/-- **MULTI-SESSION REALIZATION VIA THE HYBRID CHAIN.** For `n` concurrent sessions, if every session is
`EufCma`, the real scheme realizes `F̂_SIG` — proved by walking the hybrid chain `H_0 (all real) → H_n (all
ideal)`, `n` swaps each bounded by one single-session forgery. Same conclusion as `multi_session_realization`,
but reached through the EXPLICIT `n`-step hybrid, so the number-of-sessions factor is a theorem, not a
carrier. -/
theorem multi_session_hybrid_telescope {n : ℕ} {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : Fin n → PK) (Recorded : Fin n → Msg → Prop)
    (h : ∀ i, EufCma S (pk i) (Recorded i)) : MultiUcRealizes S pk Recorded := by
  have hr : ∀ i : Fin n, UcRealizes S (pk i) (Recorded i) :=
    fun i => (ucRealizes_iff_eufCma _ _ _).2 (h i)
  intro i m σ hv
  have h0 : worldVerify S pk Recorded 0 i m σ := by
    simp only [worldVerify]; rw [if_neg (Nat.not_lt_zero _)]; exact hv
  have hn : worldVerify S pk Recorded n i m σ := worldVerify_zero_le S pk Recorded hr n i m σ h0
  simp only [worldVerify] at hn
  rwa [if_pos i.isLt] at hn

/-- **THE HYBRID SIGNATURE REALIZES `F̂_SIG` UNDER `DL ∨ MSIS`.** Given the per-session forking reductions,
the hybrid `ed25519 × ML-DSA` signature realizes the MULTI-session functionality if EITHER floor holds:
`multi_session_realization` composed with `hybrid_secure_if_either_floor` in every session. Concurrent
composition survives to the same `SchnorrDLHard ∨ MSISHard` floor — no per-session carrier is introduced. -/
theorem hybrid_multi_session_uc_realizes
    {SID SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : SID → PKc) (pkp : SID → PKp) (Recorded : SID → Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (A : Mo →ₗ[Rq] No) (t : No) (nb : ℕ)
    (dlFork : ∀ i, Forgery Cl (pkc i) (Recorded i) → DLSolver C G)
    (msisFork : ∀ i, Forgery Pq (pkp i) (Recorded i) →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution A t nb z c w ∧ IsSelfTargetMSISSolution A t nb z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((nb + nb) + (nb + nb))) :
    MultiUcRealizes (hybrid Cl Pq) (fun i => (pkc i, pkp i)) Recorded :=
  multi_session_realization (hybrid Cl Pq) (fun i => (pkc i, pkp i)) Recorded
    (fun i => hybrid_secure_if_either_floor Cl Pq (pkc i) (pkp i) (Recorded i)
      C G A t nb (dlFork i) (msisFork i) hfloor)

/-! ### Teeth — the multi-session realization is load-bearing, both poles. -/

/-- **(FIRES)** a family of `EufCma` sessions realizes `F̂_SIG`. The positive pole over any session index. -/
theorem secureToy_multi_realizes {SID : Type*} :
    MultiUcRealizes secureToy (fun _ : SID => ()) (fun _ : SID => noQueries) :=
  multi_session_realization secureToy (fun _ => ()) (fun _ => noQueries) (fun _ => secureToy_euf_cma)

/-- **(BITES)** a family running the FORGEABLE scheme does NOT realize `F̂_SIG` — a session forgery (in every
session, here) is a multi-session distinguishing event. A scheme without `EufCma` fails multi-session
realization, so the per-session `EufCma` in `multi_session_realization` is load-bearing. -/
theorem brokenToy_multi_not_realizes :
    ¬ MultiUcRealizes brokenToy (fun _ : Bool => ()) (fun _ : Bool => noQueries) := by
  intro h; exact brokenToy_not_uc_realizes (fun m σ hv => h true m σ hv)

/-! ## §7 — THE UNIVERSAL COMPOSITION THEOREM: `ρ^π ≈ ρ^F` for an ARBITRARY protocol `ρ`.

This is the payoff. A protocol `ρ` that uses `F_SIG` as a SUBROUTINE observes it ONLY through its per-message
accept behaviour — the relation `accepts m := ∃ σ, verify pk m σ`. The composition operator plugs whatever
sits behind that interface into `ρ`, so `ρ` is a FUNCTION of the accept relation. `ρ^F` is `ρ` fed the ideal
accept relation (`= Recorded`); `ρ^π` is `ρ` fed the REAL scheme's accept relation.

Under `EufCma` (soundness: real ⟹ ideal, no forgery) AND completeness (ideal ⟹ real: honest records carry a
verifying signature — the simulator of §5), the two accept relations are EQUAL as `Msg → Prop`
(`accept_relations_agree`). Hence for ANY `ρ` whatsoever, `ρ (real) = ρ (ideal)` by congruence: the composed
protocols are INDISTINGUISHABLE — here `≈` is exact equality, the `Prop`-collapse of distance 0. The teeth
run the OTHER way: any `ρ` that distinguishes `ρ^π` from `ρ^F` yields a subroutine FORGERY
(`distinguishing_rho_yields_forgery`) — the composition operator plus the §5 simulator lifting a distinguisher
down to `pi`-vs-`F_SIG`. Composition fails EXACTLY at a forgery. -/

/-- **The real scheme's accept relation** as seen by a subroutine caller: a message is accepted iff SOME
signature verifies. This is `F_SIG`'s observable interface — what a protocol `ρ` querying the functionality
sees. -/
@[reducible] def acceptRel {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK) : Msg → Prop :=
  fun m => ∃ σ, S.verify pk m σ

/-- **THE ACCEPT RELATIONS COINCIDE.** Under `EufCma` and completeness, the real scheme's accept relation IS
the ideal `Recorded` relation, as functions `Msg → Prop`. Soundness gives real ⊑ ideal (no forgery),
completeness gives ideal ⊑ real (§5's simulator signs recorded messages); together, equality. This is the
observational equivalence of `pi` and `F_SIG` at the subroutine interface. -/
theorem accept_relations_agree {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK)
    (Recorded : Msg → Prop) (hSound : EufCma S pk Recorded)
    (hComplete : ∀ m, Recorded m → ∃ σ, S.verify pk m σ) :
    acceptRel S pk = Recorded := by
  funext m
  exact propext ⟨fun ⟨σ, hv⟩ => (ucRealizes_iff_eufCma S pk Recorded).2 hSound m σ hv,
                 fun hr => hComplete m hr⟩

/-- **THE UNIVERSAL COMPOSITION THEOREM (single-session).** For ANY protocol / environment `ρ` that uses
`F_SIG` as a subroutine — i.e. any function of the subroutine's accept relation, into ANY output type `β` —
running `ρ` with the real scheme `pi` produces the IDENTICAL result as running it with the ideal `F_SIG`,
provided the real scheme is `EufCma` and complete. `ρ^π = ρ^F`. This is the Canetti composition guarantee:
plug the (hybrid) signature into any `F_SIG`-secure protocol and behaviour is preserved — because the two
subroutines are observationally equal (`accept_relations_agree`). No monotonicity or restriction on `ρ`;
pure substitutivity. -/
theorem uc_composition_theorem {SK PK Msg Sig : Type*} {β : Sort*} (ρ : (Msg → Prop) → β)
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop)
    (hSound : EufCma S pk Recorded) (hComplete : ∀ m, Recorded m → ∃ σ, S.verify pk m σ) :
    ρ (acceptRel S pk) = ρ Recorded :=
  congrArg ρ (accept_relations_agree S pk Recorded hSound hComplete)

/-- **THE COMPOSITION REDUCTION (teeth).** Any protocol `ρ` that DISTINGUISHES `ρ^π` from `ρ^F` yields a
subroutine FORGERY on the honest key. Contrapositive of `uc_composition_theorem`: if there were no forgery
(`EufCma`) the outputs would be equal, so a difference forces a forgery. This is the composition operator
lifting an environment against the composed protocol down to an environment against `pi`-vs-`F_SIG` — the
distinguishing advantage is exactly the forgery advantage. -/
theorem distinguishing_rho_yields_forgery {SK PK Msg Sig : Type*} (ρ : (Msg → Prop) → Prop)
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop)
    (hComplete : ∀ m, Recorded m → ∃ σ, S.verify pk m σ)
    (hdist : ρ (acceptRel S pk) ≠ ρ Recorded) : Forgery S pk Recorded := by
  by_contra hno
  exact hdist (uc_composition_theorem ρ S pk Recorded hno hComplete)

/-! ### Multi-session composition — the FULL Canetti statement over `F̂_SIG`. -/

/-- **The multi-session accept relation** — per session, a message is accepted iff some signature verifies
under that session's key. The observable interface of `F̂_SIG`. -/
@[reducible] def multiAcceptRel {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) : SID → Msg → Prop :=
  fun i m => ∃ σ, S.verify (pk i) m σ

/-- The multi-session accept relations coincide with the multi-session record under per-session `EufCma` +
completeness — the observational equivalence of the concurrent real emulation and `F̂_SIG`. -/
theorem multi_accept_relations_agree {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop)
    (hSound : ∀ i, EufCma S (pk i) (Recorded i))
    (hComplete : ∀ i m, Recorded i m → ∃ σ, S.verify (pk i) m σ) :
    multiAcceptRel S pk = Recorded := by
  funext i m
  exact propext ⟨fun ⟨σ, hv⟩ => (ucRealizes_iff_eufCma _ _ _).2 (hSound i) m σ hv,
                 fun hr => hComplete i m hr⟩

/-- **THE UNIVERSAL COMPOSITION THEOREM (multi-session, the full `ρ^π ≈ ρ^F`).** For ANY protocol `ρ` using
the MULTI-session functionality `F̂_SIG` as a subroutine, replacing `F̂_SIG` by the concurrent real emulation
`pi` preserves `ρ`'s output exactly, under per-session `EufCma` + completeness. This is Canetti's composition
theorem for many concurrent signature instances: `ρ` with the real hybrid signature is indistinguishable from
`ρ` with the ideal multi-session functionality. -/
theorem uc_composition_multi_session {SID SK PK Msg Sig : Type*} {β : Sort*}
    (ρ : (SID → Msg → Prop) → β)
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop)
    (hSound : ∀ i, EufCma S (pk i) (Recorded i))
    (hComplete : ∀ i m, Recorded i m → ∃ σ, S.verify (pk i) m σ) :
    ρ (multiAcceptRel S pk) = ρ Recorded :=
  congrArg ρ (multi_accept_relations_agree S pk Recorded hSound hComplete)

/-- **THE COMPOSITION PAYOFF — the hybrid signature composes into ANY `F_SIG`-protocol under `DL ∨ MSIS`.**
For any protocol `ρ`, plugging the hybrid `ed25519 × ML-DSA` signature into `ρ` in place of the ideal `F_SIG`
preserves `ρ`'s behaviour, provided EITHER floor holds (`EufCma` via `hybrid_secure_if_either_floor`) and the
hybrid records are complete. So a game-based `DL ∨ MSIS` result GENUINELY composes: any `F_SIG`-secure
protocol stays secure with the real hybrid signature, down to the same floor, no new carrier. -/
theorem hybrid_sig_composes_under_floor
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*} {β : Sort*} (ρ : (Msg → Prop) → β)
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Recorded : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (A : Mo →ₗ[Rq] No) (t : No) (nb : ℕ)
    (dlFork : Forgery Cl pkc Recorded → DLSolver C G)
    (msisFork : Forgery Pq pkp Recorded →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution A t nb z c w ∧ IsSelfTargetMSISSolution A t nb z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((nb + nb) + (nb + nb)))
    (hComplete : ∀ m, Recorded m → ∃ σ, (hybrid Cl Pq).verify (pkc, pkp) m σ) :
    ρ (acceptRel (hybrid Cl Pq) (pkc, pkp)) = ρ Recorded :=
  uc_composition_theorem ρ (hybrid Cl Pq) (pkc, pkp) Recorded
    (hybrid_secure_if_either_floor Cl Pq pkc pkp Recorded C G A t nb dlFork msisFork hfloor)
    hComplete

/-! ### Teeth — composition holds iff no forgery; a forgeable scheme is a distinguishing `ρ`. -/

/-- **(FIRES)** for the `EufCma` `secureToy`, EVERY protocol `ρ` composes: `ρ^π = ρ^F`. The positive pole of
the composition theorem. -/
theorem secureToy_composition (ρ : (Bool → Prop) → Prop) :
    ρ (acceptRel secureToy ()) = ρ noQueries :=
  uc_composition_theorem ρ secureToy () noQueries secureToy_euf_cma (fun _ h => h.elim)

/-- **(BITES — composition FAILS without `EufCma`).** For the forgeable `brokenToy` there is a protocol `ρ`
(the one that queries "does `true` verify?") whose composed outputs DIFFER: `ρ^π` accepts the forged message,
`ρ^F` rejects it. So the `EufCma`/completeness hypothesis of `uc_composition_theorem` is load-bearing —
composition genuinely breaks exactly where a forgery lives. -/
theorem composition_fails_without_eufcma :
    ∃ ρ : (Bool → Prop) → Prop, ρ (acceptRel brokenToy ()) ≠ ρ noQueries := by
  refine ⟨fun R => R true, fun h => ?_⟩
  have hreal : (fun R : Bool → Prop => R true) (acceptRel brokenToy ()) := ⟨true, trivial⟩
  rw [h] at hreal
  exact hreal

/-! ## §8 — THE UC RESIDUAL, named (the HONEST BOUNDARY: what this beachhead does NOT yet give).

The Canetti UC theorem has THREE parts, and §6–§7 now DISCHARGE the two structural ones as real Lean
theorems at this model level: (a) the STATIC single-session realization (`ucRealizes_iff_eufCma`); (b)
MULTI-session realization of `F̂_SIG` via the explicit `n`-step hybrid (`multi_session_realization`,
`multi_session_hybrid_telescope`); (c) the UNIVERSAL COMPOSITION theorem `ρ^π = ρ^F` for an arbitrary
protocol `ρ` (`uc_composition_theorem`, `uc_composition_multi_session`) — all reduced to `EufCma`, hence to
`SchnorrDLHard ∨ MSISHard`. What remains is NOT part of the composition argument but the file-wide MODELLING
level: `≈` is here EXACT `Prop`-equality (the collapse of statistical distance to 0/1), not negligible
distance of ensembles indexed by the security parameter, and PPT-efficiency of the simulator is a complexity
statement outside Lean's logic (per `UCBridge`'s CryptHOL residue). We name those two finer-model pieces in a
structure so the boundary stays EXPLICIT, and the structure now DISCHARGES both structural obligations
(realization + composition), not just the static one. Mirrors `LightClientUC.DynamicUCResidual`. -/

/-- **`SigUCResidual S pk Recorded`** — the dynamic-UC obligation split into DISCHARGED Lean cores and the two
finer-probabilistic-model carriers. Inhabiting it means: the static realization AND the composition lift hold
(both PROVED here from `EufCma`), and the two modelling-level pieces (`≈` as negligible ensemble distance,
simulator PPT-efficiency) hold cross-system. Composition is no longer a carried `Prop` — it is a field of
proved-theorem type. -/
structure SigUCResidual {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) where
  /-- DISCHARGED IN LEAN — the static realization: `EufCma ⟹ UcRealizes`. Filled by
  `ucRealizes_iff_eufCma`; the cheapest real sub-lemma, PROVED, not assumed. -/
  static_realize : EufCma S pk Recorded → UcRealizes S pk Recorded
  /-- DISCHARGED IN LEAN — the UNIVERSAL COMPOSITION lift: for ANY protocol `ρ` using `F_SIG` as a
  subroutine, `ρ^π = ρ^F` under `EufCma` + completeness. Filled by `uc_composition_theorem`; the Canetti
  composition theorem is now a proved Lean statement, NOT a carried `Prop`. -/
  compose_lift : ∀ (ρ : (Msg → Prop) → Prop),
    EufCma S pk Recorded → (∀ m, Recorded m → ∃ σ, S.verify pk m σ) →
    ρ (acceptRel S pk) = ρ Recorded
  /-- CARRIED — the simulator is PPT (efficient). Lean's `EufCma` is a `Prop`; its efficiency is a
  complexity statement outside Lean's logic. -/
  simulator_ppt : Prop
  /-- CARRIED — `≈` as NEGLIGIBLE statistical/computational distance of ENSEMBLES indexed by the security
  parameter, rather than the EXACT equality proved here. The finer probabilistic model CryptHOL bounds; not
  part of the composition argument, which holds at distance 0 in this model. -/
  negligible_advantage : Prop
  /-- The carried modelling pieces hold (witnessed cross-system; operational content, FALSE for a broken
  floor). -/
  simulator_ppt_holds : simulator_ppt
  negligible_advantage_holds : negligible_advantage

/-- **`staticResidual` — the DISCHARGED cores are ALWAYS constructible (PROVED).** Both `static_realize`
(`ucRealizes_iff_eufCma`) and `compose_lift` (`uc_composition_theorem`) are filled by real theorems for ANY
`(S, pk, Recorded)`: these are the structural parts of the dynamic-UC obligation, now Lean theorems. The two
modelling-level fields are the explicit arguments a cross-system discharge supplies. -/
def staticResidual {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop)
    (ppt negl : Prop) (hppt : ppt) (hnegl : negl) :
    SigUCResidual S pk Recorded where
  static_realize := (ucRealizes_iff_eufCma S pk Recorded).2
  compose_lift := fun ρ hs hc => uc_composition_theorem ρ S pk Recorded hs hc
  simulator_ppt := ppt
  negligible_advantage := negl
  simulator_ppt_holds := hppt
  negligible_advantage_holds := hnegl

/-- Non-vacuity of the residual: at the `secureToy` instance, with the modelling carriers discharged trivially
(the toy has no security parameter), the residual is inhabited AND its DISCHARGED fields yield the real
`UcRealizes` and composition verdicts from `EufCma`. The Lean cores are genuine; only the toy's
probabilistic carriers are `True` (the REAL instance gets them cross-system). -/
def refResidual : SigUCResidual secureToy () noQueries :=
  staticResidual secureToy () noQueries True True trivial trivial

/-- The residual's discharged static field, applied to `secureToy`'s `EufCma`, IS the proved `UcRealizes` —
the UC-residual structure carries a REAL realization theorem, not a husk. -/
theorem refResidual_realizes : UcRealizes secureToy () noQueries :=
  refResidual.static_realize secureToy_euf_cma

/-- The residual's discharged COMPOSITION field, applied to `secureToy`'s `EufCma` and (vacuous)
completeness, IS the proved `ρ^π = ρ^F` for every protocol `ρ` — the composition theorem is carried as a
genuine field, not a placeholder. -/
theorem refResidual_composes (ρ : (Bool → Prop) → Prop) :
    ρ (acceptRel secureToy ()) = ρ noQueries :=
  refResidual.compose_lift ρ secureToy_euf_cma (fun _ h => h.elim)

/-! ## §9 — Teeth: `F_SIG` accepts recorded and rejects unrecorded; the toy schemes separate. -/

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
  multiForgery_iff_exists_session,
  multiEufCma_iff_forall_session,
  multiUcRealizes_iff_multiEufCma,
  multiUcRealizes_iff_forall_session,
  multi_session_realization,
  worldVerify_step,
  worldVerify_zero_le,
  multi_session_hybrid_telescope,
  hybrid_multi_session_uc_realizes,
  secureToy_multi_realizes,
  brokenToy_multi_not_realizes,
  accept_relations_agree,
  uc_composition_theorem,
  distinguishing_rho_yields_forgery,
  multi_accept_relations_agree,
  uc_composition_multi_session,
  hybrid_sig_composes_under_floor,
  secureToy_composition,
  composition_fails_without_eufcma,
  refResidual_realizes,
  refResidual_composes
]

end Dregg2.Crypto.UcSignature
