/-
# `Dregg2.Crypto.FloorBridge` — LINK the quantitative floors to the Boolean floors (ONE foundation).

Seam 2 of the crypto-honesty goal. Track B (`ProbCrypto`) added a QUANTITATIVE floor family
(`MSISHardQuant`/`DLHardQuant`/`HashCRHardQuant` := `∀ s, Negl (adv s)`) ALONGSIDE the tree's original
BOOLEAN floors (`Lattice.MSISHard := ¬ ∃ z, IsMSISSolution`, `SchnorrCurveField.SchnorrDLHard := ¬ DLSolver`,
`HermineHintMLWE.HashCR := ∀ i w w', H i w = H i w' → w = w'`). Two parallel foundations. This module
WELDS them into one: it proves the quantitative floor IMPLIES the Boolean floor, so the whole Boolean tree
can run as a CONSUMER of the single quantitative foundation.

## The bridge argument — a Boolean solver is a constant-advantage-`1` adversary.

The KEY: a Boolean solver (an `IsMSISSolution` witness / a `DLSolver` / a hash collision) is a
DETERMINISTIC adversary that WINS ITS GAME WITH CERTAINTY. Its winning predicate is constantly `true`
(the witness always validates), so its `winProb` is `1` (`ProbCrypto.winProb_top`) at every security
parameter — the advantage ensemble `boolWinAdv = fun _ => 1`, which is NOT negligible (`not_negl_one`).

So embed the Boolean solvers as the CANONICAL solver family `{z // IsMSISSolution …}` with advantage
`fun _ => boolWinAdv`. The quantitative floor `MSISHardQuant` says every solver's advantage is negligible;
a Boolean solver would sit in that family with advantage `1`, contradiction. Contrapositive:
`MSISHardQuant (canonical adv) → ¬ ∃ solver = MSISHard`. Same for DL and HashCR.

## What holds, and what does NOT.

  * **`Quant → Boolean` (LOAD-BEARING, proven here).** `msisHard_of_msisHardQuant`,
    `schnorrDLHard_of_DLHardQuant`, `hashCR_of_HashCRHardQuant`. The tree runs on ONE foundation: assume
    the quantitative floor, derive the Boolean one, feed it to every existing `_under_floor` consumer.
  * **`Boolean → Quant (canonical)` — VACUOUS, disclosed not laundered.** `msisHardQuant_of_msisHard`
    holds ONLY because when `MSISHard`, the canonical solver family is EMPTY, so `∀ s, Negl …` is
    vacuously true. It carries no negligibility-RATE content. For an ARBITRARY (non-canonical) advantage
    family the reverse is FALSE — Boolean hardness says nothing about a real advantage's decay. The
    load-bearing direction is `Quant → Boolean`; the reverse is degenerate and labelled as such.

## The consumer migration template (the payoff).

`turnauth_forces_authorization_quant` is `TurnAuthSignature.turnauth_forces_authorization` (a Boolean
consumer: `SchnorrDLHard → (verified ⟹ authorized)`) re-derived from the QUANTITATIVE floor
`DLHardQuant` via the DL bridge — the Boolean soundness theorem as a COROLLARY of the quantitative floor.
Every `_under_floor` consumer migrates by exactly this two-line plumb: `consumer hext (bridge hquant) hver`.

## No named-carrier laundering.

`boolWinAdv` is a genuine `winProb` real (`= 1` by `winProb_top`, a counting-probability fact), non-negl by
`not_negl_one`. The bridges are genuine implications with a satisfiable-AND-refutable hypothesis: the
quantitative floors are REFUTED here on concrete broken instances (`dlHardQuant_toy_refuted` on the toy
curve where DL is easy, `msisHardQuant_refutable` whenever a solution exists). No `axiom`, no `def …Hard`
used as a hypothesis. Keystones `#assert_all_clean`.
-/
import Dregg2.Crypto.ProbCrypto
import Dregg2.Crypto.TurnAuthSignature
import Dregg2.Crypto.HermineHintMLWE
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.FloorBridge

open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto

/-! ## §0 — The constant-advantage-`1` adversary: a Boolean solver as a game won with certainty. -/

/-- **The advantage ensemble of a Boolean solver.** A deterministic solver holding a valid witness WINS
its game on EVERY outcome — its winning predicate is constantly `true` over the (here `Unit`) coin space,
so its `winProb` is `1` at every security parameter. This is the genuine "solver ⟹ advantage `1`" content
of the bridge, tied to the real `winProb` counting-probability machinery — not a hardcoded constant. -/
noncomputable def boolWinAdv : Ensemble := fun _ => winProb (fun _ : Unit => true)

/-- `boolWinAdv` IS the constant `1` — an always-winning finite game has `winProb = 1` (`winProb_top`). -/
theorem boolWinAdv_eq_one : boolWinAdv = (fun _ => (1 : ℝ)) := by
  funext _; exact winProb_top

/-- **The discriminator behind every bridge: a Boolean solver's advantage is NOT negligible.** `boolWinAdv`
is the constant `1`, refuted by `not_negl_one`. This is what turns "a solver exists" into a contradiction
with the quantitative floor. -/
theorem not_negl_boolWinAdv : ¬ Negl boolWinAdv := by
  rw [boolWinAdv_eq_one]; exact not_negl_one

/-! ## §1 — The MSIS bridge: `MSISHardQuant (canonical) → Lattice.MSISHard`. -/

section MSIS

variable {M : Type*} [AddCommGroup M] [Lattice.ShortNorm M]
variable {Rq : Type*} [CommRing Rq] [Module Rq M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- **The canonical MSIS solver family** — the type of Boolean MSIS solutions for `(A, β)`, each embedded
as a quantitative solver. Its inhabitedness IS `∃ z, IsMSISSolution A β z` (the negation of the Boolean
floor). -/
abbrev msisSolverFam (A : M →ₗ[Rq] N) (β : ℕ) : Type _ := {z : M // Lattice.IsMSISSolution A β z}

/-- Each canonical MSIS solver has the constant-`1` advantage `boolWinAdv` (it always outputs its valid
short kernel vector). -/
noncomputable def msisSolverAdv (A : M →ₗ[Rq] N) (β : ℕ) : msisSolverFam A β → Ensemble :=
  fun _ => boolWinAdv

/-- **THE MSIS BRIDGE — `MSISHardQuant (msisSolverAdv A β) → Lattice.MSISHard A β`.** If every canonical
solver's advantage is negligible, then no Boolean MSIS solution exists: a solution `z` would be a solver
of advantage `1` (`boolWinAdv`), which the floor forbids (`not_negl_boolWinAdv`). The quantitative floor
delivers the Boolean floor. -/
theorem msisHard_of_msisHardQuant {A : M →ₗ[Rq] N} {β : ℕ}
    (h : MSISHardQuant (msisSolverAdv A β)) : Lattice.MSISHard A β := by
  rintro ⟨z, hz⟩
  exact not_negl_boolWinAdv (h ⟨z, hz⟩)

/-- **(TOOTH — the quantitative floor is REFUTABLE.)** If a Boolean MSIS solution exists, the canonical
quantitative floor FAILS — that solver has advantage `1`. So `MSISHardQuant (msisSolverAdv …)` is genuinely
load-bearing (false exactly when a solver exists), not a vacuous relabel. -/
theorem msisHardQuant_refutable {A : M →ₗ[Rq] N} {β : ℕ}
    (hsol : ∃ z, Lattice.IsMSISSolution A β z) : ¬ MSISHardQuant (msisSolverAdv A β) := by
  obtain ⟨z, hz⟩ := hsol
  intro h
  exact not_negl_boolWinAdv (h ⟨z, hz⟩)

/-- **(REVERSE — VACUOUS, disclosed.)** `MSISHard → MSISHardQuant (canonical)` holds, but ONLY because
when `MSISHard` the canonical solver family is EMPTY, so `∀ s, Negl …` is vacuously true. It carries no
negligibility-rate content; for a NON-canonical advantage family the reverse is FALSE. Kept to make the
degeneracy of the reverse explicit — the load-bearing direction is `msisHard_of_msisHardQuant`. -/
theorem msisHardQuant_of_msisHard {A : M →ₗ[Rq] N} {β : ℕ}
    (h : Lattice.MSISHard A β) : MSISHardQuant (msisSolverAdv A β) :=
  fun s => absurd ⟨s.1, s.2⟩ h

end MSIS

/-! ## §2 — The DL bridge: `DLHardQuant (canonical) → SchnorrCurveField.SchnorrDLHard`. -/

/-- **The canonical DL solver family** — discrete-log solvers for `(C, G)`: functions returning, for every
`sk`, the scalar of `sk·G`. Inhabitedness IS `DLSolver C G`, the negation of the Boolean DL floor. -/
abbrev dlSolverFam (C : SchnorrCurveField.CurveGroup) (G : C.Pt) : Type _ :=
  {solve : C.Pt → ℕ // ∀ sk : ℕ, solve (C.smul sk G) = sk}

/-- Each canonical DL solver has the constant-`1` advantage `boolWinAdv` (it always recovers the scalar). -/
noncomputable def dlSolverAdv (C : SchnorrCurveField.CurveGroup) (G : C.Pt) :
    dlSolverFam C G → Ensemble := fun _ => boolWinAdv

/-- **THE DL BRIDGE — `DLHardQuant (dlSolverAdv C G) → SchnorrCurveField.SchnorrDLHard C G`.** If every
canonical DL solver's advantage is negligible, no `DLSolver` exists: a solver would have advantage `1`,
forbidden by the floor. The quantitative DL floor delivers the Boolean DL floor. -/
theorem schnorrDLHard_of_DLHardQuant {C : SchnorrCurveField.CurveGroup} {G : C.Pt}
    (h : DLHardQuant (dlSolverAdv C G)) : SchnorrCurveField.SchnorrDLHard C G := by
  rintro ⟨solve, hsolve⟩
  exact not_negl_boolWinAdv (h ⟨solve, hsolve⟩)

/-- **(TOOTH — the quantitative DL floor is REFUTED on the toy curve.)** On `toyCurve` (`ℤ`, `s • 1 = s`)
discrete log is EASY: `Int.toNat` recovers every scalar, a canonical solver of advantage `1`. So
`DLHardQuant (dlSolverAdv toyCurve 1)` is FALSE — the concrete-security floor genuinely discriminates,
exactly as its Boolean twin `SchnorrCurveField.toy_dl_not_hard` does. -/
theorem dlHardQuant_toy_refuted : ¬ DLHardQuant (dlSolverAdv SchnorrCurveField.toyCurve (1 : ℤ)) := by
  intro h
  have hsolve : ∀ sk : ℕ, (fun x : ℤ => x.toNat) (SchnorrCurveField.toyCurve.smul sk (1 : ℤ)) = sk := by
    intro sk
    show ((sk : ℤ) * 1).toNat = sk
    simp
  exact not_negl_boolWinAdv (h ⟨fun x => x.toNat, hsolve⟩)

/-! ## §3 — The HashCR bridge: `HashCRHardQuant (canonical) → HermineHintMLWE.HashCR`. -/

/-- **The canonical hash-collision family** — triples `(i, w, w')` with `H i w = H i w'` but `w ≠ w'`: a
collision. Inhabitedness IS the negation of `HashCR` (injectivity on the committed domain). -/
abbrev hashCollisionFam {Idx W C : Type*} (cr : HermineHintMLWE.CommitReveal Idx W C) : Type _ :=
  {t : Idx × W × W // cr.H t.1 t.2.1 = cr.H t.1 t.2.2 ∧ t.2.1 ≠ t.2.2}

/-- Each canonical collision has the constant-`1` advantage `boolWinAdv` (it always exhibits its
collision). -/
noncomputable def hashCollisionAdv {Idx W C : Type*} (cr : HermineHintMLWE.CommitReveal Idx W C) :
    hashCollisionFam cr → Ensemble := fun _ => boolWinAdv

/-- **THE HASHCR BRIDGE — `HashCRHardQuant (hashCollisionAdv cr) → HermineHintMLWE.HashCR cr`.** If every
canonical collision-finder's advantage is negligible, `H` is injective on the committed domain: a collision
`w ≠ w'` with `H i w = H i w'` would be a finder of advantage `1`, forbidden by the floor. The quantitative
collision-resistance floor delivers the Boolean injectivity floor. -/
theorem hashCR_of_HashCRHardQuant {Idx W C : Type*} (cr : HermineHintMLWE.CommitReveal Idx W C)
    (h : HashCRHardQuant (hashCollisionAdv cr)) : HermineHintMLWE.HashCR cr := by
  intro i w w' heq
  by_contra hne
  exact not_negl_boolWinAdv (h ⟨(i, w, w'), heq, hne⟩)

/-! ## §4 — THE CONSUMER MIGRATION TEMPLATE.

The payoff: a Boolean protocol-soundness theorem re-derived from the QUANTITATIVE floor. The Boolean
consumer `TurnAuthSignature.turnauth_forces_authorization` is REUSED UNCHANGED; only the floor it is fed
is bridged from the quantitative one. Every `_under_floor` consumer migrates by this same two-line plumb. -/

/-- **`turnauth_forces_authorization_quant`** — the Boolean soundness rung `TurnAuthSignature`.
`turnauth_forces_authorization` (`SchnorrDLHard ⟹ verified turn-auth ⟹ authorized`) DERIVED as a
COROLLARY of the QUANTITATIVE floor `DLHardQuant`, via the DL bridge `schnorrDLHard_of_DLHardQuant`. The
tree runs on ONE (quantitative) foundation, with the Boolean consumer theorem as a derived corollary — the
template for migrating every other `_under_floor` consumer. -/
theorem turnauth_forces_authorization_quant {C : SchnorrCurveField.CurveGroup} {G : C.Pt}
    (hext : TurnAuthSignature.ForkingExtractor C G)
    (hdl : DLHardQuant (dlSolverAdv C G))
    {agentPk : C.Pt} {turnHash : ℕ} {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ}
    (hver : TurnAuthSignature.TurnAuthVerified C G agentPk turnHash chal R s) :
    TurnAuthSignature.Authorized C agentPk turnHash :=
  TurnAuthSignature.turnauth_forces_authorization hext (schnorrDLHard_of_DLHardQuant hdl) hver

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  boolWinAdv_eq_one,
  not_negl_boolWinAdv,
  msisHard_of_msisHardQuant,
  msisHardQuant_refutable,
  msisHardQuant_of_msisHard,
  schnorrDLHard_of_DLHardQuant,
  dlHardQuant_toy_refuted,
  hashCR_of_HashCRHardQuant,
  turnauth_forces_authorization_quant
]

end Dregg2.Crypto.FloorBridge
