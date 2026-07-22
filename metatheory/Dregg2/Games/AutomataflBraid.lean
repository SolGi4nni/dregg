/-
# AutomataflBraid — all-Lean sealed reveal → resolution → automaton → winner.

This file is the game-level braid over the three Lean-authored semantic legs:

* Leg S (`AutomataflRevealRefine`) opens two sealed moves;
* Leg R refines `old → resolveMid old moves`;
* Leg A refines `mid → automatonStep mid`;
* the pure game reads `winner` from the resulting board.

The functional braid below is n-generic at the pure-game layer. The existing emitted
Leg-R/Leg-A capstones prove these exact stage relations at their currently closed
instantiation (`NN = 2`); fixed-n11 Leg S cannot honestly be attached to that circuit
pair yet. `ProofNativeDeploymentJoin` names the equality carriers an n11 proof-native
caller would need, while `CurrentLiveDeployment` additionally names the live host
encoding and n=5 shape. `no_current_live_deployment` proves the latter cannot be
inhabited today. Nothing here registers a descriptor or treats those residuals as
closed.

The collision theorem is unconditional: a substituted opening with the same published
commitment and different reveal data yields an explicit arity-4 collision. The stronger
no-collision statement remains conditional and is not used by the game braid.
-/
import Dregg2.Circuit.Emit.AutomataflResolveRefine
import Dregg2.Circuit.Emit.AutomataflRevealJoin
import Dregg2.Circuit.Emit.AutomataflTurnCapstone

namespace Dregg2.Games.AutomataflBraid

open Dregg2.Games.Automatafl
open Dregg2.Circuit.DescriptorIR2 (VmTrace)
open Dregg2.Circuit.Emit.AutomataflCommit
  (boardCode packCell)
open Dregg2.Circuit.Emit.AutomataflRevealEmit
  (N PACK_FELTS)
open Dregg2.Circuit.Emit.AutomataflRevealRefine
  (PublicOpening Opens LegSSemantics SameOpeningData publicOpening swapped_opening_extracts_collision)
open Dregg2.Circuit.Emit.AutomataflRevealJoin
  (FieldOctet OldBoardPack AppRootWeldsCommitPair RevealPreservesCommitPair
   OldBoardPackEqualityCarrier LiveHostSealMatchesLegS LIVE_GAME_N
   legS_commit_pair_bound_to_preceding fixed_n11_descriptor_is_not_live_game_shape)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Revealed openings become pure game moves. -/

/-- Convert Leg S's canonical public opening to the pure game's move value. `Opens`
proves all four integer coordinates lie in `[0,11)` and the seat is exactly 0/1. -/
def openingMove (m : PublicOpening) : Move :=
  Move.mk m.seat.toNat ⟨m.fx.toNat, m.fy.toNat⟩ ⟨m.tx.toNat, m.ty.toNat⟩

def revealedMoves (t : VmTrace) : List Move :=
  [openingMove (publicOpening t 0), openingMove (publicOpening t 1)]

theorem openingMove_who {hash : List ℤ → ℤ} {s : Nat} {m : PublicOpening}
    (h : Opens hash s m) : (openingMove m).who = s := by
  simp [openingMove, h.seatExact]

theorem openingMove_inBounds11 {hash : List ℤ → ℤ} {s : Nat} {m : PublicOpening}
    (h : Opens hash s m) :
    (openingMove m).frm.x < N ∧ (openingMove m).frm.y < N ∧
      (openingMove m).to.x < N ∧ (openingMove m).to.y < N := by
  obtain ⟨hfx0, hfx1⟩ := h.fxBounds
  obtain ⟨hfy0, hfy1⟩ := h.fyBounds
  obtain ⟨htx0, htx1⟩ := h.txBounds
  obtain ⟨hty0, hty1⟩ := h.tyBounds
  simp only [openingMove, N]
  omega

/-! ## 2. The pure staged turn and its functional outcome. -/

structure TurnOutcome where
  mid : Board
  final : Board
  win : Option Pid

/-- The staged relation targeted respectively by Leg R, Leg A, and the winner read. -/
def TurnBraid (old : Board) (moves : List Move) (goals : List (Coord × Pid))
    (out : TurnOutcome) : Prop :=
  out.mid = resolveMid old moves ∧
  out.final = automatonStep out.mid ∧
  out.win = winner out.final goals

def runTurn (old : Board) (moves : List Move) (goals : List (Coord × Pid)) : TurnOutcome :=
  let mid := resolveMid old moves
  let final := automatonStep mid
  ⟨mid, final, winner final goals⟩

theorem runTurn_satisfies (old : Board) (moves : List Move) (goals : List (Coord × Pid)) :
    TurnBraid old moves goals (runTurn old moves goals) := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Functional turn outcome.** Once the old board, revealed pair, and goals are
fixed, the resolved board, automaton result, and winner are unique. -/
theorem turnBraid_functional {old : Board} {moves : List Move} {goals : List (Coord × Pid)}
    {out₁ out₂ : TurnOutcome} (h₁ : TurnBraid old moves goals out₁)
    (h₂ : TurnBraid old moves goals out₂) : out₁ = out₂ := by
  obtain ⟨hm₁, hf₁, hw₁⟩ := h₁
  obtain ⟨hm₂, hf₂, hw₂⟩ := h₂
  have hm : out₁.mid = out₂.mid := hm₁.trans hm₂.symm
  have hf : out₁.final = out₂.final :=
    hf₁.trans ((congrArg automatonStep hm).trans hf₂.symm)
  have hw : out₁.win = out₂.win :=
    hw₁.trans ((congrArg (fun b => winner b goals) hf).trans hw₂.symm)
  cases out₁
  cases out₂
  simp_all

/-- Leg-R and Leg-A's semantic targets compose definitionally into the whole pure
turn. The emitted R/A capstones establish these relations cell-wise at their closed
n=2 instantiation; an n11 instantiation is a named deployment residual below. -/
theorem turnBraid_of_legR_legA {old mid final : Board} {moves : List Move}
    {goals : List (Coord × Pid)}
    (hR : mid = resolveMid old moves) (hA : final = automatonStep mid) :
    TurnBraid old moves goals ⟨mid, final, winner final goals⟩ :=
  ⟨hR, hA, rfl⟩

/- The concrete capstones this braid consumes semantically. `#check` deliberately
retains their full real types rather than wrapping away any `Satisfied2`, canonicality,
row-length, PI-seam, or chip-table premise. The whole-turn circuit capstone is now
`AutomataflTurnCapstone.turn_sat_imp_roundStep_pi` at the deployed `n = 11` (over `roundStep` /
`resolveMoves` / the FINAL corrected board `cMidV4`, with the seam a fully emitted-crypto-free
consequence of the `cMidV4`-packing commitment); the retired V2 `resolve_step_sat_imp_applyTurn`
(`applyTurn` / `resolveMid`, `NN = 2`) is superseded by it. -/
#check @Dregg2.Circuit.Emit.AutomataflTurnCapstone.turn_sat_imp_roundStep_pi
#check Dregg2.Circuit.Emit.AutomataflRevealRefine.legS_sat_imp_semantics

/-- Leg S selects the move pair; the R/A/winner braid then has one outcome. -/
def RevealTurnBraid (hash : List ℤ → ℤ) (t : VmTrace) (old : Board)
    (goals : List (Coord × Pid)) (out : TurnOutcome) : Prop :=
  LegSSemantics hash t ∧ TurnBraid old (revealedMoves t) goals out

/-- The three semantic legs compose: Leg S fixes the pair, Leg R fixes `mid`, Leg A
fixes `final`, and the winner is the pure read on `final`. -/
theorem revealTurnBraid_of_legs {hash : List ℤ → ℤ} {t : VmTrace}
    {old mid final : Board} {goals : List (Coord × Pid)}
    (hS : LegSSemantics hash t)
    (hR : mid = resolveMid old (revealedMoves t))
    (hA : final = automatonStep mid) :
    RevealTurnBraid hash t old goals ⟨mid, final, winner final goals⟩ :=
  ⟨hS, turnBraid_of_legR_legA hR hA⟩

theorem revealTurnBraid_functional {hash : List ℤ → ℤ} {t : VmTrace} {old : Board}
    {goals : List (Coord × Pid)} {out₁ out₂ : TurnOutcome}
    (h₁ : RevealTurnBraid hash t old goals out₁)
    (h₂ : RevealTurnBraid hash t old goals out₂) : out₁ = out₂ :=
  turnBraid_functional h₁.2 h₂.2

/-! ## 3. Commit/reveal deployment carriers — exact, and explicitly incomplete. -/

/-- The nine felts supplied by the old-board carrier are exactly the pure n11
board's injective base-4 packing. -/
def OldPackRepresentsBoard (beforePack : OldBoardPack) (old : Board) : Prop :=
  ∀ j : Fin PACK_FELTS, beforePack j = packCell (boardCode old N) j.val

/-- The proof-native n11 join. This deliberately excludes the live host encoding:
it says exactly what a future n11 fold must prove before Leg S may drive the game. -/
structure ProofNativeDeploymentJoin (hash : List ℤ → ℤ) (t : VmTrace) (old : Board)
    (before after : FieldOctet) (beforePack : OldBoardPack) : Prop where
  reveal : LegSSemantics hash t
  oldSize : old.size = N
  commitWeld : AppRootWeldsCommitPair t after
  commitPreserved : RevealPreservesCommitPair before after
  oldPackWeld : OldBoardPackEqualityCarrier t beforePack
  oldPackRepresents : OldPackRepresentsBoard beforePack old

theorem proofNativeJoin_commits_preceding {hash : List ℤ → ℤ} {t : VmTrace} {old : Board}
    {before after : FieldOctet} {beforePack : OldBoardPack}
    (h : ProofNativeDeploymentJoin hash t old before after beforePack) :
    ∀ s : Fin 2,
      (publicOpening t s.val).commit =
        before ⟨Dregg2.Circuit.Emit.AutomataflRevealJoin.COMMIT_FIELD_KEY + s.val, by
          have hs := s.isLt
          simp only [Dregg2.Circuit.Emit.EffectVmEmitRotationV3.CUSTOM_APP_FIELD_OCTET_LEN,
            Dregg2.Circuit.Emit.AutomataflRevealJoin.COMMIT_FIELD_KEY]
          omega⟩ :=
  legS_commit_pair_bound_to_preceding h.reveal h.commitWeld h.commitPreserved

theorem proofNativeJoin_oldPack_preceding {hash : List ℤ → ℤ} {t : VmTrace} {old : Board}
    {before after : FieldOctet} {beforePack : OldBoardPack}
    (h : ProofNativeDeploymentJoin hash t old before after beforePack) :
    ∀ j : Fin PACK_FELTS,
      t.pub (Dregg2.Circuit.Emit.AutomataflRevealEmit.PACK_PI_BASE + j.val)
        = packCell (boardCode old N) j.val := by
  intro j
  exact (h.oldPackWeld j).trans (h.oldPackRepresents j)

/-- The actual live relation adds the current BLAKE3 host equality and live game
shape. It is named so no theorem can silently substitute Poseidon2/n11 for them. -/
structure CurrentLiveDeployment (hash : List ℤ → ℤ) (t : VmTrace) (old : Board)
    (before after : FieldOctet) (beforePack : OldBoardPack) (hostSeal : Fin 2 → Nat) : Prop
    extends ProofNativeDeploymentJoin hash t old before after beforePack where
  hostEncoding : LiveHostSealMatchesLegS t hostSeal
  liveSize : old.size = LIVE_GAME_N

/-- **Current deployment is refused at the type-level relation.** A board cannot be
both fixed-n11 Leg S's board and the live n5 game's board. The BLAKE3/Poseidon and
heap-carrier mismatches remain additional blockers even after this size cutover. -/
theorem no_current_live_deployment {hash : List ℤ → ℤ} {t : VmTrace} {old : Board}
    {before after : FieldOctet} {beforePack : OldBoardPack} {hostSeal : Fin 2 → Nat} :
    ¬ CurrentLiveDeployment hash t old before after beforePack hostSeal := by
  intro h
  have hshape : LIVE_GAME_N = N := h.liveSize.symm.trans h.oldSize
  exact fixed_n11_descriptor_is_not_live_game_shape hshape

/-- The currently closed emitted R/A braid is n2, independently of the live n5
surface mismatch. It therefore cannot yet consume fixed-n11 Leg S either. -/
def CLOSED_LEG_RA_N : Nat := Dregg2.Circuit.Emit.AutomataflResolveEmit.NN

theorem fixed_n11_reveal_is_not_closed_n2_legRA : CLOSED_LEG_RA_N ≠ N := by
  decide

/-! ## 4. Collision extraction and winner safety. -/

/-- **Unconditional swapped-opening RED theorem, at braid level.** If a replacement
opening for either seat is accepted under the same commitment but changes any revealed
move/seat/nonce datum, the pair itself is an explicit arity-4 collision. -/
theorem swapped_reveal_in_braid_extracts_collision {hash : List ℤ → ℤ} {t : VmTrace}
    {s : Nat} (hs : s < 2) (hS : LegSSemantics hash t) {replacement : PublicOpening}
    (hReplacement : Opens hash s replacement)
    (hCommit : (publicOpening t s).commit = replacement.commit)
    (hSwap : ¬ SameOpeningData (publicOpening t s) replacement) :
    ∃ x y : List ℤ, x.length = 4 ∧ y.length = 4 ∧ x ≠ y ∧ hash x = hash y := by
  have hOriginal : Opens hash s (publicOpening t s) := by
    interval_cases s
    · exact hS.2.2.1
    · exact hS.2.2.2
  exact swapped_opening_extracts_collision hOriginal hReplacement hCommit hSwap

/-- **No spurious winner.** A winner emitted by the complete turn outcome owns a
declared goal at the final Automaton position. -/
theorem turnBraid_no_spurious_winner {old : Board} {moves : List Move}
    {goals : List (Coord × Pid)} {out : TurnOutcome} {p : Pid}
    (hBraid : TurnBraid old moves goals out) (hWin : out.win = some p) :
    ∃ c, (c, p) ∈ goals ∧ out.final.automaton = c := by
  apply winner_sound out.final goals p
  rw [← hBraid.2.2]
  exact hWin

/-! ## 5. Driven game traces. -/

def winningGoals : List (Coord × Pid) := [(⟨2, 3⟩, 3)]
def nonWinningGoals : List (Coord × Pid) := [(⟨0, 0⟩, 7)]

def drivenWinning : TurnOutcome := runTurn demoBoard [] winningGoals
def drivenNonWinning : TurnOutcome := runTurn demoBoard [] nonWinningGoals

theorem drivenWinning_is_braid : TurnBraid demoBoard [] winningGoals drivenWinning :=
  runTurn_satisfies _ _ _

theorem drivenWinning_winner : drivenWinning.win = some 3 := by
  decide

theorem drivenNonWinning_is_braid : TurnBraid demoBoard [] nonWinningGoals drivenNonWinning :=
  runTurn_satisfies _ _ _

theorem drivenNonWinning_winner : drivenNonWinning.win = none := by
  decide

#guard drivenWinning.win == some 3
#guard drivenNonWinning.win == none
#guard drivenWinning.final.automaton == (⟨2, 3⟩ : Coord)

/-! ## 6. Axiom hygiene. -/

#assert_axioms openingMove_inBounds11
#assert_axioms turnBraid_functional
#assert_axioms turnBraid_of_legR_legA
#assert_axioms revealTurnBraid_of_legs
#assert_axioms revealTurnBraid_functional
#assert_axioms proofNativeJoin_commits_preceding
#assert_axioms proofNativeJoin_oldPack_preceding
#assert_axioms no_current_live_deployment
#assert_axioms fixed_n11_reveal_is_not_closed_n2_legRA
#assert_axioms swapped_reveal_in_braid_extracts_collision
#assert_axioms turnBraid_no_spurious_winner
#assert_axioms drivenWinning_is_braid
#assert_axioms drivenWinning_winner
#assert_axioms drivenNonWinning_winner

#print axioms turnBraid_functional
#print axioms swapped_reveal_in_braid_extracts_collision
#print axioms turnBraid_no_spurious_winner
#print axioms no_current_live_deployment

end Dregg2.Games.AutomataflBraid
