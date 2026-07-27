/-
  The certified Pancake chain: Lean-authored compiler stages with their emit-correctness
  proofs. Roots are the same set the source tree declares, so this cut builds the same
  library — no more, no less. Lean 4 core only (BitVec, omega, simp): no Mathlib, no
  external package, hence no `require`. Pinned via the sibling lean-toolchain.
-/
import Lake
open Lake DSL

package «orb-compiler» where
  -- keep the build deterministic; no default extra options
  leanOptions := #[]

@[default_target]
lean_lib Pancake where
  srcDir := "."
  roots := #[`Dsl.EmitPancake, `Pancake.Sem, `Pancake.Lower, `Pancake.EmitCorrectRegion, `Pancake.EmitCorrectCompose, `Pancake.EmitCorrectLoop, `Pancake.EmitCorrectClock, `Pancake.BytesModel, `Pancake.StructModel, `Pancake.SerializeCompile, `Pancake.RealStageDemo, `Pancake.NatToDecCompile, `Pancake.NatToDecFull, `Pancake.StageProg, `Pancake.StageCompile, `Pancake.StageMore, `Pancake.SerializeFull, `Pancake.SerializeHeaders, `Pancake.SerializeStruct, `Pancake.StageEvenMore, `Pancake.StructEmit, `Pancake.StageLiftHeader, `Pancake.StatusLineEmit, `Pancake.ModelUnify, `Pancake.ByteCopy, `Pancake.FullResponseCompile, `Pancake.ProofProducing, `Pancake.ServeFragment, `Pancake.ServeSlice, `Pancake.ServeEmit, `Pancake.LowerBridge, `Pancake.LowerBridgeSem, `Pancake.ServeExportServes, `Pancake.ServeConfigServe, `Pancake.ServeCompose, `Pancake.StageProg2, `Pancake.StageLiftGate, `Pancake.StageYetMore, `Pancake.ServeFull, `Pancake.DslServe, `Pancake.StageLift2, `Pancake.StageLift2Inst, `Pancake.StageLift2Cond, `Pancake.PredEval, `Pancake.CondRespProto]
