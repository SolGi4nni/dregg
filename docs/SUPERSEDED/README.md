# docs/SUPERSEDED — replaced wholesale; read the successor instead

Moved here by the 2026-07-16 triage (docs/audit/TRIAGE-2026-07-16.md, which
carries the per-file evidence). Git history preserves every prior location.

| moved file | superseded by |
|---|---|
| NULLIFIER-ACCUMULATOR-DESIGN.md | the deployed VK-epoch nullifier flip: `metatheory/Dregg2/Exec/RecordKernel.lean` (nullifierRoot/revokedRoot/commitmentsRoot) + `Exec/NullifierAccumulatorKernelBridge.lean`; `circuit/src/descriptor_ir2.rs` (noteSpendVmDescriptor2R24) |
| NULLIFIER-ACCUMULATOR-UNIFICATION.md | same as above (canonical Lean 3-accumulator roots + Rust ghost mirror) |
| ERE-FORMALIZATION-ASSESSMENT.md | docs/deos/DERIVATIVE-MATCHING-DESIGN.md |
| HERMES-INTEGRATION.md | deos-hermes/DESIGN.md + docs/deos/LOG-A-HERMES-IN.md |
| NATIVE-PROOF-BRIDGES.md | docs/deos/ETH-NATIVE-WRAP.md |
| STARK-PROVER-PERF-REVIEW.md | stark-kill: circuit/src/stark.rs is deleted; deployed proving rides the Lean-emitted p3/HidingFriPcs path |
| UPGRADE.md (ops) | deploy/aws/README.md ("build elsewhere, ship the image") + deploy/PRACTICES.md |
| MEMORY-LEGS-SCOPE.md | docs/reference/STARK-SOUNDNESS-CENSUS.md |
| PHASE2-ALL-EFFECTS-SOUNDNESS.md | docs/reference/STARK-SOUNDNESS-CENSUS.md |
| STARK-COMPLETION-AUTOMATION.md | docs/reference/STARK-SOUNDNESS-CENSUS.md |
| STARK-FLOOR-REDUCTION.md | docs/reference/STARK-SOUNDNESS-CENSUS.md |
