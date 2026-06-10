-- The foundation: the IR, the two interpretations, the unified guard, the turn wrapper,
-- the nonce reconciliation, the policy enforcement.
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Argus.Compile
import Dregg2.Circuit.Argus.CompileFold
import Dregg2.Circuit.Argus.CompileE
import Dregg2.Circuit.Argus.Guard
import Dregg2.Circuit.Argus.Turn
import Dregg2.Circuit.Argus.Nonce
import Dregg2.Circuit.Argus.Policy

-- The interpreter edge: the verified descriptor-evaluator (decideVm = satisfiedVm,
-- the TCB-shrinking reference) + the emit round-trip (the serialize edge closed).
import Dregg2.Circuit.Argus.InterpCore
import Dregg2.Circuit.Argus.EmitRoundtrip

-- The five protocol layers (the apex).
import Dregg2.Circuit.Argus.Receipt
import Dregg2.Circuit.Argus.Coeffect
import Dregg2.Circuit.Argus.Joint
import Dregg2.Circuit.Argus.Disclose
import Dregg2.Circuit.Argus.Aggregate

-- The per-effect welds (~40 effects: interp = executor, compile = circuit, welded).
-- The escrow/obligation/bridge-Lock/Finalize/Cancel welds were REMOVED with their
-- kernel effects (dregg3 F1a — they re-land as factory cell-programs in Apps/).
import Dregg2.Circuit.Argus.Effects.Attenuate
import Dregg2.Circuit.Argus.Effects.BalanceA
import Dregg2.Circuit.Argus.Effects.BridgeMint
import Dregg2.Circuit.Argus.Effects.Burn
import Dregg2.Circuit.Argus.Effects.CellDestroy
import Dregg2.Circuit.Argus.Effects.CellSeal
import Dregg2.Circuit.Argus.Effects.CellUnseal
import Dregg2.Circuit.Argus.Effects.CreateCell
import Dregg2.Circuit.Argus.Effects.CreateCellFromFactory
import Dregg2.Circuit.Argus.Effects.CreateSealPair
import Dregg2.Circuit.Argus.Effects.Delegate
import Dregg2.Circuit.Argus.Effects.DelegateAtten
import Dregg2.Circuit.Argus.Effects.DropRef
import Dregg2.Circuit.Argus.Effects.EmitEvent
import Dregg2.Circuit.Argus.Effects.ExerciseViaCapability
import Dregg2.Circuit.Argus.Effects.IncrementNonce
import Dregg2.Circuit.Argus.Effects.Introduce
import Dregg2.Circuit.Argus.Effects.MakeSovereign
import Dregg2.Circuit.Argus.Effects.Mint
import Dregg2.Circuit.Argus.Effects.Noop
import Dregg2.Circuit.Argus.Effects.NoteCreate
import Dregg2.Circuit.Argus.Effects.NoteSpend
import Dregg2.Circuit.Argus.Effects.NoteSpendCompose
import Dregg2.Circuit.Argus.Effects.PipelinedSend
-- (F2a) Effects.QueueEnqueue / Effects.QueueDequeue DELETED: the queue family classifies
-- `.factory .queue` (VerbRegistry); its behavior is the verified Apps/QueueFactory et al.
import Dregg2.Circuit.Argus.Effects.ReceiptArchive
import Dregg2.Circuit.Argus.Effects.RefreshDelegation
import Dregg2.Circuit.Argus.Effects.Refusal
import Dregg2.Circuit.Argus.Effects.RevokeDelegation
import Dregg2.Circuit.Argus.Effects.Seal
import Dregg2.Circuit.Argus.Effects.SetField
import Dregg2.Circuit.Argus.Effects.SetPermissions
import Dregg2.Circuit.Argus.Effects.SetVerificationKey
import Dregg2.Circuit.Argus.Effects.SwissDrop
import Dregg2.Circuit.Argus.Effects.SwissEnliven
import Dregg2.Circuit.Argus.Effects.SwissExport
import Dregg2.Circuit.Argus.Effects.SwissHandoff
import Dregg2.Circuit.Argus.Effects.SwissReconcile
import Dregg2.Circuit.Argus.Effects.Unseal

/-!
# Argus — the faithful witness chain (the coherence anchor)

*One reified term, two readings that provably agree.* This module imports the whole
Argus library so it builds and stands as one coherent thing.

Argus is the front-end that welds dregg's protocol semantics into a single IR: every
effect is a `RecStmt` term whose **`interp` IS the verified executor** and whose
**`compile` IS the runnable circuit**, proven to agree — so the circuit cannot drift
from what the system does. A `witnessed` guard and a circuit obligation are the same
mechanism, so caveats / cell-assertions / the silently-ignored state-constraints all
flow through one gate (Bucket-B given real circuit teeth). The whole column closes up
to a light client: `Q` = receipt = `cellCommit`, the disclosure dial is a projection
of `Q`, and the strand/aggregate carry the faithful `Q`.

What stands here (all `#assert_axioms`-clean, every gap a named hypothesis — never
papered): the foundation, ~40 effects welded across every shape, the policy
enforcement, the three crowns (capability non-amplification as the full lattice gate
in-band · double-spend non-membership · installed-assertion enforcement), and the five
protocol layers (Receipt/Coeffect/Joint/Disclose/Aggregate). The named residuals are
the honest floor: the §8 crypto portals, the shape-AIR-vs-real-AIR interpreter edge,
the structural-alloc primitive (CreateCell, obstruction *proven*), and a short
divergence burn-down (delegation-epoch, dropRef refcount). The escrow / obligation /
bridge-Lock/Finalize/Cancel effect families left the kernel circuit strata (dregg3
F1a) — they re-land as verified factory cell-programs
(`Dregg2/Apps/{EscrowFactory,ObligationFactory,BridgeCell}.lean`); BridgeMint (the
shield verb) survives.
-/
