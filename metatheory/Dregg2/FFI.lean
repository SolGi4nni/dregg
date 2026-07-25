-- §1.1 Turn execution.  (`Dregg2.Exec.FFIDirect` imports `Dregg2.Exec.FFI`, which imports
-- `Dregg2.Exec.FFI.Narrow`; all three are listed for the reader, not for Lake.)
import Dregg2.Exec.FFI
import Dregg2.Exec.FFI.Narrow
import Dregg2.Exec.FFIDirect

-- §1.3 Verified decisions the node routes through.
import Dregg2.Exec.DeployedConstraint
import Dregg2.Exec.DistributedExports
import Dregg2.Circuit.CrossCellConserveDecision
import Dregg2.Distributed.FinalityGate
import Dregg2.Distributed.StrandAdmission
import Dregg2.Deos.FlowRefine
import Dregg2.Grain.R3Verify
import Dregg2.Storage.Deployed
import Dregg2.Bridge.ProofOfHoldings
import Dregg2.Bridge.InterchainAdapterDecision
import Dregg2.Games.AutomataflFFI
import Dregg2.Games.MultiwayTugFFI
import Dregg2.Apps.DelegAdmit

-- §1.4 Post-quantum cores.
import Dregg2.Crypto.Fips203Kem
import Dregg2.Crypto.Fips204Verify
import Dregg2.Crypto.MlDsaKeygen
import Dregg2.Crypto.MlDsaSignReal
import Dregg2.Crypto.MlKemDecaps
import Dregg2.Crypto.MlKemEncaps
import Dregg2.Crypto.MlKemKeygen

-- §1.5 Exported with no current caller — in the closure deliberately (see §1.5, §4).
import Dregg2.Crypto.HandlebarsFFI
import Dregg2.Crypto.X25519HkdfExtract
import Dregg2.Circuit.FriLedger
import Dregg2.Circuit.Emit.CommitmentTreeAppendEmit
import Dregg2.Bridge.ConditionalInterchainAdapter
import Dregg2.Bridge.LightClientEthGate
import Dregg2.Bridge.LightClientMptGate
import Dregg2.Bridge.LightClientTendermintGate

/-!
# `Dregg2.FFI` — THE Lean⟷Rust boundary. One file. This one.

**What this module IS.** The single C-compilation root of the verified runtime. Every
`@[export]`-ed symbol that Rust may call is in this module's transitive import closure, and
*nothing is in that closure except because this file put it there*. `dregg-lean-ffi/build.rs`
builds exactly one Lake target — `Dregg2.FFI` — and splices exactly this module's closure into
`libdregg_lean.a`.

**Why it exists.** The question "what can Rust call into Lean for?" used to be answerable only by
grepping 172 `@[export]` attributes across 28 files and cross-checking them against a
hand-maintained 24-entry target list inside `build.rs`. Those two lists drifted, and drift here is
silent: a module missing from the target list emits no `:c` facet, so its symbol never enters the
archive, so the `#[cfg(dregg_*_present)]` bridge on the Rust side compiles its *absent* arm and the
node runs the un-gated path. It fails green. Three gates were dark that way when this file was
written (§4). Rooting the build on an import closure instead of a list makes that failure mode
structurally impossible: you cannot forget to add a module to a list that no longer exists.

**What this module is NOT.** It is not a place to put logic. It declares no definitions and proves
no theorems — it is a *manifest realized as imports*. Every export keeps living next to the proof
that justifies it; this file only fixes which of them are the runtime's boundary.

---

## §1 — The surface, by what it decides

172 exported symbols. Grouped by what a caller gets from them, with the module that owns each.

### §1.1 Turn execution — the kernel Rust hosts (8 symbols)
* `Dregg2.Exec.FFI` — `dregg_exec_full_forest_auth`, `dregg_exec_handler_turn`
* `Dregg2.Exec.FFI.Narrow` — `dregg_exec_full_turn`, `dregg_kernel_authorized`,
  `dregg_kernel_transfer_total`, `dregg_record_kernel_step`, `dregg_record_kernel_step_caps`,
  `dregg_record_kernel_transfer_total`

### §1.2 The no-copy `lean_object*` boundary (127 symbols)
* `Dregg2.Exec.FFIDirect` — the `dregg_d_*` constructor/accessor pairs Rust uses to build a
  `WTurn`/`WState` in place instead of marshalling JSON, plus `dregg_exec_full_forest_auth_direct`,
  `dregg_exec_full_forest_auth_direct_profiled`, `dregg_ffi_identity`.
  These are *not* decisions; they are the wire. They are 74 % of the symbol count and a rounding
  error of the archive.

### §1.3 Verified decisions the node routes through (18 symbols)
Each of these gates a `#[cfg(dregg_*_present)]` bridge whose absent arm reverts a proven verdict to
a Rust twin, a fail-closed refusal, or a test module that simply stops existing.
* `Dregg2.Exec.DeployedConstraint` — `dregg_constraint_admits`
* `Dregg2.Circuit.CrossCellConserveDecision` — `dregg_cross_cell_conserves` (House Law #1, Σδ=0)
* `Dregg2.Distributed.FinalityGate` — `dregg_blocklace_finalize`, `dregg_finalization_quorum`,
  `dregg_tau_order`
* `Dregg2.Distributed.StrandAdmission` — `dregg_strand_admit`
* `Dregg2.Exec.DistributedExports` — `dregg_captp_validate_handoff`, `dregg_captp_process_drop`,
  `dregg_captp_pipeline_resolve`, `dregg_coord_2pc_decide`, `dregg_coord_causal_order`,
  `dregg_coord_shared_budget`
* `Dregg2.Deos.FlowRefine` — `dregg_decide_refines`
* `Dregg2.Grain.R3Verify` — `dregg_grain_r3_verify`
* `Dregg2.Storage.Deployed` — `dregg_storage_content_root`
* `Dregg2.Bridge.ProofOfHoldings` — `dregg_holding_grant_weight`
* `Dregg2.Bridge.InterchainAdapterDecision` — `dregg_interchain_reached_consensus`
* `Dregg2.Games.AutomataflFFI` — `dregg_automatafl_rules` (the automatafl board transition,
  legality, conflict set and win — the whole game oracle `dregg-automatafl/src/reference.rs` used
  to answer with a transcription of a non-canonical Rust experiment; see §2)
* `Dregg2.Apps.DelegAdmit` — `dregg_deleg_admit` (the delegated tool/MCP-access admission verdict:
  SCOPE ∧ DEADLINE ∧ single-step ∧ sane-prior ∧ RATE, the predicate
  `Dregg2.Apps.ToolAccessDelegation.tool_invocation_commit_iff_admit` and its three rejection teeth
  are proven over. It replaced THREE hand-maintained Rust re-implementations of the same five
  conjuncts — `sdk/src/tool_gateway.rs`, `starbridge-apps/tool-access-delegation/src/lib.rs`,
  `dreggnet-offerings/src/session.rs` — each of which called itself "the byte-faithful Rust mirror".
  Absent ⇒ every routed gateway REFUSES; there is no Rust arm left to fall back to.)
* `Dregg2.Games.MultiwayTugFFI` — `dregg_multiway_tug_rules` (multiway-tug's action/response
  legality, the escrow split, row control, the tallies and the adjudicated round winner — the
  decisions `dregg-multiway-tug/src/reference.rs` re-expressed in Rust, with `winner_of` already
  DRIFTED to `roundWinner` minus its adjudication tail; see §2)

### §1.4 Post-quantum cores — the crates these take OUT of the TCB (10 symbols)
Absent ⇒ `dregg-pq` answers with an unaudited third-party crate. `DREGG_REQUIRE_PQ_CORES` turns
that into a build failure.
* `Dregg2.Crypto.Fips204Verify` — `dregg_fips204_verify`, `dregg_fips204_verify_real`,
  `dregg_fips204_sign`
* `Dregg2.Crypto.MlDsaSignReal` — `dregg_fips204_sign_real`
* `Dregg2.Crypto.MlDsaKeygen` — `dregg_mldsa_keygen_real`
* `Dregg2.Crypto.Fips203Kem` — `dregg_fips203_encaps`, `dregg_fips203_decaps`
* `Dregg2.Crypto.MlKemEncaps` / `MlKemDecaps` / `MlKemKeygen` — `dregg_mlkem_encaps_real`,
  `dregg_mlkem_decaps_real`, `dregg_mlkem_keygen_real`

### §1.5 Exported, with NO caller anywhere in the workspace (11 symbols)
Kept in the closure deliberately — deleting an export is a separate decision from rooting the
build, and each of these has a Lean-side proof that would lose its runtime meaning. Recorded here
so the next reader does not have to rediscover it:
* `Dregg2.Crypto.HandlebarsFFI` — `dregg_render_with_proof`, `dregg_replay_check`
* `Dregg2.Crypto.X25519HkdfExtract` — `dregg_x25519_ladder_step`, `dregg_hkdf_combine`
* `Dregg2.Circuit.FriLedger` — `dregg_fri_ledger` (Rust mentions it only in doc comments)
* `Dregg2.Circuit.Emit.CommitmentTreeAppendEmit` — `dregg_note_tree_root`
* `Dregg2.Bridge.ConditionalInterchainAdapter` — `dregg_interchain_conditional_admit`
* `Dregg2.Bridge.LightClientEthGate` / `LightClientMptGate` / `LightClientTendermintGate` —
  `dregg_eth_lc_verify`, `dregg_mpt_lc_verify`, `dregg_tm_lc_verify` (see §4)
* `Dregg2.Exec.FFIDirect` — `dregg_d_auth_of_tag`
* `Dregg2.Exec.FFI.Narrow` — `dregg_record_kernel_transfer_total`

---

## §2 — What this module deliberately EXCLUDES

* **Every proof that is not needed to run.** The exports' *justifications* stay in their own
  modules and their own `lake build`. This file pulls a module in only when a symbol Rust can call
  lives there. It is not the whole-tree build, and `lake build` still covers the tree.
* **Most of `Dregg2/Games/**`.** A game *program* is data the deployed evaluator admits or refuses
  (`dregg_constraint_admits`, `Dregg2.Exec.DeployedConstraint`), not a C symbol, so
  `Games.DungeonProgram` and `Games.MultiwayTugProgram` stay out — a program is CHECKED, not
  computed. The distinction is per-DECISION, not per-game: `Games.MultiwayTugFFI` is in the closure
  (below) while `Games.MultiwayTugProgram` is not, because the same game needs its teeth checked and
  its rules computed, and only the latter needs a C symbol.

  **`Dregg2.Games.AutomataflFFI` is the exception, and it is here for a measured reason.**
  automatafl's turn is not a program the evaluator runs: `dregg-automatafl` needs the *game oracle*
  — which board a round resolves to, which moves are legal, which coordinates clash, who won — to
  fill the witness of the Lean-emitted descriptor and to run the playable surface. That oracle was a
  hand-written Rust transcription (`src/reference.rs`) of `~/dev/automatafl/logic`, a non-canonical
  experiment, and the conformance audit found it divergent from the ruleset on 2-cycles and on the
  inclusive path check — with the divergence *documented in-tree* in `resolve_witness.rs` rather than
  fixed. A game whose semantics the runtime must COMPUTE needs a C symbol; one whose semantics the
  runtime merely CHECKS does not. This closure now carries the former.

  **`Dregg2.Games.MultiwayTugFFI` is here for the SAME measured reason, and it is the second member
  of a class the twin-deletion sweep could not see.** That sweep hunted twins of Lean *AIR*;
  `dregg-multiway-tug/src/reference.rs` is a twin of a Lean *SPEC*, so it was filed "not a twin" and
  survived. It had already drifted: its `winner_of` is the model's `roundWinner` truncated to the two
  absolute thresholds, so it answers "no winner" on every sub-threshold round the model ADJUDICATES
  (`undecidedState_adjudicates`) — the fix that took the draw rate from 66.1% to 5.1%. The tug
  surface must COMPUTE legality, the escrow split, row control and the winner to run a match, so
  that oracle needs a C symbol.
* **Emit drivers** (`EmitDungeonProgram`, `Emit*`). Those are `lean_exe`s that write fixtures at
  build time; they are not linked into any node.
* **`Metatheory/`, `Polis/`, `Market/`, `Bfv/` as libraries.** A handful of their modules are in
  the closure transitively (they are imported *by* an export-carrying module); none is a root here.

---

## §3 — Why this is a legacy (non-`module`) file, measured

Lean 4.30's module system is the right long-term answer to the archive's size: `meta import` marks
an import as proof-only, which keeps it out of `emitInitFn`'s transitive `initialize_` chain, which
is the mechanism that links ~200 MB of Mathlib whose compute is never called. Two facts, both
checked against this toolchain rather than assumed:

1. `meta import` requires `module`. A file without the `module` keyword fails with
   `cannot use 'meta import' without 'module'`.
2. **`module` cannot import non-`module`.** `module` + `import Dregg2.Circuit.CrossCellConserveDecision`
   fails with `cannot import non-'module' Dregg2.Circuit.CrossCellConserveDecision from 'module'`.

So `module` is viral *downward*: converting this file requires converting its whole closure first.
That closure is **193 of our own `.lean` files** (184 `Dregg2`, 8 `Metatheory`, 1 `Polis`) — and
*not* Mathlib, which is already converted at the pinned revision (7985 of 8098 files carry
`module`). The conversion is therefore entirely inside our tree and entirely tractable, but it is
193 files of per-file judgment about which imports are proof-only, and it is not a prerequisite for
rooting the build on one file. Rooting first; conversion second, bottom-up, with this file last.

---

## §4 — Known defects this file makes visible (not yet fixed here)

The three interchain light-client gates are **dark end to end**, at three independent layers:

1. `Dregg2.Bridge.LightClient{Eth,Mpt,Tendermint}Gate` were absent from `build.rs`'s target list, so
   no `:c` facet was emitted and `dregg_{eth,mpt,tm}_lc_verify` were the only Lean exports missing
   from the built archive. Importing them here fixes *this* layer.
2. `build.rs` never declares or sets `cfg(dregg_eth_lc_verify_present)`, so
   `bridge_lc_ffi.rs`'s `#[cfg(all(lean_lib_present, dregg_eth_lc_verify_present))]` arm is
   unreachable regardless of the archive.
3. The C shim it would call, `dregg_eth_lc_verify_str`, is declared and called in
   `dregg-lean-ffi/src/bridge_lc_ffi.rs` but **defined nowhere** — `lean_init.c` has 32 `_str`
   wrappers and this is not one of them.

Layers 2 and 3 are Rust/C work outside this file. Until they land, `eth_lc_verify_available()` is
constantly false and the ETH relayer path runs un-gated. `dregg_mpt_lc_verify` and
`dregg_tm_lc_verify` have no Rust caller at all.
-/
