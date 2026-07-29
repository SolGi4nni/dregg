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
-- MINA — these two have LIVE callers (`bridge/src/mina_observer.rs`) and belong in §1.3, not
-- §1.5. They are here because THIS FILE is the archive boundary: rooting a gate in `Dregg2.lean`
-- makes it ELABORATE, it does not put its `@[export]` in `libdregg_lean.a`. `Dregg2.lean:1536-1537`
-- rooted both on 2026-07-29 and the symbols were still absent from every archive, so every Mina
-- settlement returned `VerifiedGateUnavailable` — layer 1 of §4, re-entered by a lane that had
-- read §4. Added 2026-07-29; +31 modules to the closure (KimchiVerify's Pasta cone), no
-- `MinaWrapSrsG` (that 32,768-literal module is NOT reachable from these two).
import Dregg2.Bridge.LightClientMinaGate
import Dregg2.Bridge.PicklesWrapShapeGate
-- `dregg_mina_proof_chain_ok` — the PROOF↔PROOF chain gate. Same layer-1 reasoning as the two
-- above: rooted only in `Dregg2.lean` it would ELABORATE and emit no `:c` facet, so the export
-- would never enter any archive and the observer would refuse every settlement. Added
-- 2026-07-29; +0 modules to the closure (it imports only `KimchiVerify`, already pulled in by
-- `PicklesWrapShapeGate`).
import Dregg2.Bridge.PicklesProofChainGate
-- `dregg_mina_state_hash_word_ok` — the proof↔`stateHash` DERIVATION: public-input words 11 and 12
-- computed, per block, from the SERVED header and the served proof bytes. Same layer-1 reasoning
-- as the three above. Added 2026-07-29; +1 module to the closure (`PastaPoseidonFq`, the `fq_kimchi`
-- half; everything else it needs came in with `PicklesProofChainGate`).
import Dregg2.Bridge.MinaStateHashWordGate

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
* `Dregg2.Bridge.LightClientMinaGate` — `dregg_mina_lc_verify` (the Samasika anchored-segment
  verdict) and `Dregg2.Bridge.PicklesWrapShapeGate` — `dregg_mina_wrap_shape_ok` (the per-block
  Pickles Wrap-proof preamble). Both fail closed with NO Rust arm: absent ⇒ `bridge`'s
  `MinaObserver::observe_settlement` returns `ObserveError::VerifiedGateUnavailable` for EVERY
  settlement, so Mina cannot settle at all. Added to this closure 2026-07-29 — see the import
  block's note for why rooting them in `Dregg2.lean` was not enough.
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
* ⚠ `Dregg2.Bridge.LightClientTendermintGate` / `LightClientTendermintSkip` **NO LONGER BELONG IN
  §1.5** — ROUTED 2026-07-29. They were callerless when this section was written: measured
  2026-07-28, `dregg_tm_lc_verify` had no caller outside `dregg-lean-ffi` and `cosmos-lightclient`
  did not depend on that crate at all, so the Cosmos path was UN-ROUTED rather than gated — an
  ORPHAN, not the ETH pattern of a hand-written Rust twin standing beside a proven decision. There
  was no Tendermint twin to delete; `verify_cosmos_header` delegated (correctly) to the audited
  informalsystems `ProdVerifier`, and the proven gate simply sat beside it.
  `cosmos-lightclient/src/verified_gate.rs` now routes every accept path through them, fail-closed
  on an absent archive, and the two exports cover DISJOINT height ranges:
  `dregg_tm_lc_verify` decides the ADJACENT advance (epoch binding + strict `2·tot < 3·sp`) and
  `dregg_tm_skip_verify` the NON-ADJACENT skip (no epoch binding; the trust-OVERLAP threshold
  `tn·ttot < td·tsp` in its place, plus the same strict `> 2/3`).
  `tmSkip_height_disjoint_from_adjacent` is what makes "every header reaches exactly one gate" a
  theorem rather than a hope.
* ⚠ `Dregg2.Bridge.LightClientEthGate` / `LightClientMptGate` **NO LONGER BELONG IN §1.5** — they
  have callers (`eth-lightclient`'s `verified_gate.rs` and `evm.rs`) and are listed in §1.3. They
  were callerless when this section was written and the text outlived it; corrected 2026-07-28.
  `LightClientEthGate` now carries TWO exports: `dregg_eth_lc_verify` (may the client follow the
  CHAIN) and `dregg_eth_committee_rotation` (may it change WHOSE SIGNATURES IT TRUSTS).
  `eth-lightclient::verify_committee_update` decided the second in hand-written Rust until
  2026-07-28, on a path (`store::bootstrap_committee`) that mutates the trusted committee with no
  archive involved.
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

## §4 — The interchain light-client gates: FOUR dark layers, all CLOSED (`b5081491a`)

⚠ **This section described an OPEN wound and outlived it by three days.** It was read at face
value on 2026-07-28 and re-reported as a live defect ("`dregg_eth_lc_verify_str` is DEFINED
NOWHERE, so the ETH relayer runs un-gated"), costing an audit lane its first hour. The text below
is now the *record of the repair*, with the file:line of each closure, so the next reader can
check HEAD rather than re-derive the alarm. **If you are about to cite this section as a defect,
you are citing history.**

The three interchain light-client gates were dark end to end. The commit found FOUR independent
layers, not the three this section originally named — any ONE of which kept the ETH relayer
running with its verification gate compiled out, green and silent:

1. **archive facet** — `Dregg2.Bridge.LightClient{Eth,Mpt,Tendermint}Gate` were absent from
   `build.rs`'s target list, so no `:c` facet was emitted and `dregg_{eth,mpt,tm}_lc_verify` were
   the only Lean exports missing from the built archive. CLOSED by rooting the build on *this*
   file's import closure (§1.5 — that is what those otherwise-callerless imports are for).
2. **the cfg was never declared or set** — CLOSED: `dregg-lean-ffi/build.rs:2094-2096`
   (`rustc-check-cfg` for all three) and `:2978-2995` (three `archive_exports` probes that emit
   `rustc-cfg=dregg_{eth,tm,mpt}_lc_verify_present`, `absent_export_warn` on a miss).
3. **the C shim was declared and called but defined nowhere** — CLOSED:
   `dregg-lean-ffi/src/lean_init.c:1072` (`dregg_eth_lc_verify_str`), `:1098` (`tm`), `:1124`
   (`mpt`), each under the matching `#ifdef DREGG_*_LC_VERIFY` that `build.rs:3203-3211`
   `shim.define`s. The `extern lean_object *` declarations are at `:489-495`.
4. **NOT PREVIOUSLY KNOWN: `bridge_lc_ffi.rs` was in no `mod` declaration anywhere in the repo.**
   rustc never compiled a byte of it, so `cargo test --lib -- bridge_lc_ffi` matched 0 of 24 tests
   and reported green. Strictly worse than the cfg holes it sat behind: a cfg-gated module at
   least compiles its absent arm; an undeclared file has no arms at all. CLOSED by
   `dregg-lean-ffi/src/lib.rs:46`'s `pub mod bridge_lc_ffi;`.

**A FIFTH layer, found 2026-07-28 and closed the same day.** The three gates above were the ones
that *existed*. `eth-lightclient::verify_committee_update` — the decision that installs the
trusted sync committee, i.e. the ETH light client's whole trust root — had no gate to be dark
behind: it was a hand-written Rust rule (`branch.len() ∈ {5,6}` `&&` a SHA-256 fold), reachable
from `store::bootstrap_committee`, mutating the trusted committee with no archive involved. The
verify gate was honest and there was a DOOR BESIDE IT. CLOSED by `committeeRotationDecision` +
`@[export] dregg_eth_committee_rotation` in `LightClientEthGate`, with
`committeeRotationDecision_refines` (`rfl`) and `committeeRotationDecision_binding` (one beacon
state root commits ONE next committee, given the CR carrier).

**What keeps it closed** (the layer that matters — a repair is not a gate): all four ETH/MPT/TM
symbols are on `build.rs`'s `REQUIRED_DECISION_EXPORTS`, so a strict build
(`DREGG_REQUIRE_VERIFIED_EXPORTS=1` / release / `DREGG_TEST_REQUIRE_LEAN=1`) cannot re-enter the
dark state quietly; and `bridge_lc_ffi.rs`'s three `*_gate_refuses_*_through_the_real_ffi` tests
are **ungated** (four now, with `committee_rotation_gate_discriminates_through_the_real_ffi`) —
they route archive-absence through `demand_lean`, which PANICS under
`DREGG_TEST_REQUIRE_LEAN=1`, rather than ceasing to exist the way a `#[cfg(…_present)]` test
module does. Each carries a non-constancy canary (two wires differing in ONE field across the
decision boundary must not agree), so a gate that has degenerated to always-accept,
always-reject, or always-`"ERR"` fails there.
-/
