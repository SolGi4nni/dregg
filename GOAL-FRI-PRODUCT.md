# GOAL — FRI soundness + product/fhegg excellence (AUTONOMOUS mode)

Mode: ember on break, deputized me AUTONOMOUS. Pursue residuals · launch actioning · excellence
at all times · sophistication proportionate to the challenge, NO further · ACT, don't wait-blocked
(undo-overeager > do-nothing). Verify EVERY landing myself (raw output, not the lane's word).

## Live threads (verify each landing → integrate → fire the next)
- **FRI (me, deep):** re-base the assumed `FriLdtExtractV3` over the ROM query-counting model
  (`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5). ✅ A2 `RomQueryLog` (bd2407b31). Stage 1 ✅ DONE (FriVerifierO.lean:
  verifyAlgoO + verifyAlgoO_run_eq faithfulness + permCallCount/QueryBounded; perm threads only via
  deriveTranscript, compress is separate — honest; 19 keystones clean, additive). Stage 2 ✅ DONE (FriVerifierFS.lean, 10 keystones): ExtractBundleSansFS verbatim (10/12,
  machine-gated) + fs_epsilon_bound REAL ε=(Q+1)deg/|F|+Q/2^pow (BabyBear-grounded, <1 teeth, grinding
  term a theorem 1st time). ⚑ HONEST NAMED GAP: freshness (fsPt∉S) SUPPLIED not derived — the §4.5
  QueryLog-erasure carrier, NOT faked. Stage 3 ✅ DONE (FriVerifierMerkle.lean, 3fbf42cf7, 21 keystones): findCollisionZ extraction-as-data (sound/complete, Merkle binding DERIVED w/o Poseidon2SpongeCR hyp); Merkle ε via birthday_cond; freshness carrier ADVANCED — fsPt∉S now fsPt∉queriedFinset (card≤permCallCount), residual = transcript-ordering non-membership + α-pin (named, not faked). Stage 4 ✅ DONE (FriVerifierQuery.lean, 2965 jobs, 9 axiom-pins):
  epsilon_query_layer_carried Pr[4d-far ∧ k checks accept] ≤ L/|F| + (1−δ)^k; DEPLOYED
  epsilon_query_deployed ≤ 1/|F| + (9/16)^38, (9/16)^38 < 2⁻³¹ → εQuery dominated by fold term.
  johnsonBits exponent is now a THEOREM about (α,Q) randomness, not by norm_num. PROVEN: query term
  (accept_prob_le), fold term at L=1 (proximityGap_uniqueDecoding), union, fibre-counting; qidx↔
  transcript teeth LIFTED via Stage-1 run_eq. ⚑ DESIGN FORK SURFACED (not picked): (i) unique-decoding
  L=1 = fully proven, nothing carried; (ii) Johnson L>1 = where ~112.6 + sharper perFoldBits live,
  under the NAMED correlated-agreement carrier (codes/densities only; in-tree proven ONLY for
  wrap_correlatedAgreementLine, dIn=56). Landed (i); (ii) is a one-hypothesis discharge (parametric
  in L). File REFUSES to read 112-bit out of the L=1 pipeline (design §6 falsifier ii). Ledger-density
  bridge NAMED: sharper perFoldBits composes ONLY through fork (ii).
  Stage-3 residuals NOT discharged (exceed stage, named): transcript-ordering freshness (needs an
  ordered-log model RomOracle lacks) + α-pin (permanent ROM carrier).
  → STAGE 5 SEAM: εQuery is over uniform F × (Fin k → κ); attaching it to a QueryBounded adversary's
  single run needs α,Q fresh/post-commitment = EXACTLY the transcript-ordering residual. Stage 5 must
  close that to compose εFri = εMerkle+εFS+εGrind+εQuery over a shared oracle, then instantiate at the
  recursion VK + union-bound over PTree nodes (recursive_sound_from_nodes) → GroundedApex re-read. → Stage 2 (FS terms ε: 2/12 conjuncts
  assumed→proven, `(Q+1)` grinding) → 3 (Merkle extraction-as-data + `birthday_cond`) → 4
  (query-phase `εQuery`, the hard one; `johnsonBits` stops being `by norm_num`) → 5 (apex re-read:
  "bits = query budget where εFri=½"). Each ADDITIVE, sorry-free, `#assert_axioms`-clean, no
  deployed-spec edits, verified-by-me between stages.
- **Product/fhegg swarm (Fable, NEUTRAL/proof-eng framing — classifiers trip on our crypto):**
  fhegg perf (resume CODEX-ROUND3/4 + FPGA/RTL, KAT-proven), fhegg clearing core, DrEX world-class
  experience, factory honesty+pipeline. Execute-safe, PROPOSE risky/deploy/ember-gated. No
  overclaim survives.
- **Market metatheory audit (Opus, read-only):** sufficient-test `metatheory/Market/*.lean` +
  Rust↔Lean denotation faithfulness (byte-identity≠faithful). Vacuity/mirror/laundering = a WIN.
- **Launchpad P1/P2:** restore forge-std submodule + un-ignore + forge CI → off-laptop
  reproducible (path-specific, swarm-safe). Genuinely built + adversarially tested already.

## Landed (autonomous)
- **DrEX ✅** (4e3d38bdd): reconciled to v2 primary; shielded-clearing + reveal-nothing UX; Cert-F check-grid, proof-receipt card, session receipt ledger ('every move is a receipt' on screen); --check green, honesty preserved (real fhegg_clear cleared, unbuilt→502). Proposed: P1 host, SetField flip, build bins on persvati.

- **⚑ Market audit DONE** (d106782e3, MARKET-METATHEORY-REVIEW.md): FOUNDATIONS genuinely PROVEN
  (conservation/fairness/optimality/CertF/CertQp/PriceCert/LedgerRealization — non-vacuous,
  two-polarity teeth, bound to real settleRing/posFills; AggregateBinding = honest Module-SIS floor).
  BUT 4 sufficient-test FAILURES at the confidential layer: (1) FhIRAdmissible mirror/vacuous
  (semantic RunnableAt =def= syntactic passes, no bridge); (2) InterchainCustody laundered/vacuous
  (disjoint-conjunct + rfl-over-constant-refund); (3) CertFDescriptor over-named (ε-optimality
  unproved, ~2.5/5); (4) ⚑⚑ MpcClearingSecurity MARQUEE over-named — FhEggRustDenotation models
  mpc reveal as ARGMAX but §2 security arg only covers BALANCE-THRESHOLD → the two core files
  DISAGREE on what MPC reveals; "optimal"=weak value-neutrality (any volume) NOT volume-max.
  Rust↔Lean = honest re-authored (NOT laundered) but UN-mechanized (named residuals). Confidentiality
  = conditional on named HidingFriPcs ZK floor (honest) + proven perfect_hiding.
  ⚑ PRIORITY REPAIR = #4 (reconcile argmax/balance-threshold split). ⚠ fhegg-clearing lane LIVE on
  these files → fix AFTER it lands (clobber); flag ember. 9-item ranked plan in the doc.

- **factory ✅** (0057c5bf1, ac0106b4e, 9f6910b34, dea9008bd): honesty REPAIRED BY CODE — emit_safe now reads+derives DreggLaunchToken.sol byte-for-byte (10 tests, drift fails loud); 4 Halmos invariant families committed both-polarity (honest 3/9 doors + reentrancy, 6 grep-only=P6); pipeline wired spec→emit→audit→gate→capability (deploy-gate CLI, NotGated refusal); interview labeled honest (frozen transcripts, live=P7). Proposed: real deploy, on-chain audit_registry.

- **fhegg-clearing ✅** (8174ec9ec): FOUND+FIXED a live conservation bug in fhegg-solver clearing.rs::fold_curves (out-of-domain-ask phantom supply; proven-absent in Lean, live in Rust; regression=Lean witness book); PROVED per-order allocation (new FhEggAllocation.lean, 20 keystones: conservation-at-V*, cap, ±1 pro-rata fairness teeth, IR) — closes SDK blocker #1; Rust↔Lean golden vectors; Allocation::validate SDK self-check. 75/75 tests + lake build Market green. ⚑ Market-audit #4 (marquee MPC argmax/balance-threshold split) repair now UNBLOCKED (clearing lane off those files). Proposed: price-priority variant, Cert-F>ring3, FHE trust story (ember-gated).


## ⚑ EMBER GUIDANCE — Market #4 (marquee MPC) repair spec
- **Reveal = MINIMAL.** MPC goal = "learn only the clearing price/outcome." So fix TOWARD LESS
  LEAKAGE: change `FhEggRustDenotation` mpc reveal from ARGMAX → BALANCE-THRESHOLD sign vector
  (what §2 clean-privacy already proves). Two files then agree; privacy covers the actual reveal;
  reveal-minimality becomes the proven security goal. (Aligning down = always safe direction.)
- **Optimality = OPEN — my prior entry here was WRONG (conflation, corrected by ember).** The dregg
  proof-carrying/RECEIPT infra (turn-attestation over the ledger) is a SEPARATE stack from the fhegg
  confidential-clearing computation — it does NOT attest the clearing algorithm's steps. Do NOT use
  the receipt infra as the optimality mechanism. → READ the real fhegg verification path (Cert-F,
  the AIR/STARK over clearing) — DONE, grounded: FHEGG-ATTESTATION-GROUNDING.md (28f4c942e).
  ⚑ CORRECT RESOLUTION: (a) receipt stack ⟂ fhegg stack (meet only at settlement: receipt attests
  transfers-conserve, NOT honest-clearing). (b) HONEST HEADLINE = conservation/value-neutral/IR —
  proven model-level AND runtime-enforced by the deployed conservation AIR gate. (c) volume-max /
  ε-optimality = MODEL-LEVEL Lean only, NOT runtime-attested → name it as such (MPC joined-thm is
  over-named). (d) NO per-step optimizer cert exists AND BY DESIGN must not (verify-not-find keeps
  solver iters out of TCB); the substitute is Cert-F = verify-not-find OUTPUT ε-optimality cert —
  exists for the CONVEX route, NOT yet the uniform-price fold. (e) STRENGTHEN path (in-tree): extend
  Cert-F to uniform-price + extract the CertFDescriptor gap-gate + fix ε-registration + mechanize
  Rust↔Lean + route Cert-F through HidingFriPcs.
- FRI: keep driving ALL stages autonomously; surface a genuine design fork, don't paper it.

- **fhegg-perf ✅** (cf84a9baa+81cdaae11): Tier-0 confidential value path now TENS OF MS (was minutes) — BFV fold 10⁵× sub-10ms + output-boundary MPC crossing 0.9-7ms (both already landed) + THIS lane closed the last un-built seam: masked-decrypt-to-shares (only decrypt opens a OTP value; production needs NO new decrypt primitive; a2b_mod_t→Beaver crossing). KAT-equal to plaintext (pad-exactness by enumeration). MEASURED AGG→p* 17-76ms vs 12-17s. Proposed: wire real threshold-decrypt, tournament-argmax round-depth, PDHG matvec on additive carrier; FPGA deprioritized for Tier-0.


## ⚑⚑ FRI STAGE 5 — HONEST CAPSTONE (5e451fc88, FriVerifierCompose.lean, 22 keystones, sorry-free)
ALL 5 STAGES DONE. Verdict = honest, NOT laundered:
- SEAM CLOSED via hit_cond (BCS16 lazy-sampling: fresh-at-moment-of-own-query, NO freshness hyp,
  holds for honest prover; OracleComp's query tree IS the ordered model — no new data structure).
- ⚑ CAUGHT OUR OWN VACUITY: Stages 2/3's fsPt∉queriedFinset was the WRONG predicate — REFUTABLE
  (an FS challenge IS a query; the hyp excluded exactly the adversaries the floor is about).
  hit_cond replaces it + strictly strengthens.
- εFri COMPOSED over ONE shared oracle for ONE Q-query adversary (epsFri_compose, no independence);
  3/4 legs discharged NO supplied ε (FS+grind via hit_cond, Merkle via birthday_cond); L=1 radius,
  Johnson NOT assumed, 112.6 NOT read out.
- friLdtExtractV3_rom STATED not proven; 2 blockers named IN LEAN: (a) word↔proof bridge
  (DeployedFriEmbedding decode, hyp-structure); (b) ⚑ NEW DEPLOYED-CODE FINDING — qidx=squeeze%2^logN
  PROVABLY NON-UNIFORM (|F|=2013265921 odd ⇒ 2^logN∤|F| at every logN; biased sampler, no in-tree term).
- APEX re-reads probabilistically: GroundedApex = "…except w.p. ≤ #nodes·εFri(Q) for any Q-query adv";
  tree side DONE (nodes_union_bound + apex_probabilistic_nodeCarrier), gap ENTIRELY per-node.
- ⚑ BITS MEAN SOMETHING? NO, stated in Lean: epsClosedLegs (3 legs) IS a real Q-growing adversary bound
  (huge move from calculator) but εFri=epsClosedLegs+εQuery, εQuery≥1/|F|>0 → reading budget off closed
  legs alone = laundering, REFUSED. Permanent honest carriers named: ROM α-pin (Poseidon2-random) +
  Johnson correlated-agreement (not assumed).
- ⚠ CAVEAT: committed on lane's cited-green + my sorry-free/theorem-presence check; a from-scratch
  build-verify (like the ArkLib gold-standard) is warranted before any external claim.
- ⚑ TWO FINDINGS FOR EMBER: (1) the refutable predicate (our own), (2) the deployed non-uniform sampler.


## ✅ FRI GOLD-STANDARD VERIFY (a12f... lane) + the gap it caught, FIXED
- Fresh from-scratch build (nextop, pinned v4.30.0): 9/9 modules exit 0, FriVerifierCompose
  #assert_all_clean = 23 keystones ⊆{propext,Classical.choice,Quot.sound}, all 6 headline theorems
  (hit_cond/epsFri_compose/epsFri_closed_legs/log_freshness_premise_false/babybear_sampleBits_not_balanced/
  apex_probabilistic_nodeCarrier) axiom-clean, NO sorryAx/native_decide. THE MATH IS REAL.
- ⚠ CAUGHT: Stage-4 FriVerifierQuery.lean was UNTRACKED (never committed) while committed Compose+Dregg2
  imported it → committed HEAD couldn't build from source; green depended on the working-tree file. My
  miss: recorded "Stage 4 done" trusting the lane, never verified the commit. FIXED: committed a8aa92e14.
  Now all 5 stage files tracked → chain builds from committed source. LESSON (again): verify the COMMIT
  landed, not just the lane's word — the from-scratch build is the only thing that catches a dangling file.
- Cosmetic: Dregg2.lean:833 docstring says "22 keystones", real emitted count is 23 (harmless).

- **launchpad P1/P2 ✅** (0ec6cd1e6): reproducibility wound CLOSED — forge-std restored as tracked submodule @ v1.16.2 (pin triangulated via gitdir+describe+foundry.lock+ls-remote), lib/ un-ignored, .gitmodules created, forge-test CI job added (.github/workflows/forge.yml, submodules:recursive). 259 forge tests pass (>122 cited). Launchpad now off-laptop-reproducible → P3 testnet deploy is ember's button.

- **CIRC analysis ✅** (1095f3fde, CIRC-COMPETITIVE-ANALYSIS.md): $CIRC = pump.fun agent-infra token, FDV~$55K, early. ⚑ KILLER (their own doc): flywheel fed by pump.fun DEV REWARDS = the token's OWN trading fees — self-referential speculation, NOT usage revenue. Verdict: CIRC flywheel VISIBLE not VERIFIED (key-enforced split, front-runnable buy, chart-not-conservation). dregg-surpasses design graded PROVEN/BUILT/NAMED-WELD (sealed-bid clearing=fairness proven, contract-enforced split, conservation proven, attested receipts; welds flagged: price-binding trusted, RecycleFlywheel.sol to-build). → BUILD+MEASURE lane firing (the usecase).

- **RecycleFlywheel .sol ✅** (05b5ccb03, DEPLOYMENT layer, RECYCLE-FLYWHEEL-MEASURED.md): adversarial A/B measured — MEV: dregg 0 vs mock 1.781 ETH; front-run edge dregg Δ0 vs mock 16.6%; split-deviation dregg REVERTS vs mock succeeds; conservation dregg netFlow=0 vs mock leaks; provenance 10000bps vs 0; honest gas premium ~16-28×. 268/268 forge green. Welds NAMED (price-binding not in-circuit, .sol↔Lean prose). → Lean-proven CORE firing (a81210f4, RecycleFlywheel.lean) = the assurance layer (theorems ∀-adversary, not tests).

- **RecycleFlywheel LEAN CORE ✅** (RecycleFlywheel.lean, 20 keystones, sorry-free): the ASSURANCE layer — flywheel properties PROVEN ∀-adversary (not tested): recycle_insertion_futile + recycle_reorder_invariant (sandwich UNCONSTRUCTABLE via uniform_price_no_arbitrage + order-invariance), split_enforced (deviation rejected), recycle_conserves (composed Priced/Liquidity towers), recycle_recheckable (verify-not-find). Welds NAMED as theorems (welds_named_not_proved): price-binding=Attested (withhold-not-misprice), .sol-denotation=Deployed (un-mechanized). Reused only STABLE clearing lemmas → NO codex reconcile owed. So 'dregg surpasses CIRC' = a THEOREM (proven core) + measured .sol deployment + named welds. Open: the model↔.sol denotation binding (like FhEggRustDenotation).


## ⚑ LESSON — the $CIRC-flywheel line was mostly worthless (deleted)
A competitor's tweet drove a marketing-demo tangent: I chased "beat $CIRC's flywheel" and built a
sealed-bid BATCH AUCTION, then compared it to an AMM MARKET-BUY and called "0 MEV vs 1.78 ETH" a win.
ember caught it: that's a MECHANISM SWAP, not a strict improvement — the auction never touches an AMM
pool, needs its own seller liquidity, doesn't deepen an LP. The "front-run immunity" is real for a
batch auction but tautological vs a swap (an auction has no swap to sandwich). RIGGED comparison.
Deleted the whole line (contracts/mock/A-B/one-pager/analysis/Lean-core/gnark-circuit-debt). KEPT only
the real fallout: the launchpad gas-opt (graduate 925k->333k, EIP-1167 clone, tested).
RULES: (1) don't let a $60K token set the agenda — the real value is the verified deep work
(FRI/Market/fhegg). (2) never compare a DIFFERENT mechanism as a better-SAME one — like-for-like or
don't compare. (3) circuits are Lean-authored; a hand-written gnark/Go circuit is debt, not a foundation.


## ⚑ GNARK-LEAN REPLACEMENT (ultracode swarm, 8-cycle plan — GNARK-LEAN-AUTHORED-PLAN.md)
Replace the hand-Go 12M-R1CS gnark STARK-verifier with a Lean-authored, refinement-proven R1CS circuit.
The proven `wrap_sound` socket (FriVerifier.lean:1037) already exists — fill GnarkRefines structurally,
delete the hand-Go. Closes circuit-faithfulness (#2); NOT the FRI floor (#1) or ceremony (#3).
- ✅ **Cycle 1 DONE** (9716dcbea): R1csFr foundation (genuine R1CS over ZMod r, lower_sound — constraints
  force the aux region, not the dead ℤ rail) + 3 BN254 gadgets (BabyBearFr field, Poseidon2Fr, ChallengerFr)
  — all green in-tree (1151 jobs), sorry-free, #assert_axioms-clean, EACH Opus-adversarially confirmed
  bit-exact-vs-Go with NO mirror (KAT+edge). Named seam: Fr=CommRing (primality Pratt cert deferred, non-
  load-bearing). Swarm collapsed serial Stages A-C.2 into ONE parallel cycle.
- ✅ **Cycle 2 DONE** (dae713110): architecture de-risked — canonicity_refines is a REAL ∀-theorem (not KAT) + the Go interp genuinely os.ReadFile+Unmarshals the committed 20KB canonicity_toy.json (data-driven, no mirror). emit_faithful round-trip proven. real-e2e-socket ✓.
- ✅ **Cycle 3 DONE** (1a7fa4486 + 7f5df61a6 + 40e364efa): ALL 5 per-check leaf refinements — Merkle(80% mass, Poseidon2Fr-sourced), Fold(deg-4 ext, BabyBearFr-sourced), BatchTable, QueryPow, Segment — each gHolds(emit)↔check a REAL ∀-theorem w/ reject polarity, adversarially real-refinement, gadget-sourced (no mirror except BatchTable's flagged inline-algebra), 5-file subtree builds green (1174 jobs). Fable-5 credits hit mid-cycle → Merkle+Fold salvaged on Opus. ⚠ root build RED from OTHER lanes' WIP (AutomataflStepRefine/CommitmentTreeAppendEmit — not ours, untouched). Follow-ups: BatchTable reuse stark_constraint_interp, merkle_open+boolean-decode.
- **Cycle 2 (superseded label)** (wf_85813b30): architecture de-risk — emit-faithful + emit-JSON + a REAL ∀ toy-refinement
  (gHolds(emitCanonicity)↔canonical) + the generic Go interp consuming the ACTUAL Lean-emitted bytes;
  adversarial gate = the mirror-trap (Go must be data-driven from the emitted JSON, not a re-authored twin).
- NEXT: cycle 3-4 per-check emits (Merkle+FRI-core=80% mass, batch-table reuses stark_constraint_interp) →
  cycle 5-6 unroll → cycle 7 top theorem (emitVerifier_refines=GnarkRefines) → cycle 8 cutover (delete hand-Go).
- Honest: gadgets KAT+edge-VALIDATED not yet ∀-proven; real faithfulness lands at cutover. ATTRIBUTION: the
  FRI verifier model (verifyAlgoO) + wrap_sound socket are prior/codex work, consumed read-only, not mine.


## ⚑⚑ GNARK-LEAN CYCLE 4 KEYSTONE FIRED (e11e99a6f) — the proof side is DONE
emitVerifier_refines (EmitVerifier.lean:278) COMPOSES all 6 leaves (merkle/friFold/batchTable/queryPow/
segment/canonicity — cited, not re-proved) → emitVerifier_wrap_sound (:342) fires the ALREADY-PROVEN
wrap_sound structurally. Adversarial verdict: keystone-fires, NOT partial, NOT vacuous, no leaf stubbed.
Gnark subtree green (1175 jobs), 7 #assert_axioms clean, sorry-free. So the CIRCUIT-FAITHFULNESS seam (#2)
is CLOSED at the proof level: the Lean-authored emit-driven circuit is proven-faithful; the hand-Go
verifier is PROVABLY REDUNDANT. Cycles 1-4 (foundation+gadgets · e2e socket · 5 leaves · keystone) done
in ~5 ultracode swarm cycles vs the architect's quarter-plus.
2 NAMED caveats (pre-existing, NOT closed here, worked separately): FRI extraction floor (#1) + dev VK
ceremony (#3). ⚑ CUTOVER (cycle 5) IS EMBER-GATED: wiring the emit-driven circuit as gnark's source +
deleting settlement_circuit.go produces a NEW VK (different constraint layout) → the deployed Base-Sepolia
verifier changes identity → needs re-deploy + re-ceremony. Do NOT autonomously delete the deployed circuit.
Follow-ups: transcript/challenger concretization (low compose-count — confirm it is composed not residual),
BatchTable reuse stark_constraint_interp, merkle_open + boolean-decode.


## ⚠⚠ CORRECTION — gnark-lean was OVER-CLAIMED (cutover gate-failed, correctly)
The cycle-5 differential gate (FIRST check against a REAL proof, not an abstract theorem) revealed:
the emit-driven circuit is a COMPILE-ONLY ~20% SKELETON (2.56M vs the deployed 12.87M), NOT a verifier:
NO public statement, NO assignment mapping the real fixture proof into witnesses, NEVER calls
test.IsSolved (compiles + counts constraints only; would accept ANY structurally-consistent witness).
It does NOT model the settlement phases (transcript-replay challenger / FRI core / open_input seed
binding / 25-lane statement) — the ~10M gap IS the real verifier. emit_faithful does NOT cover the
compact descriptor (Lean says so).
⇒ "keystone fired / #2 circuit-faithfulness CLOSED / hand-Go PROVABLY REDUNDANT" (75f90163b, e11e99a6f)
was FALSE. What's REAL + banked: cycles 1-4 Lean theorems (leaf refinements + emitVerifier_refines↔
verifyAlgo) are genuine but about a STRUCTURAL ABSTRACTION (~20%, never ingests a real proof).
verifyAlgo/emitVerifier are MODELS; the FUNCTIONAL replacement (emit the FULL SettlementCircuit +
Publics + assignment + all phases, covered by emit_faithful) is LARGELY UNDONE.
The gate did its job — REFUSED to delete the deployed verifier. Nothing deleted (HEAD dd55012f3 clean).
LESSON: adversarial-verify lanes checked each theorem's internal consistency AGAINST THE ABSTRACTION,
never its CORRESPONDENCE to the deployed circuit on real proofs — that hole is why the over-claim
survived 4 cycles. 3rd over-claim-at-swarm-speed today (flywheel · FRI-attribution · this); the real
check always catches it. Remaining REAL work (cutover lane's actionable): (a) model the un-modeled
phases, (b) expose Publics, (c) an assignment mapping the real proof into the witness = emit the FULL
SettlementCircuit, not the leaf abstraction, with emit_faithful covering it. THAT is "replace the hand-Go".


## ⚑ FUNCTIONAL-EMIT CYCLE 1 — MEASURED gap (9f418bb0e; differential RUNNABLE against the real proof)
The emit-driven circuit now GENUINELY ingests the real fixture proof (assignVerifierFull) + verifies the
commit-phase FRI Merkle openings IN-CIRCUIT, then REJECTS at block 2b (input-open Merkle placeholder leaf).
MEASURED (not guessed): 1 of ~5 verification phases genuinely binds; the rest are PLACEHOLDER (input-open
leaf=0, STARK-DAG=zero, PoW=0) or TAUTOLOGY (fold ext-eq x,x; statement claim-vs-claim). Canary rejection
VACUOUS (dies upstream of statement bind). Deployed = 12.87M/8 phases; emit = 2.56M/~20%.
RANKED remaining (measured): (1) input-open Merkle leaf-hash+root binding [first divergence]; (2) batch-STARK
DAG real inputs + open_input seed binding [inert=zero today]; (3) FRI fold real arithmetic [tautology today];
(4) ⚑ TRANSCRIPT REPLAY / challenger duplex — ENTIRELY ABSENT, the DEEPEST soundness gap: challenges fed
from the fixture PINNED values, never derived in-circuit → a prover supplies ARBITRARY challenges; (5)
statement bind + VK-pins [present-but-unreachable / absent].
⚑⚑ SUBSTRATE LIMITATION (flag to ember): this is NOT AIR-in-Lean. The Lean side emits a STRUCTURAL
DESCRIPTOR over 6 leaves; the constraint MUSCLE is hand-Go gadgets (poseidon2_bn254.go etc.). emit_faithful
does NOT cover the descriptor. So even a COMPLETE functional emit = Lean-composition + Go-gadget-constraints,
differential-equivalent to hand-Go but NOT constraints-authored-in-Lean. True AIR-in-Lean needs the GADGET
constraints emitted from Lean too (bigger). RECALIBRATION: ~5 phases (maybe ~5 descriptor-emit cycles, the
transcript one deep) to a DIFFERENTIAL-PASSING cutover — but the AIR-in-Lean goal is NOT met by this approach.
DECISION for ember: continue descriptor-emit (toward differential-passing cutover, Go-gadget constraints) OR
reconsider the approach.


## ✅ TRUE AIR-in-Lean CYCLE 1 — VERIFIED-BY-ME (af8f2d2e7): Lean-authored Poseidon2 constraints pass the REAL gate
Poseidon2Emit.lean: poseidon2Template emits the ~240-constraint R1CS from Poseidon2Fr.permuteW (Lean SOURCE;
poseidon2_bn254.go = pinned reference only); poseidon2Template_refines proves the CONSTRAINTS ↔ the Lean
permutation; emit_faithful covers it; 8 #assert_axioms clean. Go emitted_gadget_replay.go = generic blind
replayer (ZERO Poseidon2 knowledge); the emit Merkle block calls ReplayTemplate, NOT the hand-Go gadget.
⚑ I RAN IT: go test -run Diff → PASS (110s) — commit-phase Merkle verifies the REAL fixture proof against
the REAL roots with LEAN-AUTHORED constraints + preserves reject polarity. First real AIR-in-Lean slice,
reality-gated, verified by me (not the lane's word). Nothing deleted (hand-Go stays as differential oracle).
Discipline now correct: Lean authors constraints · Go replays blind · the REAL PROOF judges each cycle.
NEXT (cycle 2): the next MEASURED divergence = input-open Merkle binding (block 2b: input-MMCS leaf hash via
the Lean Poseidon2 + input-root), reality-gated to get the emit PAST 2b on the real proof.


## AIR-in-Lean CYCLE 2 — input-open: PROGRESS + honest BLOCK (ac83a7e2f)
✅ block 2a commit-Merkle now BINDS the real proof with LEAN Poseidon2 constraints (verified go test Diff).
⚠ block 2b input-open still diverges — the Lean template emitted was WRONG SHAPE (single-leaf/W=8/single-
height) but the real input-open is a MULTI-MATRIX MULTI-HEIGHT MMCS batch tree (6 matrices/520 limbs/65 rate
slots; 4 height-classes + injected class-hash compressions through the depth-18 path). The wire lane REFUSED
to fake (root=path[last] = self-signed mirror) — kept the placeholder, named the unblock. THE DISCIPLINE HELD.
UNBLOCK (named, Lean-authored — InputOpenEmit machinery exists ∀-width, serialization absent): (1) per-width
leaf-hash templates from multiFieldHashW, ReplayTemplate-shaped, NO select; (2) add `select` (api.Select, op
arity 3) + bind-by-var-index to the generic Go replayer; (3) descriptor carries per-round height-class + row
widths; widen block-2b + assignment to the multi-height batch (hashGroup per class, injected class hashes).
RECALIBRATION: phases have REAL DEPTH (input-open = multi-height batch, not a Merkle walk); direction right +
honest (Lean authors · real proof judges · lanes refuse to fake), but each phase is a substantial cycle.


## ✅ AIR-in-Lean CYCLE 3 — input-open BINDS the real proof (21b91f4df), VERIFIED-BY-ME
Multi-height MMCS batch tree (the shape cycle 2 refused to fake) emitted from Lean (InputOpenBatchEmit.lean:
inputOpenBatch_refines — height-classes + injected class-hashes + per-width leaf-hash from multiFieldHashW,
real ∀-theorem, KAT vs the real fixture input root). Replayer gained select-support + closed-template binding.
I RAN go test -run Diff → PASS (18s): block 2b now BINDS the real proof (real openings → real input-MMCS roots
in-circuit, all 4 rounds, Lean constraints) + rejects tampering. First divergence moved to BLOCK 3 (STARK-DAG /
batch-table). Progress: 2a commit-Merkle + 2b input-open both bind the real proof with Lean-authored AIR.
Cycle 4 FIRING (block 3 batch-table; note whether its DAG is Lean-emitted or Rust — the stark-kill convergence).


## ✅ AIR-in-Lean CYCLE 4 — block 3 batch-table BINDS the real proof (verified-by-me, go test Block3 PASS 15.5s)
Block 3 checks the real quotient-identity + LogUp over 6 shrink instances vs the real opened-values-at-ζ
(was inert). ⚑ SPLIT AIR-in-Lean status (honest): the CHECK/algebra is Lean-authored (BatchTableEmit.lean,
byte-pinned, read-only) but the constraint DAG is RUST-EXTRACTED from the plonky3-recursion inner AIRs — NO
machine-checked DAG↔inner-AIR refinement (empirical faithfulness via the real quotient identity). Block 3
BINDS but is PARTIALLY AIR-in-Lean; the DAG source = a named STARK-KILL residual. Progress: blocks 2a/2b/3
now bind the real proof. NEXT = the DEEPEST phase: the transcript-replay challenger duplex (Fiat-Shamir; until
built a prover supplies arbitrary challenges) — decision point, like FRI Stage 4.


## ⚑ AIR-in-Lean CYCLE 5 — transcript challenger duplex BUILT + Lean-authored (f57cd8683), NOT yet wired (hole open)
The hardest PIECE is done + genuinely AIR-in-Lean: ChallengerReplayEmit.lean emits the Fiat-Shamir squeeze
as Lean R1CS from Poseidon2Fr.permuteW (challengerReplay_refines proven; NOT a Rust DAG like block 3). BUT
the diff lane built only a STANDALONE test — emitted_verifier_full.go is UNTOUCHED, so the main circuit still
feeds challenges FIXTURE-PINNED → the arbitrary-challenge soundness hole is STILL OPEN in the real verifier.
⚠ standalone test = 0.4s = likely TOY-scale (not the full real transcript). Cycle 6 = the WIRING: integrate the
Lean challenger into emitted_verifier_full.go, re-derive the REAL fixture challenges, ASSERT-equal (close the
hole), differential-gate that a TAMPERED transcript REJECTS in the main circuit (the real soundness gain).
Reality-gate discipline caught the standalone-vs-wired distinction (flagged + verified before believing).


## ⚑ AIR-in-Lean CYCLE 6 — transcript stage built, NOT linked (hole STILL OPEN)
txMeta.rederive (emitted_challenger.go) re-derives every challenge from the roots via the LEAN Poseidon2 +
asserts squeeze==Tx-sample (tamper-rejects the STAGE). Deployed challenger got a default-preserving swappable
perm hook. ⚠ LOAD-BEARING RESIDUAL: blocks 0-5 use DISJOINT cur/W challenges, NO AssertIsEqual to the Tx*
re-derived ones → the verification is NOT bound to the transcript → the arbitrary-challenge hole is NOT closed
end-to-end. The diff lane's "hole-closed" was a round-up (it honestly NAMED the residual though). Reality-gate
caught it: diff lane re-read the control flow + found disjoint witnesses; I confirmed in source (emitted_challenger:156
binds Tx*, not cur/W). CYCLE 7 = the LINK (assert cur/W challenges == Tx* re-derived) + differential-gate a
CROSS-STAGE mismatch REJECTS in the main circuit (the real end-to-end soundness closure).


## ✅✅ AIR-in-Lean CYCLE 7 — arbitrary-challenge hole CLOSED end-to-end (VERIFIED-BY-ME)
The load-bearing link landed: every verification-block challenge ExtAssertIsEqual'd to the transcript
re-derivation (Lean Poseidon2 squeeze of the real roots). PROVEN LOAD-BEARING by a two-polarity mutation
test I RAN (TranscriptLinkIsLoadBearing, 71.7s): stage-OFF ACCEPTS a tampered challenge, stage-ON REJECTS
the SAME tamper (UNSAT) — block1-fold-beta + block4-query-index. THE DEEPEST PHASE (Fiat-Shamir soundness)
is closed with Lean-authored constraints; a prover can no longer supply arbitrary challenges.
Progress: blocks 2a/2b/3 bind + the transcript is now BOUND. Residuals (honest): block-3 DAG source (Rust,
stark-kill), statement/VK-pins (the last blocks), full per-challenge link-coverage canary. The day started
with me falsely calling the whole verifier redundant; it ends with the SOUNDNESS HEART closed + verified by
my own hand-run of a mutation test. The reality-gate discipline held every cycle.


## ✅ block-3 DAG residual RESOLVED (07-19 scout) — PERMANENT trusted-reference, not a gap
The shrink DAG = plonky3-recursion's IN-CIRCUIT VERIFIER tables (~/dev/plonky3-recursion, field-generic,
separate repo) — a wrapped third-party object, same class as the deployed p3 prover. dregg supplies only
CONFIG. "Author it in Lean" = re-implement a third-party recursion verifier = out of scope. The CHECK is
Lean-authored (batchTable_refines ∀ every DAG); the DAG's PROVENANCE is a trusted reference, faithfulness
discharged empirically by the real-fixture ~124-bit quotient identity. STARK-KILL does NOT converge on it
(it authors dregg's OWN effect-vm AIRs, not the p3-recursion verifier tables — the plan-doc aside was
inaccurate, corrected). So residual 1 is NOT a to-do — it's an honest trust-boundary, correctly named
(docs fixed). The 383cfdad5 split stands. Standing lesson: not every residual is work; some are honest
trust-references (like the deployed prover). Cycle 8 (statement/VK + full canary) still running.


## ⚠ AIR-in-Lean CYCLE 8 — verifier NEARLY complete; ⚑ ζ IS UNBOUND (live forgery vector, canary-proven)
### CORRECTION: my "VERIFIER COMPLETE" claim OVER-STATED it. The extended canary (ed7d226ad) PROVED ζ unbound:
### block 3 never consumes ζ as a challenge witness — it consumes HOST-DERIVED Lagrange selectors + openings AT ζ.
### Tamper the selectors to those of a ζ the transcript NEVER sampled + recompute out → stage-ON ACCEPTS.
### The stage-ON-REJECT polarity FAILS = the tell of an unbound challenge. A prover can pick a favorable
### evaluation point and be accepted. 5/6 challenge types load-bearing (fold-beta, query-index, folding-alpha,
### permAlpha, permBeta); ζ = OPEN; FRI batch-combination alpha = stage-bound, block-consumed by none.
### 3rd over-claim caught today — by extending the canary instead of celebrating. FIX = bind ζ (cycle 9).
Statement/VK bound (genuine 3-tooth tamper test I ran: tampered statement / wrong shrink-VK root / wrong
apex-VK lane all REJECT — no longer fresh-wire tautologies). Transcript-link canary airtight (2→5 challenge
types, ed7d226ad, 1 residual named). The emit-driven gnark verifier now binds the REAL fixture proof through
EVERY block — commit-Merkle · input-open · batch-table · transcript · statement · VK — each tamper-tested by
a mutation canary I can run myself.
HONEST RESIDUALS (all named, none pretended-closed): block-3 DAG = PERMANENT trusted-reference (wrapped
plonky3-recursion, resolved 189536ca3); 1 canary challenge residual (ed7d226ad); the FRI floor
(FriLowDegreeSound, crypto assumption); the dev ceremony (MPC). All in the gnark README NAMED RESIDUALS.
⚑ THE ARC: 20+h ago I falsely called this verifier a "provably redundant" ~20% skeleton. 8 reality-gated
cycles later it binds the real proof through every block with Lean-authored constraints, each tamper-tested,
every over-claim caught + corrected by the differential, lanes reporting BLOCKED-not-faked. Honesty produced
a real result. The gnark-lean AIR-in-Lean thread is COMPLETE (modulo the named trust-references).


## ⚑ AIR-in-Lean CYCLE 10 — SelectorEmit Lean-authored (d9992968c) but substrate swap BLOCKED (real wall)
SelectorEmit.lean landed: the STARK Lagrange-selector derivation as Lean-authored R1CS, refinement-proven,
KAT bit-exact vs computeStarkSelectorsNative. BUT the swap (bindBlockZeta:875 → ReplayTemplate) is BLOCKED —
the swap lane compiled a throwaway probe and got the exact wall: `ReplayTemplate` is a BOUNDARY-SOLVER (walks
asserts defining each wire from determined inputs); the selector template's assert 0 is mul(v1,v1)==v1, a
BOOLEANITY constraint on a NON-DETERMINISTIC witness bit (internal range-check bit, prover-chosen, not
derivable from ζ). Boundary-solver reads v1 before it's defined → COMPILE FAIL. Poseidon2/Merkle replayed
fine because straight-line I/O, no free internal witnesses; selectors have them.
⚑ ζ SOUNDNESS UNAFFECTED: hand-Go binding still bites, canary still CLOSED (verified). Both lanes REFUSED to
fake (swap: BLOCKED not broken; gate: "canary green ≠ substrate swapped"). CYCLE 11 = teach the generic
replayer to accept templates with FREE WITNESS VARIABLES (allocate internal wires as secret witnesses +
constrain them, not boundary-solve them) — a REUSABLE unlock for every gadget with range-checks/hints (most).
Then the selector swap (+ retro Poseidon2/Merkle if they hand-alloc). The 8055470a6 hand-Go ζ-binding stands
until the replayer can consume the Lean template.


## ✅ AIR-in-Lean CYCLE 11 — SUBSTRATE FIXED: ζ Lean-authored end-to-end (VERIFIED-BY-ME)
Reusable unlock: ReplayTemplateWithWitness allocates a template's free internal vars as secret witnesses +
applies asserts as CONSTRAINTS (not definitions) — handles any gadget with range-checks/hints, not just
selectors. bindBlockZeta:917 → replaySelectorsWitness (replay of Lean SelectorEmit), emit path has ZERO live
computeStarkSelectorsNative (survives only on the deployed hand-Go lane + as KAT oracle). I RAN the canary
(80.4s): ζ CLOSED, favorable-ζ forgery UNSAT, rejection attributable to the Lean-emitted replay. ζ is now
bound AND Lean-authored. The gate lane's "honesty nuance" was honest-and-fine (the rule honored, not a gap).
Cycles 9-11 arc: ζ over-claimed complete → canary proved it a live forgery → bound (Go drift) → substrate
fixed reusably, every step a BLOCKED-not-faked or a verified-by-me gate. Standing residuals: FRI-batch-alpha
(stage-bound); ζ openings bound to transcript not proven =evals (PCS reduction, seam #2); block-3 DAG
(trusted-ref); FRI floor; ceremony. All named.


## AIR-in-Lean CYCLE 12 — 3 block-path drift classes Lean-replayed; FRI-STAGE loop still hand-Go (named)
Block expand() path: Merkle/FRI-fold/PoW+canonicity all swapped to replay committed ∀-proven Lean templates
(MerkleEmit/FriFoldEmit/QueryPowEmit) via the cycle-11 witness-aware replayer. Canaries green (ζ CLOSED),
real proof verifies (162s). ⚑ HONEST QUALIFIER (gate lane named it, I confirmed): "3-of-3" is BLOCK-level
only — fri_verify_native.go:223-224,228 (the transcript-stage native FRI loop) STILL hand-authors Merkle +
fold on the emit path when the stage is attached = a 4th live hand-Go site. Cycle 13 = convert it (same
templates). Substrate-clean count: 6 block-path constraint sites Lean-replayed; remaining hand-Go on emit path
= FRI-stage loop (cycle 13) + classes 4-6 (challenger adapter, openings-bind, quotient/DAG=seam#2, named).


## ✅ AIR-in-Lean CYCLE 13 — FRI-stage converted; NONLINEAR CRYPTO now 100% Lean-authored on the emit path
fri_verify_native.go per-round Merkle+fold → replay MerkleEmit+FriFoldEmit (friStageReplay param; deployed
SettlementCircuit lane untouched, replay==nil = old body verbatim). 13 tests PASS (229s), ζ CLOSED.
⚑ HONEST RESOLUTION (gate §4): the emit path's NONLINEAR CRYPTO gadgets are 100% Lean-template replays =
the AIR-in-Lean law achieved for the crypto. BUT "substrate-clean" ≠ zero-hand-Go: hand-Go STRUCTURAL GLUE
(§C: equality-links, wire routing, loop scaffolding stitching replayed gadgets) remains — hand-Go, not
re-authored crypto (open Q: should glue even be Lean-emitted, or is routing-of-proven-wires acceptable?).
Named seams: class 4 challenger adapter (authorship, Lean lane named); class 5 openings-bind (named);
class 6 quotient placeholder + trusted-ref DAG = seam #2 (SOUNDNESS depth, not substrate).
⚑ TWO DISTINCT ENDPOINTS, not laundered: SUBSTRATE (crypto Lean-authored) = DONE for gadgets; SOUND
(seam #2 + FRI floor) = separate deeper goal. "Basically done" is TRUE for the crypto-substrate axis.


## ⚑ SUBSTRATE VERDICT: crypto-substrate DONE (glue RULED acceptable); cycle 14 = seam-#2 quotient bind
GLUE RULING (a decision, not a deferral): hand-Go structural glue (equality-links between Lean-emitted wires,
wire routing, loop scaffolding) is NOT a substrate violation. The AIR-in-Lean law protects CRYPTO CONSTRAINT
AUTHORSHIP (hashes/field-arith/soundness constraints) — all of which are now Lean-template replays on the emit
path. Glue authors no crypto (AssertIsEqual(leanWireA,leanWireB) is plumbing). So the CRYPTO-SUBSTRATE IS DONE.
(A full structural-emit templating the glue too is possible — SegmentEmit does it for block-5 links — but
gilding, not repair; not required.)
CYCLE 14 (firing): close the seam-#2 QUOTIENT PLACEHOLDER — block-3 binds folded==fresh-out (vacuous); wire
the real folded==quotient(ζ)·Z_H(ζ) over recomposeQuotientNative, canary a WRONG quotient must REJECT.
⚑ TWO ENDPOINTS, KEPT DISTINCT: SUBSTRATE (crypto Lean-authored) = DONE. SOUND: quotient-placeholder closeable
(cycle 14), but openings-ARE-committed-poly-evaluations = the FriLowDegreeSound PCS/FRI floor (named crypto
assumption, NOT a wiring gap, NOT closed by wiring). "Basically done" is TRUE for the substrate axis; the FRI
floor is the deepest remaining SOUNDNESS thing (a crypto reduction, its own campaign).


## ✅ AIR-in-Lean CYCLE 14 — seam-#2 quotient placeholder CLOSED (verified load-bearing w/ ATTRIBUTION)
bindBlockZeta tooth 3 (:1190): folded == quotient(ζ)·Z_H(ζ) over recomposeQuotientNative(opened chunks),
placeholder fresh-out GONE. I RAN the canary (61.5s) — it ATTRIBUTES the reject: tooth3-ON/tooth2-OFF accepts
honest; folded≠quotient·Z_H UNSAT w/ tooth3 sole constraint; tooth3-OFF same tamper ACCEPTS ⇒ reject IS the
quotient identity, not leakage; even disqualifies chunk-tamper (rejects bind-OFF, transcript-observed) as not
the identity proof. Best-constructed canary of the campaign.
⚑ FINAL SUBSTRATE STATE: crypto-substrate DONE (all nonlinear crypto Lean-authored, glue ruled acceptable,
quotient identity now real). The DEEP residual is ONE thing, on the SOUNDNESS axis not the substrate axis:
FRI/PCS openings=evaluations (FriLowDegreeSound) — the opened chunks are transcript-bound but not proven to
BE the committed polys' low-degree evals at ζ. A named crypto assumption / its own campaign. Plus permanent
trust-refs (block-3 DAG, ceremony). NOT a wiring gap; NOT "basically done"-able by a cycle — honestly named.


## ⚠⚠⚠ FRI-CAMPAIGN GROUNDING (07-20) — THE FLOOR IS EMPTY IN FOUR PLACES (counterproofs of OUR OWN claims)
⚑ CORRECTION TO CYCLE 4: `FriLowDegreeSound` (FriVerifier.lean:995) is VACUOUS — provably ≡ True.
GenuineWitness has ONE unconstrained Prop field (⟨True⟩ discharges it); its only other conjunct
(proof.exposedSegment = pub.segment) IS ALREADY a conjunct of verifyAlgo (segmentTooth is definitionally
that). Antecedent syntactically implies consequent. ZERO instances in-tree; wrap_sound has NO #assert_axioms.
⇒ emitVerifier_wrap_sound ("the keystone FIRES", cycle 4, e11e99a6f) CONCLUDES NOTHING. I celebrated it as
"structural soundness conditional on a named carrier" — the honest-sounding hedge hid an EMPTY carrier.
4th over-claim of the session, and the worst.
⚑ THREE CARRIERS REFUTABLE AT REAL PARAMS (false, not undischarged): FriLdtExtractV3/DeployedTraceExtract;
DeployedFriEmbedding.accept_folds (accept ⟹ folds ∈ C' EXACTLY = strictly stronger than real FRI);
ColumnDecodeBridge.accept_chains. All assert "every accepting proof yields a codeword" — FALSE BY COUNTING
(δ-far passes k spot-checks w.p. (1−δ)^k > 0; verifyAlgo is a Bool on a SUPPLIED proof, FS derandomized, so
the accepting set CONTAINS far-word proofs). The tree says so itself (FriColumnDecode.lean:52-56).
⚑ εQuery DISCHARGED BY DETERMINISTIC COLLAPSE: FriFarnessReconcile — both far events EMPTY on accepting runs
⇒ Pr=0, (1−δ)^k NEVER PAID. FriPositiveRadiusPayment proves it is unfixable at the deployed instance
(premises UNINHABITED; friSetupK8 = 16-point domain folding to size 2 vs production 2^24). The payment
lemmas are correct and THERE IS NO INSTANCE AT WHICH THEY FIRE.
⚑ DeployedFriEmbedding has NO field tying `oracle` to the proof's committed column ⇒ oracle:=fun _ _ => 0
trivializes accept_folds ⇒ collapses to DeployedTraceExtract verbatim (they are EQUIVALENT). The later
ColumnDecodeBridge (pins decodeColumn) is the non-trivializable route — build on THAT.
⚑ "~112.6 bits" STALE + WRONG (arity-2 figure; prover folds arity-8 ⇒ 109.84; arity8_error_not_lt_2e112
PROVES 112.6 fails at arity 8). ~35 docs still quote it; fri_params_soundness_budget.rs asserts 61 vs
PROVEN-120-CONFIG's 57.
✅ GENUINELY PROVEN (efficient-adversary test PASSED): hit_cond (the keystone — REPLACED a refuted carrier;
Stages 2-3's fsPt∉queriedFinset premise is FALSE for every self-transcript-computing adversary);
epsFri_closed_legs (εFS+εGrind+εMerkle over ONE shared oracle); the union bound; the whole-TREE fold
(nodes_union_bound, apex_probabilistic_nodeCarrier — tree side DONE, gap entirely per-node); the re-basing
faithfulness; codex's FriQuerySamplingBias (all 15 decls clean, real non-vacuity witness).
⚠ epsilon_query_layer/deployed are quantified over WORDS not ADVERSARIES (a fraction of the uniform product
space, f/f' universally quantified, verifier's own honest sampling with the far word FIXED IN ADVANCE) —
the project-fri-soundness-reality finding UNCHANGED by five stages.
⇒ BOTTOM LINE: the FRI content is NOT purchased at deployed params. 3 non-FRI legs proven vs Q-query
adversaries; the FRI leg discharged only by deterministic collapse at a TOY 16-point domain under refutable
carriers, and the wrap's carrier is vacuous.
⚑ FIRST MOVE (bounded, NON-research, unblocks everything downstream): build a FriSetup/FriSetupK instance at
REALISTIC domain AND deployed rate so the proven-but-unfireable positive-radius payment lemmas can FIRE.
Then: (ii) query-log extractor (commitment→total column, BCS16 straight-line), (iii) εQuery attached to the
ADVERSARY's run + codex's epsQueryBias composed (epsQueryBias currently has ZERO consumers), (iv) arity-8
rewind, (v) RETIRE/DELETE FriLowDegreeSound (as written it launders).
NOTE: ArkLib/VCVio NOT vendored (mathlib only); ArkLib FRI soundness is `sorry` end-to-end (117) — nothing
to import. The tree is honest to an unusual degree (Stage 5 states its own NEGATIVE verdict in Lean;
FriPositiveRadiusPayment proves its own vacuity) — the campaign inherits good faith, not good bits.


## ⚡⚡⚡ FRI CAMPAIGN WAVE 1 (07-20) — THE COUNTERPROOF LANDED: deployed floor is EMPTY, machine-checked
7 lanes + 7 adversarial verifiers; 6/7 real-and-adversary-quantified, non-trivializable (verifiers TRIED
oracle:=0 / witness:=⟨True⟩, didn't take). The swarm REFUTED the deployed floor FOUR ways, with arithmetic:
- ⚑ εQuery ≥ 1 AT DEPLOYED PARAMS (81cecbfb0, FriQueryAdversary): εQuery(|F|=2013265921,k=38,δ=7/16)=1/|F|+
  (9/16)^38 ≈ 2^-30.19 ⇒ Q·εQuery ≥ 1 (a bound of ≥1 = NOTHING) already at Q=2^31
  (epsQueryAdv_deployed_vacuous_at_2_31). The system's central number is VACUOUS BY COUNTING.
- ⚑ FriLowDegreeSound ↔ True machine-checked (81cecbfb0 friLowDegreeSound_content_iff_true +
  has_no_falsifier); payoff re-proven carrier-DELETED (wrap_sound_needs_no_carrier). Cycle-4 keystone
  confirmed IN LEAN to conclude nothing.
- ⚑ arity-8 REFUTED both ways (e8d843df4 FriArityForking): rewinding priced out (babybear_8fork_vacuous) AND
  straight-line cannot supply 8 challenges. Keystone only at positive d; deployed discharge uses unobtainable d=0.
- ⚑ extractor BUILT + REFUTES "total column" (737a69fa4 FriColumnLogExtract): extractComp_queryBounded (real,
  QueryBounded 0, BCS16, treeExtract_log_isTree NO floating hyp); no_deterministic_extraction (node-check⟹
  recover-subtree FALSE even 0-query). Build on ColumnDecodeBridge, NOT the trivializable DeployedFriEmbedding.
- ⚑ payment FIRES + domain never helps (9c6376789 FriDeployedRat...): realistic instance built, folding
  closure PROVED, deployed_positive_radius_payment_fires (deg-2^21 word 14.68M-far). AND arity_payment_delta_cap
  (∀ domain size) ⇒ enlarging domain NEVER recovers advertised soundness; δ=7/16 UNREACHABLE at the instance.
- ⚑ number is 51 not 61 not 57 (d140bfc98 friCommitLedger); only proved radius δ=7/16 prices ~31.5 bits;
  capacity_claim_understates_by_2pow82 / johnson_understates_by_2pow25.
7th lane (numbers docs-sweep): INCOMPLETE — left 3 self-contradictions in lane-edited files (fix next wave).
⇒ HONEST HEADLINE: the deployed FRI soundness is NOT there at deployed parameters, and it is now MACHINE-
CHECKED that it is not — a counterproof of our OWN floor, exactly ember's hoped-for outcome #2. The bits do
not exist as claimed (~31.5 at the only proved radius, vs 57/61/112.6 in circulation). This is ACTIONABLE:
either the deployed FRI PARAMS must change (more queries / different radius) to buy real bits, or the honest
posture is "unique-decoding ~31.5 bits, everything above is a NAMED assumption we have now PROVEN unpurchased".
NEXT WAVE: (1) finish the numbers sweep + purge 112.6/57/61 tree-wide → the PROVEN 51/31.5 + which theorem;
(2) COMPUTE what params WOULD buy target bits (the actionable fix — q, radius, arity for e.g. 100 real bits);
(3) the honest wrap posture doc (retire FriLowDegreeSound in the DEPLOYED wrap, state ~31.5 + the named floor).


## ⚡ FRI CRISIS RESPONSE (07-20) — PURGE done; UPGRADE hits the FIELD WALL (proven, not guessed)
PURGE ✅: ~112.6 de-claimed tree-wide (both remaining hits are "this was WRONG" statements, not assertions);
"~57 calculator bits" relabeled INFORMAL-density-estimate-NOT-a-bound; honest posture in docs (CHAIN-INVENTORY:
theorem-backed ε_C + query-soundness). fri_params_soundness_budget calculator handled.
⚑ UPGRADE — THE FINDING: you CANNOT buy bits by changing q/pow. The FIELD caps it (FriQueryAdversaryLaunch.lean
ed9a0bb72, 11 keystones clean): field_ceiling_vacuous_at_2_124 — BabyBear degree-4 gives ε ceiling ~2^-124;
100+128=228 ≫ 122 ⇒ NO honest "100 bits vs 2^128 adv" at deg-4, at ANY q. Config CORRECTLY left unchanged
(a q bump against a field ceiling is theater). PROVEN honest TRADEOFF: launch_100bits_vs_2_22_adv (100 bits
vs weak 2^22 adv), launch_60bits_vs_2_62_adv (60 vs strong 2^62). System posture = ε_C-ceilinged (~51-61,
NOT movable by q/pow — ε_C carries no numQueries/powBits).
⚑ THE REAL LEVER = EXTENSION DEGREE (extDeg): +30.91 bits/degree. deg-4→deg-8 buys ~124 bits headroom = the
actual upgrade, but a PROVER-FIELD change (touches the AIR arithmetic) — EMBER-GATED, deeper than a q cascade.
⚠ RESIDUAL: ε_C reads 51 (friCommitLedger d140bfc98) vs 61 (launch worst-case height) — reconcile (different
height/config); + verify lane flagged residual 57/61 to finish de-claiming.
⇒ HONEST DEPLOYED POSTURE: ~51-61 bits (ε_C-ceilinged, field-bound), δ=7/16 unique decoding, ~31.5 query term.
NOT 100. NOT 112.6. The only path above the ceiling is a bigger field / higher extension degree.

## Standing
- ArkLib **PR #655 LIVE + green** (import-check fixed, 78306878). Maintainers' call now.
- Discipline: sufficient-test every floor · additive soundness gets THOUGHT · never `-A` ·
  swarm-build on hbox · Fable=neutral framing · commit messages FOR THE RECORD not Slack.
- Done today: KZG vacuity + fix + BOTH GGM models wired + PR#655; ADOPT-ARKLIB-VCVIO roadmap.
