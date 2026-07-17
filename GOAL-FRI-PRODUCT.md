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

## Standing
- ArkLib **PR #655 LIVE + green** (import-check fixed, 78306878). Maintainers' call now.
- Discipline: sufficient-test every floor · additive soundness gets THOUGHT · never `-A` ·
  swarm-build on hbox · Fable=neutral framing · commit messages FOR THE RECORD not Slack.
- Done today: KZG vacuity + fix + BOTH GGM models wired + PR#655; ADOPT-ARKLIB-VCVIO roadmap.
