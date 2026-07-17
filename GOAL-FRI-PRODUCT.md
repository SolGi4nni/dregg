# GOAL — FRI soundness + product/fhegg excellence (AUTONOMOUS mode)

Mode: ember on break, deputized me AUTONOMOUS. Pursue residuals · launch actioning · excellence
at all times · sophistication proportionate to the challenge, NO further · ACT, don't wait-blocked
(undo-overeager > do-nothing). Verify EVERY landing myself (raw output, not the lane's word).

## Live threads (verify each landing → integrate → fire the next)
- **FRI (me, deep):** re-base the assumed `FriLdtExtractV3` over the ROM query-counting model
  (`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5). ✅ A2 `RomQueryLog` (bd2407b31). Stage 1 ✅ DONE (FriVerifierO.lean:
  verifyAlgoO + verifyAlgoO_run_eq faithfulness + permCallCount/QueryBounded; perm threads only via
  deriveTranscript, compress is separate — honest; 19 keystones clean, additive). Stage 2 FIRING. → Stage 2 (FS terms ε: 2/12 conjuncts
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

## Standing
- ArkLib **PR #655 LIVE + green** (import-check fixed, 78306878). Maintainers' call now.
- Discipline: sufficient-test every floor · additive soundness gets THOUGHT · never `-A` ·
  swarm-build on hbox · Fable=neutral framing · commit messages FOR THE RECORD not Slack.
- Done today: KZG vacuity + fix + BOTH GGM models wired + PR#655; ADOPT-ARKLIB-VCVIO roadmap.
