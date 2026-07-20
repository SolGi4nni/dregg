# HANDOFF — fhEgg protocol + Lean-game swarm results (Codex, 2026-07-18—19)

This is an implementation handoff, not a feasibility estimate.  It records what the
swarm changed in the shared working tree, the narrow gates that actually ran, and the
remaining security boundaries.  Verify at HEAD before quoting it: other lanes are active
in this repository and generated artifacts can move underneath a long-lived note.

## 0. Claude re-entry: the current shape in one page

This file is cumulative.  Sections 1–16 record the first swarm wave; sections 17 onward are the
07-19 continuation and should be read before planning new work.

The system is no longer best understood as “FHE plus one private auction.”  Four reusable organs
now meet at the game engine:

1. **Confidential decision/optimization relations, authored in Lean.**  Dark Bazaar clearing,
   private preference aggregation, exact portfolio-QP certification, private raid assignment, and
   private shuffle/fairness are fixed relations with Lean-emitted descriptors and HidingFri runtime
   paths.  HidingFri is Tier 1: proof consumers do not learn the witness, but the trace-building
   process does.  No-single-viewer production remains the separate FHE/MPC/distributed-prover lane.
2. **Exact state/enactment.**  Cells, exact factory-installed `CellProgram`s and canonical-v2 VKs,
   capabilities, predicates, receipts, and the recursive history fold bind a verified result to a
   state transition.  Complex/private mechanics are custom-VK leaves; simple public local checks
   remain predicate teeth.
3. **Policy authoring and semantic audit.**  The registered `Crypto/Deriv` tower now decides and
   *runs* unbounded emptiness and language equivalence for the symbolic `PredRE` fragment over the
   infinite `Value` alphabet.  `SymbolicMintermsPlus` covers enum membership, policy lists, and
   scoped owner-match; `PredicateLibrary` is the usable surface.  A separate Fable lane is widening
   scalar atom covers.  Do not repeat the older docs' claims that equivalence/fixpoint are absent;
   supersession notices were added to those audits.
4. **Derivation/rewrite attestations.**  `Crypto.Chain.Cert R` is the generic locally-checkable
   reduction certificate.  DFA, VPA, CFG, pushdown replay, hypergraph replacement, and genuine
   match-driven graph rewriting all instantiate it.  `Crypto.GraphRewrite` already proves the
   match/delete/glue semantics in Lean.  The general hiding graph-rewrite circuit/runtime is the
   newly active devnet campaign; only the Dyck/CFG instance currently has a deployed end-to-end
   parse AIR.

The load-bearing custom-leaf VK carrier is now faithful end to end.  A direct IR2 leaf validates the
exact canonical-v2 recipe and exposes all eight VK limbs; the shared RotationV3 leg publishes the
same VK8 at PI 54–61; and the recursive binding node connects every limb in-circuit alongside the
commitment, state, and app-root teeth.  Legacy commitment4/VK4 and commitment8/VK4 carriers refuse
at the versioned boundary.  The first honest private-preference fold is implemented and typechecked;
executing its proof-heavy gate is temporarily blocked only by disk exhaustion on both the build node
and the local shared target, not by a known carrier seam.

Do not add conventional calendar or staffing estimates to this handoff.  The executable board is
in §21; narrow gates and exact refusal boundaries are the unit of progress.

## 1. Output crossing: balanced, reveal-minimal at the recorded-transcript boundary

`fhegg-fhe/src/mpc.rs` now computes the exact uniform-price rule as:

1. secret-shared `min(D[p], S[p])` for every bucket;
2. a balanced oblivious argmax tournament;
3. left/lower-index wins equality, including through odd carries;
4. only `(p*, V*)` is opened.

The modeled online depth is
`(max(b,2) + 1) * (1 + ceil(log2 K))`: 119 rounds for `(b=16,K=64)` and
153 for `K=256`.  The exact Beaver-AND count is
`K*4b + (K-1)*(4b+ceil(log2 K))` (8,506 / 34,744 for those shapes).
Tests cover power and non-power `K`, ties, odd carries, `K=1`, and the old
largest-crossing counterexample.

`Transcript::is_reveal_only(k,b)` now validates the complete recorded schema, not
only the width of `p*`: exact `p*` and `V*` widths, exactly two masked openings per
AND, and canonical bits throughout.  Appending an unmasked output, an extra masked
opening, or a non-bit turns the tooth red.  This is a simulator for the public
one-process transcript; it is not a corrupted-party/network UC theorem.

Narrow gate: `mpc::pure_tests` — 7/7 PASS.

## 2. Smudging: the scalar theorem is now an explicit transcript ledger

`metatheory/Bfv/Smudging.lean` now carries the deployed scalar epsilon, transcript
coordinate count, session count, a `TranscriptHybridLedger`, and the corresponding
union/hybrid bound.  Exact pins include:

- 4,096 coefficients × 16 ciphertexts × one session = `2^-32`;
- 256 sessions = `2^-24`;
- 65,536 sessions = `2^-16`;
- `2^32` sessions exhaust the bound at 1; beyond that it is no longer useful.

This does not invent the adaptive/RLWE bridge.  It makes the existing conditional
assumption and its composition budget explicit.

Gates: `lake env lean Bfv/Smudging.lean` and `lake build Bfv.Smudging`; 27 pinned
keystones kernel-clean.

## 3. BFV key custody: party-owned n-of-n, no conveniently assembled secret key

`fhegg-fhe/src/threshold.rs` now exposes a production-shaped honest-party API:

- public `KeygenSession` / CRP seed;
- opaque, non-`Clone`, non-`Debug` `ThresholdParty` custody;
- public-key contributions aggregated by `KeygenCoordinator` without collecting
  secret shares;
- strict public-key/decrypt-share framing;
- duplicate, session/CRP, parameter, malformed-residue, incomplete-quorum, and
  smudging-floor/ceiling refusals;
- byte-equality against fhe.rs's native mbfv public-key aggregation and a native
  decrypt oracle.

The old helper that assembles all key shares is test-only.  Channel integration
puts each party in its own thread, refuses `n-1`, and combines only the full framed
quorum.

Narrow gates: threshold unit 9/9; `threshold_party_isolation` 1/1;
`threshold_no_viewer` 2/2; private-derivative integration 1/1.

Honest residuals: this is `n-of-n`, not `t-of-n`; messages are not authenticated;
malicious-share validity, replay/crash recovery, and a zeroized persistent secret
store remain unbuilt.

## 4. Masked BFV → MPC boundary: the two halves now actually compose

`fhegg-fhe/src/boundary.rs` now has `MaskedDecryptSession`, party-retained
`MaskedBoundaryParty` masks, strict `EncryptedMaskContribution` framing,
`MaskedDecryptCoordinator`, and `ThresholdMaskedCiphertext::open_framed`.
The process-shaped path is:

`ct` → each party adds public `Enc(r_i)` → parties smudged-decrypt the exact masked
`ct'` → only `y = m + Σr_i mod t` opens → each party locally derives its mod-t row.

The coordinator never receives a plaintext mask or a threshold secret share.
`open_framed` is now bound to the exact masked ciphertext owned by the session.  This
was a real review finding: equality among submitted shares alone allowed a valid full
quorum for another ciphertext.  The gate now rejects both a mixed share and a
self-consistent wrong-target quorum before accepting the honest quorum.

Narrow gate: `threshold_masked_boundary_channels` — 1/1 PASS (5.7s test).

That arithmetic ingress is now implemented at party-thread scope in
`fhegg-fhe/src/mpc_party.rs`.  Each `PartyArithmeticInput` constructor sees only one
party's locally derived demand/supply rows, XOR-shares every bit directly to the peer
endpoints, and the parties perform a balanced source-adder tree followed by `n-1`
oblivious conditional reductions modulo `t`.  The coordinator has no peer-input
endpoint; the trusted triple dealer accepts public session shape only and cannot name
an input row or aggregate curve.  The unchanged balanced crossing then reconstructs
only `(p*,V*)`.

The exact transcript ledger includes the A2B/mod-`t` gates, actual scalar Beaver
opening rounds, and the smaller batched dependency depth
`ceil(log2 n)*(w-1) + (n-1)*(w+1) + crossing_rounds(K,b)`, where
`w = bit_length(n*(t-1))`.  Tests cover `K=1,3,5,7,8,9`, ties and odd carries,
strict transcript mutations, cross-session refusal, and `n-1` input withholding.
The real `MaskedBoundaryParty` integration now feeds its derived rows through this
runtime and returns `(Some(2),65535)`.

Narrow gates: party MPC 3/3 PASS (0.219s); composed masked boundary → party MPC
1/1 PASS (4.956s).

Remaining deployment seams are authenticated isolated-process transport,
roster/replay binding, malicious input/share validity, dealer-free or auditable
triple preprocessing, crash recovery, and `t<n` custody.  They are no longer a
clear-curve ingress seam.

`metatheory/Market/MpcClearingSecurity.lean` now models this same volume-argmax
object rather than an obsolete balance-threshold/sign-vector protocol. `MpcView`
contains only `(p*,V*)` plus public shape; the joined theorem proves conservation,
uniform-price optimality, volume maximality for every bucket, and exact reveal-only
simulation on that same clearing. RED teeth show the old balance crossing disagrees,
the old sign vector is not determined by actual leakage, and a private demand cell
cannot be simulated. The masked-boundary/A2B bridge is stated over `ZMod` with the
actual bounded-bit premises. Direct Lean gate: 17 keystones kernel-clean.

## 5. First retained resident-GPU consumer

`fhegg-fhe/src/additive.rs` now has the first real consumer of
`gpu_arena::FoldEngine`:

`KeygenCoordinator/CollectivePublicKey` → unary order-row SIMD encryption → the
required strict fhe.rs-wire parse → retained demand/supply `FoldEngine` → encrypted
`LeanCiphertext` curves → the masked threshold boundary above.

`CollectiveOrderFoldEngine` reports the actual backend, adapter capacity, resident
plan, and timings.  CPU-no-arena and GPU-unsupported-shape fallbacks are labelled;
wrap refusal stays fail-closed.  There is no joint secret key.

Focused integration: 1/1 PASS (4.15s).  On the M2 run it used the resident GPU for
both three-row sides: one upload and no reduction round per side; demand fold 8.74ms,
supply 3.71ms.  The unavoidable representation ingress was measured separately
(33.7ms total for six rows).  Exact CPU bytes and the plaintext recovered only
through the masked threshold boundary matched.

Honest transfer boundary: fhe.rs keeps coefficient rows private, so each submitted
ciphertext currently pays one serialize + strict parse; each side then pays one
host→GPU upload and one folded-ciphertext readback because the boundary consumes a
host `LeanCiphertext`.  No ct×ct or whole-solver residency claim is made.

## 6. Cert-F: field acceptance now implies integer admission for both registered wires

`metatheory/Market/CertFDescriptor.lean` first made the missing field→integer boundary
explicit (`IntegerCertF`, `IntegerWellFormed`, `IntegerAdmission`) and proved exact
incidence/objective/gap bridges plus concrete wrap countermodels.  The descriptor now
enforces the sufficient ranges rather than accepting them from callers:

- every dual potential has a fresh 28-bit range gadget;
- ring3 retains 28-bit flow/slack policy;
- market4 reuses its existing bit bands with tight 21-bit flow and 19-bit slack
  recomposition gates;
- `ring3Prog_integerAdmission` and `market4Prog_integerAdmission` are unconditional
  consequences of canonical descriptor satisfaction.

This intentionally changes the registered wire shapes: ring3 is width 465 / 482
constraints; market4 is width 581 / 602 constraints.  The Lean goldens and checked-in
descriptor JSON were regenerated.  Rust base-trace construction fills the new
potential band and tests pin the exact shape, the old common-π-shift attack, and both
market-specific tight guards.

The new artifact hashes are:

- ring3: `8f104012760b24ccda1065ed4b559a0c9c10188acd5523298bfb77a5095ab0cc`;
- market4: `15d421d24c725da84f2c67061a171a9b4f5c37323f94b662cec590974e2e1520`.

Old proofs/VKs for these descriptors are intentionally incompatible with the new bytes.

Gates: `lake env lean Market/CertFDescriptor.lean` green; 34 keystones and all 85
namespace theorems kernel-clean.  Runtime teeth 4/4 PASS:
`registered_descriptors_carry_integer_admission_policy`,
`air_rejects_unranged_potential_shift`,
`market4_tight_flow_and_slack_gates_bite`, and `air_accepts_valid_ring3`.
A redundant full-STARK rerun was deliberately not used as a per-edit tax.

The theorem is still for the registered circulation-LP certificate.  It does not
turn arbitrary complementarity/bundle auctions into integral programs, and it does
not discharge the FRI soundness floor.

The Cert-F proof path now has an actual hiding batch-STARK entry point rather than a
comment that overclaimed the plain PCS.  `prove_cert_f_zk` / `verify_cert_f_zk` run
the identical Lean-emitted IR-v2 descriptor through the repository's OS-seeded
`DreggZkStarkConfig` (`HidingFriPcs`); the compatibility `prove_cert_f` path is now
explicitly documented as non-hiding.  The focused ring3 tooth mints and verifies a
real hiding proof, asserts the random-polynomial commitment and per-instance random
openings are present, and refuses changing the public volume from 3 to 4.

Narrow gate: `hiding_stark_proves_and_binds_public_volume_ring3` — 1/1 PASS
(0.056s test body).  This builds the hiding PCS construction for registered Cert-F
programs.  A formal simulator theorem for the complete batch-STARK transcript remains
separate, as does Tier-0 distributed proving/source binding where no one prover sees
the clear orders.

The Dark Bazaar caller is now a real Cargo surface rather than an untracked file Cargo
never compiled. `dreggnet-market` exposes `certified_clearing` behind the opt-in
`certified-clearing` feature and declares the heavy prover/solver dependencies only on
that feature. Its `try_prove_stark` entry point uses the hiding Cert-F prover. An
independent minimal-crate gate compiled the exact module and drove a real three-bid
book through deterministic clearing, a valid tight certificate, and the named
unregistered-program refusal.

That refusal is the honest current boundary, not success disguised as wiring: the
auction certificate is a dynamic 2-node program whose public `w` coefficients are the
bid values, while the registered descriptors are ring3 and market4. Per-book public
descriptor specialization would reveal the bids. A fixed relation that binds private
order commitments/coefficients—or a distributed integrity proof over the party MPC—is
required before the Bazaar can mint a Tier-0 proof.

## 7. Private derivative path

`fhegg-fhe/tests/e2e_private_derivative.rs` is no longer an ignored placeholder.
It builds a real fhIR program, demonstrates the active `[-15,15]` prox refusal,
runs the certified identity sibling over `[-100,100]` for six encrypted affine
steps, encrypts under the collective key, refuses `n-1`, and decrypts only through
the full smudged quorum.  All 4,096 slots match the exact scaled result
`(1536,-1536)` at scale `3^6=729`.

This is an honest correctness/integration tooth, not a transcript-security theorem.

## 8. Lean-native game braid

The game work stayed Lean-first rather than extending the Rust AIR archaeology.

**Descent.** `Dregg2/Games/DungeonCompleteness.lean` generalizes key exhibition to
every deployed keyed way 2–4 and proves a key-mutation refusal.  More importantly,
the attempted universal completeness theorem found a real abstraction mismatch:
`Dungeon.Inv` permits a relic at another relic's home floor, while the authored
program's provenance tooth is per-relic.  `wrongHomeState` is model-invariant and
model-legal for `delve` but program-refused.  The exact repair is
`ModelProgramInv := Inv ∧ CustodyHomeWF`; it holds at genesis and is preserved by
step, replay, and reachability.  `modelProgram_delve_admitted` is the first positive
method theorem and includes exactly the depth/spent riders. The completed method suite
proves unlock (selected way 2/3/4 + spent), smite (spent), loot (spent), and flee
(fate + spent, with bank constraints exactly when its slot changes). Universal
`modelProgram_step_admitted` dispatches every legal `Move`, and
`reachable_step_admitted` lifts it to reachable states. Direct Lean check is green;
all seven capstones are individually axiom-clean and the exact forbidden-token scan
is empty.

**Automatafl Leg S.** Three new Lean-authored modules now define, refine, and join a
fixed 11×11 sealed-reveal leaf:

- `AutomataflRevealEmit`: 105 columns, 41 PIs, 115 constraints; coordinates are
  degree-2 range-constrained, flattened in-circuit, and served through Poseidon2;
- `AutomataflRevealRefine`: SAT implies both exact public openings and all nine
  old-board packed felts; a changed opening with the same commitment unconditionally
  extracts a concrete arity-4 collision;
- `AutomataflRevealJoin`: PI `[39,41)` is a constrained commit-pair slice matching
  the deployed `AppRootBinding` shape, and the join theorem binds it to the preceding
  commitment fields given the real weld/preservation carriers.

No descriptor or caller is registered.  The refusal boundary is proved and named:
the live game stores a truncated ~63-bit BLAKE3 seal while Leg S has one ~31-bit
BabyBear Poseidon lane; the current flat-field weld loses high host bits; one-felt
generic birthday scale is only about `2^15.5`; the live board is 5×5 rather than
11×11; and the nine-felt heap board pack does not fit the eight flat-field lanes.
An attempted one-felt live cutover was reverted rather than weakening the playable
game.  Emit, Refine, and Join each pass their direct Lean check and axiom gates.

`Dregg2/Games/AutomataflBraid.lean` now performs that all-Lean composition through
resolved board, automaton step, and winner. It proves functional staged outcome and
Leg-S-selected outcome, unconditional swap-to-collision extraction, no-spurious
winner, and proof-native commitment/old-pack joins; executable winning and non-winning
traces are green. The deployment mismatches remain theorems rather than prose: current
live `n=5` cannot be the `n=11` Leg-S relation, and the closed R/A `n=2` carrier cannot
be the `n=11` board. Direct Lean check, 14 axiom gates, and three executable guards are
green with no forbidden proof tokens.

## 9. Exact Dark Bazaar attestation contract

`metatheory/Market/DarkBazaarAttestation.lean` now states and proves the strongest
honest end-to-end join rather than letting four proof objects sit adjacent in prose:

`committed (OrderBook,K)` → exact volume-argmax output → fixed registered market4
Cert-F statement → exact settlement receipt.

The join carries an explicit injective source-to-Cert-F compiler, proves
`honest_end_to_end_join`, `no_spurious_settlement`, and `end_to_end_binding`, and uses
the actual market4 deployed emit-soundness bridge. The RED
`output_only_attestation_does_not_bind_source` exhibits two distinct books whose
actual outputs are both `(1,8)`, so a receipt containing only `(p*,V*)` cannot identify
which source book was cleared.

Tier 1 and Tier 0 are separated in the type-level contract. The Tier-1 world simulator
coexists with an explicit theorem that the solver receives the plaintext book. The
Tier-0 residual requires both public-view simulation and source extraction from every
accepting distributed proof; identical public views over different solver books are a
separation tooth. The compiler and Tier-0 carrier are specified, not fictionalized as
installed. Direct Lean gate: 12 keystones kernel-clean, forbidden-token scan empty.

`fhegg-fhe/src/attestation.rs` implements the matching canonical runtime envelope.
It domain-separates and length-prefixes SHA-256 bindings for protocol/session, exact
ordered roster and input ciphertext/commitment digests, BFV degree/moduli/plaintext
modulus/CRP/collective-key identity, public `(K,b,t)` rule shape, strict distributed
transcript, output-bit consistency, and `(p*,V*)`. Verification reconstructs those
objects independently and a stateful guard rejects replay.

The API refuses to equate that binding with malicious computation integrity.
`BindingOnly(OutputOnlySelfAssertion)` can pass structural binding but can never pass
`verify_full`; full verification requires a relying-party-supplied external verifier
over the exact claim digest. Mutation, roster/input reorder, wrong BFV identity,
transcript/output mismatch, binding-only promotion, bad evidence, and replay teeth are
green. Narrow gate: `attested_clearing_receipt` 3/3 PASS (0.015s).

The envelope now also has a concrete `AuthenticatedQuorumVerifier`: an exact ordered Ed25519 roster,
threshold, and verifier identity derived from roster+threshold; signatures are over the canonical claim,
signers must be strictly ordered and unique, and an unknown, duplicate, missing, reordered, or invalid signer
refuses. `dreggnet-market`'s opt-in `authenticated-clearing` feature canonicalizes the complete
`CertifiedClearing`, requires its digest exactly once inside the FHE claim, checks the output crossing, and
replays the full verification. This is a real authenticated co-endorsement weld. Its negative test also pins
the boundary: old evidence fails after a ciphertext digest changes, but a quorum can sign a newly fabricated
combined claim. Therefore it proves exact attribution and agreement, not ciphertext-opening/source relation
or malicious MPC correctness.

## 10. The feasibility brief is now an implementation brief

The earlier brief was wrong, so `HANDOFF-FHEGG-FEASIBILITY-CODEX.md` was corrected
in place. It no longer tells an agent not to build or asks for sequential rough-cost,
calendar, or conventional staffing estimates. It now asks an adversarial swarm to
implement independent technical lanes in parallel and report executable exit gates.
The current concrete boundary is:

- balanced reveal-minimal public MPC transcript: built;
- scalar-to-transcript smudging ledger: built, conditional bridge explicit;
- party-owned n-of-n BFV keygen/decrypt: built at process-shaped honest-party scope;
- party-owned masked boundary composition: built at process-shaped scope;
- retained resident GPU fold under the collective key: built and measured;
- integer-sound registered Cert-F wires: built and enforced;
- hiding Cert-F batch-STARK for registered programs: built and exercised;
- authenticated/malicious distributed protocol, `t<n`, exact committed-volume
  argmax/source attestation, a complete ZK simulator theorem, and full FRI decode:
  still distinct frontiers.

Do not collapse those last items into one "threshold/networking" checkbox; they are
different security statements and need different teeth.

## 11. First fixed private-input Dark Bazaar relation

`metatheory/Market/DarkBazaarPrivateDescriptor.lean` authors a fixed `N<=4,K=4,qty<16` relation in Lean.
Orders and eight canonical blind felts are private witness data. The public statement is exactly
`(session, rule, order_root[8], p*, V*)`; the root is the full eight-lane output of an arity-16 Poseidon2
permutation over domain/session/rule/injective packed book/blindings/four framing zeros. The arity-16 detail
is load-bearing: the first arity-12 attempt passed a width check but the deployed chip selector replaced
input lanes and made a blinding mutation root-insensitive. The wide mutation tests found it before handoff.

The emitted descriptor recomputes book packing, demand/supply/volume, minimums, unique selection, global
maximum, and lowest-price tie break. `circuit-prove::dark_bazaar_private` exposes separate non-hiding and
`HidingFriPcs` proof APIs plus fresh OS-sampled canonical blindings. Private-order/session/blind mutations
change the root; public root/price/volume tampering refuses; two proofs have different random commitments.

Lean proves semantic checker soundness, packing injectivity, collision reduction, and extraction of all
emitted modular gates/root-chip/PI pins from actual `Satisfied2` against arbitrary external public inputs.
The named residual `DarkBazaarDescriptorToAccepts` is the final bounded modular-to-integer decode/no-wrap
lift from those gates to the semantic `Accepts` relation. This is Tier-1 shielding from proof consumers: the
process constructing the trace sees plaintext orders. It is not the Tier-0 no-single-viewer producer.

Narrow gates: Lean file/module and byte-emission parity green; degraded-felt AST gate green; focused Rust
proof tests 3/3 PASS, with the hiding/tamper test taking 0.347s after build.

## 12. fhIR/optimizer admission moved onto exact teeth

`metatheory/Market/FhIRClearingPlan.lean` is the first Lean-authoritative fhIR product family: a typed
two-coordinate rebalance plan, exact compiler, resource/leakage/no-wrap/noise proofs, canonical emitted JSON,
and a strict Rust decoder that refuses malformed or drifted bytes before dispatching the real solver. This is
one concrete family, not a claim that the legacy Rust compiler for every product was replaced.

For portfolio QPs, fhIR acceptance no longer follows the f64 diagnostic certificate. `solver_bridge` lifts
the certificate into the exact fixed-point checker and accepts only the exact verdict. `compile` now
canonicalizes at `10^-9`, checks all data/dimensions/finite values and the `2^53` lift envelope, and admits the
exact rounded matrix only with a symmetric nonnegative diagonally-dominant certificate. The same rounded
matrix reaches the backend; unsupported PSD matrices refuse closed; f64 LDL remains diagnostic. Focused fhir
gate: 46/46 PASS (0.221s).

`Market.SddPsd` now closes the mathematical half of that admission claim over the exact carrier. Its
executable `sddCheck` checks an integer matrix for entrywise symmetry, nonnegative diagonal, and every exact
row inequality `sum_{j!=i} |P_ij| <= P_ii`; `sddCheck_implies_psd` lifts accepted entries to rationals and
constructs the existing `Market.PsdSymm`. The proof is general over finite dimensions: paired off-diagonal
square inequalities bound the cross energy, row dominance bounds the diagonal energy, and their sum proves
`0 <= x^T P x` for every rational vector. Concrete teeth accept `[[4,-1],[-1,2]]`, reject asymmetric,
indefinite, and negative-diagonal mutations, and prove both that rank-one `[[1,2],[2,4]]` is PSD and that the
conservative SDD checker refuses it.

The Rust-refinement seam remains explicit. Lean proves the exact integer predicate and its rational PSD
meaning; it does **not** yet prove that `fhir/src/compile.rs`'s f64 tolerance symmetry pass, pairwise averaging,
`10^9` rounding, `2^53` lift guard, checked-i128 row sums, or row-major matrix indexing produce precisely the
Lean matrix checked here. The Rust code and tests exercise that path, but a parser/canonicalizer denotation
theorem is still required before saying the compiler itself is formally faithful to `sddCheck`.

A separate fixed full-shape `n=6,mc=7` CertQp descriptor now closes the concrete emitted bridge at `S=10^3`.
`portfolio_satisfied2_implies_checker` takes only canonical BabyBear cells plus actual byte-pinned
`Satisfied2 portfolioDescriptor` and returns every exact integer checker clause: primal feasibility,
stationarity, and the low/mid/high normal-cone/clamp cases. `portfolio_noWrap_of_satisfied` derives the complete
residual window internally from the emitted 24-bit tables, x10/y12 upper gates, BabyBear-prime selector
Booleanity, and the fixed `P/q/A/l/u` arithmetic; there is no caller-supplied no-wrap premise or trusted clause
flag. `portfolio_public_return_exact` pins the sole public value to exact `-q^T x`; `(x,y)` remain private.

The verifier also exact-compares the supplied descriptor with the committed Lean artifact, so descriptor drift
refuses. Direct Lean/axiom gates and regeneration `--check` are green. An actual fhIR compile/solve/lift run
mints and verifies a HidingFri proof, and changing the public return refuses. The production runner's `S=10^9`
still needs an honest multi-limb carry/comparator AIR rather than a silent scale claim.

## 13. The Dark Bazaar now has a real Descent-asset settlement seam

`LootVault::into_assets` hands another engine organ the exact live Descent note world. A settled Bazaar
session exposes the winning `DreggIdentity` and `settle_winning_asset` crosses an existing `AssetId` for the
verified winning `$DREGG` price through `dreggnet-trade`'s sealed-escrow atomic swap. The end-to-end test starts
with a real fair-drawn Descent boss drop, never re-mints it, and verifies the lineage after
`mint -> escrow -> winner`. An unfunded winner is refused and the item returns to the seller.

Narrow remote gate: 2/2 PASS in 0.053s after build. Honest residual: auction resolution and the asset/value
cross are two committed operations, not one indivisible multi-cell turn; the dedicated live Descent frontend
does not yet feed its durable player world into the catalog Bazaar session.

## 14. Factory birth now installs the exact full program and canonical v2 VK

The sealed-auction factory previously advertised a method-dispatched `CellProgram::Cases` but factory birth
installed only a flattened `Predicate(state_constraints)`. That was a real semantic weakening: the born cell
did not necessarily execute the program whose identity the app claimed.

`ChildVkStrategy::FixedProgram` now carries the exact executable `CellProgram` together with the AIR,
verifier-implementation, and proving-system components of the canonical v2 verification-key recipe. Strategy
hashing and child validation bind all four components; executor birth installs that exact program and derives
the exact same v2 VK; node seed construction follows the same recipe. The enum variant was appended and its
postcard round-trip is pinned so existing discriminants do not move.

The sealed-auction factory now uses the full program, including constructor dispatch and the exact phase
`AllowedTransitions` floor. Integration checks program and VK identity after birth and throughout commit,
close, reveal, and resolve. Legacy-v1/wrong-VK birth, wrong verifier/proving-system components, phase rewinds,
phase skips, and overwrites refuse without leaving ghost cells.

Remote gates: `dregg-cell` 788/788 PASS (one skipped); sealed-auction factory integration 4/4 PASS;
sealed-auction library 29/29 PASS; `dregg-node --lib` compiles green.

## 15. Reusable private preference aggregation is a Lean-emitted proof organ

`Dregg2/Games/PrivatePreferenceDescriptor.lean` and `circuit-prove::private_preference` implement a fixed
`N=4,K=4` score ballot for party forks, guild votes, matchmaking selection, and quest choices. Every private
participant scores each option in `0..3`; the public statement is only
`(session, rule, ballot_root8, winner)`, with the lowest index winning a tie. Aggregate totals and winning score
remain private.

The sixteen scores are injectively packed into two 16-bit felts and committed with eight canonical blind felts
through one full-arity Poseidon2 permutation exposing all eight output lanes. Lean proves semantic checker
soundness, pack injectivity, distinct-opening collision reduction, actual `Satisfied2` gate/PI/root-chip
extraction, every binary-column decode, and exact two-bit score plus four-bit difference/slack recomposition.
`privatePreferenceN4K4_descriptor_to_accepts` now closes the whole functional bridge: actual `Satisfied2`,
canonical trace cells and canonical external PI representatives, plus the wide Poseidon chip-table theorem,
imply semantic `Accepts` for the decoded witness. Total/pack/select/max/root identification is no longer a
residual.

Rust provides strict validation, fresh CSPRNG blindings, explicit hiding/non-hiding proof APIs, and
`verify_decision_zk -> VerifiedDecision`, so a lightweight game crate can consume a verified winner without
depending on the proving stack. Tier 1 remains explicit: the trace-building process sees all ballots; a
threshold-FHE/MPC or distributed producer is required for a house-blind ballot service.

Gates: 19 Lean keystones kernel-clean; fresh emission byte-identical at SHA-256
`e7e2c7dbf4d34b104f2478b4c745a399936b5b127afa4f8b793e9ef177cc902d`; faithful-commitment scan green;
focused Rust 3/3 PASS (hiding test 0.204s after build).

## 16. Private N=8 shuffle/deal proves exact permutation and selective openings

`Dregg2/Games/PrivateShuffleDescriptor.lean` and `circuit-prove::private_shuffle` implement a fixed eight-seat
private deal. The public statement is only `(session, rule, deal_root8)`. Each seat's hidden card and eight
independent canonical blind felts enter a full-arity-16 Poseidon2 leaf; eight leaf digests fold through seven
full-width `node8` compressions. A recipient can receive only its card, leaf blind, and depth-three sibling path
and reconstruct all eight public root lanes without learning another card.

The descriptor carries an 8x8 one-hot matrix. Row-one and column-one gates plus card recomposition prove the
assignment is a bijection of canonical cards `0..7`: no duplicate and no omission. The Lean author has 258
columns, 10 PIs, 15 full-width chip lookups, and 89 exact-permutation gates; all seven named keystones are
kernel-clean. Rust exposes only the HidingFri proof API for this privacy-facing family. Opening membership and
the exact-permutation proof are deliberately separate checks and must verify against the same public statement.

The security boundary is formal, not prose: `coordinator_choice_bias_residual` exhibits two distinct valid
permutations. This organ proves shuffle correctness, not unbiased sampling. Joint entropy, a threshold MPC
shuffle, or a verifiable mix/re-encryption layer remains required before claiming that no coordinator chose the
deal.

The emitted artifact re-emits byte-exact at SHA-256
`6c1e390a0a86bf6778e62e7541a6053240207dddad6acafba457a282c9f0c539`. Five narrow tests pass: host shape and
permutation refusal, root binding, duplicate AIR rejection, selective-opening tamper refusal, and HidingFri
proof/public-statement tamper refusal.

## 17. Private preference now has a cell-bound direct-IR2 carrier, fail-closed at the exact VK boundary

`Dregg2/Games/PrivatePreferenceCellDescriptor.lean`,
`circuit-prove/src/private_preference_cell.rs`, and `turn/src/private_preference_custom.rs` extend the
standalone preference proof into a real cell-transition statement.  Its 27 public inputs are

`[old_root8, new_root8, session, rule, ballot_root8, winner]`.

The winner is the app-root field selected by the cell transition; the descriptor is width 134 and
the emitted artifact is 53,430 bytes with SHA-256
`c1009a7bc63e3669b3754c07e60748dcb9faf3ea748f45a71cad3483ae6e9b44`.  Lean proves the cell relation
projects to the base private-preference relation and therefore to semantic `Accepts`; six keystones
are kernel-clean.

The direct `CustomIr2WitnessBundle` retains the exact canonical-v2 recipe, parses the program bytes
as that exact descriptor, and exposes all eight faithful VK limbs from the anchored leaf.  RotationV3
now appends four commitment teeth and four VK teeth to the custom host (base 1619, VK base 1623,
host width 1627).  Its exact ABI is commitment8 at PI 46–53, VK8 at PI 54–61, rc at PI 62–65,
the committed app-field octet at PI 66–73, and wide anchors at PI 74–89.  The direct recursive node
connects leg VK8 to leaf VK8 lane-by-lane before re-exposing the ordinary chain segment.

Admission is a typed flag day: v1 commitment4/VK4 and v2 commitment8/VK4 are retired and refused;
v3 requires the full relative commit-teeth-plus-VK-teeth geometry.  The honest private-preference
direct fold uses the actual Lean-emitted descriptor and canonical program VK8.  Separate poles refuse
wrong descriptor/program bytes, a low4-only VK, every individual wrong VK limb, and wrong old root,
new root, or app root.  The three targeted custom registry rows are byte-identical to their Lean
emissions; SHA-256 is `7c2ce432…00cb` (narrow), `9fd3bf98…a4b` (wide), and
`7e73f325…11f7` (wide+umem).

Gates: the RotationV3 source and the RotationV3/Wide/WideCompact/UMem Lean targets are green; remote
`cargo check -p dregg-circuit-prove` and local `cargo check -p dregg-circuit-prove --tests` are green
after the fold tests were added.  The honest and four recursive refusal proofs are deliberately
ignored-heavy and typecheck, but have not executed: persvati and the local link both currently fail
with `No space left on device` (the local shared target is 92 GiB).  Preserve the caches/WIP; this is
an execution-environment residue, not a reason to weaken or prefix-match the VK carrier.

## 18. Private raid/matchmaking assignment: runtime real, formal optimizer bridge one bounded lemma away

`Dregg2/Games/PrivateRaidAssignmentDescriptor.lean` and
`circuit-prove/src/private_raid_assignment.rs` define a fixed four-seat/four-role optimizer.  The
private witness contains sixteen scores in `0..3`, sixteen independent admissibility bits, and eight
blind felts.  The public statement is only `(session, rule, input_root8, roles4)`.  A valid result is
an exact role permutation, every selected seat/role pair is admissible, the total score is globally
maximal over all 24 assignments, and the lowest assignment row wins an equal-score tie.

The descriptor has 299 columns, 14 public inputs, one full-arity-16 Poseidon2 lookup, and 701
constraints.  Artifact SHA-256:
`141aec3bbed421fc984200c97d158591f0792266d7e5fb71ffe2d7480ea7a869`.

Lean is green with 16 kernel-clean keystones.  It already extracts exact integer
score/admissibility/select/total/difference bits from actual `Satisfied2`, proves every
recomposition, obtains a genuine decoded permutation, identifies the chosen total, and closes the
candidate-chosen/candidate-allowed products without a caller-supplied no-wrap premise.  The exact
remaining bridge is narrow but semantic: map an arbitrary feasible assignment to its `Fin 24` row;
use that row's allowed/dominance certificate to prove its score is at most the selected score; then
use row order plus the lex gate to rule out an equal-score earlier row.  That packages
`Satisfied2 -> OptimalLex -> Accepts`.

The isolated Rust surface already mints and verifies a real HidingFri proof and returns
`VerifiedAssignment`.  Six remote tests pass in 0.169s, including an admissible-but-suboptimal row,
an equal-score lex-later row, faithful root binding, score-zero distinct from inadmissible, and
public-statement tampering.  The descriptor remains intentionally unregistered until the final
`OptimalLex` bridge closes.  `docs/deos/PRIVATE-RAID-ASSIGNMENT-N4K4.md` is its focused ABI/security
record.

The engine weld now keeps the optimizer ABI small.  A surrounding protocol envelope binds the
audited eligibility-policy artifact/certificate, the private admissibility proof, the optimizer's
`input_root8`, and its exact rule/VK.  A verified result then grants the existing `dreggnet-party`
role capabilities atomically; it should not lossy-fold a policy digest into one BabyBear `session`
felt. `dungeon-on-dregg::private_raid` now carries the canonical receipt/VK and a one-shot
`RaidAssignmentSession`; `dreggnet-offerings` consumes the opaque receipt as a Dungeon operation,
and the shared web/Telegram/Discord path exercises it. This runtime/enactment closure does not erase
the final bounded Lean `Satisfied2 -> OptimalLex -> Accepts` residual named above.

## 19. Joint-entropy N=8 fair shuffle: exact unbiased accepted rank, temporal anti-abort still external

`Dregg2/Games/PrivateShuffleFairDescriptor.lean`, `EmitPrivateShuffleFair.lean`,
`circuit-prove/src/private_shuffle_fair.rs`, and `private_shuffle_fair_zk.rs` add the missing
sampling organ above §16's permutation checker.  Eight private 16-bit contributions add modulo
`2^16`; an attempt is accepted only when the entropy lies below 40,320.  Accepted entropy is used
directly as a permutation rank—never reduced with `% 40320`—so no modulo bias is introduced.

Lean proves exact equivalences
`AcceptedEntropy ≃ Fin 40320 ≃ Equiv.Perm (Fin 8)`, no duplicate/no omission, and that one honest
additive contribution is a bijection conditional on all fixed other contributions.  The public
statement is `(session, fair_rule, attempt, commitment_root8, accepted, deal_root8)`.  Seed
commitment leaves bind the participant, attempt, seed, and eight blindings; an accepted deal root is
byte-compatible with the existing private-shuffle framing, while a rejected attempt exposes a zero
deal root.

The descriptor has 823 columns, 20 public inputs, 1,026 constraints, and 30 full-width Poseidon2
lookups.  It enforces seed bits/recomposition, exact additive carry, accepted/rejected threshold
slacks, factorial/mixed-radix rank recurrence, the recursive `Perm.decomposeFin` selector, and final
row/column permutation gates.  Thirteen keystones are kernel-clean.  The artifact SHA-256 is
`43d010af24ffcd7cee9aa5af7e8d5e4919173411ba82c19c777606f7f66a3c52`; the faithful-commitment scan
passes.

Rust proves and verifies both accepted and rejected attempts through HidingFri.  Four remote tests
pass in 0.330s, including an exhaustive host enumeration of all 40,320 ranks, AIR rank/permutation
mutation, and seed/blind/attempt/root/acceptance tampering.

Two boundaries remain explicit.  First, the emitted `Satisfied2` facts still need their final
bounded modular-to-integer identification with the semantic seed/carry/threshold/factorial selectors
and both root trees.  Second, a static accepted/rejected relation alone does not prevent selective
abort. The executable layer now supplies that missing temporal shell:
`dungeon-on-dregg::private_fair_shuffle::FairShuffleTable` records all eight commitments before a
proof, reconstructs the exact commitment root, retains every rejected attempt while monotonically
advancing the counter, and refuses card openings before an accepted proof. The Dungeon Offering and
shared web/Telegram/Discord operation path carry its canonical receipt. Timeout/withholding policy
and distributed input production are still external; the current `PreparedFairShuffle` is Tier-1
and sees all contributions.

## 20. Policy decisions and graph rewriting are complementary semantic-web attestation backends

The live `Crypto/Deriv` tower has moved materially beyond the older audit documents:

- `SymbolicEquivalence` assembles language equivalence from symmetric-difference emptiness;
- `SymbolicMinterms` generalizes the hard-coded delimiter witnesses to per-guard symbolic covers;
- `SymbolicFixpoint` consumes `simDecide` in an adaptive similarity-deduplicated worklist;
- `EquivalenceFixpoint` makes equivalence kernel-runnable on real examples;
- `SymbolicMintermsPlus` closes `symMemberOf`, semantics-preserving `allOf`/`anyOf` desugaring, and
  scoped correlated `digFieldEq` covers;
- `PredicateLibrary` exposes role/status/reference/owner and boolean policy combinators with actual
  satisfiable/contradictory/equivalent/not-equivalent examples.

This is the authoring/audit organ: “is my guild/quest/raid guard contradictory?” and “did this edit
change the accepted histories?”  It does not by itself hide the player's state.  For hidden state,
the exact audited policy identity and its VK bind a Hiding/FHE/MPC relation which reveals only the
authorized result.  Cells and receipts then make the result temporal and enforceable.

The rewrite side is more general than a word guard.  `Crypto.Chain` proves
`(exists c, Cert R start goal c) <-> ReflTransGen R start goal` for any relation.  DFA acceptance,
VPA acceptance, CFG production, pushdown replay, hyperedge replacement, and contextual graph rewriting
all reuse that substrate.  `Crypto.GraphRewrite` has genuine pattern homomorphisms/embeddings and a
match-driven contextual `RewriteStep`: select a licensed rule, instantiate its variables, preserve a
context, delete the matched LHS, and glue the RHS.  `graphRewrite_bridge` lifts chains of those steps
to semantic reduction.

Do not confuse the two hypergraph layers.  `Crypto.Hypergraph` is the rewrite-certificate carrier;
`Dregg2.Hyperedge` is the N-party atomic-turn apex.  The latter binds all legs to one turn id and one
aggregate conservation equation, and `Apps.SheafHyperedge` proves agreement gives distributed
knowledge while a fork has no shared apex.  Together they support the intended distributed
operation: privately prove a valid semantic rewrite, then enact its N-party resource/capability
effects atomically.

`Crypto.GraphRewriteHistory` now supplies the receipt/history bridge.  A certified step's public
ABI is `(session, rulesRoot, index, oldRoot, newRoot)` while its semantic graph openings and
`RewriteStep` proof remain witness-side.  Links require the same session/ruleset, an exact `+1`
index, and equal adjacent roots.  Unconditionally, a linked history yields either a genuine
semantic reduction/common `Cert R` or an explicit commitment collision; an explicit binding
carrier removes the collision branch.  A same-root/different-graph splice constructs that collision
directly.  Wrong session, rules root, index, or public endpoint refuses.  The registered module has
13 kernel-clean keystones (`/tmp/graph-rewrite-history-lean.log`).

The first private bounded rewrite leaf is now built as an isolated, generated lane.  Its precise
semantic scope is **injective match-driven bounded hyperedge replacement**, not categorical DPO:
RHS-only freshness and the dangling condition for LHS-only variables remain explicit follow-on
teeth.  `Crypto.PrivateGraphRewrite` carries four host-edge slots, two LHS/two RHS slots, two
preserved-context slots, four variables/nodes/labels in `Fin 16`, a complete private two-rule
ruleset opening, an injective substitution, nonempty selected LHS, old-edge permutation, and the
exact canonical new endpoint `context ++ instantiated RHS`.  It proves the step refines the generic
`RewriteStep`, proves the selected match is an `Embeds`, and reduces distinct accepted old/new/rule
openings to explicit full-eight-lane digest collisions.  Seven keystones are kernel-clean.

`Crypto.PrivateGraphRewriteDescriptor` is the Lean-authored IR2 relation.  Its public ABI is
`(domain, session, version, shape, index, rulesetRoot8, oldRoot8, newRoot8)`; old and new graph roots
share one graph-state domain tag, so adjacent receipts can reuse the exact new opening as the next
old opening.  The descriptor is width 310 / height 4 / 29 public inputs, with nine full-width
Poseidon2 lookups and eighteen faithful four-bit range lookups.  It opens both private rules and
their blindings, selects one rule privately, proves six inverse teeth for substitution injectivity,
uses the fixed six-comparator network `[01,12,23,01,12,01]` for arbitrary old-edge order, and pins
the canonical new endpoint directly.  Transition gates are duplicated at the last row.  The
generated artifact is `circuit/descriptors/by-name/private-graph-rewrite-4x2.json`, SHA-256
`d2b56d7e601cb65ad06fb98fa78efb048f4c78fa1d575726c15166a715cdd2c7`; twelve descriptor keystones
are kernel-clean.

The `Satisfied2` bridge is materially past raw modular gate extraction but not yet the final
`Accepts` theorem.  `privateGraphRewrite_decoded_air_sound` proves every control is an honest
integer bit, every range-routed label/node/substitution cell is in `[0,16)`, all nine eight-lane
digest blocks are the genuine wide-chip outputs, and every canonical PI binding is exact.
`controlledSwap4_perm` and `six_controlled_swaps_perm` prove that the authored network preserves the
four-slot multiset.  The exact remaining formal residual is finite: lift each source/stage equation,
package the canonical padded columns as `PrivateWitness`, and identify the resulting `List.Perm`
and digest equations with `Accepts`.  Do not report this checkpoint as the closed
`Satisfied2 -> Accepts` theorem.

The isolated Rust filler/prover is `circuit-prove/src/private_graph_rewrite.rs`.  It validates the
bounds and canonical padding, derives the six old-edge swap controls by exhaustive 64-mask search,
fills the exact 310 columns/nine hashes/eighteen ranges, constructs the 29-felt statement, and uses
HidingFri with exact descriptor/config/VK fingerprints and postcard verification.  An external
module harness compiles in 14.04s; four focused tests pass (0 fail, 2.75s test execution, 17.98s
total wall), including proof/verify/postcard/tamper and a fixture with `sigma[0] = 4` plus an inactive
selected LHS slot.  That fixture found a real descriptor completeness bug: inactive rule padding
had still muxed `sigma[0]` into staged endpoints.  The Lean AIR now active-gates instantiated
source/destination fields, so inactive slots are canonical zero without restricting the semantic
witness; the regenerated SHA above and all four tests cover the repair.

The remaining deployment boundary is integration rather than invention: the new Rust module is
not yet exported from `circuit-prove/lib.rs`, and the descriptor/prover is not yet in the shared
emit/registry/custom-carrier path or folded into receipt history.  The deployed parse circuit
remains the one-bracket Dyck/CFG instance.  Adjacent old/new roots in this leaf are nevertheless the
exact intended segment endpoints for arbitrary folded rewrite histories once those integrations and
the final finite Lean packaging theorem land.

## 21. Executable board after this handoff

These are active technical closures, not a sequential schedule:

1. **Graph-rewrite leaf:** the bounded semantic relation, Lean-authored AIR, exact generated
   artifact, isolated Rust witness/HidingFri prover, fingerprints, and four focused positive/tamper
   teeth are built and green.  Next close the finite
   `privateGraphRewrite_decoded_air_sound -> Accepts` packaging, add explicit wrong-match/context/rule/root
   AIR mutations, then export/register the coherent module and consume its adjacent roots through
   the faithful custom carrier.  Preserve the exact scope: injective contextual hyperedge
   replacement now; DPO freshness/dangling later.
2. **Faithful custom carrier consumer gates:** the RotationV3 VK8 widening, targeted registry
   regeneration, exact leg-to-leaf VK8 connection, honest private-preference fold, and wrong-limb /
   wrong-root teeth are implemented and typecheck.  Run the ignored-heavy honest/refusal proofs once
   either test host has working disk capacity, then reuse this direct carrier for graph rewrite.
3. **Private raid semantics:** close the `Fin 24` dominance/lex bridge, register the descriptor, then
   consume `VerifiedAssignment` in a party/raid enactment that grants exactly the proved role caps.
4. **Fair shuffle semantics and temporal protocol:** close the modular-to-semantic theorem, register
   the descriptor, then add the commit-before-reveal/monotone-attempt/timeout receipt cell.
5. **Rewrite history and N-party enactment:** the generic same-ruleset/contiguous-index/root-linked
   semantic history theorem is built.  Connect the new rewrite AIR's public endpoints to that
   receipt ABI, fold them to one history proof, and use the N-party `Hyperedge` apex for balanced
   cross-cell effects.
6. **Playable surfaces:** private raid, fair shuffle, and the two-step private graph-rewrite quest
   are now mounted as Dungeon Offering operations and have shared web/Telegram/Discord transport
   tests. The encrypted-amount Dark Pool is a separate opt-in Offering with the same frontend
   adapters and an offline ciphertext-producer CLI. Private preference still lacks that hosted
   operation wrapper. None of this tree-local integration proves the live `arcade.dregg.net`
   deployment has been refreshed; deployment state must be checked separately.

The reuse rule is: retain existing identity, eligibility, custody, asset, capability, cell, receipt,
history, and frontend shells; author a fresh Lean relation when the old mechanic leaks the wrong
information or proves the wrong semantics.  Rewriting the entire engine is not required, but
reusing a public-ballot or coordinator-chosen core merely because its shell exists is also not
acceptable.

## 22. Encrypted-amount Dark AMM now has a one-bit MPC decision, durable certificate, and hosted game

`fhegg-fhe/src/dark_amm.rs` no longer requires plaintext swap amounts. `PrivateAppliedSwap` carries
encrypted post-reserves and an encrypted invariant; `try_private_swap_proposed` accepts bounded BFV
ciphertexts for `dx` and `dy`, computes `Enc(x') = Enc(x)+Enc(dx)`,
`Enc(y') = Enc(y)-Enc(dy)`, and one ct×ct `Enc(x'·y')`. Debug/public values contain neither amounts
nor reserves. A blind-house commit refuses to coexist with the old plaintext LP view.

The preferred commit path does not return a rejected product. `PartyMpcSession::equality` runs two
party-owned mod-`t` scalar shares through the same direct-peer/Beaver engine as the clearing circuit
and reconstructs one equality bit. `PrivateAppliedSwap::decision_session_nonce` binds that session to
public `k`, the exact invariant ciphertext, both candidate post-state ciphertexts, and their bounds.
`commit_private_decision` consumes the non-cloneable decision capability; a false bit holds state,
and a bit from any other candidate/session refuses. This runtime is still semi-honest, uses trusted
Beaver preprocessing, and does not cryptographically prove each party shared the correct masked BFV
opening.

`fhegg-fhe/src/decision_attestation.rs` supplies the durable companion that the in-process capability
deliberately lacks. The strict `FHDAR001` receipt binds candidate/session, equality-circuit shape,
reveal-only transcript digest, roster digest, and the released bit. A configured Ed25519 threshold
roster signs the exact domain-separated claim; full verification checks independent expected objects
before consuming a replay id. The wire carries no operand, product residue, ciphertext, Beaver
material, or party share. The real integration test drives encrypted candidate creation, actual
party-MPC equality, 2-of-3 signatures, wire round-trip, replay verification, and atomic commit in one
chain; focused release gate 1/1 passes (0.580s). Signatures authenticate roster agreement, not
malicious share validity.

`Market.DarkAmmDecisionReceipt` now authors the corresponding durable state machine in Lean. It checks
the independently reconstructed candidate/session/roster/triple/circuit-shape binding, injects the
signature verifier honestly as a cryptographic premise, consumes a fresh receipt id on either released
bit, proves a false bit holds the exact reserve state, and proves a true bit plus the separately refined
range certificate commits exactly `DarkAmmPrivateSwap.post`. `TrustedMeaning` is the explicit carrier
obligation: the authenticated equality bit must refine `invariantDecision`, and the range/source bit
must refine `dy <= y`; signatures are not falsely proved secure in Lean. Seven keystones are kernel-clean.

The hosted surface is `dreggnet-market::dark_amm_game`, operation id
`dark-bazaar.private-amm-swap.v1`. An external producer receives a public session/key/cap/sequence
context, encrypts `dx`/`dy` offline, and submits a canonical opaque request. The Offering pins
session, public-key identity, invariant, and sequence; journals the canonical request plus actor;
replays from the immutable origin; and discloses only accepted-move count. `dark-amm-tool` supplies
`keygen`, `public`, `public-id`, `cursor`, and `swap` workflows. The opt-in web registrar loads
`DREGG_DARK_AMM_SECRET_KEY_FILE` only from a regular non-symlink owner-only file on Unix, validates
persisted pk/sk/relinearization algebra, and otherwise refuses.

Hosted gates: market release integration 3/3 (atomic rejection, linked CLI-produced swaps,
restart/replay); shared web/Telegram/Discord E2E 1/1; combined
`dreggnet-web --features dark-amm-game,fhegg-settlement --release` check green. Its disclosure is
load-bearing: this particular playable host retains one BFV secret/relinearization key and can
technically decrypt reserves; the rejected raw product is visible inside that process; amount bounds
are caller-declared; and no ZK proof binds ciphertexts to the pool key. It is an executable encrypted
game boundary, not the no-single-viewer deployment claim.

## 23. Private market proof status was re-grounded at HEAD; a two-root AMM receipt relation is next

The older N4K4 status text was stale. `Market.DarkBazaarPrivateDescriptor` already closes the full
fixed-shape `Satisfied2 -> Accepts` chain in
`darkBazaarPrivateN4K4_descriptor_to_accepts`: canonical one-hot/order decoding, injective packed
book, bounded modular-to-integer lifts, exact demand/supply/volume columns, lowest maximizing price,
wide-Poseidon root semantics, and arbitrary external PI binding. All 18 keystones are kernel-clean.
The remaining N4K4 gaps are proof-authoritative source/ledger/allocation and no-viewer witness
production—not functional correctness of the fixed hiding relation. The source roadmap,
SDK-readiness note, focused N4K4 note, and `HORIZONLOG.md` were corrected in place.

`Market.DarkAmmPrivateReceipt` authors the corresponding AMM semantic target. Its public statement is
`(session,rule,k,oldRoot8,newRoot8)`. The bounded private witness contains `x,y,dx,dy` plus independent
old/new eight-felt blinds; the new state is derived, never freely supplied. Acceptance enforces
nonzero amounts, `dy<=y`, old `x*y=k`, exact `(x+dx,y-dy)`, new product `k`, two distinct full-arity
root preimages, and canonical blind representatives. It refines `DarkAmmPrivateSwap.Admissible` and
reduces distinct accepted root openings to explicit collision events without asserting finite-field
hash injectivity. Direct Lean check and aggregate `lake build Market` are green; 9 keystones are
kernel-clean. The exact IR-v2/HidingFri carrier and its full `Satisfied2 -> Accepts` theorem are now
built as recorded in §28; this paragraph must not be copied forward as a descriptor residual.

## 24. Authenticated `t<n` opening now proves the exact BFV share relation and smudge range

The quorum path is no longer authenticated transport around an unproved decryption share.
`fhegg-fhe/src/threshold/quorum.rs` anchors every custody share in coefficient-wise Pedersen
commitments constructed from the exact bivariate-VSS rows accepted at setup. A strict `FHQPv001`
certificate proves, in zero knowledge, the exact negacyclic/RNS decryption relation
`raw(c1*s_i) - p = q*k1` and `lambda*p + smudge - h = q*k2`. Aggregated Bulletproofs constrain the
signed smudge representation and both quotient families; a batched Fiat-Shamir Schnorr argument
binds the committed witness to the public share. The transcript binds DKG, custody identity and
index, opening, exact ciphertext, public `h`, declared bounds, and every relevant dimension. The
verified combiner rejects a missing certificate, so a legacy unproved share cannot enter the new
opening path.

This is a real correction to the earlier readiness ledger: decrypt-share relation and smudge-range
proofs are **built**, not a remaining feature. The complete 3-of-4 Descent/Dark Bazaar settlement
passed with six degree-4096 certified shares. Its measured release runtime was **1086.009 seconds**
(18m06s). That makes the current construction correctness-grade, not interactive-grade: proof
batching/compression, parallel proving, and proof-size work are now a central shipping blocker, and
the heavy test is deliberately excluded from the normal loop.

One scheduler-level optimization is already cut into the library:
`partial_decrypt_quorum_parallel` preflights exact selected-party presence/uniqueness, runs independent
custody states concurrently, preserves the canonical roster order, and retains each party's replay
machine. The focused legacy-share scheduling/refusal tooth passes 1/1 in release (0.665s). This removes
an accidental coordinator serialization point; it has not yet been substituted into and re-measured
against the 1086-second heavy path, and it does not compress any individual certificate.

The remaining custody seams are still load-bearing. Setup does not yet prove ternary/CBD shortness;
the public commitment publication/endorsement/complaint ceremony is not a distributed persistent
protocol; anti-replay state is in-memory; and direct internal mutation vectors for every exact
ciphertext/transcript/recommitted-share/range failure should be expanded. These are narrower claims
than “threshold BFV is done,” but they no longer include the exact decryption-share relation itself.

## 25. Encrypted bid source identity is welded through the real seal, transport, restart, and settlement

The bid source seam is now fail-closed at Tier 1. `fhegg-fhe/src/order_ingress.rs` supports an exact
deterministic BFV re-encryption opening. A configured, non-serializable source-verifier capability
checks the plaintext order and encryption seed against the supplied ciphertext under an independently
retained `(parameters, collective public key)` identity, then signs the internally recomputed binding.
That certificate binds actor, listing/session, signed-message digest, ciphertext digest, and BFV key
domain. Its digest is included in the actual sealed-auction `WriteOnce` commitment rather than riding
as detached metadata.

The market settlement path requires every board bid's exact adjacent
`(signed-message digest, ciphertext digest)` source pair exactly once. A freshly quorum-signed clearing
claim over a substituted ciphertext therefore still refuses before mutation. Canonical owning bundles
survive transport and journal restart, while legacy `TURN_BID` is explicitly `UnboundSource` for fhEgg
settlement. Focused exact-opening and adversarial gates, the sealed-auction substitution gate, transport,
restart/tamper, and the fast market feature suite are green (15/15 in the latter). Negatives include
order, ciphertext, actor, certificate/signature, internally inconsistent digest, wrong collective key,
wrong value/quantity/side/session, missing/duplicate source input, and corruption of the real ledger seal.

Do not call this lattice zero knowledge. The source verifier sees plaintext plus encryption randomness
and is trusted to attest the same opening; public replay deliberately omits the seed, while the current
CRAWL operator can still see the move log. The seller/listing supply residual named here has since been
closed: `ListingOrderSourceCertificate` nests the exact ask opening and adds an asset-bound signature;
`TURN_BIND_FHEGG_SUPPLY` commits it into reserved WriteOnce slot zero before bids; settlement requires
the listing pair plus every bid pair exactly once under one BFV identity. Listing/session/actor/asset/
value/quantity/ciphertext/key/seal substitutions, unbound supply, and post-bid listing all refuse. The
Descent fixture now uses the actual encrypted ask and actual loot asset, and transport/restart replay the
listing action. That former additive asset-cross seam is now closed at the exclusive one-host boundary:
§33 records the composed atomic apex and its restart journal. The remaining apex is a distributed
transaction across independently committing federation and asset ledgers, not another in-process weld.

## 26. Multiparty relinearization removes the assembled-secret-key seam from the n-of-n Dark AMM

`fhegg-fhe/src/threshold/relin.rs` now runs fhe.rs's real two-round multiparty BFV RelinKeyGen protocol
over the exact `ThresholdParty` shares that formed the collective public key. Each scoped party worker
reconstructs only its own fhe.rs `SecretKey`, retains its secret-dependent generator and private `u`
between R1 and R2, and emits only the typed protocol shares. `RelinKeySession` domain-separates its CRP
entropy from key generation and binds the exact keygen session, collective-public-key SHA-256 digest,
roster, timeout, and derived session id. The coordinator fails closed on missing/duplicate parties,
wrong session, substituted collective key, wrong phase, channel closure, timeout, or a party panic. No
API exposes a party secret or constructs the joint secret.

The load-bearing test drives a three-party collective key through that ceremony, performs a real
encrypted `41*7`, and obtains `287` only through Lean-pinned smudged threshold opening. The same key
then initializes the actual encrypted-amount `DarkPool`, evaluates the exact `60/70 + Enc(10)/Enc(10)`
transition, threshold-checks invariant `4200`, commits atomically, and independently checks encrypted
post-state `70/60`. Focused relin tests pass 2/2 in release (1.656s); the complete `fhegg-fhe` library
passed 101/101 with one deliberate skip, and the existing party-isolation tooth remains green.

This closes one precise no-viewer key-generation seam, not threshold relin as a finished deployment
protocol. Section 31 now records the authenticated/restartable public control transcript, while the
upstream algebraic shares remain typed and nonserializable. Malicious-share proofs, a canonical share
codec or proof commitment, party restart, dropout recovery, a `t<n`/quorum relin variant, and Lean
formalization remain open. Section 29 records the completed masked-boundary equality MPC and durable
one-bit decision receipt that replaced this section's earlier test-only scalar invariant opening.

## 27. Party MPC now has a strict-comparison organ, not only crossing and equality

`PartyMpcSession::less_than` adds a session-separated scalar circuit over the existing direct-peer
arithmetic ingress and Beaver engine. Each party owns only its two local mod-`t` shares. The circuit
performs exact reduction, evaluates the shared canonical-bit comparison, and reconstructs only
`left < right`; neither operand, residue, difference, nor bit decomposition enters
`ComparisonTranscript`. Equality and comparison input/preprocessing material cannot cross session kinds.

`AttestedComparisonReceipt` adds a separate `FHCAR001` wire/protocol/replay domain over the exact
comparison session, roster, circuit shape, reveal-only transcript digest, and released bit. A configured
threshold roster signs the exact claim; equality receipts cannot parse as comparison receipts. The focused
three-party tests cover equality, both strict polarities, zero, the upper 16-bit edge, 2-of-3 receipt wire/
full verification, and replay refusal; 3/3 release tests pass in 0.021s.
`Market.PrivateComparison` authors the corresponding Lean semantics:
strict comparison, bounded windows, the exact floor-invariant window `k <= P < k+postX`, stable
lower-score preference, same-decision declared-output equality, exact receipt binding, replay refusal,
fresh consumption, and authorized-bit refinement. Ten keystones are kernel-clean.
This is immediately reusable for private allocation/preference/matchmaking/range decisions. The runtime
remains semi-honest with trusted Beaver preprocessing and upstream canonical-range promises; it is not
yet a maliciously input-bound comparator service.

## 28. The private AMM receipt is now a Lean-emitted HidingFri proof, not only a semantic target

`Market.DarkAmmPrivateDescriptor` is the fixed 104-column / 19-public-input IR-v2 relation for the exact
receipt from §23. It range-checks 10-bit `x,y,dx,dy`, 11-bit `postX`, nonzero inverse gates, exact
`y=postY+dy` and `postX=x+dx`, both constant-product equations, and old/new applications of one
state-commitment-domain arity-16 wide root function. Consequently an accepted new-root preimage is the
next receipt's exact old-root preimage, rather than a domain-mismatched dead end. The complete canonical
trace/PI and `ChipTableSoundN` bridge closes
`Satisfied2 -> Market.DarkAmmPrivateReceipt.Accepts`; 19 keystones are kernel-clean. `EmitByName` now
registers the family, and its 36,280-byte JSON is byte-identical to the Lean emitter.

`circuit-prove/src/dark_amm_private.rs` exposes only hiding `prove_zk`/`verify_zk` APIs: there is no
non-hiding convenience path. `PrivateAmmWitness::try_new` constructs the exact statement and refuses
malformed relation, overdraw, zero amounts, and noncanonical values. Focused release tests pass 2/2,
including honest proof/verification, randomized reproof, and changed old root/new root/`k` refusal.
This closes functional and proof-carrier correctness for the fixed hiding relation. Section 32 records the
subsequent hosted proof/root weld and strict offline producer lifecycle; §34 records the opt-in exact Tier-1
BFV↔HidingFri same-opening authority. The current prover/operator still sees the witness even though ordinary
proof consumers do not, and distributed/no-single-viewer witness production remains later work.

## 29. Collective-key Dark AMM acceptance no longer scalar-opens the invariant

`fhegg-fhe/tests/threshold_relin_dark_amm_decision.rs` composes the real privacy path in one executable
chain: three opaque `ThresholdParty` shares form the collective BFV key; the two-round multiparty ceremony
forms the relin key; reserves and `dx/dy` remain ciphertexts; only a one-time-padded invariant is threshold
opened; mask-owning parties locally derive mod-`t` shares; direct-peer equality MPC releases one bit; a
configured 2-of-3 roster signs the strict `FHDAR001` receipt; full verification consumes replay state; and
`commit_private_decision` atomically advances the ciphertext pool. The acceptance/refusal test imports no
`SecretKey`, never calls `threshold::combine` or `try_decrypt`, and never reconstructs the raw invariant.
The accepting chain now serializes and restores `SnapshotReplayGuard` before asserting the same receipt
is refused, so restart continuity is exercised rather than only process-local duplication.

The negative chain submits a wrong encrypted quote, obtains a false bit and residue-free refusal, and
checks byte-identical ciphertext state. A fully valid receipt/decision for candidate A cannot authorize
candidate B. Combined relin plus decision gates pass 4/4 in release (1.792s); the decision composition alone
passes 2/2 (0.903s). The remaining deployment boundary is n-of-n, in-memory/semi-honest masking and MPC,
trusted shape-only triples, and signatures that authenticate roster agreement rather than malicious
ciphertext/share correctness. This is the actual no-scalar-opening algorithmic composition, not yet a
real-process hosted committee.

## 30. Replay guards have a strict restart snapshot instead of only process memory

`SnapshotReplayGuard` is a reusable canonical replay-set carrier for clearing, equality, and comparison
receipts. A caller-selected context digest prevents cross-game/verifier restoration; the wire binds a
revision, bounded sorted set of exact replay ids, exact EOF, and domain-separated corruption checksum.
Fresh acceptance increments the revision, canonical emission sorts independently of insertion order, and
restoration retains every prior refusal. Focused tests pass 2/2, covering restart roundtrip, duplicate
refusal, wrong context, every truncated prefix, corruption, and a checksum-recomputed noncanonical order.

This is the storage primitive, not a false rollback claim. The checksum is public, not a MAC; a malicious
storage operator could restore an older valid snapshot. A deployment must persist the snapshot in the same
transaction as the authorized state mutation and anchor revision/digest in monotonic, consensus-backed, or
otherwise rollback-resistant storage. Existing hosted consumers should now replace process-local guards at
their journal boundary rather than invent another replay codec.

## 31. Relin has an authenticated, restartable public control transcript—without faking an upstream share codec

`fhegg-fhe/src/threshold/relin/transport.rs` adds fixed-width Ed25519 envelopes for the honest n-of-n
relinearization ceremony. Every manifest binds the exact relin session, collective-public-key digest,
ordered signing roster, R1/R2 phase, party slot, predecessor transcript, and a nonzero party message ID.
The coordinator accepts each party once, rejects cross-session/PK/roster/phase and replay before mutation,
and derives R2's predecessor from the complete canonical signed R1 transcript. Its bounded snapshot retains
both signed round prefixes in canonical party order; recovery is under an independently supplied expected
session and replays every envelope through normal signature/phase validation, recomputes both transcript
digests, verifies an exact-EOF checksum, and can require an exact recorded manifest on live-party resend.
No snapshot contains a secret share, `RelinKeyGenerator`, private ephemeral `u`, or algebraic share payload.

The remaining seam is important and deliberately represented rather than papered over: fhe.rs 0.1.1's
public `RelinKeyShare<R1/R2>` has private fields and no public `Serialize`/`Deserialize`. A coordinator can
restart and restore its authenticated public transcript, but live parties must resend the typed public
share; the manifest ID cannot yet cryptographically bind that opaque value. Party restart mid-ceremony is
also unsupported because private `u` must survive R1→R2. Closing that requires an upstream canonical share
codec (or proof/commitment to the algebraic share) and persisted party-local protocol state. This work is
not `t<n`, dropout recovery, or malicious-share correctness. Its public checksum detects corruption, not
rollback; production storage must transactionally anchor the accepted snapshot/version. Focused release gates cover both-phase
serialize/restart/continue, exact recorded resend, every truncated prefix, trailing bytes, corruption,
forgery, cross-session/roster/phase, wrong predecessor, duplicate/replay, validly re-signed substitution,
and atomic no-mutation on every rejection; the existing real Dark AMM relin tests remain the algebraic-key
consumer gate.

## 32. The hosted Dark AMM and its offline private producer form a runnable root-continuous lifecycle

`dreggnet-market::dark_amm_game` now keeps the legacy encrypted-only
`dark-bazaar.private-amm-swap.v1` visibly separate from proof-required
`dark-bazaar.private-amm-swap.proved.v2`. A v2 request carries the exact 19-felt statement, canonical opaque
HidingFri proof, and BFV ciphertexts. The host pins session/rule/`k`/sequence/current root, verifies the proof,
runs the encrypted candidate gate, and only then advances ciphertext state, root cursor, sequence, and the
durable request/statement/proof digest journal. Restart replay rebuilds and rechecks that complete root chain.
The shared hosted-operation adapter exposes the exact same upload through web, Telegram Mini App, and Discord
Activity surfaces.

The offline producer no longer requires caller-authored Rust or an externally assembled witness. A fixed-width,
versioned, checksummed `DarkAmmPrivateState` retains `(hosted session, receipt session, k, x, y, blind)` and is
accepted by the CLI only from a regular non-symlink file with no group/other permissions. `private-init` binds
the opening to a bootstrap public session; `public-id-private` or `public-private` creates the proof-required
context at its exact computed root; and `private-swap` reuses the current blind, samples the successor blind,
proves the exact transition, and encrypts the same `dx/dy` in one process. It publishes one fsynced 0700
directory containing 0600 `request.dbam`, `statement.dbas`, `next-state.dbao`, and `authority.dbaa`, refusing
pre-existing targets. The successor state is promoted only after host acceptance; `proved-cursor` then advances
the public root and sequence for the next transition.

The owner-only authority file retains the full witness plus independent deterministic fhe.rs-0.1.1/StdRng
encryption seeds, and pins the exact statement/proof/request digests. Its validation reconstructs the statement
and byte-identical ciphertexts, so §34's `ExactBfvAmountOpening` can endorse the already-uploaded request without
reproving or re-encrypting. This eliminates accidental honest-producer divergence; the hosted mutation path
still needs to require §34's verified capability before calling that relation cryptographically closed. The
focused release lifecycle gate passes one end-to-end test with two real hiding-proof transitions and covers
wrong session, wrong state, invalid quote, stale state, loose permissions, checksum tamper, and output collision.

## 33. Authenticated fhEgg clearing and the exact Descent asset now share a crash-recoverable one-host apex

`DarkBazaarOffering::settle_fhegg_asset_atomic` no longer asks a game host to clear the encrypted auction
and then transfer its source asset as two independently fallible calls. It checks the exact source board,
session/BFV identity, certified result, quorum receipt, replay, listing asset, live owner, buyer balance,
escrow, and provenance against detached images. It executes `close + every reveal + resolve` as one real
four-action executor turn, then installs the already-validated economic world and replay image. Its public
receipt digest binds the claim and source commitments, source-certified `AssetId`, seller/winner/price,
before/after world digests, and exact executor receipt. Wrong asset, short buyer, wrong owner, substituted
source, injected pre-commit refusal, and replay all leave every live domain unchanged; the Descent
integration now consumes this apex instead of the former clear-then-cross pair.

The durable form adds a strict `Prepared -> MarketApplied -> WorldApplied -> Committed` journal. Its bounded
canonical `FHEGGJ01` record binds transaction and replay ids, the complete settlement audit, exact market
turn, before/after world images, receipt count, and—after executor application—the produced receipt hash.
Recovery accepts only the exact not-applied or fully-applied market/world images at each phase; a third
image fails closed. Re-entry advances only missing phases, so it cannot submit a second market turn,
transfer the asset twice, pay the seller twice, or consume the replay id twice. Alternate transaction ids
cannot reserve the same fhEgg replay id.

`FileAtomicSettlementJournal` is the production storage implementation rather than a test-only trait
fiction. Cooperating processes serialize CAS through an OS advisory lock; replay reservation and the
record map occupy one bounded, sorted 4,096-record snapshot; each mutation writes and fsyncs a temporary sibling,
atomically renames it, then fsyncs the directory. The kernel releases the separate lock inode on process
death, and a fresh journal object ignores any leftover temp file and reads only a checksum-verified strict
snapshot. The five injected boundaries—after prepare, market, world, replay, and committed record—drop the
old object, reopen the file journal, recover, then repeat recovery read-only. The complete focused default
gate passes 6/6 in 19.313s, including strict wire, cross-thread CAS, corruption, mismatch, rollback, and all
five crash boundaries. Nextest once marked the file-corruption process late-exiting despite success; its
isolated rerun passed 1/1 in 0.061s without that mark. A focused release attempt was stopped before tests
after 27 minutes rebuilding the unrelated broad Lean FFI closure; there is no release-test failure to hide.

This is durable recovery for one host with exclusive ownership of the mutable market, `TradeWorld`, replay
guard, and journal namespace. The host must restore those other three state images before invoking
recovery; the test simulates their exact surviving images rather than killing and restarting a complete
deployed process. Advisory locks cover cooperating writers, and the public checksums detect corruption,
not a malicious operator restoring an older valid snapshot. Consensus/monotonic anchoring and a shared
transaction across independently committed federation and asset ledgers remain open; do not describe this
one-host protocol as that distributed hyperedge. Rotation/archival beyond the file cap must preserve the
replay set in that rollback-resistant host state.

## 34. The private Dark AMM has an exact Tier-1 BFV↔HidingFri opening authority

The opt-in `fhegg-fhe/amm-input-binding` feature adds `src/amm_same_opening.rs` without pulling the
proof-production tower into fhEgg's default fast surface. `Tier1SameOpeningAuthority::endorse` is the only
reference signing path: before invoking the existing Ed25519 threshold signer, it deterministically
re-encrypts both `dx` and `dy` from their claimed fhe.rs-0.1.1/StdRng seeds under the exact collective key,
refuses zero or cross-amount-reused seeds, requires byte-identical canonical ciphertexts, requires those values to equal the private-AMM witness,
reconstructs the exact 19-felt Lean-authored statement from the same `x/y/dx/dy` plus old/new blinds, and
verifies the supplied HidingFri proof against it. Two or more independent issuers can then assemble the
existing strict threshold evidence; an issuer cannot obtain a signature from this API before all checks pass.

The fixed canonical claim binds the declared `Tier1IssuerVisible` grade, hosted session and sequence,
proof session/rule/`k`/old-root/new-root, complete BFV public identity, exact `dx`/`dy` ciphertext digests,
HidingFri statement/proof/Lean-descriptor digests, and exact issuer roster/verifier/threshold. Receipt
verification reconstructs every field from independently supplied ciphertexts, key, statement, proof, and
authority; verifies the proof and threshold signatures again; and consumes a durable replay slot keyed by
hosted `(session, sequence)` only after all checks succeed. The strict bounded wire refuses truncation,
trailing data, noncanonical signer order, and oversized authority sets. A verified host receives an opaque
`VerifiedAmmSameOpening` capability rather than any witness or encryption randomness.

This is a genuine exact same-opening authority and closes the immediate Tier-1 proof/input composition
seam; it is deliberately not described as lattice ZK or no-viewer. Every issuer sees `x/y/dx/dy`, both
commitment blinds, and both encryption seeds, and threshold signatures authenticate issuer agreement rather
than proving a malicious quorum ran the reference code; zero/reuse refusal does not certify caller entropy.
The HidingFri proof remains hiding from receipt
consumers. Snapshot replay detects duplicate acceptance across restart but still needs transactional,
rollback-resistant storage. The hosted state-mutation producer lane remains separate and must require the
verified capability before commit.

## 35. The exact-opening-required host transition now has a Lean-authored atomic law

`Market.DarkAmmBoundReceipt` models the v3 host boundary without turning a cryptographic implementation
claim into an axiom. `RequestVersion` separates proof-only v2 from exact-opening-required v3, while the
pre-state-indexed `ExactOpeningCapability` carries a public `SameOpeningClaim` plus two explicit obligations:
the exact replay slot is fresh, and some hidden witness satisfies both `DarkAmmPrivateReceipt.Accepts` and an
uninterpreted `CipherOpensTo` relation for the two exact ciphertext identities. Lean does not derive either
obligation from BFV bytes or signatures. The independent encrypted candidate gate likewise enters only through
`DarkAmmDecisionReceipt.TrustedMeaning`, supplied as an external refinement premise.

The structural `Binds` record pins request version, hosted and receipt sessions, sequence, complete proof
statement, rule, public `k`, old root, both ciphertext identities, both public BFV wrap-safety bounds,
authority roster/verifier/tier/threshold,
and the replay slot `(hosted session, old sequence)`. A build-enforced dependency pin keeps this equality layer
independent of the private-receipt checker, same-opening meaning, and decision verifier. The eight kernel-clean
keystones prove that v2 cannot reach acceptance; every accepting step retains all bindings; the exact fresh
slot is absent before and present after; accepted reserves/root/sequence/replay occupancy are one atomic state
derived under the private receipt and decision relations; accepted reserves refine the existing semantic
`DarkAmmPrivateSwap.commit`; accepted hidden amounts lie beneath both request bounds; refusal holds the
complete prior state; and no partial third outcome exists.

This is the formal host law, not yet a Rust-refinement theorem for the v3 implementation and not a proof of
BFV, HidingFri, or Ed25519 security. `lake env lean Market/DarkAmmBoundReceipt.lean`, the `Market.lean`
aggregate, and the Lean orphan gate are green; all eight named theorems pass both `#assert_axioms` and
`#assert_all_clean`.

## 36. The hosted Dark AMM now actually requires the Tier-1 exact-opening receipt

`dreggnet-market::dark_amm_game` now has a strict third operation,
`dark-bazaar.private-amm-swap.proved.same-opening.v3`. Its canonical `DBAMv003` wire contains an exact
proved-v2 body plus §34's `AmmSameOpeningReceipt`; neither v1 nor v2 bytes are ever reinterpreted as v3.
`DarkAmmGameOffering::demo_same_opening_required` and the explicit-reserve sibling install an ordered
`AuthenticatedQuorumVerifier` policy and expose only v3. The host reconstructs the exact BFV parameters,
public key, `dx/dy` ciphertexts, canonical HidingFri proof, statement, and public context from the submitted
body, then pins hosted/proof session, key, sequence, rule, `k`, roots, exact bodies, and issuer
roster/verifier/threshold before touching the encrypted candidate.

The existing game host owns one ordinary BFV key, so v3 records that identity honestly as
`n=1/opening_threshold=1` through a reproducible public single-host keygen marker. It is not described as
distributed key generation or no-viewer custody. The issuer quorum is a different axis: each Tier-1 issuer
sees the complete witness and encryption seeds, and its signature authenticates the exact re-encryption and
proof check. The `FHASO003` claim also authenticates the full canonical BFV parameter digest and both public wrap-safety bounds; the reference issuer
refuses a bound below the exact opened amount, while HidingFri proves ten-bit amounts and no-overdraw. The
host still technically can decrypt reserves/amounts and observes the rejected candidate product inside its
process. Bound soundness therefore closes at the same explicit Tier-1 trust grade, not at lattice-ZK grade.

Receipt replay is session-local and transactional with game mutation. Descriptor/journal preflight verifies
against a cloned replay guard; invoke verifies against another clone and installs it only after the encrypted
candidate commits. Refusal burns nothing. Offering verification and durable journal resume start empty and
replay every accepted v3 body, deterministically rebuilding both pool/root state and receipt replay state.
The operation receipt binds the v3 request, statement, proof, exact-opening claim, new root, and visible
single-host custody grade.

The producer side no longer needs ad-hoc glue:
`DarkAmmPrivateSwapAuthority::endorse_same_opening` reconstructs the exact public objects and produces one
issuer endorsement; `assemble_same_opening_request` assembles and pre-verifies the canonical v3 wrapper.
Separate `same-opening-endorse` CLI invocations consume protected owner-authority and raw issuer-key files
and emit only strict public `FHASE003` artifacts; `same-opening-assemble` verifies distinct quorum evidence
and emits `DBAMv003`. The commands enforce regular non-symlink owner-only secret inputs, bounded canonical
roster/key/artifact parsing, atomic create-new outputs, and no secret stdout. Remote protected channels and
long-running issuer services remain deployment work; the actual artifact boundary is executable.

The focused release gate `dark_amm_same_opening_game` passes 1/1 in 15.583s. It mints a real HidingFri proof,
uses independently seeded exact BFV ciphertexts, assembles a real 2-of-3 receipt, and accepts the game
transition end to end. It also refuses every v2 bypass, a receipt swapped from another valid ciphertext pair,
signature tamper, wrong hosted session/public key/sequence/`k`/old root, wrong issuer roster, duplicate/stale
submission, and verifies that all refusals leave the durable operation journal empty. Restart replays the
accepted v3 journal entry and refuses it again as stale without appending a second operation.

## 37. Strict v3 is a production feature and shared web/bot operation, not a hidden library mode

The `dreggnet-web` Dark AMM registrar now accepts a separate relying-party authority policy through
`DREGG_DARK_AMM_AUTHORITY_PUBLIC_KEYS` and `DREGG_DARK_AMM_AUTHORITY_THRESHOLD`. Root plus key without that
policy deliberately preserves proof-only v2 for generic research callers; root, key, ordered roster, and
threshold instantiate `demo_same_opening_required` and expose only v3. The aggregate
`public-shielded-games` server is stricter: once any Dark AMM field is present, all four must be present and
cryptographically instantiate before the process binds a socket. It refuses proofless v1 and proof-only v2
as public deployment configurations rather than silently weakening them.

The deployment examples and hbox script carry the same invariant. The script reads the env file as data,
requires both authority fields and both custody/root fields, retains the protected-key file/mode/size checks,
and validates the eight canonical BabyBear root lanes before building. `bash -n` and a full dry run are green;
no production secret was provisioned and no deployment was performed in this sprint.

The shared binary-operation adapter needed no Dark-AMM-specific transport fork. A release integration test
mints a real HidingFri transition, deterministic BFV amounts, and a real 2-of-3 exact-opening receipt; registers
strict v3 through the env-shaped production registrar; discovers the v3 name/media/disclosure on the web
catalog; confirms the Telegram Mini App and Discord Activity routes enforce their respective authentication;
submits the same canonical bytes through the web route; observes the exact-opening claim/proof receipt; and
refuses the duplicate. Proof-only v2 is absent from that operation catalog. The combined proved-v2/v3 web
gate passes 2/2 in 8.120s, and the aggregate deployment contract passes 3/3, including paired authority-policy
parsing and every private dungeon operation in the same host.

This makes the issuer-visible exact-opening Dark Bazaar genuinely player-facing and deploy-selectable. It
does not change §36's custody grade: the current table is still a single-key host, and the issuer roster sees
the witness. The next privacy upgrade is to replace that host key/equality opening with the already-executable
collective masked-decision path and real private committee transport, while retaining the same v3-or-later
version discipline and frontend-neutral operation envelope.

## 38. The public evaluator now restarts and commits without a host secret

`FHDAP002` canonically transports the complete public Dark-AMM evaluation image: full fhe.rs parameter
identity, collective public key, public relin key, `k`, caps, and both reserve ciphertexts. A restored
`DarkPool` takes no secret key and can build the next encrypted candidate. The candidate nonce binds the
exact encrypted pre-state, preventing an old authorized transition from rolling an advanced pool backward.
`dark_amm_attested` reconstructs the equality session from independent relying-party policy, verifies a
reveal-only `FHDAR001` quorum receipt, stages replay, and only then infallibly installs the ciphertext state.
The focused no-secret gate is 6/6 and the full normal fhEgg release gate is 170/170 (one named heavy test
skipped).

An adversarial audit found that the first public parameter digest omitted fhe.rs's error variance. The repair
is a protocol bump, not a silent reinterpretation: `FHDAP001` is retired, v2 hashes the complete canonical
parameter serialization, and variance-only substitution plus checksum-valid old-wire substitution fail
closed. Public accessors expose validated collective PK/relin bytes so downstream code never parses carrier
offsets. The carrier still cannot prove that PK, relin key, and ciphertexts share one secret domain or that
the initial hidden reserves multiply to `k`; creation evidence and rollback-resistant storage remain open.

## 39. Lean now authors the public-host, lifecycle, and two-authority state laws

`Market.DarkAmmPublicHost` has ten clean keystones for exact encrypted pre-state binding, stale refusal,
decision-nonce binding, exact after-state/replay installation, false/refused complete-state hold, restart,
and separate state-staleness versus receipt-replay sequential barriers.
`Market.DarkAmmPublicHostLifecycle` adds fourteen clean laws for exact staging, wrong/stale/false/replayed
commit refusal, exact successful commit, abandonment, complete restart, and no partial outcome.

`Market.DarkAmmCollectiveTwoAuthority` records the detail that mattered in implementation: same-opening and
FHDAR have independent replay domains. Ten clean laws prove stage consumes neither; `abandon (stage ...)`
restores the exact prior image; acceptance requires exact pending plus independently fresh, bound authority
capabilities; and one atomic commit installs candidate-after, advances sequence, consumes both exact replay
ids, and clears pending. Either replay, binding, or refusal holds the complete state. These modules parameterize
BFV, nonce hashes, signatures, MPC, and codecs rather than promoting their security to axioms.

## 40. A real two-phase collective Dark AMM game service exists

`dreggnet-market::dark_amm_collective` configures collective DKG identity, validated public material,
Tier-1 same-opening authority, and independent FHDAR policy without importing `SecretKey`, decryption, or
`threshold::combine`. Stage verifies the complete proof/authority and records exact pending work without
consuming either replay image. Commit re-verifies into two cloned guards, rebuilds the candidate against a
detached public-only pool, and atomically installs ciphertext material, root, sequence, both replay images,
and pending clear. `DBACv001` strictly checkpoints committed and pending state. The public commit receipt
names both authority claim digests.

The review caught a genuine liveness failure before the final gate: consuming same-opening replay at stage
would burn the sole `(hosted session, sequence)` slot, so abandonment could never be followed by a replacement.
The repaired implementation preserves replay at stage; abandonment restores the byte-exact pre-stage
checkpoint and restaging succeeds after restart. The focused release test is 1/1 (2.486s before the later
identity bump; 2.99s after it) using real 3-party DKG/relin, HidingFri, 2-of-3 exact-opening authority,
external FHDAR, refusal atomicity, both-side restart, and abandon/restage. Its reveal-only worker transcript
is simulated; the upstream 6/6 target is the real masked no-assembled-secret computation gate.

A second audit found full-parameter identity stopped at `FHDAP002`: producer session and same-opening claim
still omitted variance. `DBAPv003` and `FHAS{O,E,R}003` now bind the same canonical full parameters; DBAP
v001/v002 and FHAS v002 fail closed, and variance-only substitution is an explicit tooth. The common
non-AMM `BfvPublicIdentity` ABI was deliberately left stable. Core same-opening is 2/2; collective + issuer
CLI + hosted strict-v3 are 3/3 release. Initial carrier honesty, issuer-visible witness/seeds, malicious MPC,
and rollback resistance remain. The existing player-facing table is still n=1; the new collective service
has not yet replaced its shared operation registration.

## 41. fhIR exports one self-contained PSD-plus-KKT certificate

`FHQPB001` joins the exact scale-9 SDD/PSD admission witness to the exact-arithmetic fixed-point KKT residual
witness. Its standalone bounded decoder checks checksum before allocation, `n,m<=1024`, checked implied
vector sizes, nested `FHSDD001`, exact EOF/canonical replay, both independent checkers, equal scale, and
entry-for-entry equality of the two `P` matrices. Valid-checksum version/dimension/matrix substitutions and
KKT witness forgery fail. The fhir gate is 58/58 and fhir+solver is 164/164.

`Market.QpCertificateBundle` supplies the semantic crown with two clean theorems: same-matrix SDD transports
PSD to the optimizer problem, and SDD plus exact-zero KKT implies global optimality for every feasible point.
It explicitly does not turn the deployed positive-tolerance residual check into exact-zero KKT. Source-f64
averaging/rounding refinement, wire decoding refinement, authentication, and the residual-to-optimality bound
remain honest seams.

## 42. The shared player path survived the protocol hardening

After the `DBAPv003`/`FHAS003` cutover, the production-shaped web regression passes 2/2 release: a real
HidingFri/exact-opening request crosses browser identity, HMAC-validated Telegram initData, and Discord's
production ticket mint/verify handler (only external OAuth exchange injected), advances the exact root once,
refuses replay, and reconstructs from the journal. Telegram and Discord credentials remain non-interchangeable.
This confirms the existing n=1 strict table remains player-facing while the collective service is prepared
for the next shared-interface cutover; it is not a claim that collective custody has already been deployed.

## 43. The complete public-shielded web surface is green after source hardening

The final aggregate `dreggnet-web --features public-shielded-games` release gate exposed a stale generic
fhEgg operation fixture that still built ordinary visible listing/bid moves. The settlement boundary now
correctly requires the exact encrypted seller ask/asset and every bid to be certified and frozen into the
board, so the old fixture failed with `UnboundListingSource`. The repaired fixture drives real deterministic
BFV order encryption, exact re-encryption acceptance, the signed listing-source action, two signed
source-bound bid actions, the derived public BFV identity, and the resulting source digest through the same
browser/Telegram/Discord operation adapter. Its focused gate is green.

That aggregate run also found an independent Descent fixture generating a winning line from today's seed
while opening a fixed fixture seed. `demo_win_for_seed` now makes the dependency explicit; the demo builder
and devnet tests generate moves from the exact world they open, eliminating both seed drift and a UTC-day
boundary race. The complete public-shielded web package now passes 143/143 release, including fhEgg
settlement, strict Dark AMM v3, private preference/shuffle/raid/quest, web, authenticated Telegram, Discord,
restart, and the wider game catalog. The persvati run used the prescribed test-only `DREGG_REQUIRE_LEAN=0`
override because that build lane lacks the seeded Lean archive; this is test evidence for these paths, not a
shipping authorization for the marshal-only executor.

## 44. The optimizer bundle can be verified against an independently compiled fhIR problem

`FHQPB001` is no longer limited to internal consistency between its PSD and KKT halves.
`fhegg-solver::CertQpExact::verify_problem_binding` now compares every dimension and every entry of
the complete external `(P, q, A, l, u)` problem against the certificate. The fhIR boundary exposes
`verify_certified_qp(compiled, wire)`: it decodes the bounded canonical artifact, independently
rechecks both certificate families, binds them to the exact problem emitted by the supplied
`Compiled`, and returns a verified value carrying the program digest and exact primal/dual vectors.
It does not rerun ADMM or silently search for a replacement witness; this is a verify-not-find API.

Dimension, objective, constraint-matrix, bound, scale, and program substitutions are refusal teeth.
The focused gates were `fhir` 60/60 and `fhegg-solver` 107/107, including the exact external-binding
test. The existing floating-point source-to-fixed-point refinement and positive-residual
optimality-bound seams remain exactly as stated in §41.

Commit: `a1220dc91` (`fhir: verify optimizer certificates against compiled programs`).

## 45. Collective party custody has a strict restart image

Opaque `ThresholdParty` custody now has a bounded, checksummed, canonical restart carrier. Restore
reconstructs the exact party/session/CRP/parameter identity and refuses corruption, trailing bytes,
wrong party index, wrong keygen session, and parameter substitution. This closes evaluator restart
without reintroducing the convenience API that assembles all shares into one secret key.

This is still an in-process honest-party custody object. It is not an HSM/TEE integration, does not
authenticate an operating-system principal, and does not make n-of-n robust to dropout. Those are
separate transport/custody properties, not implied by a sound codec.

Commit: `687900c82` (`fhegg: make threshold party custody restartable`).

## 46. The collective decision is now a context-bound public work item

The staged collective AMM no longer asks an authority to infer what it is approving from a raw
candidate. `CollectiveDecisionTask` is a strict bounded carrier for the exact hosted session,
sequence, committed pre-root, public-material digest, same-opening claim digest, BFV parameter and
DKG identities, collective key, equality width/caps, and canonical encrypted candidate. Its digest
is the PartyMPC/FHDAR attestation nonce. A valid receipt for a different task, session, sequence,
root, rerandomized ciphertext, key, material image, or same-opening claim cannot authorize commit;
the older raw candidate nonce is deliberately not accepted in this contextual path.

While a candidate is pending, `CollectiveDarkAmmOffering` exports that exact public task as
`dark-amm.collective-decision-task.v1`. The generic Offering artifact boundary enforces bounded
names, media types, visibility, exact-session routing, canonical bytes, BLAKE3 digest headers, ETag,
and `no-store`; web, Telegram Mini App, and Discord Activity expose the same artifact rather than
three reimplementations. The collective deployment registrar replaces the secret-key table when
collective public material is configured. The end-to-end service test downloads the task,
re-parses it against independently held public material and context, runs the real masked worker,
and commits the returned two-authority bundle.

Focused gates: artifact host 2/2; web artifact adapters 3/3; contextual worker 2/2; collective
service 1/1; restart/atomicity 1/1. Public task bytes contain ciphertexts and public identities, not
reserves, masks, threshold secret shares, or same-opening witnesses. The worker is still an
in-process set of party threads with trusted Beaver preprocessing and semi-honest inputs; an
external-process command/transport, malicious share/input proofs, dealer-free preprocessing, and
rollback-resistant storage remain live work.

Commits: `ef807ade5`, `c2c9b6dac`, `a9a215027`, and `7b46e9e31`.

## 47. The party surface is a live shared capability game, not four demo names

`PartyOffering` now begins with an empty multi-identity lobby. Authenticated players claim the
Tank, Scout, Mage, and Healer seats, ready/unready/leave, and the first claimant launches only a
full ready roster. Every admitted formation mutation advances a real audit cell with a
`FieldDelta(+1)` revision and the complete 256-bit lobby-journal root. The launched roster lowers
into the existing capability-seated `dreggnet-party::Party`; identity, not a caller-supplied role
argument, chooses the player cell. Per-seat actions and signed fork ballots retain complete real
turn receipts and replay across `OfferingHost` restart.

Role contributions now carry executor-installed `WriteOnce` teeth. A repeated forged click reaches
the executor as marker `1 -> 2`, is refused there, and leaves both state root and receipt count
unchanged. The previous `1 -> 1` lowering would have vacuously satisfied WriteOnce and is gone.

The catalog split was corrected at the same time: inventories, craft, gear, and the other
identity-owned RPG surfaces remain private per-player hosts; `party` is a shared table. Web and
Telegram tests prove two identities see and mutate one roster, and Discord routes party through the
shared per-channel adapter. Focused gates passed for direct WriteOnce, hosted party (2/2), catalog
routing, and Telegram compilation. The web execution target and legacy fork targets encountered
the repository's then-fail-closed missing verified ML-DSA core before their test bodies; the
subsequent keygen guard repair at `49d2c8212` should be used for the next aggregate rerun rather than
laundering the earlier compile-only evidence.

Commit: `e7d473b74` (`games: host live shared capability-seated parties`). The immediate game
frontier is to make shielded preference/raid/shuffle results change later encounter authority and
resources, instead of remaining impressive but partially museum-like receipt panels.
