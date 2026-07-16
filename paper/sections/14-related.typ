// =============================================================================
// Section 14: Related work
// =============================================================================

#import "../defs.typ": lean
= Related work <sec-related>

Each stub names what dregg takes and where it differs.

*Object capabilities* @elang @eros. The authority model is Miller's: no ambient
authority, _connectivity begets connectivity_, rights amplification via
sealer/unsealers, the Granovetter introduction. dregg's contribution is to
mechanize the *production* law --- non-amplification and non-forgeability as
two-valued, axiom-pinned theorems over the running executor
(#lean("EffectsAuthority.introduce_non_amplifying"),
#lean("EffectsAuthority.amplifying_grant_rejected")) --- and to make every act of
authority receipt-disclosed, hence verifiable after the fact by a third party.

*Macaroons* @macaroons *and Biscuits* @biscuit. Caveated bearer tokens with
offline attenuation are the token lineage dregg inherits; HMAC caveat chains are
on the assumption floor, and token adapters point inward to kernel capabilities.
The difference is that dregg's caveat language is the same predicate algebra as
cell programs and circuit obligations --- an attenuation is checkable by the
proof system, not only by the issuing service.

*seL4 / l4v* @sel4. The methodological north star: a kernel whose specification,
implementation, and proof live together, with explicit statements of what is and
is not covered. dregg's analog of the refinement stack is the two-readings
discipline (executor $arrow.l.r$ circuit, welded per effect) plus the assurance
case organized by guarantee; its analog of the l4v assumption statement is the
eight-carrier floor. dregg verifies a distributed protocol substrate rather than
a microkernel, and its executable artifact *is* the verified Lean rather than
verified C.

*Mina and recursive-SNARK light clients* @mina. The aspiration "a chain you can
verify on a phone" is shared, and the light-client theorem is the same shape (one
root, recursive verification). dregg differs in what the proof witnesses: not
only consensus-rule validity but per-step authority, conservation, integrity, and
freshness --- the proof attests the protocol's semantics, not just its block
structure --- and the verified statement is about the same Lean kernel the node
executes.

*Bridges, IBC, and zk light clients.* Cross-chain systems answer "did this
happen on the other chain?" in three ways: a committee attests (Wormhole,
LayerZero, Hyperlane), each chain runs the counterparty's header verifier (IBC),
or a succinct proof of the counterparty's consensus replaces the header chain
(zkBridge, Xie et al.). dregg takes IBC's discipline --- the receiving side
checks for itself --- and the zk-bridge economy of checking succinctly, and
removes the vote entirely: outbound, a target chain's contract verifies a
Groth16 wrap of a dregg state transition directly (`DreggSettlement.sol` on the
EVM, with a CosmWasm twin verifying the same proof); inbound, holdings on a
foreign chain enter as consensus-anchored proofs while custody stays in the
holder's wallet. What the proof witnesses differs as against Mina: per-turn
semantics, not headers. The verifiers pass both polarities in test on a
development trusted setup; none is deployed to a mainnet.

*FRI soundness accounting* @fri. Deployed STARK practice reports soundness from
a parameter ledger: StarkWare's ethSTARK documentation (IACR ePrint 2021/582)
composes the commit-phase and query error terms as a minimum, with the
commit-phase term proved by Ben-Sasson, Carmon, Ishai, Kopparty, and Saraf
(BCIKS20, proximity gaps for Reed--Solomon codes) and improved from quadratic to
linear in the domain by its 2025 successor (BCSS25). The field convention of
quoting queries $times$ blowup / 2 plus grinding as _the_ soundness number keeps
only the query column and silently drops the commit-phase term. dregg's ledger
keeps the two columns separate as a theorem:
#lean("FriLedgerSound.query_ledger_does_not_determine_perFold") exhibits two
deployed configurations with identical query ledgers and different per-fold
postures, so neither column may stand in for the other. The same development
transcribes BCIKS20's commit-phase error so the reported bound under-approximates
the paper's term; the assurance case states the resulting numbers for the
deployed configuration.

*Ceptre and linear-logic programming* @ceptre. Reading state change as focused
proof search in linear logic informs the substance discipline (value as a linear
resource, verbs as structural rules). dregg fixes the dual orientation: search is
untrusted and lives at the edges (solvers, intent matchers); the kernel only
checks.

*Verifiable game state and autonomous worlds.* Dark Forest demonstrated
hidden-information play enforced by zero-knowledge proofs, and the MUD line of
on-chain game frameworks treats a game world as state whose rules the chain
itself enforces. dregg takes the ambition --- game state whose rules the
operator cannot bend --- and moves the guarantee's source: a game is a
factory-minted cell whose moves are ordinary turns, so authority, conservation,
and integrity arrive as inherited kernel theorems rather than per-title
circuits, and a finished run verifies under the same light-client check as any
other history. Hidden information is not a hand-authored circuit per mechanic
but the per-viewer projection whose non-interference is proved once (the
compositor stub below); a move a player could not see is absent from their view,
not encrypted within it.

*Blocklace / Cordial Miners* @blocklace @stingray. The ordering fabric: a signed
DAG with equivocation exclusion, leaderless finality, and finality tiers as a
lattice. dregg consumes it as the modal half of the step logic --- when facts
become common knowledge --- and gates finality on the verified rule; its
liveness enters the assurance case as the single PostGSTProgress carrier rather
than diffusing through the proofs.

*CapTP / OCapN* @capnproto. The session layer for distributed object
capabilities --- sturdy refs, three-party handoff, promise pipelining --- is the
lineage of dregg's session surface. The kernel-facing difference: a delivered
handoff is admitted only through a verified non-amplification gate
(#lean("AuthModes.captp_granted_le_held")), and session machinery is kept out of
the consensus-visible kernel (pipelining is turn composition; references are
capabilities in slots). The sturdy reference is also the unit dregg's
rehydratable surface ships: a persistable, attenuable handle to a witnessed
scene, behind a membrane that re-checks authority at reacquisition.

*seL4 capability description* @capdl. capDL writes a system's capability layout
down once so a loader instantiates it and the deployment is checkable at the
capability level. dregg's seL4 image places its cell-and-grant layout in the
same relation --- seL4 capabilities isolate the protection domains, dregg
capabilities mediate the cells within --- and grounds the attenuation leg of the
inner discipline in a transcription of seL4's own abstract specification, under
one named bridge assumption
(#lean("Firmament.dregg_executor_cap_authority_grounded_in_seL4")).

*Secure GUI servers* @nitpicker. The trusted-window lineage --- a minimal GUI
server that mediates input and labels output so domains cannot spoof or spy on
each other --- is where deos's compositor sits. A cross-domain compositor
_trusts_ its rendering process to provide isolation; deos _proves_ per-viewer
non-interference of the projection (#lean("Deos.noninterference"),
#lean("Deos.hiddenCell_absent")) and the frame property of the compositing
algebra (#lean("Deos.render_frame_property")). A window is a capability, so the
right to see is separated from the right to act by construction.

*Hybrid post-quantum migration.* Migration practice pairs a classical and a
post-quantum scheme and accepts only when both verify --- hybrid key
establishment in TLS (X25519 with ML-KEM) and dual-signature certificate
proposals --- on the argument that the pair is at least as strong as its
stronger half. dregg takes the pattern and mechanizes the argument: a hybrid
quorum certificate (an ed25519 vote quorum paired with FIPS 204 ML-DSA-65
signatures) is unforgeable if either half is
(#lean("HybridQuorum.hybrid_unforgeable_of_either")), and remains unforgeable
under a total break of the classical half --- the classical verifier replaced by
an always-accepting one (#lean("HybridQuorum.hybrid_survives_classical_break")).
A compact variant replaces the per-signer ML-DSA concatenation with one
committee-independent lattice threshold certificate whose unforgeability reduces
to MSIS (#lean("HermineHybrid.hermine_hybrid_unforgeable_of_either")). The
hybrid path is implemented and staged behind a scheme flag; it is not wired into
live consensus.
