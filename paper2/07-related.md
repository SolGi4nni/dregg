# 7 · Related work

Short, honest positioning; each stub names what we take and where we differ.

**Object capabilities (Dennis & Van Horn; Miller's E and ocap discipline).**
The authority model is Miller's: no ambient authority, connectivity begets
connectivity, rights amplification via sealer/unsealers, the Granovetter
introduction. dregg's contribution is to mechanize the *production* law —
non-amplification and non-forgeability as two-valued, axiom-pinned theorems
over the running executor — and to make every act of authority
receipt-disclosed and hence verifiable after the fact by a third party.

**Macaroons (Birgisson et al.) and Biscuits.** Caveated bearer tokens with
offline attenuation are the token lineage dregg inherits; HMAC caveat chains
are on the assumption floor, and token adapters point inward to kernel
capabilities. The difference is that dregg's caveat language is the same
predicate algebra as cell programs and circuit obligations — an attenuation
is checkable by the proof system, not only by the issuing service.

**seL4 / l4v.** The methodological north star: a kernel whose specification,
implementation, and proof live together, with explicit statements of what is
and is not covered. dregg's analog of the refinement stack is the
two-readings discipline (executor ⟺ circuit, welded per effect) plus the
assurance case organized by guarantee; its analog of the l4v assumption
statement is the eight-carrier floor. dregg verifies a distributed protocol
substrate rather than a microkernel, and its executable artifact *is* the
verified Lean rather than verified-C.

**Mina and recursive-SNARK light clients.** The aspiration "a chain you can
verify on a phone" is shared, and the light-client theorem is the same shape
(one root, recursive verification). dregg differs in what the proof
witnesses: not only consensus-rule validity but per-step authority,
conservation, integrity, and freshness — the proof attests the protocol's
semantics, not just its block structure — and the verified statement is
about the same Lean kernel the node executes.

**Ceptre and linear-logic programming (Martens).** The reading of state
change as focused proof search in linear logic informs the substance
discipline (value as a linear resource, verbs as structural rules). dregg
fixes the dual orientation: search is untrusted and lives at the edges
(solvers, intent matchers); the kernel only checks.

**Blocklace / Cordial Miners (Shapiro, Keidar et al.).** The ordering fabric:
a signed DAG with equivocation exclusion, leaderless finality, and finality
tiers as a lattice. dregg consumes it as the modal half of the step logic
(when facts become common knowledge) and gates finality on the verified
rule; its liveness enters the assurance case as the single PostGSTProgress
carrier rather than diffusing through the proofs.

**CapTP / Spritely Goblins / OCapN.** The session layer for distributed
object capabilities — sturdy refs, three-party handoff, promise pipelining —
is the lineage of dregg's CapTP surface. The kernel-facing difference: a
delivered handoff is admitted only through a verified non-amplification gate
(`captp_granted_le_held`), and session machinery is kept out of the
consensus-visible kernel (pipelining is turn composition; references are
capabilities in slots).
