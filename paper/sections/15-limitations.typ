// =============================================================================
// Section 15: Limitations
// =============================================================================

#import "../defs.typ": lean
= Limitations <sec-limitations>

Present-tense facts about the system as it stands. Each is a property a reader
can check, not a roadmap.

*The host-context seam.* Some wire-effect families are executed by host Rust
whose verdicts are cross-checked against the Lean kernel turn-by-turn rather than
produced by it. For those families the host implementation is in the trust base;
the node reports the exact producer split live at `/api/node/producer`, and
guarantee R is stated over the verified entry, not over the host arms.

*Composition security is not machine-checked end-to-end.* The per-guarantee
theorems are kernel-pinned, and the cross-corner welds (executor $arrow.l.r$
circuit) are theorems; a universal-composability statement for the protocol stack
as a whole --- that the guarantees survive arbitrary concurrent composition with
adversarial environments --- is not yet a Lean artifact. The UC-shaped
scaffolding exists (`Crypto/UCBridge.lean`); the end-to-end statement does not.

*The value law is per-turn, not yet per-issuer-global.* Exact conservation
($Sigma delta = 0$ per asset, per turn, lifted to attested runs) is proven. The
stronger discipline --- the issuer carrying negative supply so every asset's
system-wide total is identically zero at all times --- is specified and probed,
but is not the deployed ledger discipline.

*Guard expressibility has stated edges.* The enforceable constraint grammar is
the relational and quantified closure of @sec-guards; its source-stated limits
(what a program cannot see) are quoted in the generated predicate catalog.
Causal and temporal guards --- predicates over the receipt trace rather than one
transition --- are designed, but the installable surface is the transition
fragment; trace-shaped rules are presently witnessed-predicate territory.

*The explain reading is rendering, not semantics.* The clerk's human-facing
explanation of a turn is a total, deterministic rendering of the term IR.
Totality and injectivity-on-semantics are the honest scope; natural-language
faithfulness is not a theorem and is not claimed as one.

*Liveness is exactly as strong as its carrier.* Safety guarantees are
unconditional modulo the cryptographic floor; liveness --- finality and
revocation-at-finality --- additionally rests on PostGSTProgress, eventual
synchrony. A partitioned network stalls finality; it cannot forge it.

*The verified executor does not yet run on the bare microkernel.* The seL4 image
(@sec-sel4) boots the microkernel root, an on-device STARK verifier, and the
directory-cell userspace, and retargets to a second architecture; the *executor*
protection domain --- the compiled Lean entry --- does not yet link for the
freestanding target. The wall is characterized (host object format; an
event-loop-coupled runtime initialization the pure executor path never reaches)
and the excision is a banked checklist, not an open question, but until it lands
the substrate's verified-compute organ on seL4 is the prover, not the executor.

*Rotated coverage of heterogeneous turns is staged, not total on the live path.*
The rotation discipline (@sec-proof-arch) proves equivalent enforcement and equal
published state for the rotated cohort, and the chained-cohort composition that
keeps heterogeneous turns proven is mechanized per leg; the live cutover of every
heterogeneous shape is staged beside the legacy path. Two effect kinds whose
circuits the current per-row arithmetization does not express resolve fail-closed
to the monolithic path rather than to a rotated descriptor.

*deos's compositor and pg-dregg's open edges are realization frontiers.* The
deos surface, affordance, membrane, and rehydration theorems are kernel-clean and
the rehydration and affordance stack ships; the certified compositor as a
sole-framebuffer protection domain is the frontier piece (@sec-sel4). In pg-dregg
(@sec-pg) the authorization and mirror tiers and the verified-store chain tooth
are live and circuit-free, and the embeddable executor runs the verified step
in-backend (it initializes post-fork and commits a conserving, executor-attested
turn); the named edges are the range proof-attestation (pending proof
serialization) and full in-backend *decoding* of an arbitrary submitted turn (the
extension does not yet link the turn codec, so the in-backend producer
reconstructs a conserving turn rather than decoding the submitter's envelope ---
the executor's verdict remains authoritative). Each is stated as a present-tense
fact a reader can check, with the live floor and the frontier marked.
