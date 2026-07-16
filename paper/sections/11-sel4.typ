// =============================================================================
// Section 11: dregg on seL4
// =============================================================================

#import "../defs.typ": lean
= dregg on seL4: capabilities all the way down <sec-sel4>

The firmament's strong properties (@sec-firmament) want a substrate that shares
its thesis: capability security by construction, enforced by the machine. seL4
is that substrate. A dregg image on seL4 stacks two capability graphs --- the
seL4 graph isolates the protection domains, and the dregg graph mediates the
cells inside them --- so the deployment is capabilities all the way down. The
stack is not a design sketch. The verified executor of @sec-realization ---
the compiled Lean kernel the node calls --- runs a real committed turn inside
an seL4 protection domain, and a six-domain node assembly builds with that
executor in its seat.

== Two capability graphs, one thesis

The deployment is a small assembly of protection domains under the seL4
monitor (`sel4/dregg.system`). Each domain holds only the capabilities its
role requires. The *executor* domain embeds the verified entry and holds
exactly two memory capabilities: read on the turn-input region and read--write
on the commit region. It holds no device capability. The *verifier* domain is
pure compute over bytes; it holds no prover authority, no storage capability,
and no network capability, and its only connection to the executor is a
one-way notification channel. "A verifier never calls back into a prover" is
therefore a property of the capability graph, not of code review. The
*persist* domain is the designated seat of the storage-device capability and
the only domain besides the executor that maps the commit region. The *net*
domain is the sole holder of the network-interface capability and touches
nothing else. The *ingress* domain runs the TCP/IP stack, checks a turn's
signature at the edge, and is the sole writer of the executor's input region,
so a badly signed turn never reaches the executor. An *application* domain
(the directory cell below) holds only what its factory minted. Ambient
authority is structurally absent, enforced by the memory-management unit and
the capability-derivation tree rather than by convention.

The stacking is mechanized, with a stated scope. The Lean development
transcribes the pure fragment of seL4's own abstract specification --- each
definition headed by its l4v source file and line range, pinned to l4v commit
`e2f32e54`, with `derive_cap` pure-ised by threading the `ensure_no_children`
verdict as a boolean --- and proves that the transcribed derivation never
amplifies conferred authority
(#lean("Firmament.SeL4Abstract.seL4_derive_cap_non_amplifying")). The one
opaque branch, architecture-specific capabilities, is a named hypothesis; it
is what an l4v arch-derivation proof discharges per architecture. The bridge
theorem
(#lean("Firmament.SeL4Abstract.dregg_executor_cap_authority_grounded_in_seL4"))
then derives dregg's own capability non-amplification --- the cap-authority
leg of the running-entry guarantee (@sec-assurance) --- from the seL4 lemma
rather than re-proving it on the dregg side. The derivation runs under a named
bridge assumption (#lean("Firmament.SeL4Abstract.SeL4DeriveNonAmpBridge"))
whose embedding-faithfulness obligations are carried as hypotheses, not
proved; an l4v-to-dregg refinement would discharge them. The authority
relabelling between the two vocabularies is total and injective on the eight
seL4 authority constructors dregg uses
(#lean("Firmament.SeL4Abstract.alpha_total_iff_used")); the remaining four
project into other parts of the model (memory access into the memory-checking
model, revocation into the registry, arch authority above dregg's level). So
one leg is grounded, by a named reduction; this is not a refinement of dregg
against l4v. Within that scope the two graphs are one discipline at two
scales: the same `granted ⊆ held` law that governs a delegated cell capability
governs a derived seL4 capability, which is the firmament's distance-parameter
claim (@sec-firmament) seen from the substrate.

== What boots

The executor domain is the central boot. Getting the compiled Lean kernel onto
the microkernel required rebuilding its runtime, and the port is itself a
checkable artifact (`sel4/dregg-pd/executor-pd/WALL.md`). The verified closure
rooted at the FFI entry is recompiled to ELF, excluding one metaprogramming
leaf that exports no runtime function. The Lean runtime is rebuilt from the
toolchain's own sources for a hosted musl target, with its event-loop library
replaced by a stub --- the pure entry takes bytes and returns bytes, so the
turn reaches no socket, file, or timer. GMP is cross-built; a small shim maps
the runtime's allocator onto musl `malloc`; the link closes with zero
undefined symbols. On that runtime, inside a protection domain booted under
QEMU, `dregg_exec_full_forest_auth` --- the exported form of
#lean("FullForestAuth.execFullForestG") with admission --- runs a committed
transfer turn: the nonce advances, a 30-unit transfer moves conservatively
across two cells, and a nullifier and a commitment register, with the same
accepted receipt the host build produces
(`sel4/dregg-pd/executor-rootserver/`).

The domain's cryptographic portals are real, not stubbed
(`sel4/dregg-pd/executor-pd/crypto-floor/`). Poseidon2 over BabyBear matches
the circuit's two-to-one hash; BLAKE3, the Poseidon2-derived nullifier, and
the keyed MAC match the transcript primitives; strict ed25519 verification is
the executor's own authorization check; the Ristretto255 value commitment is
byte-identical to the cell's; the note box's authenticated encryption opens
genuine ciphertexts and rejects tampered ones. The one portal that does not
compute is proof verification, and it fails closed (an unverifiable proof
rejects); the next subsection states why.

The partition above assembles into one bootable image with the verified
executor in its seat (`sel4/build/dregg-real.report.txt` lists the executor's
thread among the six domains). Fitting the roughly 280 MiB executor image
under the Microkit tool takes a one-function patch mapping image segments with
2 MiB pages. In the recorded assembly boot the executor commits its turn and
signals the persist and verifier domains, the persist seat observes the commit
signal, the network driver probes a real virtio-net device and brings the link
up, and the directory cell enforces its membership list, rejects a stale
compare-and-swap, and mints only the object shape its factory slot allows. A
separate two-domain image welds the executor to a display domain: the receipt
the executor writes drives a repaint in the viewer over a cross-domain
notification, so a verified commit in one protection domain changes pixels
owned by another (@sec-deos). The smaller bring-up rungs also stand: a minimal
banner domain, a structural verifier domain exercising the bundle-in,
verdict-out contract, and the banner domain retargeted to and booting on a
second instruction-set architecture (riscv64).

== Proof checking on the device

The verifier domain today boots, holds nothing beyond its notification
channel, and acknowledges the one-way executor-to-verifier edge
(`sel4/dregg-pd/verifier-stark/src/main.rs`). An earlier bring-up carried a
hand-authored STARK engine into this domain byte-for-byte and proved,
verified, and tamper-rejected a small arithmetization on the device. That
engine was deleted repo-wide when the Lean-emitted descriptor prover became
the single production path (@sec-proofs), and the vendored on-device copy went
with it. On-device proof *checking* is therefore not currently demonstrated.
The production verifier --- `verify_vm_descriptor2` over the emitted
descriptors (`circuit/src/descriptor_ir2.rs`) --- is a hosted workspace crate
on the Plonky3 stack, and it has not been carried into the `no_std` domain.
Until it is, the executor's proof-verification portal rejects rather than
passes, and proof checking for the seL4 deployment happens off the device,
by the same light client any other deployment answers to.

== What remains

Recomputed at the current tree, the remaining work is four named items. First,
on-device proof checking under the production prover: carry the descriptor
verifier into the verifier domain. The deleted demo shows the port shape ---
the same carry that moved the hand engine --- but the descriptor verifier's
dependency set is larger. Second, the persist seat is a stub: it maps the
commit region read-only and observes commit signals, and the storage-device
capability with a durable store behind it has not landed. Third, an externally
delivered turn end to end on the device: the assembly wires TCP ingress,
signature check, staging, and the executor signal, but the recorded boots
exercise the executor's compiled-in turn rather than one arriving over the
wire. Fourth, the bridge assumption's embedding obligations remain hypotheses.
Every domain named above boots; the four items name exactly the distance
between that and the full deployment.
