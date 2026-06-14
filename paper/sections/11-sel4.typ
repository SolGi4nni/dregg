// =============================================================================
// Section 11: dregg on seL4
// =============================================================================

#import "../defs.typ": lean
= dregg on seL4: capabilities all the way down <sec-sel4>

The firmament's strong properties (@sec-firmament) want a substrate that shares
its thesis: capability security by construction, enforced by the machine. seL4 is
that substrate. A dregg image on seL4 is *capabilities all the way down* --- the
seL4 capability graph isolates the protection domains, and the dregg capability
graph mediates the cells inside them --- and it is no longer only a design: real
Rust protection domains boot the seL4 microkernel and run on it, including a real
cryptographic prover on the device.

== Two capability graphs, one thesis

The deployment is a small assembly of protection domains under the seL4 monitor.
Each domain holds only the capabilities its role requires, and the seL4
capability partition *is* the trust boundary the realization's crate split
already gestures at: an *executor* domain runs every turn through the verified
entry and holds no device capability; a *verifier* domain checks proofs and holds
no prover authority --- the kernel-enforced form of "a verifier runs in a separate
process with no callback into a prover"; a *persist* domain is the sole holder of
the storage-device capability, the only domain that can touch the disk; a *net*
domain is the sole holder of the network-interface capability, de-enveloping and
signature-checking a turn before it reaches the executor; and *application*
domains hold only the capabilities the firmament minted for them. A bad signature
never reaches the heart, no domain but persist can forge durable state, and an
application's ambient authority is structurally absent --- enforced by the
hardware memory unit and the capability-derivation tree, not by convention.

This stacking is mechanized. The seL4 capability model is given a Lean semantics
in which a derived capability is non-amplifying
(#lean("Firmament.seL4_derive_cap_non_amplifying")), and the bridge theorem grounds
the dregg layer in it: the executor's authority over a cell is grounded in the
seL4 capability that admits the executor domain
(#lean("Firmament.dregg_executor_cap_authority_grounded_in_seL4")). The two
graphs are one discipline at two scales --- the same `granted ⊆ held` law that
governs a delegated cell capability governs a minted seL4 capability --- which is
exactly the firmament's distance-parameter claim (@sec-firmament) seen from the
substrate.

== What boots

The bring-up runs as protection domains on the seL4 microkernel under emulation,
on a native toolchain. A minimal domain prints its banner; a verifier domain
takes a proof bundle in and emits a verdict, rejecting a tampered bundle; and a
directory-cell domain --- versioned content-addressed storage with a membership
list and a factory slot constraint --- runs the Robigalia userspace heritage layer
on the microkernel. The same domains retarget to a second instruction-set
architecture.

The load-bearing boot is the *on-device prover*. A verifier domain runs a real
STARK --- the BabyBear / FRI construction of @sec-proofs with BLAKE3 Merkle
commitments and a Fiat--Shamir transcript, carried from the host into a `no_std`
environment byte-for-byte --- proving a small arithmetization, verifying it on the
device, round-tripping its wire form, and showing the anti-tamper teeth: a tampered
proof and a wrong public input both reject. The prover is deterministic (Fiat--Shamir, no entropy source), so the
domain needs no randomness, no Lean, and no operating-system services. This is the
firmament's verified heart organ standing on the microkernel: real proof
generation and checking, isolated by seL4 capabilities.

== The one characterized blocker

The verified executor of @sec-realization is *compiled Lean linked into the
node*, and that is the one piece that does not yet run on the bare microkernel
target --- for two precisely characterized reasons. First, the compiled Lean
closure and its runtime archives are built for the host object format and must be
recompiled for the microkernel's freestanding target, not merely relinked.
Second, the Lean runtime's initialization pulls in an event-loop library coupled
to operating-system sockets and files, even though the executor path performs no
input or output: the pure entry takes bytes and returns bytes. The coupling is
concentrated and separable --- a handful of the runtime's objects carry it, named
by I/O concern, and the executor calls none of them --- so the excision is a
concrete checklist: recompile the closure for the freestanding target, stub the
two input-output initializers and the symbols the linker demands but execution
never reaches, provide bignum arithmetic for the target (or a fixnum shim if no
turn exceeds machine-word range), and host the result on the microkernel's
experimental libc shim. It is genuine runtime-porting work --- weeks to a quarter
--- and it is the single highest-risk item in the bring-up. Until it lands, the
substrate leads with the verified heart *organ* (the on-device STARK verifier) and
the userspace heritage layer rather than the full executor.

The honest summary is the one the firmament's status board states (@sec-firmament,
@sec-limitations): the microkernel root, the on-device prover, the
directory-cell userspace, and the second-architecture retarget *boot*; the network
edge *probes a real device*; and the executor protection domain has a
characterized wall with a banked excision plan, not an unbounded one. The
deployment that earns "capabilities all the way down" in full is the assembly with
the executor domain live; the deployment that runs *today* earns it for every
domain that boots, and names exactly what remains.
