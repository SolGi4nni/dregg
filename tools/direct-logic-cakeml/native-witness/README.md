# Native CakeML guarded-witness checker

This directory closes one concrete stage in the typed direct-logic pipeline:
an exact live descriptor certificate can now be paired with a Boolean witness,
checked by a HOL4-defined function, translated proof-producibly to CakeML,
compiled by CakeML's verified arm8 backend, and executed as a native arm64
binary.

The accepted pipeline is:

```text
Lean finite-logic predicate
  -> exact DescriptorIR2 JSON + DREG-v1 semantic certificate
  -> guarded DREG-v2 live certificate
  -> DREW-v1 Boolean witness envelope
  -> HOL4-defined checker
  -> proof-producing CakeML translation
  -> verified arm8 compilation
  -> native accept/reject process
```

This is the witness-checking side for the current finite Boolean descriptor
family. It does **not** generate witnesses, parse arbitrary DescriptorIR2,
compile arbitrary Lean terms, or use the superseded IR-v1 `CircuitEmit` route.
The intended extension point is a typed Lean predicate/circuit DSL producing
three coupled artifacts: live DescriptorIR2, a witness program, and a semantic
certificate. Future CakeML work should execute the generated witness program
and check its output under a generalized guarded descriptor interface.

## Assurance classes

- **Theorem-backed:** `check_witness_bytes_sound` proves that every accepted
  byte string contains a canonical DREG-v2 live certificate, exact reconstructed
  descriptor bytes, a Boolean row of the certified atom width, and a witness
  under which both source and lowered target are true. The checker theory has
  zero axioms.
- **Proof-producing translation:** `check_witness_bytes_v_thm` relates the HOL4
  checker to the CakeML deep embedding without a precondition.
- **Verified compilation:** `direct_logic_witness_compiled_arm8` is produced by
  kernel evaluation of CakeML's verified arm8 compiler and emits the assembly
  linked by the test script.
- **Translation/case validation:** the independent Standard ML twin checks all
  eight assignments of the three-atom policy plus 12 hostile/golden cases. The
  native CakeML binary checks the same eight-row truth table plus seven raw-byte
  framing/canonicality/tamper refusals. These
  cases are useful regressions, not universal proofs.
- **Cross-prover boundary:** the exact descriptor emitter is independently
  defined in Lean and HOL4/SML and pinned by the existing DREG-v2 fixture. No
  theorem transfers a Lean proof into HOL4; agreement at that seam is exact-byte
  translation validation.

See [SCHEMA.md](SCHEMA.md) for the wire contract.

## Reproduce

On an arm64 host with the local HOL4 and CakeML trees:

```sh
cd tools/direct-logic-cakeml/native-witness
DREGG_HOLDIR=/Users/ember/dev/HOL \
DREGG_CAKEMLDIR=/Users/ember/dev/CakeML \
  ./build_and_test.sh
```

The script builds the HOL4 theories, kernel-evaluates the verified arm8
compiler, links the emitted assembly against CakeML's Basis FFI, runs the
independent SML suite, emits hostile raw-byte fixtures, and executes all native
cases. Generated objects, assembly, fixtures, and the binary stay under ignored
paths.

Audit theorem tags and theory axioms in a fresh HOL process after the build:

```sh
cd tools/direct-logic-cakeml/native-witness/hol4
DREGG_CAKEMLDIR=/Users/ember/dev/CakeML \
  /Users/ember/dev/HOL/bin/Holmake --holdir /Users/ember/dev/HOL \
    DirectLogicWitnessAuditTheory.uo
```

The most recent captured run is summarized in [EVIDENCE.txt](EVIDENCE.txt).
