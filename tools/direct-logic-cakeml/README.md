# Independent direct-logic certificate checker

This directory is the first executable independence boundary for the
direct-logic pipeline. It reimplements the Lean-proved `DREG` v1 certificate
contract in small Standard ML, extends it to the live `DREG` v2 envelope, and
models both checkers in HOL4.

The acceptance rule is useful precisely because it is narrow: untrusted bytes
must decode under a known version, contain exactly one source and one target
prefix tree, have no trailing bytes, and claim the unique target reconstructed
from the source. Accepted source and target trees therefore have equal Boolean
semantics for every atom environment.

What is present:

- `SCHEMA-v1.md` and `SCHEMA-v2.md`: exact octet, tag, length, and resource-cap
  contracts;
- `checker.sml`: independent fail-closed SML implementation;
- `fixtures.sml` and `test_checker.sml`: golden plus malformed and
  non-canonical specimens;
- `live_checker.sml` and `test_live_checker.sml`: compositional `DREG` v2
  checker binding the embedded v1 certificate, atom bound, and exact live
  descriptor JSON bytes;
- `hol4/DirectLogicCheckerScript.sml`: HOL4 definition and kernel-checked
  acceptance-implies-semantic-equivalence theorem;
- `hol4/DirectLogicCheckerProgScript.sml`: proof-producing CakeML translation
  of the v1 HOL checker functions;
- `hol4/DirectLogicLiveCheckerScript.sml`: v2 definitions plus soundness and
  v1-compatibility theorems;
- `hol4/DirectLogicLiveCheckerProgScript.sml`: proof-producing CakeML
  translation of the live checker and certifier;
- `hol4/DirectLogicLiveMainScript.sml` and
  `hol4/DirectLogicLiveCompileScript.sml`: raw-stdin `accept`/`reject` wrapper
  and verified x86-64 compiler invocation.

The v2 checker does not trust a general JSON parser. It reconstructs the exact
live IR-v2 descriptor bytes from the accepted v1 source and compares the entire
section byte-for-byte. The fixture pins this emitter to Lean's
`demoDescriptorJson` literal.

What is not claimed: the hand-written SML file has not itself been proved equal
to the Lean function, and this is not an end-to-end verified
Lean-to-machine-code compiler. The HOL4/CakeML route instead supplies a second
formalization and proof-producing implementation of the small certificate
boundary. See `hol4/AUDIT.txt` for the exact completed build and native-export
status rather than inferring it from the presence of the compiler scripts.

Run the independent implementation tests:

```sh
cd tools/direct-logic-cakeml
poly --script test_checker.sml
poly --script test_live_checker.sml
```

Build the HOL4 semantic theorems, CakeML translation certificates, and native
export:

```sh
cd tools/direct-logic-cakeml/hol4
DREGG_CAKEMLDIR="$HOME/dev/CakeML" "$HOME/dev/HOL/bin/Holmake"
```

Audit the exported theorem tags in a fresh HOL4 process:

```sh
CAKEMLDIR="$HOME/dev/CakeML" \
  DREGG_CAKEMLDIR="$HOME/dev/CakeML" \
  "$HOME/dev/HOL/bin/hol" < audit.sml
```

The recorded clean build and theorem-tag audit are in `hol4/AUDIT.txt`.
