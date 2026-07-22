# DREG direct-logic compilation certificate, wire version 1

This is the executable wire contract proved by
`Dregg2.Logic.CompilationCertificateBundle`. It is deliberately smaller than
the live descriptor certificate in `FiniteLogicDescriptorIR2`: version 1 binds
a Boolean source tree to a separately encoded target tree. The checker accepts
only the unique canonical lowering; it does not trust a claimed target.

All entries are unsigned octets. Multibyte integers do not occur in version 1.
Atom identifiers therefore range from 0 through 255.

## Envelope

| Offset | Field |
| --- | --- |
| 0..3 | ASCII `DREG`, bytes `68 82 69 71` |
| 4 | version, exactly `1` |
| 5.. | one source prefix tree, then one target prefix tree |

The target tree must consume the final byte. Unknown versions, invalid or
unknown tags, missing operands, values outside the octet range, and trailing
bytes are rejected.

## Source prefix tags

| Tag | Node | Following payload |
| ---: | --- | --- |
| 0 | atom | one identifier octet |
| 1 | top | none |
| 2 | bottom | none |
| 3 | not | one source tree |
| 4 | and | two source trees |
| 5 | or | two source trees |

## Target prefix tags

| Tag | Node | Following payload |
| ---: | --- | --- |
| 16 | input | one identifier octet |
| 17 | truth | none |
| 18 | falsity | none |
| 19 | inverse/not | one target tree |
| 20 | conjunction | two target trees |
| 21 | disjunction | two target trees |

The canonical lowering preserves tree shape and atom identifiers while mapping
source tags `0..5` to target tags `16..21`. Acceptance is exactly:

```text
version = 1  and  decoded_target = canonical_lower(decoded_source)
```

The golden top certificate is `44 52 45 47 01 01 11` in hexadecimal. The
larger policy and adversarial corpus live in `fixtures.sml`.

