# DREW guarded witness envelope — wire version 1

`DREW` binds one already-guarded `DREG` v2 live descriptor certificate to one
Boolean assignment. All integers are unsigned 32-bit big-endian. Lengths count
octets. The decoder rejects malformed input, sections larger than 1 MiB,
non-Boolean witness octets, length disagreement, and every trailing octet.

```text
offset        size          field
0             4             ASCII "DREW" (44 52 45 57)
4             1             version = 01
5             4             DREG-v2 live-certificate length
9             4             witness length
13            live length   complete guarded DREG-v2 certificate
13 + live     witness len   witness octets, each exactly 00 or 01
end           0             no trailing data
```

The witness length must equal the atom count decoded from the guarded DREG-v2
certificate. The checker accepts only if:

1. the complete DREG-v2 certificate passes `check_live_bytes`;
2. its embedded DREG-v1 source/target certificate decodes canonically;
3. every witness octet is exactly 0 or 1; and
4. evaluating the decoded source under the indexed witness is true.

The existing DREG-v2 theorem then supplies source/target semantic equivalence
and exact equality between the claimed descriptor bytes and the descriptor
reconstructed from the source. The new HOL4 theorem
`check_witness_bytes_sound` concludes that both the source and lowered target
are true under the accepted witness.

This is the executable witness-checking boundary for the finite Boolean
descriptor family. It neither parses arbitrary DescriptorIR2 nor generates a
witness. The intended larger pipeline remains a typed Lean predicate DSL that
emits a live descriptor, a witness program, and a semantic certificate.
