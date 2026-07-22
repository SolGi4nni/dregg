# DREG direct-logic live certificate — wire version 2

All integers are unsigned 32-bit big-endian.  All lengths count octets.  A
decoder rejects malformed input, a section larger than 1 MiB, an atom count
larger than 256, and every trailing octet.

```text
offset  size                 field
0       4                    ASCII "DREG" (44 52 45 47)
4       1                    version = 02
5       4                    atom_count
9       4                    v1_length
13      4                    descriptor_length
17      v1_length            complete DREG-v1 certificate
17+v1   descriptor_length    canonical EffectVmDescriptor2 JSON bytes
end     0                    no trailing data
```

The embedded v1 section uses [`SCHEMA-v1.md`](SCHEMA-v1.md) without alteration.
The v2 checker accepts exactly when all of the following hold:

1. the outer framing is canonical and within the resource caps;
2. the embedded v1 checker accepts;
3. every atom mentioned by the decoded v1 source is strictly below
   `atom_count`; and
4. the descriptor section is byte-for-byte equal to the canonical IR-v2 JSON
   reconstructed from `atom_count` and that source.

The reconstructed descriptor has one main table of arity `atom_count`, one
Booleanity gate `x_i * (x_i - 1)` for every column, and a final gate asserting
`P(source) - 1 = 0`.  The source polynomial is generated structurally:

```text
atom i  -> x_i              top       -> 1
bottom  -> 0                not p     -> 1 - P(p)
p and q -> P(p) * P(q)      p or q    -> P(p) + P(q) - P(p) * P(q)
```

The exact JSON encoding is deliberately part of the certificate contract.  It
has no insignificant whitespace, uses the field order implemented in
`live_checker.sml` and `DirectLogicLiveCheckerScript.sml`, and ends with
`"hash_sites":[],"ranges":[]}`.  A separately trusted JSON parser or digest is
therefore not in the acceptance path.

The HOL4 theorem `check_live_bytes_sound` proves that acceptance supplies the
decoded v1 source and target, an accepted v1 certificate, the atom bound, exact
descriptor equality, and source/target Boolean semantic equality for every
environment.  `check_live_bytes_v1_compatible` records the compatibility
projection explicitly.
