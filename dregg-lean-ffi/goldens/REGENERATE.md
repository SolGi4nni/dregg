# `goldens/` — provenance & regeneration

Two goldens live here. `mina-devnet-block-540186.hex` is documented at the bottom; the rest of this
file is about `marshal-golden.txt`.

# `marshal-golden.txt` — provenance & regeneration

`marshal-golden.txt` is the **translation-validation golden corpus** for the hand-written Rust T8/T9
marshaller (`../src/marshal.rs`), Klein CRITICAL-2 (the Rust half). It is **emitted from the verified
Lean spec** — never hand-edited.

Each line is `KIND\t<name>\t<wire>`:

- `IN  <name>\t<wire>` — the bytes the **proved** Lean encoder `Dregg2.Exec.FFI.encodeWWire` produces
  for a shape-covering `WWire` (the T8 *encode* target). The Rust `marshal_turn_hosted` must reproduce
  each byte-for-byte.
- `OUT <name>\t<wire>` — the bytes the **proved** Lean output encoder `encodeWStatusOut` produces (the
  T9 *decode* target). The Rust `unmarshal_result` must decode each to the expected structured result.

The conformance gate is `cargo test -p dregg-lean-ffi --test marshal_conformance`
(`../src/marshal_conformance.rs`). It needs **no** Lean runtime — it compares the Rust marshaller's
bytes against this committed golden string. The two corpora (Lean `EmitMarshalGolden.inputCorpus` /
Rust `conformance_input_corpus`) are joined on `<name>`; a case present on one side only is a hard
failure, so they cannot silently diverge.

## Regenerate (after any wire-grammar change)

```sh
cd metatheory
lake env lean --run EmitMarshalGolden.lean > ../dregg-lean-ffi/goldens/marshal-golden.txt
```

Then re-run the gate:

```sh
cd ..
cargo test -p dregg-lean-ffi --test marshal_conformance
```

A diff in the gate after regenerating means the Rust marshaller and the proved Lean codec disagree on
bytes — a real seam bug to fix in `marshal.rs` (not in the golden). The golden is the proved reference.

## Coverage (what the corpus exercises)

- all 12 `allAuths` credential cases (10 `Authorization` variants + both `bearer` stark bools + 2
  **nested** `oneOf`);
- all 30 `allActions` arms (incl. the nested `exerciseA` inner array and `heapWriteA`'s signed digests);
- a **depth-2** delegation forest (`holder`/`keep`/`cap`/`sub` edges, a grandchild, caveats per node);
- **all 11** `WState` fields, multi-element, with `Value` recursion (nested record, `dig`/`sym`/`int`,
  an **escaped** field name), signed-negative fields, a top-level `dig` cell, escrows with `some`/`none`
  + bridge/resolved flags, an empty-rights swiss row, multi-entry `lifecycle`/`deathCert`;
- the host context (`diag` + a **populated** one with a non-empty freeze-set);
- the envelope's signed `fee` and the **optional** `,"block_height":N` arm (the `turn_blockheight`
  case, the only encoder branch the `block_height = 0` cases skip);
- a tier-3 ("coordinated") caveat;
- all three `TurnStatus` output codes (`status:0/1/2`) + the empty malformed-wire sentinel.

## Residual (NOT anchored by this gate)

- **Non-zero high digest bytes.** Every corpus digest is `Digest::from_u64(_)` (low 64 bits; high 192
  zero), so the Lean `Nat`-digest and the Rust `[u8;32]`-digest agree trivially. The *full-256-bit*
  path of `to_hex32_bytes` (a digest with non-zero bytes 8..32) is structurally exercised but never with
  non-zero high bytes; to anchor it, the Lean emitter would need the `Nat` equal to the big-endian
  interpretation of a non-trivial 32-byte array, and the Rust side a matching `Digest::from_bytes`. This
  is the cleanest remaining extension.
- **`block_height > 0` round-trip.** `turn_blockheight` anchors the *encoder*'s optional arm; the
  *round-trip* proof `CodecRoundtrip.parseWWire_encode` is stated only for `blockHeight = 0` (the
  deployed shape), and `Refine.lean`'s `export_refines_endToEnd` likewise — so block_height>0 is outside
  the proved-codec boundary by design, not merely untested.
- **The `MarshalError` paths** (negative wire-`Nat`, missing envelope field) are total-encoder guards
  with no Lean counterpart (the Lean types make those states unrepresentable); they are exercised by
  `marshal.rs`'s own unit tests, not by this Lean-anchored byte corpus.

---

# `mina-devnet-block-540186.hex` — provenance & regeneration

The 1,544 bytes of Mina **devnet block 540186**'s binprot `Protocol_state.Value.Stable.V2`, exactly
as a peer served them over `coda/rpcs/0.0.1`, rendered as lowercase hex (76 columns, whitespace
insignificant). It is **not** emitted by a Lean run like `marshal-golden.txt` — it is a transcript of
a real network object, and the same bytes are pinned in Lean as
`Dregg2.Bridge.MinaBinprotRealBlock.devnetBlock540186`.

It exists so the Samasika fork-choice route-through
(`mina_fork_choice_decides_on_real_devnet_bytes_through_the_real_ffi`, in `../src/bridge_lc_ffi.rs`)
can drive `dregg_mina_better_tip` / `dregg_mina_head_advance` on a REAL block through the Rust wire
builders and the C ABI. The Lean `native_decide` theorems `the_exported_gate_decides_on_real_devnet_bytes`
and `the_head_rolls_on_real_devnet_bytes` make the same assertions **inside** Lean; what the Rust
test adds is the four layers those theorems cannot see (archive facet, `cfg`, the C `_str` shim, and
the `hex_lower` encoding).

The test's SIBLING tip is derived, not stored: byte 1068 (the low byte of the 5-byte `0xfd`-form
`blockchain_length` beginning at 1067) is bumped `0x1a → 0x1b`, making a chain one block longer with
an untouched staking-lock checkpoint — so the pair is short-range and length decides.

## Regenerate (only if the pinned block changes)

```sh
python3 - <<'PY'
import re
src = open('metatheory/Dregg2/Bridge/MinaBinprotRealBlock.lean').read()
body = re.search(r'def devnetBlock540186 : List Nat := \[(.*?)\]', src, re.S).group(1)
nums = [int(x) for x in re.findall(r'\d+', body)]
assert len(nums) == 1544 and all(0 <= n < 256 for n in nums)
h = ''.join('%02x' % n for n in nums)
lines = [h[i:i+76] for i in range(0, len(h), 76)]
open('dregg-lean-ffi/goldens/mina-devnet-block-540186.hex', 'w').write('\n'.join(lines) + '\n')
PY
cargo test -p dregg-lean-ffi --lib mina_fork_choice
```

A red test after regenerating means the Rust route and the Lean gate disagree about the same bytes —
a seam bug, not a golden to edit.
