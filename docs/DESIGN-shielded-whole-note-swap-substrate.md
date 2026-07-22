# Shielded whole-note swap substrate: emitted relation and hard non-authority boundary

Status (2026-07-22): a Lean-authored DescriptorIR2 whole-note barter relation, exact checked-in
emission, distinct strict 100-lane FWS1 ABI, and code-owned HidingFRI producer/verifier exist. This
cut is **not the semantic ShieldedExactApexV4 relation and not standalone settlement authority**.
It omits the semantic apex's nineteen Dark-AMM lanes, twenty-seven ring lanes, and fixed
pricing/ring rule, in addition to the four witness welds below. Its Rust public/result types and
consequence domain cannot be converted into semantic-v4 authority without a future explicit
refinement/weld.

## Concrete artifacts

- Future semantic target (not implemented by this relation):
  `metatheory/Dregg2/Circuit/ShieldedExactApexV4.lean`.
- Emitted bounded relation:
  `metatheory/Dregg2/Circuit/Emit/ShieldedWholeNoteSwapSubstrateDescriptor.lean`.
- Canonical bytes:
  `circuit/descriptors/by-name/shielded-whole-note-swap-substrate-v1.json`.
- Isolated byte emitter: `metatheory/EmitShieldedWholeNoteSwapSubstrate.lean`.
- Strict public ABI and earlier binding substrate:
  `circuit-prove/src/shielded_exact_apex_v4.rs`.
- Actual witness filler, distinct public type, and opaque proof boundary:
  `circuit-prove/src/shielded_whole_note_swap_substrate.rs`.

The descriptor is
`shielded-whole-note-swap-substrate-v1::one-opening-aafi32-v1`: 15,611 main columns, two
constant rows, and exactly 100 public inputs. It contains no clear value or asset lane.

The narrow Lean gate is:

```sh
cd metatheory
lake env lean Dregg2/Circuit/Emit/ShieldedWholeNoteSwapSubstrateDescriptor.lean
```

The emitted bytes can be reproduced with:

```sh
cd metatheory
lake build Dregg2.Circuit.Emit.ShieldedWholeNoteSwapSubstrateDescriptor
lake env lean --run EmitShieldedWholeNoteSwapSubstrate.lean
```

## What the emitted relation proves

One selected hidden opening supplies all of the following in the same AIR witness:

1. two domain-separated Poseidon2 sponges whose sixteen field results are canonically decomposed
   into the full public sixteen-u16 nullifier plus constrained high limbs;
2. two domain-separated eight-lane sponges forming the sixteen-lane value/asset binding from the
   exact u64 value, asset, and hiding randomness limbs;
3. input zero of a fixed two-input/two-output whole-note swap;
4. output note one's exact value and asset; and
5. the value carried by the appended FNI4 linked exact leaf.

The bounded market rule transfers the counterparty input's complete value/asset to the selected
owner and transfers the selected input's complete value/asset to the counterparty owner. Per-asset
conservation is therefore structural for this whole-note swap; there is no host-computed scalar
conservation certificate and no `legacy_value_binding` authority.

Both output openings are hidden. Two domain-separated eight-lane hashes commit each output; FXO4
commits the ordered pair. The AIR derives the public output root rather than accepting it from the
caller.

The exact transition is a depth-32 binary linked-leaf AAFI. It authenticates the predecessor leaf,
rewrites its `next` pointer to the full derived nullifier, authenticates an FNE4 empty leaf at the
exact pre-count cursor, appends the FNI4 leaf, proves both middle roots equal, derives the successor
root, and proves the exact u64 count increment. FNI4, FNE4, FNN4, and FNS4 are distinct full-state
sponge domains. FWS1 binds the nullifier, wide binding, FNS4 endpoints, output root, historical
fields, and outer endpoints.

All semantic teeth are first-row boundaries; there is no last-row/height-one vacuity. Every hash
step is an unguarded state16 lookup, including all 128 binary tree nodes.

## What this relation does not prove

These are active security seams, not documentation niceties:

1. **Dark-AMM/ring semantics.** The nineteen Dark-AMM lanes, twenty-seven ring lanes, and their
   pinned pricing/ring rule are entirely absent. Whole-note conservation is not price validity,
   pool-invariant validity, or ring-clearing validity.
2. **Selected note membership.** `historical_note_root` is bound into FWS1, but this descriptor does
   not authenticate the selected opening against that root.
3. **Selected spend authority.** `selected_secret` drives the nullifier, but v1 does not derive
   `selected.owner` from that secret.
4. **Counterparty provenance.** The counterparty is constrained by the swap equations but is not
   authenticated as a historical note, market reserve, or output of an accepted FHE/MPC clearing
   relation. By itself, v1 permits a prover to manufacture that private opening.
5. **Outer transition semantics.** `before_outer_commit` and `after_outer_commit` are both bound in
   FWS1, but the state transition between them is not executed in this descriptor.

The accepted-apex/finalization composition can consume a verifier authority token; it cannot make
these absent relations true. Live settlement needs a new semantic relation with the market/ring
lanes and rule plus all four witness welds on the same opening and consequence before minting that
token. The Rust module therefore returns only an opaque substrate proof and its distinct FWS1
public statement, never a settlement-authority capability.

## Fixed 100-lane ABI

| Lanes | Meaning |
|---:|---|
| 0–3 | historical height, u64 as four little-endian u16 limbs |
| 4–11 | historical note root |
| 12–27 | full nullifier, sixteen u16 limbs |
| 28–43 | hidden value/asset binding, sixteen field lanes |
| 44–51 | derived successor exact root |
| 52–59 | derived prior exact root |
| 60–63 | pre-count, u64/u16x4 |
| 64–67 | derived post-count, u64/u16x4 |
| 68–75 | derived FWS1 consequence |
| 76–83 | derived FXO4 output-note root |
| 84–91 | before outer commitment |
| 92–99 | after outer commitment |

The producer derives every lane from the private witness. There is no API that accepts a detached
nullifier, binding, output root, or successor root for proving.

## Verifier and transport pinning

The proof boundary uses only `create_zk_config()` and exposes no caller-selected configuration.
The verifier identity commits to:

- the canonical typed DescriptorIR2 bytes parsed from the Lean-emitted JSON;
- the AIR fingerprint;
- the pinned Plonky3 revision;
- every exported HidingFRI/extension knob; and
- the canonical proving-system encoding.

Raw JSON is provenance and parse input, never program identity. A differential pin reorders the
top-level JSON keys and whitespace without changing the AIR fingerprint or final VK, while a typed
descriptor-field mutation changes both.

The opaque decoder has a hard byte ceiling, consumes the complete postcard input, requires the
canonical re-encoding, pins the proof instance/degree shape, and refuses a missing random
commitment or any missing per-instance random opening. Shape validation runs after proving, during
decode, and before verification.

## Cryptographic floor and remaining theorem work

The deployed floor is BabyBear + Poseidon2-W16 + HidingFRI. It is hash-based and plausibly
post-quantum in the usual conservative sense, but no reduction is claimed here. The remaining
formal/cryptographic work is:

1. a refinement theorem from emitted acceptance to the narrow whole-note relation actually deployed;
2. knowledge soundness for the pinned HidingFRI/Poseidon construction;
3. collision/preimage assumptions for the full-state sponge domains; and
4. the full semantic FXC4 relation (nineteen Dark-AMM + twenty-seven ring lanes and pinned rule),
   its Lean refinement, and the four live same-witness composition welds above, followed by one
   durable transaction for the exact frame, nullifier, output notes, and executor state.

No Ristretto/Bulletproof assumption is used by this emitted relation. Any surrounding classical
proof reintroduces a classical floor until it is replaced or joined through a proved native-PQ
same-opening construction.
