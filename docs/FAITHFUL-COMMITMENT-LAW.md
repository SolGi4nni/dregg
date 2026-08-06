# The Faithful-Commitment Law

**Every 32-byte component that flows into the deployed state commitment binds its
SOURCE at the system's own soundness strength — never a lossy 1-felt projection.**

⚠ That strength is **`2^123.63` of COLLISION** (`8 · log₂ p / 2`, the birthday bound over a full
8-lane image), not the `2^247.26` image size. This headline read "~124-bit, the 8-felt encoding"
for its whole life without saying which of the two it meant, and the ambiguity is load-bearing —
see *THE FLOOR, WITH THE BOUND NAMED* below, and the `2^120` object it let through.

## Why this is a law, not a preference

The deployed state commitment once carried components folded **32 bytes → ONE
BabyBear** (`fold_bytes32_to_bb`, a Horner fold). A single BabyBear is ~31 bits,
so two distinct 32-byte values collide with probability ~`1/p ≈ 2^-31`. That is
**far below** every column of the FRI knob ledger (`FriLedger.friLedger` /
`friCommitLedger`), whose weakest deployed reading is the commit column
(`FriDeployedHeightPairing.deployed_wrap_commitBits`, at `ir2_leaf_wrap_config()` /
`|D⁽⁰⁾| = 2^22`; the digit is in `docs/reference/PROVEN-120-CONFIG.md`). ⚑ Those are LEDGER READINGS, not a proven soundness floor: there is no
adversary object in the tree, and `FriLdtExtractV3` — the extraction guarantee the apex
actually consumes — is assumed. The former **arity-2 per-fold "proven floor"** claim here was
wrong twice: it quoted the arity-2 per-fold column
(`wrap_perFold_soundness_capacity`, `FriCorrelatedAgreementSharp.lean` §8) as if it were
the system's number, and the arity-8 leaf mint refutes it outright
(`FriArityTransfer.arity8_error_not_lt_2e112`). The FRI capacity conjecture that once
quoted ~130 is refuted — see `FRI-PARAM-FRONTIER.md`:
an adversary who can grind a 31-bit collision can show a light client a forged
committed state that the proof still accepts.

The insidious part: **a bare `BabyBear` limb carries no evidence of
faithful-vs-degraded.** A faithful 8-felt binding and a degraded 1-felt fold are
the same type (`BabyBear` / `[BabyBear; …]`), so a lossy fold slid into the
commitment silently and was only found by a **bit-audit months later** — then
cost weeks to grind back to faithful 8-felt. The cost of catching it at write
time is one CI second; the cost of not catching it is the months-to-weeks loop.

See the historical analysis in `.docs-history-noclaude/FAITHFUL-STATE-COMMITMENT.md`
and the memory note *Don't Launder a Load-Bearing Insecurity*.

## The rule

- **Degraded (forbidden in a commitment position):** `fold_bytes32_to_bb(x)` —
  32 bytes → 1 felt. IMAGE `2^30.9`; COLLISION `2^15.45`. Defined in
  `circuit/src/effect_vm/helpers.rs`.
- **Faithful (required):** an octet whose COLLISION bound clears the floor —
  `[BabyBear; 8]` and its hash-domain siblings (`hash_many` over 8-felt groups). The commit
  binds the **source**, not a degraded projection of it.

### ⚠ THE FLOOR, WITH THE BOUND NAMED (corrected 2026-08-01)

This document has quoted "~124-bit, the 8-felt encoding" since it was written without ever saying
*which* bound that is, and the omission is what let a `2^120` object in through the front door.
The arithmetic, once:

| quantity | value | what it is |
|---|---|---|
| `p` | `2013265921` | BabyBear, `2^31 − 2^27 + 1`; `log₂ p = 30.907` |
| 8-lane IMAGE | `2^247.26` | `8 · log₂ p` — the size of `[0, p)^8` |
| **8-lane COLLISION** | **`2^123.63`** | `8 · log₂ p / 2`, the birthday bound. ⚑ **THIS is the "~124-bit" floor.** |
| 9-lane CAPACITY | `2^278.16` image / `2^139.08` birthday | ⚠ what nine lanes can HOLD — the CODOMAIN. **Not** the numbers of any encoding; see the row below and the tell beneath the table. |
| 32-byte source | `2^256` | ⚑ `> 2^247.26`, so **no** 8-lane encoding of 32 bytes is injective, under any chunking |
| base-`2^29` NONET | image **exactly `2^256`**, **INJECTIVE** | the nine-lane encoding actually recommended (`Dregg2.Circuit.KeyLanes9.keyToLanes9`; `keyToLanes9_injective`, total decoder + machine-checked left inverse). **No encoding collision exists**, so the encoding step loses nothing and the binding reduces to the sponge. |

⚑ **The tell, and it is one comparison.** This document priced the ninth key lane at "`2^278.16`
image" — a figure LARGER than `2^256`. A map out of 32 bytes has at most `2^256` images, so
`2^278.16` cannot be one; it is the codomain's size. Quoting it as an image, in the very section
below that forbids quoting the flattering number of a pair, is the house error reappearing inside
its own correction. ⚠ **Say which bound, every time, in every string.** `2^278.16 / 2^139.08` are
correct *as a capacity* and are wrong *as this encoding's strength* — the encoding is injective, so
its encoding-collision cost is not a birthday number at all.

Two consequences that were not being drawn:

1. **The floor is a COLLISION bound, so anything compared against it must be quoted as one.**
   Quoting an image size where a birthday bound is meant is *the house error* in this tree — it is
   how `compute_effects_hash_4` came to claim ~124 bits for a `2^15.5` object, and how
   `from_canonical_key`'s "240 bits total, faithful" read as a pass.
2. **Reaching the floor takes more than eight lanes; it takes eight lanes that are hard.**
   `bytes32_to_8_limbs` has the full `2^247.26` image and a collision cost of **`0`** — `2p < 2^32`,
   so a colliding sibling is CONSTRUCTED by adding `p` to a 4-byte chunk. Its strength is borrowed
   from whatever hash produced its input and evaporates for an attacker-chosen 32-byte value.
   *Faithful width is necessary and not sufficient*, which is the same thing `faithful8.rs` says
   about what its type wall does not guard.

A degraded fold is a fine **consistency tag** where the *real* binding lives
elsewhere (defense-in-depth), and a fine per-effect param projector. It is a
**bug** only when it IS the commitment of a 32-byte component.

## Where the law bites (the commitment-bearing producers)

The scope has exactly one authority — the `files:` blocks of
`.ast-grep/rules/faithful-commitment-felt.yml`, which the gate script derives
rather than re-transcribing. It is **eight** producers, not the three this table
listed until 2026-08-02:

| File | Role |
|------|------|
| `cell/src/commitment.rs` (`compute_rotated_pre_limbs`) | the canonical `pre_limbs` the rotation commits |
| `turn/src/rotation_witness.rs` | the producer twin of the above |
| `circuit/src/effect_vm/trace_rotated.rs` | the rotated trace that re-absorbs `pre_limbs` |
| `cell/src/commitment_set.rs` (added 2026-07-31) | `accumulator_leaf` — a folded address keys a tree that silently dedupes collisions |
| `cell/src/nullifier_set.rs` (added 2026-07-31) | the sibling accumulator, same shape |
| `cell/src/revoked_set.rs` (added 2026-07-31) | `accumulator_leaf`; the committed `revoked_root` group is opened in-circuit against a tree of these |
| `cell/src/shielded_note_set.rs` (added 2026-07-31) | `accumulator_leaf` with a `ZERO` value column, so the folded address is the leaf's only distinguishing content |
| `node/src/turn_proving.rs` (added 2026-07-31) | `nullifier_to_field`, whose image is a published PI and the double-spend search key |

Non-commitment uses of the fold are **out of scope and sound**: the executor/SDK
per-effect param projectors (`effect_vm_bridge.rs`, `cipherclerk.rs`), the D5 PI
cross-binding reconstruction in `proof_verify.rs`, and tests.

⚠ `node/src/turn_proving.rs` stood in that out-of-scope sentence — "the real
binding is the `SCHEMA_NOTE_SPEND` proof + the committed set" — until 2026-08-02.
It does not belong there and the rule has scoped it since 2026-07-31: the fold's
image IS `PI[NOTESPEND_NULLIFIER]`, so it is not a projector beside a binding, it
is the binding. It is one of the two live reds below.

## The gate

`scripts/check-no-degraded-felt.sh` runs `ast-grep` against the producers above
(rule `.ast-grep/rules/faithful-commitment-felt.yml`, scoped by its `files:`
field).

**Where it runs (corrected 2026-08-02): `scripts/local-gates.sh`, NOT GitHub.**
It was the `no-degraded-felt` job in `.github/workflows/ci.yml` until **2026-07-29**,
when nine jobs were deleted because each ran a command character-for-character
identical to a local-gates row (the deletion manifest is the comment block at
`.github/workflows/ci.yml:815`). The gate is now the `no-degraded-felt` row of
`scripts/local-gates.sh:142`, which invokes it as `--rev HEAD`.
`grep -rn 'check-no-degraded-felt' .github/workflows/` returns nothing.

⚠ Combine that with `main` not being branch-protected and a red here **blocks
nothing automatically** — it reports. That is a large part of how a gate which
has never passed came to be cited as green by a dozen documents: no one was
stopped by it.

### ⚑ THE GATE DOES NOT PASS AT HEAD (measured 2026-08-02)

Run over a clean extract (`scripts/check-no-degraded-felt.sh --rev HEAD`, which
grades a commit rather than a shared working tree) it exits 1 with **two**
errors. Both are real, both are in production:

| Site | What the fold reaches |
|------|-----------------------|
| `cell/src/commitment.rs:561` | `cap_root::fold_bytes32(cap.target)` — the cap-tree leaf's target field in the DEPLOYED canonical state commitment |
| `node/src/turn_proving.rs:1159` | `nullifier_to_field` — its image IS `PI[NOTESPEND_NULLIFIER]`, and also the key the double-spend freshness search and the `canonical_spent_nullifier_set` consensus anchor run on |

**They are left red on purpose.** Repairing either changes what the circuit
commits to and opens — `CapLeaf` is a 7-field Poseidon2 leaf opened in-circuit,
`PI[NOTESPEND_NULLIFIER]` is an AIR public input — so the repair is a
**Lean-authored AIR change plus a VK epoch and a re-genesis**, on the
exact_cap_root / exact-nullifier tracks. A Rust-side re-encoding would be the
drift, not the fix.

**Why every earlier verdict read green.** The rule was widened twice:
**2026-07-31** (scope 3 files → 8) and **2026-08-01** (the alias names
`fold_bytes32` / `fold_value32` added to a name-bound pattern). Both live wounds
sit exactly in that widening — `commitment.rs:561` spells the fold
`cap_root::fold_bytes32`, which the pre-08-01 pattern could not see, and
`node/src/turn_proving.rs` was outside the scanned set before 07-31. A green
recorded before those dates was green **under a narrower rule**, not evidence
about these two sites.

⚠ **What the gate cannot yet do:** distinguish a net-new fold from these two
known wounds. There is no ratchet baseline (the shape of
`scripts/guard-discipline-baseline.txt` — counts that may only fall), so a red
is information about the whole scope, not about the diff. The old formulation
"a net-new `fold_bytes32_to_bb` in a commitment producer **fails the PR**" was
wrong on both halves: the run was already failing, and there is no PR gate to
fail. Building the baseline is the missing piece.

### Allowlisting a deliberate residual

A justified residual is annotated inline, line-scoped:

```rust
// FAITHFUL-COMMITMENT-LAW residual: <why this is safe / when it gets fixed>.
pre[4 + i] = fold_bytes32_to_bb(&cell.state.fields[i]); // ast-grep-ignore: degraded-felt-commitment
```

⚠ The text after the directive's colon is parsed by ast-grep as a **rule-id
list**, so the suppression must read exactly `// ast-grep-ignore:
degraded-felt-commitment` (the rule id) — the human REASON goes on the line
ABOVE, never after the colon.

⚠ **Suppression is NOT the disposition chosen for the two live wounds.**
`cell/src/commitment.rs:561` and `node/src/turn_proving.rs:1159` are not
allowlisted and must not be. A directive there would turn a red gate green
while the deployed commitment still binds a 32-byte component at ~31 bits — a
containment below the bar, adopted in place of the AIR change that actually
fixes it. The gate exists to keep those two visible until the VK epoch lands.
An allowlist entry is legitimate only as the conclusion of an argument that the
site is not a commitment position, as in the residual below.

### Current allowlisted residuals

**ONE — `trace_rotated.rs::undelegated_spend_ancestor` (felt-width site #20, added 2026-07-24).**
The spend-side delegation-ancestor sentinel the deployed `spendAncestorFreshOp` opens `.absent`
against the revoked set. It is **not a commitment**: the felt lands only in param col 71, which the
rotated commit chain (`recompute_block_commit` over `row[BEFORE_BASE..]`/`row[AFTER_BASE..]`) does
not cover and no PI binds — the law's own "fine per-effect param projector" case; the gate fired on
the *pattern* because `trace_rotated.rs` is a scoped file. Widening is **not representable**: the
deployed IR types a map-op key as one felt (`DescriptorIR2.lean:301-313`, `key : EmittedExpr` beside
`root : Fin 8 → EmittedExpr`), and the insert side is one felt too, so 8-felt keys are a VK-affecting
Lean AIR epoch. Soundness-neutral (a same-fold-keyed `.absent` can only over-revoke, never
under-revoke); the residual is a **real ~2^31-offline-grind availability wound**, argued at the site
and priced as #20 in `docs/WOUND-felt-width-boundaries-2026-07-19.md`. A suppression is legitimate
only as the conclusion of an argument — that argument is the doc-comment section on the function, not
this sentence.

### ⚠ The `fields[0..7]` residual — this section claimed CLOSED and was FALSE (corrected 2026-07-30)

**What it said:** *"The `fields[0..7]` residual is CLOSED (v13 fields-octet epoch) … The state
commitment now binds ALL 32 bytes of every flat field at ~124 bits."* This is the same overclaim
`commitment.rs`, `faithful8.rs`, `helpers.rs` and `EffectVmEmitRotationV3.lean` all carried, and it
survived the sweep that corrected those four — **the law document was the one place nobody looked.**
It matters more here than in any of them, because this file is what a reader consults to decide
whether a commitment position is safe.

**The arithmetic.** The v13 grow did replace the r3..r10 Horner folds in
`compute_rotated_pre_limbs` and its `rotation_witness` twin with the
`Faithful8::from_field_limbs8` 8-lane split (lane 0 = the u64-lane lo32 riding the welded limb
`4 + i`, lanes 1..7 riding the completion lanes `113 + 7·i .. +6`). But every lane was `u32 % p`, and
`2p = 4026531842 < 2^32`, so a colliding sibling was **CONSTRUCTED** by adding `p` to any 4-byte
chunk with no grind. `fields[0..7]` are deliberately excluded from the byte-exact authority residue
(`cell/src/commitment.rs` — it walks `fields[8..]`), so those lanes are their ONLY binding, and the
alias reached `TurnReceipt::{pre,post}_state_hash`, the executor signature and the receipt QC.
Exhibited at the anchor by `turn/tests/fields_octet_aliases_at_the_anchor.rs`.

⚑ **STATUS 2026-08-01: SUPERSEDED — the fields octet is CLOSED by the ninth lane, and the two
paragraphs below are the record of the 8-lane era, not the present.** `field_limbs8` and
`Faithful8::from_field_limbs8` were **deleted** 2026-07-31 and replaced by `Faithful9` over the
nine-lane `field_limbs9`, whose injectivity on 32-byte values is a Lean theorem with a total
decoder and a machine-checked left inverse (`Dregg2.Circuit.FieldLanes9.fieldToLanes9_injective`),
and whose in-circuit canonicity gate is `Dregg2.Circuit.Emit.FieldsCanonicity9Emit` — 7 gates plus
12 lookups per (block, slot), with `canon9_forces_canonical` carrying `Satisfied2 ⟹ Canonical9` on
the **committed columns** and `canon9_rejects_the_forged_nonet` exhibiting a specific forged vector
(lane 8 = `3 · 2^24`) that has no aux fill at any canonical values. Flag day: `APPENDIX_SPAN`
539 → 651, every rotated member's `traceWidth` +112, a descriptor re-emit and a VK rotation, **no**
re-genesis. ⚠ *Provenance:* taken from the emit module's own header and this wave's measurement of
it; this lane did not re-run the Lean build, so read it as "proved and emitted", which is not the
same rung as "a relying verifier was observed rejecting". The `2^92.7` figure below no longer
describes the deployed fields octet.

**Where it stood under `field_limbs8` (historical).** `field_limbs8` lanes 2..7 carried the leading six felts of a Poseidon2 image
over an injective 16 × u16-LE preimage of the whole 32-byte value; lanes 0/1 (the kernel u64 lane)
are byte-identical to before. The constructed alias is gone. **The octet is still NOT injective**:
eight BabyBear lanes carry 247.26 bits against 256, so no 8-lane encoding of 32 bytes is injective
under any chunking, whatever the lanes contain. Say "hash-strength", never "faithful", and never
"binds all 32 bytes".

⚑ **Price the right attack.** Six BabyBear lanes carry `6 · log₂ p = 185.4` bits of IMAGE, and lanes
0/1 contribute NOTHING to an attacker's bill (they are `u32 % p` over bytes 24..32, matched for free
by leaving the window alone or adding `p`). So **second preimage ≈ 2^185** — an attacker holding an
honest value and wanting a different 32-byte value with the same octet — and **collision ≈ 2^92.7**,
the birthday bound, when the attacker chooses both values. Quoting the image size where the birthday
bound is meant is the house error; it is how `compute_effects_hash_4` came to claim ~124 bits for a
~2^15.5 object. ⚠ **2^92.7 is below the ~124-bit bar quoted elsewhere in this document**, so the
fields octet is now the weakest COLLISION term in the rotated commitment even though it is no longer
`O(1)`-forgeable.

Cost of that change: a **re-genesis** (`PersistentStore::CANONICAL_STATE_SCHEMA_EPOCH` 12 → 13, so a
pre-v13 store refuses to load rather than carrying stale commitments). **No** descriptor re-emit and
**no** VK rotation — audited across all 175 rotated members of the four registries, the only
constraints that touch a fields-completion column are the `colEq(before, after)` freeze, the setField
`pi_binding` publications, and the Poseidon2 absorption lookups. None constrains a lane's value.

**What closed it:** a NINTH lane — done, see the STATUS above. ⚑ The sentence this replaced read
*"What closes it properly: a NINTH lane. That is a descriptor re-emit, a VK rotation and a
re-genesis, and it is gated on `circuit/descriptors/PROVENANCE.json` losing its `"source_dirty":
true`."* Worth keeping visible: the priced cost was **larger** than the landing turned out to need
(no re-genesis), and the "gated on" clause named a blocker that did not block. A cost estimate is
not a constraint — the identical shape is now in front of the **key** octet, where the ninth lane
is priced at a re-genesis and that re-genesis was already spent by the schema-epoch 14 → 15 bump
of 2026-07-31.

**Deployed reality — the R1 paragraph here was also stale.** It said the deployed member is
`v3OfFrozen (setFieldTickFace slot)` (freeze-**ALL**), so an honest LARGE-value setField could not
prove and the seam was a *completeness* residual. The VALUE8 epoch landed: `v3RegistryBare` now emits
`withSetFieldCompletionPins slot (withSelectorGate SEL_SET_FIELD (setFieldV3 slot))` — freeze-EXCEPT
(the written slot's 7 lanes are FREED) plus 7 `.piBinding .last` pins publishing them as PIs 46..=52.
The high 224 bits are bound by PUBLICATION rather than by being frozen shut. Consequences, both
measured by `circuit/tests/setfield_completion_lane_forge.rs`: an honest large-value write now
PROVES, and the written-slot completion forge is still UNSAT (the pin bites where the freeze used
to). ⚠ The side effect is that **the prover no longer refuses a wrong-lane encoder** — the whole
32-byte value is writable — so `circuit/tests/setfield_encoder_window_gate.rs`'s type-directed source
walk is now the only detector for that class, not belt-and-braces.

## The capstone: the `Faithful8` TYPE WALL (built)

The type-level capstone **exists**: `dregg_circuit::faithful8::Faithful8`
(`circuit/src/faithful8.rs`, re-exported as `dregg_circuit::Faithful8`) — a
newtype over `[BabyBear; 8]` with a **private** inner array, so a bare octet
cannot enter a commitment sink without naming a faithful constructor. A
degraded felt in a typed commitment position is now a **compile error**
(`compile_fail` doc-tests in the module are the tripwire).

**Constructors (the only ways in).** ⚑ Split into two lists on 2026-08-01, because a single list
is how a below-floor packer came to sit beside the tree roots:

*Faithful by construction:*

- the **tree roots** — `cap_root::compute_capability_root{,_with_tombstones}`,
  `cap_root::empty_capability_root`, `heap_root::compute_canonical_heap_root_8{,_entries}`,
  `heap_root::empty_heap_root_8`, `CanonicalHeapTree8::root8` all *return* `Faithful8`
  (internally via the crate-private `from_root8`);
- the **wire-commit chain** — `from_wire_commit` / `from_wire_commit_chip`;
- `Faithful8::ZERO` — the absent-material / vk-revoke sentinel; not a projection of anything.

*Admitted, and each one an admission:*

- `Faithful8::from_lossy_31bit_DANGER(reason, limbs)` — the **greppable escape hatch**. The
  burn-down list below is its call sites, and it is **NOT empty**;
- `Faithful8::from_canonical_key` — the 30-bit KEY_COMMIT `pubkey8` pack. ⚑ **Its body IS the
  hatch** as of 2026-08-01: IMAGE `2^240`, birthday COLLISION `2^120`, actual collision `0`. See
  the section below;
- `Faithful8::from_bytes32` — `bytes32_to_8_limbs`. Full `2^247.26` image, collision cost **`0`**
  for an attacker-chosen input (`v` and `v + p` alias). Its strength is **borrowed** from whatever
  produced its input, so "is this site safe" is a **per-site obligation**, not a property of the
  constructor. Its commitment-bearing sites in `compute_rotated_pre_limbs` /
  `rotation_witness::produce` take `child_vk` and `contract_hash` (a VK hash and a contract hash),
  and a large share of the remaining ~25 sites are not encodings at all but **lane repacking** —
  already-canonical felts written to bytes and read straight back
  (`commit::poseidon2_tree::faithful8_from_lanes`, `cell::nullifier_set`, `cell::revoked_set`),
  where `from_bytes32` is an exact inverse. It is not routed through the hatch because it is not
  below floor *for those inputs*; that is a narrower claim than "faithful" and it is the one this
  list now makes.
  ⚠ **Not audited exhaustively by the 2026-08-01 pass, and one site does not fit the pattern:**
  `cell/src/state.rs`'s serde `deserialize` calls `from_bytes32` on 32 bytes taken **off the
  wire**, so a chunk `≥ p` is silently reduced and two distinct serialized strings deserialize to
  one `Faithful8`. Whether anything downstream re-serializes and compares is not measured here.

- ~~`from_field_limbs8`~~ — **DELETED 2026-07-31** together with the `field_limbs8` encoder. This
  entry survived the deletion by a day and described a constructor that no longer existed. Its
  successor is `Faithful9` over the nine-lane `field_limbs9`, whose injectivity is a Lean theorem
  (`FieldLanes9.fieldToLanes9_injective`, total decoder + machine-checked left inverse) and whose
  in-circuit canonicity gate is `Dregg2.Circuit.Emit.FieldsCanonicity9Emit`. There is no
  `Faithful8` path to a fields octet any more.

**Typed sinks:** the octet fills of the three commitment producers
(`cell::commitment::compute_rotated_pre_limbs`, `turn::rotation_witness::produce`,
and the `trace_rotated` accumulator-lane overrides) go through
`Faithful8::write_octet` / `write_lanes`; the cell digest producers
(`compute_authority_digest_8`, `perms_digest_8`, `vk_digest_8`,
`compute_canonical_capability_root_8`, `state::compute_canonical_{heap,fields}_root_8`,
`compute_canonical_state_commitment_v9_felt8`, `rotation_witness::wire_commit_8`)
all return `Faithful8`. Reading out is unrestricted (`Deref` / `.limbs()` /
`Into<[BabyBear; 8]>`) — the wall polices construction, not inspection, which is
what stops the consumer cascade at module boundaries. Circuit-internal trace
math stays bare `BabyBear` by design.

**Gate + wall are complementary:** the ast-grep gate catches the degraded
*pattern* (`fold_bytes32_to_bb` in a producer file, including sites that never
touch a typed sink); the wall catches the degraded *value* (any bare octet
smuggled toward a typed sink, in any file, including ones the gate has never
heard of). Neither subsumes the other; both stay.

Complementary is not the same as clean. At HEAD the gate is **red** on the two
production sites named above and the wall is green over them — the wall polices
construction of a `Faithful8`, and neither `cap_root::fold_bytes32` nor
`nullifier_to_field` produces one. Two mechanisms disagreeing that way is the
expected reading: the fold reaches a commitment without passing a typed sink.

## ⚑ THE KEY_COMMIT OCTET IS BELOW THE FLOOR — reclassified 2026-08-01

**What the wall said.** `Faithful8::from_canonical_key` stood in the faithful constructor list,
its doc reading *"8+8+8+6 = 30 bits per limb, 240 bits total, faithful"*. It entered through the
**front door** — not through the `_DANGER` hatch that exists precisely so admissions of this kind
are listed. The hatch was built, documented, and walked past.

**The arithmetic, with the bound named every time.** `canonical_32_to_felts_8` /
`canonical_to_babybear_pi` compute `lo | mid1<<8 | mid2<<16 | ((hi & 0x3F) << 24)` per lane.

- **IMAGE = `2^240`, exactly.** Each lane sweeps all of `[0, 2^30)` and `2^30 < p`, so nothing
  reduces; the image is `(2^30)^8` on the nose. That is `2^-7.26` of the `[0, p)^8` its columns
  can hold — the pack refuses 99.35 % of the committed space, which is a real (if unenforced)
  narrowing and is *not* a security level.
- **COLLISION (birthday) = `2^120`.** Against the floor of `2^123.63` established above: **below
  it by 3.63 bits.** 240 bits of image is not "at floor" on even the most generous reading, and
  that alone settles the classification.
- **COLLISION (actual) = `0`. No search.** Bits 6-7 of bytes 3, 7, 11, 15, 19, 23, 27, 31 are
  never read, so every octet has exactly `2^16` distinct 32-byte preimages and a second preimage
  is one bit-flip. Measured, not asserted:
  `circuit/tests/faithful8_key_octet_below_floor.rs` flips all 256 source bits against the
  deployed packer and gets 240 that move the octet and 16 that do not.

⚑ **And the "only a *meaningful* collision costs anything" escape does not hold for this source.**
The octet carries `Cell::public_key`, an **Ed25519** public key, and RFC 8032 §5.1.2 puts the
x-sign in **bit 7 of byte 31** — one of the sixteen unread bits. So a point `A` and its negation
`−A` are two distinct, valid, decompressible public keys of the same order whose encodings differ
in exactly that bit, and they **pack to one octet**. The exhibit is a real curve point and its
negation through the real packer (`an_ed25519_key_and_its_negation_pack_to_one_octet`). A colliding
*valid public key* is free. What an adversary can then *do* with `−A` — whether any deployed
signature path will accept for it — is not measured here; the commitment's failure to distinguish
them is.

**Where it lands.** `B_PUBKEY_OCTET = 105..112` on both blocks, a pre-iroot limb, so it rides the
`wireCommitR` absorption chain into `state_commit` and on to the signed consensus anchor. Two
producers write it: `cell::commitment::compute_rotated_pre_limbs` and
`turn::rotation_witness::produce`.

**What this lane did, and what it did not.** It moved the constructor's body onto the `_DANGER`
hatch and put it on the list below — type- and doc-level only. **No encoder changed.** The octet
is exactly as weak as it was this morning; it is now *listed* as weak.

**What closes it: a NINTH key lane**, and ⚠ **say which bound.** This sentence read "`2^278.16`
image, `2^139.08` collision — clears the floor by 15.5 bits" until 2026-08-01. Those are the
CAPACITY of nine BabyBear lanes, not the encoding's numbers, and `2^278.16 > 2^256` gives it away.
The encoding recommended below — the base-`2^29` nonet — has **image exactly `2^256` and is
INJECTIVE** (`Dregg2.Circuit.KeyLanes9.keyToLanes9`, `keyToLanes9_injective` from a total decoder
`keyLanes9ToBytes` and a machine-checked left inverse; the fit `K^8 · KTOP = 2^256` is exact). So
**the encoding step loses nothing — there is no encoding collision to bound — and the binding
reduces to the sponge that absorbs the lanes.** Not "clears the floor by 15.5 bits": nothing about
a birthday bound is being claimed.

The geometry: the pre-limb region is 184/184 full, so this is `rotatedNumPreLimbs` 184 → 187 (the
`≡ 1 (mod 3)` `chunk31` invariant forbids +1 or +2), `B_SPAN` 247 → 251, a descriptor re-emit, a VK
rotation and a `CANONICAL_STATE_SCHEMA_EPOCH` bump — a re-genesis. ⚠ **The epoch NUMBER is
deliberately not written here.** This sentence said "15 → 16" and was stale by seven within the
day; go read `persist::PersistentStore::CANONICAL_STATE_SCHEMA_EPOCH`. The key octet, unlike the
fields octet, is welded to nothing and read lane-wise by nobody, so the encoding can be replaced
**wholesale**: the nonet needs no `NoWrap` leg, no cube gate and no aux columns, and its canonicity
envelope is two legs and zero gates (eight lookups at 29 bits, one at 24 — `canonicalKey9_iff_in_image`
proves the two together are exactly the image). Related and wanting the same flag day: the E10
free-felt AFTER-owner limb (`circuit/tests/zzz_e10_freeze_owner_falsifier.rs`), which is a **missing
constraint** and needs no collision at all.

✅ **RUNG, 2026-08-02 — EMITTED AND ON THE WIRE.** The sentence above read *"authored and proved in
Lean, not emitted into any member and not consumed by a verifier; the column map is still a
parameter because lane 8's column does not exist"* and every clause of it is now false.
`KeyCanonicity9Emit.keyCanonical9Wire` is applied by `EmitRotationV3.lean` and both wide registry
probes; the committed registries carry **960 lookups at 29 bits and 120 more at 24** (narrow;
912 / 114 wide) where they carried **zero at 29** the day before. `deployedKeyCanon9Cols` leaves
nothing free but the face width. Geometry did not move — `traceWidth`, `piCount` and the table list
are `rfl`-unchanged, so this rotated the AIR fingerprint and both registry FPs and **not** the
schema epoch. The exhibit is `circuit/tests/key_nonet_canonicity_envelope_old_admits_new_rejects.rs`:
one forged trace, accepted without the 18 lookups and UNSAT with them.

### ⚑ THE OTHER TWO CARRIER OCTETS — `child_vk` (89..96 ‖ 184) and `contract_hash` (97..104 ‖ 185)

**Priced 2026-08-02. This is a SECOND cutover, and the reason is the PRODUCER, not the Lean.**

The 187-limb grow bought three ninth lanes — `ROTATED_OCTET_NINTH_LANES = [184, 185, 186]` — and
**one is used.** Columns 184 and 185 are emitted, tiled, `#guard`-ed and absorbed by `wireCommitR`,
and **no producer writes them**: both twins still fill those two octets with
`Faithful8::from_bytes32` (`turn/src/rotation_witness.rs:725,730` ·
`cell/src/commitment.rs:1365,1369`), which is `bytes32_to_8_limbs` — eight 4-byte little-endian
chunks reduced `mod p`.

**How weak, exactly.** A chunk is uniform on `[0, 2^32)` and `p = 2013265921`, so every limb value
has **2 or 3** preimages (3 when the value is below `2^32 − 2p = 268435454`, else 2). Therefore
**every committed octet is shared by between `2^8 = 256` and `3^8 = 6561` distinct 32-byte values**
— expected `(2^32/p)^8 = 2^8.74`, which is the `256 − 8·log₂ p = 8.74` bits pigeonhole loses — and a
sibling is constructed by **one addition**: add `p` to any 4-byte window whose value is below
`2^32 − p`. Both octets are also PI-published on `factoryVmDescriptor2R24` — `child_vk8 → PI[47..54]`,
`contract_hash8 → PI[55..62]` — so the ambiguity reaches a light client that has no ledger to
disambiguate against.

⚠ **`2^8.88` until 2026-08-06, in the same sentence as `8.74`.** Two numbers for one quantity and
neither was derived here; `E[Π reps] = (2^32/p)^8 = 2^8.74` is the one that follows from the line
before it.

### ⚑ AND THE SEVERITY WAS OVERSTATED — corrected 2026-08-06, measured at the source

This paragraph read *"That is `O(1)`, not a birthday bound, and it is `O(1)` **for the attacker's own
chosen bytes**, which is what these two carriers hold."* **The second clause is false**, and it is the
clause that sets this cutover's priority. What the carriers hold:

* `child_vk` is `ChildVkStrategy::derive_child_vk` = `blake3_derive_key("dregg-derived-child-vk-v1",
  factory_vk ‖ param_hash)` (`cell/src/factory.rs:181`), or under `Fixed`/`FromSet` a VK identifier
  that must correspond to a program whose proofs verify. It is a **BLAKE3 image**, not a free field.
* `contract_hash` is a `[u8; 32]` the SDK caller passes verbatim
  (`sdk/src/hatchery_mint.rs::attest_hpres`), and `circuit-prove/src/hatchery_leaf_adapter.rs` names
  its own residual: anchoring it to a **verifying** contract proof in-circuit is **not done**. The
  value is therefore already unconstrained, and an alias buys nothing there that choosing the value
  outright does not already buy.

So the sibling is `O(1)` **in the byte domain** — and it is exhibited there, at the deployed producer
and the deployed fold, by `circuit/tests/carrier_octet_siblings_survive_the_key_nonet_flag_day.rs`.
Turning it into a forgery at `child_vk` means landing a *semantically valid* VK inside a target set of
size `2^8.74`: a BLAKE3 second preimage, ≈`2^247`. ⚠ **Say that bound.** This is **not** the owner-key
situation, where `A` and `−A` were both valid keys, the attacker held the private half of the
negation, and the two packed identically for free — which is exactly why the owner key was the
correct first repair and is the one that is done.

**What remains true, and is what justifies the cutover:** the committed carrier does not *determine*
the 32 bytes, it determines a set of size `≥ 2^8`. So no `keyCanon9_determines_the_owner_key`-shaped
capstone is statable for these two carriers at all, and any downstream sentence of the form "the
committed octet determines the installed child VK" is false as written. That is a real defect in what
the anchor means, priced honestly rather than as a live forgery.

**What the fix is NOT.** It is *not* "their own Lean emit face". `keyCanonical9At (col : KeyColMap)`
is column-agnostic and `lane_bounds_atCols` proves the forcing for **any** nine columns; only
`deployedKeyCols` (which spells `B_PUBKEY_OCTET`) and the named capstones are owner-key-specific.
The Lean delta is a `deployedCarrierCols (octetBase ninthLane : Nat)` generalization of one `def`
plus three instantiations and their `#guard`s — on the order of 80 lines in a file that already
exists, not a new module. **Whoever schedules this should not inherit the earlier estimate.**

**What it IS, and why it is a separate flag day.** The producers must stop using a different
encoder, and that changes committed VALUES rather than adding constraints:

1. **Both producer twins** switch to `Faithful9::from_key_lanes9` over new
   `CHILD_VK_NONET_LANE_COL` / `CONTRACT_HASH_NONET_LANE_COL` consts, derived positionally from
   `ROTATED_OCTET_BASES` / `ROTATED_OCTET_NINTH_LANES` with the same const-gate `PUBKEY_NONET_LANE_COL`
   carries. Four call sites; the consts are the review.
2. **Limbs 89..104 change meaning** — `bytes32_to_8_limbs` and `key_limbs9` are different encoders,
   so every factory / hatchery-mint `state_commit` moves. That is a **RE-GENESIS**, i.e. a
   `CANONICAL_STATE_SCHEMA_EPOCH` bump (read the constant; the number is deliberately not written
   here) *and* a `VK-REGEN-LOG` row, where the owner-key envelope needed neither.
3. **The factory PI face grows** `63 → 65`: the octet pins publish 8 lanes each and a nonet needs 9,
   or the published half stays ambiguous while the committed half is not — which is the wound moved
   rather than closed. Every consumer of `PI[47..62]` re-indexes.
4. Only then does the envelope apply, and it applies verbatim.

**Sequencing, stated so it cannot be read as a deferral.** (2) and (3) are the work; the envelope is
the cheap part and must not land first — an envelope over `bytes32_to_8_limbs` columns would force
them into the image of a map that is not injective on its domain, which is precisely the containment
`KeyCanonicity9Emit`'s own header refuses for the eight-lane owner octet. So the order is forced by
correctness, not chosen by cost: **encoder, then PI face, then envelope.**

### The `_DANGER` sites = the burn-down list — **EMPTY as of 2026-08-02**

`grep -rn from_lossy_31bit_DANGER --include='*.rs'` IS the burn-down list, plus the call sites of
any ROUTER — a constructor in `circuit/src/faithful8.rs` whose body calls the hatch. The gate
derives the router names from the source rather than from this sentence, which is why the recipe
here could name a deleted one (`from_canonical_key(`, then `from_key_nonet_low8(`) and the gate
still be right.

⚠ **It has read "empty" before and been wrong.** It said **"EMPTY (v13 DONE)"** until 2026-08-01,
and it was empty only because the key octet had been let in the FRONT DOOR as a named constructor
— the emptiness was a property of the list's definition, not of the tree. So read today's emptiness
narrowly: **nothing routes through the hatch**, and that is the whole claim. `from_bytes32` still
admits an `O(1)`-aliasable octet through the front door, and the section above ("WHAT THIS WALL
DOES NOT GUARD" in `circuit/src/faithful8.rs`) is where the wall's real limits live.

⚑ **This list is now a GATE.** `circuit/tests/faithful8_key_octet_below_floor.rs
::the_burn_down_list_names_every_hatch_admission` walks every `*.rs` in the workspace, collects the
non-comment call sites, and fails the suite unless the set below matches **exactly** — in both
directions, so a closed residual cannot linger here either. "Adding a `_DANGER` site without
listing it here is a review-time violation" was a rule with no instrument, and a documented wound
is not a detected one.

⚑ **The key is the `(file, reason-constant)` ADMISSION, not the file path** — corrected 2026-08-01,
and the correction matters more than the gate did. The first version pushed a file path once and
`break`-ed. It caught a *new* file with a hatch call, and it was **blind exactly where the next
degraded octet gets added**: the three listed files are the two deployed producers and the wall
itself, and a second, distinct residual added inside one of them passed 5/5. A gate whose stated
purpose is "a documented wound is not a detected one" could not see the wound it guards. `(file,
line)` would go red on every reflow and would be relaxed within a week; the reason constant survives
a reformat and names what is being admitted.

**Format, which is parsed — do not reformat it.** Each entry reads ``- `<path>` — `<REASON_CONST>`
— why``; the first two code spans on the line are the key. Continuation lines carry no `- ` and are
ignored. Two further rules the gate enforces:

- a reason must be a `&str` **constant declared beside the hatch** in `circuit/src/faithful8.rs`
  (an inline literal at the call site is refused — the grep and this document need one source);
- the constant's **value** must be quoted **verbatim** in this section, so the two cannot drift.
  The previous version asserted three hand-picked needles were somewhere in the document, which
  left a second residual's reason unchecked entirely.

`tests/` directories are scoped out, by the same sentence that scopes them out of the law itself
("Non-commitment uses of the fold are out of scope and sound: … and tests"). A test that CALLS the
residual is exercising it, not admitting it into a commitment; a `#[cfg(test)] mod` inside a `src/`
file is still scanned. On its first run the gate went red on a sibling lane's
`commit/tests/key_octet_f2_twins_and_the_hole.rs` — an unlisted site that no reviewer had flagged,
which is both the reason the scope is written down here and the evidence that the walk works.

<!-- BURN-DOWN-LIST-BEGIN -->
(no entries)

⚑ **CLOSED 2026-08-02 — the owner key's ninth lane reaches the anchor.** The three entries that
stood here (`cell/src/commitment.rs`, `circuit/src/faithful8.rs`, `turn/src/rotation_witness.rs`,
all carrying `KEY_NONET_NINTH_LANE_UNBOUND`) admitted that `state_commit` absorbed **lanes 0..=7
only — 232 of the owner key's 256 bits, and the Ed25519 x-sign was not among them**, so a point
`A` and its negation `-A` reached the signed consensus anchor with a byte-identical limb vector at
cost zero.

They are gone because the residual is, not because the list was redefined:

1. the emitted geometry is `NUM_PRE_LIMBS = 187` with `B_PUBKEY_NINTH_LANE = 186`, an ABSORBED
   pre-limb, so `wireCommitR` folds it into `state_commit`;
2. both producers write all nine lanes through `Faithful9::from_key_lanes9` over
   `dregg_circuit::effect_vm::PUBKEY_NONET_LANE_COL`;
3. the constructor `Faithful8::from_key_nonet_low8` and the reason constant
   `KEY_NONET_NINTH_LANE_UNBOUND` are **deleted** — there is no `Faithful8` path to an owner-key
   octet any more, so a caller that wants one gets a compile error rather than a doc row.

(Numbered, not bulleted, deliberately: the gate parses every line in this section that opens with
a dash and a code span as an ENTRY, so prose here must not wear an entry's shape.)

⚠ **What is NOT closed by this, and must not be read into an empty list.** The nonet's CANONICITY
ENVELOPE (`Emit.KeyCanonicity9Emit.keyCanonical9At` — eight range lookups at 29 bits plus one at
24) is authored and proved in Lean and **applied by nothing**. So the anchor now BINDS all 256 key
bits, and no emitted constraint yet REFUSES a lane vector outside the encoder's image. The
`OwnerFreezeWire` colEq on limb 186 is emitted and does hold the lane frozen BEFORE-to-AFTER.

<!-- BURN-DOWN-LIST-END -->

The `fields[0..7]` pair that used to be the list is genuinely gone — closed by the nine-lane
`Faithful9` / `field_limbs9` grow of 2026-07-31, not by a redefinition.
