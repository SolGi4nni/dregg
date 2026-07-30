# The Faithful-Commitment Law

**Every 32-byte component that flows into the deployed state commitment binds its
SOURCE at the system's own soundness strength (~124-bit, the 8-felt encoding) —
never a lossy 1-felt projection.**

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
  32 bytes → 1 felt (~31-bit). Defined in `circuit/src/effect_vm/helpers.rs`.
- **Faithful (required):** `bytes32_to_8_limbs(x)` → `[BabyBear; 8]` (~124-bit),
  and its hash-domain siblings (`hash_many` over 8-felt groups). The commit binds
  the **source**, not a degraded projection of it.

A degraded fold is a fine **consistency tag** where the *real* binding lives
elsewhere (defense-in-depth), and a fine per-effect param projector. It is a
**bug** only when it IS the commitment of a 32-byte component.

## Where the law bites (the commitment-bearing producers)

| File | Role |
|------|------|
| `cell/src/commitment.rs` (`compute_rotated_pre_limbs`) | the canonical `pre_limbs` the rotation commits |
| `turn/src/rotation_witness.rs` | the producer twin of the above |
| `circuit/src/effect_vm/trace_rotated.rs` | the rotated trace that re-absorbs `pre_limbs` |

Non-commitment uses of the fold are **out of scope and sound**: the executor/SDK
per-effect param projectors (`effect_vm_bridge.rs`, `cipherclerk.rs`), the D5 PI
cross-binding reconstruction (`proof_verify.rs`, `node/src/turn_proving.rs` — the
real binding is the `SCHEMA_NOTE_SPEND` proof + the committed set), and tests.

## The gate

`scripts/check-no-degraded-felt.sh` runs `ast-grep` against the producers above
(rule `.ast-grep/rules/faithful-commitment-felt.yml`, scoped by its `files:`
field). Wired into CI as the **`no-degraded-felt`** job in `.github/workflows/ci.yml`.
A net-new `fold_bytes32_to_bb` in a commitment producer **fails the PR**.

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

**Where it stands now.** `field_limbs8` lanes 2..7 carry the leading six felts of a Poseidon2 image
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

**What closes it properly:** a NINTH lane. That is a descriptor re-emit, a VK rotation and a
re-genesis, and it is gated on `circuit/descriptors/PROVENANCE.json` losing its `"source_dirty":
true`.

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

**Constructors (the only ways in):**

- `Faithful8::from_bytes32` — `bytes32_to_8_limbs`, the canonical 32-byte limb split;
- the **tree roots** — `cap_root::compute_capability_root{,_with_tombstones}`,
  `cap_root::empty_capability_root`, `heap_root::compute_canonical_heap_root_8{,_entries}`,
  `heap_root::empty_heap_root_8`, `CanonicalHeapTree8::root8` all *return* `Faithful8`
  (internally via the crate-private `from_root8`);
- the **wire-commit chain** — `from_wire_commit` / `from_wire_commit_chip`;
- `from_canonical_key` — the 30-bit KEY_COMMIT packing (the `pubkey8` lane);
- `from_field_limbs8` — the **flat-fields[0..7] octet** projection (`field_limbs8`: lane 0 =
  u64-lane lo32, lane 1 = u64-lane hi32, lanes 2..7 = a Poseidon2 image over an injective
  16 × u16-LE preimage of the whole value), THE constructor for the `fields[0..7]` octets (it
  REPLACED the `from_lossy_31bit_DANGER` fields hatch). ⚠ Hash-strength, **not injective** — see the
  corrected section above; lanes 1..7 have not carried "the higher bytes" since 2026-07-30;
- `Faithful8::ZERO` — the absent-material / vk-revoke sentinel;
- `Faithful8::from_lossy_31bit_DANGER(reason, limbs)` — the **greppable escape
  hatch** for named residuals (currently UNUSED — the burn-down list is empty).

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

### The `_DANGER` sites = the v13 burn-down list — **EMPTY (v13 DONE)**

`grep -rn from_lossy_31bit_DANGER --include='*.rs'` IS the burn-down list. It is
now **empty** of call sites: the `fields[0..7]` residual pair
(`cell/src/commitment.rs::compute_rotated_pre_limbs` +
`turn/src/rotation_witness.rs::produce`) was the last one, closed by the v13
fields-octet grow (`Faithful8::from_field_limbs8`). The constructor is retained
as the greppable hatch for any FUTURE named residual.

Adding a new `_DANGER` site without listing it here is a review-time violation.
