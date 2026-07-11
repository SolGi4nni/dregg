# CapOpen 32-bit maskRecon wrap — soundness investigation

**VERDICT: (A) REAL SOUNDNESS GAP — capability-authorization forgery.** The deployed cap-open
circuit reconstructs the FULL 32-bit effect mask in one weighted sum and binds it to the committed
leaf mask ONLY mod `p`. Because `2p = 0xF0000002 < 2^32`, a boolean 32-bit decomposition of
`mask + p` or `mask + 2p` also satisfies the recon gate mod `p`, and its per-bit values differ from
the honest mask's bits. An adversarial prover picks a decomposition whose selected bit `n` is set —
**forging submask membership for an effect the cap does NOT grant.** The Lean and the deployed Rust
AGREE (both `MASK_BITS / CAP_OPEN_MASK_BITS = 32`); this is not model-only. The Lean is HONEST about
it — `CapOpenRowCanon.reconExact` is an EXPLICIT carried assumption naming the residual — but that
assumption is **not enforced by any deployed constraint**, so the `effCapOpenV3_*_authorizes`
keystones are discharged on a hypothesis the wire does not pay for.

This is the SECOND instance of a wrap-residual CLASS (cf. `VAULT-CARRY-WRAP-INVESTIGATION.md`,
verdict A, 16-bit carry). Same root: a field-mod-`p` gate reconstructing a value whose honest range
reaches or exceeds `p`, with no range invariant pinning the ℤ value.

## 1. The Lean gate + canonicality (quoted)

`metatheory/Dregg2/Circuit/DeployedCapOpen.lean`:
- `MASK_BITS := 32` (line 258).
- `maskReconGate c` (335-337): `(mask_lo + mask_hi·65536) − Σ_{i<32} bitᵢ·2ⁱ = 0` — over `leaf[3]`
  (`mask_lo`), `leaf[4]` (`mask_hi`), and the 32 `bit` columns.
- `maskBitBoolGate c i` (329-330): `bitᵢ·(bitᵢ − 1) = 0` — each bit column boolean.
- `selectedBitGate c n` (347-348): `bitₙ − 1 = 0` — bit `n` (where `eff_bit = 1<<n`) must be set.

`metatheory/Dregg2/Circuit/Emit/CapOpenEmit.lean`:
- The recon gate is deployed AS a generic `.base (.gate (maskReconGate …))` inside
  `capOpenConstraintsEff` (270-279); the constraint list is `leafLookup + nodeLookups + dirBoolGates
  + maskBitGates + rootPinGates + [targetBind, effBitGateFor, maskRecon, selectedBit]`.
  **There is NO range lookup on the reconstructed sum.**
- `CapOpenRowCanon` (157-164) carries `reconExact : (maskReconGate c).eval env.loc = 0` — the
  ℤ-EXACT recomposition — as an explicit field. The §1.5 header (140-146) states it outright: "The
  ONE gate whose mod-`p` vanishing genuinely does NOT pin its ℤ value is the 32-bit mask
  recomposition … `2p < 2^32`, so a boolean decomposition of `mask ∓ p` (or `∓ 2p`) also vanishes
  mod `p` … the wrap dodge is a NAMED residual … priced here rather than laundered."
- `effCapOpenV3_satisfiedEff` (438-454) sets `maskRecon := hcanon.reconExact` — i.e. the ℤ-exactness
  is taken from the ASSUMPTION, not derived from the satisfied constraints. `effCapOpenV3_authorizes`
  (500-520) then requires `hcanon : CapOpenRowCanon …` as a hypothesis.

## 2. The deployed Rust (file:line)

`circuit/src/effect_vm/trace_rotated.rs`:
- `CAP_OPEN_MASK_BITS: usize = 32` (2484) — matches Lean.
- `fill_cap_open` (2882-2885): `full_mask = leaf[3] + leaf[4]·65536`; bits filled as
  `row[root_base + 10 + i] = (full_mask >> i) & 1`. This is the HONEST prover; the bit columns are
  free witness columns.
- The constraints realized are exactly the Lean `capOpenConstraintsEff` generic gates + lookups (the
  descriptor twin). **No range lookup on the mask sum; the leaf `mask_lo`/`mask_hi` limbs are NOT
  range-checked to `< 2^16`** — they are pinned to the committed Merkle leaf via `leafLookup`
  (fold-to-`cap_root`, `rootPinGate`), but their magnitude is unconstrained beyond the field.

**The adversary controls the decomposition independently of the pinned mask.** The mask VALUE
`mask_lo + mask_hi·65536` is committed (Merkle leaf → root pin). The 32 bit columns are separate
witness columns tied to that value ONLY by the mod-`p` recon gate. The prover chooses them.

## 3. The concrete exploit

Take a cap leaf whose committed mask `M` has bit `n` CLEAR (the cap does NOT permit effect-kind
`1<<n`) — e.g. `M = 0`, a cap that grants nothing, opened for `n = 1` (`EFFECT_TRANSFER`):
- Honest bits of `M=0`: all zero → `selectedBitGate 1` (`bit₁ − 1 = 0`) FAILS. Good.
- Adversary sets the bit columns to the boolean decomposition of `2p = 0xF0000002 = 4026531842`
  (`< 2^32`, so a valid 32-bit boolean vector). Then:
  - `maskBitBoolGate` ✓ (all bits 0/1);
  - `maskReconGate`: `M − Σ = 0 − 2p = −2p ≡ 0 (mod p)` ✓;
  - `selectedBitGate 1`: `bit₁ = 1` (bit 1 of `0xF0000002` is SET) ✓.
- All appendix constraints satisfied → `SatisfiedEff … 1` rebuilt → `authorizedFacetEffB caps
  provided (1<<1) = true`. **A cap granting nothing authorizes a TRANSFER.** Full capability
  escalation; any cap can be opened for any effect-kind `n` for which some `M+kp (< 2^32, k∈{1,2})`
  has bit `n` set (true for essentially every practical `M`, `n`).

Arithmetic (verified): `p = 0x78000001`, `2p = 0xF0000002 < 2^32`, `3p > 2^32`. Candidate boolean
sums for committed `M` are `{M, M+p, M+2p} ∩ [0,2^32)`; the adversary selects whichever has the
target bit set.

## 4. Why the vault fix does not transplant

Vault's fix was narrowing `CARRY_BITS 16→15` (honest carries fit 15 bits `< p`). Here narrowing is
NOT available: `EFFECT_ALL = 0xFFFFFFFF = 4294967295 ≥ p` is a LEGITIMATE broad-cap mask, so the
honest 32-bit range genuinely exceeds `p` and a "range-check Σ `< p`" would reject real caps. The
sound fix is to **decompose PER 16-bit LIMB**: range-check `mask_lo, mask_hi < 2^16` and reconstruct
each limb from its own 16 bits (each sum `< 2^16 < p`, hence a UNIQUE mod-`p` decomposition — no
wrap), reading bit `n` from `mask_lo` (`n<16`) or `mask_hi` (`16≤n<32`). That admits `EFFECT_ALL`
while pinning every bit exactly. `CapOpenRowCanon.reconExact` then becomes a DERIVED consequence of
the deployed per-limb range checks rather than a carried assumption.

## 5. Wrap-class audit — other reconstruction gates

| Gate | File:line | Width | Wrap? |
|---|---|---|---|
| `maskReconGate` (cap-open) | `DeployedCapOpen.lean:335` / `trace_rotated.rs:2882` | **32-bit**, honest range `[0,2^32) ≥ p` | **SUSPECT — verdict A (this doc)** |
| `gMaskRecon` (cap-reshape / delegation non-amp) | `EffectVmEmitCapReshape.lean:496`, `MASK_BITS=8` (443) | 8-bit, sum `< 256 < p` | SAFE by width (unique mod-`p` decomposition); anti-amp `gSubmaskBit` also on bits |
| Vault cross-carry recon | `VaultSatDescriptor` (see VAULT doc) | 16-bit carry, `2^16` reach past `−p` | **verdict A (separate doc, fix `16→15` pending)** |
| `reconMaskExpr`/`reconMaskN` helpers | `DeployedCapOpen.lean:262/268` | the `maskReconGate` engine | same as row 1 |
| RotationWide limb groups | `EffectVmEmitRotationWide.lean:130` | Poseidon2 CHIP-ABSORB inputs, equality-bound lane-for-lane (NOT a `Σ·2^k` scalar recompose) | SAFE — not a value reconstruction |
| `pow2Body` / DFA `stateGrid`/`transition` bodies | `AdjacencyMembershipEmit.lean:133`, `DfaRoutingEmit.lean` | small quadratic/boolean gridding, no `≥p` sum | SAFE — no wide weighted reconstruction |

Only `RowCanon` structure carrying an explicit `reconExact`-style ℤ-exactness assumption is
`CapOpenRowCanon` (line 164) — i.e. the maskRecon is the unique migrated cap-authorization gate that
launders the wrap into a carried hypothesis. Cell/bridge RowCanons (`CellSeal`, `BridgeMint`,
`SetField`, …) are cell-canonicality only, no weighted `≥p` reconstruction.

**Class summary:** the wrap-residual is a CLASS with two live verdict-A instances (vault carry,
cap-open maskRecon). The discriminant is always the same: a mod-`p` weighted reconstruction whose
honest value range reaches `p`, with no range invariant pinning the ℤ value. The audit found no
THIRD live instance among the migrated Emit gates (cap-reshape `gMaskRecon` is safe by its 8-bit
width; the rotation carriers are chip absorbs, not scalar recompositions).

## 6. What is undeterminable from the Rust

Nothing material — the deployed constraint set is fully visible (the descriptor twin of
`capOpenConstraintsEff`) and contains no range lookup on the mask sum or its limbs. The gap is
confirmed live, not undeterminable.
