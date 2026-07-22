# Shielded exact apex v4: emitted-relation and verifier-key seam

Status: semantic relation landed; no emitted AIR or runnable prover is claimed here.

The Lean source is `metatheory/Dregg2/Circuit/ShieldedExactApexV4.lean`. Its exact umbrella import,
once the active `Dregg2.lean` owner is ready to register it, is:

```lean
import Dregg2.Circuit.ShieldedExactApexV4
```

The standalone gate is:

```sh
cd metatheory
lake env lean Dregg2/Circuit/ShieldedExactApexV4.lean
```

## What the relation fixes

The relation has one selected hidden note opening. The same typed opening supplies:

1. a full sixteen-u16-limb nullifier derivation;
2. the sixteen-lane native-PQ value/asset commitment;
3. the selected head of the hidden input list used by per-asset conservation; and
4. the fixed market/game consequence that creates the output-note list.

There is no clear value or asset in the public statement. Other private inputs may appear after the
selected spend so a closed AMM/ring update can conserve each asset across all consumed and created
notes, rather than pretending that a cross-asset trade is a same-asset transfer.

The fixed market surface is typed as exactly nineteen Dark-AMM lanes, twenty-seven two-leg ring
lanes, and a `Fin 2` selected leg. An emitter cannot silently omit a lane, add a trailing lane, or
select a third leg.

The v4 exact state uses a root rewrite over the full nullifier and all sixteen wide-binding lanes,
plus the exact `after.count = before.count + 1` law. It is intentionally not FNSP-v3/FNI2, whose
public statement and leaf preimage contain a clear four-limb value.

## Rust ABI mapping

`circuit-prove/src/shielded_exact_apex_v4.rs` defines the 100-lane outer ABI. The Lean relation in
this note owns the shielded subrelation fields:

| Rust field | Lean semantic field |
|---|---|
| full nullifier, 16 u16 lanes | `PublicStatement.nullifier : RawNullifierKey` |
| hidden value/asset binding, 16 field lanes | `PublicStatement.valueAssetBinding : WideDigest` |
| prior/successor exact roots and counts | `exactBefore`, `exactAfter` |
| output-note root | `outputNotesRoot` |
| FXC4 consequence root | `consequence` |

Historical note-root membership and full outer pre/post state belong to the surrounding exact-v4
consensus/frame relation. They should be joined to this subrelation by the accepted-statement digest,
consequence commitment, output-note commitment, and exact before/after points—not duplicated as a
second shielded semantics.

## Fixed emitted descriptor

A Lean-authored emitter should compile one relation with the following witness columns and checks:

- selected note: canonical value, asset, binding randomness, owner, nonce, and nullifier secret;
- optional additional private inputs and the complete ordered output list;
- full Dark-AMM and ring public surfaces with the selected leg;
- canonical u16 decomposition for every integer-bearing word;
- full nullifier derivation into all sixteen public limbs;
- the sixteen-lane wide Poseidon commitment from the selected note's same value/asset opening;
- the fixed Dark-AMM/ring/game rule over the hidden inputs and outputs;
- per-asset conservation over exactly those input and output lists;
- one note commitment per output, their exact ordered list, and its eight-lane output root;
- the FNI4 root rewrite and exact count increment;
- FXC4 over the full nullifier, wide binding, exact endpoints, fixed market surface, output count,
  and output root.

The old scalar `legacy_value_binding` may be retained only as a migration compatibility check. It is
not a same-opening proof: openings separated by the BabyBear modulus can share that scalar. The
emitted relation must use the selected witness columns directly for both the wide commitment and
conservation constraints.

## Verifier identity and proof-system seam

The Lean `PinnedVerifierContract` names the intended boundary. Deployment still needs:

1. a canonical descriptor serialization and relation ID;
2. a verifier-key digest derived for exactly that descriptor and fixed proof parameters;
3. code-owned verifier dispatch that refuses caller-selected IDs, keys, dimensions, or FRI knobs;
4. a translation/refinement theorem from emitted acceptance to `Relation`;
5. a knowledge-soundness argument for the deployed HidingFRI/Poseidon construction; and
6. durable admission that persists the exact frame, full nullifier, output notes, and executor state
   in one transaction.

`PinnedVerifierContract.knowledgeSound` is deliberately a required field, not an axiom secretly
inhabited by this module. The standalone Lean proofs show what follows if that fixed contract is
discharged; they do not claim that the current Rust verifier already discharges it.

## Cryptographic floors kept explicit

- Canonical serialization and shared-witness wiring are unconditional structural theorems.
- Distinct wide openings with the same digest reduce to the explicit Poseidon transcript collision
  event from `WideNativePqCommitment`.
- Distinct output-commitment lists with one output root reduce to `OutputRootCollision`.
- Distinct FXC4 semantic preimages with one consequence digest reduce to `ConsequenceCollision`.
- Nullifier PRF security, note commitment hiding/binding, Poseidon collision resistance in the
  deployed parameterization, and HidingFRI knowledge soundness remain computational obligations.

No Ristretto/Bulletproof claim is used to call this relation post-quantum. If the deployed
conservation proof remains curve-based, the live composite remains classical even though the wide
carrier and FRI layer are hash-based. The native-PQ route is to emit conservation directly in this
fixed relation or replace every classical subproof with a proved same-opening PQ construction.
