# DESIGN — the shielded value on-ramp (Shield / Deshield)

**Architectural design. 2026-07-24. Ground-truthed at HEAD `ea496b225c`.** Resolves the open question
`docs/DESIGN-shielded-apex-tree-reconciliation.md` §7.1 — *"the value on-ramp: there is no
`Shield`/`Deshield` effect"* — which stands between the shielded apex redesign and **L4** (pin
membership to `note_shielded.root8()`, the route that closes seam #15).

House-law-1, said out loud: **every constraint described here is Lean-authored AIR.** The boundary
opening (C6), the append grow-gate, and the public-value tie are descriptor content emitted from
`metatheory/Dregg2/Circuit/Emit/`; Rust only fills witnesses and calls the emitted object. Nothing
below is a licence to hand-write a `Builder` gadget or an `air_accepts` predicate in Rust.

---

## 0. The three verdicts, up front

1. **Does value enter the shielded pool today? NO — and it never did.** There is no shield path, no
   mint path, and no ledger object anywhere in a shielded input's provenance. Input notes exist only
   as prover-fabricated Merkle witnesses. Worse than §7.1 states: the transfer **also publishes no
   output note commitment**, so shielded→shielded outputs are unspendable too. The pool is a
   proof-composition demo, not a value system. (§1)
2. **The on-ramp design:** `Shield` = spend a cleartext note, mint a Poseidon2 shielded note
   commitment appended to `note_shielded`, with the **amount public at entry** (Shield-A) so the
   whole boundary gate is Poseidon2 and needs no Pedersen leg at all. `Deshield` is its mirror. (§2)
3. **Can L4 land before the on-ramp? NO.** Not merely "it would reject everything" — L4 today has
   **no satisfiable instance**, its leaf encoding is **undetermined** without the appender, and
   committing `note_shielded.root8()` as populated today (L1) would pin membership to a tree the
   **prover writes into**, relocating #15 rather than closing it. (§3)

---

## 1. How value enters the shielded pool today: it does not

### 1.1 The inputs — proven against a root the prover invented

`apply_shielded_transfer` (`turn/src/executor/apply.rs:1713`) reconstructs the transfer from the wire:

```rust
let transfer = ShieldedTransfer::from_serialized_parts(
    payload.merkle_root,                     // apply.rs:1749 — a wire u32 (action.rs:1021)
    payload.inputs.iter().map(|i| (i.nullifier, i.legacy_value_binding, i.spend_proof.clone())).collect(),
    …)
```

`payload.merkle_root` becomes `BabyBear::new(merkle_root)` (`circuit-prove/src/shielded/transfer.rs:286`)
and every input's hiding spend proof is verified against **that** felt
(`input.public_inputs(self.merkle_root)`, `transfer.rs:91-95`, verified `:155`). The membership leaf
`hash_fact(value,[asset,owner,randomness])` and the whole arity-4 Merkle path are **witness data**
(`circuit-prove/src/shielded/spend_circuit.rs` cols `VALUE=12 … LEAF_COMMIT=16`,
`pi::{NULLIFIER=0, MERKLE_ROOT=1, VALUE_BINDING=2}`, `PUBLIC_INPUT_COUNT=3`).

So "this input note exists" is proven **relative to a root the prover chose**. The only producers in
the tree do exactly that, explicitly:

```rust
let w = make_input(11, amount, in_blinding, 0xABCD, 4);   // fabricated deterministic siblings
let merkle_root = w.spend.merkle_root();                  // the root COMPUTED FROM the fabrication
```
(`turn/src/executor/apply.rs:5085-5087`; identically `circuit-prove/tests/shielded_transfer_m2a.rs:113-114`,
`make_input` at `:54-102`.)

**There is no mint, no shield, no genesis, and no ledger read anywhere in an input's provenance.**

### 1.2 The outputs — Pedersen legs, not notes

```rust
pub struct ShieldedLeg {          // turn/src/action.rs:974-979
    pub asset_type: u64,
    pub commitment_bytes: [u8; 32],   // compressed Ristretto Pedersen VALUE commitment
}
```

That is the **entire** output. There is no output note commitment, no `owner`, no `randomness`, no
encrypted note ciphertext. The circuit-side object agrees (`ShieldedTransfer` fields,
`circuit-prove/src/shielded/transfer.rs:111-136`: `merkle_root`, `inputs`, `input_legs`,
`output_legs`, `output_range_proofs` — no output note commitment).

**Consequence:** a shielded output is not a note. Not even the intended recipient receives an object
that could be the leaf of a future spend. The pool has no circulation, independent of the on-ramp.

### 1.3 What GATE 4 (L0) actually appends

```rust
// apply.rs:1846-1854
let mut set = self.note_shielded.lock().unwrap();
for leg in &payload.output_legs {
    let commitment = ShieldedNoteCommitment(leg.commitment_bytes);   // ← THE WIRE BYTES, VERBATIM
    set.insert(commitment)…;
    journal.record_shielded_note_inserted(commitment);
}
```

L0 landed the right *type* (`cell/src/shielded_note_set.rs`: hiding leaf
`HeapLeaf::entry(fold_bytes32_to_bb(cm), ZERO)`, 8-felt `root8()`, AAFI seq, rollback) and the right
*plumbing* (`turn/src/journal.rs:145,502,682`; executor field `executor/mod.rs:901,1221,1304,1357`).
Its own module doc is honest that the appended object is a placeholder (`apply.rs:1836-1845`:
*"WHICH 32-byte commitment becomes the canonical membership leaf is the single committed-tree
ENCODING decision of L2 / L4"*). This design closes that decision — and §3 shows why it must be
closed before, not after, L1/L4.

### 1.4 Reachability — is the pool used on any live path?

**No.** `grep Effect::ShieldedTransfer` across the workspace yields dispatch/classification arms and
**test constructors only** (`turn/src/executor/apply.rs:5045,5073,5114`;
`circuit-prove/tests/shielded_transfer_m2a.rs`). No SDK, CLI, node, or web surface builds a
`ShieldedTransferPayload`. And a verify-only build fails the effect closed (`apply.rs:1861-1876`), so
even in principle it is node-operator-trust only.

### 1.5 The lifecycle, honestly

| hole | what is missing | named where |
|---|---|---|
| **H1 entry** | no `Shield` effect; the `Effect` enum has only `NoteSpend`, `NoteCreate`, `ShieldedTransfer` (`action.rs:1122,1145,1529`) | reconciliation §7.1 |
| **H2 circulation** | the transfer publishes **no output note commitment** — shielded→shielded outputs are unspendable (§1.2) | **nowhere; found here** |
| **H3 exit** | no `Deshield` effect; value cannot leave the pool | reconciliation §7.1 (implicitly) |

The reconciliation doc names H1. H2 is the one that makes "the pool is unusable" true even if H1 and
H3 were both built.

---

## 2. What the on-ramp must be

### 2.1 The hinge: both sides already speak Pedersen — and that is the trap, not the answer

dregg's *cleartext* note path is already optionally value-committed. `detect_commitment_mode`
(`turn/src/executor/finalize.rs:157-188`) splits `Cleartext / Committed / Mixed / Empty`, and the
`Committed` arm runs a turn-level Schnorr excess over the collected `ValueCommitment`s bound to
`turn.hash()`, plus per-output Bulletproof range proofs (`check_committed_conservation`,
`finalize.rs:192-225`; `collect_committed_notes_from_effect`, `:253-288` — `NoteSpend` legs are
inputs, `NoteCreate` legs are outputs; **a `ShieldedTransfer` contributes nothing**, falling in the
`_ => {}` arm). The shielded transfer runs the *same* primitive over its *own* legs and its *own*
transcript (`apply.rs:1772-1781`).

It is tempting to make `Shield` "one excess proof spanning a cleartext leg and a shielded leg" — that
is the amount-hiding design (Shield-B, §2.3). **It is the wrong first move**, because nothing ties the
hidden `v` in the Pedersen leg to the `value` inside the note commitment: that is exactly the #16
wound `ShieldedValueLinkPin.genuine_note_inflates` falsifies (a genuinely-owned `v`-note mints `v+1`
with conservation passing). Shield-B inherits #16 *and* #17 (Shor-broken Ristretto in the no-mint
TCB) at the moment value enters the system.

### 2.2 Shield-A (RECOMMENDED for v1) — amount public at entry, Poseidon2 all the way

`Effect::Shield` consumes one cleartext note and mints one shielded note.

**Consumes** — identical gates to `apply_note_spend` (`apply.rs:1340-1580`), reused verbatim, not
re-authored: nullifier well-formedness, the strict FNSP-v2/v3 carrier bound to the authenticated
historical note root **and** the exact planned nullifier-accumulator successor
(`verify_faithful_note_spend_v2`, `apply.rs:1584-1670` — note this path already recomputes
`planned.faithful_root8_exact()` and refuses a carrier that does not match), then the journaled
single insert into `note_nullifiers`.

**Mints** — the effect carries:

| field | type | role |
|---|---|---|
| `note_commitment` | `ShieldedNoteCommitment([u8;32])` | the **Poseidon2** image `hash_fact(value,[asset_type, owner, randomness])` — exactly `ShieldedSpendPortDischarge.IsCommittedNote` (`metatheory/Dregg2/Circuit/ShieldedSpendPortDischarge.lean:109`) and the spend gadget's C6a/C6b leaf. **This** is what lands in `note_shielded`, never a Pedersen point. |
| `value`, `asset_type` | `u64` | public at entry; the conservation identity is a public integer equality |
| `encrypted_note` | `Vec<u8>` | the recipient's `(value, asset, owner, randomness)` opening — reuses `NoteCreate`'s existing ciphertext slot (`action.rs:1153`) so the recipient can later spend. **Without this the shielded note is unspendable — H2's lesson applied at the entry.** |
| `shield_proof` | `Vec<u8>` | the Lean-emitted descriptor proof (§2.4) |

**Conserves** — `value_in == value` as a plain `u64` equality the executor checks in the clear, with
`asset_type_in == asset_type`. No Pedersen leg, no Schnorr excess, no Bulletproof at the boundary.
The *only* thing the executor cannot check itself is that the published `note_commitment` really
opens to `(value, asset_type)` — it lacks `owner`/`randomness`. That is precisely what the AIR proves
(§2.4). **Post-quantum posture: the entry gate is Poseidon2-only**, strictly better than the
transfer's own Ristretto conservation and unaffected by residual #17.

### 2.3 Shield-B (LATER) — amount hidden at entry

Source is a *committed* cleartext note (`NoteSpend { value_commitment: Some(C_in), .. }`); the shield
publishes `C_out`; one Schnorr excess proves `C_in − C_out = r_excess·R`, reusing
`check_committed_conservation` verbatim. This hides the amount at entry — a property Zcash's t→z
shielding does **not** have — but it is only sound once the leaf↔leg value-link is a circuit
constraint, i.e. once `shieldedValueLinkDesc`
(`metatheory/Dregg2/Circuit/Emit/ShieldedValueLinkDescriptor.lean:205`) is emit-wired (L3) and routed
(L4). **Ordering: Shield-B strictly after L3+L4. Shield-A does not depend on either.**

### 2.4 The AIR — Lean-authored, three constraint blocks, all already modeled

A new module `Dregg2.Circuit.Emit.ShieldedShieldDescriptor` (to be created under
`metatheory/Dregg2/Circuit/Emit/`), emitted as
`dregg-shielded-shield::v1`. PIs: `(piVALUE, piASSET, piCM, piROOT_BEFORE, piROOT_AFTER)`.

1. **C6 opening** — `piCM = hash_fact(piVALUE, [piASSET, owner, randomness])` over witness
   `owner`/`randomness`. **Reuse the existing shape verbatim**: it is the same relation
   `IsCommittedNote` (`ShieldedSpendPortDischarge.lean:109`) that `emitted_leaf_isCommittedNote`
   (`:132`) already discharges for the spend side. Do not author a second note-commitment relation —
   two shapes for one object is how the encoding split happened in the first place.
2. **The append grow-gate** — `piROOT_AFTER = append_at_free_index(piROOT_BEFORE, piCM)`. The model
   exists and is the one wired shielded descriptor: `ShieldedWholeNoteSwapSubstrateDescriptor`
   proves *"the private computation, output-note commitment, and binary depth-32 linked exact
   append"* (`circuit-prove/src/shielded_whole_note_swap_substrate.rs:16-18`; `TREE_DEPTH = 32`,
   `ROOT_LANES = 8`, `output_notes_root()` at `:213`, and the exact-cursor check
   `append_path.position != pre_count → reject` at `:655`). L2 generalizes that append; the Shield
   is its **first single-note consumer** and is strictly simpler than the two-party swap.
3. **The public-value tie** — a `.piBinding` of `piVALUE` to the same in-AIR value cell C6 opened.
   One descriptor line; it carries the entire conservation content of the boundary.

**Non-negotiable:** `piROOT_BEFORE` is **executor-sourced** from `note_shielded.root8()`, never from
the wire. The reconciliation doc makes this exact point about `piCOMMITTED` (§2.2: *"if the executor
fills it from anything the prover controls, #15 simply reopens one level up"*) — it applies with
equal force to the append's pre-root.

### 2.5 Deshield (exit) — the mirror, and the pin's first real consumer

`Effect::Deshield` consumes one shielded note and mints cleartext value.

- **Consumes:** the same `shieldedSpendDesc` membership+nullifier proof, with membership pinned to
  `note_shielded.root8()` — **this is L4's pin, and Deshield is what makes it non-vacuous.** The
  nullifier is consumed once (§5.3 on which set).
- **Mints:** a public `value: u64` — either credited to a cell or landed as an ordinary
  `Effect::NoteCreate` in `note_commitments` with its cleartext `(commitment, value)` leaf
  (`apply.rs:2275-2296`).
- **Conserves:** the in-AIR `value` cell of the spent shielded note is published as a PI and the
  executor checks `value_out == piVALUE`. In-AIR that is precisely the
  `shieldedValueLinkDesc` "leafValue = legValue" content (`emitted_linkHolds`,
  `ShieldedSpendPortDischarge.lean:267`) with the free Pedersen leg replaced by a **public felt** —
  which is why the exit, like the entry, needs no curve.

**The resulting global property, stated plainly:** the pool is a black box that publishes
`Σ shielded-in` and `Σ shielded-out` in the clear and hides everything in between. Value conservation
across the boundary is a public integer identity at both ends and an in-AIR identity inside.

### 2.6 Privacy at the boundary — is a public entry amount acceptable?

Yes, and it is the standard posture, but the honest statement is narrower than "Zcash does it too":

- Shield-A reveals `(amount, asset)` at entry and links the spent cleartext note to the turn. It does
  **not** link the shielded note to its future spend: the nullifier is `hash_fact(cm, key[0..4])`
  computed inside the hiding STARK, and the spend proof's openings are blind (`HidingFriPcs`,
  `circuit-prove/src/shielded/mod.rs:26-30`). The anonymity set at spend time is *the whole
  `note_shielded` set*, which is the correct and maximal one.
- The comparison that actually holds: Zcash's t→z shielding transaction reveals the amount for the
  same structural reason (the transparent side must debit a public balance). Fixed-denomination
  mixers reveal the denomination instead.
- **The caveat that is dregg-specific and must not be laundered:** the anonymity set starts EMPTY and
  grows one note at a time. The first shield is fully linkable; the k-th is linkable to within k.
  This is a real product property, not a soundness bug, and it does not improve until the pool has
  volume. Fixed shieldable denominations would help both this and §5.2's range problem.

---

## 3. THE L4 ORDERING ANSWER — the on-ramp first. Decisively.

**L4 (pin membership to `note_shielded.root8()`) must NOT land before the on-ramp.** Three
independent reasons, in increasing severity. Only the first is the "the pool is empty so pinning is
free" argument, and it is the weakest.

### 3.1 L4-alone has no satisfiable instance — it is a fence with a VK epoch stapled to it

`note_shielded` is empty on every live node (nothing but GATE 4 appends, and nothing constructs the
effect, §1.4). Beyond emptiness, the two objects are not comparable at all:

| | membership root the spend proves | `note_shielded.root8()` |
|---|---|---|
| width | **1 felt** (`pi::MERKLE_ROOT`, `spend_circuit.rs:159`) | **8 felts** (`Faithful8`, `shielded_note_set.rs:297`) |
| structure | arity-4 plain Poseidon2 Merkle | depth-16 **BINARY-node sorted IMT** (arity-3 LEAF) with `next_addr` links (`circuit/src/heap_root.rs:62,108-109,143-149`) |
| leaf preimage | `hash_fact(value,[asset,owner,rand])` | `hash[fold(pedersen_bytes), 0, next_addr]` |

There is no wire assignment satisfying the pin. **L4-alone is `Effect::ShieldedTransfer => Err(..)`
with a flag-day attached.** The identical behavior is available for free as the DECISION brief's
Option C fence (3 lines, zero VK) — and L1, the epoch L4 needs, *re-baselines every rotated
descriptor VK* (reconciliation §6, precedent `revoked_root` base limb 37,
`turn/src/rotation_witness.rs:72`). Spending the heaviest VK epoch in the plan to buy a fence is the
wrong trade. Landing it and *calling* it a #15 closure would be the "a real gate pointed at a
re-authored fixture, asserted CLOSED" register error.

### 3.2 L4's leaf encoding is UNDETERMINED without the appender

Reconciliation §7.2 asks the central unresolved question — arity-4 plain Merkle, or the AAFI IMT? —
and it has **no answer until you know what puts leaves in.** The on-ramp *is* the appender, and it
forces the answer: the leaf must simultaneously be (a) the object the spend gadget opens
(`IsCommittedNote`) and (b) the object the append gate mints. One object, two constraints, one
decision — §2.4 makes it the Poseidon2 note commitment over the substrate's exact-append encoding.
Deciding L4's encoding *before* the on-ramp is guessing; deciding it *with* the on-ramp is forced.

### 3.3 ⚑ Committing today's `note_shielded` (L1) is actively UNSOUND — the strongest reason

GATE 4 appends `ShieldedNoteCommitment(leg.commitment_bytes)` — **bytes taken verbatim from the
prover's wire** (`apply.rs:1849`). They are a Ristretto Pedersen point encoding; nothing constrains
them to lie in the image of `hash_fact(value,[asset,owner,rand])`. The set's sort key is
`fold_bytes32_to_bb(commitment)` — 32 bytes squeezed to one ~31-bit felt
(`shielded_note_set.rs:277-283`), so a prover can additionally *grind the blinding* to place a chosen
address in the tree at ~2^31 work.

Therefore **`AccumulatorSound` is FALSE for `note_shielded.root8()` as populated today.** That is
exactly the `NoteAccumulatorCR` hypothesis `pin_accept_is_note_committed` requires
(`ShieldedSpendPortDischarge.lean:174,182`), and exactly what R1 was introduced to discharge *in
reality* (reconciliation §2.2). It is harmless **only** because `root8()` is committed nowhere. The
moment L1 lands it as a carrier base limb, the L4 pin binds membership to a tree the prover writes
into: **seam #15 does not close, it relocates one level up** — the precise failure mode the
reconciliation doc warned about for `piCOMMITTED`.

This is now an **armed regression test**, not prose:
`turn/src/executor/apply.rs::shielded_executor_tests::shielded_append_is_prover_written_not_ledger_derived`.

### 3.4 The corrected schedule

Insert **L0.5** as a hard dependency of L1 and L2:

| lane | work | byte-safe? | depends on |
|---|---|---|---|
| L0 | `ShieldedNoteSet` + executor field + journal | landed (byte-safe) — but its append writes the **wrong object** | — |
| **L0.5** | **on-ramp encoding decision (§2.4) + GATE 4 appends the decided Poseidon2 note commitment + the wire carries it** | **NO** — needs `ShieldedTransferPayload`/`Effect` changes ⇒ `effects_hash` ⇒ VK | this doc |
| L1 | `shielded_note_root` carrier base limb | regen; **heaviest epoch** | **L0.5** |
| L2 | Lean append grow-gate | regen (new descriptor VK) | **L0.5** |
| L3 | emit-wire the three already-proven descriptors | regen (additive) | — (**parallel, land any time**) |
| L4 | route `apply_shielded_transfer`: pin + append + source `piCOMMITTED` | cutover | L1, L2, L3 |
| L5 | fold the shielded segment into the committed turn | VK epoch | L4 |

L3 remains genuinely independent and changes no behavior — if a lane wants forward motion on the
apex redesign *today*, **L3 is the one to run**, not L4.

---

## 4. The byte-safe first step

| piece of the on-ramp | byte-safe? | why |
|---|---|---|
| the encoding decision (§2.4) | free | a document |
| **falsifier: `note_shielded` is prover-written** | **YES — IMPLEMENTED** | test-only; no wire, no VK, no behavior. Arms §3.3 so L1/L4 cannot land past it silently. |
| Lean `ShieldedOnRampPin.lean` (boundary conservation model + falsifier: an unconserved shield mints) | YES | metatheory-only, the exact precedent of `ShieldedMerkleRootPin.lean` / `ShieldedValueLinkPin.lean`, both of which landed ahead of the deployed change. **The recommended next lane.** |
| GATE 4 leaf correction | **NO** | requires an output note commitment on the wire ⇒ `ShieldedTransferPayload` change ⇒ `effects_hash` change |
| `Effect::Shield` / `Effect::Deshield` variants | **NO** | appending variants is wire-additive (postcard varint discriminants; no existing turn holds one), but each needs an `effects_hash` arm (`action.rs:2520,2695`), an `EFFECT_*` kind (`:2784`), a `LinearityClass` (`:1895`), authorize/pipeline/reversible arms — and decisively a **descriptor rung**, because it MOVES VALUE. `SetProgram` set the precedent for landing an executor path with no circuit witness (`action.rs` doc: *"binding the program write into the turn commitment is VK-affecting (ember-gated)"*) — applying that precedent to **money** is a different question and is ember's call. |
| the shield/append AIR | **NO** | Lean-authored, new `dregg-shielded-shield::v1` VK |
| `note_shielded` carrier limb | **NO** | the L1 flag-day |

**Implemented here:** the falsifier test. It asserts that GATE 4 appends the wire bytes verbatim,
that `root8()` therefore moves to a prover-determined value, and that what landed decodes as a
Ristretto `ValueCommitment` — i.e. a Pedersen *value* commitment, not the Poseidon2 *note* commitment
the membership gadget opens. When the on-ramp lands, that test must be rewritten; **the rewrite is
the tripwire.**

---

## 5. Honest open tensions

1. **Value conservation across two trees with different value encodings — unresolved.** The cleartext
   committed leaf carries `split_u64(value).0`, the **low 30 bits** of a `u64`
   (`cell/src/commitment_set.rs:262-273`). The shielded leaf carries the value only inside a
   Poseidon2 hash over BabyBear felts (`p < 2^31`). Neither faithfully represents a full `u64` in one
   felt. So the boundary identity `value_in == value_out` is a clean `u64` check *in the executor*,
   but the in-AIR C6 opening reduces `value` **mod p** — the same aliasing hazard
   `modulus_alias_splice_rejects_at_real_executor_no_mint_entry` (`apply.rs:5150`) guards for the
   wide binding, and the same residual as the PLAN's "BabyBear caps a conserving sum near `2^30/N`"
   (`shielded_ring_clearing_nleg_air.rs:85-91`). The on-ramp must either carry the value in the
   16-lane wide encoding (`WideValueBindingProof`, `action.rs:1000-1002`) or cap shieldable amounts.
   **Not resolved by this design. It is the first thing the Lean lane should model.**
2. **`piCOMMITTED` is ONE felt — "8-felt root retires the ~31-bit width" is not automatic.**
   `shieldedSpendDesc.piCount == 4` with `piCOMMITTED : Nat := 3` a single lane
   (`ShieldedSpendDescriptor.lean:160,275`), and the root-binding adapter binds exactly
   `ROOT_BOUND_LANES = 2` single lanes (`shielded_spend_leaf_adapter.rs:607`). Sourcing `piCOMMITTED`
   from an 8-felt `root8()` therefore requires either folding 8→1 (**reintroducing the ~31-bit
   width #15 entered through**) or widening the PI to an 8-lane group — a *descriptor* change, not a
   wiring change. The substrate's `output_notes_root()` is already 8 lanes
   (`shielded_whole_note_swap_substrate.rs:213`). **Recommendation: widen the pin to 8 lanes when the
   descriptor is (re)emitted at L3.** This partially revises reconciliation §4's "1→8 felt width"
   claim, which reads as if L0's `root8()` alone delivers it.
3. **Nullifier segregation (reconciliation §7.3) stops being bookkeeping at the exit.** Shielded
   nullifiers currently share `note_nullifiers` with a hardcoded value `0` (`apply.rs:1813`, the
   placeholder). Once `Deshield` exists, a shielded spend's value is no longer meaningless, and the
   `0` becomes a false entry inside a **value-carrying** accumulator whose leaf column the cleartext
   grow-gate reads. Segregating `note_shielded_nullifiers` becomes **required**, not optional —
   batch it into L1's epoch as the reconciliation suggests, but do not treat it as deferrable.
4. **H2 (circulation) is a wire change nobody has scoped.** Shield + Deshield give entry and exit;
   shielded→shielded still publishes no output note commitment (§1.2), so a shielded note can be
   created only by shielding and spent only by deshielding. That is a *shielded custody* product, not
   a shielded *transfer* product. Fixing H2 is the same wire change as L0.5 (an output note
   commitment + ciphertext per output leg) — **do them together or the pool stays a one-hop pipe.**
5. **The anonymity set starts at zero** (§2.6). Not a soundness property; do not narrate it as one in
   either direction.

---

## Summary

Value has never entered the shielded pool: input notes are prover-fabricated Merkle witnesses
(`apply.rs:5085-5087`), outputs are Pedersen legs with no note commitment (`action.rs:974-979`), and
no production surface constructs the effect. The on-ramp is `Shield` — spend a cleartext note, mint a
**Poseidon2** note commitment `hash_fact(value,[asset,owner,rand])` into `note_shielded` with the
amount **public** at entry, conserved by a public `u64` identity and a Lean-authored C6-opening +
free-index-append descriptor, needing no curve at the boundary — and `Deshield`, its mirror, which is
what makes L4's pin non-vacuous. **L4 cannot land first**: it has no satisfiable instance, its leaf
encoding is undetermined without the appender, and — decisively — GATE 4 currently appends
prover-supplied wire bytes, so `AccumulatorSound` is **false** for `note_shielded.root8()` today and
committing it would relocate #15 rather than close it. The byte-safe step taken here is the falsifier
that arms that fact; the recommended next byte-safe lane is the Lean boundary-conservation model, and
the recommended parallel lane is **L3**, which is the only part of the redesign that is genuinely
unblocked.
