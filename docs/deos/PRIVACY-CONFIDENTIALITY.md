# Privacy & Confidentiality

> **STATUS — Milestone 0 SHIPPED; the crypto organs live in the `dregg-cell-crypto` crate.**
> The read-cap rung this document designs has landed: `ReadCap` (with `ReadCap::attenuate`,
> the `granted.slots ⊆ held.slots` read-lattice) lives in `cell-crypto/src/read_cap.rs`
> (crate `dregg_cell_crypto`), the membrane read-side dual welds through it
> (`cell/src/membrane.rs`, `crate::read_cap::ReadCap::attenuate`), and the moldable
> inspector surfaces it live in `starbridge-v2/src/read_cap_lens.rs` (which states outright
> "the privacy weld landed … PRIVACY-CONFIDENTIALITY.md Milestone 0"). So **§4 Milestone 0
> below is delivered**, not the next ship. **M1** (selective disclosure) and **M2**
> (ZK-private cells, VK-affecting, ember-gated) remain the forward rungs.
>
> Also note the §0 primitive citations: the ECIES note-encryption / stealth / value-commitment
> / sealer / oblivious-transfer primitives moved out of `cell/src/` into the dedicated
> `dregg-cell-crypto` crate — their paths are `cell-crypto/src/*` throughout (fixed inline below).

dregg's authority model is cold on **write**: a capability says who may *change* a
cell's state, attenuably, with a verifiable receipt. The dual question — who may
*read* a cell's state — is not yet a first-class capability, even though almost
every confidentiality primitive it would need already exists in the tree,
disconnected. This document maps what is here, names the gap, and designs the
**read-cap** + **encrypted cell state** + **ZK-private cell** layer that closes it.

The through-line, stated once: *a read is the exercise of an attenuable
viewing-authority over committed state, leaving no trace and revealing nothing
beyond what the authority discloses.* It is the write-discipline run backwards —
authority over decryption rather than authority over mutation.

---

## 0. What exists today (the disconnected organs)

dregg already carries a near-complete confidentiality toolbox. The lacks survey
that prompted this document found it "thin" because nothing **welds** these into a
read-authority; the pieces themselves are real and, several of them, Lean-proven.

| Organ | File | What it gives |
| --- | --- | --- |
| **Per-field visibility** | `cell/src/state.rs:74` `FieldVisibility { Public, Committed, SelectivelyDisclosable }`; `CellState.field_visibility[16]`, `commitments[16]` (`state.rs:103-108`) | Each of a cell's 16 state slots is independently *public*, *committed* (only a hash is on-chain, value private), or *selectively disclosable* (committed + provable without reveal). The data model for read-confidentiality is **already in the cell**. |
| **ECIES note encryption** | `cell-crypto/src/note_encryption.rs` | X25519 ephemeral DH → BLAKE3-KDF → ChaCha20-Poly1305. Encrypts a note opening so *only the recipient may read it* (`note_encryption.rs:6`), drops straight into `Effect::NoteCreate { encrypted_note }`. The recipient's `view_pubkey` is the decryption authority. |
| **Anonymous notes** | `cell/src/note.rs` | Consume-once cells with *private state*: a Poseidon2 commitment to `(owner, fields[8], randomness, nonce)`; spend = reveal a nullifier only the owner can compute. Validity is self-proving (STARK + Merkle path), contents hidden. |
| **Stealth addresses** | `cell-crypto/src/stealth.rs` | Monero/EIP-5564 one-time CellIds: a `view_pubkey` lets the recipient *scan* for incoming notes; a `spend_pubkey` controls spending. Unlinkable identities → metadata privacy. |
| **Value commitments** | `cell-crypto/src/value_commitment.rs` | Pedersen-over-Ristretto: hiding + binding + homomorphic. The executor verifies conservation (`Σin − Σout = excess`) **without learning amounts**. |
| **Sealer/Unsealer** | `cell-crypto/src/seal.rs` | E-style rights-amplification: X25519 + ChaCha20-Poly1305 sealed boxes for partition-tolerant capability transfer (forward-secret per seal). |
| **Oblivious transfer** | `cell-crypto/src/oblivious_transfer.rs` | 1-of-n OT (Naor-Pinkas-style) — the receiver learns one message, the sender learns nothing about which. A building block for private queries. |
| **Membrane / per-viewer projection** | `starbridge-web-surface/src/affordance.rs:387` (`Viewer`, `Membrane`, `project_membrane`, `membrane_shows`) | The fog-of-war: a surface projects DIFFERENT affordance/content sets to different viewers along **two** dimensions — the cap dimension (`is_attenuation`) AND a `permits` *disclosure bit* (witness-graph clearance). Two viewers at equal cap-authority but different `permits` see distinct surfaces. **Lean-proven** non-amplifying (`metatheory/Dregg2/Deos/Membrane.lean`, twin `membraneShows`). |
| **ZK-hiding STARK** | `circuit/src/stark_zk.rs` | `p3_fri::HidingFriPcs` (PCS `ZK=true`) over `MerkleTreeHidingMmcs` (salted leaves): the *same* prove/verify doubles the trace with random rows, commits a random codeword, and salts every leaf so query openings *reveal nothing about the witness beyond the public inputs*. Statistically ZK by construction. The circuit already proves "I performed action X" without revealing the chain/caps (`circuit/src/lib.rs:47,72`). |

**The gap, precisely:** none of these is wired to a `Permissions`-style
**read-authority**. `cell/src/permissions.rs` has eight `AuthRequired` slots
(`send, receive, set_state, set_permissions, set_verification_key,
increment_nonce, delegate, access`) — **all gate WRITE**. There is no `read`/`view`
slot, no read-cap, and no path from "I hold this attenuated cap" to "therefore I
may decrypt slots 3–5 of this cell." The membrane's `permits` disclosure bit is
the closest thing, but it lives only in the surface layer and is a free closure,
not a delegable, revocable, receipt-leaving capability on the cap substrate.

---

## 1. Threat model & what "confidentiality" means here

We separate **four** confidentiality questions. They are independent; a system can
win some and lose others, so we name each with its adversary and its current status.

### 1a. Read-confidentiality — *who may READ a cell's state*
> **Adversary:** a party who can observe the ledger / fetch a cell but should not
> learn its contents.

The dual of write-authority. Today `FieldVisibility::Committed` hides a value
behind a hash, but there is no *authority* that lets a designated holder read it —
the value is simply private to whoever generated it. **Confidentiality here means:
a cell field is encrypted, and a *read-cap* is the decryption authority, attenuable
and revocable exactly like a write-cap.** This is §2 — the first buildable rung.

### 1b. Metadata privacy — *who-talks-to-whom, when, how much*
> **Adversary:** a network/ledger observer doing traffic analysis even when
> payloads are encrypted.

The hardest tier and the one most systems lose. dregg has the *primitives*
(stealth addresses → unlinkable identities; OT → private queries; the nullifier
model hides which note is spent) but no *composed* metadata-privacy story: turn
receipts, cell-fetch patterns, and federation callbacks still leak graph structure.
**Confidentiality here means: an observer learns neither the participants nor the
shape of an interaction.** Honestly partial; see §5.

### 1c. Confidential computation — *compute on hidden state, prove it was correct*
> **Adversary:** a light client who must be convinced a turn was valid **without**
> being shown the inputs.

dregg's STARK already separates **public inputs** from **private witness**. The ZK
question is whether the cell's *state itself* can be a private witness: the circuit
proves `old_committed_state →[effect] new_committed_state` is a genuine kernel
transition while the values stay hidden. **Confidentiality here means: validity is
public, contents are private, the light client still cannot be fooled.** This is
§3 — the deeper rung, and it is real crypto work (the floor in §3c).

### 1d. Relation to write-authority (the unifying claim)
Write-authority answers *"may this turn happen?"*; read-authority answers *"may
this viewer see the result?"*. They are **dual faces of the same cap**:

- A **write-cap** authorizes producing a new committed state.
- A **read-cap** authorizes *opening* a committed state (or a slice of it).
- **Attenuation is the same operation in both directions:** `granted ⊆ held`. A
  read-cap for slots {3,4,5} attenuates to one for {3} exactly as a write-cap for
  `{send, delegate}` attenuates to `{send}`. The `is_attenuation` gate
  (`cell/src/capability.rs`) is reused verbatim; only the lattice changes
  (which *slots/fields* may be opened, vs which *effects* may be issued).
- **Confidential computation is where they meet:** a turn carries a write-cap (it
  may mutate) AND its receipt is decryptable only under a read-cap (the result is
  confidential). The circuit binds both into the commitment so neither can be
  forged independently — the ARGUS "no-forgotten-precondition" bar, extended to
  reads.

---

## 2. The read-cap model (the first buildable rung)

### 2a. The capability that gates READ
Add a **viewing dimension** to the cap lattice. A `ReadCap` over a cell names a set
of *openable field slots* (a subset of the 16) and carries a *viewing key* — the
decryption authority for those slots.

```text
ReadCap {
    target:   CellId,             // which cell
    slots:    FieldSet,           // which of the 16 slots it opens (the lattice)
    view_key: ViewKey,            // the decryption authority for those slots
    caveats:  Vec<Caveat>,        // attenuation: expiry, predicate, viewer-bind
    breadstuff: Option<[u8;32]>,  // same provenance token as a write-cap
}
```

- **`slots` is the read-lattice.** `granted.slots ⊆ held.slots` is exactly the
  `is_attenuation` partial order, computed by the SAME gate the write side uses
  (`cell/src/capability.rs`). Granting a narrower read-cap = handing a `ViewKey`
  that decrypts only the granted slots (key-derivation below). There is no
  amplification: you cannot grant read of a slot you cannot read.
- **`view_key` is the decryption authority.** Reuse the existing ECIES path
  (`cell-crypto/src/note_encryption.rs`): each `Committed`/encrypted slot is sealed to a
  per-slot symmetric key; the `ViewKey` is the material (or the X25519 secret) that
  derives those per-slot keys. Per-slot derivation = `KDF(root_view_key,
  domain="dregg-read-slot v1", slot_index)`, so a cap for slots {3,4} hands a key
  from which exactly slots {3,4} (and no others) are derivable — **attenuation of a
  read-cap is attenuation of the key it derives.** (HKDF-tree, not "hand over the
  root and trust them"; the seam is a real key-management primitive, see §5.)
- **Revocation** rides the existing channel (`cell/src/revocation_channel.rs`) for
  the cap-object; *cryptographic* forward-revocation (re-encrypt under a fresh key
  so a revoked holder cannot read NEW state) is the honest residual — past reads
  cannot be un-seen, exactly as in every encryption system. The cap-layer revoke
  stops FUTURE issuance/use; key-rotation stops future *content*.

### 2b. Encrypted cell state
Promote `FieldVisibility::Committed` from "hash only, value private to its author"
to "**ciphertext-plus-commitment**, value readable under a read-cap":

```text
slot i, Committed:   on-ledger = (commitment_i, ciphertext_i)
    commitment_i = Poseidon2(value_i || nonce_i)     // binds the value (circuit-native)
    ciphertext_i = ECIES_seal(value_i || nonce_i, to = slot_view_pubkey_i)
```

- The **commitment** is what the circuit and conservation already see — unchanged,
  so write-soundness is untouched. The cell-side note commitment is already
  Poseidon2 in the STARK-native field (`cell/src/note.rs`), so this reuses the
  audited sponge.
- The **ciphertext** is the new artifact; a read-cap holder ECIES-opens it. A
  party without the cap sees only `(commitment, ciphertext)` — binding without
  hiding-loss. This is exactly the note-encryption pattern (`note_encryption.rs:6`,
  "that opening must travel encrypted; only the recipient may read it") generalized
  from notes to **arbitrary cell slots**.
- `Public` slots stay plaintext (no ciphertext). `SelectivelyDisclosable` slots
  add §3's predicate-proof path on top. The three `FieldVisibility` variants thus
  become a clean ladder: *public → readable-under-cap → provable-without-reveal*.

### 2c. Composition with the membrane (formalizing the fog-of-war)
The membrane (`starbridge-web-surface/src/affordance.rs`) is **already** a
confidentiality primitive: `Viewer.permits` is a per-viewer disclosure bit
orthogonal to the cap, and `project_membrane` returns only what BOTH the cap-gate
and the disclosure-bit admit — Lean-proven non-amplifying (`Dregg2.Deos.Membrane`,
`membrane_two_viewers_distinct`). The read-cap **gives `permits` a cryptographic
spine**:

- Today `permits: Box<dyn Fn(&str) -> bool>` is a *trusted local closure* — it
  decides what names a viewer SEES, but a malicious surface could ignore it. With
  read-caps, the disclosure bit becomes "does the viewer hold a read-cap that
  derives the key for this slot/affordance?" — so the projection is enforced by
  *not being able to decrypt*, not by a closure choosing to hide. The fog-of-war
  stops being advisory and becomes cryptographic.
- The Lean `membraneShows` predicate is then refined: `membraneShows(viewer, aff)
  = is_attenuation(held, fire_rights) ∧ readCapDerives(viewer.readcap,
  aff.slots)`. The existing non-amplification proof (`reshareN_attenuates`,
  `Dregg2.Deos.lean:20`) extends: a reshared membrane cannot grant read of a slot
  the resharer could not read, because it cannot hand a key it cannot derive.
- **Per-viewer projection = read-cap evaluation.** "Open a surface re-acquires a
  per-viewer projection" (`web_cells.rs` doc) is, after this rung, literally:
  decrypt the slots this viewer's read-cap opens; everything else stays
  `(commitment, ciphertext)`. The web-of-cells already verifies the attested root;
  it just couldn't *read* confidentially. Now it can, attenuably.

---

## 3. ZK-private cells (the deeper rung)

### 3a. The shape
A **ZK-private cell** is one whose state lives entirely as commitments (no public
slots), and whose every turn is accompanied by a STARK proving the transition is a
genuine kernel transition — **without revealing old state, new state, the effect's
operands, or the cap chain.** The light client verifies the proof against the
public inputs (the committed roots + the verification key) and is convinced the
cell evolved correctly; it never learns the contents. This is the §1c question made
concrete and it is the Midnight angle: *Midnight proves the value-transfer is
valid; dregg proves the authorized state-transition is valid* — they compose at the
app layer (`project-midnight-strategy.md`).

### 3b. What the circuit must prove (the obligation)
For a ZK-private turn over `old_commit → new_commit` under effect `e`:

```text
∃ (old_state, new_state, cap_chain, witness) :
      Poseidon2(old_state) = old_commit                 // openings bind to public roots
    ∧ Poseidon2(new_state) = new_commit
    ∧ authorized(cap_chain, e)                          // the cap chain admits e
    ∧ is_attenuation throughout cap_chain               // no amplification
    ∧ apply(e, old_state) = new_state                   // the genuine kernel transition
    ∧ conservation(old_state, new_state)                // Σδ = 0, via value-commitments
```

All of `old_state, new_state, cap_chain, witness` are the **private witness**; only
`old_commit, new_commit, vk, height` are public inputs. This is precisely the
two-axis authority + apply + conservation obligation the **Circuit-Soundness Apex**
campaign is already proving for the *non-private* case
(`docs/reference/lean-circuit.md`); the ZK-private cell **inherits that
soundness for free** and *adds hiding on top* via §3c. The light-client
unfoolability theorem (`verifyBatch accept ⟹ ∃ genuine kernel transition`) holds
verbatim — the witness being hidden does not weaken it, because soundness is a
property of the public inputs + vk, not of witness visibility.

### 3c. The honest crypto floor (real ZK vs Lean-provable)
Split clean, in the spirit of *don't-launder-a-load-bearing-insecurity*:

- **Real ZK primitive (statistical, in-tree):** the *hiding* comes from
  `circuit/src/stark_zk.rs` — `HidingFriPcs` (ZK=true) + `MerkleTreeHidingMmcs`
  (salted leaves) + random trace rows + random FRI codeword. This is Plonky3's
  *battle-tested* hiding PCS, statistically-ZK by construction; dregg deliberately
  **does not hand-roll masking** (the doc names that a "classic soundness footgun").
  This is the load-bearing crypto and it is honest about its strength: hiding is
  statistical-ZK at the configured blinding degree, soundness is FRI's ~130-bit
  floor (match the commitment to it — `docs/FAITHFUL-COMMITMENT-LAW.md`).
- **Lean-provable (the logical layer):** the *transition-correctness* obligation in
  §3b — that a satisfying witness implies a genuine kernel transition, that the cap
  chain is non-amplifying, that conservation holds. This is the Metatheory trunk's
  job (`metatheory/Dregg2/Circuit/`) and is exactly the apex work in flight. **Lean
  proves the relation is the right relation; the hiding PCS proves the prover knows
  a witness for it without revealing it.** Neither launders the other: a Lean proof
  of a vacuous relation buys nothing (prove non-vacuity), and a sound hiding PCS
  over the *wrong* relation hides a lie.
- **The metadata residual (§1b) is NOT solved by this rung.** A ZK-private cell
  hides its *contents*; it does not by itself hide *that a turn happened* or *which
  cell*. Nullifier-style unlinkability (`note.rs`) + stealth addresses (`stealth.rs`)
  attack that, but composing them into a full metadata-private turn is open work.

---

## 4. The design & the first buildable milestone

### Milestone 0 — the read-cap on the existing cap substrate (SHIPPED)
The smallest end-to-end confidential read, all on organs that exist — now delivered:
`ReadCap` + `ReadCap::attenuate` in `cell-crypto/src/read_cap.rs`, the membrane read-side dual
in `cell/src/membrane.rs`, and the live inspector surface in `starbridge-v2/src/read_cap_lens.rs`.
The four pieces, as built:

1. **`ReadCap` type** (§2a) in `cell-crypto/` (crate `dregg_cell_crypto`), sharing `is_attenuation` and the caveat/
   breadstuff machinery with the write-cap. The `slots: FieldSet` lattice + the
   HKDF-tree `ViewKey` derivation (`KDF(root, slot_index)`).
2. **Encrypted `Committed` slots** (§2b): on `SetField` of a `Committed` slot,
   store `(Poseidon2 commitment, ECIES ciphertext)`. Reuse `note_encryption.rs`
   verbatim; the recipient pubkey is the slot's view-pubkey.
3. **`open(read_cap, cell) → {slot: value}`**: derive the per-slot keys the cap's
   `slots` admit, ECIES-open those ciphertexts, return cleartext for exactly those
   slots. A holder of a narrower cap gets fewer slots — *demonstrated by decryption
   failing*, not by a policy check.
4. **Membrane weld** (§2c): make `Viewer.permits` consult the read-cap
   (`readCapDerives`) so the per-viewer surface projection is cryptographically
   enforced. Refine the Lean `membraneShows` to carry the read-cap conjunct and
   extend `reshareN_attenuates` to it.

**Test bar (the non-vacuity tooth):** two viewers, equal write-authority, different
read-caps → `open` returns DIFFERENT slot sets, AND the narrower viewer *cannot*
decrypt the slot the wider one can (the key is not derivable, ciphertext stays
opaque). Both true (wide reads it) and false (narrow cannot) — proven, not asserted.

### Milestone 1 — selective disclosure
`SelectivelyDisclosable` slots gain predicate proofs: the holder proves
`value_i > threshold` (or membership, range, equality) over the *committed* value
WITHOUT revealing it, using the existing predicate-AIR family
(`circuit/src/` `PredicateAir`, `ArithmeticPredicateProof`, `RelationalProof`).
This is the bridge to §3 and reuses circuit machinery that already exists.

### Milestone 2 — ZK-private cells
The full §3 rung: a cell whose state is all-commitments and whose turns carry the
hiding-STARK transition proof. Gated on the Circuit-Soundness Apex landing the
transition obligation for the cleartext case first (the hiding is additive). Deploy
ember-gated because it is VK-affecting.

### The ordering rationale
M0 is **pure weld** — it connects `FieldVisibility::Committed`, `note_encryption`,
`is_attenuation`, and the membrane, all of which are already green, into a
read-cap; no new crypto, no VK change, `cargo test`-able. M1 reuses predicate AIRs.
M2 alone needs the deep circuit work and rides the apex campaign. This respects
*weld-beats-build* (the census found the organs) and *the floor that sits under
other work comes first* (M0 unblocks the whole confidentiality story cheaply).

---

## 5. Honest hard parts

- **Key management is the human-layer seam.** A read-cap is only as private as the
  `ViewKey`'s custody. Who holds it, how it is rotated, how a human grants "let
  Bob read slots 3–5 until Friday" without leaking the root — this ties directly to
  the human-layer / powerbox workstream (`starbridge-v2/src/powerbox.rs`). The
  HKDF-tree (§2a) makes *delegation* clean (derive a sub-key); it does **not** solve
  *rotation* (re-encrypting a cell under a fresh key on revoke is O(slots) work and
  cannot un-reveal past reads). This is a real, named primitive, not a wall — but it
  is genuine work, not a one-liner.
- **Cryptographic revocation ≠ cap revocation.** The cap layer can revoke the
  *object* (stop future issuance/use via `revocation_channel.rs`); only key-rotation
  stops a revoked holder reading *new* content, and *nothing* un-reveals what was
  already decrypted. This is inherent to encryption and must be stated plainly to
  users, not hidden.
- **Metadata privacy (§1b) is the genuinely hard tier.** Encrypting payloads does
  not hide who-talks-to-whom, turn timing, or fetch patterns. Stealth addresses +
  nullifiers + OT are the right ingredients but composing them into a full
  metadata-private turn (and quantifying the anonymity set) is open research, not a
  milestone. We should NOT claim metadata privacy from M0–M2.
- **The circuit-hides-state rung is real crypto work.** §3 is not a refactor: it
  requires the apex transition obligation in Lean (in flight) PLUS the hiding-PCS
  integration on the *production* AIRs (today `stark_zk` hides for the Plonky3
  Poseidon2 path; the effect-VM AIRs must be put through it). VK-affecting, so
  ember-gated, deploy-after-Lean.
- **Selective disclosure leaks structure.** A predicate proof "value > 1000"
  reveals *that you asked* and the predicate shape; rich disclosure histories can
  themselves leak. Compose with care; the membrane's disclosure bit should gate
  *which predicates a viewer may even request*.

---

## Appendix — the one-paragraph summary

dregg's `Permissions` gate write, never read; but the confidentiality organs
already exist disconnected — per-field `FieldVisibility` (`cell/src/state.rs:74`),
ECIES note encryption (`cell-crypto/src/note_encryption.rs`), stealth addresses, value
commitments, sealers, OT, the Lean-proven per-viewer **Membrane** fog-of-war
(`starbridge-web-surface/src/affordance.rs`), and a real ZK-hiding STARK
(`circuit/src/stark_zk.rs`, `HidingFriPcs`). The design adds a **read-cap**: an
attenuable capability (`granted.slots ⊆ held.slots` via the SAME `is_attenuation`
gate) carrying an HKDF-derived **ViewKey** that decrypts exactly the cell slots it
opens; `Committed` slots become `(Poseidon2 commitment, ECIES ciphertext)` —
binding unchanged (write-soundness intact), hiding added. It welds the membrane's
disclosure bit to read-cap derivation, making the fog-of-war cryptographic rather
than advisory. The deeper rung — **ZK-private cells** — proves
`old_commit →[e] new_commit` is a genuine, authorized, conserving kernel transition
with all state as private witness, inheriting the Circuit-Soundness-Apex
unfoolability theorem and adding hiding via the in-tree statistical-ZK PCS.
**First milestone (M0):** the read-cap + encrypted-`Committed`-slots + membrane
weld — pure weld of green organs, no new crypto, no VK change, `cargo test`-able,
with a non-vacuity tooth (a narrow read-cap provably *cannot* decrypt a slot a wide
one can). Hard parts named with their lanes: key custody/rotation (human-layer
seam), cryptographic-vs-cap revocation, metadata privacy (the genuinely hard tier,
not claimed), and the ZK-private circuit rung (real, VK-affecting, ember-gated).
