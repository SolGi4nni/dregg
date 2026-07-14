# SHIELDED-DEPOSIT BRIDGE — real token → shield → private-clear → settle

The concrete answer to *"real tokens through the actual dregg circuits."* This
maps the four-stage composition that turns "pieces verified individually" into a
single flow — a real public-testnet token, deposited into the shielded pool as a
shielded note, participating in a private clearing (fhEgg engine + reveal-nothing
STARK + output-boundary MPC), and settling (the wrap-adapter → on-chain, or
unshield back to the public chain).

Each stage is graded **EXISTS** (cited, real code), **PARTIAL** (built but one
wire short), or **MISSING** (the exact wire named). The honest one-line: **the
middle two stages (shield, private-clear) are real and proven; the two ends
(deposit-attestation → mint, cleared-result → settle) are DESIGNED with their
load-bearing primitives already built — the missing pieces are glue, not
foundations.**

The first brick is PoC'd and runs green
(`circuit-prove/tests/shielded_deposit_bridge_poc.rs`); the numeric clearing +
Cert-F settle-certificate run in the real engine (`fhegg-solver` `fhegg-e2e`).
Both runs are cited below.

---

## The pipeline, at a glance

```
  (a) DEPOSIT              (b) SHIELDED HOLD        (c) PRIVATE CLEAR        (d) SETTLE
  real testnet token  →   shielded note in     →   fhEgg engine +      →   wrap-adapter → chain
  locked + LC-attested    the pool, nullifier-     reveal-nothing STARK     OR unshield → release
                          gated, PQ-bound          + no-viewer MPC
  ── EXISTS (code) ──      ── EXISTS ──             ── EXISTS ──             ── EXISTS (tail) ──
  attest→mint glue PoC'd,  real + Lean-proven       engine+STARK+MPC real,   settle-back PoC'd,
  escrow CONTRACT stub                              note↔order seam PoC'd     wrap-prove own-tested
```

---

## Stage (a) — DEPOSIT: lock a real token, attest it, mint a note — **EXISTS (code brick); escrow contract stub**

A real token on a public testnet is locked in a bridge escrow; a proof of that
lock is produced; the shielded pool consumes the proof and mints a note bound to
the locked `(value, asset)`.

**EXISTS (PoC'd, runs green) — the attestation→mint GLUE (`deposit_to_note`).**
`circuit-prove/tests/shielded_deposit_glue_poc.rs` is the deposit-glue brick:
`deposit_to_note = attest ∘ shieldK`. Given an attested lock (the `verify_holding` /
`mpt_holding_leaf` output — `(asset, locked_value, chain, lock_ref)`, holding
identity `mpt_holding_hash_felt(root, token, holder, slot, balance)`,
`ConsensusProven`), it mints a shielded `BoundNote` bound to `(asset, value)` GATED
on: **no-mint-without-a-valid-lock** (the holding identity must recompute — the REAL
in-AIR Poseidon2 leaf binding — AND the trust tag must be `ConsensusProven`);
**`value ≤ locked`** (the custody `drawMint` gate `supply + a ≤ locked`,
`overMint_refused`); and **one-lock-one-note** (a deposit nullifier keyed on the
lock identity, consumed once). It `recordEscrow`s the lock + `drawMint`s the note on
a per-asset `MirrorState`, so `Σ minted ≤ Σ locked` per asset (`supply ≤ locked`).
The PoC then COMPOSES the whole chain — the deposit notes are sealed as REAL fhEgg
orders, cleared by the REAL engine (c), and a cleared output note unshields+releases
(d): **deposit → shield → clear → settle over real pool notes, in one run.** Both
polarities fire: a valid ConsensusProven lock (`value ≤ locked`) mints + clears +
settles; a FORGED attestation (tampered locked balance ⇒ holding-hash mismatch), an
ABSENT/unproven attestation (`trust ≠ ConsensusProven`), a MINT BEYOND THE LOCK
(`value > locked`), and a DOUBLE-MINT against the same lock are each REJECTED. Run:
`cargo test -p dregg-circuit-prove --test shielded_deposit_glue_poc -- --nocapture`.

**EXISTS — the real-token attestation.**
`eth-lightclient/src/bin/verify_holding.rs` is a RUNNING Ethereum light client
built from the crate's verified rules. It follows the beacon-header trust chain
(real mainnet period-1800 sync committee, 397/512 BLS participation over the real
attested header), Merkle-proves the committee rotation, verifies the finality +
execution branches to a finalized EVM state root, and settles a real WETH holding
via a real EIP-1186 `eth_getProof` →
`HoldingTrust::ConsensusProven` (`verify_holding.rs:234-251`). A forged balance
(+1 wei) is refused fail-closed at the storage-trie gate (`:263-277`). This is a
real public-chain token attestation, produced by Ethereum itself.

**EXISTS — the holding→leaf adapters.**
`circuit-prove/src/mpt_holding_leaf.rs` lifts an MPT-proven holding into a circuit
leaf; `circuit-prove/src/bridge_leaf_adapter.rs` is the cross-chain bridge leaf.
These are the in-circuit carriers a deposit proof would ride.

**EXISTS (model) — the custody invariant.**
`metatheory/Market/InterchainCustody.lean` proves the `lock → mirror → clear →
release` lifecycle: `recordEscrow`/`drawMint`/`lock`/`release`, with the backing
invariant `live_supply ≤ currently_locked` PRESERVED by every operation
(`invariant_holds`), `lock`/`release` moving `locked` and `supply` 1:1 (the
redeemability gap `locked − supply` invariant), and `systemValue` conserved across
the whole lifecycle. The red-team BR-3 gate (a mint with no backing lock →
`MirrorError::InsufficientLocked`) is the load-bearing check.

**CLOSED — attestation → note-mint glue (the deposit-glue brick, above).**
`deposit_to_note` (`shielded_deposit_glue_poc.rs`) binds the attested lock to the
`shieldK` note-mint: the mint fires only against a valid ConsensusProven holding
whose identity opens, the note's value is `≤` the attested locked amount (the
`drawMint` gate), and one lock event mints exactly one note (the deposit dedup
nullifier). The note is a REAL shielded `BoundNote`, not a transparent mirror.

**REMAINING (labelled stub) — the escrow CONTRACT / lock-event, not balance-snapshot.**
`verify_holding` proves a *holding* (a balance at a finalized root). A production
deposit needs a *lock event* into a specific escrow contract's storage slot. The LC
machinery proves arbitrary storage slots (real), so the deposit-glue attests the
LC-verified holding identity + a labelled `lock_ref` (the escrow address + lock
slot) — but the deposit **escrow contract** itself is unbuilt (its deploy is
ember-gated). This is a contract-deploy + fixture change, not new crypto.

---

## Stage (b) — SHIELDED HOLD: the note in the pool — **EXISTS (real + proven)**

The note lives in the shielded pool: value+asset hidden, nullifier-gated against
double-spend, the pool provably undrainable beyond its live notes.

**EXISTS — the shielded kernel verbs, Lean-proven.**
`metatheory/Dregg2/Exec/ShieldedValue.lean §6`:
- `shieldK` / `unshieldK` (`:330`, `:345`) — the shield/unshield verbs, freshness-
  gated, doing their own bookkeeping.
- `PoolInvariant` (`:322`) + `shieldK_preserves_pool` (`:519`) /
  `unshieldK_preserves_pool` (`:571`, *"THE POOL IS UNDRAINABLE"*) — the pool's
  transparent balance equals the total unspent hidden value, preserved by both
  verbs.
- `unshield_value_binding` (`:408`) — the unshield amount **is** the spent note's
  value by construction (not a free parameter — the probe's zero-note drain
  fails-closed).
- `noteCreateBound_in_range` (`:114`) — no hidden inflation at creation
  (`0 ≤ value < 2^n`); `created_value_conservation` (`:148`) — `Σ commit = commit
  (Σ value)` over executed state.
- All `#assert_axioms`-clean; the `#guard` roundtrip (`:680-708`) shields, unshields
  exactly the note's value, and REFUSES the double-spend (`:701`) and the re-mint
  under a used nullifier (`:705`).

**EXISTS — the PQ commitment floors.**
`metatheory/Dregg2/Shielded/RealCrypto.lean`:
- `ValueBindingCommit.binds_value_and_asset` (`:267`) + `mint_forces_collision`
  (`:276`) — the note's value-binding `hash_fact(value, [asset, randomness, 0])`
  binds `(value, asset)` jointly under `HashCR` (Poseidon2 CR, quantum-safe); a
  hidden mint forces a collision.
- `Poseidon2Tree.root_binds` (`:328`) + `forged_set_forces_collision` (`:343`) —
  membership under a real Poseidon2 tree root; a forged set forces a collision.
- `twoLeg_noWrap_conservation` (`:199`) + `inAir_conservation_refines_pedersen`
  (`:219`) — the in-AIR field conservation refines integer conservation via the
  range gadget (no wraparound mint).

**EXISTS — the circuit realization.**
`circuit-prove/src/shielded/spend_circuit.rs` (membership + nullifier + the C7
value-binding, `hash_fact(value,[asset_type,randomness,0])`), `pool.rs` (multi-
asset pool transfer), `transfer.rs`, `attest.rs` (ZK attestations over hidden cell
state). All run through the production hiding uni-STARK (`prove_dsl_zk`,
`HidingFriPcs`) with zero hand-written AIR.

This stage is **real**: the note-mint, conservation, no-inflation, and no-double-
spend are all proven and executable.

---

## Stage (c) — PRIVATE CLEAR: match the notes privately — **EXISTS (one seam)**

The pooled notes participate in a clearing that reveals nothing but the clearing
price `p*` and volume `V*`.

**EXISTS — the engine.**
`fhegg-solver/src/clearing.rs` (`clear` / `allocate` / `crossing` — fold + scan +
volume-maximizing crossing + conserving pro-rata allocation with
`Allocation::conserves()`), `pdhg.rs` (`solve_cpu`, the circulation-LP PDHG
search), `cert.rs` (`CertF` primal-dual certificate + `check`).

**EXISTS — the reveal-nothing STARK.**
`circuit-prove/src/cert_f_air.rs` — the Cert-F check as a real BabyBear+FRI STARK;
the witness `(f, π, s)` (the private flows) lives only in the trace under the
hiding PCS, and the only public value exposed is the cleared volume `wᵀf`.
`circuit-prove/src/shielded_ring_clearing_air.rs` / `_nleg_air.rs` — the shielded
ring-clearing AIR.

**EXISTS — the no-viewer MPC.**
`fhegg-fhe/src/mpc.rs` — the output-boundary MPC: an additive threshold-BFV fold
of `n` encrypted orders into aggregate curve ciphertexts, then a secret-shared
GMW/Beaver crossing that reveals only `(p*, V*)`. Any coalition below the
threshold `t` sees a one-time-pad-masked view — adversarial no-viewer, not a
policy claim.

**EXISTS — the Lean clearing proofs.**
`metatheory/Market/ShieldedClearing.lean`: `shielded_ring_clears` (`:182`, the
private-matching keystone), `shielded_ring_value_conserves_hidden` (`:222`, hidden
conservation over notes), `shielded_ring_clears_real_crypto` (`:254`, over the real
primitives). `metatheory/Market/CertF.lean` (`certifies_epsilon_optimal`,
`weak_duality`), `RevealNothing.lean`, `MpcClearingSecurity.lean`.

**MISSING — the one seam: note ↔ order.**
The engine clears abstract `Order`s (`clearing.rs`: `qty` + price-level `limit`),
NOT pool notes. The Lean `shielded_ring_clears` is stated over a `ShieldedRing` of
notes, but no Rust code turns a minted pool note into a sealed fhEgg order and back
into an output note. **This is the single highest-leverage missing wire in the
whole pipeline**: a note→order adapter (hiding the note's value under its
commitment as the order it seals) and an order→output-note adapter (minting the
fill as a fresh conserving note), so that `Σ input-note value = Σ output-note value
= V*` closes `created_value_conservation` across the clearing.

---

## Stage (d) — SETTLE: the cleared result lands — **PARTIAL**

The cleared result settles: either the clearing turn shrinks to an on-chain-
verifiable proof, or the output notes unshield back to the public chain.

**EXISTS — the wrap-adapter (just landed).**
`turn/src/rotation_witness.rs` `finalized_turn_from_full_turn` (`:731`) — takes a
node's proven `FullTurnProof`, mints the rotated wrap leg, and binds it to the
proof's wide 8-felt (~124-bit) `old_commit`/`new_commit` anchors, failing closed if
the minted leg's anchors do not match (`:773-786`). This is the real turn → wrap →
on-chain-verifiable shrink.

**EXISTS — unshield + release.**
`ShieldedValue.lean` `unshieldK` (`:345`) unshields a note back to a transparent
balance (amount = the note's value, by construction). `InterchainCustody.lean`
`release` (the redeem: `live_supply -= a`, `currently_locked -= a`, gated on
availability) reverts the escrow, restoring the locked value with none lost.

**EXISTS (PoC'd, runs green) — the settle-back: output note → unshield → release.**
`circuit-prove/tests/shielded_settle_back_poc.rs` routes a cleared **output note**
(a real Poseidon2 `BoundNote`, the fill/change note stage (c) mints) →
`settle_output_note` = `unshieldK` (consume the nullifier, exit the pool, debit by
exactly the note's value — `unshieldK_preserves_pool`) → `InterchainCustody.release`
(release exactly that value, gated on `supply ≤ locked`). The conservation seam
recomputes: released = note value (`unshield_value_binding`), `supply ≤ locked`
preserved (`release_backed`), the redeemability gap `locked − supply` invariant
(`release_gap`), the pool debited by the note's value, the nullifier consumed once.
Both polarities fire: a valid settle conserves; an OVER-RELEASE (> note value / >
locked-supply), a RELEASE-BEYOND-LOCKED, a DOUBLE-SETTLE (replayed nullifier), and a
NON-CLEARED note are each REJECTED. The settle turn's `(old_commit, new_commit)`
custody anchors are exhibited as the shape the wrap adapter binds to. Run:
`cargo test -p dregg-circuit-prove --test shielded_settle_back_poc -- --nocapture`.

**MISSING — the wire's tail.**
The wrap-adapter is generic over *any* `FullTurnProof` — the settle turn's anchor
SHAPE is wired (above), but it has not been fed a real proven **shielded-clearing /
settle turn** end-to-end (the full wrap-prove runs under its own tests,
`ivc_turn_chain_rotated.rs`), and the escrow's actual **on-chain** release awaits the
deployed vault contract (stage (a)).

---

## The design — the exact wiring

```
  testnet token                                                       testnet chain
      │  lock into escrow contract                                          ▲
      ▼                                                                     │ release
  ┌────────────┐   verify_holding      ┌──────────────┐  note→order   ┌──────────┐
  │  ESCROW    │──(ConsensusProven)──▶ │  shieldK     │──(sealed)────▶│  fhEgg   │
  │  (deposit  │   +storage-slot       │  BoundNote   │   adapter     │  clear + │
  │  contract) │   lock proof          │  in the POOL │  ◀(output     │  Cert-F  │
  └────────────┘                       └──────────────┘    notes)     │  + MPC   │
   [glue EXISTS,                        [EXISTS:            [seam        └──────────┘
    contract stub]                       §6 proven]          PoC'd]         │
                                                                            ▼
                                                              finalized_turn_from_full_turn
                                                              → wrap → on-chain  [EXISTS,
                                                                                  not yet fed]
```

**1. Deposit → note.** The escrow contract locks `amount` of `token` and records a
lock event at a storage slot. `verify_holding` (generalized to prove that slot)
yields a `ProvenErc20Holding{ConsensusProven}`. A bridge turn consumes it and calls
`shieldK` to mint a `BoundNote` with `value = amount`, `asset = the bridged class`.
The binding constraint: the note's `value_binding = hash_fact(value,[asset,rand,0])`
opens to the LC-proven `amount` (a single equality in the deposit circuit,
`mpt_holding_leaf` ⋈ the C7 value-binding). Dedup: a deposit-nullifier keyed on the
lock's storage key mints exactly one note per lock (mirrors `shieldK`'s freshness
gate).

**2. Shielded hold.** The note sits in the pool under `PoolInvariant` — undrainable
beyond its live notes, nullifier-gated.

**3. Private clear.** The note→order adapter seals the note as an fhEgg order
(value hidden under the commitment); `clear`/`allocate` (or the no-viewer MPC path)
produces `(p*, V*)`; the order→output-note adapter mints the fills as fresh notes.
The reveal-nothing STARK (`cert_f_air` / `shielded_ring_clearing_air`) proves the
clearing correct while hiding `(f, π, s)`; `created_value_conservation` +
`twoLeg_noWrap_conservation` close conservation `Σ in = Σ out = V*`.

**4. Settle.** The clearing turn → `FullTurnProof` → `finalized_turn_from_full_turn`
→ wrap → on-chain; OR the output notes → `unshieldK` → `InterchainCustody.release`
→ the escrow releases on the testnet chain.

### The soundness seams

| Seam | Binding | Floor |
|------|---------|-------|
| Deposit attestation | note `value_binding` opens to the LC-proven locked amount | LC `ConsensusProven` (BLS + MPT) + `HashCR` |
| No-double-mint | one lock storage-key → one deposit-nullifier → one note | `HashCR` + escrow burn |
| Shielded conservation | `Σ commit = commit(Σ value)`, no-wrap range | `HashCR` + STARK range gadget |
| Clearing correctness | `shielded_ring_clears` + Cert-F ε-optimality, hiding `(f,π,s)` | STARK soundness + `HashCR` |
| Bridge conservation | `supply ≤ locked` across `lock → clear → release` | `InterchainCustody.invariant_holds` |
| Settle | wrap anchors bound to the proof's wide `old/new_commit` | full-turn STARK soundness |

---

## The first brick — PoC'd, runs green

`circuit-prove/tests/shielded_deposit_bridge_poc.rs` exercises the REAL shielded
primitives for the middle of the pipeline, end to end, both polarities. Run:

```
cargo test -p dregg-circuit-prove --test shielded_deposit_bridge_poc -- --nocapture
```

```
(a) DEPOSIT  [STAND-IN]: attested lock of 1000 units of asset 1
(b) MINT: REAL Poseidon2 note over the attested deposit (asset 1)
      leaf commitment  = BB(299599287)
      value_binding    = BB(1268224360)  (binds (value,asset) under HashCR)
      nullifier        = BB(1335024050)
      MINTED (commitment inserted into the pool set)
      [neg] double-mint (same commitment) REFUSED
      [neg] hidden-inflation (value >= 2^30) REFUSED
      [neg] value_binding re-open to value+1 gives a DIFFERENT hash (binding)
(c) PRIVATE CLEAR: reveal-nothing hiding STARK (attr >= 1 over the hidden value)
      solvency proof over value=1000 VERIFIES (value stays hidden)
      [neg] zero-value note CANNOT attest solvency (no verifying proof)
(d) SETTLE: consume the nullifier (the cleared result settles once)
      SETTLED  ·  [neg] double-spend (replayed nullifier) REFUSED
test shielded_deposit_bridge_end_to_end ... ok
```

**What is REAL in the PoC:** the Poseidon2 `hash_fact` value-binding
(`hash_fact(value,[asset,rand,0])`, the exact C7 / `RealCrypto §1.3` commitment),
the note leaf commitment and nullifier, the no-double-mint / no-hidden-inflation /
no-double-spend gates, and the production `HidingFriPcs` reveal-nothing STARK
(`prove_dsl_zk`) proving the note solvent while its value stays hidden. Both
polarities fire at every soundness seam (the insolvent-note rejection is the range
gadget biting in the debug constraint checker, caught as a refusal).

**What is a labelled STAND-IN:** the deposit `(asset, value)` — it stands in for
`verify_holding`'s `ProvenErc20Holding{ConsensusProven}` locked in an escrow. The
LC and the escrow contract are NOT run in this PoC (the LC runs on its own,
`verify_holding`; the escrow is unbuilt).

### The numeric clear + Cert-F settle — the real engine

`fhegg-solver` `fhegg-e2e` runs the real clearing + settle-certificate:

```
[0] N=5000 orders, K=256 levels: cleared V*=93414 at price index 127, conserves=true
[2] Cert-F: wᵀf=24022.07 (cleared volume), gap=1.06e-1, ‖Af‖=2.5e-14
[4] honest certificate ACCEPTED (16641-row Cert-F AIR = Market/CertF.lean)
    break-conservation REJECTED · over-capacity REJECTED · sub-optimal (gap>ε) REJECTED
```

This is the real fhEgg private-clear + Cert-F optimality certificate the settle
depends on, positive polarity accepted and all three negative polarities rejected.

---

## Honest scope

**REAL brick (built + running):** the shielded note-mint (PQ value-binding,
nullifier, no-double-mint, no-inflation), the reveal-nothing STARK, the numeric
clear + Cert-F settle-certificate. All cited above.

**PoC'd (the glue bricks, all run green over real primitives):**
- the LC-attestation → `shieldK` mint glue (`deposit_to_note`, stage (a) — no-mint-
  without-a-valid-lock, `value ≤ locked`, one-lock-one-note);
- the note ↔ order clearing seam (stage (c));
- the output-note → unshield → release settle-back path (stage (d));
- the full deposit → shield → clear → settle composition over real pool notes.

**DESIGNED (primitives real, deploy unbuilt):**
- the deposit escrow contract on a testnet + the lock-event storage proof (the
  attested lock is the LC-verified holding identity + a labelled `lock_ref`);
- the clearing-turn → wrap on-chain shrink (`finalized_turn_from_full_turn`, wired
  in shape, own-tested).

**EMBER-GATED (deploy-time, not code):**
- the persistent federation of `n` parties for the no-viewer MPC (today: solo
  committee-of-one, `DEVNET-DEPLOYMENT-REALITY.md`);
- the actual public-testnet deploy + live tokens;
- the VK-epoch re-key + re-genesis for the shielded-bridge descriptors.

### The composition — all four code bricks CLOSED

The four glue bricks are PoC'd and run green over real primitives:
- (a) deposit LC→mint glue — `shielded_deposit_glue_poc.rs` (`deposit_to_note`);
- (b) shielded hold — `ShieldedValue.lean §6` + `RealCrypto.lean` (Lean-proven);
- (c) note↔order clearing — `shielded_clearing_note_order_poc.rs`;
- (d) settle-back — `shielded_settle_back_poc.rs`.

The deposit-glue PoC composes (a)→(b)→(c)→(d) in one run — a deposited token mints a
shielded note, clears privately, and settles, over real pool notes. What remains is
NOT code: the on-chain escrow CONTRACT deploy (the attested lock is today the
LC-verified holding identity + a labelled `lock_ref`), the persistent MPC federation
for the no-viewer clearing, and the public-testnet deploy + VK-epoch re-genesis — all
ember-gated (deploy-time).
```
