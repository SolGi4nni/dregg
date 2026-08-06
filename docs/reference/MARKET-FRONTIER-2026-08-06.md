# Private-Market Frontier — fresh, file:line-grounded, at HEAD `dccd4e030` — 2026-08-06

*Lane market-frontier. This SUPERSEDES the status lines in `docs/PRIVATE-MARKET-DEV-PLAN-2026-07-25.md`
(12 days old, demonstrably stale — see §7) as the anchor a private-market brief cites. Every verdict
below is a READ of the deciding code at HEAD, not a keyword hit, with the commit that changed it where
CLOSED. What I could not verify is named plainly in §8.*

Scope: the five ranked cross-cutting needs re-verified, the #15 merkle-root soundness question settled
definitively, the three-tier spectrum (open / shielded / dark) with a per-tier honest-cost table, the
FRI-assurance status framed correctly (assurance, NOT a capability gate), and a fresh dispatch queue.

---

## 0. The one thing to read first — the #15 verdict

**#15 IS LIVE. A forged-root shielded spend is genuinely accepted on the deployed executor path, and
`AccumulatorSound` is FALSE there.** The deployed spend-accept never compares the prover-supplied
`merkle_root` against any committed accumulator; the STARK only proves membership in a tree *the prover
chose*. The PROVEN Lean fix sits beside it, un-exported and unrouted. Full closure is **ember-gated**
— it is coupled to the on-ramp/L0.5 encoding decision (need #1), not autonomously routable. Details in §1.

It does **not** contradict "the shielded pool clears today": the ring-clearing math
(`Market/ShieldedClearing.lean`) is a separate, sound Lean object about *matching*. #15 is a hole in the
deployed *spend-accept* membership binding — a different layer.

---

## 1. ⚑ #15 merkle-root theft — SETTLED: LIVE deployed-path hole (ember-gated fix)

### The accept path, traced end to end

A shielded transfer's authority is checked in exactly one place — `apply_shielded_transfer`
(`turn/src/executor/apply.rs:1793`), which delegates the crypto to the injected
`CircuitShieldedTransferVerifier`:

1. `turn/src/executor/apply.rs:1814` — `verifier.verify(payload)` (fail-closed by absence, `:1803`).
2. `turn-prover/src/shielded_transfer_verifier.rs:67` — the verifier reconstructs the transfer with
   `ShieldedTransfer::from_serialized_parts(payload.merkle_root, …)`. **`payload.merkle_root` is a bare
   wire `u32`** (`turn/src/action.rs:957`), passed straight through with ZERO comparison to ledger state.
3. `turn-prover/src/shielded_transfer_verifier.rs:82` — GATE 1: `verify_stark_with_wide_bindings` →
   `circuit-prove/src/shielded/wide_value_binding.rs:427` → `transfer.verify_stark_side()`
   (`circuit-prove/src/shielded/transfer.rs:148`), which builds PIs `[nullifier, merkle_root,
   value_binding]` (`transfer.rs:89-94`) from `self.merkle_root` and verifies the spend STARK against them.
4. The STARK's own root binding is a **boundary to a PUBLIC INPUT**: `spend_circuit.rs:267` —
   *"Last row: `current == pi[1]` (merkle_root)."* `pi[1]` is whatever the prover put in
   `payload.merkle_root`. The STARK proves *"these input notes are members of a tree whose root is
   `pi[1]`"* — and the prover built that tree.
5. `apply.rs:1818` GATE 3 consumes the (attacker-chosen) nullifiers; `apply.rs:1863` GATE 4 appends the
   output legs to `note_shielded`.

**No step compares `payload.merkle_root` to `note_commitments.root8()`, `note_shielded.root8()`, a
trusted-root set, or any committed accumulator.** Verified: the only `merkle_root`-vs-committed
reasoning in the tree is (a) the BridgeMint path's trusted-set equality (`apply.rs:2459`, a *different*
effect), and (b) the code's own admissions that the shielded root is unpinned (`apply.rs:1867`).

The `note_shielded` accumulator that GATE 4 appends to is **not even in the consensus state
commitment** — `consensus_state_commitment` (`turn/src/executor/mod.rs:2042`) folds
`note_nullifiers.root8()`, `note_commitments.root8()`, `note_revoked.root8()` and **not**
`note_shielded`. GATE 4's own docblock says it: *"The append thus has ZERO effect on any committed value
or proof today — pure additive live executor state"* (`apply.rs:1879`).

### The concrete theft (inputs → wrong accept)

1. Attacker builds their own Merkle tree containing a note commitment `leaf` they never legitimately
   created (any value, any owner), with an authentication path folding to a root `R` they compute.
2. Attacker generates an honest spend STARK for membership of `leaf` at root `R` (trivially satisfiable
   — they own the tree), plus a self-conserving transfer (Σ in = Σ out) with valid Bulletproof range
   proofs and a Pedersen conservation proof over legs they choose.
3. Attacker sets `payload.merkle_root = R`.
4. `verify_stark_side` verifies membership against `pi[1] = R` → passes; range/conservation pass. The
   executor consumes the attacker's nullifiers and appends the outputs. **Commit.**

This is the Lean falsifier, proved over ALL hashes (so it holds for the real Poseidon2) and
`#assert_axioms`-clean: `ShieldedMerkleRootPin.root_substitution_forges` and
`deployed_admits_but_pin_rejects` (`metatheory/Dregg2/Circuit/ShieldedMerkleRootPin.lean:166,183`).
The deployed model `accepts` (`:135`) is HEAD-faithful — membership against `p.suppliedRoot`, the
committed root binder ignored on purpose (`accepts_independent_of_committedRoot`, `:147`).

The existing Rust test does NOT catch it. `honest_note_spend_verifies_and_tamper_rejects`
(`apply.rs:5110`) and the shielded m2b tests only reject a **mutated** root on an *honest* proof
(`root + 1` without re-proving → membership breaks). They never test an attacker who *proves against
their own chosen tree*. The Lean review names this exact gap: `mutation_test_is_not_the_pin`
(`ShieldedMerkleRootPin.lean:222`).

### Monetizability / why it must not wait

The pool is value-less today (need #1: no `Shield`/`Deshield`), so there is nothing to steal *yet*. But
`AccumulatorSound` is already false and double-spend protection is already meaningless (each attack
picks fresh roots and fresh notes). The instant a `Deshield` on-ramp lets pool notes become real ledger
value, forged-root spends become **mint-from-nothing inflation**. Per house doctrine (CLAUDE.md
greenfield §"the phases are backwards"): the pin must land **before or with** the on-ramp, never after.

### The fix is PROVEN but UNROUTED — and it is ember-gated, not autonomous

The Lean fix is done and axiom-clean:
- `metatheory/Dregg2/Circuit/ShieldedSpendPortDischarge.lean:246` `emitted_accept_is_committed` proves a
  satisfying trace of the *emitted* descriptor forces `pi[root] ≡ pi[committed_root]` in-AIR (the
  root-substitution pin), with NO `AccumulatorSound` hypothesis.
- `metatheory/Dregg2/Circuit/ShieldedMerkleRootPin.lean:258` `pinned_accept_is_committed` and
  `pin_closes_the_falsifier` (`:270`) close the falsifier under the pinned predicate.

It is **not routed to Rust**. Confirmed: `grep` for `@[export]` in the emit/discharge files → none; the
deployed verifier uses the **hand-written Rust AIR** `shielded_spend_descriptor()`
(`circuit-prove/src/shielded/spend_circuit.rs:270`, width 20, 3 PIs, no committed-root pin), *not* the
Lean-pinned descriptor. `spend_circuit.rs` is itself the Rust-AIR debt house-law #1 targets.

**Why the fix is ember-gated (this corrects the dev-plan's "AUTONOMOUS-ish — confirm").** Two couplings,
both to the on-ramp encoding:
1. *No coherent committed root to pin to yet.* `note_shielded` holds output legs' **Ristretto Pedersen
   `commitment_bytes`** (`turn-prover/src/shielded_transfer_verifier.rs:108`), which are NOT the
   Poseidon2 `hash_fact(v,[asset,owner,rand])` membership leaves the spend STARK opens against
   (`apply.rs:1871-1877` names this as the L2/L4 encoding decision). Today's spend proves membership in a
   Poseidon2 tree while the accumulator holds Ristretto legs — incommensurable. A meaningful pin needs
   the canonical committed-tree leaf/encoding *decided first*, and that is the on-ramp's VK-affecting
   L0.5 decision (ember-gated, CLAUDE.md pause-list §1).
2. *Even the in-AIR pin alone doesn't give "spends a LEDGER-AUTHORIZED note."* The keystone's own
   docblock (`ShieldedSpendPortDischarge.lean:243`, `289`) is explicit: the note-authorization conjunct
   (`IsLedgerNote`) "comes in through the floor," discharged "by the Shield-A append" — i.e. by the
   on-ramp. At the ∃-image predicate the floor is *vacuous under C6 surjectivity*
   (`noteAccumulatorCR_vacuous_of_c6Surjective`); the floor that prices something is the
   authorization-carrying one the on-ramp supplies.

**Verdict: #15 is a real, live, deployed-path soundness hole. The Lean fix exists and is axiom-clean but
UNROUTED. Routing it soundly is L0.5-encoding-gated (ember-gated), and must be sequenced WITH the
on-ramp, not deferred behind it.** A pure Rust equality-refusal shim (`payload.merkle_root ==
committed_shielded_root`) is only meaningful once (1) is decided, so it is not an autonomous partial.

---

## 2. The five ranked cross-cutting needs — LIVE / PARTIAL / CLOSED at HEAD

| # | Need | Verdict | Evidence (file:line) | Change since 07-25 |
|---|------|---------|----------------------|--------------------|
| 1 | Value on-ramp + shielded custody | **LIVE** | No `Effect::Shield`/`Deshield` in the 36-variant enum (`turn/src/action.rs:1044`); `note_shielded` is executor RAM only (`mod.rs:963`), absent from the state commitment (`mod.rs:2042`); GATE 4 append is "ZERO effect on any committed value" (`apply.rs:1879`); nullifier value hardcoded `0` (`apply.rs:1848`) | Unchanged since the 07-24 L0 accumulator (`a9a8d7f3a`). Lean obligation + falsifier landed (`ShieldedOnRampPin.lean`, `deployed_append_unsound_today`), but deployed path unmoved. |
| 2 | Pin merkle_root (#15 theft) | **LIVE** (fix ember-gated) | See §1 — full trace | Lean fix proven + axiom-clean, unrouted. Deployed accept unchanged. |
| 3 | Distributed no-single-viewer committee | **PARTIAL** (materially advanced) | Real multi-process committee over TCP with hybrid PQ transport landed: `fhegg-fhe/src/threshold/distributed.rs:1`, party binary `fhegg-fhe/src/bin/threshold_committee_party.rs:420`, transport X25519+ML-KEM-768 / Ed25519+ML-DSA-65 (`fhegg-fhe/src/mpc_party/transport.rs:553-613`); tests across real pids (`fhegg-fhe/tests/distributed_threshold_committee.rs:313,552`) | **`9927bb188`** (07-25, +2885). The dev-plan's "single-process simulated ceremony" is now stale on the *substrate*. |
| 4 | Same-opening binding (ring↔wide-join) | **LIVE** | Deployed join is still one BabyBear-felt equality `legacy_binding` (`circuit-prove/src/shielded/wide_value_binding.rs:412`), reached every transfer via `shielded_transfer_verifier.rs:82`. Code admits it: *"the legacy felt is now only an equality join"* (`shielded_transfer_verifier.rs:81`). Falsifier intact + strengthened (`ShieldedWideJoinPin.dark_value_decouples`) | No landing commit. See §4a for the "12 consumers" correction. |
| 5 | Malicious-secure MPC | **LIVE** | Trusted-dealer triples in prod (`fhegg-fhe/src/mpc_party.rs:1761`, callers `node/src/dark_clearing_service.rs:954`); dealerless path a typed dead-end (`fhegg-fhe/src/dealerless_preprocessing.rs:502` `AwaitingCrossTermProvider`); malicious-OT trait has ZERO impls (`fhegg-fhe/src/mpc_distributed_mac.rs:478`, only filler is test `ideal_ot`); no authenticated garbling (fhegg is GMW/Beaver, `garbl` absent) | Nothing from the 07-25 malice-roadmap landed; all substrate predates it (07-20→07-22). Docs are honest; the gap is real work not done. |

### 3-note (committee), why PARTIAL not CLOSED

The distributed committee EXISTS but: (a) **no production caller uses it** — the two market callers and
the node still run every party in one process (`dreggnet-market/src/threshold_committee.rs:33`,
`node/src/dark_clearing_service.rs:42`); `DistributedDkg`'s only consumers are two tests + one example.
(b) **localhost-only** (`threshold_committee_party.rs:428` binds `LOCALHOST`; rendezvous is a shared
FS dir). (c) **the distributed path is weaker crypto than the in-process one** — its openings carry NO
ZK decrypt-share certificate (`fhegg-fhe/src/threshold/quorum.rs:1392`), model is SEMI-HONEST
(`distributed.rs:31,50`); every verified-transcript constructor is under `#[cfg(test)]`
(`quorum.rs:4108`+). So: the *ops perimeter* work is the remaining item, plus lifting the distributed
path to malicious security.

---

## 3. The tier spectrum (open / shielded / dark) — three complementary mechanisms, per-tier honest cost

**These are NOT a pick-one fork.** They are three different mechanisms with different capabilities. The
load-bearing distinction: **ZK (shielded) proves a statement about data the prover KNOWS; MPC (dark)
computes over data NOBODY sees.** Shielded is *not* a committee-free substitute for dark — it
structurally cannot do blind matching over mutually-hidden orders. They are complementary tiers.

| Tier | Mechanism | Privacy property | Committee? | Perf | HEAD status | The real current gap |
|------|-----------|------------------|------------|------|-------------|----------------------|
| **OPEN / CLEAR** | plaintext ring matching, solver sees orders | none | no | ~ms | **works** (regression CLOSED, see below) | — |
| **SHIELDED** | ZK ring; amounts+owners hidden behind Pedersen commitments; conservation checked HOMOMORPHICALLY over commitments; prover knows the openings and proves in ZK | amounts+owners hidden from public | **committee-FREE** | STARK-proving cost | note/ledger layer real+kernel-clean, but marquee overreaches (see below); deployed spend has #15 | **#15 unrouted-root (§1)** + the on-ramp (need #1) + FUSE the cleartext matcher to the note layer + a binding/hiding witness that isn't the identity + STARK proving cost |
| **DARK** | orders ENCRYPTED (BFV); price crossing by secret-shared MPC revealing only `(p*,V*)` | true blind multilateral discovery — no party, not even the matcher, sees any order | **needs n-party committee to decrypt the masked aggregate** | network-round-bound | crypto real, semi-honest, single-process in prod | network-MPC latency + honest distributed committee (need #3) + malicious security (need #5) + toy params |

### OPEN/CLEAR — the flagship regression is CLOSED

The DrEX "list→clear→settle" journey broke on 07-24 (`1b8d7827c2` inverted intent's ring settlement so
an unregistered Lean gate REFUSES the ring; `drex_clear.rs` never registered it). **Fixed at HEAD:**
`exec-lean/src/bin/drex_clear.rs:257` `main()` now calls `dregg_exec_lean::register_distributed_gates()`
("the fix for the twin-deletion regression"), commit **`cf7cb0b76`** (07-25), pinned by
`exec-lean/tests/drex_clear_gate.rs`. The dev-plan's "DrEX-clear regression (dispatched)" is DONE.

### SHIELDED — the clearing model is real at the note/ledger layer, but the marquee sentence overreaches in three places

`metatheory/Market/ShieldedClearing.lean` (465 lines) is sorry-free, axiom-free in its transitive
shielded deps, `#assert_axioms`-clean across 9 gates (`:431-439`, `.olean` present so they fired). The
kernel/ledger layer is genuinely real, NOT an identity carrier: `unshieldK`
(`Dregg2/Exec/ShieldedValue.lean:345`) is a real partial function with fail-closed gates (note lookup by
nullifier → freshness → asset-typed pool→dst transfer), both polarities inhabited (2-leg ring `:357`,
double-spend refusal `:396`, computed mint tooth `:462`). Committee-free is real by absence (no
`threshold_decrypt`/Shamir/key-holder object anywhere in `Market/*.lean`): *"decrypts nothing"* (`:8`).

**But the headline `shielded_ring_clears` / `shielded_ring_clears_real_crypto` overreaches — three
specific gaps a brief must not relay as "clearing is proved over the committed claims":**
1. **The matcher layer is CLEARTEXT and UNFUSED to the note layer.** Clauses (a)/(b) of the keystone
   (`:193`) are over `MatchNode` — a plain record of cleartext `offerAsset/offerAmount/wantAsset/wantMin`
   (`Dregg2/Intent/Ring.lean:657`). Nothing binds a `MatchNode` column to any commitment; the file
   admits it twice (`:127` "the two layers are composed, not yet fused"; at `:334` the demo leg offers
   *asset 10, amount 100* while its "bound" note is *asset 0, value 3*). Clause (a) conservation is never
   even witnessed — `demoShieldedRing_fair_and_private` (`:368`) skips it.
2. **No hiding / ZK is stated in this file.** Clause (c) is authorization + no-double-spend only; there
   is no indistinguishability or simulator statement. The ZK claim lives in `Market/RevealNothing.lean`
   and is *conditional on the undischarged `HidingFriPcs` statistical-ZK floor*.
3. **The "real crypto" membership weld half (b) is `P → P`, refutable at the deployed inhabitant.** Its
   hypothesis `hnc` (`:273`) unfolds — via `rootCollFind l₁ l₂ = (l₁,l₂)` (identity,
   `Shielded/RealCrypto.lean:371`) — to the conclusion verbatim, and at the tree's own
   `deployedPoseidon2Tree` it is refutable for *every* leaf set (`sponge [5,7] = sponge [5,7+p] = 6889`).
   Non-vacuous only at `refTree = Encodable.encode`, which the file itself calls *"the FALSE COMFORT
   `HashFloorHonesty` names"*. The only `CryptoPrimitives` inhabitants in-tree are trivial `Int` and
   `pedTwoGen` with **`commit v r := (v,r)`** (identity pairing, zero hiding, `binding := True`).

The homomorphic-conservation half IS genuine algebra (`shielded_ring_value_conserves_hidden` `:233`,
`commit_hom` over an abstract `AddCommGroup`) — but it proves **completeness** (equal values ⇒ equal
commitment sums), NOT the **soundness** direction a verifier needs (equal commitment sums ⇒ conserved
value), which requires binding that is `True` in the only witness.

Net: honestly self-documented and kernel-clean where it counts, but "the shielded ring clears the
committed claims in ZK" is not yet a proved property — fusing the matcher to the note layer and supplying
a non-identity binding/hiding witness is real remaining work, distinct from #15.

### DARK — the MPC crossing, priced

`crossing_rounds(k,b) = (geq_rounds(b)+1)·(1+⌈log₂ k⌉)` (`fhegg-fhe/src/mpc.rs:370`) — e.g. **~221
network rounds at b=16, K=4096** (cited `docs/deos/DREX-TIER-STATUS-2026-07-24.md:232`). Semi-honest
only (`mpc.rs:24`). GPU is not a lever here — the crossing is round-trip-bound regardless
(`DREX-TIER-STATUS:232`). So DARK's "excellent UX" needs the network-MPC latency story solved, plus the
honest distributed committee (#3) and malicious security (#5).

---

## 4. Corrections to the stale docs (verified at source)

### 4a. Same-opening "≈12 consumers" — a name conflation, the deployed join is UNCHANGED (need #4)

The "12 `dreggnet-market/` consumers" that motivated re-checking #4 consume
**`fhegg_fhe::amm_same_opening`** — a *different* object on a *different* path (BFV↔HidingFri attested
clearing on the dark-AMM swap, `fhegg-fhe/src/amm_same_opening.rs`), and it is **authenticated Tier-1
quorum-trust, not a ZK same-opening** (`amm_same_opening.rs:22-28`: *"authenticated Tier-1 same-opening,
not lattice zero knowledge… every issuer asked to endorse learns the full witness"*). Live consumers:
`dreggnet-market/src/{dark_amm_game,dark_amm_collective,dark_amm_collective_worker}.rs`,
`src/bin/dark-amm-tool.rs`.

The Lean gadget `Market.EmitSameOpeningGadget` the dev-plan §4 names is **still PROVED-BUT-DEAD, zero
Rust consumers** (`grep same_opening_gadget|same_opening_descriptor --include=*.rs` → none), and it is a
BFV/DarkBazaar decryption-consistency relation — even if wired it lands on the market path, not the ring
path. The ring↔wide-join fix is a *third* file, `Market/WideCarrierSameOpening.lean` (Fix A / Fix B),
also zero consumers. **The deployed ring↔wide-join is unchanged: still the ~31-bit felt.** ⚠ And the
falsifier got *worse*: `WideCarrierSameOpening.legacy_binding_aliases` / `docs/DESIGN-bazaar-apex-v4.md`
show the legacy squeeze reduces mod-p before hashing, so `v` and `v+p` present identical inputs — the
collision is **FREE, not the ~2^15.5-birthday / ~2^31-chosen the dev-plan quoted**.

### 4b. Stale line references and status words in the dev-plan (07-25)

- `PRIVATE-MARKET-DEV-PLAN-2026-07-25.md:51` cites `action.rs:1017` for `merkle_root` — stale; that line
  is now the `ExcessNotZero` docblock. The field is `action.rs:957`; hash sites `:2452` (ShieldedTransfer)
  and `:2171` (BridgeMint, a different effect).
- `:50-55` labels #15 "AUTONOMOUS-ish — ROUTING … Gated only if it depends on the L0.5 encoding —
  confirm." **Confirmed: it DOES depend on it. Reclassify #15 as ember-gated** (§1).
- `:47` "single-process… no distributed committee" for #3 — stale on substrate (`9927bb188`); PARTIAL.
- `:31-32` / `:63-65` frame "discharge the FRI floor" as "engineered to ONE elementary theorem" and a
  "Path-3 unlock." **Both wrong** — see §5.

### 4c. Already-closed gaps the earlier docs still list open (staleness pattern, for the record)

`custody_cross_boundary_conserves` bound in `d8897bc3b`; the CertFDescriptor ε-gap extracted in
`d68e3d34c` (already re-marked CLOSED in `MARKET-METATHEORY-REVIEW.md:48` by the certf-descriptor lane).
`MARKET-METATHEORY-REVIEW.md` is being kept partially fresh by lanes (findings 1, 2, 8 updated 08-06);
the 07-25 dev-plan is the frozen one this doc supersedes.

---

## 5. FRI-metatheory status — corrected framing: this is ASSURANCE, not a capability gate

**The dev-plan's "discharge the FRI floor to unlock Path 3" is a category error.** The FRI soundness
bound is the standard assumption of ANY FRI-based STARK; every STARK the repo deploys already rests on
it, and the shielded pool clears TODAY (`shielded_ring_clears` proved). Formalizing FRI/correlated-
agreement is about the **assurance level of the STARK verifier** (machine-checking soundness instead of
trusting the conjectured bound) — orthogonal to whether any product feature works. Nothing product-facing
is locked behind it.

Reported at that correct resolution, from `docs/reference/FRI-SOUNDNESS-THREE-ISLANDS-2026-07-28.md`
(source-checked, HEAD-current):
- The deployed floor's "51 bits" is an **informal ledger leaf** — `deployed_wrap_commitBits`
  (`FriDeployedHeightPairing.lean:142`) machine-checks `commitBits = 51` as bracket arithmetic, but
  `verifyAlgo` is never mentioned in the ledger family. Nothing else in it is attached to the verifier.
- **Three non-communicating islands.** A: the deterministic apex the light client runs
  (`CircuitSoundness.lean`, all soundness Props Boolean/undischarged; the earlier vacuity wound is now
  *repaired* by the `FriLdtExtractV3Faithful` cutover). B: the adversary-quantified chain that DOES reach
  the real `verifyAlgo` (`FriVerifierO.verifyAlgoO_run_eq`) and composes `εFriᵃ` — but **ε_C/commitBits
  is NOT one of its legs**, and its headline `epsFriAdv_deployed_vacuous_at_2_31` proves the bound `≥ 1`
  at deployed params. C: the L0–L6 correlated-agreement ladder, which reaches a *different column*
  (~101 per-fold bits over the quartic extension, BCIKS20 Thm 4.1), explicitly **not** ε_C.
- **The correlated-agreement (proximity) column is essentially PAID.** `CorrelatedAgreement/Theorems.lean`
  proves L5/L6 (`:273,285`) and the deployed quartic-extension instantiations (`:710`), with ONE named,
  bounded, sub-1.2-bit residual (`:379-410`, a `|Good|` band at the deployed `(2²⁴,2²¹,·,8)`) that needs
  Kopparty 2025 §2.1's oversized error-locator — **bounded work, not open research**. Current: **≈96.8 of
  ≈98.0 target per-fold bits over `|L| ≈ 2^123.6`.** This — and only this — is what the dev-plan's "one
  elementary theorem away" was accurately describing; it was never a description of the floor-to-`verifyAlgo`
  attachment. Nothing in `CorrelatedAgreement/` changed since 07-25.
- **The floor-to-`verifyAlgo` attachment is a DIFFERENT object, and it is a stack of ≥3 named bridges,
  none lemma-sized:** (1) `hcover`, the word↔proof bridge as a hypothesis (`FriEpsFriComposedAdversary.lean:158`,
  self-declared un-discharged `:55`); (2) `WordProofBridge`/`DeployedFriEmbedding`
  (`FriVerifierCompose.lean:312`, "not a lemma-sized gap: the FRI-proximity-to-VmTrace decode"); (3)
  `DecodedLdtLink` (`FriDecodedTraceWitness.lean:454`) — the DEEP-ALI residual the CA column targets but
  is **not yet imported into** (`deployed_colsClose_of_curveUD` is referenced only inside
  `CorrelatedAgreement/Interface.lean`). Plus the absent fifth commit-phase leg (Lemma 8.2 shape over
  `Strategy`/`OracleComp`; no formalization in-tree). The one chain that DOES reach the real `verifyAlgo`
  (island B) is *vacuous* — `epsFriAdv_deployed_vacuous_at_2_31` proves the bound `≥ 1` from 2^31 upward.
  A genuinely promising unexploited asset: `FriFoldConsistencyDichotomy.lean` (974 lines, fully proved,
  no `sorry`, imported by one file) proves exactly the dichotomy ε_C exists to cover — wiring it as the
  fifth leg may make BCIKS's separate ε_C addend unnecessary for this codebase's strategy.

So: the shielded verifier's machine-checked soundness is at the "Boolean apex + paid proximity column +
un-attached adversary chain" level. The proximity math is nearly done; the verifier attachment is a
multi-piece formalization the tree's own authors call not-lemma-sized. A real, worthwhile ASSURANCE goal
— but not a gate on shipping any tier. (For reference: Plonky3's own `conjectured_soundness_bits` at D=4
is 123.6, `|F|`-blind, zero callers — `docs/reference/FRI-BOTH-WIN-LEVERS.md:426`.)

---

## 6. Ranked dispatch queue — what to do next, autonomous vs ember-gated

**Ember-gated (architecture commitments — do not lane these blind):**
1. **The shielded on-ramp / L0.5 encoding (need #1) + #15 pin, sequenced TOGETHER.** This is the crown:
   it decides the canonical committed-tree membership leaf, lets value enter the pool, AND is the
   precondition that makes the proven `emitted_accept_is_committed` pin routable. VK-affecting,
   re-genesis. Doing #15 "first and alone" is not possible (§1); doing the on-ramp *without* the pin
   ships a live inflation bug (§1 monetizability). Land them as one campaign.
2. **The path/tier product commitments** — how much to invest in DARK's network-MPC ops perimeter (need
   #3 finish + #5 malicious security) vs SHIELDED's proving cost. This is taste + resourcing, not lane
   work. Frame as the tier spectrum, not a fork.

**Autonomous (routing proven objects / non-VK crypto — a lane can drive):**
3. **Wire the ring↔wide-join same-opening (need #4)** via `WideCarrierSameOpening.lean` Fix A/B into the
   deployed `wide_value_binding.rs:412` join, retiring the ~31-bit `legacy_binding` felt. Highest
   security-per-effort; the falsifier is FREE-collision (worse than the doc said), and the fix is
   design-landed in Lean with zero consumers. Does not touch the on-ramp VK. (Confirm no VK epoch first.)
5. **Finish the distributed-committee ops perimeter (need #3)** — route the two market callers and the
   node off the in-process committee onto `DistributedDkg`, and lift the distributed path to carry the ZK
   decrypt-share certificate (retire the `#[cfg(test)]`-only verified constructors,
   `quorum.rs:4108`+). Multi-host/WAN beyond localhost. Ops + protocol wiring, crypto is done.
6. **Malicious-MPC builds that don't touch VK (need #5)** — wire the malicious-OT trait
   (`mpc_distributed_mac.rs:478`) to a real impl; close the sacrifice forgery hole
   (`sacrifice.rs:36`); take the dealerless ceremony past `AwaitingCrossTermProvider`. Research tail —
   never claim done.

**Already done (do not re-dispatch):** the DrEX-clear regression (`cf7cb0b76`); `custody_cross_boundary_
conserves` (`d8897bc3b`); the CertFDescriptor ε-gap (`d68e3d34c`).

---

## 7. Why the dev-plan is retired as an anchor

Measured against HEAD, `PRIVATE-MARKET-DEV-PLAN-2026-07-25.md` carries: a stale `merkle_root` line
reference (§4b); a wrong autonomy classification for #15 (§1); a stale "single-process committee" for #3
(§2); a "12 consumers ⇒ same-opening wired" implication that is a name conflation (§4a); and a malformed
"discharge FRI to unlock Path 3" (§5). Three of its listed gaps are already closed (§4c). Cite THIS doc.

---

## 8. What I could not verify (stated plainly)

- **I did not build.** All verdicts are source reads at HEAD `dccd4e030` (working tree; the shielded/
  action/executor files above are unmodified in `git status`). I did not compile a forged-root test to
  watch it commit, nor elaborate the Lean descriptors — the #15 accept-path trace and the Lean falsifier
  statements (axiom-clean, over all hashes) are strong enough that a live PoC would only re-confirm §1.
  If ember wants the theft executed on a box, `/tank/dregg-build/poa-nightwatch` is the lane; the test
  writes a `ShieldedTransferPayload` with an attacker-built tree and asserts `apply_shielded_transfer`
  returns `Ok`.
- **The exact commit that first added `register_distributed_gates()` to `drex_clear::main`** — I
  attribute it to `cf7cb0b76` (07-25, which touched that call and the gate test); if a predecessor added
  the line the fix is still no later than that. The *state* (regression CLOSED at HEAD) is certain.
- **DARK end-to-end wall-clock** — I have the round formula and the cited 221-round example, not a timed
  run. `DREX-TIER-STATUS-2026-07-24.md` has the measured GPU/latency numbers.
- **fhegg internals depth** — the committee/MPC verdicts rest on module docblocks + call-site census
  (which constructors are `#[cfg(test)]`, which traits have impls), not a line-by-line crypto audit of
  the transport AEAD or the SPDZ MAC arithmetic.
