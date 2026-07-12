# The Verified-Light-Client Fold Path

**From a Lean-verified light-client predicate to a recursion-foldable leaf in the dregg IVC
(rung 3), traced against the DECO/custom precedent — every call named, every seam classified.**

This is the fold-path map for the verified-chains layer: the Lean side
(`metatheory/Dregg2/Bridge/VerifiedLightClient.lean` — `ForeignLightClient` with
`noForgery`/`failClosed`/`nonVacuous` as proof-obligation fields, lines 130–149) already
composes with `InterchainAdapter` (`metatheory/Metatheory/Bridge/InterchainAdapter.lean:70`,
`foreignFinal : Header → Prop`) via `toAdapter` (`VerifiedLightClient.lean:165`), discharging
the finality hypothesis at `TrustRung.proof`. That is rung 2: a re-executing dregg node runs
the verified rules. Rung 3 is making the SAME verification witnessable by a **pure light
client** — one that only folds the per-turn recursion tree — by re-proving the light-client
check as a STARK leaf and binding it into the fold. dregg already does exactly this for two
foreign verifications: the DECO/zkTLS Stripe commitment (`circuit-prove/src/deco_leaf_adapter.rs`)
and arbitrary `CellProgram` sub-proofs (`circuit-prove/src/custom_leaf_adapter.rs`). This note
traces those real calls and maps the chain-light-client leaf onto them.

The two-layer law carries through unchanged: **RULES fold; CRYPTO stays a named leaf.** In
Lean the crypto leaf is `CryptoLeaf.sigSound` / `hashCR` (`VerifiedLightClient.lean:87,90` —
visible structure fields, never a global axiom). In the fold the same factoring is the deployed
DECO posture: ed25519 / HMAC / SHA-256 stay **off-AIR, executor-verified named carriers**
(`deco_leaf_adapter.rs:27–34` — "exactly bridge's posture (its ed25519 / nullifier-set stay
off-fold)"), while the Poseidon2-expressible arithmetic — the RULES — is recomputed in-AIR.
The AIR does not (and honestly cannot, today) verify ed25519/BLS/keccak in-circuit; it verifies
the **rules over crypto verdicts**, with the verdicts carried exactly the way `Deco.lean`'s
`SK.unforgeable` carriers already are.

---

## 0. The precedent, end to end (the real DECO/custom call chain)

Read these five stations once and the whole path is visible:

1. **The witnessed sub-proof.** `BoundCustomProof`
   (`circuit-prove/src/custom_proof_bind.rs:100–118`): `program : CellProgram`, `proof_bytes`,
   `public_inputs`, and — the fold switch — `witness_values :
   Option<HashMap<String, Vec<BabyBear>>>` (line 115). `Some(trace witness)` = the prover can
   RE-PROVE the sub-proof as a recursion-foldable leaf; `None` (the on-wire form —
   `dregg_turn::CustomProgramProof` never serializes the witness, line 112–114) = the off-AIR
   verify only, "exactly the re-exec-only rung" (line 114). **The `Option` IS the rung
   discriminator**: `Some` → pure-light-client rung 3, `None` → re-exec rung 2.

2. **The foldable leaf.** `prove_custom_leaf_with_commitment`
   (`custom_leaf_adapter.rs:1179–1247`): lowers the `CellProgram` descriptor to an IR-v2
   `EffectVmDescriptor2` (`cellprogram_to_descriptor2`, line 668; the constraint-alphabet
   mapping table at lines 23–118), proves it through the general IR-v2 prover
   (`prove_vm_descriptor2_for_config`, line 1192), and leaf-wraps it via
   `build_and_prove_next_layer_with_expose` (line 1239) with an `expose_claim` hook that
   computes the 4-felt PI commitment **in-circuit** (`incircuit_custom_pi_commitment`, line
   1108) — byte-identical to the host `custom_proof_pi_commitment`
   (`custom_proof_bind.rs:84–88`). The claim is welded to the execution: a prover cannot expose
   a commitment disagreeing with the PIs the leaf proves (lines 1172–1175).

3. **The dual-expose leg leaf.** The per-turn EffectVM leg is minted as a leaf whose single
   `expose_claim` carries `segment lanes [0..SEG_WIDTH) ++ the published claim PIs`
   (`prove_descriptor_leaf_dual_expose`, `ivc_turn_chain.rs:1483`; the slot-parameterized
   `..._at`, line 1528; the slice-expose primitive `prove_descriptor_leaf_with_pi_slice_expose`,
   line 1280).

4. **The binding node.** `prove_custom_binding_node_segmented`
   (`joint_turn_recursive.rs:591`; the DECO twin `prove_deco_payment_binding_node_segmented`,
   `deco_leaf_adapter.rs:391–457`) folds leg-leaf × sub-proof-leaf under one aggregation layer
   whose expose hook `cb.connect`s the leg's claimed lane(s) to the sub-proof's exposed lane(s)
   (`deco_leaf_adapter.rs:440`) and re-exposes the segment (line 442) — so the node "folds into
   `aggregate_tree` like any per-turn segment leaf" (line 382). **The tooth**: a leg publishing
   a claim no verifying sub-proof backs is a `connect` conflict ⇒ UNSAT ⇒ no root exists
   (lines 386–388).

5. **The deployed wire.** `prove_chain_core_rotated` (`ivc_turn_chain.rs:3004`) dispatches on
   `leg.carrier_witness` (line 3085): `Some(CarrierWitness::Custom(bundle))` mints the dual
   leaf, calls `prove_custom_leaf_with_commitment` (line 3094), folds under
   `prove_custom_binding_node_segmented` (line 3105); `Deco(bundle)` is the same shape at lines
   3180–3216 (`prove_deco_leaf_with_claim` → `prove_deco_payment_binding_node_segmented`);
   there is "deliberately NO wildcard arm, so a new variant is a compile error" (line 3081–3082).
   Legs without a witness take `carrier_witness: None` — the sanctioned re-exec rung (3080).
   The wire is admission-gated: `carrier_claim_pins_admitted` REFUSES a leg whose deployed
   descriptor lacks the claim pin (lines 3076–3078, 3183–3190) — fail-closed, never a free
   column.

(One naming correction against older notes: there is no `prove_ln_with_claim`; the real
with-claim mints are `prove_deco_leaf_with_claim` (`deco_leaf_adapter.rs:358`) and
`prove_note_spend_leaf_with_claim` (used by the bridge arm, `ivc_turn_chain.rs:3151`).)

---

## 1. Verified predicate → a CellProgram whose AIR accepts iff the predicate holds

The Lean object is `V : ForeignLightClient` with `V.verify : TrustedState → Update → Bool`
(`VerifiedLightClient.lean:141`) and the proven fields `noForgery/failClosed/nonVacuous`
(lines 145–149). `verify` is executable and Bool-valued — already constraint-shaped. The steps:

**Step 1 — factor `verify` at the crypto seam (in Lean, a theorem).**
Split the chain's verify into the crypto-leaf calls and the rules arithmetic:

```
verifyRules : TrustedState → Update → Verdicts → Bool     -- pure arithmetic/hash-chain
cryptoVerdicts (u : Update) : Verdicts                     -- the leaf.sigVerify / hash calls
factoring : ∀ ts u, verify ts u = verifyRules ts u (cryptoVerdicts ts u)
```

`Verdicts` is small and concrete: per-signer signature-verdict bits, plus the digests the
`hash` leaf produced. The factoring theorem is proved by `rfl`/`simp` when `verify` is written
compositionally (it should be — write it factored from day one). This is the SAME factoring
`Deco.lean::deco_binds_payment` already performs (`deco_leaf_adapter.rs:31–33`): the
`sigSound`-carried conjuncts stay outside; the identity/commitment arithmetic goes in-AIR.

**Step 2 — express `verifyRules` in the mapped constraint alphabet.**
`CellProgram` (`circuit/src/dsl/circuit.rs:1206–1213`: `descriptor : CircuitDescriptor`,
`version`, `vk_hash : [u8;32]` — the identity, BLAKE3 of the postcard-serialized descriptor,
lines 1231–1235) carries a `ConstraintExpr` list. The kinds that lower faithfully to the
foldable IR-v2 leaf are the table at `custom_leaf_adapter.rs:30–42` plus the three landed
extensions — and they cover exactly what a light-client rules-check needs:

| light-client rule | constraint carrier |
|---|---|
| stake summation `Σ stakeᵢ·votedᵢ` | `Polynomial` (Σ coeff·∏cols, line 35) + running-sum `Transition` cross-row (line 41) |
| `votedᵢ ∈ {0,1}` | `Binary` (line 34) |
| `3·signed ≥ 2·total` (the ≥2/3 quorum) | bit-decomposition range gate on `3·signed − 2·total` — the DECO amount-range precedent (`deco_leaf_adapter.rs:19–20,70–74`, `AMOUNT_RANGE_BITS`) |
| chain-id / height / period equality | `Equality` / `PiBinding{First}` (lines 32, 42, 52–59) |
| committee-membership (validator in the trusted set) | `MerkleHash` → `TID_P2` Poseidon2 chip lookups with position-ordered child reconstruction (lines 63–78) — "the shared primitive every hash-heavy carrier's path verification rides" |
| vote-set / update running commitment | `ChainedHash2to1` + `SeedHash2to1` copy-forward accumulator (lines 80–91) — the `dregg-dfa-routing-v1` byte-for-byte precedent |
| per-signer verdict wiring | `TableFunction` bivariate-Lagrange gate (lines 93–99) where a small grid suffices |

The trusted state (`TrustedState` — committee root, chain-id, period) enters as **PI-pinned
values** (`PiBinding{First}`); the update fields and the `Verdicts` bits enter as witnessed
columns constrained against those PIs. What is NOT expressible in-AIR — keccak, SHA-256,
ed25519, BLS pairings — is precisely the `CryptoLeaf` content, and it stays off-AIR by
construction of Step 1. (Named residuals if a chain's rules need them: the fact-sponge `Hash`,
arbitrary `Lookup` tables, `BoundaryRow::Index` — `custom_leaf_adapter.rs:101–118`. Tendermint/
sync-committee quorum arithmetic needs none of these.)

**The honest scope statement this buys:** the leaf AIR accepts iff
`verifyRules ts u verdicts = true` over the PI-pinned trusted state — i.e. the RULES hold over
the claimed verdicts. The verdict bits themselves are bound the way DECO binds its off-AIR
gates: the executor's `verify_proof_bind`-side check (`custom_proof_bind.rs:28–33`) runs the
REAL `V.verify` (crypto included) before the turn is accepted, and the leaf's PI commitment
binds the same `(ts, u)` bytes into the turn hash (`custom_proof_bind.rs:47–49`), so a verdict
bit the executor did not certify cannot be substituted without changing the turn identity. The
pure light client witnesses "the rules were checked against these committed inputs and
verdicts"; the crypto verdicts carry the same named-carrier trust as `sigSound` — no more, no
less. This is the two-layer law, deployed.

**Step 3 — mint the program + prove the teeth.**
`CellProgram::new(descriptor, version)` (`circuit.rs:1217`) derives `vk_hash` — the identity
the EffectVM Custom row binds at column 68 (`custom_proof_bind.rs:37–41`; unknown program =
fail closed, `ProofBindError::UnknownProgram`, line 150). Then the Nomad-law teeth AT THE LEAF:
an honest-accept test (genuine quorum proves), and forged-reject tests (sub-quorum stake,
wrong chain-id, tampered committee root, zeroed update ⇒ trace generation or proof fails /
verification rejects) — the AIR-level image of `toy_gate_discriminates`
(`VerifiedLightClient.lean:343`) and the exact shape of
`circuit-prove/tests/custom_binding_deployed_tooth.rs` (`custom_leaf_adapter.rs:180–182`).

---

## 2. The foldable leaf and the fold (the Some-witness path)

**Mint the bundle.** The chain-verification turn carries a `BoundCustomProof` with
`witness_values: Some(trace)` + `num_rows: Some(n)` (`custom_proof_bind.rs:115–117`) — the
named trace-column witness `CellProgram::generate_trace` consumes (`circuit.rs:1248`). On the
deployed path this lives on `RotatedParticipantLeg::custom_witness`
(`joint_turn_aggregation.rs:238,578`) — prover-side only, never on the wire.

**Re-prove as a leaf.** `prove_custom_leaf_with_commitment(program, witness, rows, pis, config)`
(`custom_leaf_adapter.rs:1179`) with `config = ir2_leaf_wrap_config()` (the ONE FRI engine the
whole rotated tree runs at, `ivc_turn_chain.rs:3043–3045`). The leaf exposes the in-circuit
4-felt PI commitment; `read_exposed_pi_commitment` (line 1251) reads it host-side.

**Bind into the per-turn fold.** The leg leaf is minted dual-expose over the deployed
`customVmDescriptor2R24`'s `custom_proof_commitment` PI slots 46..49
(`custom_leaf_adapter.rs:163–174`), and `prove_custom_binding_node_segmented`
(`joint_turn_recursive.rs:591`) `connect`s claimed-vs-genuine commitment in-circuit and
re-exposes the segment. From there the node is an ordinary segment leaf to `aggregate_tree`
(`ivc_turn_chain.rs:3719`) and the root folds into the `WholeChainProof` a pure light client
verifies. A forged claim ⇒ no satisfying partner for the `connect` ⇒ UNSAT ⇒ "a PURE LIGHT
CLIENT verifying the deployed `WholeChainProof` never receives a verifying artifact"
(`custom_leaf_adapter.rs:171–174`).

**Route A vs Route B.** Two concrete ways in, both deployed patterns:

* **Route A — the generic custom arm (zero new circuit code).** Ship the light-client
  `CellProgram`, register it in the host `ProgramRegistry`, carry
  `CarrierWitness::Custom(bundle)`; the `ivc_turn_chain.rs:3086–3114` arm does the rest.
  **One real blocker**: `incircuit_custom_pi_commitment` supports ≤ 4 PIs today — more is an
  explicit `Err` ("the multi-chunk additive sponge over the shared challenger op is the named
  residual", `custom_leaf_adapter.rs:1120–1126`). A light-client leaf's natural PIs (8-felt
  committee root + chain-id + update digest + verdict) exceed 4. Either (a) close the
  multi-chunk residual (chain `add_poseidon2_perm_sponge_step` calls, line 1151 — the
  primitive already exists), or (b) pre-hash: make the leaf's descriptor PIs a single 4-felt
  Poseidon2 digest of the full input tuple, recomputed in-AIR from the pinned columns (the
  DECO one-lane-binds-the-tuple argument, `deco_leaf_adapter.rs:384–388`).

* **Route B — a dedicated leaf adapter (the DECO shape).** A
  `lightclient_leaf_adapter.rs` mirroring `deco_leaf_adapter.rs`: hand-rolled IR-v2 descriptor,
  `prove_<chain>_leaf_with_claim` via `prove_descriptor_leaf_with_pi_slice_expose`
  (`ivc_turn_chain.rs:1280` — exposes a PI slice directly, NO sponge, no ≤4 limit;
  `DECO_CLAIM_LEN = 5` at `deco_leaf_adapter.rs:101`), a new `CarrierWitness::<Chain>` arm
  (the no-wildcard match FORCES the decision, `ivc_turn_chain.rs:3081`), and a claim pin in the
  deployed descriptor — which is **VK-affecting** and rides the big-bang regen tie
  (`carrier_claim_pins_admitted`, line 3183). More work, but the claim can be the full tuple
  and the AIR is purpose-built.

Route A option (b) is the near path: no VK movement, no new carrier arm, one in-AIR digest.
Route B is the right long-term home once a chain leaf is load-bearing enough to deserve its
own carrier arm and descriptor pin.

---

## 3. The honest cost

* **Per-turn prover cost (the real growth).** A chain-verification turn on the fold path costs
  **three extra recursion proofs** versus a plain segment leaf: the dual-expose leg re-wrap,
  the chain sub-proof leaf-wrap (`prove_custom_leaf_with_commitment` — itself an inner IR-v2
  STARK + a leaf-wrap layer), and the binding aggregation node. Each wrap layer's circuit
  FRI-verifies its child in-circuit, so its size scales with the child's **opened-column count
  × query count** — a wide light-client AIR (Merkle chips + range bits + running hashes; cf.
  DECO's `BASE_WIDTH = 38` before chip lanes, `deco_leaf_adapter.rs:94–97`) pays for its width
  at the binding layer. This is prover latency, per chain-turn, and it is the price of rung 3.

* **The apex wrap term — corrected accounting.** The gnark wrap's arithmetic residual is the
  ROOT proof's reduced opening — ~752 opened cols × 19 queries ≈ **~3.2M R1CS**
  (`docs/deos/WRAP-NATIVE-HASH-DECISION.md:119`). Because the binding node **re-exposes the
  same `SEG_WIDTH` segment** and folds into `aggregate_tree` like any segment leaf
  (`deco_leaf_adapter.rs:381–382`, `SEG_WIDTH` at `ivc_turn_chain.rs:278`), the root's shape —
  and therefore the wrap term — is **unchanged by adding chain leaves inside the tree**. The
  earlier framing "each folded chain grows the wrap" holds only for a chain wrapped as its OWN
  root (a separate `WholeChainProof` → its own ~3.2M-residual gnark instance). Inside the
  per-turn fold, chains grow prover time, not the apex. That asymmetry is an argument FOR the
  binding-node architecture and worth preserving.

* **Wire cost: none.** The re-provable witness never serializes
  (`custom_proof_bind.rs:112–114`); the light client sees only the folded root.

* **Fail-degraded mode is sanctioned, not silent.** A prover unwilling to pay mints
  `witness_values: None` / `carrier_witness: None` and the turn takes the re-exec rung
  (`ivc_turn_chain.rs:3079–3080`) — still verified by re-executors running `V.verify`, just
  not light-client-witnessable. The rung is visible in the artifact, never laundered.

---

## 4. Lean as the source of truth for the AIR (the Lean-first → AIR link)

Yes — and the precedent already exists in-tree:
`metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean` models THE REAL `dregg-dfa-routing-v1` AIR
constraint-for-constraint (C1–C3/B1–B3 listed in its header, lines 20–30) and proves
`air_run_is_table_run` — **an AIR-satisfying trace IS the deterministic run** — plus
`route_commitment_binds_trace` under the named Poseidon2-CR carrier, plus non-vacuity against
the exact deployed router (header §Non-vacuity). And that same program fully lowers to a
foldable leaf (`dsl_leaf_adapter.rs:30–36` — `prove_dsl_leaf_with_commitment`, line 113,
REUSES the custom machinery; `dsl_leaf_unmapped_kinds` pre-gates the alphabet, line 158). So
"Lean-modeled AIR" and "foldable AIR" are ALREADY the same object once, for the DFA carrier.

The light-client discipline, then — three theorems per chain, all in the lane's Lean file:

1. **The factoring theorem** (Step 1 above): `verify = verifyRules ∘ cryptoVerdicts` — pins
   what went in-AIR vs what stayed a leaf.
2. **The AIR-faithfulness theorem** (the `air_run_is_table_run` shape): model the descriptor's
   `ConstraintExpr` list as a Lean predicate `AirAccepts : Trace → PIs → Prop` and prove
   `AirAccepts tr pis ↔ verifyRules ts u verdicts = true` (with `pis` the encoding of
   `(ts, u, verdicts)`). Because a `CircuitDescriptor` is pure data (postcard-serialized,
   BLAKE3-identified — `circuit.rs:1231–1235`; the JSON lives under `circuit/descriptors/`),
   the Lean model and the shipped descriptor can be pinned against each other: emit the
   descriptor FROM the same constraint list the Lean model quantifies over, and pin its
   `vk_hash` as a KAT in the Rust tests (the descriptor-pin pattern every carrier arm already
   uses). Drift = a hash mismatch, not a silent divergence.
3. **The composed no-forgery**: chaining 1 + 2 + `V.noForgery` gives
   `AirAccepts tr pis → V.ForeignValid u` — the AIR-level image of
   `toAdapter_foreignFinal_discharged` (`VerifiedLightClient.lean:177`), which is what the
   folded leaf actually certifies to the light client, modulo the STARK soundness carrier
   (the same `extractable` boundary `DfaAcceptanceAir` names, header line ~47) and the named
   crypto leaves.

That makes the Lean `verify` genuinely the source of truth: the AIR is derived from the
factored rules, checked against them by theorem 2, and identified by `vk_hash` all the way to
the EffectVM Custom row column 68 and the turn hash. The chain's `ForeignLightClient` instance
(rules proven), the descriptor (rules folded), and `CustomBindingFromFold` (fold proven to
bind, premise TRUE on the deployed path — `custom_leaf_adapter.rs:161–174`) meet at one
identity.

---

## 5. The lane list (what a chain fold-lane actually does)

1. Write `verify` FACTORED (`verifyRules` + `cryptoVerdicts`) in the chain's Lean lane;
   instantiate `ForeignLightClient`; discharge the three field obligations. Gate:
   `lake env lean`, `#assert_axioms` clean modulo the named `CryptoLeaf` fields.
2. Emit the `CellProgram` descriptor from the rules constraint list; `CellProgram::new`; pin
   `vk_hash` KAT. Prove the leaf teeth (honest-accept + ≥3 forged-rejects) against
   `prove_custom_leaf_with_commitment`.
3. Close the PI seam: Route A(b) in-AIR 4-felt input digest, or close the multi-chunk sponge
   residual (`custom_leaf_adapter.rs:1120–1126`), or Route B dedicated adapter + carrier arm.
4. Wire the turn: `CarrierWitness::Custom` bundle on the leg (Route A) — the
   `ivc_turn_chain.rs:3086` arm already folds it — and run the deployed tooth
   (`custom_binding_deployed_tooth.rs` shape) end-to-end through
   `prove_turn_chain_recursive → verify_turn_chain_recursive`.
5. Prove the AIR-faithfulness theorem (§4.2) and compose it with `noForgery` (§4.3).

Nothing on this list invents machinery: every station is a deployed call with a passing tooth
today, for DECO, bridge, dsl, and custom. The chain leaf is the ninth rider on an
eight-carrier road.
