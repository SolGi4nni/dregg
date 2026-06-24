# dregg2 → real dregg1 SUCCESSOR — the gear-shift roadmap

> **Current as of 2026-06-02.** This doc has been re-grounded against the live Lean. The
> 2026-05-29 status block below is SUPERSEDED — the project moved well past the 5-effect
> scalar micro-core. What exists today is a **tree-shaped, full-op-set, per-asset executable
> turn with an executed auth gate + a complete FFI wire codec being proven a left-inverse** —
> a real start on Phase A/B, though still NOT a verified distributed OS. This doc is the plan
> to finish. Reads with `DREGG1-TO-DREGG2.md` (crate fates), `ROADMAP.md`, `dregg2.md`,
> `../THE-SWAP.md` (the cutover map).

## What's REAL today (machine-checked, no inflation) — 2026-06-02
- A Lean4 project that compiles: **~181 `Dregg2/**` modules + 12 `Metatheory/**` modules**
  (was "31"). **ZERO real open holes / `admit`/`axiom`/`native_decide`** across the corpus
  (the last 3 by-design open holes were retired + a CI guard now forbids them; task #128 /
  `WF-ZERO-HOLES`). The hundreds of grep hits in doc-comments are all prose.
- **The executable turn is no longer a 5-effect scalar kernel.** `Dregg2/Exec/TurnExecutorFull.lean`
  defines `FullActionA` — a **46-arm** per-asset action sum (`TurnExecutorFull.lean:1928`) —
  and `execFullA` dispatches **all 46 arms** (`:2236`): transfer/mint/burn (per-asset), 5
  pure-state field/log effects (setField/emitEvent/incrementNonce/setPermissions/setVK), 6
  authority effects (introduce/delegateAtten/attenuate/dropRef/revokeDelegation/validateHandoff/
  exercise), supply (createCell/spawn/bridgeMint), escrow+obligation+note side-tables,
  committed-escrow, the 3 bridge-lock ops, seal/unseal/sealPair/makeSovereign/refusal/
  receiptArchive, the 4 queue ops (ring-buffer FIFO), and the 4 CapTP swiss-table ops.
  `Dregg2/Exec/FullForest.lean` wraps this in a **TREE**: `FullForestA` (`:82`) with operational
  executor `execFullForestA` (`:113`), proven equal to `execFullTurnA` over a pre-order lowering
  (`execFullForestA_eq_execFullTurnA`, `:171`), carrying per-asset conservation, non-amplification,
  per-node attestation, and root fail-closed.
- **Per-asset CONSERVATION VECTOR (FILL 1, task #129) is live on the record kernel.**
  `Dregg2/Exec/RecordKernel.lean` carries `bal : CellId → AssetId → ℤ` (`:304`) and the combined
  conserved measure `recTotalAssetWithEscrow b` (per-asset, reads `bal`+`escrows`);
  `execFullTurnA_conserves_per_asset` (`TurnExecutorFull.lean:2699`) proves every committed turn
  moves the measure by exactly the turn's per-asset ledger delta.
- **An EXECUTED credential+caveat AUTH GATE** (META-FILL D, task #132): `Dregg2/Exec/FullForestAuth.lean`
  defines `gateOK = credentialValidG && capAuthorityG && caveatsDischarged && revocationGate`
  (`:462`, a **4-leg** fail-closed conjunction). `capAuthorityG` is VERIFIED-IN-LEAN via
  `AuthModes.authModeAdmits` (`Dregg2/Exec/AuthModes.lean:184`, an **8-constructor** `AuthMode`
  sum — custom/capTpDelivered/bearer/token/oneOf/unchecked + leaves — each with an
  `authModeAdmits ⇒ abstract-authority` proof). `revocationGate` reads the kernel-state revocation
  registry `s.kernel.revoked : List Nat` (task #139); `gateOK_revoked_fails` (`:473`) proves a
  revoked credential rejects. The gate fires IN FRONT of `execFullA` via `execFullAGated` (`:489`),
  no-TOCTOU by construction.
- The **portals** `CryptoKernel`/`World` (uninterpreted Lean⟷Rust interface) stand exactly as
  designed: `CryptoKernel.verify` is an **opaque `Bool` oracle** (the §8 boundary), NOT a Lean
  law — `Dregg2/CryptoKernel.lean:46`. A Rust impl instantiates it via `@[extern]` (e.g.
  `dregg_poseidon_hash`); the §8 soundness is the CIRCUIT obligation, derivable from
  `Circuit.bridge` (`Dregg2/Circuit.lean:229`, `satisfied kernelCircuit ↔ fullStepInv`, both
  directions). Crypto is still a PORTAL, not real `@[extern]` Pedersen/WHIR in this tree.
- **Step-completeness** is intact: `Exec/StepComplete.cexec_attests` (`StepComplete.lean:75`) —
  every committed chained step attests the full 4-conjunct `StepInv`.
- A **working FFI** (`/Users/ember/dev/breadstuffs/dregg-lean-ffi/`): Rust hosts the compiled
  kernel; **10k/10k golden-oracle differential** vs a Rust reference (`differential.rs:91`,
  `const N = 10_000`). The wire codec was **widened to the complete turn** (META-FILL I, task
  #135): `Dregg2/Exec/FFI.lean` exports `dregg_exec_full_turn` (`:938`), `dregg_exec_full_turn_wide`
  (`:2732`), and the GATED `dregg_exec_full_forest_auth` (with REAL caveat teeth, §WG). A verified
  **Rust marshaller** `dregg-lean-ffi/src/marshal.rs` (+ `marshal_roundtrip.rs`) is byte-exact vs
  the live export (task #142, THE SWAP Rust half — in progress).
- **FILL J — the codec is being PROVED a left-inverse** (task #136). `Dregg2/Exec/CodecRoundtrip.lean`
  proves, all hole-free and `#assert_axioms`-pinned (29 keystones, `:2479`–`:2507`): every leaf
  (§0), the per-asset `BAL` entry (§2), recursive `Value`/`FIELDS` (§5), the SECURITY-CRITICAL
  `Authorization`/WHO decoder at all **10 variants + recursive `oneOf`** (§6, `parseAuthW_roundtrip`),
  the `FullActionA`/WHAT decoder at **all 46 arms** (§7, `parseActionW_roundtrip` + `parseActionW_setfield`),
  and EVERY wide-state side-table list (§8–§11c: AUTHS/Nats/Bal/Escrows/Queues/Swiss). The
  top-level `parseWState`/`parseWTurn`/`parseWWire` assembly is the remaining follow-on (its
  component list-productions are all proven).
- Honest classification of the genuine OPEN theorems (now isolated in `Metatheory/Open/`, NOT
  left as open holes — stated as honest scope-notes / named assumptions): Byzantine quorum-intersection
  & GST-liveness (`Dregg2/Proof/BFT.lean`, `BFTLiveness.lean`), family joint-soundness
  (`ConservationMultiEdge`, `CrossCellBisim`), perfect ZK/UC (`PerfectZK`, `PerfectUC`),
  final-coalgebra & authority-closure.

## The toy→real gap (what "successor" actually requires)
| Layer | Toy now | Real dregg1-successor needs |
|---|---|---|
| **Cell/state** | accounts + ℤ balances + cap list | a sovereign **cell** = data-model value + multi-asset resources + slot-table + a `CellProgram` (the real `cell/`); the camera resource model deployed |
| **Turn** | one transfer/mint/burn/cap-op | the real **call-forest / effect tree**, predicates+caveats, the 6-clause auth-in-proof chain, partial turns / WitnessedReceipts |
| **Authority** | `actor == src` or a cap in a list | real cap **derivation/attenuation/revocation** kernel + the l4v integrity proof over IT (not abstract) |
| **Multi-cell** | `JointBinding` as hypothesis (proved sound) | the executable **JointTurn** = γ.2 bilateral aggregation; reuse the existing `circuit::bilateral_aggregation_air` |
| **Consensus/finality** | tier lattice + abstract `committed` + `World` stub | a real protocol (blocklace / Cordial-Miners) discharging `World`; the Byzantine theorems |
| **Privacy** | algebraic tier proved over `CryptoKernel` | real Pedersen/stealth/nullifier/ZK as the `CryptoKernel` Rust impl |
| **Circuit** | 4 scalar ℤ-equations | the real field-AIR; the `chainOk`→Poseidon-digest binding; extract `kernelCircuit` to the prover |
| **CapTP/GC** | caps model + GC laws/impossibilities | the transport protocol + an executable collector |

## Phased plan to BE the successor (not a demo)
**Phase A — grow the verified kernel core to dregg1's real shape.** Replace the toy
`KernelState`/`Turn` with the real cell (multi-asset camera resources, slot-table, a
`CellProgram` interpreter), keeping every law (`exec_conserves`/`cexec_attests`/`bridge`)
proved as it grows. This is the heart: make the *verified* kernel cover what dregg1's
`turn`/`cell` crates actually do.

**Phase B — execute the cascade (DREGG1-TO-DREGG2.md), oracle-first.** For each
REPLACE-BY-LEAN crate (`turn`, `cell`, `coord`): (1) extend the differential harness to
the crate's real conservation+authority+predicate checks, (2) drive Lean≡Rust to 100% on
its real inputs, (3) re-seat the Rust check onto the FFI'd Lean kernel. Frozen v1 stays
until its check is oracle-equal. Real `CryptoKernel`/`World` Rust impls (Poseidon/Pedersen/
WHIR; net/clock) are the contract.

**Phase C — close the metatheory.** Find remaining mis-stated theorems (the
abstract-parameter risk — 4 found so far), close the deep opens (or pin them as named
assumptions), grow the circuit to the real AIR, totalise `CellProgram→TurnCoalg`.

**Phase D — reorg + polish.** Move flat Abstract files → `Metatheory/Spec/Abstract/`;
the `Spec/Exec/Proof/Foundation/Protocol` layout; slim the heavy `import Mathlib.Tactic`.

## Robigalia relationship (scope)
rbg (Robigalia) is the seL4-based OS; **dregg is a *component* of it**, not the OS. We do
NOT boot, integrate seL4, or own the kernel-on-metal — `~/dev/sel4` + the rust-in-seL4
frameworks are rbg's job. dregg2 earns inclusion in rbg by being a good enough verified
distributed-object/capability layer. So "dregg2 should be bootable" is a non-goal; "dregg2
is a real, verified dregg1 successor that rbg can host" is the goal.

## The discipline that got us here (keep it)
Spec-first, every claim compiler-checked; NO fake-to-pass (honest open holes with PRIMITIVE/
OPEN notes, never `axiom`/`admit`/`native_decide` cheats); race-free parallel via
`lake env lean`; the portals keep crypto out of the trusted Lean; the differential harness
keeps Rust ≡ the Lean golden oracle.
