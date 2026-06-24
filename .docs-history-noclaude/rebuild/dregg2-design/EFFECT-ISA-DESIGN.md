# EFFECT-ISA-DESIGN — is the 54-effect VM the right instruction set for a verified capability kernel?

> ⚑ **GROUND-CHECKED vs live Lean 2026-06-02** (post-2-compaction drift-repair); REAL/DECORATIVE/ASPIRATIONAL
> tags carry file:line receipts. The Rust side (`action.rs`, `columns.rs`, `apply.rs`) is unchanged at 54;
> the DRIFT was on the Lean side, which this doc had only as a secondary cross-check + a wishlist of
> "MISSING" primitives. **What actually landed (the good-direction drift):** the doc's *#1 CORE-MISSING*
> primitive — **per-asset balance (multi-asset C1/C2)** — is now the **primary executable kernel surface**
> (`FullActionA`, `TurnExecutorFull.lean:1928`, 46 constructors, each money-moving arm carrying
> `(asset : AssetId)`; `MultiAsset.lean:38`; per-asset conservation **PROVED + `#assert_axioms`-pinned**,
> `execFullForestA_conserves_per_asset` `FullForest.lean:224`/:421). The doc's *#4* one-shot linear
> continuation / await family **also landed** in the verify-side metatheory (`Await.lean`,
> `four_faces_unify:426`, term-proved). The vat-boundary **law** landed coinductively (`Boundary.lean`,
> `boundary_respecting_sound:244`) though ρ_in/ρ_out as a *typed selector* is still absent (the
> effect-level claim stands). The forest-delegation handoff is the one gap that did **not** close:
> `execFullChildrenA` still discards the edge (`FullForest.lean:124`, pattern `⟨_, _, _, sub⟩`) — **#138
> genuinely OPEN**. See **§0.5 (Lean ground-truth)** for the full receipt block.
>
> **Scope / method.** Read-only design analysis. The question is whether dregg's effect set is the
> RIGHT *orthogonal basis* for a verified capability kernel that will REPLACE the Rust kernel —
> answered in BOTH directions: **(A) reduction** (where it is bloated / redundant) and **(B)
> expansion** (where the dregg2 architecture implies primitives no current effect expresses). The
> set can be simultaneously over-named AND under-covered; the goal is the right basis, not the
> smallest one.
>
> **Ground truth (file:line).** The runtime `Effect` enum: `turn/src/action.rs:760` (54 variants
> + the `Effect::linearity` exhaustive match at `:1675`). The in-circuit set: `NUM_EFFECTS = 54`
> selectors at `circuit/src/effect_vm/columns.rs:78` (indices 0..53 at `:82–:250`), per-variant
> witness in `circuit/src/effect_vm/effect.rs`, per-selector constraints in
> `circuit/src/effect_vm/air.rs`. The actual mutations: `turn/src/executor/apply.rs` (one
> `apply_*` per effect, dispatch at `:26`). **The Lean mirror (CORRECTED 2026-06-02):** the 52-tag
> abstract coloring `inductive EffectKind` is in **`metatheory/Dregg2/CatalogInstances.lean:285`**
> (exactly 52 constructors, grep-counted), with `effectLinearity` total + `every_effect_classified`
> exhaustive at `CatalogEffects.lean:201` (`CatalogEffects.lean` *extends*, never redefines, the
> coloring). But the **executable** ISA — the one the swap actually runs — is now the **46-arm
> `inductive FullActionA`** at `metatheory/Dregg2/Exec/TurnExecutorFull.lean:1928`, dispatched by
> `execFullA` (`:2236`–`:2660`, 46 arms). The 52-vs-54 gap (Lean colors 52, Rust enums 54) is the
> honest delta: `queueAtomicTx`/`queuePipelineStep` are colored but the executable `FullActionA`
> folds them, and a couple of Rust variants have no Lean tag yet. Prior evidence:
> `docs/rebuild/FAITHFULNESS-AUDIT.md` ("the
> 52-effect catalog is ~6 shapes wearing ~50 names"). Architecture: `docs/rebuild/REORIENT.md §2`,
> `cand-A-vat-coalgebra.md`, `cand-C-cap-distributed.md`, `study-mina-relink.md`.
>
> **One correction carried in.** A concurrent agent (FID-ESCROW) is de-shadowing
> escrow/obligation/note to genuinely-distinct semantics (single-cell-debit-into-side-table +
> nullifier-set). This doc reads dregg1's *stable* `apply.rs` for the real semantics and treats
> escrow/note/obligation as **genuinely distinct shapes**, NOT as the `pairedStep` shadow the
> Lean toy modeled. The FAITHFULNESS-AUDIT's "~6 shapes" count was an artifact of the *Lean*
> simplification (`EffectsPaired.lean` made escrow a balance-conserving two-cell transfer); the
> *Rust* `apply_create_escrow` (`apply.rs:1674`) is single-cell debit + side-table insert — a
> distinct shape. The honest shape count, read off `apply.rs`, is **~9–11**, not 6.

---

## 0.5 Lean ground-truth receipt block (the 2026-06-02 drift-repair)

This doc was written against the *Rust* runtime as the ISA to be replaced, with the Lean side as a
secondary cross-check and a wishlist. Two compactions later, the live Lean has moved **toward** the
proposed basis. Here is what the executable Lean kernel actually is, tagged **REAL** (a term-proved
Lean object with teeth), **DECORATIVE** (vocabulary only — no Lean object; grep-confirmed absent), or
**ASPIRATIONAL** (honestly-named OPEN / unbuilt). Receipts are `file:line` into `metatheory/Dregg2/`.

**The executable ISA is `FullActionA` — and it is per-asset.** — **REAL.**
`inductive FullActionA` (`Exec/TurnExecutorFull.lean:1928`, **46 constructors**), dispatched by
`execFullA` (`:2236`–`:2660`, **46 arms**, no open holes / `native_decide`). Every value-moving
arm carries `(asset : AssetId)`: `balanceA (turn) (asset)`, `mintA/burnA (…) (asset)`,
`bridgeMintA/bridgeLockA/bridgeFinalizeA (…) (asset)`, `createEscrowA/createObligationA/createCommittedEscrowA (…) (asset)`.
This is the **executable artifact of the proposed §A CORE** (C1 balance, C2 supply, C9/C10 side-table
lock/settle, C8 lifecycle, C4 authority, C11/C12 notes) — not a wishlist; it runs.

**§1's #1 "MISSING-NEEDS-PRIMITIVE: per-asset C1/C2" — LANDED.** — **REAL.** `MultiAsset.lean:38`
`abbrev AssetId := Nat`; balances are a total `MACellId → AssetId → ℤ` (`:47`); the conserved quantity
is the per-asset family `maTotal k a := ∑ c, k.bal c a` (`:86`). Keystones, all term-proved +
`#assert_axioms`-pinned: `maExec_conserves_per_asset` (`MultiAsset.lean:130`); at the forest level
`execFullForestA_conserves_per_asset` (`FullForest.lean:224`, pinned `:421`) — *a committed forest whose
net per-asset delta is 0 in asset b preserves b's total supply, the `CONSERVATION_VECTOR`*. The doc's
"this must be CORE before the kernel replaces Rust" is satisfied on the executable layer. (Task **#129
FILL 1** is still `in_progress` — the residual is breadth/wiring, not the keystone, which is proved.)

**The forest no-amplification (Granovetter) law — PROVED, but as forest *data*, not the *handoff*.**
— **REAL theorem / ASPIRATIONAL execution.** `execFullForestA_no_amplify` (`FullForest.lean:251`,
pinned `:423`) proves `∀ e ∈ forestEdgesA f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2`
via `derive_no_amplify` — REAL over the edge *list*. **BUT** the executor does NOT install those caps:
`execFullChildrenA` (`FullForest.lean:124`, pattern `| ⟨_, _, _, sub⟩ :: rest =>` — the holder/keep/
parentCap fields **discarded**; same discard at `:145` lowering and `:412`) runs each child against the
**unchanged** state (the `DelegationMode::None` default, candidly stated `FullForest.lean:317` §9). The
§9 docstring at `:119`–`:121` *claims* "the delegated cap is `derive`d into the child holder's slot" —
that text is **ASPIRATIONAL**; the code is a no-op handoff. **Routing the edge onto
`recKDelegateAtten` is task #138, genuinely OPEN.** This is the one place the doc's framing under-states
the gap: forest delegation is *decorative on execution* today (cf. memory "Forest Delegation Decorative").

**Per-node attestation across the whole tree — PROVED.** — **REAL.** `execFullForestA_each_attests`
(`FullForest.lean:290`, pinned `:426`): every tree node attests `fullActionInvA` (per-asset ledger
vector ∧ ChainLink ∧ ObsAdvance ∧ the kind obligation) — read through `execFullForestA_eq_execFullTurnA`
over the pre-order lowering. `execFullForestA_unauthorized_fails` (`:309`) is the fail-closed root.

**§B #4 "one-shot linear continuation typing + the await family" — LANDED in the verify metatheory.**
— **REAL (verify-side), still ASPIRATIONAL as a kernel selector.** `Await.lean` encodes the await
family as algebraic effects + a one-shot continuation: `OneShot` (`:109`, "intentionally **no**
projection back to a reusable `k`", `:103`); `four_faces_unify` (`:426`, term-proved) collapses
zkpromise / discharge / intent / eventual to one `AwaitCore`; `runtime_guard_is_double_spend` (`:223`)
and `commit_resumes_once` (`:312`) are term-proved. ⚠ **Docstring drift:** the header says "open-hole
bodies are real obligations" (`Await.lean:42`) — **STALE**; grep finds zero proof-term open holes (the only
such tokens are that comment). The await *engine* the doc called "MISSING as a typed effect" is now a
proved algebra; it is still **not** a kernel selector/effect, so the ISA-level §B claim stands.

**The vat-boundary *law* — LANDED coinductively; ρ_in/ρ_out as a *typed selector* — still absent.**
— Boundary law **REAL**, ρ-effect **ASPIRATIONAL**. `Boundary.lean` carries the coinductive
`BoundaryRespecting` law + `boundary_respecting_sound` (`:244`, term-proved `:= by exact hbr.admissible …`).
⚠ **Docstring drift:** "every theorem is stated with an open-hole body" (`:29`) and "Stated open" (`:243`)
are **STALE** — those theorems have real bodies. But this is the *soundness law of the membrane*, **not**
a `Cap.exportAsKey`/`importKey` effect: grep confirms no ρ_in/ρ_out selector in `FullActionA` or
`Exec/VatBoundary.lean`. So §B #3 (ρ_in/ρ_out as first-class typed effects) is **still genuinely OPEN**.

**The FFI swap target is wired.** — **REAL (wire), DIFFERENTIAL-pending.** `@[export] dregg_exec_full_forest_auth`
(`Exec/FFI.lean:3027`) is the gated complete-turn export (the swap entry per the memory roadmap), alongside
`dregg_exec_full_turn` (`:938`) and `dregg_exec_full_turn_wide` (`:2732`). The COMPLETE-turn wire codec
roundtrip (FILL J, task #136 `in_progress`) is PROVED for most productions incl. `FullActionA` "complete at
all 46 arms" and the per-asset `BAL` ledger entry, `#assert_axioms`-pinned (`Exec/CodecRoundtrip.lean:21,41,70`);
the one in-progress production is `parseCaveatsW` (`:58`).

**Net for this doc:** the §A CORE basis is no longer a *proposal* — its money/lifecycle/authority/note
shapes are the **live `FullActionA`**, per-asset, term-proved, axiom-pinned. The §B expansion list is
**half-retired**: multi-asset (#1) DONE, one-shot await (#4 engine) DONE in metatheory; the genuinely-open
remainder is **forest-delegation handoff (#138)**, **ρ_in/ρ_out typed effects (#3)**, **cross-cell BoundDelta
as a kernel arm (#2)**, **return-projection (#4 the return face)**, and **fork (#5)** — see §3's revised ranking.

---

## 0. Executive answer

**No, the 54-effect set is not the right basis — but the fix is not "shrink to 6."** It is
simultaneously **over-named** (≈18 effects are derivable macros or DSL-userspace that need not be
kernel primitives / circuit selectors) and **under-covered** (the dregg2 architecture implies
≈7 operations with NO current effect — most importantly the *coalgebra-level* operations
checkpoint/fork/return-projection, the *vat-boundary* ρ_in/ρ_out cap↔key crossing as a typed
effect, the *JointTurn half-edge* BoundDelta, and *beacon/VRF randomness*).

The right orthogonal basis is **~13 CORE primitives** (the genuine state-transition shapes the
circuit MUST bake in for one-trace atomicity) **+ a small set of new boundary/coalgebra primitives
the architecture demands** + everything else demoted to **DERIVED-MACRO** (expands to CORE inside
the executor, no dedicated selector) or **DSL-USERSPACE** (a `Custom`/program obligation). The
payoff is a TCB / constraint-surface cut from 54 selectors to ~18–20, while *adding* the
primitives that make it a verified *capability OS* rather than a verified *ledger*.

---

## 1. The effect catalog by TRUE state-transition signature

Signature columns: **R/W** = what it reads / writes on the cell ledger (`bal` = balance slot,
`field` = named state field, `caproot` = c-list Merkle root, `side` = an off-ledger side table,
`nullset` = the nullifier set, `lifecycle` = the off-trace lifecycle phase, `nonce`); **Cons** =
LinearityClass (`action.rs:1675`); **Auth** = does it touch the authority graph. Selector index
from `columns.rs`. Grouped by **genuine shape** (the clustering, not the name).

### Shape S1 — balance debit/credit (conservative two-party move)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `Transfer` | 1 | bal− (from), bal+ (to), nonce | Conservative | `:536` (real two-cell) |
| `QueueEnqueue` | 19 | bal− (sender), bal+ (queue cell) | Conservative | `:3310` (real two-cell deposit) |
| `QueueDequeue` | 20 | bal+ (refund), queue-root advance | Conservative | `:3420` |

`balance_change: Option<i64>` on the `Action` itself (`action.rs:96`) is the *Mina-style* signed
half-edge — a turn-level conservation accumulator that already expresses S1 without a paired
`Transfer`. **This is the seed of the BoundDelta half-edge** (§B).

### Shape S2 — single-cell debit-into-side-table + settle-from-side-table (the escrow/obligation family)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `CreateEscrow` | 37 | bal− (creator), `side`(escrows) insert | Conservative | `:1674` debit-only + `self.escrows.insert` `:1770` |
| `ReleaseEscrow` | 42 | bal+ (recipient), `side` resolve | Conservative | `:1790` credit-only `:1958`, `resolved=true` `:1969` |
| `RefundEscrow` | 43 | bal+ (creator), `side` resolve | Conservative | `:1976` credit-only `:2030` |
| `CreateCommittedEscrow` | 39 | bal− (creator), `side` insert (commitments) | Conservative | `:2049` (+ range proof) |
| `ReleaseCommittedEscrow` | 44 | bal+ (recipient, by opening), `side` resolve | Conservative | `:2231` |
| `RefundCommittedEscrow` | 45 | bal+ (creator, by opening), `side` resolve | Conservative | `:2331` |
| `CreateObligation` | 6 | bal− (obligor) by stake, `side`(obligations) insert | Conservative | `:1337` |
| `FulfillObligation` | 7 | bal+ (obligor), `side` resolve | Conservative | `:1483` |
| `SlashObligation` | 9 | bal+ (beneficiary), `side` resolve | Conservative | `:1599` |

**This is ONE genuine shape with TWO halves: `lock` (debit→side-table) and `settle` (side-table→credit).**
Conservation holds *across the pair via the side table*, not per-effect on the cell ledger. Escrow,
committed-escrow, and obligation are the **same lock/settle automaton over different side-table
record types + different release predicates** (proof / signatures / predicate-hash / deadline). The
committed variant adds a Pedersen value-commitment + range proof (a *crypto-portal* attribute), not
a new shape. This is the cluster the FAITHFULNESS-AUDIT flagged as over-named; FID-ESCROW's
side-table model is the correct distinct semantics, and it collapses **9 selectors → 1 shape with a
record-typed payload + a release-predicate**.

### Shape S3 — nullifier-set insert / membership-spend (the note family)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `NoteCreate` | 5 | `nullset`/note-tree commitment insert, bal− or committed | Conservative | `:988` |
| `NoteSpend` | 4 | `nullset` insert (double-spend reject), bal+ | Conservative | `:854` set-insert `:951`, ZK verified `:926` |

Genuinely distinct from S1/S2: the conserved quantity lives in a Merkle note-tree + a nullifier set,
not in cell balances; the move is gated by a STARK spending proof (crypto portal). **One shape**
(commitment-insert / nullifier-insert), two directions.

### Shape S4 — supply mint / burn (disclosed non-conservation)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `Burn` | 46 | bal− (no credit), `was_burn` disclosed | Annihilative | `:4317` |
| `BridgeMint` | 40 | bal+ (from portable proof) | Generative | `:1106` |
| `CreateCell` | 31 | new cell, bal+ ex nihilo | Generative | `:748` |
| `CreateCellFromFactory` | 13 | new cell w/ factory provenance | Generative | `:3112` |
| `SpawnWithDelegation` | 32 | new child cell + snapshot caps | Generative | `:2947` |

`Burn`/`BridgeMint` are the canonical asymmetric mint/burn pair (the supply generator). `CreateCell*`
/ `Spawn` are *object* generation (a new `νF` point) — arguably a **distinct shape** from *value*
generation (see §B: spawn-as-anamorphism). Today they share the Generative color but mutate
different things (a new ledger entry vs. a balance).

### Shape S5 — cap-graph edge add / remove / narrow (the authority family)
| effect | sel | R/W | Auth | apply.rs |
|---|---|---|---|---|
| `GrantCapability` | 3 | caproot += edge | add edge | `:595` |
| `Introduce` | 35 | caproot += edge (3-party, attenuated) | add edge | `:2791` (`is_attenuation` `:2829`, consent `:2845`, expiry) |
| `RevokeCapability` | 24 | caproot −= slot | remove edge | `:673` |
| `AttenuateCapability` | 48 | caproot: slot → narrower commitment | narrow edge | `:4377` |
| `ExerciseViaCapability` | 34 | recursive: cap lookup + inner effects on target | traverse | `:2441` |

**One shape with three operations** (add / remove / narrow) + **one combinator** (`Exercise` = the
categorical eval map `B^A × A → B`, which RECURSES into inner effects — `apply.rs:2441`). `Introduce`
is `GrantCapability` + an attenuation+consent+expiry guard; `AttenuateCapability` is a narrowing
edge-rewrite. These are genuinely distinct authority moves but they are all *cap-graph edge edits*.

### Shape S6 — named-field write / passthrough-with-binding (the Neutral / state family)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `SetField` | 2 | field write | Neutral | `:497` |
| `SetPermissions` | 26 | permission table (off-trace), passthrough | Neutral | `:775` (applied LAST) |
| `SetVerificationKey` | 27 | VK (off-trace), passthrough | Neutral | `:803` |
| `EmitEvent` | 25 | nothing (receipt log only), passthrough | Neutral | `:703` |
| `RefreshDelegation` | 29 | epoch bump (off-trace), passthrough | Neutral | `:2991` |
| `IncrementNonce` | 53 | nonce++ | Monotonic | `:719` |

**This is the dominant "moved-complexity" cluster.** In the AIR, `SetPermissions`,
`SetVerificationKey`, `EmitEvent`, `CreateSealPair`, `RefreshDelegation`, `RevokeDelegation`,
`CreateCell`, `Spawn`, `BridgeCancel`, `Exercise`, `Introduce`, `PipelinedSend`, `ReleaseEscrow`,
`RefundEscrow`, `Release/RefundCommittedEscrow`, `CellDestroy`, `CellSeal`, `CellUnseal`,
`ReceiptArchive`, `Refusal`, `MakeSovereign`, `CreateCellFromFactory` are **all "state passthrough
+ bind a hash into `effects_hash` + tick nonce"** (`air.rs:909, 931, 950, 1194, 2224, 2315, 2358,
2393` etc.). The ONLY per-selector difference is **which hash is bound and how many params** — i.e.
a selector + a domain-tagged hash. Two dozen selectors are the *same algebraic row* distinguished by
a constant. This is the literal "~50 names" the audit named, in the circuit.

### Shape S7 — lifecycle one-way transition (Terminal)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `CellSeal` | 49 | lifecycle → Sealed | Terminal | `:4218` |
| `CellUnseal` | 50 | lifecycle Sealed→Live | Terminal | `:4251` |
| `CellDestroy` | 47 | lifecycle → Destroyed (irreversible) | Terminal | `:4283` |
| `MakeSovereign` | 12 | cells → sovereign_commitments | Terminal | `:3084` |
| `ReceiptArchive` | 51 | lifecycle → Archived | Terminal | `:4441` |
| `RevokeDelegation` | 30 | child epoch invalidated | Terminal | `:3044` |
| `Seal` | 10 | field-seal bit set (in-trace) | Generative\* | `:2743` |
| `Unseal` | 11 | field-seal bit clear (brand) | Generative\* | `:2874` |

`CellSeal/Unseal/Destroy/Archive/MakeSovereign` are **lifecycle-phase writes** — a finite-state
machine on an off-trace `CellLifecycle` enum. One shape (a guarded phase transition), with `Destroy`
the absorbing state. `Seal`/`Unseal` (field-level, selectors 10/11) are a *different* primitive (a
field-mask bit + brand) from `CellSeal`/`CellUnseal` (lifecycle) — the name collision is itself an
over-naming smell (`effect.rs:269` vs `:520` explicitly note they coexist).

### Shape S8 — queue (FIFO Merkle structure)
| effect | sel | R/W | apply.rs |
|---|---|---|---|
| `QueueAllocate` | 18 | new queue cell, bal− cost | `:3227` |
| `QueueResize` | 21 | capacity field, bal− if growing | `:3507` |
| `QueueAtomicTx` | 22 | multi-queue root transition, net deposit | `:3586` |
| `QueuePipelineStep` | 23 | source-root advance + sink-root advance | `:3747` |
| (`QueueEnqueue`/`Dequeue` are S1 balance moves + a Merkle-root advance) | 19/20 | | `:3310`/`:3420` |

The queue family is a **Merkle-CRDT structure on a cell's state** (`field[4]=queue_root`). Enqueue/
dequeue are S1 (balance) + a hash-chain root advance; allocate/resize are S4 (object/quota gen);
AtomicTx/PipelineStep are **macros over enqueue/dequeue** with an all-or-nothing wrapper. This is a
prime **DSL-userspace** candidate: a queue is a *cell program* (a CellProgram whose state field is a
MerkleQueue), not a kernel primitive. The kernel needs only "advance a Merkle root under a checked
transition" + S1 — everything queue-specific is a userspace rule.

### Shape S9 — CapTP wire-mirror (export / enliven / drop / handoff)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `ExportSturdyRef` | 14 | swiss-table insert, export_counter++ (field[7]) | Monotonic | `:3879` |
| `EnlivenRef` | 15 | caproot += routing entry, use_count++ (field[6]) | Monotonic | `:3955` |
| `DropRef` | 16 | refcount−− (field[5]) | Terminal | `:4034` |
| `ValidateHandoff` | 17 | Merkle membership of cert, consume leaf | Monotonic | `:4069` |

These mirror CapTP wire ops as on-chain turns (`action.rs:1159`). `Enliven` is **S5 cap-graph add**
(it grants a routing entry); `Export` is a swiss-table insert + counter; `Drop` is a refcount
decrement; `ValidateHandoff` is a Merkle-membership consume. This is *the vat-boundary crossing*
expressed in dregg1's idiom — but expressed as **four separate counter-bumps**, not as the typed
ρ_in/ρ_out the architecture wants (§B).

### Shape S10 — pipelined/eventual send (promise pipelining)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `PipelinedSend` | 36 | dispatch action to an `EventualRef` | Neutral | `:2657` |

The promise-pipelining seam. Today a near-noop passthrough at the executor level (`:2657`); the
*await/resolve* semantics live in `turn/src/pending.rs` + `conditional.rs`. This is the embryo of
the coalgebra's `Await` family (§B).

### Shape S11 — sealer/unsealer brand (the rights-amplification-free transfer)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `CreateSealPair` | 28 | register brand pair | Generative | `:2675` |
| `Seal` | 10 | wrap cap in opaque box | Generative | `:2743` |
| `Unseal` | 11 | recover cap from box (recipient) | Generative | `:2874` |

Miller's sealer/unsealer (three-vat handoff). `CreateSealPair` mints a brand; `Seal`/`Unseal` are
the wrap/unwrap. Note `Seal` selector 10 is *overloaded* between field-seal (S7) and box-seal (S11)
at the wire level only by context — a real distinctness hazard.

### Shape S12 — evidence-of-absence (the categorical dual)
| effect | sel | R/W | Cons | apply.rs |
|---|---|---|---|---|
| `Refusal` | 52 | nonce++, audit-slot record, witnessed non-action | Monotonic | `:4114` |

Genuinely novel (the categorical initial object — proof of non-action, `action.rs:1238`). It is S6
(passthrough + bind a `(commitment,reason)` hash) at the state-transition level, distinguished by a
witnessed non-membership proof. Whether it is a *primitive* or a *Custom witnessed-predicate* is the
sharpest CORE-vs-DSL question in the set (§A classification).

---

## 2. PART A — REDUCTION: CORE-PRIMITIVE / DERIVED-MACRO / DSL-USERSPACE

**The orthogonal-basis test.** A primitive is CORE iff (1) it is a distinct *state-transition
shape* not expressible as a composition of other CORE shapes, AND (2) the circuit must bake it as a
dedicated selector for **one-trace atomicity** (the row's algebra is genuinely different, not just a
different bound constant). A DERIVED-MACRO expands to a CORE composition inside the executor with
NO dedicated selector. A DSL-USERSPACE op is a `CellProgram` rule / `Custom` witnessed predicate —
verified by the program's own obligation, not the kernel ISA.

### The CORE primitives (the genuine basis) — ~13

| CORE primitive | subsumes (current names) | why it must stay a selector |
|---|---|---|
| **C1 `Balance.move(from?,to?,δ)`** signed half-edge | Transfer, QueueEnqueue/Dequeue balance leg, `balance_change` | the conservation arithmetic (30+34-bit limbs, underflow range-check, `air.rs` Σδ=0) is the soundness keystone; must be in-circuit |
| **C2 `Supply.adjust(cell,±δ,disclosed)`** | Burn, BridgeMint (local leg) | disclosed non-conservation needs the `was_burn`/`was_mint` flag bound into receipt_hash in-circuit |
| **C3 `Cell.create(seed)`** object generation | CreateCell, CreateCellFromFactory, SpawnWithDelegation | a new `νF` point + provenance; factory/spawn are C3 + a *descriptor*/*snapshot* param, not new shapes — see DERIVED below |
| **C4 `CapGraph.edge(op∈{add,remove,narrow}, src,dst,attenuation)`** | GrantCapability, RevokeCapability, AttenuateCapability, Introduce, EnlivenRef | the caproot Merkle advance + attenuation monotonicity is the authority keystone; op is a 2-bit param, NOT 5 selectors |
| **C5 `Cap.exercise(slot, inner)`** eval map | ExerciseViaCapability | RECURSIVE (`apply.rs:2441`); the one combinator; must gate inner effects' authority in one trace |
| **C6 `Field.write(idx,value)`** | SetField | the only genuine state-field mutation |
| **C7 `Meta.bind(domain_tag, hash)`** passthrough+commit | SetPermissions, SetVerificationKey, EmitEvent, RefreshDelegation, BridgeCancel, BridgeFinalize, PipelinedSend, Refusal, ReleaseEscrow/Refund\*, CreateSealPair | **ALL state-passthrough + bind-a-hash rows collapse to ONE selector** with a `domain_tag` param; the row algebra is identical (`air.rs:909–1000, 2224–2400`) |
| **C8 `Lifecycle.transition(phase)`** guarded FSM | CellSeal, CellUnseal, CellDestroy, MakeSovereign, ReceiptArchive, RevokeDelegation | one FSM on the off-trace lifecycle; `phase` is a param, not 6 selectors |
| **C9 `SideTable.lock(record)` / C10 `SideTable.settle(id,predicate)`** | CreateEscrow/Obligation (lock); Release/Refund/Fulfill/Slash (settle) | the lock/settle automaton; record-type + release-predicate are payload params (FID-ESCROW's model) |
| **C11 `NoteTree.insert(commitment)` / C12 `Nullifier.spend(nullifier,proof)`** | NoteCreate (insert); NoteSpend (spend) | nullifier-set membership + double-spend reject + ZK-portal gate; distinct conserved domain |
| **C13 `Nonce.tick`** | IncrementNonce | the global monotone row invariant (every non-NoOp ticks it; explicit selector for nonce-only turns, `columns.rs:65`) |

Plus the structural `NoOp` (selector 0, padding). That is **~13 CORE shapes** (C9/C10 and C11/C12
are dual halves of two shapes, so 11 *shapes*; 13 *operations*).

### DERIVED-MACRO (expand to CORE in the executor; NO selector)

| current effect | derivation |
|---|---|
| `Introduce` (35) | C4.add with a `(attenuation ⊑ held) ∧ consent ∧ expiry` guard — a *guarded* C4, not a new shape (`apply.rs:2829–2862`) |
| `CreateCellFromFactory` (13) | C3 + factory-descriptor validation (a Custom obligation on `params`) |
| `SpawnWithDelegation` (32) | C3 + a cap-snapshot (`SnapshotRefresh` mode) — C3 + C4-batch |
| `QueueAllocate/Resize/AtomicTx/PipelineStep` (18,21,22,23) | C3 (allocate) / C6+C2 (resize) / **macros over C1+root-advance** with an all-or-nothing wrapper |
| `ReleaseEscrow/RefundEscrow/Fulfill/Slash` (42,43,7,9) | C10.settle with a release-predicate (proof / sigs / deadline / predicate-hash, `apply.rs:1829–1947`) |
| `Release/RefundCommittedEscrow` (44,45) | C10.settle with a commitment-opening predicate |
| `CreateCommittedEscrow` (39) | C9.lock with a Pedersen-commitment record + range-proof (crypto portal) |
| `BridgeMint/Lock/Finalize/Cancel` (40,38,41,33) | C2 (mint leg) / C9.lock (lock) / C7 (finalize/cancel passthrough+bind) + a *foreign-finality portal* hypothesis |
| `ValidateHandoff` (17) | C7 (Merkle-membership consume = bind + monotone counter) |
| `Refusal` (52) | C7 + a witnessed non-membership predicate (DSL — see below) |
| `EmitEvent`, `SetPermissions`, `SetVerificationKey`, `RefreshDelegation`, `PipelinedSend` | C7 (`domain_tag` distinguishes) |

### DSL-USERSPACE (a CellProgram rule / `Custom` witnessed-predicate; NOT a kernel selector)

| current effect | why it is userspace |
|---|---|
| The entire **queue family** semantics (FIFO ordering, capacity, pipeline routing) | a queue is a *cell whose state field is a MerkleQueue*; the kernel needs only "advance a Merkle root under a checked transition"; FIFO discipline is a program rule, not an ISA shape (`apply.rs:3227–3879`) |
| `Refusal`'s non-action proof | a `WitnessedPredicate::NonMembership` (`action.rs:1268`) — the kernel verifies the witness via the registry; non-action is an *app* artifact |
| Committed-escrow's range proof / Pedersen path | a crypto-portal obligation (the AIR keeps it OUT of the semantic law per `cand-A §2.4` / `REORIENT §6`) |
| `Seal`/`Unseal` field-mask (10,11) | a cell-program field-lock convention, distinct from the lifecycle C8 and the brand C11 |

**Reduction tally.** 54 selectors → **~18–20** (the 13 CORE ops + a handful that stay selectors for
in-circuit atomicity: the two side-table halves, the two note halves, the lifecycle FSM, the
sealer-brand C11, the cap-exercise combinator). The ≈18 demoted to DERIVED-MACRO add ZERO circuit
selectors (they expand to CORE rows in the trace generator). The queue-semantics + refusal-proof +
committed-crypto move to DSL/portal. **TCB / constraint-surface payoff: roughly a 60% cut in
selector count and per-selector AIR constraint blocks** — the `air.rs` passthrough-with-bind family
(§S6, ≈24 selectors sharing one row algebra) collapses to C7 with a `domain_tag` param.

---

## 3. PART B — EXPANSION: architecture-implied operations × coverage

For each operation the dregg2 architecture (`cand-A`, `cand-C`, `study-mina-relink`, `REORIENT`)
implies, the table maps it to a current effect or **NONE**, then classifies the gap:
**MISSING-NEEDS-PRIMITIVE** (a new kernel selector/shape), **COMPOSABLE-IN-DSL** (a userspace
rule / Custom), or **IS-A-RUNTIME-THEOREM** (no effect at all — a property of the coalgebra +
retained log, per `cand-A §5/§10`).

| architecture op | source | current effect | gap class |
|---|---|---|---|
| living-cell **spawn / fork-as-coalgebra** (one pre-state → two valid descendant heads) | `cand-A §6` | `SpawnWithDelegation` (32) spawns a *child*, NOT a *fork* of self; no fork-the-unfold op | **MISSING-NEEDS-PRIMITIVE** (fork is a span/pushout, `cand-A §6`) |
| **anamorphism re-seed** (restore from a retained head) | `cand-A §5` | NONE | **IS-A-RUNTIME-THEOREM** (re-seed the unfold; "the coinductive head IS the checkpoint") |
| **checkpoint** (name a `(head,receipt)` point) | `cand-A §5` | NONE; `ReceiptArchive` (51) is the *embryo* (it names a prefix) but archives, not checkpoints | **IS-A-RUNTIME-THEOREM** + a thin **MISSING** "name-a-head" effect if checkpoints must be on-chain |
| **replay** (re-run from the log) | `cand-A §5` | NONE (differential harness does it off-chain) | **IS-A-RUNTIME-THEOREM** |
| **time-travel** (fork at a checkpoint, alt turn-stream) | `cand-A §5` | NONE | **IS-A-RUNTIME-THEOREM** (= fork at step n) |
| **JointTurn participation / CG-5 bound-delta half-edge** | `study-mina-relink §1`, `REORIENT §2` | `balance_change: Option<i64>` (`action.rs:96`) is a turn-level half-delta; `StateConstraint::BoundDelta` (`program.rs:747`) names the peer | **MISSING (kernel arm) — but the LAW landed**: `Exec/CrossCellForest.lean` carries `crossForest_conserves` (the N-ary cross-cell Σ=0 binding-carried CG-5), `crossForest_no_amplify`, `crossForest_attests` (REAL, routed from `FullForest.lean:328` §9). The cross-cell **Σ=0 measure** is proved; what is still missing is a **first-class `FullActionA` half-edge arm with a peer-existence witness** (today cross-target is a routing overlay, not an executable action) |
| **vat-boundary ρ_out** (serialize held cap → biscuit key-as-cap) | `cand-C §398`, `cand-A §11` | `Authorization::Token` export is the *carrier* (`action.rs:422`) but there is no *effect* that performs ρ_out | **STILL MISSING (effect) — but the boundary LAW landed**: `Boundary.lean` proves the coinductive `BoundaryRespecting`/`boundary_respecting_sound:244` (REAL); ρ_out as a typed `Cap.exportAsKey` selector is still absent in `FullActionA` (grep-confirmed). Today only `exportSturdyRefA` (CapTP-swiss), not biscuit ρ_out |
| **vat-boundary ρ_in** (re-mint key-as-cap → c-list slot) | `cand-C §399` | `enlivenRefA` re-mints a *swiss* ref; `Authorization::CapTpDelivered`/`Token` verify on entry | **PARTIAL (unchanged)** — `enlivenRefA` is the swiss flavor; biscuit ρ_in is **MISSING** as a cap-graph-add-from-verified-key effect. The membrane *soundness obligation* is discharged (Boundary.lean); the *typed crossing effect* is not |
| **revocable-forwarder / named-lossy Φ** (the membrane) | `cand-A §2.1`, `cand-C §210` | NONE (the loss is by-construction; `revocation_channel` on bearer caps `action.rs:470` is the closest) | **IS-A-RUNTIME-THEOREM** (`LossyMorphism` theorem, `cand-A §8`) + revocation = a tombstone edge (C8/C4) |
| **beacon / VRF randomness** | (implied by any fair-ordering / leader / lottery; absent from canon as a primitive) | NONE — only `note_spending_air.rs:305` note `randomness` (a blinding scalar, not a beacon) | **MISSING-NEEDS-PRIMITIVE** *iff* the kernel must consume verifiable randomness in a turn (leader election lives in finality, but app-level lotteries need it) — **deferrable** |
| **proof-carrying-forest ops** (attest a forest of step-proofs) | `circuit/src/proof_forest.rs` (new), `ProofForest.lean` | NONE at the effect level (forest is a *turn/finality* structure, not an effect) | **NOT an effect** — it is the JointTurn aggregation layer; correctly above the ISA |
| **conditional / await (zkpromise/zkawait)** | `cand-A §3` | `pipelinedSend` + `pending.rs`/`conditional.rs` (`ProofCondition`, `ConditionProof`) | **ENGINE LANDED in metatheory (2026-06-02)** — `Await.lean` now proves the **one-shot linear continuation typing** as a term-proved algebra: `OneShot:109` (no reusable-`k` projection, `:103`), `four_faces_unify:426` (zkpromise/discharge/intent/eventual unified), `runtime_guard_is_double_spend:223`. ⚠ its header "open-hole bodies" comment (`Await.lean:42`) is STALE. Still **not a kernel selector**; the **settled-call return projection** (next row) remains MISSING |
| **return projection** (typed `Obs`-delta the callee commits, caller awaits) | `cand-A §2.2/§3` | NONE | **STILL MISSING — the genuinely-open #4 residual.** The `Await` one-shot covers the *caller-resumes-once* face; the *callee commits a typed `Obs`-delta the caller awaits* (the "second observation", bidirectional turn) is unbuilt. Task #82 (`W3-I` zkpromise/zkawait + await unification) is `in_progress` |
| **sealer/unsealer + three-vat handoff** | `cand-A §3`, Miller | `CreateSealPair` (28), `Seal` (10), `Unseal` (11) | **COVERED** (shape S11) — but overloaded with field-seal at selector 10 |
| **multi-asset / Resource camera** | `REORIENT §2`, `Resource.lean` | ✅ **DONE (Lean executable layer)** — `FullActionA` arms carry `(asset : AssetId)` (`Exec/TurnExecutorFull.lean:1928`); the per-asset ledger + conservation vector is REAL (`MultiAsset.lean:38,86,130`; `FullForest.lean:224`). `Resource.lean` is the Iris-**camera** conceptual tier (`Resource.lean:22`). (Rust `bal` is still a scalar `u64` — the Lean kernel is now *ahead* of Rust here, which is the point of the swap.) | **WAS the #1 soundness gap; now REAL on the executable kernel.** Residual = wire/breadth (task #129) |
| **I-confluence / merge (BEC)** | `REORIENT §2`, `cand-A §6` | NONE (merge is a fork-resolution, above the ISA) | **IS-A-RUNTIME-THEOREM** / finality-layer — merge = CRDT join for lattice state, provable-fail for linear (`cand-A §6`) |

### Ranked MISSING primitives (genuinely CORE, not deferrable)

> ⚑ **Drift-repair note (2026-06-02):** items **#1 (multi-asset) and the *engine* half of #4 (one-shot
> await)** are no longer missing — they LANDED in the live Lean (see §0.5). The list below is kept as the
> historical analysis with each item's *current* status stamped inline.

1. **Per-asset-class balance (multi-asset C1/C2).** ✅ **DONE — REAL, not missing (2026-06-02).** The
   single biggest soundness gap *was* this; it is now the executable kernel's primary shape.
   `cand-A §1.3`'s per-class `CONSERVATION_VECTOR` is realized as `maTotal k a` over a
   `MACellId → AssetId → ℤ` ledger (`MultiAsset.lean:38,47,86`); every money-moving `FullActionA` arm
   carries `(asset : AssetId)` (`Exec/TurnExecutorFull.lean:1928`); per-asset conservation is term-proved
   + `#assert_axioms`-pinned at both turn level (`maExec_conserves_per_asset`, `MultiAsset.lean:130`) and
   forest level (`execFullForestA_conserves_per_asset`, `FullForest.lean:224`/:421). The "must be CORE
   before the kernel replaces Rust" bar is **met on the executable layer** (task #129 residual = breadth/
   wiring, not the keystone).
2. **The cross-cell BoundDelta half-edge (CG-5).** 🟡 **LAW landed; kernel-arm still open.** The N-ary
   cross-cell Σ=0 binding is PROVED as `crossForest_conserves` (`Exec/CrossCellForest.lean:241`,
   "binding LOAD-BEARING", `#assert_axioms`-pinned), with `crossForest_no_amplify:217` and
   `crossForest_attests:278`. So the *irreducible cross-side conservation measure* (`study-mina-relink §1`;
   the `νF₁⊗νF₂`-is-not-final intuition, now correctly framed in the canon as **sound joint-turns form a
   PROPER SUBOBJECT of the product**, `Hyperedge.lean` `hyper_binding_is_proper:164` / `Core.lean`
   `conservation_step:176`) is term-proved at the FOREST level. What remains OPEN is a **first-class
   `FullActionA` half-edge *arm*** carrying a peer-existence witness — today cross-target subtrees are a
   routing overlay (`FullForest.lean:328`), not an executable action. (Closely tied to forest-delegation
   #138.)
3. **Vat-boundary ρ_in/ρ_out as typed effects.** 🟡 **Boundary LAW landed; typed effect still open.** The
   coinductive membrane soundness obligation is discharged — `Boundary.lean` `boundary_respecting_sound:244`
   (REAL; its "Stated open" docstring `:243` is STALE). But ρ_out (serialize-held-slot→key,
   attenuation-only) and ρ_in (verify-key→mint-slot) are **still not selectors/arms**: today the crossing is
   split across `exportSturdyRefA`/`enlivenRefA` (swiss) + `Authorization::Token` (biscuit carrier) with no
   unifying typed effect. This is what makes it cross-vat at all — **genuinely OPEN as a primitive.**
4. **Return projection / settled-call await.** 🟡 **One-shot continuation landed; the *return face* open.**
   `Await.lean` proves the one-shot linear continuation algebra (`OneShot:109`, `four_faces_unify:426`,
   `commit_resumes_once:312`) — the caller-resumes-once half of `cand-A §2.2/§3`, term-proved in the verify
   metatheory. The *callee-commits-a-typed-`Obs`-delta-the-caller-awaits* second-observation face
   (bidirectional turn / zkRPC product) is **still unbuilt** (task #82 `in_progress`).
5. **Fork (span/pushout) as a primitive.** 🔴 **Still OPEN (unchanged).** `cand-A §6`: fork is the one
   structural hole; time-travel and merge derive from it. `spawnA` is child-creation, not self-fork.
6. *(Deferrable, unchanged)* **Beacon/VRF randomness** — only if app-level lotteries enter the core; leader
   election is a finality concern, not an effect.
7. *(Deferrable, unchanged)* **On-chain checkpoint naming** — only if checkpoints must be attested on-chain
   rather than being a pure runtime theorem.

### Layer recommendation for the gaps (2026-06-02 revised)

- **Already in CORE (done):** ✅ multi-asset C1/C2 (#1) — the executable `FullActionA` is per-asset and
  conservation is proved (§0.5).
- **Into CORE next (the genuinely-open kernel-arm work):** the cross-cell BoundDelta **arm** (#2; the *law*
  is done, the executable half-edge action is not), ρ_in/ρ_out typed effects (#3), forest-delegation
  handoff (#138 — route the discarded edge onto `recKDelegateAtten`; today `FullForest.lean:124` drops it).
- **New CORE coalgebra ops, after the living cell lands:** return projection (#4 — the *return face*; the
  one-shot face is already proved in `Await.lean`), fork (#5).
- **Runtime theorems (no effect):** checkpoint/restore/replay/time-travel/merge — per `cand-A §5/§6`
  these are *consequences* of codata + retained log + rollback-handler turn, NOT primitives. The
  ChainLink/`ObsAdvance` half is the executable substrate they ride on (`Exec/TurnExecutorFull.lean:472,484`
  — `ChainLink` PROVED: a committed action extends the newest-first chain by *exactly* its receipt, so a
  replayed action that re-appends the same receipt is detectable, `:513` — the anti-replay seed). Adding them as
  effects would be a category error (the FAITHFULNESS-AUDIT's "moved-complexity" trap in reverse).
- **DSL/portal:** queue semantics, refusal non-action proof, committed-escrow crypto.

---

## 4. Tradeoffs (honest)

- **TCB / constraint-surface payoff.** 54 selectors → ~18–20. The dominant win is collapsing the
  ≈24 passthrough-with-bind selectors (§S6) into **C7 `Meta.bind(domain_tag, hash)`** — they already
  share one row algebra in `air.rs` (state passthrough + fold-hash-into-effects_hash + nonce tick),
  distinguished only by a domain constant. Fewer selectors = fewer per-selector AIR constraint
  blocks to audit = smaller verifier. The Lean 52-tag exhaustive coloring (`EffectKind`,
  `CatalogInstances.lean:285`; `every_effect_classified`, `CatalogEffects.lean:201`) shrinks
  to ~13 shape-tags + a `domain_tag` enum. (The *executable* `FullActionA` already collapses below 54 —
  46 arms — by folding `queueAtomicTx`/`queuePipelineStep` and aliasing `createObligationA`→`createEscrowA`.)
- **In-circuit atomicity is the hard constraint — these MUST stay primitive.** The EffectVmAir bakes
  54 selectors into ONE trace partly so a whole turn's effects prove atomically (one proof, one
  `OLD_COMMIT→NEW_COMMIT`). Any shape whose *row algebra* genuinely differs MUST keep a selector:
  C1 (balance limbs + underflow), C2 (disclosed flag), C4 (caproot advance + attenuation), C5
  (recursive inner-effect gating), C9/C10 (side-table), C11/C12 (nullifier set), C8 (lifecycle FSM).
  You cannot demote these to "a DSL rule" without re-introducing a second proof and losing one-trace
  atomicity. **The reduction is in the NAMING (selectors that are the same row), not in the genuine
  shapes.**
- **The moved-complexity risk (the central danger of reduction).** Demoting queue/refusal/committed-
  escrow to DSL only helps if the DSL (CellProgram + Custom witnessed-predicate) is *itself verified*.
  Today `CellProgram` is the flat-and-dead fragment (`REORIENT §4`); pushing the queue automaton into
  it without proving the program-obligation just relocates the unverified surface. **Recommendation:
  demote to DSL only behind a verified `Custom` obligation; until then keep the macro expanding to
  CORE rows in the executor (DERIVED-MACRO), which preserves in-circuit atomicity with zero new
  selectors.** DERIVED-MACRO is the safe default; DSL-USERSPACE is the goal once the program law is
  proved.
- **Mergers that would LOSE a real distinction (do NOT merge these).**
  - `Burn` (C2 annihilative) vs `Transfer { direction:1 }` (C1): the `was_burn` disclosure is bound
    into receipt_hash (`effect.rs:438`); merging would let an executor strip the supply-reduction
    disclosure. Keep distinct.
  - `Seal` field-mask (10) vs `CellSeal` lifecycle (49) vs `Seal` brand-box (11): three genuinely
    different operations sharing a name. The reduction here is **renaming for distinctness**, not
    merging.
  - `Introduce` vs `GrantCapability`: same C4 shape, but Introduce's attenuation+consent+expiry guard
    (`apply.rs:2829`) is a real authority distinction — keep it a *guarded macro*, do not silently
    fold its guards away (the FAITHFULNESS-AUDIT notes consent+expiry are *unmodeled* in Lean; the
    fix is to model them, not drop them).
  - `NoteSpend`/`NoteCreate` vs escrow S2: both "conservative," but the conserved domain differs
    (nullifier-set+note-tree vs cell-ledger+side-table). Merging would conflate two conservation
    laws.
- **Additions that are genuinely CORE vs deferrable (2026-06-02).** Multi-asset (#1) is **DONE and
  REAL** on the executable kernel (it *is* now a multi-asset capability OS at the Lean layer). BoundDelta
  (#2) and ρ_in/ρ_out (#3) have their **soundness laws proved** (`crossForest_conserves`,
  `boundary_respecting_sound`) but their **executable kernel arms/effects** are the open CORE work.
  Return projection (#4) is half-done — the one-shot `Await` algebra is proved (`Await.lean:426`); the
  *return face* and fork (#5) are CORE-but-after-the-living-cell-lands. Beacon/VRF (#6) and on-chain
  checkpoint (#7) are deferrable. Proof-carrying-forest is NOT an effect (it is the JointTurn/finality
  aggregation layer — `Exec/ProofForest.lean`) — adding it to the ISA would be a layer violation.

---

## 5. RECOMMENDATION — the right orthogonal basis

**The basis is ~13 CORE operations (11 shapes) + 5 new boundary/coalgebra primitives, with ~36
current effects demoted to DERIVED-MACRO or DSL-USERSPACE.** Neither the 6-shape over-shrink (which
loses the genuine distinctness of side-table vs nullifier vs cap-graph vs lifecycle) nor the 54-name
status quo (which is ~24 passthrough rows wearing different domain constants).

### The proposed ISA

**CORE (selectors the circuit MUST bake for one-trace atomicity):**
`NoOp` · `C1 Balance.move` (per-asset signed half-edge) · `C2 Supply.adjust` (disclosed ±) ·
`C3 Cell.create` · `C4 CapGraph.edge{add,remove,narrow}` · `C5 Cap.exercise` (recursive eval map) ·
`C6 Field.write` · `C7 Meta.bind(domain_tag,hash)` (subsumes the ~24 passthrough effects) ·
`C8 Lifecycle.transition(phase)` · `C9 SideTable.lock` · `C10 SideTable.settle(predicate)` ·
`C11 NoteTree.insert` · `C12 Nullifier.spend` · `C13 Nonce.tick` · `C11′ Sealer.brand{create,seal,unseal}`.

**NEW CORE (architecture-demanded, ranked) — 2026-06-02 status stamped:**
✅ `Asset` parameterization on C1/C2 (#1) — **DONE** (`FullActionA` per-asset, conservation proved, §0.5) ·
🟡 `BoundDelta.halfEdge(peer,δ,existence-witness)` (#2) — **the Σ=0 LAW is proved** (`crossForest_conserves`,
`Exec/CrossCellForest.lean:241`); the executable *arm* with a peer-existence witness is the open half ·
🔴 `Boundary.exportKey` / `Boundary.importKey` ρ_out/ρ_in (#3) — **the membrane LAW is proved**
(`Boundary.lean:244`); the typed *effect* is open · 🟡 `Return.project(Obs-delta)` + `Await.settle` (#4) —
**the one-shot `Await` algebra is proved** (`Await.lean:426`); the *return face* is open ·
🔴 `Fork.span` (#5) — open.

**DERIVED-MACRO (executor expands to CORE; no selector):** Introduce, CreateCellFromFactory, Spawn,
Queue{Allocate,Resize,AtomicTx,PipelineStep}, all escrow/obligation release/refund/fulfill/slash,
Bridge{Mint,Lock,Finalize,Cancel}, ValidateHandoff, EmitEvent, SetPermissions, SetVerificationKey,
RefreshDelegation, PipelinedSend, BridgeCancel, the CapTP swiss family (Export/Enliven/Drop folded
into C4 + counters or the new ρ ops).

**DSL-USERSPACE (verified CellProgram rule / Custom predicate):** queue FIFO semantics, Refusal
non-action proof, committed-escrow Pedersen/range-proof crypto.

**RUNTIME-THEOREM (no effect at all):** checkpoint, restore, replay, time-travel, merge,
revocable-forwarder lossiness — per `cand-A §5/§6/§8`.

### Phased path

1. **Phase R (reduction, low-risk, do first).** Collapse the §S6 passthrough family into **C7
   `Meta.bind(domain_tag,hash)`** — one selector, a `domain_tag` enum param. This is pure
   constraint-surface reduction with zero semantic change (the rows are already algebraically
   identical in `air.rs:909–1000, 2224–2400`). Re-tag the Lean `CatalogEffects` coloring to shapes.
   *Payoff: ≈24 selectors → 1, biggest TCB cut, no soundness risk.*
2. **Phase R2.** Fold `Introduce`→C4-guarded, `Spawn`/`Factory`→C3-param, `Bridge*`/escrow-settle→
   C9/C10/C2-with-portal as DERIVED-MACRO in the trace generator (no new selectors). Model the
   consent+expiry guards the FAITHFULNESS-AUDIT found unmodeled.
3. **Phase E1 (the soundness-critical additions).** ✅ **Asset-class half DONE** — C1/C2 are
   per-asset on the executable kernel and the `CONSERVATION_VECTOR` is proved (`MultiAsset.lean:130`,
   `FullForest.lean:224`). 🟡 The cross-cell **BoundDelta half-edge** (CG-5) has its **Σ=0 law proved**
   (`crossForest_conserves`, `Exec/CrossCellForest.lean:241`); the remaining E1 work is the
   executable *arm* + threading the forest-delegation edge that `execFullChildrenA` currently discards
   (`FullForest.lean:124`, task #138) so delegation has teeth on execution, not just on edge-data.
4. **Phase E2 (the membrane).** Add `Boundary.exportKey`/`importKey` (ρ_out/ρ_in) unifying the CapTP
   swiss family and the `Authorization::Token` carrier into typed, named-lossy boundary effects. The
   coinductive *boundary law* they must satisfy is already proved (`Boundary.lean:244`) — E2 is the
   *typed effect surface* on top of it, still OPEN.
5. **Phase E3 (the coalgebra faces, after the living cell lands per REORIENT §5).** 🟡 The one-shot
   `Await` algebra (`Await.lean:426`, `four_faces_unify`) is **already proved** — E3 adds the
   `Return.project` *return face* (the second observation / zkRPC, task #82) and `Fork.span`; derive
   checkpoint/restore/replay/time-travel/merge as **theorems**, not effects (the ChainLink anti-replay
   substrate is proved, `Exec/TurnExecutorFull.lean:484,513`).
6. **Phase D (move-to-DSL, last, behind a verified program law).** Demote queue semantics, refusal
   proof, and committed-escrow crypto to verified CellProgram/Custom obligations — only after the
   `CellProgram` law is proved (else it is moved-complexity, not reduction).

The net is a kernel ISA that is **smaller in its constraint surface** (the 24-way passthrough
collapse + the macro demotions) yet **larger in what it can express** (multi-asset, cross-vat
half-edges, the membrane, the coalgebra return/fork faces) — the right orthogonal basis for a
verified capability OS rather than a verified ledger.

**Where we actually are (2026-06-02).** The §A CORE is no longer a proposal: the executable
`FullActionA` (46 arms, `Exec/TurnExecutorFull.lean:1928`) *is* the per-asset money/lifecycle/authority/
note basis, term-proved and `#assert_axioms`-pinned. The §B expansion has flipped from "all missing" to
"the laws landed, the kernel arms are next": multi-asset DONE (#1); the Σ=0 cross-cell law
(`crossForest_conserves`), the membrane law (`boundary_respecting_sound`), and the one-shot await algebra
(`four_faces_unify`) all PROVED in the metatheory. The genuinely-open frontier is the small, named set:
the **forest-delegation handoff** (#138 — `execFullChildrenA` discards the edge, `FullForest.lean:124`),
the **BoundDelta executable arm** (#2), **ρ_in/ρ_out as typed effects** (#3), the **return face** (#4), and
**fork** (#5). The *reduction* side (the §S6→C7 passthrough collapse) is still entirely future work on the
Rust circuit selectors.

---

*A closing couplet, since the egg is still warm:*
*fifty-four names, but the shapes are thirteen — / a basis is found where the rows agree;*
*the asset arrived, and the forest conserves — / now the membrane, the half-edge, the handoff it serves.*
🐉🥚
