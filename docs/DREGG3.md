# DREGG3 — the kernel, redesigned

**Status:** design proposal (2026-06-09). Says what the kernel SHOULD BE. Not a
changelog. Written from a whole-tree read: the 52-variant `Effect` enum, the
19-field `RecordKernelState`, the 10-variant `Authorization`, the 37-variant
`StateConstraint`, the five-stratum proof tower, the circuit-family census
(~11.5K live of 112K), and the token-lineage crates (macaroon/token/
discharge-gateway). Companion: `docs-old/STORAGE-AS-CELL-PROGRAMS.md` (the
May 24 thesis this doc generalizes), `metatheory/Dregg2/Claims.lean` (the
proof ledger this doc's assurance case restructures).

---

## §0. The essence (what dregg has always been)

Strip every generation of accretion and one sentence survives, visible from
the macaroon beginning to the Argus end:

> **A turn is the exercise of an attenuable, proof-carrying token over owned
> state, leaving a verifiable receipt.**

Four primitive ideas, each the descendant of the humble origin:

1. **The token** (macaroon → biscuit → capability): bearer authority that can
   only ever *narrow* — caveats compose by conjunction, attenuation is
   `granted ⊑ held`, third parties discharge what they're asked to. The
   biscuit thread runs deeper than nostalgia: biscuit's *Datalog
   authorization* is literally the ancestry of `dsl/derivation.rs` — the
   derivation circuit proves "this fact chain derives Allow" — so **the token
   IS the proof system's oldest circuit**. Dregg's capability is a biscuit
   whose caveat language is `Pred` and whose verification is a STARK.

2. **The cell**: owned, guarded state. Every cell has a responsible operator
   (sovereign owner, host, or federation) — *nothing is ownerless*. The
   cell's `program` is the same caveat language turned inward: caveats
   attenuate what a token may do; programs constrain what a cell may become.
   One algebra, two polarities.

3. **The turn**: the unit of execution and the unit of proof. Authorization ∘
   guarded body ∘ receipt. Sequencing, parallel (joint) composition, typed
   holes (intents) await their counit (fulfillment). `{P} e {Q}` — the
   transformer algebra.

4. **The receipt (Q)**: the committed postcondition. Everything downstream is
   Q and its projections — the witness proves Q, the verifier consumes Q, the
   privacy dial projects Q, aggregation folds Q, the light client trusts only
   a chain of Q.

Diamond dregg2 is not more machinery than this. It is *exactly* this, with
nothing else, verified end to end.

---

## §1. The harsh critique (twelve faults, each with its disease)

The pieces are individually strong — the hygiene war was won (0 sorry, 238
axiom pins, real anti-ghost teeth). The faults are **ontological**: model
collaborators only ever *added*, and nothing had the authority to subtract.

| # | Fault | Evidence | Disease |
|---|-------|----------|---------|
| 1 | **Verb accretion.** 52 kernel effects; queues×6, escrows×6, swiss×4, bridge×4, obligations×3 are protocol verbs. | `turn/src/action.rs:789` | Every app pattern became a kernel verb instead of a cell-program composition. The May 24 doc diagnosed this and was never executed. |
| 2 | **Ownerless side-tables.** `RecordKernelState` carries `escrows/queues/swiss/sealedBoxes/factories` as flat global lists — objects summoned from nowhere, no responsible cell. | `RecordKernel.lean:475` (19 fields) | Modeling convenience ossified into ontology. The cell-keyed fields (`bal`, `lifecycle`, `slotCaveats`) show the right shape was known. |
| 3 | **Authority vocabulary fragmentation.** TEN `Authorization` variants (incl. `Unchecked`!) × `CapabilityCaveat` × 37 `StateConstraint`s × `Preconditions` × macaroon caveats × biscuit Datalog × breadstuff — at least six overlapping predicate vocabularies. | `action.rs:210`; `cell/src/program.rs`; `macaroon/`; `token/` | Each auth need grew its own enum instead of one guard algebra with atoms. (The Lean side already proved them isomorphic: `Pred ≅ Caveat ≅ Spec.Guard`.) |
| 4 | **Commitment pluralism.** BLAKE3 cell commit + Poseidon2 circuit commit + receipt-hash domains + (until yesterday) an XOR-fold cap root — cross-*bound* after the fact by the CommitmentCrossBind crown instead of being *one scheme*. | `cell/src/commitment.rs`; `CommitmentCrossBind.lean` | Designed per-component, welded later. The crown is heroic proof-work that a single scheme makes unnecessary. |
| 5 | **Conservation modulo-burn.** The fee split (50/30/20 proposer/treasury/burn) is hardwired into the turn epilogue, so the conservation law is `Σδ = −burn`, not `Σδ = 0`. | `Argus/Turn.lean` | Economic policy leaked into the kernel invariant. Meanwhile `Action.balance_change` already implements the exact-`Σδ=0` Mina-excess discipline — two value laws coexist. |
| 6 | **Session layer in the kernel.** ExportSturdyRef/EnlivenRef/DropRef/ValidateHandoff — CapTP *transport* concerns — are protocol verbs with circuit descriptors. | `action.rs` effects 14-17 | Layer confusion: vat-to-vat session machinery promoted to consensus-visible semantics. |
| 7 | **Interop in the kernel.** Bridge×4 as kernel verbs; plus a dormant SP1/nova `chain/` workspace as a *fourth* proving stack. | effects 37-40; `chain/` (untouched since May 26) | Foreign-chain trust models belong in bridge *cells* (programs demanding foreign-finality witnesses), not in every node's verb set. |
| 8 | **Privacy as special-cased verbs** (NoteSpend/NoteCreate with bespoke universe-conventions) instead of a single shielded-pool boundary. | effects 4-5; the noteCreate divergence saga | The pool boundary (shield/unshield + nullifiers) is the only kernel-level privacy primitive needed; the rest is Q-projection (already built: the Disclose dial). |
| 9 | **Asset namespace ≠ cell namespace.** `AssetId` is its own space; mint/burn are bespoke verbs; issuers are nowhere. | `RecordKernel.lean` `bal : CellId → AssetId → ℤ` | A missed unification: an asset IS an issuer's promise — the issuer should be a cell. |
| 10 | **Executor multiplicity.** dregg1 Rust executor (4.7K-line apply.rs) + Lean `execFullA`/per-action handlers + legacy `recKExec` + Argus `interp` — four expressions of the semantics, kept consistent by proofs (good) that wouldn't need to exist (better). | census Q1 | The SWAP half-done; the proofs of agreement are scaffolding for a deletion that hasn't happened. |
| 11 | **The codec.** A bespoke JSON-ish wire with hand-proven per-field roundtrips (the FILL-J campaign — heroic, and recurring: every field-add re-opens it). | `Exec/CodecRoundtrip/` | Should be ONE schema-derived canonical encoding with a once-proven generic codec. |
| 12 | **The claims ledger is a journal, not an argument.** `Claims.lean` = 34 sections in *campaign order*, stale (no Argus). The end-to-end light-client theorem exists in parts; the assurance *case* was never assembled. | `Claims.lean` (Jun 6) | Proofs accreted faster than the argument that organizes them. |

---

## §2. The kernel, redesigned

### §2.1 The nouns (six)

```
Pred       — ONE guard algebra. atoms (the 37, curated) ⊕ all/any/not ⊕ witnessed(vk)
             ⊕ third-party(discharge). Used as: caveats (on capabilities),
             programs (on cells), preconditions (on turns), intent demands (on holes).
             Evaluated by the executor; compiled to circuit obligations
             (a witnessed guard and a circuit constraint are the same thing).

Cap        — the token. {target, rights: Finset Auth, caveats: Pred, expiry, epoch}.
             Bearer, attenuable (⊑ on every component), revocable (epoch),
             STORABLE (a cap is a value a cell may hold in a slot — this single
             feature absorbs seal-boxes, sturdyrefs, escrowed authority).
             Verified by the derivation circuit (the biscuit lineage).

Cell       — the owned-state unit. {operator, lifecycle, nonce,
             bal : Asset → ℤ, clist : sorted-Merkle of Cap, program : Pred,
             slots : Slot → Value (caps storable)}.
             EVERY object in the system is a cell or lives in one.

Asset      — an issuer cell's promise. AssetId := CellId of the issuer.
             The issuer's own balance may run negative (it carries −supply),
             so conservation is EXACT: ∀a. Σ_c bal(c,a) = 0, always.
             Mint = the issuer moving from its well (gated by its own program);
             burn = moving back. No mint/burn verbs. No modulo-burn law.

Turn       — auth ∘ body ∘ receipt. body ::= verb | seq | par | hole(Pred).
             Prologue (fee = ordinary moves to fee-pot cells; nonce tick) and
             epilogue are MADE OF the same verbs — no special-cased value flow.
             Multi-party composition via per-action commitment (already in
             Action.commitment_mode); cross-turn atomicity via conditional
             turns (proof-gated, timeout-aborted — keep, it's good).

Receipt(Q) — the committed postcondition: new roots + admission witness +
             event payload, under ONE commitment scheme. The witness proves Q;
             the dial projects Q; aggregation folds Q; the light client
             verifies only Q-chains.
```

### §2.2 The verbs (eight)

| Verb | Subsumes (of the 52) | Note |
|------|---------------------|------|
| `create` | CreateCell, CreateCellFromFactory, SpawnWithDelegation | Birth only via factory descriptor (a bare cell is the trivial factory). Spawn = create + grant. |
| `write` | SetField, SetPermissions, SetVerificationKey, EmitEvent, ReceiptArchive, + every storage-primitive op | Guarded delta to owned slots. Caps storable in slots. Events = receipt payload, not a verb. |
| `move` | Transfer, Burn, BridgeMint/Lock/Finalize/Cancel, Create/Release/Refund(Committed)Escrow, balance legs of everything | THE value verb, per-asset, Mina-excess discipline: per-action signed deltas, turn-level Σδ=0 *exactly* (ratifies `Action.balance_change`). Escrows/bridges = cells that hold value via move under programs. |
| `grant` | GrantCapability, AttenuateCapability, Introduce, RefreshDelegation, Seal/Unseal/CreateSealPair, ExportSturdyRef/EnlivenRef | Install attenuated cap (granted ⊑ held, in-circuit — the cap-reshape). Attenuate = grant-to-self. Sealed/sturdy = caps in slots + guarded grant-out. |
| `revoke` | RevokeCapability, RevokeDelegation, DropRef | Edge removal + epoch bump (the delegation_epoch semantics, kept). |
| `shield` / `unshield` | NoteCreate / NoteSpend | The one privacy boundary: transparent↔shielded pool, nullifier ledger, commitment ledger. Everything else privacy-wise is Q-projection (Disclose). |
| `lifecycle` | CellSeal, CellUnseal, CellDestroy, MakeSovereign | seal/unseal/destroy(+death-cert)/custody — kernel-known because frozen cells must reject writes and custody changes who attests. |
| *(none)* | ExerciseViaCapability, IncrementNonce, Refusal, PipelinedSend, QueueAtomicTx, QueuePipelineStep, ValidateHandoff, Noop, Custom | **Not verbs.** Exercise = *using* a cap as any verb's authorization. Nonce = turn prologue. Refusal = a turn outcome. Pipelining/batching = turn-composition structure (`eventual.rs` semantics, kept as composition). Handoff-validation = a `Pred` atom. |

Eight verbs. Everything else in the current 52 is a **cell-program pattern**
(factory descriptor + Pred constraints + these verbs), per the May 24 doc —
queues, inboxes, pubsub, blinded queues, relays, escrows, obligations,
auctions, namespaces, bridges.

### §2.3 The ones (the unifications)

- **ONE guard algebra** (`Pred`) — caveat = program = precondition = intent
  demand. The Authorization enum collapses: `Signature | Proof |
  cap-exercise | token-adapter(macaroon/biscuit edge formats)` — and
  `Unchecked` **dies**.
- **ONE commitment scheme** — sorted-Poseidon2 Merkle all the way down: slots
  tree, clist tree (the cap-reshape, done), balance tree, cell leaf, state
  root, receipt chain. BLAKE3 only at non-load-bearing edges. The
  CommitmentCrossBind crown becomes a *definition* instead of a theorem.
- **ONE value law** — Σδ = 0 per asset per turn, exact, no exceptions; fees
  are moves; supply lives at issuers.
- **ONE executor** — the verified Lean executor IS the executor (the SWAP
  finished); Rust survives as the *witness generator and prover host*
  (dreggrs), never as semantics.
- **ONE circuit** — the Lean-emitted descriptor for the 8-verb × guard-compiler
  statement, interpreted by `lean_descriptor_air` (the invariant, now reachable:
  8 verbs ≈ the 18 already-graduated descriptors minus the doomed 30).
- **ONE codec** — schema-derived canonical binary, generic roundtrip proven once.
- **ONE assurance case** — see §4.

### §2.4 The layers (what is NOT kernel)

```
userspace   cell programs: queues, escrows, obligations, auctions, namespaces,
            inboxes, pubsub, relays, registries, DEX/intent-settlement…
            (factories + Pred + the 8 verbs; the intent crate's solver/matcher
            machinery lives here, settling via ordinary turns)
session     CapTP: vats, sturdyref wire format, handoff certs, promise
            pipelining transport, store-and-forward (caps-in-slots + grants
            underneath; nothing consensus-visible)
interop     bridge cells (programs demanding foreign-finality witnesses);
            chain/ zkVM experiments stay out of the kernel
edge-auth   macaroon/biscuit token formats adapt INTO caps at the boundary
            (the `token` crate's trait, pointed inward)
kernel      §2.1–§2.3 only
```

---

## §3. What this does to the proof tower

The five-stratum tower (Spec→Inst→Witness→Emit→Argus) is *kept* — it's a good
architecture — but it is ×8 instead of ×52: roughly **227 per-effect files →
~40**, with the keystones (CommitmentCrossBind, Argus apex, RecursiveAggregation,
Boundary coinduction, the cap-reshape gates) carrying over nearly unchanged.
The guard compiler becomes the new load-bearing middle: ONE theorem family
"`Pred` evaluation ⟺ circuit obligation" replaces per-effect gate proofs for
everything that moved to userspace. App-level guarantees (escrow safety, queue
FIFO, auction soundness) become **userspace verification** — `Dregg2.Verify`
consuming Q against factory descriptors — which is where they always belonged:
apps get theorems without kernel surface.

## §4. The assurance case (replaces the Claims journal)

Five top-level claims, each a theorem DAG over the strata, with the assumption
floor explicit (Poseidon2 CR, ed25519, FRI soundness, GST liveness — and
nothing else):

- **A. Authority** — every state change was authorized by an unforgeable,
  never-amplified, fresh token chain. (derivation circuit + cap-reshape gates
  + epoch freshness)
- **B. Conservation** — ∀ asset: Σδ = 0, exactly, every turn. (the one value law)
- **C. Integrity** — receipts bind the entire post-state; tamper ⇒ reject.
  (the commitment scheme + anti-ghost teeth)
- **D. Freshness** — no replay, no double-spend, revocation is immediate-at-
  finality. (nonces, nullifiers, epochs, the bound verifier)
- **E. Unfoolability** — a light client verifying a Q-chain learns A–D hold
  for the whole history, against an arbitrarily malicious network. (Argus +
  RecursiveAggregation, composed)

`Claims.lean` becomes `AssuranceCase.lean`: five sections, each importing its
DAG, each `#assert_axioms`-pinned, organized by guarantee — never by date.

## §5. dregg2 → dregg3 (a reduction, not a rewrite)

Verdict: **dregg3 is dregg2 minus ~44 verbs plus 6 unifications.** The verified
core (cells, caps lattice, conservation spine, commitment crown, Argus, the
blocklace) IS already the dregg3 kernel — encrusted. Staged, each stage green:

1. **Cap crown** (in flight): openable clist + in-circuit non-amp + consumed-
   witness + authority binding. *(Phases A–B landed.)*
2. **Value unification**: ratify `balance_change` as THE mechanism; issuers
   as cells; exact conservation; fees as moves. (One VK/commitment rotation,
   shared with stage 1 — rotate once.)
3. **Storage-as-cell-programs**: execute the May 24 doc; delete queue/escrow/
   obligation/swiss/seal verbs as their factories land; `storage/` and
   `app-framework/` dissolve.
4. **Guard unification**: Pred everywhere; Authorization collapses;
   `Unchecked` dies; macaroon/biscuit become edge adapters.
5. **The cutover** (already mapped): descriptor prover = THE prover for the
   8-verb circuit; delete hand-AIRs + ~33K orphaned circuit LOC + the dormant
   stacks.
6. **The SWAP finishes**: Lean executor everywhere; apply.rs dies; dreggrs =
   witness-gen.
7. **AssuranceCase.lean** + the codec + docs consolidation.

Each stage is independently shippable and strictly subtractive after its
landing. No greenfield. The metatheory keeps its 238 pins throughout.

## §6. Decision points (ember)

1. **AssetId := issuer CellId** (exact conservation, issuer-carried supply) —
   the deepest semantic change. Yes/no shapes stage 2.
2. **Caps storable in slots** (absorbs seal/sturdyref machinery) — yes/no
   shapes stage 3-4.
3. **Fee economics as ordinary moves to pot-cells** (kills modulo-burn) —
   policy lives in the proposer/treasury pot programs, not the kernel.
4. **Intent layer placement** — solver/matcher as userspace settling via
   turns (recommended), or intents as a 9th kernel verb family?
5. **The 37 Pred atoms** — curate which survive as kernel atoms vs userspace
   `witnessed(vk)` customs.
6. **Naming**: execute as "dregg2 in shape" (this doc = the spine of the
   consolidation) or fork the identity to dregg3 (clean VK/commitment epoch,
   same tree)?
