# DREGG3-MARATHON — current tree → releasable dregg3 devnet, through the polis

**Status:** the campaign plan (2026-06-09, ember-approved "with prejudice").
Companion to `docs/DREGG3.md` (the substrate — what we're building) and
`metatheory/CONSTRUCTIVE-KNOWLEDGE.md` (the logic it realizes). This document
is the HOW and the ORDER. Waves are independently green; every load-bearing
elegance is probe-gated (DREGG3 §6); the flesh ships with the skeleton.

---

## §0. Definition of done — the releasable dregg3 devnet

A public devnet (plus the n=1 local story) where ALL of the following are
demonstrably true:

1. **The kernel** is the 8-verb substrate: Lean executor authoritative on
   every turn (no Rust-fallback effects remain — they died with their verbs);
   exact conservation (Σδ=0, issuer-cells); authority under the
   non-forgeability discipline with the cap-crown gates in-circuit.
2. **One of each**: one circuit (the Lean-descriptor prover IS the prover;
   hand-AIRs deleted), one VK epoch, one commitment scheme, one codec, one
   guard algebra (`Pred`; `Authorization::Unchecked` does not exist).
3. **Q is served**: every committed turn's receipt + proof retrievable; a
   light client verifies chains it never executed; aggregation folds them.
4. **The polis layer is live**: factories birth cells with theorem-carrying
   descriptors; ≥5 flagship apps run as verified factories (escrow, registry/
   namespace, bounty, auction, agent-mandate) each with a Gated contract +
   receipts-face; governance cells (a council, a constitution-as-program,
   a forward-certified amendment) operate on devnet.
5. **The gateway product works for a stranger**: `dregg-auth` issues/
   attenuates/verifies tokens with zero node dependency; the MCP gateway
   profile scopes a real agent; the cipherclerk explains any turn it signs.
6. **The assurance case is an artifact**: `AssuranceCase.lean` — five claims
   (Authority · Conservation · Integrity · Freshness · Unfoolability),
   organized by guarantee, assumption floor explicit, every pin green.
7. **The shipware drills pass** (DREGG3 §4): root rotation with chains
   intact; week-long partition + merge; live upgrade of executor, factory,
   constitution; the explain-rendering audit by a cold human reader.

## §1. The tracks

Four tracks run through the waves. Any wave may carry work from several.

- **K (kernel/circuit)** — the substrate reduction + the one-of-each.
- **M (metatheory)** — grow `Metatheory/*` into the generating doctrine;
  discharge dregg2 against it (per CONSTRUCTIVE-KNOWLEDGE.md §7).
- **P (polis/product)** — dregg-auth, cipherclerk, workbench, governance,
  apps, devnet ops.
- **A (assurance)** — the Verify toolkit's missing faces, AssuranceCase,
  the shipware drills, red-team.

## §2. The waves

### W0 — in flight now (probes + the crown's payoff)
- [K] **Cap-crown D**: the sdk authority binding onto the openable cap_root
  (the membership leg binds to `capability_root`, not whole-state old_commit).
  A+B+B2+C landed; D is the payoff. Includes the B2 residual designs:
  recipient-side sorted-INSERT (indexed-leaf tree) + executor installs
  genuinely-attenuated entries (close the runtime-laxity gap the circuit
  already enforces).
- [M] **S0 (R1 probe)**: the Fpu substrate probe — running. Its verdict
  shapes W1's exact formulation. My standing prediction (from the
  `stateStepGuarded` read): the gate's anatomy is
  `(global Pred guard) × (componentwise substance-disciplined update)` —
  if S0 reports that split, it's a PASS-with-structure, not a failure.
- [K] **R2 probe**: re-prove tri-domain conservation + noteSpend
  value-binding under issuer-supply BEFORE any ledger migration.
- [K] **R3 probe**: the ESCROW factory + its release-safety contract in the
  Verify toolkit BEFORE deleting escrow verbs.
- [A] **R7 design**: the stored-cap retrieval rule (epoch re-check at load,
  in-circuit) BEFORE caps-in-slots absorbs the seal/sturdy machinery.

**Gate W0→W1:** S0 verdict in; R2/R3 probes green (or fallbacks adopted);
cap-crown D landed.

### W1 — the substrate (one VK rotation, once)
- [K] **Value unification**: AssetId := issuer CellId; issuer-carried
  −supply; Σδ=0 exact; fees = ordinary moves to pot-cells; ratify
  `Action.balance_change` as THE mechanism; retire modulo-burn.
- [K] **The single rotation**: cap-crown layout + value unification + any
  remaining commitment-layout changes land as ONE VK + commitment-context
  epoch (succession drill #1: rotate with chains intact — this rotation IS
  the first shipware test).
- [M] **D1**: the dynamics layer into `Metatheory/*` — substances + the
  verb signature + the non-forgeability production law, candidate-
  independent, with `Dregg2` instantiating it. (Grown from S0's verdict +
  `ConstructiveKnowledge.lean` §3's `Confers`/`no_forge_step`.)
- [M] **▶ becomes real**: connect `StepCamera`'s step-indexing to
  `Boundary.Later` (retire the identity placeholder) — discharging the
  metatheory's own §2 (`knowledge_does_not_drift` over genuine guarded
  recursion).

### W2 — the great reduction
- [K] **Storage-as-cell-programs**, family by family, probe-first:
  escrow → queues/inbox/pubsub → swiss/sturdyref (needs R7) → obligations →
  seal-boxes (caps-in-slots) → bridges (bridge-issuer cells). Each family:
  factory + Pred constraints + Verify contract LAND before the kernel verbs
  DIE. `storage/` and `app-framework/` dissolve into factories + thin
  Action shims.
- [K] **Guard unification**: the 37 StateConstraint atoms curated into
  kernel-`Pred` atoms vs `witnessed(vk)` customs; `Authorization` collapses
  to {signature, proof, cap-exercise, token-adapter}; `Unchecked` dies;
  caveat = program = precondition = intent-demand, one evaluator.
- [K] **Verb deletion**: 52 → 8 as coverage lands; the per-effect proof
  strata (Spec/Inst/Witness/Emit/Argus ×52) shrink with each deletion —
  subtraction increases total verified surface (every dead verb's semantics
  re-lands as a verified factory with a contract it never had).
- [M] **D3**: completeness + minimality of the 8 verbs over the substance
  signature (the metatheorems that make the kernel's smallness defensible).

### W3 — one of each
- [K] **The cutover**: descriptor coverage completes over the 8-verb
  surface (the DEEPER-20 problem mostly dissolves — those descriptors die
  with their verbs); `lean_descriptor_air` becomes THE prover;
  `effect_vm/air.rs` + `effect_vm_p3_full_air.rs` + ~33K orphaned circuit
  LOC + dormant stacks (old IVC, presentation, predicate_program,
  effect_action_air, note_spending duplicates; `chain/` decision) deleted
  under verified-replacement gates. `EffectVmP3Proof` type ownership moves;
  the node fast-path gets its descriptor equivalent; recursion/aggregation
  re-target descriptor proofs (task #94).
- [K] **The SWAP finishes**: the Lean executor is THE executor on every
  surface (wasm + sdk-local included); `apply.rs` retires to
  witness-generation (dreggrs); the root-gap fallback list is empty.
- [K] **One codec**: schema-derived canonical encoding; the generic
  roundtrip proven once; the FILL-J hand-proof era ends.
- [M] **D2 (R9 probe)**: initiality of the IR over the doctrine — the
  Freyd/graded shape. If it lands: interp/compile/explain/merge as unique
  homomorphisms (N² agreement proofs retire). If it fails: keep pairwise
  agreement, document, move on.

### W4 — the polis layer
- [P] **`dregg-auth`** (the gateway): extract from token/macaroon/
  cipherclerk a standalone, offline-verifying, two-dependency library +
  CLI + middleware; the MCP gateway profile (per-tool attenuated caps,
  receipt logging); 60-second quickstart. The adoption-quotient commitment:
  no node, no wallet, no ontology at L1, forever.
- [P] **The cipherclerk elevated**: dials wired as literal Q-projections;
  the `explain` reading (R6 scope: proved-total deterministic rendering of
  the IR term) — the clerk that cannot lie about what a turn does.
- [P] **The workbench v0**: the Widget surface (trust badges from
  collectAxioms, CapabilityGraph, ConservationLedger, DreggForest,
  VerifiedTurn) becomes a served web UI over a sandbox polis (n=1);
  factory authoring with live proof badges; "why rejected?" returns the
  failing Pred leaf.
- [P] **Governance cells**: council/registry/constitution factories;
  constitutions as forward-certified programs; one real amendment executed
  on devnet (succession drill #2).
- [A] **The Verify toolkit's two missing faces** (study-confirmed gaps):
  the **factory-descriptor face** (contracts over birth constraints) and
  the **Q/receipt face** (light-client-grade app guarantees from receipt
  chains alone — D4's Q-functor made practical). The ~20 Gated apps
  upgrade; the 5 flagship apps ship with both faces.

### W5 — assurance + ship
- [A] **`AssuranceCase.lean`**: the five claims as theorem DAGs; Claims.lean
  retires to git history; the assumption floor (Poseidon2 permutation CR,
  BLAKE3 CR, ed25519, HMAC, AEAD, DLog, FRI, PostGSTProgress) stated once.
- [A] **The shipware drills** as devnet exercises: rotation, partition-week,
  live upgrades, the cold-reader explain audit, the n=1 closure run.
- [A] **Red-team pass** over the reduced surface (the old findings' classes,
  re-aimed at the new kernel).
- [P] **Devnet deploy**: AWS + local; proving on (`--prove-turns` default
  for the devnet profile); proofs served; the lightclient verifying from a
  cold start; onboarding (task #110) — a stranger does something real in
  minutes, via dregg-auth or the workbench.
- **Docs**: the constitution page; metatheory/README reflecting the
  metatheory-vs-verification split (§7's rename completed).

## §3. Discipline (how the marathon stays honest)

- **Probe-first** for every load-bearing elegance (the §6 register; R-gates
  named in each wave). A failed probe adopts its fallback the same day —
  no mourning, no rescue-by-vacuity.
- **Land-before-kill**: a factory + contract lands before its verbs die;
  a reading lands before its differential retires; verified-replacement
  gates on every deletion.
- **One rotation per epoch**: VK/commitment changes batch into named
  epochs (W1 has the big one); every rotation doubles as a succession drill.
- **The anchor stays green**: `lake build Dregg2.Circuit.Argus` (and its
  successors) + the cutover harness + the gauntlets, every landing.
- **The constellation is jazz, not load**: svenvs/mediateor/graphplay
  correspondences live in `Metatheory/*` as their own modules (EpistemicDial
  is the template), never as kernel dependencies.
- **Agents commit early, report after** (the session-cap lesson); the main
  loop verifies my-eyes before push; WIP is never discarded.

## §4. Sequencing constraints (the honest dependency spine)

```
S0 ──→ D1 ──→ D2(R9) ──→ explain/merge readings
cap-D ─┐
R2 ────┼─→ W1 rotation ──→ W2 families (escrow R3-first) ──→ verb deletion
R7 ────┘                          │
                                  ├─→ W3 cutover (descriptor coverage = 8 verbs)
                                  └─→ W3 SWAP-finish (root-gaps die with verbs)
Verify Q-face + factory-face ──→ W4 flagship apps ──→ W5 drills
dregg-auth: independent — can start ANY time (only reads token/macaroon/cipherclerk)
workbench v0: after explain (W4) but scaffolding can start on Widget now
```

The critical path is K: probes → rotation → families → cutover/SWAP. M and
P run beside it; `dregg-auth` is deliberately path-independent (the wedge
must never wait on the kernel).
