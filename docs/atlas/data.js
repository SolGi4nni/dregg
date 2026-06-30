// dregg architecture atlas — grounded data model.
// Status vocabulary (the whole point — distinguish truth from staging from design):
//   PROVEN      — Lean theorem, #assert_axioms-clean (only standard crypto carriers open)
//   DEPLOYED    — live in the deployed VK / runtime default; a light client witnesses it today
//   REAL        — shipped, working code + tests; enforced by the running system
//   EXEC        — EXECUTOR-WITNESSED: enforced by the Rust executor today, but its circuit/VK
//                 shadow (light-client witness) is named + STAGED, not yet flipped
//   STAGED      — built + proven + emitted, but NOT flipped into the deployed VK / default
//   SCAFFOLD    — green build, honest scaffold; the real path errors / is mock until a named rung
//   DESIGN      — designed, not shipped (blueprint / frontier / one-wiring-away)
//
// File refs: paths are relative to the breadstuffs repo root.
// Serve from the repo root (python3 -m http.server) to make breadstuffs refs clickable.

const STATUS = {
  PROVEN:   { label: "PROVEN",   cls: "s-proven",   blurb: "Lean theorem, axiom-clean (only standard crypto carriers remain open)" },
  DEPLOYED: { label: "DEPLOYED", cls: "s-deployed", blurb: "Live in the deployed VK / runtime default — a light client witnesses it today" },
  REAL:     { label: "REAL",     cls: "s-real",     blurb: "Shipped, working code + tests; enforced by the running system" },
  EXEC:     { label: "EXECUTOR-WITNESSED", cls: "s-exec", blurb: "Enforced by the Rust executor today; its circuit/VK (light-client) shadow is STAGED" },
  STAGED:   { label: "STAGED",   cls: "s-staged",   blurb: "Built, proven, emitted — but NOT flipped into the deployed VK / default" },
  SCAFFOLD: { label: "GREEN-SCAFFOLD", cls: "s-scaffold", blurb: "Green build / honest scaffold; the real path is mock or errors until a named rung" },
  DESIGN:   { label: "DESIGNED", cls: "s-design",   blurb: "Designed, not shipped — blueprint / frontier / one-wiring-away" },
};

// f(path, line, label?) — a breadstuffs file ref.
const f = (path, line, label) => ({ path, line, label, repo: "breadstuffs" });

const ATLAS = {
  layers: [
    {
      id: "substrate",
      name: "dregg substrate",
      kind: "OPEN · AGPL · verified",
      tagline: "A light client holding one root knows every transition in the whole history was authorized, conservative, fresh, and correctly committed — re-executing nothing.",
      sections: ["cells", "turns", "predicates", "umem", "dregg3", "circuit", "lean", "capacities"],
    },
    {
      id: "economy",
      name: "service economy",
      kind: "OPEN · the rail",
      tagline: "Value, services, leases, and metered tool-access — every charge desugars to one conserving Transfer (Σδ=0). This is the rail an operator rents over.",
      sections: ["economy"],
    },
    {
      id: "deos",
      name: "deos pillars",
      kind: "OPEN · the desktop",
      tagline: "A reflective workspace where every action is a verifiable turn and adds zero new trust: affordances are cap-gated turn templates, history is the receipt chain, sharing is a cap-confined membrane.",
      sections: ["cockpit", "bridges", "apps"],
    },
    {
      id: "welds",
      name: "Gentian VK welds",
      kind: "honesty-critical — STAGED vs DEPLOYED",
      tagline: "Binding each capacity invariant into the EffectVM so a LIGHT CLIENT, not just a re-executing validator, witnesses it. Coverage is DEPLOYED; satisfaction is STAGED — the FLIP is not taken.",
      sections: ["vkepoch"],
    },
  ],

  sections: [
    // ───────────────────────────── SUBSTRATE ─────────────────────────────
    {
      id: "cells", layer: "substrate", title: "Cells & the four substances",
      what: "The cell is the unit of sovereign, capability-secure state and identity. Each cell holds four orthogonal substances obeying distinct disciplines: value (per-asset signed balances, Σδ=0 exact), state (16 guarded fields + maps + heaps, a monotone nonce), authority (a capability tree / c-list), and evidence (append-only nullifier / commitment ledgers). A card, a document, an agent, a room, a service, you — each is a cell, folded into one canonical commitment.",
      components: [
        { name: "Cell", status: "REAL", what: "The bundle: identity, public_key, token_id, state, permissions, verification_key, delegate, capabilities, program, mode, lifecycle.",
          files: [f("cell/src/cell.rs", 249), f("docs/reference/cells.md")] },
        { name: "CellState — the four substances", status: "REAL", what: "16 user fields + monotone nonce; value = signed i64 balance (issuer well carries −supply); committed via sorted-Poseidon2 roots (fields/heap/system).",
          files: [f("cell/src/state.rs", 101), f("cell/src/state.rs", 127, "balance / well")] },
        { name: "Authority — CapabilitySet + Permissions", status: "REAL", what: "The c-list (attenuation lattice, tombstone revoke) + a permission lattice over 8 auth-required fields. You hold a cap iff you can PRODUCE its witness.",
          files: [f("cell/src/capability.rs", 202), f("cell/src/permissions.rs")] },
        { name: "Evidence — NullifierSet", status: "REAL", what: "Append-only Merkle nullifier set + note commitments — monotone, the anti-replay substance.",
          files: [f("cell/src/nullifier_set.rs")] },
        { name: "AssetId := issuer cell (Σδ=0)", status: "REAL", what: "W1 value unification: the asset IS its issuer cell; the issuer carries −supply, so every asset sums to exactly 0 across all cells, always.",
          files: [f("types/src/lib.rs", 701, "CellId derivation"), f("cell/src/commitment.rs", 204, "canonical commitment")] },
        { name: "CellLifecycle", status: "REAL", what: "Live / Sealed / Migrated / Destroyed / Archived transitions; mode = Hosted (default) vs Sovereign.",
          files: [f("cell/src/lifecycle.rs", 37)] },
      ],
    },
    {
      id: "turns", layer: "substrate", title: "Turns & the Effect vocabulary",
      what: "A turn is one authorized inference step: a forest of actions executed as an atomic transaction (all-or-nothing, journalled with rollback), each action gated by the kernel before it commits, chained via a receipt that binds the whole post-state (tampering an illegitimately-written field makes the turn unprovable — the anti-ghost property). The deployed Effect enum carries ~32 variants; the DREGG3 design abstracts these to 8 structural verbs.",
      components: [
        { name: "Turn → CallForest → Action → Effect", status: "REAL", what: "Turn{agent,nonce,call_forest,fee,valid_until,previous_receipt_hash,…} → Vec<CallTree> (Merkle forest_hash) → Action{target,method,args,authorization,preconditions,effects,…}.",
          files: [f("turn/src/turn.rs", 258), f("turn/src/forest.rs", 30), f("turn/src/action.rs", 73), f("docs/reference/turns.md")] },
        { name: "The Effect vocabulary (~32 variants)", status: "REAL", what: "SetField · Transfer · IncrementNonce · EmitEvent · Grant/Revoke/Attenuate/ExerciseViaCapability · CreateCell(/FromFactory) · SetPermissions/VerificationKey/Program · CellSeal/Unseal/Destroy · MakeSovereign · NoteSpend/NoteCreate · BridgeMint · Burn · Mint · Spawn/Refresh/RevokeDelegation · Introduce · PipelinedSend · Promise · Notify · React · Refusal.",
          files: [f("turn/src/action.rs", 962, "Effect enum")] },
        { name: "LinearityClass — the conservation discipline", status: "PROVEN", what: "Every effect is classed: Conservative (pair-sum-zero) · Monotonic · Terminal · Generative · Annihilative (Burn, with receipt disclosure) · Neutral. Σδ=0 is policed per-effect.",
          files: [f("turn/src/action.rs", 855), f("metatheory/Dregg2/Spec/Conservation.lean", 78)] },
        { name: "Executor — atomic apply + journal rollback", status: "REAL", what: "execute(turn,ledger) → Committed/Rejected/Expired/Pending. Admission (nonce/balance/receipt-chain), fee phase (never rolled back), STARK proof fast-path, depth-first forest walk with per-action auth, LedgerJournal undo on failure.",
          files: [f("turn/src/executor/execute.rs", 152)] },
        { name: "Verified Lean shadow (strict veto)", status: "PROVEN", what: "The Lean executor (execFullForestG) is the oracle: if Lean rejects and Rust commits, the ledger is restored and the result is Lean's Rejected. Conservation / no-amplification / unauthorized-fails are theorems.",
          files: [f("turn/src/shadow.rs", 111), f("turn/src/executor/execute.rs", 168)] },
        { name: "Receipt — the verifiable witness", status: "REAL", what: "turn_hash, forest_hash, pre/post state hash, effects_hash, consumed-capability Merkle proofs, disclosure bits, executor signature. The chain binds pre==prior.post for offline replay.",
          files: [f("turn/src/turn.rs", 844)] },
        { name: "Partial turns / promises (Promise/Notify/React)", status: "REAL", what: "Reactive effects: a guarded hole (Promise) is a guarded field write; React consumes it as a nullifier (fail-closed). CapTP promise pipelining braids into the effect layer.",
          files: [f("turn/src/action.rs", 962), f("turn/src/eventual.rs"), f("turn/src/conditional.rs")] },
      ],
    },
    {
      id: "predicates", layer: "substrate", title: "Predicates / caveat algebra & dregg-dfa",
      what: "One witnessed-predicate algebra unifies slot caveats, capability caveats, preconditions, and authorization guards under a single shape: a kind + a 32-byte commitment + an input reference + a proof witness index. The registry is extensible — 7 built-in verifier kinds plus a Custom escape hatch. dregg-dfa is the verified dispatch primitive: a boolean-closed derivative algebra over the same predicate shape.",
      components: [
        { name: "WitnessedPredicate", status: "REAL", what: "(kind, commitment[32], input_ref, proof_witness_index). The one shape behind caveats, guards, preconditions, intents.",
          files: [f("cell/src/predicate.rs", 149)] },
        { name: "The 7 verifier kinds + Custom", status: "REAL", what: "Dfa · Temporal · MerkleMembership · NonMembership · BlindedSet · BridgePredicate (Gte/Lte/…/InRange) · PedersenEquality · Custom{vk_hash}. Five+ wired with real verifiers.",
          files: [f("cell/src/predicate.rs", 207)] },
        { name: "InputRef resolution", status: "REAL", what: "Slot / Witness / PublicInput / Sender / SigningMessage / AuthContext — where a predicate's input comes from.",
          files: [f("cell/src/predicate.rs", 167)] },
        { name: "dregg-dfa — the verified dispatch primitive", status: "REAL", what: "NFA→DFA compilation (concat/alt/intersection/byte-ranges/repetition), RouteTable (BLAKE3 commitment), GovernedRouter (governance-gated atomic table swap), AirTrace for the STARK. Production routing: gossip filtering, intent pre-filter.",
          files: [f("dfa/src/lib.rs"), f("docs/deos/DERIVATIVE-MATCHING-DESIGN.md")] },
      ],
    },
    {
      id: "umem", layer: "substrate", title: "Universal memory (umem)",
      what: "A witnessed key→value store whose committed sorted-Poseidon2 root IS its boundary. Six disjoint domains tag the address space; one Blum memory-checking trace attests consistency across all of them at once. Whole-world state, per-cell heaps, transient scratch, and passable intermediate states all use the same construct — the substrate for time-travel, continuations, and checkpointable runtime.",
      components: [
        { name: "The six domains", status: "REAL", what: "Registers (transient VM regs) · Heap (per-cell record state) · Caps (authority state) · Nullifiers (insert-only) · Index (receipt MMR) · Working (service/interpreter scratch).",
          files: [f("turn/src/umem.rs", 99)] },
        { name: "umem IS the deployed prover", status: "DEPLOYED", what: "The umem-flip fired — umem is the live prover surface (per-cell heap, working domain, composable umem-refs all landed).",
          files: [f("turn/src/umem.rs", 28)] },
        { name: "Soundness keystones", status: "PROVEN", what: "universal_memory_sound (trace ⟹ per-domain projection), memcheck_pins_final, boundary_init_root_bound (init IS pinned to the committed root; tampered declared heap refused). #assert_axioms-clean.",
          files: [f("metatheory/Dregg2/Crypto/UniversalMemory.lean", 197), f("metatheory/Dregg2/Crypto/UniversalMemory.lean", 475)] },
        { name: "Time-travel · continuations · documents", status: "REAL", what: "O(1) reify_ledger inverse fold restores a past image (byte-identical reify↔project); suspended turns resume into the running ledger; a sovereign document is bound by one umem root.",
          files: [f("turn/src/continuation.rs"), f("docs/reference/umem.md")] },
        { name: "Stage-B checkpoint/resume effect surface", status: "DESIGN", what: "A first-class effect emitting a umem-ref + one consuming it; carrier wiring (EventualRef / CapTP / SharedFork) named, not built.",
          files: [f("docs/deos/UMEM-STAGE-B-DESIGN.md")] },
      ],
    },
    {
      id: "dregg3", layer: "substrate", title: "DREGG3 — the kernel redesign (design)",
      what: "The kernel's ideal shape: 6 nouns, 8 structural verbs, 6 unifications. It is a DESIGN ABSTRACTION with a minimality theorem — NOT the deployed variant count (the runtime carries ~32 Effect variants). Most underlying pieces are built and verified; the refactor to the literal 8-verb kernel is staged, not runtime-flipped.",
      components: [
        { name: "6 nouns", status: "DESIGN", what: "Pred (one guard algebra) · Cap (attenuable token) · Cell (four substances + program) · Asset (issuer's promise, AssetId:=CellId) · Turn (auth∘body∘receipt) · Q (receipt, committed postcondition).",
          files: [f(".docs-history-noclaude/DREGG3.md", 115)] },
        { name: "8 verbs (minimality theorem)", status: "DESIGN", what: "create · write · move · grant · revoke · shield/unshield · lifecycle. A design abstraction over the deployed Effect vocab + its minimality theorem over Substrate/VerbRegistry.lean.",
          files: [f(".docs-history-noclaude/DREGG3.md", 151)] },
        { name: "6 unifications", status: "STAGED", what: "R1 Fpu camera (returned partial/strong) · R2 AssetId:=issuer (LANDED) · R3 cell-programs cover storage · R4 svenvs≅mandate · R5 mediator≅joint-cell · R7 caps-in-slots (LANDED both sides).",
          files: [f(".docs-history-noclaude/DREGG3.md", 281)] },
      ],
    },
    {
      id: "circuit", layer: "substrate", title: "Descriptor circuit & light-client unfoolability",
      what: "Each turn carries a STARK proving it was a valid kernel transition. Turns fold into a constant-size recursive whole-chain aggregate. A light client holds no secrets, re-runs no cell, and — checking only a succinct root — learns the whole history is genuine. The apex theorem and the five guarantees are axiom-clean; the only genuine open items are the STANDARD crypto carriers (FRI/STARK soundness, Poseidon2 collision-resistance, deployed-tree faithfulness).",
      components: [
        { name: "lightclient_unfoolable — the apex", status: "PROVEN", what: "verifyBatch accepts ⟹ ∃ a genuine kernel transition s⟶s′ with commitments binding pre/post. Single-transition; lifted to whole-turn and whole-history. #assert_axioms-clean.",
          files: [f("metatheory/Dregg2/Circuit/CircuitSoundness.lean", 453), f("docs/reference/lean-circuit.md")] },
        { name: "Whole-history aggregation", status: "PROVEN", what: "light_client_verifies_whole_history — the verified aggregate attests every per-step transition, ordering, genesis pin, and genuine final fold.",
          files: [f("metatheory/Dregg2/Circuit/RecursiveAggregation.lean", 200)] },
        { name: "The five guarantee apexes", status: "PROVEN", what: "Authority · Conservation · Integrity · Freshness · Unfoolability — each a genuine conjunction of content-carrying keystones (no True anchors); #assert_axioms on each.",
          files: [f("metatheory/Dregg2/AssuranceCase.lean", 166), f("docs/reference/lean-assurance.md")] },
        { name: "The standard crypto carriers (the only open floor)", status: "DESIGN", what: "StarkSound (FRI/STARK soundness extraction) · Poseidon2SpongeCR (collision-resistance) · DeployedFaithful (deployed-tree). Carried as typeclass hypotheses, never as Lean axioms — the audited crypto foundation, by design terminal.",
          files: [f("metatheory/Dregg2/Circuit/CircuitSoundness.lean", 382)] },
        { name: "Circuit subsystem reference", status: "REAL", what: "The descriptor circuit, batch STARK, recursive fold — the running prover/verifier.",
          files: [f("docs/reference/circuit.md"), f("circuit/")] },
      ],
    },
    {
      id: "lean", layer: "substrate", title: "The Lean theory (verified kernel)",
      what: "An l4v-shaped stack: Spec states abstract laws (parametric over value monoids + rights lattices); Exec builds a fail-closed machine; refinement proves Exec ⊑ Spec. Authority = production under non-forgeability. Conservation = Σδ=0 over an arbitrary value monoid. The distributed theory reindexes the single-machine proofs over a topology.",
      components: [
        { name: "Kernel spec — Exec ⊑ Spec", status: "PROVEN", what: "exec k turn : Option KernelState commits only when authorized + 0≤amt≤bal + src≠dst, fail-closed otherwise. exec_conserves, exec_authorized; refinement square via two projections.",
          files: [f("metatheory/Dregg2/Exec/Kernel.lean", 69), f("docs/reference/lean-kernel.md")] },
        { name: "Authority — production under non-forgeability", status: "PROVEN", what: "The attenuation algebra (confers: reflexive/transitive non-amplifying order); only_connectivity_begets_connectivity (every reachable edge descends from a held edge or an authorized generative act).",
          files: [f("metatheory/Dregg2/Spec/Authority.lean", 456), f("docs/reference/lean-authority.md")] },
        { name: "Conservation — six-color linearity, Σδ=0", status: "PROVEN", what: "LinearityClass (6 colors); conservedInDomain := Σδ=0; conservation_over_monoid; multi_domain_independent (4 domains conserve independently).",
          files: [f("metatheory/Dregg2/Spec/Conservation.lean", 217), f("docs/reference/lean-conserve.md")] },
        { name: "macaroon ↔ kernel-gate bridge", status: "PROVEN", what: "The arrow from the macaroon/biscuit caveat algebra to the kernel's authority gate — CaveatCapBridge.",
          files: [f("metatheory/Dregg2/Authority/CaveatCapBridge.lean", 168)] },
        { name: "Distributed — settlement soundness", status: "PROVEN", what: "settlement_soundness: a settled turn exercised a LiveAtTip authority (held AND honored at the settlement tip). Eventual-bounded revocation; immediate at n=1. Composed against the real circuit.",
          files: [f("metatheory/Metatheory/SettlementSoundness.lean", 153), f("docs/reference/lean-distributed.md")] },
        { name: "Honesty ledger", status: "REAL", what: "The skeptic-facing inventory of exactly what is proved (and what is not); the conceptual spine.",
          files: [f("metatheory/CLAIMS.md"), f("metatheory/CONSTRUCTIVE-KNOWLEDGE.md")] },
      ],
    },
    {
      id: "capacities", layer: "substrate", title: "House capacities & their welds",
      what: "Six heap-committed cell-programs, each grounded as a Lean rung by reuse of a proven commitment lattice (the cap-lattice or the committed-heap-root). For each: the EXECUTOR tooth (the verifier holds sources/caps and rejects a forge) is REAL today; the CIRCUIT/VK weld (so a light client, not just a re-executing validator, witnesses the invariant) is the named shadow — STAGED per capacity in the weld plan.",
      components: [
        { name: "Membrane (cap conjunction / forwarder)", status: "EXEC", what: "reshare_chain_attenuates: re-sharing only attenuates, never amplifies. Executor tooth real; circuit weld STAGED (VK-affecting).",
          files: [f("metatheory/Dregg2/Deos/Membrane.lean", 100), f("docs/deos/HOUSE-CAPACITY-FRAMEWORK.md")] },
        { name: "Derived (materialized view = f(sources))", status: "EXEC", what: "claim_bound_in_root + forged/stale rejection. Circuit DerivedEquals constraint STAGED.",
          files: [f("metatheory/Dregg2/Deos/DerivedCell.lean")] },
        { name: "Sealed escrow (atomic 2-of-2 swap)", status: "EXEC", what: "leg_status_bound_in_root + replay/nonconforming/over-claim rejection. The SettleEscrow descriptor weld is STAGED (see Gentian).",
          files: [f("metatheory/Dregg2/Deos/SealedEscrow.lean", 47)] },
        { name: "Standing obligation (recurring duty/rent)", status: "EXEC", what: "cursor_strict_mono + cursor_bound_in_root + period/one-shot replay rejection. Factory descriptor STAGED.",
          files: [f("metatheory/Dregg2/Deos/StandingObligation.lean")] },
        { name: "Hatchery (abstraction-mint / custom verifier)", status: "DEPLOYED", what: "HpresProof::Attested IS a machine-checked CellContract carry (a forever-crown, not a trusted flag); invariant_forever. Custom cell programs live; the contract-binding weld is the named follow-up.",
          files: [f("metatheory/Dregg2/Deos/Hatchery.lean"), f("docs/deos/HATCHERY-ABSTRACTION-MINT.md")] },
        { name: "Vault (timelock + preimage + claim-once)", status: "DESIGN", what: "Provably immune to ERC-4626's inflation attack (deposit_no_dilution). Prototype + smoke tests; weld priority 1 (small, no new Effect, no VK change).",
          files: [f("cell/src/vault.rs"), f("docs/deos/CONDITIONAL-VAULT.md")] },
      ],
    },

    // ───────────────────────────── ECONOMY ─────────────────────────────
    {
      id: "economy", layer: "economy", title: "The service economy",
      what: "The value + service layer above the kernel: Payable routes every charge through one shared interface that desugars to a single conserving Transfer; the intent ring matches offers/wants into atomic value cycles; the service-promise binds service-for-payment as a 2-cycle escrow; the ToolGateway meters pay-per-tool access under a cap-gated mandate; the execution-lease models durable metered workloads (the rail an operator rents). The SDKs (Rust/TS/Py) expose all of this in a few lines. Everything below landed and is tested.",
      components: [
        { name: "Payable — the conserving Transfer DSI", status: "REAL", what: "The one verified source of truth for cross-app value: pay() routes through resolve_pay and desugars to exactly one Effect::Transfer (Σδ=0). Used identically by framework turns, the SDK runtime, and the tool gateway.",
          files: [f("dregg-payable/src/lib.rs", 17), f("app-framework/src/payable.rs", 52)] },
        { name: "Intent ring + service-promise", status: "REAL", what: "RingCoordinator collects offers → matches a ring → verifies Σδ=0 → atomically drives apps (fail-closed). ServicePromise binds a service contract; committed-state escrow is release-XOR-refund one-shot. 4 e2e contracts proven (happy/refund/atomic/conserved).",
          files: [f("app-framework/src/ring_trade.rs", 176), f("app-framework/src/service_promise.rs", 84)] },
        { name: "ToolGateway — pay-per-tool", status: "REAL", what: "deleg_admit (byte-faithful Lean mirror: SCOPE ∧ DEADLINE ∧ RATE) + a mandate_program (FieldLte + Monotonic meter). Each admitted call charges one conserving Transfer. Unit + e2e + red-team tests (every overrun refused in-band).",
          files: [f("sdk/src/tool_gateway.rs", 115), f("sdk/src/tool_gateway.rs", 220)] },
        { name: "Execution-lease (the rail)", status: "REAL", what: "A durable-execution provider on the value layer (fly.io-lite): a lease cell holds a checkpoint, a cap-gated worker runs metered by FieldLte+Monotonic, payment is a conserving Transfer; lapse refuses on non-payment. This is what an operator bridge fulfills.",
          files: [f("sdk/src/service_economy.rs", 305), f("starbridge-apps/execution-lease/src/lib.rs", 1)] },
        { name: "Rust SDK — dregg-sdk", status: "REAL", what: "AgentRuntime::pay() / invoke_service() / ExecutionLease — the mature core; embeds the verified executor.",
          files: [f("sdk/src/service_economy.rs", 86), f("docs/reference/sdk.md")] },
        { name: "TypeScript SDK — @dregg/sdk 0.3.0", status: "REAL", what: "Publish-ready npm package (standalone pure-TS core). Exports ServiceEconomy, Lease, LeaseStep, LeaseTerms, PayLeg.",
          files: [f("sdk-ts/package.json", 1), f("sdk-ts/src/index.ts", 78)] },
        { name: "Python SDK — dregg (pip)", status: "REAL", what: "maturin/pyo3 build; LIGHT kernel-free default wheel; opt-in dregg[kernel] (embedded verified Lean) + dregg[pg] (the no-reflexive-features architecture).",
          files: [f("sdk-py/pyproject.toml", 6), f("sdk-py/src/lib.rs", 1)] },
        { name: "Developer guides", status: "REAL", what: "SERVICE-ECONOMY-SDK.md (authoritative: each call → underlying turn/effect) · BUILD-WITH-DREGG.md · AGENT-QUICKSTART.md · WHAT-YOU-CAN-BUILD.md.",
          files: [f("docs/guide/README.md"), f("docs/guide/SERVICE-ECONOMY-SDK.md")] },
      ],
    },

    // ───────────────────────────── DEOS ─────────────────────────────
    {
      id: "cockpit", layer: "deos", title: "The deos pillars (desktop + runtime)",
      what: "The reflective desktop: a cap-first window manager over a live local dregg world, where cells become windows, mutations are verified turns, and history carries provenance. One gpui-free view-tree model paints to native windows AND browser tabs; real SpiderMonkey drives cells (not a DOM) via cap-gated turns; a confined agent inhabits the cockpit; the whole substrate compiles to wasm and runs light-client-verified in a tab.",
      components: [
        { name: "starbridge-v2 — the cockpit shell", status: "REAL", what: "Cap-first window manager + verified-scene compositor (3 teeth: non-overlap, label-binding, focus-exclusivity, ported from Lean), shared_fork membrane, login/logout cap ceremony. --desktop boots the live workbench; embeds the verified executor.",
          files: [f("starbridge-v2/src/shell.rs", 190), f("starbridge-v2/src/compositor.rs", 1), f("docs/reference/cockpit.md")] },
        { name: "deos-view — renderer extraction", status: "REAL", what: "One serializable deos.ui.* view-tree (VStack/Row/Text/Bind/Button/Input/List/Table…) → native gpui pixels OR web HTML, from identical input. SolidJS-shaped fine-grained re-render.",
          files: [f("deos-view/src/tree.rs", 22), f("docs/reference/deos-view.md")] },
        { name: "deos-js — JS on cells", status: "REAL", what: "Real SpiderMonkey (mozjs) driving sovereign cells via cap-gated verified turns. drive (affordances = turns) + crawl (cap-bounded reflection). Transclusion is a provenanced include. The cap tooth (is_attenuation) is in-band.",
          files: [f("deos-js/src/applet.rs", 164), f("deos-js/src/js.rs", 618), f("docs/deos/JS-ON-CELLS.md")] },
        { name: "deos-hermes — confined agent", status: "STAGED", what: "An agent loop as a cap-gated surface cell: every ACP tool-call is intercepted → cap-gated, metered, RECEIPTED turn through the proven ToolGateway. End-to-end loop runs over a mock peer; live subprocess install is the seam.",
          files: [f("deos-hermes/src/bridge.rs", 18), f("deos-hermes/src/acp_client.rs", 33), f("docs/deos/HERMES-INTEGRATION.md")] },
        { name: "deos-zed — editor surface", status: "REAL", what: "A Zed-fork text editor as a deos surface; Fs trait (RealFs today). FirmamentFs stub maps load=cap-read, save=receipted turn — Level-1 (file=cell) is one host wiring away.",
          files: [f("deos-zed/src/editor.rs", 65), f("deos-zed/src/fs/firmament.rs", 9)] },
        { name: "deos-web-cells + wasm + deos-leptos", status: "DEPLOYED", what: "The real verified substrate compiled to wasm32 (71+ bindings); the cockpit renders in-browser on WebGPU; a cell's card is served to a browser, light-client-verified IN the tab. Frustum snapshots, per-viewer projection.",
          files: [f("wasm/src/lib.rs"), f("deos-web-cells/src/document.rs"), f("docs/reference/wasm-web.md")] },
        { name: "deos-matrix · deos-terminal · deos-reflect", status: "REAL", what: "Matrix client with a fog-of-war membrane (per-viewer vision projection, proved) · real PTY over alacritty with a platform-free transport (native + WebSocket) · a gpui-free cap-bounded attested reflective view of cells/ocap-graph/affordances.",
          files: [f("deos-matrix/src/membrane.rs"), f("deos-terminal/src/model.rs", 204), f("deos-reflect/src/graph.rs")] },
      ],
    },
    {
      id: "bridges", layer: "deos", title: "The bridges (external world)",
      what: "Connectors that bring outside value/state into a cell as a conserving, cap-gated turn. Each transforms an external authorization (a Solana lock, a Stripe webhook, a Midnight state root) into an Effect the kernel accepts, never letting the mirror claim more than was locked/paid.",
      components: [
        { name: "Solana mirror + trustless consensus", status: "REAL", what: "pump.fun $DREGG token mirroring → conserving Mint that pays a lease; real Tower-BFT consensus verification (stake-weighted Ed25519 votes + bank-hash + accounts inclusion + PoH). live_supply ≤ currently_locked invariant.",
          files: [f("bridge/src/solana_mirror.rs", 366), f("bridge/src/solana_consensus.rs"), f("bridge/src/solana_trustless.rs")] },
        { name: "Concurrency double-mint gate", status: "STAGED", what: "Consume-once lock_id nullifier + committed mirror-ledger cell, designed sound (BRIDGE-ARCHITECTURE-SOUNDNESS §3). Nullifier derivation real; per-relayer in-memory seen_locks is still the active dedup until the committed gate routes in the executor apply path.",
          files: [f("bridge/src/solana_mirror.rs", 59), f("docs/deos/BRIDGE-ARCHITECTURE-SOUNDNESS.md")] },
        { name: "Stripe payment rail", status: "REAL", what: "Webhook-verified payment → conserving mint → pays an execution-lease.",
          files: [f("bridge/src/stripe_mirror.rs")] },
        { name: "Midnight state-inclusion + Ethereum/Mina", status: "REAL", what: "Native state-INCLUSION over a re-committed mirror root (splits 'is root valid' from 'is state in root'); permissionless watchtower. Ethereum + Mina ZK-proof connectors.",
          files: [f("bridge/src/midnight.rs"), f("bridge/src/ethereum.rs"), f("docs/deos/DIFFERENT-MIDNIGHT-BRIDGE.md")] },
        { name: "Custom-VK / recursive verification", status: "STAGED", what: "ProgramRegistry keyed by VK hash + Effect::Custom carrying program_vk_hash + proof_commitment. The in-circuit proof_bind constraint is STAGED (deployed descriptor is a bounds-check; genuine recursive verify runs in the Rust engine). Lift 4→8 felts in one gated epoch.",
          files: [f("metatheory/Dregg2/Circuit/CustomApex.lean", 90), f("docs/deos/CUSTOM-VK-AUTHORIZATION.md")] },
      ],
    },
    {
      id: "apps", layer: "deos", title: "starbridge-apps (userspace apps-as-cells)",
      what: "~24 native-primitive userspace apps, each a cap-bounded cell-program with its own Cargo crate, README, and green test suite. They are the worked exemplars of what the substrate enables — escrow, governance, identity, multiplayer, agent-orchestration — built on the real verified executor, not mockups.",
      components: [
        { name: "Value / market apps", status: "REAL", what: "bounty-board (escrow-backed bounties) · escrow-market (SealedEscrow atomic swap) · compute-exchange (requester↔provider, no intermediary) · sealed-auction (front-running-proof) · execution-lease (durable payable resource).",
          files: [f("starbridge-apps/bounty-board/"), f("starbridge-apps/escrow-market/"), f("starbridge-apps/execution-lease/")] },
        { name: "Governance / identity apps", status: "REAL", what: "polis (M-of-N councils, constitution-as-program, KERI pre-rotation) · governed-namespace (governance-bound atomic route-table swap) · identity (verifiable credentials) · nameservice (federation directory) · privacy-voting (one-vote-per-ballot, tamper-evident).",
          files: [f("starbridge-apps/polis/"), f("starbridge-apps/identity/"), f("starbridge-apps/governed-namespace/")] },
        { name: "Agent / delegation apps", status: "REAL", what: "agent-orchestration · swarm-orchestration · agent-provenance (proof-carrying agent memory) · tool-access-delegation (ocap model for AI) · compartment-workflow-mandate · storage-gateway-mandate.",
          files: [f("starbridge-apps/agent-orchestration/"), f("starbridge-apps/tool-access-delegation/")] },
        { name: "Distributed / composition apps", status: "REAL", what: "branch-stitch-multiplayer (disjoint edits merge clean) · tussle (2-party JOINT TURN with STARK ring settlement) · first-room (welds other apps' organs into one scenario) · supply-chain-provenance (custodianship as conservation) · kvstore · subscription · gallery.",
          files: [f("starbridge-apps/branch-stitch-multiplayer/"), f("starbridge-apps/tussle/"), f("starbridge-apps/first-room/")] },
      ],
    },

    // ───────────────────────────── GENTIAN VK WELDS ─────────────────────────────
    {
      id: "vkepoch", layer: "welds", title: "Gentian VK-epoch constraint-binding",
      what: "The deliberately-gated work of binding each capacity invariant into the deployed VK, so a pure light client (not just a re-executing validator) witnesses it. The honesty distinction that this whole atlas exists to make: COVERAGE (the caveat manifest rides the live AIR-bound rotated carrier) is DEPLOYED today; SATISFACTION (the gate verdict in-AIR) is built, proven, emitted — but the FLIP is NOT taken. 'Deployed hverifier enforcement' names the SELECTOR column's real existence; the flip that makes it enforced in production is still ahead.",
      components: [
        { name: "Coverage carrier (tag 17, PIECE 1)", status: "DEPLOYED", what: "The caveat manifest rides the AIR-bound rotated carrier; the omission-proof coverage check is live; manifest pinned to PI 45 via caveatCommit. Zero VK impact — a pure light client witnesses coverage TODAY.",
          files: [f("circuit/src/effect_vm/verify.rs"), f("metatheory/Dregg2/Deos/CapacityCarrier.lean"), f("docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md")] },
        { name: "Escrow satisfaction weld (tag 17, PIECE 2)", status: "STAGED", what: "BUILT, PROVEN, EMITTED — NOT FLIPPED. Soundness proven (satisfaction_witnessed); real selector column (ESCROW_SEL_COL=70, pinned to PI 46); 4 gates over rotated field columns; emitted descriptor in the staged registry; exerciser validates at constraint level. Remaining: producer emitting a satisfying trace, a full STARK prove against a COMMITTED VK, and live routing.",
          files: [f("metatheory/Dregg2/Deos/CapacitySatisfaction.lean"), f("metatheory/Dregg2/Deos/SettleEscrowSatDescriptor.lean", 133)] },
        { name: "Tags 18/19 satisfaction (discharge, vault)", status: "STAGED", what: "Soundness PROVEN (2026-06-28); the in-AIR gates are NOT a mirror of the escrow equality template — discharge needs a range-checked due-ness inequality; vault needs strict inequalities + an overflow-safe product (exceeds BabyBear's ~31-bit field). An equality-only weld would DROP the early-discharge / inflation-attack disciplines — unsafe to flip until the range/product gadgets land.",
          files: [f("metatheory/Dregg2/Deos/CapacitySatisfaction.lean")] },
        { name: "The FLIP — not taken", status: "STAGED", what: "Deployed descriptors + VK are byte-identical (drift guard green); rotated_descriptor_name_for_effect is unchanged; no turn routes through the welded descriptor. The capability-membership posture: a light client witnesses satisfaction WITH the caller-supplied opening, not yet from the deployed VK alone. DEPLOYED ≠ FLIPPED.",
          files: [f("docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md")] },
        { name: "Host & container bridges (frontier)", status: "DESIGN", what: "Same Target/Capability/is_attenuation gate, only the backing moves — a drop-in rehearsal for native seL4. Design complete (phased H0–H2 / C0–C2); no circuit/execution code yet.",
          files: [f("docs/deos/HOST-AND-CONTAINER-BRIDGES.md"), f("docs/deos/ETH-NATIVE-WRAP.md")] },
      ],
    },
  ],
};
