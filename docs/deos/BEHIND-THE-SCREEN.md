# BEHIND THE SCREEN — a zero-knowledge trustless private fiction engine

*A design. The game-master keeps a secret module; every generated thing is provably a
legitimate expansion of that module over valid committed world-state — verifiable by anyone,
in zero-knowledge, without ever seeing behind the screen.*

Grounded 2026-07-07 against the real tree (grounding workflow `wf_b8ecb2e4-66d`). This is a
**composition** of proven machinery, not new cryptography — the honest part is the four named
gaps in §5, each a descriptor-authoring or wiring task on components that already ship.

---

## 1. The one primitive — the provenance certificate

A distributed MUD / interactive fiction generates content **from templates over game-world
state**. The thing worth proving isn't "the text has no bad tokens" (prompt-injection is the
wrong frame) — it's **provenance**:

> **The content a player consumes is a legitimate expansion of the sanctioned template,
> filled only from valid committed world-state — and nobody fabricated it.**

Stated as one certificate, proven in zero-knowledge over two public commitments:

```
ProvenanceCert  (public: C_template, R_worldstate  |  hidden: template, state, bindings)
  proves:   content   = expand(template, bindings)          -- DERIVATION
        ∧   template  opens C_template                       -- the sanctioned module (may be secret)
        ∧   ∀ v ∈ bindings.  v opens R_worldstate            -- genuine committed game state
  ⟹        content is a legit template-expansion over valid state
           WITHOUT revealing the template or the state.
```

The **DERIVATION** half is a `Hypergraph.bridge` / `graphRewrite_bridge` / `cfg_bridge`
certificate (content is reachable from the template under the rewrite/derivation relation).
The **OPENING** half is the membership/adjacency descriptor (each substituted value opens the
committed world-cell root). The **ZK** is the shielded hiding PCS (template + state + bindings
in the private witness; only the two commitments public). All three exist and are proven.

## 2. The certified generation loop — one verified turn

```
   ┌─ INPUT side (new) ──────────────┐   ┌─ ORACLE ─┐   ┌─ OUTPUT side (exists) ─┐
   │  template (secret) ⊗ world-cell │──▶│ the model │──▶│  zkOracle attestation  │
   │  → ProvenanceCert (§1)          │   │  (DM/LLM) │   │  authentic ∧ well-formed│
   └─────────────┬───────────────────┘   └───────────┘   └───────────┬────────────┘
                 └───────────────── folds into ─────────────────────┘
                          the WorldCell turn  (one signed receipt)
                                     │
                             O(1) light-client root
```

- **Input side (the gap this design fills):** the prompt/content is proven to be
  `expand(secret_template, committed_state)` — the ProvenanceCert.
- **Oracle:** the DM is a model. If it's an LLM, the output rides the existing zkOracle path.
- **Output side (already real):** `ZkOracleAttestation` proves the response is authentic
  (zkTLS/DECO, key hidden) ∧ well-formed — and is a live *host* for descriptor-carried ZK legs.
- **The turn:** both certs fold into the `WorldCell::commit` turn as ONE receipt; the whole
  generative history collapses to an O(1) root a light client verifies without replay.

## 3. Why it's real — every ingredient is grounded and proven

| ingredient | status | where |
|---|---|---|
| **template = grammar / rewrite-rules** | ✅ proven, axiom-clean | `Cfg` + `Hypergraph.bridge` (parametric over ANY reduction R) + `GraphRewrite` (`step_matches`) |
| **derivation certificate** | ✅ + fast | the compact O(tokens) CFG cert, now on the descriptor prover (10× vs the hand engine) |
| **value-opens-committed-root** | ✅ proven, ZK-of-state | Merkle/Adjacency membership descriptors (leaf+path private, only root public), Rung-2 no-forgery |
| **ZK-hiding (the "private")** | ✅ **shipped** | `circuit-prove/src/shielded/*` already does ZK attestations over *hidden committed cell state*, pure-descriptor; `prove_dsl_zk`/HidingFriPcs, OS-blinded |
| **fold → O(1) light client** | ✅ real, tested | `lightclient` whole-chain IVC (`light_client_attests_whole_history`); every leaf exposes a folding segment |
| **response attestation** | ✅ real, wired | `ZkOracleAttestation` (authentic ∧ well-formed), into `deos-hermes` + the grain ledger |
| **the world engine** | ✅ real | `spween-dregg` (story = world-cell, each choice = a verified turn, replay re-verifies, collective authoring) + `starbridge-v2/src/mud.rs` (room = cell, item = cap, "can't dupe the item") |
| **the exact attach seam** | ✅ identified | `spween-dregg/src/world.rs:311` `WorldCell::commit`; cert lands on `StepReceipt` (world.rs:421); template ⊗ state already split by `compile_scene` (compiler.rs:124) |

The load-bearing discovery: **spween's compiler already factors a story into
`(predicate program = template) ⊗ (cell slots = state)`** — the precise decomposition the
provenance cert needs. The pieces are adjacent; the design connects them.

## 4. Why it's impressive — six properties that fall out

1. **Behind the screen.** The DM keeps a secret module — hidden templates, hidden rooms,
   hidden plot — and still proves every beat is a fair expansion of it. Players verify the DM
   never cheated *without seeing the module*. The literal GM's screen, made cryptographic.
   This is real because the shielded subsystem already proves attestations over hidden state.
2. **Provenance to genesis.** Every artifact chains a cert to its template; the world's whole
   generative history is verifiable. Fabricated content cannot exist.
3. **Light-client-verifiable procedural generation.** The certs fold into the turn chain, so a
   light client verifies the entire generated world in O(1) — no LLM replay, no template
   disclosure.
4. **Collective authoring, private attribution.** Many authors contribute templates (each a
   committed cell, over the real `CollectiveChoiceEngine`); every generated thing is provably
   attributable to its author *while the template stays secret* — credit + governance without
   disclosure.
5. **Game integrity as a theorem.** "Can't dupe the item" (already real in `mud.rs`)
   generalizes to "can't fabricate *anything*": items are caps, rooms are cells, generation is
   provenance-certified.
6. **It's a rentable grain.** The DM is the confined, metered, R2-verified grain we built —
   now it *also* proves provenance per turn. **Rent a trustless private dungeon-master.**

## 5. The honest gaps — the build (each a descriptor/wiring task, no new crypto)

The grounding named exactly four gaps between "the pieces exist" and "the engine runs":

1. **Content is static, not template-filled.** spween prose is fixed `SmolStr` literals
   (`spween/src/ast.rs:73`); `current_prose` concatenates with zero interpolation. **Build:**
   a template-fill step (grammar / graph-rewrite expansion) that generates content and emits
   the derivation cert — the derivation engine exists; wire it to generation.
2. **The template isn't committed.** The cell token is `blake3(scene_id)` (`world.rs:119`),
   not the prose/grammar bytes — a GM can swap prose undetected. **Build:** commit the template
   (the grammar/Scene) to `C_template`; make it the thing the cert opens. This is the
   load-bearing binding for "provable fair play."
3. **No provenance certificate / descriptor.** `prove_vm_descriptor2` is referenced nowhere in
   `spween-dregg`; `StepReceipt` carries no content commitment. **Build:** the
   `ProvenanceDescriptor` = derivation-cert ⊗ opening-cert composed (via the fold's
   `connect`+`expose_claim` channel that already carries production claims), authored as
   descriptor DATA; attach at `WorldCell::commit`, land on `StepReceipt`, fold to the light
   client.
4. **No ZK over the template.** The compiler is transparent today. **Build:** author the
   ProvenanceDescriptor on the `shielded` ZK path (`prove_dsl_zk`) so template + state + bindings
   are private witness and only `C_template`/`R_worldstate` are public — the shielded subsystem
   proves this is a solved shape, not a research problem. (`fully_gated` in `compiler.rs:85`
   honestly bounds which choices are 100% arithmetizable vs handler-only — the ZK circuit
   covers the fully-gated core first.)

## 6. The demo that sells it — the Sealed Module

A dungeon whose module is **secret**. A real player explores. Every room description, every
item, every monster's line arrives with a ZK provenance cert: *this is a legitimate expansion
of the (hidden) module over (committed but hidden) world-state.* The player — and any observer
running a light client — verifies the DM **never fabricated a room, never conjured an item,
never went off-module**, in O(1), while seeing *none* of the module. Then a second author adds
a wing to the dungeon (a new committed template); their content is attributable to them,
provably, still secret. Trustless, private, verifiable, collaboratively-authored fiction.

## 7. The build campaign (phases, each gated + demoable)

- **P1 — Commit the template + the derivation cert (transparent first).** Commit a spween
  Scene/grammar to `C_template`; author the `ProvenanceDescriptor` derivation half; a generated
  passage carries a cert that it derives from the committed template. Gate: the cert verifies
  through `verify_vm_descriptor2`; a swapped template is rejected.
- **P2 — Bind the fill to committed world-state.** Compose the opening half (each fill value
  opens the world-cell root) via the fold `connect` channel. Gate: a fabricated state value is
  UNSAT; the composed cert rides the turn.
- **P3 — Go private (ZK).** Re-author the ProvenanceDescriptor on the `shielded` hiding path;
  template + state hidden, only commitments public. Gate: `prove_dsl_zk` roundtrip; a light
  client verifies with zero template/state disclosure.
- **P4 — Fold + light client + the Sealed-Module demo.** Fold the provenance cert into the
  `WorldCell` turn chain; the O(1) light client verifies the whole playthrough; ship the
  Sealed Module demo. Compose with the zkOracle response attestation for the LLM-DM variant.

Each phase is real, gated, and demoable on machinery that already ships. The novelty is the
composition — the certificate that binds *matched the template* to *from valid committed
world-state*, in zero-knowledge — which is exactly the question this started from.
