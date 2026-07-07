# Submit-Path Diagnosis — does an external HTTP turn reach the blocklace DAG + finalize cross-node?

READ-ONLY diagnosis. Scope: the ingress → consensus wiring in `node/src/api.rs` and
`node/src/blocklace_sync.rs`. No build, no code change, no live-mesh change. Grounded
file:line at HEAD.

Companion lane: the n=3 **finality-gate** diagnosis (a6137a773) covers turns that are
ALREADY in the DAG (does `tau` super-ratify + does `execute_finalized_turn` fire). This
doc covers the step *before* that: does an externally-submitted (HTTP) turn ENTER the DAG
at all, or does it stop at the entry node's local cipherclerk receipt chain.

---

## Short answer

An external HTTP turn does **not** reliably reach the blocklace DAG. The
`blocklace.submit_turn(...)` injection wiring **is present** on every ingress's committed
branch (it is NOT an un-wired stub), but the turn is stopped **upstream of that call** by
how the ingress handlers author + gate the turn:

- **`POST /turn/submit`** (thin client) **structurally cannot** carry a *client's* turn
  into consensus. The confused-deputy hardening rewrites the request's `agent` to the
  node's OWN operator cell (`api.rs:2891-2900`). A turn is therefore only authorable when
  the operator's own default cell exists in the ledger — true on a clean-boot genesis
  node, **absent on a joiner / relaunched node** (`main.rs:846-856`), where the turn is
  `Rejected("cell not found")` before the blocklace injection (`api.rs:3147`) is reached.

- **`POST /turns/submit`** (caller-signed rich client) *can* carry the client's own cell
  and *does* inject to the blocklace on commit (`api.rs:3407-3423`), but it (a) requires
  the client cell to **already exist** in the ledger — no actor provisioning path — and
  (b) binds + appends the client's receipt onto the **node operator's** cipherclerk chain
  (`api.rs:3269-3283`, `api.rs:3322`), serializing all clients through one node-owned
  chain.

- **`POST /api/faucet`** works cross-node **only because** its actor is the genesis-
  provisioned faucet cell, and it was explicitly engineered for finalization-driven
  provisioning (`api.rs:6572-6607`).

**Verdict: DESIGN GAP.** The "external client turn → DAG → cross-node finality" path is
incompletely wired, not a single broken wire and not pure client-error. The consensus
injection exists; the ingress layer never gets a *fresh client's own* turn to it.

---

## 1. The three external ingress endpoints

All three are `protected_routes`, gated by `require_auth` (`api.rs:1318`, layered at
`api.rs:1800`).

| Endpoint | Handler | Agent the turn acts as |
|---|---|---|
| `POST /turn/submit` | `post_submit_turn` (`api.rs:2869`) | node operator's own cell — body `agent` **ignored** |
| `POST /turns/submit` | `post_submit_signed_turn` (`api.rs:3209`) | the caller's signer default cell (must match) |
| `POST /api/faucet` | `post_faucet` (`api.rs:6490`) | the genesis faucet cell |

---

## 2. Traced submit path — where each commits, where each injects to the DAG

### 2a. `POST /turn/submit` (thin HTTP)

```
post_submit_turn (api.rs:2869)
  ├─ rate-limit + unlocked gate                                 (api.rs:2878-2889)
  ├─ CONFUSED-DEPUTY HARDENING: ignore req.agent, derive the
  │  operator's own cell from s.cclerk.public_key()             (api.rs:2891-2900)
  ├─ build CallForest signed by the operator cipherclerk        (api.rs:2918-2949)
  ├─ execute_via_producer(...) against s.ledger                 (api.rs:3002-3007)
  └─ match exec_result:
       Committed  → append_receipt onto s.cclerk (LOCAL chain)  (api.rs:3036)
                  → gossip_turn                                  (api.rs:3136-3141)
                  → blocklace.submit_turn(...)  ← DAG injection  (api.rs:3147-3163)
       Rejected   → return; NO blocklace injection               (api.rs:3174-3187)
```

The DAG injection at `api.rs:3147` is only reached on the `Committed` branch. Because the
turn acts on the operator's own cell, it commits **only when that cell exists**:

- Clean-boot genesis node: the operator agent cell is provisioned at boot
  (`main.rs:855` — "clean boot → agent cell present with the operator key"). The turn
  commits locally (`append_receipt`, `api.rs:3036`) and stages to the blocklace.
- Joiner / refused-launch-then-relaunch node: the operator cell is **absent**
  (`main.rs:846-856` documents exactly this) → `execute_via_producer` returns
  `Rejected("cell not found")` → the handler returns at `api.rs:3174` and **never** calls
  `blocklace.submit_turn`. This is the finding's `4fc1e09c… → cell not found`.

Either way, a *client's own* turn is unreachable: the body `agent` is discarded, so the
endpoint can only ever author operator turns.

### 2b. `POST /turns/submit` (caller-signed SignedTurn)

```
post_submit_signed_turn (api.rs:3209)
  ├─ verify signer signature over turn hash                     (api.rs:3230)
  ├─ REQUIRE turn.agent == derive_raw(signer, "default")        (api.rs:3243-3256)
  ├─ REQUIRE turn.previous_receipt_hash == s.cclerk head        (api.rs:3269-3283)  ← NODE chain
  ├─ execute_via_producer(...) against s.ledger                 (api.rs:3294-3299)
  └─ Committed → append_receipt onto s.cclerk (NODE chain)      (api.rs:3322)
              → gossip_turn                                     (api.rs:3398-3403)
              → blocklace.submit_turn / submit_turn_bundle      (api.rs:3407-3423)  ← DAG injection
```

This path **does** let a client carry its own cell (`api.rs:3245`) and **does** inject to
the blocklace. Two structural couplings remain:

1. **No actor provisioning.** `execute_via_producer` requires `turn.agent` to already
   exist; a brand-new client cell yields `Rejected("cell not found")`. Nothing along the
   HTTP path provisions a fresh client cell, and finalization only provisions transfer
   *destinations* (see §3).
2. **Node-chain coupling.** The `previous_receipt_hash` gate (`api.rs:3269`) checks the
   **node operator's** `s.cclerk` head, and `append_receipt` (`api.rs:3322`) appends onto
   `s.cclerk`. Every client's turns are serialized through the one node-operator receipt
   chain — this is the "local cipherclerk receipt chain" the finding observes on node0.

### 2c. `POST /api/faucet`

`post_faucet` (`api.rs:6490`) transfers from the **genesis faucet cell**
(`api.rs:6595-6596`), which is present authoritatively on every node. In multi-party mode
it runs execution against a **scratch clone** for the HTTP receipt and leaves authoritative
state to finalization (`api.rs:6572-6607`), then injects to the blocklace exactly like the
others (`api.rs:6938-6943`). It reaches the DAG because its actor cell exists.

---

## 3. Traced internal turn → DAG → finalize path (what the external path relies on)

Once a payload reaches `blocklace.submit_turn`, the machinery is uniform:

```
BlocklaceHandle::submit_turn (blocklace_sync.rs:410)
  → submit_turn_payload (blocklace_sync.rs:519)
       n>1: STAGE into pending_payloads, return (receipt, Local)   (blocklace_sync.rs:529-544)
       n=1: add_block immediately (solo finalizes trivially)       (blocklace_sync.rs:547-565)

cadence_tick_round_driven (blocklace_sync.rs:3369)  [round-driven producer loop]
  → round_cadence_decision → DrainTurns                            (blocklace_sync.rs:3406)
  → pop_front pending_payloads → produce_round_block(payload)      (blocklace_sync.rs:3439-3450)
  → produce_round_block (blocklace_sync.rs:484):
       plan_round_block gate — advance ONLY on a supermajority of
       distinct creators at the current round                     (blocklace_sync.rs:495-502)
       else RoundPlan::Wait → None → re-stage the payload          (blocklace_sync.rs:3462-3469)

finality executor → tau super-ratifies → execute_finalized_turn    (blocklace_sync.rs:3718, 3932)
  → provision_transfer_destinations (DESTINATIONS ONLY)            (blocklace_sync.rs:7737-7749)
  → execute_via_producer on every node, uniform post-state         (blocklace_sync.rs:4177-4180)
```

Two facts from this path matter to the external gap:

- **The block producer carries exactly one queued payload per round block**
  (`blocklace_sync.rs:3439-3448`) and only when `plan_round_block` reaches a supermajority
  (`blocklace_sync.rs:495`). If rounds cannot advance, staged turns never drain and
  `block_height` stays at genesis — this is the round-advancement / finality-gate concern
  the n=3 lane diagnoses (S5-1, documented at `blocklace_sync.rs:453-478`).
- **`execute_finalized_turn` provisions only Transfer *destinations***
  (`provision_transfer_destinations`, `blocklace_sync.rs:7737-7749`) — NOT the turn's
  **actor** cell. So even a finalized foreign-agent turn whose actor cell is absent has no
  uniform cross-node provisioning for the actor.

---

## 4. Verdict — design-gap / bug / client-error

**DESIGN GAP.** Grounded:

- It is **not** a single broken wire: `blocklace.submit_turn` is present and correct on
  every ingress's committed branch (`api.rs:3147`, `:3407`, `:6938`) and the cadence loop
  drains staged payloads into round blocks (`blocklace_sync.rs:3439-3450`).
- It is **not** pure client-error: on `POST /turn/submit` the client's `agent` is
  deliberately discarded (`api.rs:2895`), so no client request shape can author the
  client's own turn. There is no documented "use endpoint X instead" that provisions a
  fresh client cell into consensus.
- It **is** an incompletely-wired path: the mechanism to take a *fresh external client's
  OWN* turn all the way into the DAG was never built. `/turn/submit` was built for the node
  operating on its own (genesis-provisioned) cell; `/turns/submit` requires the client cell
  to pre-exist and folds it through the node operator's chain; the faucet works only
  because its actor is genesis-provisioned. On any node whose operator cell is absent, even
  the operator path fails `cell not found` (`main.rs:846-856`).

Net: external HTTP-submitted turns reach the **entry node's local cipherclerk receipt
chain** (via `append_receipt`, `api.rs:3036`/`:3322`) and, on nodes where the actor cell
exists, *stage* toward the DAG — but a fresh client's turn does not become a
blocklace block that peers cite and `tau` finalizes.

---

## 5. Fix design (grounded; NOT fired — node/api/consensus layer, ember/consensus-owner call)

The correct external-turn path = **caller-signed turn → deterministic actor provisioning at
finalization → uniform cross-node execution**, decoupled from the node operator's chain.

1. **Make `/turns/submit` THE external client path; decouple it from the node chain.**
   The `previous_receipt_hash` gate (`api.rs:3269`) and `append_receipt` (`api.rs:3322`)
   should key off the **client's own** receipt chain, not the node operator's `s.cclerk`.
   Simplest safe form: on a foreign-agent turn, treat the local commit as an **optimistic
   ack only** (do not append to `s.cclerk`), and let the finalization pass be the sole
   authoritative application — mirroring what the faucet already does with its scratch
   clone (`api.rs:6572-6607`).

2. **Provision the ACTOR cell at finalization, deterministically.** Extend
   `provision_transfer_destinations` (`blocklace_sync.rs:7737`) — or add a sibling step in
   `execute_finalized_turn` before `execute_via_producer` (`blocklace_sync.rs:4177`) — to
   provision the turn's actor cell as `derive_raw(SignedTurn.signer, "default")` with a
   zero-balance stub if absent. This is byte-deterministic and safe: `SignedTurn.signer` is
   carried in the block and its signature is already verified at
   `blocklace_sync.rs:3955`, so every node inserts the identical stub — the same uniformity
   argument the transfer-destination provisioning already relies on
   (`blocklace_sync.rs:4128-4143`). This lets a fresh client's FIRST turn finalize
   cross-node instead of `cell not found`.

3. **Keep `/turn/submit` as an operator-only demo endpoint** and document it as such — it
   is not, and cannot be, a client-turn path while the confused-deputy hardening
   (`api.rs:2891-2900`) stands (correctly — the hardening prevents the operator signature
   being pointed at a victim c-list). Do NOT relax the hardening; route client turns
   through the caller-signed `/turns/submit` instead.

With (1)+(2), a client builds a `SignedTurn` over its own cell, `POST /turns/submit`
injects it to the blocklace, the round producer carries it, and `execute_finalized_turn`
provisions the actor + applies it uniformly on every node.

---

## 6. Interaction with the n=3 finality-gate lane

**Both fixes are required** for a real flagship turn to finalize cross-node — they are
sequential gates on the same pipeline:

```
external client turn
   │  [THIS lane: submit → DAG]   — actor provisioning + /turns/submit decoupling
   ▼
blocklace DAG (staged in a round block)
   │  [n=3 lane: finality-gate]   — plan_round_block supermajority / tau super-ratify
   ▼                                 (blocklace_sync.rs:495, 3718)
execute_finalized_turn fires on every node   (blocklace_sync.rs:3932)
```

- This lane closes the first gate: get a fresh client's own turn INTO the DAG.
- The n=3 lane closes the second: make DAG turns actually super-ratify + execute
  cross-node (`plan_round_block` round advancement, `blocklace_sync.rs:495`; the S5-1
  round-synchronous-shape concern, `blocklace_sync.rs:453-478`).

Fixing only submit→DAG leaves turns staged-but-unfinalized if rounds cannot advance;
fixing only the finality-gate leaves the DAG finalizing internal operator/faucet turns
while external client turns never enter it. The payoff ("a real external turn reaches
consensus + finalizes cross-node") needs **both**.
