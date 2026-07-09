# the grain economy — renting, hosting, metering, forking, and reaping confined agent grains (grounded at HEAD)

*A file:line-grounded record of what the grain economy IS: the rent → confine → meter →
drive-as-kernel-turns → finalize → verify → reap lifecycle, the R0→R2 verifiability ladder
(with the honest R3 seam), the durable metered lease, fork/rewind/stitch, and the
grain-commons app-store. Present-tense what-is; every claim points at code; every trusted
step and every unbuilt seam is named. Companion to the vision docs
`docs/deos/GRAIN-HOMESERVER.md` / `docs/deos/GRAIN-CONFINED-BODY.md`; THIS is the ground
truth of the composition.*

## The one sentence

A **grain** is a hosted agent whose *object* is the source of truth: its mind is a committed
`dregg_cell::Cell`, its economics are a `HostedLease`, its confinement is an OS jail, and its
history is a signed receipt chain welded to committed kernel turns — so it can be **rented,
metered, driven, verified, forked, rewound, and reaped** as a first-class value, not as an
opaque vendor instance.

## The crate map (who does what)

| crate | role in the economy |
|---|---|
| **`agent-platform`** | rent / host / meter / reap confined agent grains; the R0–R2 renter ladder; the HTTP gateway (`rent`/`drive`/`transcript`-SSE/`verify`/`checkpoint`/`share`); the local-node landing leg |
| **`hosted-lease`** | the dregg-native durable-execution lease — the committed `EXEC_COLL` image + the `Monotonic` checkpoint cursor + the FUSED prepaid meter (meter⊗draw one write) |
| **`hosted-durable`** | the conserving settlement + metering rail — the `Settlement` trait, `LeaseCharge`/`SettleReceipt` (exactly-once, Σδ=0), `Account`/`OverBudget`, `MeterCharge` |
| **`grain-turn`** | the R2 kernel-turn weld — `ToolGatewayMinter` drives every admitted action through a real `dregg_sdk::ToolGateway::invoke`, so a receipt becomes a VIEW over a committed executor turn and the `calls_made` caveat meters host-side |
| **`grain-fork`** | fork / rewind / branch-and-stitch a grain's mind; `ConfinedSession::fork_two` (the four teeth) — the confined-session fork |
| **`grain-commons`** | the app-store — package/publish/install (`.spk`, App ID = author key), `GrainRegistry` + `RentQuote`, fork `Pedigree`, `GenesisAgent::hatch` |
| **`grain-verify`** | the renter attestation *consumer* side — `GrainAttestation::{verify, verify_for_renter, verify_r2}`, the R0→R3 ladder, and the honest `WHOLE_HISTORY_GAP` constant |
| **`grain-jail`** | (context, already documented) the confined *body* — `ConfinedBrain` plugs an OS-jailed subprocess into the `AgentBrain` seam |

## The lifecycle: list → rent → confine → meter → drive-as-kernel-turns → finalize → verify → reap

### 1. List & rent (`grain-commons`, then `agent-platform`)

A grain-store listing is a **cell** in a committed umem heap
(`grain_commons::registry::GrainRegistry`, `registry.rs`), keyed by App ID. `discover` reads
it back; `rent` prices a `RentQuote` bounded by the listing's `ListingTerms`
(`registry.rs::GrainRegistry::rent`). **This is honestly a quote, not a lease** — the module
states it explicitly (`registry.rs`, `RentQuote` doc): "No value moves here and nothing is
funded"; the quote's numbers feed the REAL funded lease. That real lease is opened by
`AgentPlatform::rent` (`agent-platform/src/lib.rs`), which parses the cap bundle under
`Confinement::Hosted` (`parse_caps_confined` — a raw `shell` is refused), opens a confined
`dregg_agent::session::Session`, and opens the hosting lease funded for `FUNDED_PERIODS`
(=1024) periods.

### 2. Confine (`grain-jail` body + `Confinement::Hosted` policy)

The tenant is a hosted, cap+budget-bounded `Session` opened under `Confinement::Hosted`
(`lib.rs::rent`) — lexically-confinable tools only. The drive's toolkit is ALWAYS rooted at
the grain's rented `workdir` (`OperatorTools::new(Toolkit::new(), &tenant.workdir)` in
`drive_in`), so a caller cannot substitute tools rooted outside the confinement. The confined
*body* itself is `grain-jail`'s `ConfinedBrain` (an OS-jailed subprocess behind the
`AgentBrain` seam — already documented).

### 3. Meter (`hosted-lease` fused prepaid meter, settled by `hosted-durable`)

Rent opens a FUSED prepaid lease: `open_vat_prepaid` seals the durable image AND the prepaid
meter+reserve on the SAME cell (`lib.rs::rent`), with the reserve seeded to
`rent_per_period * FUNDED_PERIODS` so it MIRRORS the funded balance. `AgentPlatform::bill_period`
(`lib.rs`) runs three steps under ONE tenant lock:

- **GATE** — `HostedLease::check_bill` (`hosted-lease/src/lib.rs`) reads-only the rent this
  period will draw, refusing off-schedule / replay / over-draw / exhausted-reserve
  (`InsufficientBudget`) BEFORE any value moves.
- **SETTLE** — the drawn rent becomes one conserving cross-cell `LeaseCharge` through the
  injected `Settlement` (`hosted-durable/src/settle.rs`): exactly-once by `(lease_id, period)`,
  Σδ=0 (the `TestConservingLedger` double still runs through the proven
  `apply_conserving_transfer` primitive; the production rail is `PayableSettlement`).
- **DISCHARGE** — `HostedLease::discharge` is the ONE atomic write that draws exactly `rent`
  from the reserve AND advances the meter cursor (`prepaid_lease::discharge_period`).

So `sum(settled) == drawn_total <= budget`, and **meter/pay drift is unrepresentable** — a
type error, not app discipline (`hosted-lease/src/lib.rs`, `Metering::Prepaid` doc). A grain
behind on rent lapses ON USE: `drive_in` calls `lease.lapse_if_behind(clock)` and refuses a
lapsed lease (`AgentPlatformError::Lapsed`).

### 4. Drive as kernel turns (R2 — `grain-turn` + `agent-platform::node`)

The default served drive `AgentPlatform::drive_serving` (`lib.rs`) routes every admitted
action through a **real committed executor turn**. `grain-turn`'s `ToolGatewayMinter`
(`grain-turn/src/lib.rs`) implements the `GrainTurnMinter` seam over
`dregg_sdk::ToolGateway::invoke`: each admitted action becomes a genuine turn on the
cap-gated grain turn-cell, witnessing `consumed`, `heap_root`, and `action_commit(label,cost)`
as committed state, and the turn's `turn_hash` is sealed into the receipt as its
`turn_receipt_hash`. The executor's own `calls_made` `FieldLte`+`Monotonic` caveat is the
**host-side meter**: a session loop that skipped its local meter still cannot drive the
on-ledger counter past the granted ceiling.

The served path further **lands** each turn on a real node: `agent-platform/src/node.rs`'s
`NodeMinter` mints the byte-identical witnessed turn straight onto a `LocalNode`'s world-state
ledger (a genuine `dregg_turn::TurnExecutor`) and records it on the node's finalized receipt
log via `LocalNode::land` (fail-closed — `land` rejects any receipt that does not link/extend
the log).

### 5. Finalize & checkpoint (`hosted-lease` durable image + the resumable carrier)

Every drive advances the lease's `Monotonic` durable checkpoint with a **verified binding**
of the session (digest + chain tip + turn count + consumed, re-checked on every `verify` —
`image_binds`). Beyond those cursor slots, a checkpoint also persists the FULL resumable
`SessionCarrier` (`lib.rs`) into the committed `EXEC_COLL` heap — chunked with a LENGTH slot,
a ROOT-TOOTH slot (`blake3` of the carrier), then data slots — so a grain is WAKEABLE from
its lease heap ALONE (`AgentPlatform::wake_from_lease`), fail-closed on a root-tooth mismatch
(`CarrierRefused`). Secret handling is explicit: only the carrier's ROOT (a hash) is
committed; the receipt-signing secret never appears in an attestation (`SessionCarrier` doc).

### 6. Verify (`grain-verify`, the consumer side)

A renter re-witnesses the grain holding only the handed-back artifact and re-running nothing.
`AgentPlatform::verify` runs the chain + budget re-witness + the durable-image bind;
`verify_r2` (`lib.rs`) additionally checks every admitted receipt is a VIEW over a turn in the
committed-turn manifest (`grain_verify::R2Verified`); `verify_landed` (`lib.rs`) confirms every
manifest turn is on the local node's finalized, light-client-verifiable log. `attest` hands
back a `grain_verify::GrainAttestation` carrying the R1 anchor material.

### 7. Reap (`agent-platform` + the vat lifecycle)

The grain's lifecycle is a `starbridge_vat::VatState` (`Created`/`Running`/`Sleeping`/`Lapsed`/`Reaped`)
sealed on the lease cell, advanced ONLY through the legality-checked `apply_transition`
(the executor's `Monotonic(VAT_PHASE)` tooth — `Tenant::transition`). `reap_if_behind`
(`lib.rs`) lapses a delinquent lease and mirrors the LAPSED tooth into the vat lifecycle;
`sleep`/`wake` are the checkpoint-and-teardown / restore transitions.

## The verifiability ladder R0 → R1 → R2, and the R3 seam

The renter ladder is documented in-code at `agent-platform/src/lib.rs` (crate docs) and
`grain-verify/src/lib.rs` (the one-line rung↔verifier table). Each rung's verifier RUNS every
rung below it.

- **R0 — third-party forgery closed + in-transit mutation.** The receipt-chain key is a fresh
  RANDOM persisted secret, not `BLAKE3(agent_id)` — a third-party report-holder cannot
  re-derive it and forge. `GrainAttestation::verify` (`grain-verify/src/lib.rs`) composes
  `verify_agent_run` (chain genuine + ordered + single-signer; consumed ≤ budget at the tip)
  and adds the headroom-identity and per-step within-budget teeth. **Honest trust:** the HOST
  runs the signer, so R0 alone is tamper-evidence, not host-independence.
- **R1 — the renter finality anchor.** `RenterAnchor` (`lib.rs`: a genesis nonce + the
  renter's countersign pubkey, whole or absent) supports the `GET`/`POST <host>/checkpoint`
  protocol (`checkpoint_offer`/`submit_checkpoint`). `verify_for_renter`
  (`grain-verify/src/lib.rs`) requires the anchor and checks **anti-truncation** (≥ num_turns
  receipts shown) and **anti-rewrite** (the receipt at the acknowledged position hashes to the
  countersigned `head_root`) against a **renter-held** key the platform cannot forge.
- **R2 — actions become kernel turns, receipts become views.** `drive_serving` welds every
  action to a committed executor turn (`grain-turn`), and `verify_r2` rejects any receipt not
  linked to a turn in the committed-turn manifest. **Honest trust:** R2 makes the meter a
  kernel caveat and binds each receipt to a committed turn, but **still trusts the executor
  host** that committed the turns — it does not re-execute them (`grain-turn/src/lib.rs`,
  "Honest scope (R2, not R3)").
- **R3 — the whole-history STARK leg (THE NAMED GAP).** `grain-verify` re-executes **nothing**;
  it ships "the maximal real subset over `verify_agent_run`: tamper-evident + renter-anchored
  + kernel-linked, not unfoolable." The exact machine-readable ask is the exported constant
  `grain_verify::WHOLE_HISTORY_GAP` (`grain-verify/src/lib.rs`): `dregg_lightclient::verify_history`
  needs each grain turn minted as a **rotated wide-anchored EffectVM leg** (`FinalizedTurn`
  publishing the 8-felt Poseidon2 wide state-commit roots the recursion folds) — a
  breadstuffs-side build in `grain-turn`, not a wiring gap this crate can close. Until then,
  R3 is VK-terminal.

**The honest trust, stated plainly:** R2 trusts the executor host that committed the manifest
turns. R3 (whole-history STARK) is what would remove that trust — and it is a named, unbuilt
seam, not a shipped guarantee.

## The durable metered lease (`hosted-lease` × `hosted-durable`)

`HostedLease` (`hosted-lease/src/lib.rs`) is built on the proven `starbridge_execution_lease`
capacity: the durable image is the lease cell's committed `EXEC_COLL` heap, the checkpoint
cursor is `Monotonic` (a rewind/forge is a real executor refusal), and metering rides one of
two `Metering` modes:

- **`Metering::Obligation`** — a `StandingObligation` cursor metered per period, PAID by a
  separate settlement draw (meter and pay are two enforced pieces coupled by control flow).
  `meter` / `lapse_if_behind`.
- **`Metering::Prepaid`** — the FUSED `dregg_cell::prepaid_lease` capacity: `check_bill` (gate)
  / `discharge` (the one atomic meter-advance ⊗ reserve-draw). This is the drift-unrepresentable
  path `agent-platform` rents on.

`hosted-durable` supplies the value rail the platform's biller binds to (`hosted-durable/src/settle.rs`):
the `Settlement` trait is **conserving** (Σδ=0) and **exactly-once** (per `(lease_id, period)`).
Backends: `PayableSettlement` (production — one conserving `Effect::Transfer` turn over an
injected `PaySubmitter`), `DurableSettlement` (restart-surviving write-ahead ledger),
`TestConservingLedger` (the explicit in-process double — NOT a production path; its move still
runs through the proven `apply_conserving_transfer` primitive).

## Fork / rewind / branch-and-stitch (`grain-fork`)

Because the mind is a real committed cell, everything proven about cells becomes true of it
(`grain-fork/src/lib.rs`):

- **`Grain::fork`** — copy the mind's committed image at its checkpoint root into a child under
  its OWN cap-confined lease. State copies; **value and authority do not duplicate** (the mind
  carries no balance; the child gets only deliberately-conferred caps the parent holds —
  `UnconferrableCap` otherwise). The child's lease genesis IS the parent's checkpoint root
  (provable common ancestry).
- **`Grain::rewind`** — restore the mind to an earlier committed root, **fail-closed** on a
  boundary mismatch: the reified image must re-derive its sealed root under the kernel's real
  `compute_heap_root` / `compute_fields_root`, else the restore is refused (`BoundaryMismatch`)
  and the live mind is untouched.
- **`stitch` + `Grain::absorb`** — merge a child's divergent state back through the PROVEN
  field-granular pushout (`stitch_projections`) + the settlement-sound authority gate
  (`settle_umem_stitch`), CONSUMED from `starbridge_v2::umem_membrane`, not reimplemented.
  Disjoint learnings fold clean; a same-address clash is a first-class `UmemConflict` (never
  silent last-writer-wins); a cap revoked between branch and settlement is LINEAR-DROPPED at
  the tip. `absorb` is fail-closed three ways (`ForeignStitch` / `NotSettled` / `AbsorbDivergence`),
  staged on a scratch copy so a refusal never touches the live mind.

**`ConfinedSession::fork_two`** (`grain-fork/src/confined.rs`) lifts this onto a live confined
session — ONE checkpoint yields TWO sovereign lives, each with the four teeth: **sovereign**
(own lease/mind/confinement/receipt chain), **attenuated never amplified** (egress ⊆ parent,
caps ⊆ parent-held), **budget-conserving** (the two shares SUM to ≤ the parent's — the reserve
is SPLIT, not minted, `BudgetOverdraw` otherwise), and **independently verifiable + isolated**
(each child's receipt chain is a fresh hash chain rooted at the SHARED fork root; a turn in one
touches neither the other's mind nor its chain).

## The grain-commons app-store (`grain-commons`)

The design principle is **compose, don't reimplement** — every load-bearing guarantee is an
existing proven primitive wired into a market shape (`grain-commons/src/lib.rs` table). The
four faces:

1. **Package & publish** (`package.rs`) — an `AgentConfig` (cap bundle + budget + brain +
   roles) packaged as a **real signed Sandstorm `.spk`** via `sandstorm_bridge::SpkBuilder`.
   **Provenance IS the key**: the App ID is the author's Ed25519 signing key
   (`Spk::app_id`); `install` verifies the signature before returning any config, so a single
   tampered byte yields no installable grain. `install` also cross-checks the signed manifest's
   facets against the embedded config's cap bundle (`ConfigManifestMismatch`).
2. **List & rent** (`registry.rs`) — listing cells in a committed umem heap; discover by App
   ID; `rent` prices a `RentQuote` (honestly a quote — the numbers feed the real lease); review
   is a receipted turn leaving a `GrainReceipt`.
3. **Fork with pedigree** (`fork.rs`) — `fork_from_package` restores a committed `/var` backup
   into a fresh grain under a new owner, minting a `Pedigree` Merkle path. Trust is DERIVED from
   three teeth bound at mint: the author is a signature-verified App ID, the backup provably
   belongs to that app (`ProvenanceMismatch` / `data_root` re-witness), and — decisively — the
   backup carries a valid OWNER SIGNATURE over `(app_id ‖ data_root)` (`BadBackupSignature`).
   A hand-built `Pedigree` is NOT authenticated by `traces_to`; the gate is the mint-site
   refusal (documented honestly in `fork.rs`).
4. **Hatch bounded sub-agents** (`hatchery.rs`) — a `GenesisAgent` mints a `HatchedSubAgent`
   with a **forever-invariant** baked into a `FactoryDescriptor` the executor re-evaluates on
   every turn of the child's life (`MintedKind::evaluate_transition` → a genuine kernel
   `ConstraintViolated`), endowed with a **strict cryptographic attenuation** of the genesis
   agent's caps on the real `dga1_` powerbox rail (`attenuate_grain_cap`; `granted_permissions`
   reads back the crypto-derived facet set).

## Two named cross-crate welds (honest, from the code)

- **The registry↔lease weld.** `grain-commons`'s `RentQuote` and `ListingTerms` deliberately
  do NOT ship a shadow lease; feeding those numbers into `hosted-lease::HostedLease` /
  `grain-fork::Grain::rent` is the named reconcile "once the detached crates join one
  workspace" (`registry.rs` module docs). Both `grain-turn` and `grain-fork` are workspace
  `members` but NOT in `default-members` (Cargo.toml) — detached like the forge crates.
- **The two fork surfaces.** `grain-commons::fork` forks the *hosting image* (`/var` backup +
  pedigree, provenance across owners); `grain-fork` forks the *committed kernel mind* (cell heap
  + rewind + proven stitch). The named weld is to make the backup's `data_root` BE the mind's
  committed checkpoint root, so a pedigree fork point and a `grain-fork` ancestor root are the
  same 32 bytes (`grain-commons/src/fork.rs` module docs).

## A real finding

The module and Cargo docs across `agent-platform`, `grain-commons`, and `grain-verify` cite a
vision doc at **`docs/THE-GRAIN.md`** ("THE-GRAIN.md face #1/#2/#3", "§Commons") — but that
path does not exist in the tree. The present vision docs are `docs/deos/GRAIN-HOMESERVER.md`
and `docs/deos/GRAIN-CONFINED-BODY.md`. The references are stale pointers, not a code defect.
