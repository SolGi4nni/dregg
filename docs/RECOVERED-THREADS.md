# RECOVERED THREADS — valuable work the dreggfi sprint buried

*Mined 2026-07-13 from the `cv` session corpus (2668 sessions) + HORIZONLOG + the
git-tracked FINDING/DESIGN/GOAL docs. Read-only recovery pass.*

**The shape.** `cv stats`/`cv timeline` show the fleet's centre of gravity swung hard
to the **dreggfi / DrEX / launchpad / multichain-settlement** wave from ~2026-07-08 on
(86 breadstuffs sessions on 07-11 alone; every top-`cv ls` session since is titled
"Explore LayerZero…", "stark-verifier-soundness-audit", "VK-epoch recursion-verifier",
"Migrate to breadstuffs"). The lanes that were *live the week before the pivot*
(07-05 → 07-10: federation, distributed-deos, storage, the layout allocator, the audit
envelope) went quiet mid-stride. Below are the threads that were **real work** — a green
build, a diagnosed bug, a landed foundation with the next rung named — not just ideas,
that the sprint pulled attention off of.

Honesty tags: **BUILT-STRANDED** (green/working, not integrated or not followed) ·
**DIAGNOSED** (bug found + fix designed, not built) · **FOUNDATION+RUNG** (green base
landed, named next rung unbuilt) · **STALLED-LANE** (an active GOAL lane that went quiet).

---

## Ranked recoveries

| # | thread | state | value now | re-pickup |
|---|--------|-------|-----------|-----------|
| 1 | Federation triad: checkpoint-unwired · state-field truncation · federation-wide settlement | DIAGNOSED (3 docs, 07-10) | HIGH — blocks federation-wide reads the DrEX proof-of-holdings frontier needs; truncation is a **live silent data-loss bug** | reachable→medium |
| 2 | Verified layout **optimizer** (above the landed allocator) | FOUNDATION+RUNG | HIGH — retires the stark-kill hand-AIR grind + is the game-engine "verified allocator" keystone | medium→big |
| 3 | Witnessed-nondeterminism **audit envelope** (`dregg-agent/envelope.rs`) | BUILT-STRANDED (1142 LoC, 07-12) | HIGH — turns DreggCloud's hosted-agent "audit rail" from prose into a running dispute-settler | medium |
| 4 | Crown-lowering **assurance ladder** (general auto-lift + TEE rung) | FOUNDATION+RUNG | HIGH — the one gadget the game-engine D-crown, DreggCloud, and forge all hand-crank around | medium |
| 5 | distributed-deos lane — the sovereign live image across machines | STALLED-LANE (quiet since 07-07) | MED-HIGH — the "distributed inhabited world"; one sharp named residual left | medium |
| 6 | deos self-hosting named-seams residue (service-registry panel · reify_seam Lean · derivative-matching St.4) | BUILT-STRANDED ×3 | MEDIUM — each is a LANDED capability one small closure from complete | reachable each |
| 7 | Storage north-star tail — the **decentralized provider market** | FOUNDATION+RUNG | MEDIUM — the erasure/PoR/sharding crate is built; the live multi-provider market is the unbuilt north star | medium |
| 8 | Moldable inspectors → the **reflective cockpit** | FOUNDATION+RUNG | MEDIUM — L1–L10 inspectors shipped (06-24); the reflective cockpit above them is unbuilt | medium |

Grounded-but-forward (real footing, not stranded builds — lower recovery urgency):
**polisware** (66 `Polis/*.lean` + project doc, Andy-Ayrey pull) · **distributed-houyhnhnm**
(Settlement Soundness proven+wired; forward = patch-theory→document-language) ·
**Midnight/ZKIR v3** (scout-only) · **rhizomatic** (ongoing metabolize).

---

## Detail

### 1. The federation triad — three bugs surfaced 07-10, buried by 07-11 (HIGH)
Three git-tracked FINDING docs were written on 2026-07-10 (`docs/FINDING-*.md`), the day
before the 86-session multichain surge. Each names a concrete, buildable close; none was
acted on:

- **`FINDING-checkpoint-pipeline-unwired.md`** — the qc-bearing `dregg_federation::Checkpoint`
  is dead code: `persist::store_checkpoint` has **zero callers**, nothing constructs a
  `Payload::Checkpoint`, the node's `FinalizedBlock::Checkpoint` arm was a no-op. The doc's
  own verdict: **don't** wire the checkpoint; build the *ledger-state inclusion* path instead
  — a `GET /api/cell/{id}/proof` endpoint riding the already-live attested-root quorum
  (~2-3 days). **This is exactly the federation-wide read the DrEX/multichain non-custodial
  proof-of-holdings story needs** — it composes directly with the current frontier.
- **`FINDING-state-field-truncation.md`** — a cell's 32-byte state field is **truncated to its
  low 8 bytes** the first time any turn touches the cell (`setField` is a scalar u64 lane
  end-to-end: `metatheory/Dregg2/Exec/Effect.lean:98`, `field_from_u64`). A full cell id
  stashed in a heap slot becomes a non-existent id → downstream payment/settlement silently
  stops. **This bites anything that parks a 32-byte identity in a scalar slot — including the
  bridge/dreggfi path that stores chain ids/addresses.** Acute fix (per the doc): relocate
  32-byte identities into a `Ty.digest` side-table (`circuit/src/effect_vm/helpers.rs:122`),
  not `PROVIDER_SLOT`. Full kernel widening is correctly sequenced with the v13 faithful-fields
  epoch — but the acute relocation is buildable now.
- **`FINDING-federation-wide-settlement.md`** — metered lease rent only settles on the node
  that owns the lease; federation-wide replication needs the lease-*program* discharge path,
  not a plain operator `Transfer` (~1 week, the kernel-parity constraint work is the crux).
  Composes with DreggCloud metered rent.

*Where:* `docs/FINDING-{checkpoint-pipeline-unwired,state-field-truncation,federation-wide-settlement}.md`.
*Corpus:* the 07-10 swarm; `~/dev/DreggNet/docs/FEDERATION-WIDE-READ.md` (Option B).

### 2. The verified layout OPTIMIZER — foundation green, optimizer designed (HIGH)
The **allocator foundation landed green** and is fresh (Phase 1 → 2c commits through
2026-07-13: `f66f2c7c4` RotatedLayout, `e58fd19e6` complete-tiling theorem, `0486f2e56`
emit-derives-from-layout, `dd467d6d9` Rust-side Legal disjoint-tiling guard,
`c52b3890d` groupTable). What is **designed but unbuilt** is the *optimizer* above it:
untrusted layout search whose output is checked by a refinement proof (translation
validation) → "write nice, get efficient, get verified." `docs/DESIGN-verified-layout-optimizer.md`
(07-12, post-4-scholar census) documents the disease it retires: the disjointness invariant
that caused the revoked-root 178-limb 14-file flag-day is **machine-checked nowhere** — held
by a comment (`EffectVmEmitRotationV3.lean:1695`); `NUM_PRE_LIMBS=178` is declared 3× by hand.
Composes with **stark-kill** (the ~45 hand AIRs) and the **game-engine "verified allocator
keystone"** (`docs/GAME-*`). *Where:* `docs/DESIGN-verified-layout-optimizer.md` + the
landed `RotatedLayout` Lean.

### 3. Witnessed-nondeterminism audit envelope — 1142 lines built, not wired (HIGH)
`dregg-agent/src/envelope.rs` is a **1142-line built module** (07-12) implementing
deterministic-replay-under-a-witnessed-nondeterminism-envelope for the agent loop: given a
turn's initial state + a sealed record of every nondeterministic input, an auditor re-executes
and reproduces every admission/refusal/meter-draw/receipt byte-for-byte (honest ceiling: LLM
outputs are captured-as-input, not re-derived — stated up front in the doc). What's missing is
the **wire into the live `AgentCloud::drive_state` loop + an auditor-replay CLI**. This is the
mechanism that makes DreggCloud's hosted-agent "audit rail" a *running* dispute-settler instead
of a narrative log — high leverage for the cloud/forge product. *Where:*
`docs/DESIGN-witnessed-nondeterminism-envelope.md` + `dregg-agent/src/envelope.rs`.

### 4. Crown-lowering assurance ladder — primitive landed, generalization designed (HIGH)
`docs/DESIGN-crown-lowering-and-assurance-ladder.md` (07-11) named "the single highest-leverage
less-LARPing move": `ConstraintExpr` had **no inequality primitive**, so every ordering tooth
(`FieldGte`/`Monotonic`/…) reached the circuit only by a hand-authored bit-decomposition per
rule — the bottleneck the game-engine D-crown, DreggCloud's honest-rung, and the forge all
hand-crank around. The **inequality/range gadget landed** (`97679f369` 07-11 + `323e08663`
multi-limb u64-slot). Still designed-not-built: the **general "any executor rule auto-lifts to
the crown" gadget** + the **TEE assurance rung**. One gadget, three efforts converge.

### 5. distributed-deos — the sovereign live image across machines (MED-HIGH)
`GOAL-DISTRIBUTED-DEOS.md` lane went quiet after 2026-07-07 when multichain took over. It got
far first — homeserver-as-a-grain COMPLETE (`45777b5cf`), confined Matrix homeserver serving
200 through the jail. The sharp **stranded residual** (`435746047`, 07-07): Pillar-2b
"identical cap on any box" holds only **in-process** — the `NodeWorldSink` crawl **drops the
c-list** (the node exposes an edge *count*, not the edges). That's the one seam between "runs
on my box" and "the distributed inhabited world." *Where:* `GOAL-DISTRIBUTED-DEOS.md` + the
`NodeWorldSink` crawl.

### 6. deos self-hosting named-seams residue (MEDIUM, reachable each)
From the 2026-06-24/25 self-hosting cluster (HORIZONLOG §§915–1066), several capabilities
LANDED with a small named closure that the pivot buried:
- **service-registry cockpit panel + serviced-answer** — `invoke()` + the SERVICE EXPLORER
  landed end-to-end (`bc954216f`); the registry-wire UI (register a descriptor) and surfacing
  the refused Serviced answer as a read-only bound row are the seams (HORIZONLOG:992).
- **`reify_seam` Lean uproj-injectivity** — closed at the value level; the Lean proof of the
  four value-planes `project_cell` doesn't yet carry (heap preimage, …) is the seam
  (HORIZONLOG:1048).
- **derivative-matching Stage 4 table-equality** — Stages 0/1/3 kernel-clean over dregg's
  `Pred`; Stage 4 language-half done, table-equality unblocked (HORIZONLOG:977).

### 7. Storage north-star tail — the decentralized provider market (MEDIUM)
The storage extraction *landed* (GOAL.md: 13 soundness fixes closed by 07-07; `storage/` crate
is real — `erasure.rs`, `durability_deal.rs`, `sharding.rs`, `placement.rs`, `operator.rs` PoR,
active to 07-11 `5be9afae7`). The unbuilt **north star** is the live *decentralized provider
market* (multi-provider deals + market clearing over the durability deals). Also parked, genuinely
ember-gated: the `canonical_32_to_felts` per-caller exploitability audit / 9-felt injective VK
regen (GOAL.md round-4 tail). *Where:* `GOAL.md`, `storage/`.

### 8. Moldable inspectors → the reflective cockpit (MEDIUM)
L1–L10 moldable inspectors over 151 types shipped (06-24; `cv` agents `agent-a3/a4`). The
**reflective cockpit** above them (the cockpit inspecting/molding itself) is the named-but-unbuilt
next rung. *Where:* memory `project-moldable-inspector-epoch.md` + the 06-24 sessions.

---

## Verified-CLOSED (checked so this mining is trustworthy — do NOT re-open)
These looked like candidates but `cv`/git show them genuinely finished:
- **IVC #1 same-endpoint mixed-root forgery** — GENUINELY CLOSED, codex-confirmed by 4 arbiters
  (`ef0b08d19`, 06-25) + streaming-path port (`c5b609700`). HORIZONLOG's "BUILT but BLOCKED" is stale.
- **WASM executor wall-clock** (`Instant::now` panic on wasm32) — FIXED, a real verified turn
  fires in-browser (`3423a08ae`, 06-24).
- **promise-pipelining lift of `yield_point`** — LANDED as captp executable promise pipelining +
  N-party coordination, driven live (`bbedc4a8e`, `43dd06e5c`, `c2fee36c7`).
- **storage extraction / audit_run / vat wire** — CLOSED (GOAL.md rounds 3–4).
- **dregg-doc (document foundation web)** — ACTIVE, not lost (last touched 07-13, `90d0f381e`).

---

## Top 3 to re-pick-up now

1. **The federation triad (#1), starting with the `/api/cell/{id}/proof` federation-wide read** —
   it's the read the DrEX/multichain proof-of-holdings frontier is already reaching for, ~2-3 days,
   and the **state-field truncation is a live silent data-loss bug** that can bite the bridge path.
2. **Wire the audit envelope (#3)** — 1142 lines are already built; the loop-wire + a replay CLI
   converts DreggCloud's audit rail from a claim into a running dispute-settler.
3. **The layout optimizer (#2) / crown-lowering generalization (#4)** — the allocator + inequality
   foundations landed *this week*; the optimizer/auto-lift rung on top retires the stark-kill hand-AIR
   grind and unifies the game-engine, DreggCloud, and forge onto one gadget.
