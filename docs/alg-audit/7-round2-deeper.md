# Alg-Complexity Audit 7 — Round 2, deeper (2026-07-07)

Round 1 (`docs/ALG-COMPLEXITY-AUDIT.md` + `docs/alg-audit/1-6-*.md`) reported each lane's TOP 5
and swept some areas shallowly. Round 2 hunts the rest of the same `tauOrderFast` class:
**`Vec`/`List` linear-scan where a `HashMap`/`HashSet` belongs, or recompute where a cache belongs,
on an input that grows with the chain / ledger / history / session / receipt-log.**

Two work streams:
- **(A) The TAIL** below round-1's top-5 in the six already-covered areas — promoted growing-with-use items.
- **(B) The UN-audited / shallow areas** — a 6-lane parallel sweep of `sdk/**`, `bridge/**`, `intent/**`,
  `starbridge-apps/**` (~40 apps), `app-framework/**`, `agent-platform/**`, `dregg-agent/**`, `grain-*`,
  `hosted-*`, `captp/**`, `net/**` (deeper), `dregg-query/**`, `verifier/**`, `lightclient/**`,
  `credentials/**`, `directory/**`, `dregg-auth/**`, the `starbridge-v2` cockpit + `deos-*`, `dregg-dsl/**`,
  and the long tail of small crates (`auditable-fund`, `spween-dregg`, `zkoracle-prove`, …).

**Headline of round 2:** the sharpest *new* class is the **gpui cockpit's per-REPAINT full-history
rescans** — worse than a per-request scan because they fire on every `cx.notify()` (keystroke,
mouse-move, tick), not once per turn. Second is a **shared `LocalNode::contains` linear-log-scan root**
that makes three independent verify paths (agent-platform `verify_landed`, `auditable-fund`,
`grain-verify`) O(n²) in session length. Third is the **light-client acceptance gate** counting quorum
with an O(votes²) `Vec` dedup, run 2–3× per verification.

---

## RANK (severity = complexity × frequency × what-grows)

### 🔴 Tier 1 — hot path, grows with history/receipts/session (fix first)

| # | derp | file:line | complexity | grows with | fix | class |
|---|------|-----------|-----------|-----------|-----|-------|
| B1 | Cockpit **Provenance Walker** re-derives all effects+rows every paint (self-described "never a cache") | `starbridge-v2/src/deos_desktop/mod.rs:6414-6443` | O(receipts + steps·eff)/**paint** | recorded steps + receipt log | memo keyed on `world.height()`; receipt-hash→idx `HashMap`; build only shown window | needs-design (trivial height key) |
| B2 | Cockpit **desktop icon census** — 2 linear scans per cell per frame; offers add cells → O(cells²) | `mod.rs:4982,4986` → `app_shelf.rs:153`, `exchange_floor.rs:310` | O(cells·(apps+offers))/**frame** | installed apps, exchange offers, cells | `HashMap<CellId,(kind,glyph)>` face-index, O(1) `.get` | **cheap-win** |
| B3 | **Light-client quorum** count — O(votes²) `Vec` dedup + O(votes·committee), run 2–3× per verify | `lightclient/src/lib.rs:337-357,361-371` (called ×2–3 at `:630,632,640`) | O(votes²) × ~3 / **verify** | validator/committee vote set | `HashSet` dedup; hoist `committee` to `HashSet` once; compute `distinct_committee_signers` once | **cheap-win** |
| B4 | **`LocalNode::contains` linear log scan** — the shared root under 3 verify paths | `agent-platform/src/node.rs:152` (`log…iter().any`) | O(F) per call | node finalized log | maintain `HashSet<[u8;32]>` of finalized turn_hashes in `LocalNode` (populate in `land`) | **cheap-win** (one struct) |
| B5 | ↳ `verify_landed` loops committed_turns × `node.contains` → O(M·F) | `agent-platform/src/lib.rs:1044` | O(M·F) / **verify** | grain session history | snapshot `HashSet` once (or fix B4) | **cheap-win** |
| B6 | ↳ `audit_fund` loops records × `node.contains` → O(n²) (independent-auditor entry point) | `auditable-fund/src/audit.rs:123` | O(n²) / **audit** | fund ledger (finalized turns) | `let on_chain: HashSet = node.turn_hashes().collect()` before loop | **cheap-win** |
| B7 | ↳ `check_turn_links` loops receipts × `committed_turns.iter().any` → O(R·T) | `grain-verify/src/lib.rs:576` | O(R·T) / **R2 verify** | session history | hoist `committed_turns` into `HashSet` before loop | **cheap-win** |
| B8 | Cockpit **Cell Inspector** — 2 full receipt-log scans per open inspector per repaint | `mod.rs:5236,5314-5333` → `rewind.rs:339` | O(receipts)×2 / **paint** | receipt log | `HashMap<CellId, Vec<receipt_idx>>` appended on commit | needs-design (tracks live append + rewind) |
| B9 | Cockpit **App Shelf** — receipt scan per installed app per repaint | `starbridge-v2/src/deos_desktop/app_shelf.rs:514` → `cell_receipt_count` | O(apps·receipts) / **paint** | receipt log | shares B8's per-cell receipt index | needs-design (shares B8) |

### 🟠 Tier 2 — per-op / per-request, grows with app-state or committee

| # | derp | file:line | complexity | grows | fix | class |
|---|------|-----------|-----------|-------|-----|-------|
| B10 | billing `invoices_for` rescans whole event pool per account → O(A·E)≈O(E²) | `starbridge-apps/billing/src/invoice.rs:359,194` | O(A·E)/run | usage-event pool | one pass bucketing `BTreeMap<acct,BTreeMap<res,LineItem>>` | **cheap-win** |
| B11 | credentials `rebuild_root` sorts+rehashes whole revoked set per revoke → O(n²log n) | `credentials/src/revocation.rs:116,250` | O(n log n)/revoke | revocation registry | `BTreeSet` (kills per-op sort); incremental root = needs-design | cheap-win + needs-design |
| B12 | `verify_attested_root_ed25519` `known_keys.contains` per sig → O(committee²) | `verifier/src/cross_fed.rs:473` | O(committee²)/verify | committee | `HashSet<&PublicKey>` once (mirror the `seen` set) | **cheap-win** |
| B13 | intent gossip `our_intent_ids: Vec` — `contains` in `receive` + nested in `rematch_all` | `intent/src/gossip.rs:226` (scan `:381,:602`) | O(pool·our_intents) | our published-intent set | `HashSet<[u8;32]>` (siblings already `HashMap`/`HashSet`) | **cheap-win** |
| B14 | sdk sealed-governance `nullifiers: Vec` dedup per ballot → O(n²) | `sdk/src/sealed_governance.rs:567,652` | O(n²)/election | ballots/voters | parallel `HashSet` beside the ordered Vec | **cheap-win** |
| B15 | **coord `sync_from_blocklace`** — `virtual_chain` (whole-DAG scan+sort) once per participant | `coord/src/shared_budget.rs:412` → `finality.rs:895` | O(P·N)/sync | blocklace DAG × participants | one pass over DAG grouping debits by creator into `HashMap<creator,u64>` | **cheap-win** |
| B16 | spween-dregg `verify_chain_linkage` `seen: Vec` dedup → O(n²) | `spween-dregg/src/verify.rs:101` | O(n²)/verify | playthrough receipt log | `HashSet::insert` returns dup flag | **cheap-win** |
| B17 | agent-host account registry `find_by_account`/`find_by_key` linear | `agent-host/src/lib.rs:321,326` | O(N)/login | agent/account roster | side `HashMap<key,idx>` indexes, rebuilt on (rare) writes | **cheap-win** |

### 🟡 Tier 3 — proof/verify recompute-from-scratch (incremental structure belongs)

| # | derp | file:line | complexity | grows | fix | class |
|---|------|-----------|-----------|-------|-----|-------|
| B18 | `nullifier_set::prove_non_membership` + `root()` rebuild the full Merkle tree over ALL nullifiers per proof | `cell/src/nullifier_set.rs:130,135` (+ `root()`) | O(n)/proof | spent-nullifier set | incremental sorted-tree root (a HEAD design commit `1d05c350c` is already moving here) | needs-design |
| B19 | supply-chain / agent-provenance `verify_chain` re-folds the entire custody chain per call | `starbridge-apps/supply-chain-provenance/src/lib.rs:315`; `agent-provenance/src/lib.rs:143` | O(n)/verify, O(n²) if per-append | handoff/claim history | cache `(len, prev_digest)`, fold only the new tail | needs-design (repeats across both) |
| B20 | `check_no_amplification::rec` deep-clones the whole granted-cap `BTreeMap` per call-tree node | `dregg-userspace-verify/src/lib.rs:426` | O(nodes·caps) | attacker-influenced call forest | port onto `GrantedScope::Layer` chain (`fused_walk` at `:762` already does) | needs-design (fix already in-repo) |

### 🟢 Tier 4 — tail, bounded-by-committee / off-hot / config (note only)

- **`blocklace/src/constitution.rs` `participants: Vec<[u8;32]>`** — `contains`/`retain`/`dedup`
  (`:65,86,117,131,170,173`). The **deployed twin** of Lean round-1 #5 (`MembershipSafety`/`EpochReconfig`).
  Grows with the committee over the network's life, but committee-bounded and per-reconfig (rare) — same
  "REFUTED (bounded by committee) *today*" verdict. `HashSet` twin when committees scale.
- **`blocklace/src/finality.rs` `finality_of`** — `ordering.ordered: Vec` linear `contains` (`:462`); only
  reached by `preflight/src/checks/blocklace.rs` today (not a hot loop). `causal_past` (`:908`) is an
  uncached BFS rebuilt per call — fine as a primitive, an O(N²) hazard only if looped
  (`is_predecessor` at `:972` calls it fresh; no live loop caller found).
- **`federation/src/node.rs:355`** `collected_votes.iter().any(v.voter==…)` — per-reconfig-round vote dedup,
  committee-bounded. `federation/src/epoch.rs:220,366,499` member scans — committee-bounded. Low.
- **`starbridge-apps/polis` `CouncilCharter::validate`** — O(n²) `members[..i].contains` dedup at
  `:498,:515` (copy-pasted twice) — `MAX_MEMBERS`-capped, build-time only. Skip in practice; `HashSet`
  seen-set if the pattern is ever templated wider.
- **`dregg-deploy/src/refine.rs:546`** NFA subset-construction `Vec<Proc>` dedup — O(states²) bounded by the
  process automaton (4096-iter cap), not manifest/ledger growth; `Proc` isn't trivially `Hash`. Low.
- **`intent/src/solver.rs:508` `build_graph_cached`** rebuilt each greedy iteration — O(max_results·n²), but
  `max_results` is config-bounded and the expensive `is_compatible` sweep is already cached. Low.
- **`bridge/src/present.rs:591`** each attenuation step clones the accumulated fact set → O(k²) memory over
  attenuation depth `k` (short/bounded in practice). Low.

---

## Notable per-finding detail

### B1–B4 / B8–B9 — the cockpit per-repaint receipt/step rescan cluster (the sharpest new class)

The gpui cockpit (`starbridge-v2/src/deos_desktop/`) rebuilds views from the live `World` on **every
paint** — and paint fires on every `cx.notify()`. Four open-window bodies each re-scan the *fastest-growing*
structures (the receipt log and the recorded-step log) from scratch every frame:
- **Provenance Walker** (`mod.rs:6414`) maps `effect_kinds` over *all* committed steps, walks all receipts
  into rows, and `find`s the selected row — then renders only the last 48. Its own comment advertises
  "re-derived by `walk_rows` on every paint … never a cache", i.e. the anti-pattern is intentional and
  documented.
- **Cell Inspector** (`mod.rs:5236,5314`) and **App Shelf** (`app_shelf.rs:514`) both funnel into
  `cell_receipt_count` → `rewind.rs:339` `p.receipts.iter().filter(|r| r.agent==cell).count()` — an O(receipts)
  filter per open inspector / per installed app, per frame.

The whole cluster collapses to **one shared design fix**: a per-`world.height()` memo plus a
`HashMap<CellId, Vec<receipt_index>>` appended as receipts commit, so the ever-growing log is never
re-scanned on paint. **B2 (icon census)** is the one pure cheap-win in the cluster: two `HashMap<CellId,
face>` indexes updated on install/offer-post, replacing `installed.iter().find` / `offers.iter().find`
run per icon per frame (and offers *add* cells, so this is quietly O(cells²) as the exchange floor fills).

### B4–B7 — the `LocalNode::contains` linear-log-scan root

`agent-platform/src/node.rs:152` `pub fn contains(&self, turn_hash) { self.log.lock()…iter().any(…) }` is
an O(F) scan of the whole finalized log. Three independent verify paths call it inside a loop over a second
per-session-growing list, each turning O(n²) in session length:
- `agent-platform/src/lib.rs:1044` `verify_landed` — the renter/light-client verify path,
- `auditable-fund/src/audit.rs:123` `audit_fund` — the independent-auditor entry point (the crate's whole
  purpose is trustless re-verification),
- `grain-verify/src/lib.rs:576` `check_turn_links` — the same shape with a local `committed_turns: Vec`.

Fix the root once (a `HashSet<[u8;32]>` of finalized turn_hashes in `LocalNode`, populated in `land`) and
all three drop to O(M+F); the call sites can also each hoist a one-shot `HashSet` snapshot.

### B15 — coord `sync_from_blocklace` (new; round-6 covered `coord/budget.rs`, not `shared_budget.rs`)

`coord/src/shared_budget.rs:411` loops participants and calls `blocklace.virtual_chain(&creator_key)`
(`finality.rs:895`: `self.blocks.values().filter(|b| b.creator==creator).collect()` + `sort_by_key`) — a
full scan+sort of the **whole DAG per participant**, O(P·N), recomputed from scratch. This is the documented
P2P-without-ordering-nodes mode (`plans/shared-resource-budget.md`); the file even comments that an
alternative avoids re-scanning full virtual chains. Fix: one pass over the DAG grouping per-resource debits
by creator into a `HashMap<creator,u64>`, then assign — O(N) instead of O(P·N).

---

## CHECKED & CLEARED (round-2 sweep is legible)

- **bridge** — all replay/dedup sets already `BTreeSet`/`HashSet` (`solana_mirror` `seen_locks/redeems`,
  `stripe_mirror` `seen_payments`, `trustless` senders/receivers). `midnight/mina_observer` `find`s are in
  `#[cfg(test)]` mock RPCs.
- **captp** — export/import/question/answer tables are all `HashMap<CellId,…>`; GC is single `retain`/`filter`
  passes; data-plane subscriber lists per-topic bounded. No O(n²) over a growing global table.
- **net** (beyond the two round-5 gossip items) — `seen`/`index`/`anchors`/`message_cache` are
  `HashSet`/`HashMap`; the `contains` hits at `gossip.rs:2243/2356/2462/1972/1951` are HashSet O(1);
  `peer_score` eager-set is bounded-fanout. No NEW O(n²).
- **dregg-query** — `eval` is an explicit hash-join with per-atom `build_join_index` + anti-join HashMap.
  Index-optimized. **dregg-merge** — set `union`/`contains` on element-id sets, O(1).
- **directory** — records keyed by `HashMap`; `discover` is a single `values().filter()` with a per-record
  bounded tagset. `directory_diff` `position` is test-only.
- **dregg-auth** — credential-chain verify is a single linear pass; `verify_discharged` is bounded by
  attenuation depth / third-party-caveat count.
- **deos-reflect / deos-view / deos-js / deos-js-runtime / deos-web-cells / dregg-dsl / dregg-dsl-runtime /
  dregg-sandbox** — hot-spot membership tests are over `HashSet`/`BTreeSet` or per-cell/per-bundle bounded
  lists; codegen/proof-composition are one-shot, not per-frame. Flagged `.contains`/`.find`/`.position`
  hits are in `#[cfg(test)]` or bounded by fixed circuit/tree structure.
- **app-framework** — affordance/method/cell/asset lookups are over bounded static app-spec surfaces;
  `agent_coordination` already uses `HashSet` + Kahn layering.
- **dregg-agent / grain-* / hosted-lease / hosted-durable / sandstorm-bridge / http-serve / dregg-ipfs** —
  grant-covering is cap-set bounded; receipt/log verifies are single O(n) passes; confined-swarm's O(n²)
  cross-contact matrix is the intended pairwise-product result, not an accidental scan.
- **starbridge-apps (~40)** — overwhelmingly stateless DEOS effect/constraint generators with **zero**
  `self.<field>.push` in `src/`; the few stateful cores (gallery `submissions`, sealed-auction/tussle
  `commitments`) already use `HashSet`/`BTreeMap`. Only billing (B10), supply/agent-provenance (B19), and
  the bounded polis validator surfaced.
- **collective-choice / commons-arbiter / attested-dm / dregg-payable / mud-dregg / zkoracle-prove /
  deco-prove / preflight / redteam / perf / dregg-storage-templates** — electorate/jurisdiction/voter sets are
  `BTreeSet`/`HashSet`; `dregg-payable` routes through a verified DFA (not linear `find`); the compact
  cfg-attestation path (`prove/verify_cfg_compact`) is single-pass with O(1) indexed `grammar.get` (the O(n²)
  `leftmost_chain`/`produces`/`expand_compact` are test/interop only). Clean.
- **webauth-core / observability / dregg-analyzer** — config-set `contains`; `dregg-analyzer`'s
  O(equivocators·blocks) is an offline one-shot forensic report (equivocators normally empty).

## NOT deeply swept (low-value remainder, no priority-area gap)

Protocol primitives and UI shells not on any growing-state hot loop: `macaroon`, `token`, `tokenizer`,
`secrets`, `commit`, `trace`, `wire`, `persist`, `federation` (spot-checked — committee-bounded, above),
`rbg` (spot-checked — tag-filter bounded), `dfa-federation`, and the `deos-terminal`/`deos-matrix`/
`deos-hermes`/`servo-render`/`starbridge-web-surface`/`android-cell` host/UI shells. Flag for a round-3 only
if one reaches a per-message or per-frame path over a growing collection.

---

### New-findings summary (strongest first)
1. **Cockpit per-repaint receipt/step rescans** (B1/B2/B8/B9) — O(history)/paint; shared memo + per-cell
   receipt index (B2 a pure cheap-win).
2. **Light-client quorum O(votes²)×3** (B3) — `HashSet` dedup + hoisted committee set.
3. **`LocalNode::contains` cluster** (B4→B5/B6/B7) — one `HashSet` in `LocalNode` fixes three O(n²) verify paths.
4. **billing `invoices_for` O(A·E)** (B10), **credentials `rebuild_root` O(n²log n)** (B11),
   **coord `sync_from_blocklace` O(P·N)** (B15) — each a one-pass / `BTreeSet` / grouping fix.
5. A batch of drop-in `Vec`→`HashSet` cheap-wins (B12 verifier, B13 intent, B14 sdk, B16 spween, B17 agent-host).
