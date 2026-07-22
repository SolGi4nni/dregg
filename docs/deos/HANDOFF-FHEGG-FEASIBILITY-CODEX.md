# HANDOFF — fhEgg / Dark Bazaar current implementation ledger

*Rewritten from current source, focused commits, captured gates, `HORIZONLOG`,
and the compacted-session record on 2026-07-22. Authority cut:
`6d0e024f19`. This is a present-tense handoff, not an append-only diary; older
versions remain in git and `cv`.*

## 0. How to read this file

Status words are intentionally strict:

- **LIVE** — in the production call graph at the named boundary.
- **GATED** — the named focused test/proof gate was captured green.
- **SUBSTRATE** — executable and useful, but not the whole product claim.
- **WIP** — committed or dirty work that has not earned a composed green.
- **OPEN** — the construction or integration is absent.

A Lean theorem proves the model stated in that module. It does not silently
prove a Rust codec, FFI, witness producer, cryptographic reduction, network
protocol, persistence path, or deployment. A hiding proof protects against its
verifier; it does not automatically hide the witness from the process that
constructed the proof.

The shared tree is dirty in unrelated frontend, AutomataFL, HOL, and symbolic
predicate lanes. Do not fold those files into a fhEgg status claim. In
particular, `7ba02bc122` is a large mixed WIP checkpoint; each contained lane
needs its own gate or focused follow-up.

## 1. Executive state

The Dark Bazaar is no longer merely a design or operator-visible crawl:

- one deployment-owned private Bazaar offering is mounted through the shared
  catalog and game spine;
- web, Telegram, and Discord use the same authority-bound session and
  viewer-blind publication grammar;
- a private, supervised, restartable receipt worker owns raw settlement
  evidence and applies one exactly-once Dungeon consequence;
- durable, signed, checkpoint-anchored character worlds are shared between
  that worker and the playable Dungeon surface;
- exact FNSP-v3 proof acceptance executes at block finality; FRC1 lookup, CTM1
  typed terminal outcomes, and private dependent wake-up are durable;
- the lossy fields-root/Descent quarantine has been replaced by an exact v11
  full-key/full-value epoch and a canonical-v2 HidingFRI census door; and
- FWS1, q0 carrier/LogUp, terminal-binding, dealerless preprocessing, WGPU NTT,
  TFHE, HidingFRI, and Bulletproof work materially advanced.

The apex is not done:

- live exact-v3 is not dark value;
- the full semantic v4/FXC4 shared-witness proof is not installed;
- the complete private BFV terminal is not authoritative;
- FHTRI005 still requires a malicious/PQ cross-term provider;
- the q0 ceremony lacks authenticated broadcast and cross-commitment
  same-opening;
- witness construction is not yet distributed enough to remove every single
  source viewer; and
- v4 persistence, output-note mutation, selector, and committee finality are
  open.

## 2. Live exact finality and transport

### 2.1 Exact FNSP-v3

The banked path now includes:

- canonical typed DescriptorIR2 relation identity rather than JSON bytes as
  protocol identity;
- the complete 16×3,760 HidingFRI relation and strict 76-lane wire;
- a private, non-Clone accepted-proof token bound to the complete proof carrier
  in the authenticated `SignedTurn`;
- staged exact state, durable faithful↔exact state, frame/receipt identities,
  historical replay, and O(1)-style live predecessor authority;
- block-finalizer selection and off-lock proof work followed by under-lock
  revalidation and atomic persistence; and
- typed terminal disposition:
  `Committed | DeterministicallyRejected | RetryableOperational |
  FatalIntegrity`.

Key current commits include `f49d68e770` (canonical exact relation),
`02db5d60ff` / `6dd7aecc2e` (opaque accepted proof and signed carrier),
`d33cad69e9` / `f8836e4498` (faithful exact finalization and production
execution), and `56fcd69438` (historical replay repair).

The authority boundary remains explicit:

- v3 public inputs expose value, asset, nullifier, roots, counts, and outer
  coordinates;
- the currently characterized execution slice includes the value-zero form;
- the live frame authority is not the final signer-independent committee v4
  core; and
- v3 is the exact anti-double-spend/receipt foundation, not a private-value
  claim.

### 2.2 FRC1, CTM1, and private dependent turns

`e5b21f17a7` activates CTM1 and the exact failure disposition.
`605135698b`, `ec03940ce3`, and `b0c3a9fea0` provide reciprocal durable FRC1
identity and authenticated public queries without exposing the local executor
signature envelope.

`d5bb140504` closes the private dependent ingress seam:

1. a sealed ready item is destructively claimed;
2. its CTM1 ingress reservation is made in the same transaction;
3. ordinary SignedTurn validation/finality remains the only execution route;
4. crash uncertainty is reconciled through finalized identity rather than
   blind resubmission; and
5. the dependent wakes only from the exact finalized receipt.

This is a real safety closure. It does not make the sealed payload itself a
public API or grant a second executor path.

## 3. The player/runtime path

### 3.1 Shared authority-bound game spine

The hosted surfaces do not implement three separate games. The current path
uses:

- `GameHostIncarnation` to name one deployment/federation authority;
- a durable close/reopen generation;
- an authority-bound `GameSessionRef`;
- a signed action plus a separate authority signature over incarnation,
  generation, action/operation, advertised pre-head, and counter; and
- one game epoch ledger shared by the catalog/web/chat adapters.

`05aed2c8e2` closes the primary durable epoch cut.
`cd19363ca8` carries it through Telegram shielded-crown commands.
`d1b181dec7` binds private operation and artifact routes.
`ac32f1cc54` removes native Telegram/Discord bypasses.

The hostile web tests cover old tabs after close/reopen, restart-invalidated
forms, foreign host incarnation, generation changes, and head mismatch.
`6d0e024f19` additionally fixes the full-Lean timed close: it runs on a
Lean-registered runtime worker rather than `spawn_blocking`, whose foreign
thread caused the reality gate to refuse the close. The focused full-Lean
overlay gate was 13/13.

### 3.2 Private Bazaar deployment and worker

`PrivateBazaarLiveDeployment` owns, as one value:

- validated deployment policy and exact offering;
- live-session registry;
- commitment store;
- durable exactly-once XP adapter;
- private authority directory;
- authenticated finalized-receipt source; and
- start/stop ownership of the private worker runtime.

`cd3ea449b0` supplies the production worker.
`9723e14ba5` supervises authenticated receipt discovery.
The v2 spool is fixed-width, append-only, checksum chained, deployment /
federation / market / policy scoped, owner/mode checked, no-follow opened,
inode pinned, fsynced, and bounded. A semantic core may be reissued with a new
local proof envelope; a semantic fork or cross-deployment replay refuses.

The worker journal is:

`Prepared → Dispatching → Applied → Committed`.

The target receipt makes a crash after dispatch recoverable without applying
Dungeon XP twice. Frontends cannot obtain the winner, blind, raw receipt, or
private input digest from the public worker report.

### 3.3 Durable Dungeon target

The earlier draft’s base-hero shadow ledger is gone from the authority path.
`d08100655b`, `7bd87790fb`, and `ed5c4c5643` provide signed,
crash-recoverable world cells with continuous checkpoint authority.
`190938372b` delegates reward pricing to that durable world. The target
registry verifies program/cell/custody pins, restores the exact character
state, and registers the same `CharacterStore`-backed Dungeon offering used by
the frontend.

The public result is a viewer-blind journey/consequence card. The private
worker retains everything needed to apply the effect.

## 4. Exact fields and Descent

The prior fields-root design folded four-byte chunks into BabyBear and hashed
keys into one felt. That admitted concrete source aliases without a Poseidon
collision. It is no longer the current epoch.

`8113f7a55e` cuts:

- v11 persistence;
- exact raw-`u64` keys;
- full field-byte values;
- domain-separated exact leaves, nodes, and empty leaves;
- ledger root v3; and
- strict refusal of populated legacy/unmarked stores.

Concrete key and value `+ BabyBear::ORDER` aliases are tests.

`e63baf8fa5` rebuilds the fixed-eight Descent custody census against the exact
root. The canonical-v2 custom-VK verifier accepts only the checked-in
Lean-authored descriptor under the code-owned hiding configuration and binds
the six census totals to Descent fields `0..6` with the declared integer
encoding. `5d538dabc4` emits the corresponding exact refusal-fields transition.

This closes the old census quarantine. It does not prove arbitrary heap
aggregations or every Descent game rule.

## 5. Shielded proof stack

### 5.1 Semantic v4 boundary

`circuit-prove/src/shielded_exact_apex_v4.rs` defines the correct public
boundary:

- no clear value or asset;
- full 256-bit nullifier;
- sixteen-lane hidden value/asset binding;
- exact prior/successor accumulator state;
- consequence and output-note roots; and
- exact before/after outer commitments.

The FXC4 transcript reserves the complete 19 Dark-AMM and 27 ring lanes.
The Rust module itself correctly says these are binding/wire primitives, not
proof acceptance authority.

### 5.2 FWS1: the honest proof that exists

`f540ed95a1` deletes the misleading “shielded apex v4” proof artifact and
banks `shielded-whole-note-swap-substrate-v1`.

FWS1 is a real HidingFRI proof of a hidden two-input/two-output whole-note swap
with exact nullifier, wide value/asset binding, authenticated predecessor and
append paths, conservation, output-note root, and outer endpoints. It has a
strict canonical postcard decoder and a code-owned hiding verifier.

FWS1 is not the semantic v4 apex. It lacks the full 19+27 FXC4 consequence,
live output-note installation, persistent v4 frames, selector, and committee
finality.

### 5.3 BFV terminal and LogUp

The public q0 terminal module remains deliberately fail-closed because its
legacy context commitment does not prove same-opening between a hidden product
and the carrier coefficient.

The repair stack now includes:

- exact q0 radix reconstruction and production carrier identities
  (`13357f84c2`, `7c61dbe1a7`, `9066ab2447`);
- party-local q0 ceremony laws (`a0d22fd5cb`);
- deployed root-order proofs (`07ccddf4ac`);
- a terminal-product/spectral-trace Lean binding (`9dbb0bef55`); and
- exact public-row LogUp table semantics and fixed q0/N=8 KAT proofs
  (`057a9e904a`).

The fused child relation in `7ba02bc122` joins one exact 4,096-term private
slice to the threshold terminal in one HidingFRI trace. It supports only
coordinate `o0/c0/q0/k0`. It is a valuable same-opening cut, not the complete
98,304-equation private terminal or live market authority.

## 6. Dealerless and no-single-viewer custody

The current FHTRI005 composition has real content:

- real threshold-BFV candidate formation;
- 129 candidates per kept binary gate;
- party-local candidate and MAC-bit custody;
- roster/session/collective-key/correlation-profile binding;
- committed distributed MAC-key material;
- joint commit-reveal beacon;
- Lean proof of the complete ordered distinct-party cross-term identity; and
- durable one-use custody/tombstones for protected FHTRI004 material.

It also has an intentionally uninhabited production seam:
`AwaitingCrossTermProvider`. A malicious-secure PQ chosen-input VOLE/OT (or
equivalent) provider must deliver the off-diagonal `α_i · x_j` shares without
co-locating both inputs, bind receipts to the exact roster/session/candidate
manifest, and resist omission, direction swap, chosen-input substitution,
selective failure, replay, and reused setup.

The experimental q0 commitment ceremony also still refuses public authority.
It has party-local openings and inclusion checks but no authenticated broadcast
and no public same-opening proof between the Ristretto/VSS commitment and the
q0/SIS-style commitment.

Therefore:

- **dealerless algebra and custody:** real substrate;
- **trusted-dealer-free live market:** open;
- **HidingFRI privacy from proof consumers:** real for named proofs;
- **privacy from every witness producer/operator:** open until collaborative
  proving/distributed witness production lands.

## 7. Portable GPU and performance

Banked WGPU work includes exact BFV odd NTT, batched BFV validation, TFHE
external products/blind rotation/PBS/comparison/selection, HidingFRI folding,
and exact CPU differentials. `e100aae2a1` adds the optimized odd-NTT path and a
required-GPU crossover harness; `07ccddf4ac` proves the exact deployed root
orders.

The performance claim is scoped:

- a kernel running on WGPU does not make the full market GPU-resident;
- the new crossover harness is ignored/on-demand and must be captured on hbox
  before quoting a crossover;
- CPU can still beat GPU for small geometry;
- live custody/range proofs include classical Ristretto/Bulletproof work;
- Bulletproof proving was parallelized/right-sized and verification improved,
  but it remains classical, not post-quantum; and
- release-mode hbox/persvati measurements with exact CPU parity are authority,
  not debug timings or adapter discovery.

Lean remains local; heavy Rust/crypto gates belong on persvati or hbox per
`AGENTS.md`.

## 8. fhIR and Lean-first ownership

fhIR remains a typed product/compiler layer with real private convex,
allocation, and direct-logic families. `ff3001c325` adds a certified
complementary-root zero-observation lowering, while explicitly requiring an
external same-opening receipt.

The project boundary should remain:

- Lean authors semantics, admissibility, exact arithmetic laws, descriptor
  identity, and protocol state machines;
- emitted canonical typed objects are protocol relations;
- Rust implements strict interpreters, witness construction, storage,
  transport, and host integration;
- WGPU/Rust may implement fast paths only behind exact differentials and
  pinned relation identities.

There is not yet a whole-fhEgg theorem saying every Rust FHE/MPC/network action
refines the Lean model. Do not call “Lean module exists beside Rust code”
functional correctness.

## 9. Current WIP exclusion

`7ba02bc122` contains useful but mixed work, including the fused BFV terminal,
CAP-v2/UMEM-v2 material, Descent whole-turn spine, bridge work, and direct-logic
artifacts. It is not a full-suite green.

At the time of this rewrite, dirty frontend/Bazaar files and unrelated
AutomataFL/HOL/symbolic-predicate work also exist. They are deliberately absent
from this authority ledger until their owners bank and gate them.

## 10. Closure order for the next team

1. **Full FXC4 shared witness.** One canonical relation must carry the exact
   note opening, BFV/TFHE market result, 19 Dark-AMM lanes, 27 ring lanes,
   conservation/range facts, output notes, and exact state endpoints.
2. **Dealerless provider.** Implement and verify the malicious/PQ cross-term
   provider at `AwaitingCrossTermProvider`; complete q0 authenticated broadcast
   and cross-commitment same-opening.
3. **Live v4 authority.** Add persistent activation/frame/state, selector,
   atomic output-note mutation, signer-independent receipt identity, and
   federation/committee finality.
4. **One composed deployment gate.** Run
   Bazaar → exact finality → authenticated private source → durable worker →
   Dungeon/Descent consequence through web, Telegram, and Discord with full
   Lean and the audited PQ backend.
5. **Distributed prover.** Turn verifier-hiding into house-blindness by
   removing the single complete-witness process.
6. **Resident operation, then measurement.** Compose BFV/TFHE/HidingFRI stages
   in one retained GPU schedule and publish exact cold/warm counters.
7. **Game expansion.** Reuse the same authority/receipt/world spine for private
   shuffle, vote, matchmaking, netting, and Dark-AMM mechanics.

## 11. Focused entry points and gates

Read these first:

- `docs/deos/THE-DARK-BAZAAR.md`
- `docs/deos/FHEGG-RESEARCH-FRONTIER-2026-07-22.md`
- `circuit-prove/src/shielded_exact_apex_v4.rs`
- `circuit-prove/src/shielded_whole_note_swap_substrate.rs`
- `circuit-prove/src/private_book_bfv_terminal.rs`
- `circuit-prove/src/private_book_bfv_terminal/fused.rs`
- `fhegg-fhe/src/dealerless_preprocessing.rs`
- `dreggnet-catalog/src/private_bazaar_live.rs`
- `dreggnet-catalog/src/private_bazaar_worker.rs`
- `dreggnet-catalog/src/private_bazaar_targets.rs`
- `dreggnet-catalog/src/game_spine.rs`
- `turn/src/descent_census_custom.rs`

Use narrow gates, never the debug workspace gauntlet:

```sh
cargo nextest run -p dreggnet-catalog
cargo nextest run -p dreggnet-web -E 'test(/game_epoch|private_bazaar/)'
cargo nextest run -p dregg-turn -E 'test(/descent_census/)'
cd metatheory && lake env lean Dregg2/Claims.lean
```

Proof-heavy, WGPU, exact-v3, and custody tests should be selected explicitly
and run in release on hbox/persvati. A focused lane’s captured green is enough
for that lane; do not rerun the heavy world to edit a Markdown ledger.
