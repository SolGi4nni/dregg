<!-- ⚑⚑ THIS REPO RUNS MULTIPLE CONCURRENT /goal SESSIONS. This GOAL.md is only the
     storage-in-lean lane. The full list of live goals + their trail files is in
     GOALS-INDEX.md — read that to see every active goal (stark-kill, distributed-deos,
     fable, federation, storage-in-lean). Edit only YOUR lane's trail; don't clobber. -->

> ⚑ **Multiple goals are live in this repo — see [`GOALS-INDEX.md`](GOALS-INDEX.md).**
> This file is the **storage-in-lean** lane only.

# GOAL — STORAGE-IN-LEAN: rebuild the dregg storage layer in Lean (proven), package to Rust

## The mission
Rebuild the Rust storage constructions **IN LEAN as the source of truth** — executable Lean
`def`s + REAL theorems — then package to Rust via `@[export]` (leanc-compiled, FFI'd, like the
kernel), retiring the hand-written Rust. North star: **decentralized storage providers with
erasure + fountain codes + proof-of-retrievability + a provider market, all Lean-verified.**

## THE PATTERN (proven — follow it exactly)
The template is `metatheory/Dregg2/Storage/BucketCommitment.lean` (committed `06a1e8fe8`):
- Build on the existing Lean machinery — `Dregg2.Lightclient.MMR` (`mroot`, `mroot_injective`,
  `Opens`, `mroot_binds_position`; the executable Merkle with real binding proofs), and the ONE
  crypto floor `Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR`.
- Prove the REAL property (`contentRoot_injective`: the root binds the object set; `read_sound`:
  the trustless read). Reduce to the existing theorems + CR — do NOT re-prove Merkle from scratch.
- The ONLY assumption is `Poseidon2SpongeCR`, threaded as a HYPOTHESIS (not a Lean axiom). Prove
  it `#assert_axioms`-clean. Carrier ONLY at the irreducible crypto floor (the §8 line the circuit
  already draws) — NEVER carrier the math you can prove.
- Iterate single-file: `cd metatheory && lake env lean Dregg2/Storage/<File>.lean` (fast, cached).
- Integrate: add `import Dregg2.Storage.<File>` to `metatheory/Dregg2.lean` (with a one-line
  descriptive comment matching the style), then `lake build Dregg2.Storage.<File>` (~15s cached).
- Commit path-specifically (`git commit <files> -F -`) — `Dregg2.lean` is a shared file (many
  lanes); path-specific commits avoid the shared-index race. `git add && git commit` bypasses the
  boundary guard AND can lose a stage to a concurrent lane.

## HARD-WON LESSONS (do not repeat)
- **The 2026-07-06 mis-fire**: I first swarmed Rust-first-with-Lean-"probes" + assumed the hard
  math via "honest carriers". WRONG. ember: "the whole point is to rebuild all that old rust shit
  in lean." Lean-first, real proofs, no probes, no carriering the provable math.
- **CENSUS FIRST**: I overwrote a real 29KB `storage/src/erasure.rs` (Reed–Solomon, k-of-n,
  availability sampling) with a stub because I assumed it didn't exist. The Rust storage is RICH
  (`erasure`, `availability`, `retrieval`, `sharding`, `bucket_commitment`, `dedup`, `quota`,
  `metering`, `wal`, the queue primitives). READ the Rust construction you're rebuilding first.
- **Lean is LOCAL** (never persvati/hbox). Lean builds are slow; single-file `lake env lean` for
  iteration, full `lake build` as the integration gate.
- **Verify agent claims** + **don't launder**: green + self-reported ≠ verified. A `P→P` Lean
  theorem builds green. Audit every theorem STATEMENT for non-vacuity (refutable on a false
  instance). Lead the HARD proofs (codec correctness) myself; only fan out the tractable ones
  (decidable-eval cell-programs) against the proven template, with a hard `#assert_axioms` audit.

## Next constructions (each: Lean-first, proven, then packaged)
1. **RS/erasure correctness** — `Dregg2/Storage/Erasure.lean`: decode of any k-of-n shards = the
   original (the emblematic "rebuild the Rust codec in Lean"; a real algebraic theorem —
   Vandermonde/RS-distance; the field arithmetic is the hard part). Rust twin: `storage/src/erasure.rs`.
2. **Proof-of-retrievability** — `Dregg2/Storage/Retrievability.lean`: challenge → Merkle opening
   → verify over `contentRoot`; verify accepts ⟹ the provider holds the challenged data (Merkle
   soundness REAL via BucketCommitment.read_sound; sampling-extractability the honest carrier). NEW.
3. **Fountain/rateless codes** — `Dregg2/Storage/Fountain.lean`: LT/Raptor; decode(≥k+ε droplets)
   = original, droplets bind `contentRoot`. NEW (no Rust yet). Hand-roll a real LT (robust soliton
   + BP decode); the recovery bound may be an honest carrier, the root-binding must be real.
4. **Provider market** — `Dregg2/Verify/…` or a cell-program: deals/bond/slash/registration as a
   decidable-eval cell-program (TRACTABLE real proof, like `QueueFactoryProbe`). Rust twin lives in
   `dregg-storage-templates` (a template, not a codec).
5. **@[export] packaging** (batch, later): compile the executable Lean defs to native via leanc,
   wire into `dregg-lean-ffi` (the `libdregg_lean.a` archive splice), thin Rust FFI bindings,
   retire the hand-written Rust codecs. See `dregg-lean-ffi/build.rs` + the `@[export]` surface
   (`dregg_exec_full_turn` etc. — the kernel is already Lean-compiled-into-Rust).

## STILL-OPEN from this session (not storage-in-lean but owed)
- **Storage endpoint auth-gap**: `app-framework/src/inbox_endpoint.rs` STILL trusts a
  client-asserted `sender_hex` (P0-5 fail-open) — must derive the sender from a SIGNED action
  (fail-closed), two-pole. (An agent was mid-flight; killed. Redo — it has `auth.rs`/`cipherclerk.rs`
  siblings for the real auth.) Same twin already fixed at `node/api.rs:2493` (`75f6b0032`).

## Done-log
- `06a1e8fe8` — storage-in-lean (1/N): `BucketCommitment.lean` proven + in-corpus. THE PATTERN.
- `13ffbbff2` — storage-in-lean (2/N): PoR (`Retrievability.lean`) proven on read_sound (por_sound + anti-forgery). Next: RS/erasure decode-correctness.
- `877a8d4ce` — storage-in-lean (3/N): RS erasure decode-correctness (`Erasure.lean`) — rs_decode_correct + no_wrong_reconstruction, real algebra via Mathlib, no carrier. Next: fountain codes, then provider-market.
- `8b53045e5` — storage-in-lean (4/N): fountain LT decode-uniqueness (`Fountain.lean`) — real linear algebra, no carrier. Next: provider-market cell-program, then the availability capstone (compose commitment+erasure+PoR).
- `ccfa5c2d4` — storage-in-lean (5/N): availability CAPSTONE (`Availability.lean`) — verifiable_erasure_recovers composes commitment+PoR+RS. 5 constructions proven, all #assert_axioms-clean. Next: provider-market cell-program (economic layer); then @[export] packaging.
- `4f75080d8` — storage-in-lean (6/N): provider MARKET (`ProviderMarket.lean`) — cap-first claim + no-double-sell + slash-burns-bond, decidable-eval, no carrier. 6 constructions proven. Next: @[export] packaging (Lean->Rust round-trip), or bind erasure shards to the commitment object-level.

## PURGE CAMPAIGN — retire unverified Rust in favor of the verified Lean
The "package to Rust, retire the Rust" half of the mission. ~13.5K unverified-Rust storage lines,
THREE buckets (purge means different things per bucket):

- **PHASE 0 — dead-module sweep (SAFE, quick):** purge 0-consumer dead modules. `poly_queue` done
  (`208712676`, -1457). RULE: never purge a module with live consumers; `cargo build -p dregg-storage`
  green after each.
- **PHASE 1 — BIND the hot codecs (SAFE, quick — NOT purge):** `erasure` (RS), `sharding`,
  `bucket_commitment`-verify are GF-crunch / hot; a Lean-via-FFI codec over MB is too slow. So keep the
  fast Rust but make it non-independent: add property-tests asserting the EXACT property the Lean proves
  (`Erasure.rs_decode_correct` = k-of-n reconstruction; `BucketCommitment.contentRoot_injective` +
  `read_sound`) + cite the theorem. Proved-property + checked-impl. A bind-test that can't fail on a
  broken codec is worthless.
- **PHASE 2 — complete the cell-programs MIGRATION (SUBSTANTIAL, the big purge):** rewire the ~47
  consumers of the deprecated operators (`inbox`16 `operator`9 `relay`7 `programmable`6 `blinded`5
  `pubsub`4) onto `dregg-storage-templates` + `ProviderMarket`/`QueueFactory` Lean, then delete the ~5K
  deprecated lines. Folds in the `inbox_endpoint` client-asserted-sender auth-gap. Main-loop, per-module,
  behavior-sensitive.
- **PHASE 3 — @[export] the VERIFY logic (DELICATE, coordinated):** package `BucketCommitment`/
  `Retrievability`/`availability` via `@[export]` (closure RE-SEED of `libdregg_lean.a` via
  `scripts/rebuild-dregg2-closure.sh`) → replace the Rust verify with thin FFI bindings → purge the
  hand-written verify. "Lean IS the runtime." Needs a clean window + FFI-lane coordination.

### Purge-campaign done-log
- `208712676` — Phase 0: purged dead `poly_queue` (-1457).
- `5e8ec5fb5` — Phase 1: BOUND erasure (RS) + bucket_commitment to their Lean specs (falsifiable
  tests, mutation-canary-confirmed non-vacuous). Codecs now checked-impl-of-proven-spec.
- Phase 2 MAP (grounded): inbox->cap_inbox, blinded->blinded_queue, programmable->programmable_queue,
  pubsub->pubsub_topic, relay->relay_operator. inbox's 16 consumers: 6 teasting/tests, 2 app-framework
  (incl. inbox_endpoint.rs = THE AUTH-GAP), + subscription/preflight/node/sdk-net/templates. KEY:
  migrating inbox_endpoint -> cap_inbox CLOSES the client-asserted-sender auth-gap (the template
  enforces SenderAuthorized) — the migration IS the fix. Do the easy test/preflight consumers first,
  then the real crates, then delete the deprecated module.

### Phase 2 — the ordered MIGRATION plan (dependency-graphed; execute to COMPLETION, never strand)
The deprecated operator-process cluster is INTERDEPENDENT (sg-mapped): `queue` is the base (used by
operator6/programmable4/blinded2/inbox1/relay1/pubsub1); `operator` mid-layer (uses inbox2+relay1+
queue6); external consumers wrap the operator OBJECTS. Templates that "replace": cap_inbox,
blinded_queue, programmable_queue, pubsub_topic, relay_operator. The current tree is CONSISTENT (the
deprecated modules compile+work; templates exist alongside) — NOT partial. Do NOT half-delete.

ORDER (each step a complete-consistent commit; green-gate the whole tree after each):
1. LIGHT swaps: consumers using only the SLOT constants / CAP_INBOX_FACTORY_VK (node/genesis,
   subscription, preflight, ...) → re-import the SAME-named consts from `dregg_storage_templates::
   cap_inbox` (mechanical). Reduces coupling, strands nothing.
2. KEYSTONE: rewrite `app-framework/src/inbox_endpoint.rs` (15 CapInbox refs — it WRAPS the operator)
   + `dregg-sdk-net/src/mailbox.rs` (4) to produce SIGNED TURNS via `cap_inbox::build_send_action` /
   `build_dequeue_action` instead of wrapping the operator object. THIS closes the client-asserted-
   sender auth-gap (the template enforces SenderAuthorized). Two-pole test each.
3. TESTS: teasting/storage_lifecycle + storage/tests operator tests → migrate to the template's own
   tests (or delete — the operator they test is going away).
4. DELETE `inbox` (once no non-operator consumer remains), then `programmable`/`blinded`/`pubsub`/
   `relay` similarly, then `operator` (mid-layer), then `queue` (base) LAST.
5. Full-tree green gate + a grep proving no `dregg_storage::{inbox,operator,relay,...}` consumer
   remains before each module deletion.
RISK: step 2 changes a LIVE auth contract — needs focused care + two-pole tests, NOT a hasty tail-of-
session cut. Best as a dedicated focused push with the plan above as the anti-strand insurance.

### THE EXTRACTION (the real "Lean is the runtime" for storage) — ember's @[extern]-to-fast-Rust architecture
Insight (ember): don't reimplement Poseidon2 in Lean (the proofs are over an ABSTRACT CR hash — the
stronger form). Instead the Lean hash is `@[extern "dregg_poseidon2_hash"] opaque` (Lean-opaque,
proofs assume Poseidon2SpongeCR — the §8 floor), realized at runtime by the FAST Rust Poseidon2
(circuit::binding::from_poseidon2). Verified LOGIC = Lean (leanc-compiled); hot PRIMITIVE = fast Rust;
FFI binds both ways. Working precedent: `@[extern "dregg_ed25519_verify"]` (PortalFloor.lean).
- STEP 1 (DONE, `5b5fc8099`): `Dregg2/Storage/Deployed.lean` — contentRootDeployed over the FFI hash +
  contentRootDeployed_injective (binding via the CR carrier). Lean side, lake-green, axiom-clean.
- STEP 2 (next, fiddly + heavy — do fresh): (a) `@[export dregg_storage_content_root] def (String) :
  String` marshaling wrapper (parse objects → contentRootDeployed → encode felt; mirror FFI.lean's
  parseFullTurn/encode). (b) Rust `#[no_mangle] extern "C" fn dregg_poseidon2_hash(...)` wrapping
  from_poseidon2 (match the Lean lean_object calling convention — the fiddly part), in the
  dregg-lean-ffi shim. (c) the extern-"C" decl of the @[export] wrapper + a Rust caller. (d) add
  Deployed + the wrapper module to build.rs's compile list; heavy build (delta leanc + 171MB link).
  (e) DIFFERENTIAL test: Lean-extracted content_root vs Rust content_root — if they AGREE (same
  Poseidon2 + encoding), the Rust content_root LOGIC can be retired (the real purge). Verify green.

### THE EXTRACTION — status: PROVEN both sides; link-wiring is the coordinated-window last step
- Lean (`94da933b5`): Dregg2/Storage/Deployed.lean — contentRootDeployed over @[extern "dregg_poseidon2
  _2to1"], binding proven, @[export dregg_storage_content_root] entry, #assert_axioms-clean, lake-green.
- Rust (`01708af9d`): circuit::storage_ffi::dregg_poseidon2_2to1 = real hash_2_to_1 (tested).
- REMAINING (link-wiring — touches SHARED lean_init.c + build.rs; do in a COORDINATED window, NOT while
  another lane is building; mirror the FlowRefine/DistributedExports splice):
  1. dregg-lean-ffi: add `circuit` as a (dev-)dep so `dregg_poseidon2_2to1` resolves at final link.
  2. build.rs: add "Dregg2.Storage.Deployed" to `lake_targets` (~line 232); add a probe
     `archive_exports(&build_archive, "dregg_storage_content_root")` → cfg `dregg_storage_content_root_present`
     (mirror `dregg_decide_refines`).
  3. lean_init.c: `extern lean_object *initialize_Dregg2_Dregg2_Storage_Deployed(uint8_t);` +
     `extern lean_object *dregg_storage_content_root(lean_object *);` + the initialize CALL in the shim
     (mirror StrandAdmission/FlowRefine so the self-linking closure pulls Deployed's object).
  4. A dregg-lean-ffi test (cfg-gated): marshal a String of object-int-triples → call
     dregg_storage_content_root → assert a non-empty root felt. THE ROUND-TRIP: Lean logic + Rust Poseidon2.
  5. (step 3 / the real purge) DIFFERENTIAL: make Lean contentRootDeployed byte-match the Rust
     content_root (same leaf/fold/domain-sep) → retire the Rust content_root logic.
- `2ae48bf1b` — storage-in-lean (7d): THE EXTRACTION ROUND-TRIPS. verified_content_root_runs_in_lean_calling_rust_poseidon2 PASSES — the @[export] Lean content-root runs as leanc-native code IN the Rust binary, calling the fast Rust Poseidon2 via @[extern]. "Lean IS the runtime" for storage, proven AND running. (Battled: harness restarts + a 100%-full disk + a #[used] force-link fix for DCE.) NEXT: the DIFFERENTIAL (make Lean contentRootDeployed byte-match Rust content_root -> retire the Rust logic).

### Phase 2 — the RECON MAP (2026-07-07, read-only agent; supersedes the rough map above)
KEY: `queue.rs` is NOT deprecated (0 markers) — it's the BASE primitive (DequeueProof/QueueEntry/
verify_dequeue_proof = live wire format); it STAYS, never migrates. Only 5 REAL behavior-changing
consumers; the rest are tests(9)/harness(2). GOTCHA: multi-line brace imports
(`use dregg_storage::{…, inbox::{…}}`) EVADE `dregg_storage::inbox` greps — sweep by TYPE NAME.
Per-module (template-covers? / gaps / consumers):
- pubsub→pubsub_topic: covers pub/sub/grant; gaps read_next/subscriber_lag/gc. Consumers: TEST-ONLY
  (teasting ×2 + preflight). ← EASIEST, do first.
- programmable→programmable_queue: covers program/factory; gaps the programs::{acl,rate_limited,…}
  presets + QueueLookupTable + compute_vk_dual. Consumer: app-framework/queue_endpoint.rs (REAL HEAVY).
- blinded→blinded_queue: covers commit/consume; gaps FairDistribution lifecycle + client helpers; the
  spend AIR STAYS in blinded.rs (registered in WitnessedPredicateRegistry — file shrinks, never fully
  deletes). Consumer: app-framework/blinded_endpoint.rs (REAL HEAVY).
- inbox→cap_inbox: covers send/dequeue/grant; gap InboxMessage enum (LIVE WIRE TYPE for relay_service —
  re-home before deleting). Consumers: inbox_endpoint.rs (REAL HEAVY — auth-gap DONE e16dfe17e),
  node/relay_service.rs (LIGHT, InboxMessage only), teasting ×4. Deletion BLOCKED by operator.
- relay→relay_operator (partial): gaps MeteredRelay in-process API. Consumers: preflight/relay.rs
  (harness), relay_service (LIGHT RelayError mapping), teasting ×2. Deletion BLOCKED by operator.
- operator→relay_operator: covers register/slash; drain/gc→signed turns. Consumer: relay_service
  (REAL HEAVY — holds `pub operator: RelayOperator`; ALREADY dual-imports the template @ line 38).
  operator uses inbox+relay+queue = the mid-layer capstone.
ORDER: 1 pubsub (test-only) → 2 programmable (close preset gaps, then queue_endpoint) → 3 blinded
(keep AIR residual) → 4 inbox-consumers → 5 relay-consumers → 6 operator (relay_service, the one real
model change) → then delete inbox+relay. queue KEEPS. Full detail: agent a242d9d357a4b3532 output.

### PURGE SWARM (2026-07-07, 2 waves, 10 lanes) — DONE (wave 3 died on Fable credits)
Went WIDE per ember. Committed + verified-myself:
- 8 storage modules BOUND to falsifiable specs: erasure+bucket_commitment (5e8ec5fb5), sharding
  (40ef4285d), availability+retrieval (c6777bc52), commitment+content+wal (bf306ca29). Every bind
  refused to fake a mismatched Lean binding — documented "no spec yet" where none applies.
- 2 REAL BUGS FIXED: inverted deadline (2b986558d — FieldLteHeight→FieldGteHeight, kernel-verified,
  two-pole that inverts the enshrined test); DAS confidence-inflation (a6b0dcccf — chunk.index binding).
- auth-gap CLOSED (e16dfe17e — inbox_endpoint signed-send, fail-closed, two-pole).
- 14 honesty overclaims corrected: starbridge ×12 (b7a235e22), core crates ×2 (0a7842ba8).
- dead-sweep: clean (nothing dead left). Phase-2 recon MAPPED (bf2942330 — queue STAYS, 5 real consumers).
NAMED RESIDUALS (HORIZONLOG, not laundered): accumulator verify_non_membership FORGEABLE (+ sdk/
privacy.rs prover-supplied gap); commitment encode_bytes_to_felts bit-6/7 masking non-binding;
from_leaves leaf-count non-binding. WAVE-3 TODO (Fable credits): accumulator soundness fix; honesty-3
(turn/intent/deos); pubsub→pubsub_topic migration (test-only, the easy Phase-2 first step).

### PROTOCOL LOGIC IN LEAN (ember's direction: implement the protocol in Lean, proofs alongside; deploy)
The deployable-storage engine's RULES live in Lean (proven), the I/O in Rust. Verified core DONE
(commitment/RS/fountain/PoR/availability/market/deal-lifecycle). Now the protocol + deployment:
- `8/N` DONE (`271949459`): DealLifecycle.lean — the deal as a proven state machine (Open→Claimed→
  Active→Audited{Pass|Fail}→{Settled|Slashed}); illegal step unrepresentable; terminal_is_final,
  settle_requires_passed_audit, slash_requires_failed_audit, bond_nonincreasing_after_claim.
- NEXT (Lean, proofs alongside): (a) MarketAudit — connect Retrievability.por_sound to
  DealLifecycle.auditPass/Fail → the end-to-end theorem "honest provider NEVER slashed ∧ withholding
  IS slashable". (b) Provider registration (cap-first, bond posting) as a proven cell-program. (c) the
  client/renter protocol (upload→erasure-code→distribute→retrieve→audit→settle-or-slash) as a proven
  interaction.
- DEPLOYMENT (Rust I/O + the verified core): provider daemon (stores/serves/answers-PoR); client
  lib/CLI; market-on-the-live-ledger (deals as real dregg turns); TRANSPORT via `./orb` (drorb — the
  VERIFIED network engine: HTTP/QUIC/TLS proven) so it's verified-storage-over-a-verified-wire;
  EXTRACTION endgame via `./orb-compiler` (Lean spec→CakeML/Pancake→machine code with a preservation
  PROOF — stronger than our trusted leanc/@[extern]). Deploy+test persvati→hbox→david's homelab.
- CRYPTO NOTE (ember): ed25519 stays for now (the hard PQ parts — STARK/FRI + Poseidon2 — are ALREADY
  hash-based/PQ-plausible; identity is the migratable part). PQ SIGNATURES later = Dilithium/Falcon/
  SPHINCS+, NOT Kyber (Kyber is a KEM/encryption). Migrate via crypto-agility + cross-attestation. 2027.

### PROTOCOL-IN-LEAN — COMPLETE (2026-07-07 full-send). 13 constructions, end-to-end proven.
Storage core (1-7): BucketCommitment · Retrievability(PoR) · Erasure(RS) · Fountain · Availability ·
ProviderMarket · Deployed(extraction runs). Protocol layer (8-13, all #assert_axioms-clean):
- 8 DealLifecycle (271949459) — deal state machine, illegal step unrepresentable.
- 9 MarketAudit (41be35f29) — audit drives lifecycle: honest=>safe, withholding=>slashed.
- 10 DealLifecycleTrace (07bad8124) — ACYCLIC + forward-only (never moves backward).
- 11 DealPayment (ebfc4260c) — value CONSERVED (settle/slash payouts; burn is real, not skimmed).
- 12 ProviderRegistry (e407bdd7f) — provider stake lifecycle, cap-first registration.
- 13 ClientProtocol (5a2f0e2a9) — THE END-TO-END THEOREM data_survives_and_cheaters_pay: composes
  Availability + MarketAudit into "your data recovers if k providers honest ∧ honest keep bond ∧
  cheaters slashed" — DERIVED, not asserted.
REMAINING SEAM (mechanical follow-on): ProviderMarket <-> DealLifecycle refinement. ProviderMarket is
the executor-wired cell-program but COARSE (open/claimed + a slash-with-auditFailed-bool; it predates +
collapses the audit states). Clean close = upgrade ProviderMarket to carry the full DealLifecycle
states so the cell-program refines the abstract protocol; needs the RecordKernelState field mechanics.
NEXT after that: the deployment (Rust I/O daemon/client/market-on-ledger) — orb transport deferred.
- `8304d0fbc` — 14/N: MarketRefinement — the executor cell-program refines the abstract protocol (claim leg, via cell field mechanics). PROTOCOL-IN-LEAN COMPLETE. Only slash-leg refinement remains (needs ProviderMarket upgraded to carry the audit states — a LEGACY-alignment follow-on, not a protocol-logic gap).

### RESIDUAL GRIND (2026-07-07, /goal: no residuals/all-legs/all-alignments) — state @ quiesce
DONE: 15/N DealCell (ALL SIX legs refine DealLifecycle, f097763e1) · commitment felt-encoding made
INJECTIVE (8cc597a9d — 3-byte packing, Poseidon2 form now binds every preimage bit; poseidon2_form_
binds_all_bits) · leaf-count mis-framing corrected (from_leaves is a count-agnostic Merkle PRIMITIVE
by design — membership proofs are paths; count-binding lives + is PROVEN at the Accumulator,
prop_accumulator_binds_item_sequence; a first attempt to bind it in from_leaves BROKE blinded consume
— reverted). Full storage suite 232 passed.
NEXT (in flight, censused, NOT yet coded — resume here): the ACCUMULATOR FORGERY in
commit/src/accumulator.rs. `verify_non_membership` (static) is FORGEABLE — any remainder'!=0 with
quotient'=(Acc-remainder')/(alpha-x) passes the bare identity; it never binds remainder=f(x). The
struct STORES `elements: Vec<BabyBear>`, so the SOUND fix is a `&self verify_non_membership` that
recomputes f(element)=product(element-h_i) and requires witness.remainder==that (+ the identity, +
!=0). The setless static verify is fundamentally forgeable (verifier holds only alpha/Acc from a set
COMMITMENT — cannot recompute f(x) without the set or a pairing) -> rename to
`verify_non_membership_identity`, #[deprecated], consistency-check-only doc. Caller
`sdk/src/privacy.rs:767 verify_accumulator_non_membership` uses prover-supplied alpha/Acc -> route to
the sound path (needs the trusted set/accumulator; if it genuinely lacks it, that's the honest floor:
O(1) setless non-membership needs a pairing). AFTER: commit-crate typed.rs has its OWN
encode_bytes_to_felts with the same 4-byte mask (separate residual, same 3-byte fix).

### RESIDUAL GRIND — CLOSED (2026-07-07): all tractable storage/commit residuals ground out
- accumulator FORGERY closed (ec0bd9ef5): verify_non_membership_bound(&self) recomputes+binds f(x);
  the setless static #[deprecated] as forgeable; the forgery is a PROVEN-caught test, not a doc caveat.
- storage + commit encode_bytes_to_felts made INJECTIVE (8cc597a9d, 588cd454c): 3-byte packing, the
  Poseidon2 form of arbitrary-byte commitments binds every bit. Storage 232 / commit 126 green.
- leaf-count corrected (8cc597a9d): from_leaves is a count-agnostic Merkle PRIMITIVE by design (a
  wrap breaks membership paths — a first attempt broke blinded consume); the count is bound + PROVEN at
  the Accumulator. canonical_32_to_felts_4 "bijection" overclaim -> one-way fingerprint (this commit).
- DealCell (f097763e1): ALL SIX legs refine DealLifecycle.
TWO remaining are GENUINE CROSS-LANE boundaries (recorded, not laundered, cannot close in this lane):
  (a) sdk::verify_accumulator_non_membership verifies PROVER-SUPPLIED alpha/Acc -> architecturally must
  fetch the federation-committed (trusted) accumulator to call verify_non_membership_bound; blocked on
  sdk/privacy.rs being clean (another lane's live note-spending WIP). The sound primitive EXISTS.
  (b) canonical_32_to_felts_4/8 fingerprint a 32-byte BLAKE3 DIGEST (CR input -> masking non-exploitable)
  AND are mirrored BIT-IDENTICALLY by the circuit AIR; injectivity needs 9 felts = an AIR-width +
  deployed-VK regen = the deployed-faithful lane (ember-gated). Dual BLAKE3 form binds fully.

### RESIDUAL GRIND — final state (2026-07-07). All CLEANLY-BOUNDED residuals CLOSED.
CLOSED this campaign: DealCell all 6 legs (f097763e1) · storage+commit encode_bytes_to_felts INJECTIVE
(8cc597a9d, 588cd454c) · accumulator FORGERY bound+proven-caught (ec0bd9ef5) · leaf-count reframed to
the Accumulator where it's proven (8cc597a9d) · canonical bijection->fingerprint doc (d2de3b53a) · mcp
tool-call FULL-digest binding, was 64-bit (e97ccbfba). [+ earlier: DAS index-fix a6b0dcccf, inverted
deadline 2b986558d, auth-gap e16dfe17e.]
REMAINING — each needs an ember-decision OR deeper cross-crate work; NONE is a launder:
- sdk::verify_accumulator_non_membership: CLOSED (37425294a) — now requires the TRUSTED accumulator,
  checks alpha/Acc match it, binds f(x) via verify_non_membership_bound. (Was blocked on sdk dirty.)
- [was] sdk prover-supplied verify. The sound primitive
  (verify_non_membership_bound) EXISTS; the fix is architectural — the SDK must obtain the trusted
  federation-committed accumulator (with the set) to bind f(x). This is the crypto FLOOR: setless O(1)
  non-membership is impossible over a field accumulator (needs a pairing/KZG). EMBER DECISION: hold the
  set (O(n) sound) vs adopt a KZG accumulator. Also blocked on sdk/privacy.rs (another lane's live WIP).
- canonical_32_to_felts_4/8: fingerprint a 32-byte BLAKE3 DIGEST (CR input -> masking non-exploitable)
  AND the circuit AIR mirrors them BIT-IDENTICALLY. Full-injective needs 9 felts = an AIR-width +
  deployed-VK regen = the deployed-faithful lane (EMBER-GATED). Dual BLAKE3 binds fully.
- audit_run step<->receipt cross-check: needs an auditor-RE-DERIVABLE action commitment on TurnReceipt
  (turn_hash includes signing). A turn-crate change, not a local fix.
- nameservice FieldDelta: bake the exact-increment caveat into the name FACTORY DESCRIPTOR (real
  cell-program wiring). vat verified-turn wire: unbuilt (a FEATURE, not a bug).

### RESIDUAL GRIND — round 2 (2026-07-07): nameservice CLOSED; 3 genuinely remain
- nameservice FieldDelta CLOSED (93d06be26): restructured name_cell_program to CellProgram::Cases with
  a MethodIs(renew_name) case carrying FieldDelta{EXPIRY_SLOT, DEFAULT_RENT_EPOCH_BLOCKS} — renew now
  advances EXPIRY by EXACTLY one rent epoch (all matching cases enforced). (Flagged "deep", was
  tractable — the guard model supports per-transition caveats.)
- sdk accumulator forgery CLOSED (37425294a). [Campaign total: 10 soundness/binding fixes.]
GENUINELY REMAINING (each PROVEN deep/gated by actually digging in, not hand-waved):
1. canonical_32_to_felts VK — regenerating it RE-KEYS the live federation (deployed-faithful). Only
   ember can trigger. Dual-BLAKE3 binds meanwhile; the masking is non-exploitable for CR-digest input.
2. audit_run step<->receipt cross-check — needs to store the SIGNED action in the log (additive, fine)
   AND recompute make_turn + turn_hash to bind e.step<->e.receipt; the turn-hashing isn't exposed +
   make_turn determinism is unverified. A real turn/app-framework infra build.
3. vat verified-turn wire — vat has ZERO executor integration (no cipherclerk/executor imports); the
   wire is a from-scratch feature: a transition->effects builder + fire_vat_transition + install + a
   two-pole executor test. A genuine feature build.

### RESIDUAL GRIND — round 3 (2026-07-07): audit_run CLOSED. Only 2 remain (both genuinely gated/feature).
- audit_run step<->receipt cross-check CLOSED (e39df1e40): engine retains the EXECUTED turn per step
  (new EmbeddedExecutor::submit_turn_executed — turn.hash() == receipt.turn_hash); audit_run verifies
  the stored turn hashes to its receipt AND its effects bind the step's worker/tool/cost/sub_task
  (TurnReceiptMismatch / StepNotFaithful). Threaded through DurableLog::append. Two-pole tested (a
  forged step record is caught). I'd flagged this "needs turn-crate infra" — I built the infra.
  [Campaign total: 12 soundness/binding fixes.]
REMAINING (2):
1. canonical_32_to_felts VK regen — RE-KEYS the live federation. ember's key, genuinely. Dual-BLAKE3
   binds meanwhile; masking non-exploitable for CR-digest input. NOT a code fix I can land.
2. vat verified-turn wire — vat has ZERO executor integration (no cipherclerk/executor imports). A
   from-scratch feature: transition->effects builder + fire_vat_transition + install + a two-pole
   executor test. A genuine feature build (not a residual-bug), buildable next.
