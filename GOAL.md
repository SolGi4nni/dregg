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
