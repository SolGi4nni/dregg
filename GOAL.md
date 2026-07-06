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
