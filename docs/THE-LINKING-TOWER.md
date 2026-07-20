# The Linking Tower

**What a light client is entitled to believe, and why.**

A light client holding one root knows every transition in the whole history was
authorized, conservative, fresh, and correctly committed — re-executing nothing
([`OVERVIEW.md`](OVERVIEW.md)). That entitlement is not one theorem; it is a
tower. Each rung is a different *kind* of fact — bytes, denotation, cryptography,
kernel semantics, composition — and each rung has its own named hypotheses.
The tower is told bottom-up here, and at every rung the assumptions are listed,
because **hypotheses are not free**: `#assert_axioms` checks the axiom closure
of a proof term and never its hypothesis list. A `def FooHard` consumed as a
hypothesis is an assumption, however clean the axiom report. Every "proven"
below means: proven *from* the named premises of that rung, with the premises
stated.

---

## Rung 0 — the deployed verifier bytes

The object a light client actually runs is compiled bytes, not a Lean term. The
bottom rung is the chain of custody from the verified source to those bytes.

- **The descriptor registry is committed bytes.** The live per-turn effect-VM
  registry is `V3_STAGED_REGISTRY_TSV` — `include_str!` of
  `circuit/descriptors/rotation-v3-staged-registry.tsv` with its sha256 pinned
  beside it (`circuit/src/effect_vm_descriptors.rs:826-829`). Structural
  coverage of every row is a unit test
  (`v3_staged_registry_parses_and_covers`, `effect_vm_descriptors.rs:2305`).
- **The VK pins the bytes — one component by content, three by convention.**
  `compute_recursive_vk_hash`
  (`circuit-prove/src/recursive_witness_bundle.rs:135`) folds four components
  into one hash: the AIR descriptor fingerprint, the constant program-bytes
  label `RECURSIVE_VK_PROGRAM_BYTES` (`:103`), a verifier-surface
  fingerprint, and the pinned Plonky3 rev; `lookup_recursive_vk` (`:180`)
  accepts exactly that hash, the verifier rejects any other
  (`verifier/src/lib.rs:772-776`), and the rejection has a tooth
  (`foreign_circuit_root_is_refused_by_vk_pin`,
  `circuit-prove/tests/ivc_turn_chain_rotated.rs:626`). The verifier-surface
  component is not a hash of the verifier source:
  `recursive_verifier_source_hash` (`:123`) is BLAKE3 of the constant string
  `"dregg-recursive-witness-bundle-verifier-v1"` — a version label the code
  says to bump "when this module's verifier surface changes meaningfully",
  reserving the git-blob-hash form for "a fuller VK v2 rollout". The Plonky3
  rev has the same failure mode: `RECURSION_P3_REV` (`:111`) is a
  hand-mirrored string whose shipped comment says a rev bump "must be
  mirrored here" because "bumping the rev without bumping this string would
  silently let old recursive proofs verify against new code". A
  verifier-source change or a rev bump with a forgotten mirror leaves the VK
  hash unchanged: only the AIR descriptor fingerprint pins by content; the
  other three components pin by convention.
- **The bytes are a cache of the Lean, and the cache is gated.** A sha256
  rehash proves only self-consistency — a committed file matching the hash
  committed beside it. The gate with teeth is generate-fresh:
  `scripts/check-descriptor-drift.sh` re-emits every descriptor from the
  compiled Lean emitters and fails on any byte difference, in CI as the
  `descriptor-drift` job. The regen lifecycle and its misuse controls are
  [`VK-REGEN-CONTROLS.md`](VK-REGEN-CONTROLS.md).

**This rung assumes:** the toolchain and git tree that built the deployed
binary are the ones CI checked. Reproducible builds are a named frontier
(the one deploy caveat of this document); today this rung is a CI-and-git
chain of custody, not a bit-for-bit reproduction.

## Rung 1 — descriptor denotation: the bytes mean a Lean object

The TSV rows are the image of a verified Lean value, not a hand-authored
artifact. The emitters live in `metatheory/Dregg2/Circuit/Emit/*.lean`
(`EffectVmEmitRotationV3.lean`'s `v3Registry` is the source of the live
registry), and the descriptor language they emit has its semantics *in Lean*:
`Satisfied2` is what it means for a trace to satisfy a descriptor, and
`vkOfRegistry` (`metatheory/Dregg2/Circuit/CircuitSoundness.lean:327`) is the
registry commitment the verification key denotes.

On top of the denotation sits the refinement family: each deployed effect's
descriptor instance carries a full-state soundness keystone, and the
registry-wide statement is proven whole —
`descriptorRefines_complete`
(`metatheory/Dregg2/Circuit/DescriptorRefinesComplete.lean:88`):
`∀ e, descriptorRefines (Rfix e) (kstepAll e)`, over all deployed effect tags,
no catch-all arm.

**This rung assumes** (the module's own residual census,
`DescriptorRefinesComplete.lean:37-52`): `Poseidon2SpongeCR hash` *inside*
each `descriptorRefines` — a terminal crypto floor sitting in the statement
itself; the `ClosureReadouts` extraction-carrier bundle `rds` (the per-effect
circuit-decode carriers, the census's "genuinely-hard residual"); and
`mkLog`, the `logHashInjective` log-commitment CR floor. The theorem's
signature additionally carries `compressInjective` / `cellLeafInjective` /
`RestHashIffFrame` carriers, which at the deployed instantiation are
hash-binding assumptions. The simplified statement above elides the
`S_live`/hash parameters where these premises live. The rung's connection
*downward* to the running system is rung 0's drift gate; its connection
*upward* is consumed by rung 2.

## Rung 2 — STARK soundness: accept ⇒ a real witness, on a named crypto floor

`kernelConfigSound` (`metatheory/Dregg2/Circuit/KernelConfigSoundness.lean:126`)
is the rung's headline: a `verifyBatch`-accept over the real registry `Rfix`
forces the existence of decoded kernel states and a genuine `fullActionStep`
between them — the machine evolved correctly, not merely "a trace satisfied
constraints". The full census of what is discharged versus carried is
[`reference/STARK-SOUNDNESS-CENSUS.md`](reference/STARK-SOUNDNESS-CENSUS.md);
the floor it rests on is short and named:

- **`Poseidon2SpongeCR`** — sponge collision-resistance (all Merkle/commitment
  binding reduces here).
- **`Poseidon2ChipArithSound`** — the Poseidon2 chip's round-gate output
  correctness, proven *distinct* from CR (`arithSound_not_CR`).
- **The FRI floor at deployed parameters** — see the FRI ledger below.
- **FS-SZ ε** — Fiat–Shamir non-exceptionality as a `ProbCrypto.winProb` game,
  not an axiom.

The rest of the crypto side reduces: RLC de-batching to Schwartz–Zippel,
commitment binding to `Poseidon2SpongeCR`, the LogUp bus to SZ, range tables
proven symbolically. One carried premise is neither crypto nor custody:
`kernelConfigSound` consumes `href : DeployedRefines`, inline-labeled in the
signature "code-refinement residual: Rust `verify_batch` ↔ Lean `verifyAlgo`"
(`KernelConfigSoundness.lean:152-154`). `DeployedRefinesProof.lean` proves
`DeployedRefines` is unprovable as stated — `verifyBatch` is `opaque`, with
no computational content to case on — and reduces it exactly to
`DeployedMatchesModel`: the opaque Rust `verify_batch` computes the model
verdict, which that file names as the one thing no Lean object there can
provide. The other carried hypotheses (`hbusF`, `hasm`,
`hrec`/`CanonicalHeapExtract`) have dischargers in-tree
(`AcceptanceDischarge.lean`, `IndexedMerkleTree.lean:392`); `DeployedRefines`
is the one whose remaining content is the named Rust↔Lean correspondence
itself. It appears as item 6 of the floor list below.

### The FRI ledger

FRI soundness is **two columns, never a product**
(`FriLedgerSound.query_ledger_does_not_determine_perFold` is a theorem):

- **The capacity column is refuted, and is carried only as a drift canary.**
  The proximity-gaps-to-capacity conjecture that production STARKs historically
  quote (~130 bits here) is disproven — Crites–Stewart (eprint 2025/2046, by
  reduction) and Kambiré (arXiv 2604.09724, counterexample over prime fields).
  No published counterexample instantiates at BabyBear, and that is *not* a
  defence: a conjecture refuted in general is not a security basis on a
  field-cardinality technicality. The deployed ledger says so in the code that
  ships it (`circuit/src/lib.rs:98-128`); the research record is
  [`reference/FRI-SOUNDNESS-FRONTIER-RESEARCH.md`](reference/FRI-SOUNDNESS-FRONTIER-RESEARCH.md).
- **The proven per-fold number for the dimension-2 (arity-2) fold is ~112.6
  bits — at the near-capacity radius; the DEPLOYED arity-8 fold carries ~109.84
  bits (`FriArityTransfer.arity8_perFold_soundness`), and ~112.6 provably fails
  there (`arity8_error_not_lt_2e112`).** `wrap_perFold_soundness_capacity`
  (`metatheory/Dregg2/Circuit/FriCorrelatedAgreementSharp.lean:1085`) proves
  the per-fold error `< 2⁻¹¹²` (exact ≈ 2⁻¹¹²·⁶) by the capacity-radius
  counting chain: the field-independent bound `|Good| ≤ C(64,2) = 2016`
  (`wrap_good_challenge_card_le_capacity`, `:939`) on the arity-2 constant
  fold — per the shipped ledger, "a 2-to-1 fold the deployed prover does NOT
  run" — resting on the near-capacity `dOut = 125` fiber bound
  `wrap_fiber_le_one` (`:919`). It does not rest on the Johnson-boundary
  result `wrap_correlatedAgreement_sharp_proved : WrapCorrelatedAgreementSharp
  292` (`:466`), which is a separate theorem in the same file. It is a
  structural theorem about *this* code, immune to the capacity refutation
  because it never invokes the conjecture. The shipped
  config it describes is the arity-2 `ir2_leaf_wrap_config` (112 bits); the
  deployed arity-8 wrap pays the moment-curve price and carries **109** per
  `FriArityTransfer.arity8_perFold_soundness` (`circuit/src/lib.rs:58-63`).
  The deployed ledger scopes both figures (`circuit/src/lib.rs:76-87`):
  "these numbers are claims about NEAR-CAPACITY words, not about the
  operating radius." The `M = 1` fiber discharge fires only for words
  `dOut ≥ 496` of `512` — 96.9%-far — while FRI's proven argument runs at the
  Johnson radius 87.5% (`dOut = 448`); `M = 1` is false in the band
  `[448, 496)` (`deployed_M1_false_at_johnson`), so 109 is true and
  non-vacuous about 96.9%-far words and does not cover the operating regime.
  At the Johnson radius the fiber bound is `M ≤ 7` and the count is
  `arity8_johnson_good_card_le`'s `3528` ⟹ ~111 bits — higher only because
  it is a weaker claim (it bounds the `dIn = 56` challenge family, not the
  larger `dIn = 62` one).
- **The query column is Johnson**: `num_queries·log_blowup/2 + pow` = 73 on six
  shipped configs, 71 on `create_recursion_config` — proven for any code, and
  explicitly the `m → ∞` idealisation that drops the commit-phase term.
- **The ledger is Lean-owned.** `FriLedger.friLedger` is a computable Lean
  function, `@[export dregg_fri_ledger]`
  (`metatheory/Dregg2/Circuit/FriLedger.lean:380`), and
  `circuit-prove/tests/fri_params_soundness_budget.rs` calls it per shipped
  config. Rust derives none of the figures.

**Named frontier:** composing both columns as ethSTARK eq. (20) at the measured
deployed trace heights reads well below the per-column headlines (the apex
posture, and the only route to a genuine proven-120 — the `d = 8`
extension-degree rewrite — are worked in
[`reference/PROVEN-120-CONFIG.md`](reference/PROVEN-120-CONFIG.md) and
[`reference/FRI-PARAM-FRONTIER.md`](reference/FRI-PARAM-FRONTIER.md)). The
operative ledger is the two columns read at their stated scopes — the Johnson
query column at the operating radius, the per-fold column at near-capacity;
the composed figure and the operating-radius per-fold posture are labeled
frontiers.

## Rung 3 — kernel guarantees, and the linking keystones

What the forced transition *means* is the kernel rung. `fullActionStep` is the
real declarative kernel step over `RecordKernelState` — accounts, per-asset
balances, caps, nullifiers, commitments, heaps and `heap_root`, fields, nonce —
with per-effect frame conditions proved (a transfer moves balances only, under
conservation Law 1; a noteSpend inserts nullifiers only) and the cross-step
frame derived, not assumed. The
[census](reference/STARK-SOUNDNESS-CENSUS.md) tables six deployed soundness
gaps at this layer (mod-p wrap forgeries, heap-sortedness double-spend,
cell-birth takeover), each with its fix in the re-keyed VK epoch. The rule
that keeps commitment bindings at full strength — every 32-byte component binds its source at the
8-felt ~124-bit encoding, never a 1-felt fold — is the
[Faithful-Commitment Law](FAITHFUL-COMMITMENT-LAW.md), enforced by an ast-grep
CI gate and the `Faithful8` type wall.

The rung's **linking** content is the `*BindingFromFold` keystone family
(`metatheory/Dregg2/Circuit/{Dsl,Sovereign,Membership,BlindedMembership,Custom,Hatchery,Deco,Factory,Bridge,Presentation}BindingFromFold.lean`).
Each closes the same seam: a bare per-effect AIR publishes an identity (a mint
hash, a membership root, a custom-leaf digest) that the AIR alone does not
force to be *backed* — the paired `*BackingAttack` module proves exactly that
omission. The keystone then proves the backing **from the fold**: the per-turn
aggregate re-verifies the real sub-proof leaf in-circuit and its combine
constraint ties the leaf's exposed identity to the published PI, so a verifying
aggregate *forces* a genuine backing witness. Taking the bridge instance as the
shape of the family (`BridgeBindingFromFold.lean`):

- `bridge_binding_from_fold` (`:167`) — a satisfying fold forces ∃ a verifying
  foreign note-spend whose digest *is* the published `mint_hash`, and the
  consumed nullifier is determined by it (anti-double-mint linkage via CR).
- `backedAt_from_fold` (`:200`) — the grounding onto the exact predicate the
  attack module proved the bare AIR omits.
- Non-vacuity at both poles: `honest_companion_fires` (`:250`) and
  `forged_unsat` / `forged_mint_hash_unsat_demo` (`:284`, `:313`) — the §A
  forgery the bare AIR admits, the aggregate refuses.

**This rung assumes**, per keystone, exactly the rung-2 set localized: the FRI
extraction floor (the same carrier `AggAirSound.FriExtract` opens),
`Poseidon2SpongeCR`, the identity factoring (the digest of a verifying
sub-proof is the sponge of its tuple), and the in-circuit connect. One scope
boundary is named: the bridge's consume-once freshness half rides
the executor's journaled nullifier set (`hfresh`), not a fold edge — the fold
contributes the linkage that makes the executor's uniqueness range over a
light-client-visible key.

## Rung 4 — the apex: light-client unfoolability

Two headline theorems, and their grounded forms:

- **Single transition** — `lightclient_unfoolable`
  (`metatheory/Dregg2/Circuit/CircuitSoundness.lean:570`): a `verifyBatch`
  accept forces decoded kernel states, the claimed effect's real step between
  them, and published commitments that *are* the genuine endpoint commitments.
- **Whole history** — `light_client_verifies_whole_history`
  (`metatheory/Dregg2/Circuit/RecursiveAggregation.lean:206`): checking only
  `verify agg.root = true`, a client obtains `AggregateAttests` — every turn
  executed correctly, ordered (no reorder/drop/insert), the final root the
  genuine fold of the whole history — plus the verify-side genesis anchor
  (`AnchoredAttests`) pinning the history's *start* to the client's trusted
  checkpoint, so no prefix can be hidden.

`GroundedApex.lean` re-rests both on proven carrier reductions rather than
assumed engine legs: `engineSound_grounded_v2` (`:149`) assembles the recursion
engine with all three legs *derived* — chain-ordering from the binding AIR
(`BindingAirSound`), per-leaf executor binding from the complete refinement
family (`WitnessRealizing` + `descriptorRefines_complete`), recursive soundness
from per-node `FriExtract` carriers (`RecursiveSoundFromNodes`) — yielding
`light_client_verifies_whole_history_grounded_v2` (`:202`) and
`lightclient_unfoolable_grounded` (`:232`). The remaining trust base of a
deployed light client is `{the FRI/recursion floor, Poseidon2SpongeCR, the
CommitSurface CR set}` plus the realizer data an honest prover supplies.

The apex family is itself gated: `#keystone_audit`
(`metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean`) requires every
unfoolability keystone to carry both a satisfiable honest instance (the light
client *fires* on a real chain) and a tooth (a tampered aggregate *cannot*
bind) — non-vacuity and refutation, as a CI-failing check.

## What the client is *not* entitled to believe

- **Freshness.** The apex covers *authenticity* of transitions and histories.
  A proof `(pi, π)` alone does not establish that its pre-state is current: a
  client wanting freshness tracks the live stored commitment and rejects any
  proof anchored elsewhere. The cross-turn no-replay close is proven
  (`Freshness.deployed_no_replay` /
  `CommitFaithfulRegrounded.no_replay_faithful`), with `Poseidon2SpongeCR` as
  its crypto residual — but it is the CAS's job, not the proof's
  (`CircuitSoundness.lean`, the scope note above `WitnessDecodes`).
- **A 128-bit headline.** There is no `2⁻¹²⁸` here. The ≥128 capacity gate is
  drift detection on refuted arithmetic; the numbers to believe are the
  per-column proven ones above, and the composed-ledger posture is a named
  frontier.
- **Anything a hypothesis carries.** Each rung's premise list above *is* the
  claim's boundary. The axiom-hygiene reports (`#assert_axioms` ⊆
  `{propext, Classical.choice, Quot.sound}` on every load-bearing arm) certify
  the proof terms, not the premises — which is why this document names the
  premises instead of waving at the reports.

## The floor, in one list

A deployed light client's entitlement reduces to:

1. `Poseidon2SpongeCR` — one hash's collision resistance.
2. `Poseidon2ChipArithSound` — the chip's arithmetic correctness (distinct
   from 1).
3. The FRI floor at deployed parameters — per-fold proven ~109.84 bits at the
   deployed arity-8 fold (`FriArityTransfer.arity8_perFold_soundness`; the
   ~112.6 dimension-2 figure provably fails at arity 8,
   `arity8_error_not_lt_2e112`), both about near-capacity words rather than the
   operating radius; the deployed **query-soundness floor is ~31.5 bits** at the
   unique-decoding radius δ=7/16 (`(9/16)³⁸ < 2⁻³¹`,
   `DeployedProximitySoundness`) — the 71–73 Johnson figure is the m→∞
   idealisation that drops the ε_C commit term; capacity refuted and demoted to
   a canary.
4. The FS-SZ game bound.
5. Rung 0's operational custody (CI, git, the VK pin).
6. `DeployedRefines`, reduced by `DeployedRefinesProof.lean` to
   `DeployedMatchesModel` — the opaque Rust `verify_batch` computes the Lean
   model verdict. Neither a crypto floor nor build custody: custody says the
   binary came from the checked tree; this says the checked tree's Rust
   semantics match the Lean spec.

Everything above those six is a theorem in `metatheory/Dregg2/`, and the exact
proof inventory with its scope labels is
[`../metatheory/CLAIMS.md`](../metatheory/CLAIMS.md). The kernel-side story of
what the proven step *means* is [`KERNEL.md`](KERNEL.md); the system spine is
[`OVERVIEW.md`](OVERVIEW.md).
