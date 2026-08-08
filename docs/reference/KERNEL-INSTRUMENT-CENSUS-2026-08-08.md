# Kernel instrument census — 2026-08-08

Scope: `turn/` `cell/` `cell-crypto/` `circuit/` `circuit-prove/` `persist/` `exec-lean/`
`dregg-lean-ffi/` `bridge/`.

Method: the four questions that paid out in the Path of Angels sweep, pointed at the kernel.

| # | Class |
|---|---|
| **Q1** | a gate watches a **SOURCE** while the consumer reads an **ARTIFACT** |
| **Q2** | a **refusal shares a representation** with a success or an honest reject |
| **Q3** | a **negative test passes because the thing under test never ran** |
| **Q4** | a **docblock asserts compliance with a law the file violates** |

Verdicts: **(a)** an instrument that cannot fire · **(b)** a live defect the instrument was
hiding · **(c)** sound.

## Counts

| Class | (a) cannot fire | (b) live defect | (c) sound | total |
|---|---|---|---|---|
| Q1 | 5 | — | 2 | 7 |
| Q2 | 3 | 17 | 5 | 25 |
| Q3 | 6 | 1 | 4 | 11 |
| Q4 | 2 | 4 | — | 6 |
| **total** | **16** | **22** | **11** | **49** |

A finding is counted once even where it spans many sites: BR-1 is one Q2 (b) covering twelve
wrappers; BR-3 is one Q3 (a) covering 24 guard sites.

**The headline is the (b) column.** 22 of the 49 are not dead instruments — they are live defects
that a dead instrument was hiding, and every one of them sits on a verification, consensus or
admission path.

Plus a mechanical sweep: **44 of 1382** error/verdict variants across 199 kernel enums are
**defined, `Display`-formatted, matched in a handler, and constructed zero times** (script and
full table at the end). That count is the purest available measure of "instruments that cannot
fire", and three of them turned out to be class (b).

Provenance of each row is marked: **MEASURED** = read at source and/or executed by this lane;
**SUB-MEASURED** = measured by a fan-out lane, source-quoted, not independently re-executed here.

---

# Ranked by blast radius

## BR-1 — ⚑⚑⚑⚑ Twelve verified-gate wrappers render "I could not read the wire" as a REJECT verdict

**Class Q2 (+Q4). (b) LIVE DEFECT. FIXED this pass.** MEASURED.

`dregg-lean-ffi/src/bridge_lc_ffi.rs`, twelve sites (pre-fix lines 143, 276, 473, 664, 843, 1041,
1220, 1407, 1604, 1917, 2153, 2432), each:

```rust
let out = shadow_<gate>(&wire)?;
Ok(if out == "1" { Verdict::Accept } else { Verdict::Reject })
```

The gate grammar is `"1"` | `"0"` | `"ERR"`, where **`"ERR"` means the Lean gate refused to READ
the wire Rust built** — the subject was never examined. The decoder put that inside the verdict
type. Callers then mint named factual claims from the `Reject`:

| caller | claim minted from a possible `"ERR"` |
|---|---|
| `bridge/src/mina_observer.rs:1201` | `ObserveError::WrapProofNotChained { child_height, parent_height }` — "these two real blocks are not a Pickles-recursion chain" |
| `bridge/src/mina_observer.rs:1294` | `ObserveError::HeaderBindingMismatch { block_height, served_state_hash }` — "this peer re-labelled the proof" |
| `bridge/src/mina_observer.rs:1137` | `PicklesOutcome::Refused` — a `false` into the finality conjunct |
| `eth-lightclient/src/verified_gate.rs:126,338`, `eth-lightclient/src/evm.rs:580`, `cosmos-lightclient/src/verified_gate.rs:290,444` | `Ok(false)` = "the light client rejects this update" |

So a rendering drift in any projection (`decimal_of_le32`, the 16-limb challenge arrays, the eight
decimal lists at `mina_observer.rs:1254-1289`) accuses an honest peer of forgery, and the
accusation is **byte-identical to a real one**.

This is not hypothetical. `bridge/src/mina_head.rs:885-890` records the same fusion having
**already fired once**, in the fork-choice gate: *"every call here decoded to `"ERR"`.
`verified_mina_better_tip` maps every non-`"1"` output to `KeepExisting` … which means the two
assertions expecting `KeepExisting` … were satisfied by a refusal."* That wound was diagnosed; the
decoder it names was never changed, and eleven siblings shared it.

**Q4 half:** four sibling gates in the same file (`verified_mina_wrap_challenges` :3700,
`verified_mina_wrap_ft_eval0` :3765, `verified_mina_checkpoint_advance` :4036,
`verified_mina_head_advance` :2240) already do `if out == "ERR" { return Err(..) }`. And
`bridge_lc_ffi.rs:1388-1390`, directly above the broken proof-chain decoder, states the discipline:
*"the caller must treat that as a REFUSAL with its own distinct error, never as a skipped check and
never as a proved `no`."* True of the ABSENT-archive case it was written for; false of `"ERR"`, one
line below it. `bridge/src/mina_observer.rs:1164-1168` states the same rule and separates only the
absent case.

**Fix (landed):** a strict `decode_gate_bit(gate, out)` — `"1"`→`Ok(true)`, `"0"`→`Ok(false)`,
**everything else → `Err`**. Malformed is no longer a member of the verdict type. Still fail-closed
(every caller already refuses on `Err`; verified at all 9 production call sites), but the refusal
now carries the right cause. 19 docblocks that asserted the old behaviour were corrected.

## BR-2 — ⚑⚑⚑⚑ The MSM/gate cross-check cannot fire on the polarity it exists for

**Class Q2+Q4. (a)+(b). FIXED this pass.** MEASURED.

`bridge/src/mina_accumulator_discharge.rs:505` (pre-fix):

```rust
let gate_ok = answer == "1";
let computed = receipt.verdict == Verdict::Discharged;
if gate_ok != computed { return Err(DischargeError::GateDisagreed { computed, gate: answer }); }
if !computed { return Err(DischargeError::Refused("the batched MSM … did not vanish")); }
```

When the MSM refuses (`computed = false`) **and** the gate answers `"ERR"`, `gate_ok == computed`
holds, `GateDisagreed` does not fire, and `discharge` reports `Refused` — as though the verified
gate had **concurred** — when the gate had decided nothing. The cross-check could only ever fire on
the positive polarity, which is the half that needs it least.

The function's own docblock (`:490-495`): *"ask the VERIFIED gate, then refuse unless both say yes
… A disagreement … is `GateDisagreed` — never a silent preference for either."* `GateDisagreed`'s
variant doc (`:118`) goes further: *"answered something other than the discharge we computed, **or
`ERR`**"*. The code could not produce that. Consumed on the turn path via
`exec-lean/src/mina_accumulator_oracle.rs:102`, whose `Err` gates a turn.

**Fix (landed):** decode to a two-valued verdict *first*; a non-verdict answer returns
`GateDisagreed` before any comparison. `gate_ok` is now constructible only from an actual verdict.

## BR-3 — ⚑⚑⚑⚑ `persist/` has 24 silent skip guards and zero `demand_lean`

**Class Q3. (a).** MEASURED (guards, dependency, archive presence, live run).

The repo built a purpose-made fail-loud gate for exactly this wound —
`dregg_lean_ffi::demand_lean` (`dregg-lean-ffi/src/lib.rs:290`), **armed by default** (UNSET ⇒
armed, `lib.rs:271-276`), which panics naming the missing capability instead of letting a test
report `ok`. `TESTQALOG.md:589` records 17 sites in 13 files converted. **`persist/` was never
converted**: `rg -c demand_lean persist/` returns nothing, while `persist/Cargo.toml:32` depends on
`dregg-lean-ffi`.

24 raw guard sites across 21 test fns, all bottoming out in `poa_world_activation_available()`
(`dregg-lean-ffi/src/poa_world_activation_ffi.rs:11`) — a **runtime** check — with no `eprintln`
and no arming:

| file | sites |
|---|---|
| `persist/src/commit_log.rs` (`galley_native_available`, :4407) | 8 |
| `persist/src/poa_world_activation.rs` (`require_native`, :1153) | 6 |
| `persist/tests/poa_epoch2_multiplexed_world.rs` (:134) | 3 |
| `persist/src/poa_galley_authority.rs` (:1970, :2294) | 2 |
| `persist/src/poa_activated_content.rs` (:609) | 2 |

These sit on the PoA world-activation / galley-authority path and are named for the refusals they
check (`..._rejects_invalid_signature_after_staging_and_rolls_back`,
`..._refuses_replay_invention_...`, `..._wrong_current_world_rolls_back_every_weld`).

**Measured on this box:** the archive IS linked (`dregg-lean-ffi/libdregg_lean.a`, 178 MB, cfgs
emitted) and `cargo test -p dregg-persist --lib poa_world_activation` ran 10 tests for 321 s — they
really executed here. **On CI they do not**: the Q1 lane measured `Test (ubuntu-latest)` and
`Test (macos-latest)` both failing with `no dregg-lean-ffi/libdregg_lean.a after the seed fetch`.
Any lane that gets past that point reports `ok` for all 21 having asserted nothing.

Two special cases inside the cluster:

* `persist/src/poa_galley_authority.rs:2278` — `preparation_refuses_absent_or_substituted_active_world_before_play`.
  The first `is_err()` leg runs on an **empty store**, so it passes for the trivial reason "no world
  is installed at all". The **substituted-world** leg — the actual claim in the name — sits behind
  the guard at :2294. Half the name is never tested; the other half is vacuous.
* `persist/src/poa_world_activation.rs:1266` — `absent_native_export_refuses_preparation_without_a_rust_twin`
  has an **INVERTED** guard (`if require_native() { return; }`), so on a correctly-built lane it
  asserts nothing at all, and on a broken one its only assertion is that a missing export produces
  an error. Setup-failure-as-assertion in its purest form.

## BR-4 — ⚑⚑⚑⚑ The only descriptor gate that re-derives from Lean has never produced a verdict

**Class Q1. (a), and (b) downstream.** SUB-MEASURED (workflow config + GitHub run API + commit
counts); the artifact/consumer wiring re-checked here.

125 `circuit/descriptors/by-name/*.json` are `include_str!`d into live AIRs
(`circuit/src/effect_vm_descriptors.rs:79-106`, `membership_descriptor_4ary.rs:141`,
`note_spend_witness.rs:72`, `cross_cell_conservation_air.rs:80`, `mina_fixture_emit.rs:132`). Those
bytes **are** the deployed circuits and their VKs.

Five gates watch them. **Four compare the artifact against a stamp that sits beside it** —
`every_descriptor_fp_matches_its_json_bytes` (`effect_vm_descriptors.rs:2368`),
`provenance_json_pins_match_checked_in_descriptor_bytes` (:2433), `emit_descriptors.py:959`
`verify_provenance`, and `check-emit-gate-weld.py` (checked-in copy vs checked-in copy). All five
stay **GREEN on a wholly stale set**. The repo says so itself at
`scripts/check-descriptor-drift.sh:6-10`.

The one honest gate — `check-descriptor-drift.sh`, which re-emits from Lean and diffs — is
`if: github.event_name != 'push'` (`ci.yml:1920`), so it is skipped on every push to main, and the
nightly has never finished it: 08-06 killed at 60 min inside the 158-module Lean corpus build,
08-07 cancelled, 08-05 skipped, 08-03→07-31 failed in the static preflight. The local row
(`scripts/local-gates.sh:238`) is hand-invoked only.

**Consequence, measured:** since the last recorded re-emit (`docs/VK-REGEN-LOG.md`, commit
`f7bc7d351`, 2026-08-07) there are **8 commits touching `metatheory/Dregg2/Circuit/Emit/`
(31 files, +4150/−547)**, including two brand-new emitters. `circuit/descriptors/**` is currently
gated only by self-consistency.

Named residual found alongside: `circuit-prove/src/shielded/deshield.rs:7` claims *"Both are read
byte-pinned out of the Lean sources"* — its sibling `transfer_link_2out.rs:98` really does
`include_str!` its `.lean`, but `deshield.rs` has **no `include_str!` at all**. (Class Q4, (b).)

### ⚑ LIVE CORROBORATION, measured 2026-08-08 in the shared tree

`cargo test -p dregg-bridge --lib mina_` is **91 passed / 3 failed at HEAD**, and all three failures
are this class firing:

```
mina_opening_check::tests::the_embedded_lean_artifacts_are_pinned_and_parse         FAILED
  bridge/src/mina_opening_check.rs:945 — resolve_descriptors().expect("the pinned descriptors must resolve")
mina_observer::tests::opening_check_proves_and_verifies_on_a_real_devnet_block_end_to_end  FAILED
mina_observer::tests::a_foreign_challenge_vector_is_refused_through_the_opening_check_wiring FAILED
```

`resolve_descriptors()` is `check_pin` (sha256 of the compiled-in JSON against a pinned hash) +
`parse_vm_descriptor2` + shape checks — **pure artifact validation**, touching no FFI, no gate and
no verdict decoding, so it is independent of every fix in this document (verified: the
`prove_opening_check` path contains zero `verified_*`/`shadow_*`/`decode_gate_bit` calls).

The exact refusal, captured 2026-08-08:

```
the pinned descriptors must resolve: DescriptorMalformed {
  artifact: "pasta-rcb-sg-derive-0-of-10922.json",
  why: "constant at byte 169907 does not fit a BabyBear felt (19 decimal digits,
        p_babybear = 2013265921). A gate body carrying it cannot round-trip the field, so its
        integer semantics say nothing about any proof over it. Re-emit on a felt-sized encoding
        (Dregg2.Circuit.Emit.PastaFieldSound), or parse through the named unsound escape." }
```

So this is **not** a hash drift — it is `parse_vm_descriptor2` exercising a **felt-width soundness
refusal** against a compiled-in Mina opening-check descriptor whose constants do not fit the field
the proof is taken over. A working instrument, red at HEAD, correctly saying the artifact needs a
re-emit — which is precisely what BR-4 predicts while the only re-deriving descriptor gate never
completes. It also touches the felt-width campaign (`project-felt-width-repair-campaign`: width
bounds the IMAGE, not the attack).

**Not touched by this lane.** It is a world problem, not a gate problem — the fix is a re-emit on
`PastaFieldSound`, which belongs to whoever owns the Mina opening-check emitter. Recorded here so
it is findable, and so nobody "fixes" it by routing through the named unsound escape.

## BR-5 — ⚑⚑⚑ Three Lean-seed freshness gates, none wired to any workflow

**Class Q1. (a).** SUB-MEASURED.

The artifact is `dregg-lean-ffi/libdregg_lean.a`. A stale or short member makes `build.rs` emit no
cfgs, every `#[cfg(dregg_*_present)]` module compiles out, and ~43 guarded tests report `ok`
(this is the mechanism behind BR-3). Three gates exist, each reading a different proxy —
`check-lean-seed-freshness.sh` (two strings), `check-lean-seed-closure.sh` (member *names*),
`check-lean-seed-member-freshness.py` (member **mtimes** — the real one). `grep -rn
"check-lean-seed" .github/` hits **only `.github/dark-targets.txt`**, i.e. prose. All three live
solely in `scripts/local-gates.sh`.

The member-freshness gate landed 2026-08-07 in response to precisely this class:
`deployed_constraint_probe` printed `8 passed` daily 07-30→08-06 with six of eight assertions
false, because the archive carried a 07-25 object. **It is a good gate wired to nothing automatic.**

## BR-6 — ⚑⚑⚑ `fast_path` asserts a nonce check in three docblocks and does not perform one

**Class Q4 + Q2. (a)+(b).** MEASURED.

`turn/src/fast_path.rs`. `FastPathError::NonceMismatch { cell_id, expected, got }` (:54) is
defined, `Display`-formatted (:94-106), and **constructed zero times**. Three docblocks say
otherwise:

* `:331` — *"then cheap checks (**nonce**, fee, ownership, lock availability)"*
* `:346` — *"If any cell in the write set cannot be locked (already held **or nonce mismatch**), no locks are acquired"*
* `:384` — *"3. Extract write set and **verify nonces** + lock availability."*

The code beneath that third comment reads `let nonce = cell.state.nonce();` and uses it **purely as
a lock-table key**. The turn's own declared nonce is never compared against it. Live path:
`node/src/api.rs:7316`.

Impact is bounded — the lock key uses the ledger's nonce, so the module's equivocation argument
(:26) still holds, and a stale-nonce turn is caught later at execution — so this is lock-slot
squatting and a wasted certificate round, not a forgery. Ranked here for the **docblock/behaviour
gap**, which is what makes it dangerous to the next reader.

Three siblings in the same enum are also never constructed: `BudgetExhausted`, `LockExpired`,
`HasDependencies`. `HasDependencies` is dead because `is_fast_path_eligible` (:288) returns **bool**
and collapses every disqualification into `NotEligible` — a small Q2 in its own right.

## BR-7 — ⚑⚑⚑ `verify_finalization_quorum` fuses six distinct falses; eight tests read the fused value

**Class Q2. (b).** SUB-MEASURED, source-quoted.

`persist/src/federation.rs:256` returns `bool` with six causes: no `blocklace_block_id` (:265 —
*structural, "not yet anchored"*), `len < threshold` (:268), misaligned PQ roster (:274 — a
**config error**), non-member signer (:289), bad ed25519 (:293), unpinned/bad ML-DSA (:302,:305).
The crate knows these differ — `has_finalization_quorum` (:222) exists **only** to separate "not yet
anchored" from "claims a quorum". Consumed as authority at `node/src/state.rs:1857`, `:1948`,
`node/src/exact_fnsp_v3_actor_authority.rs:215`. Eight negative assertions read the fused value
(`persist/src/tests.rs:786, 818, 831, 846, 859, 869, 879, 1006`).

## BR-8 — ⚑⚑⚑ Consensus decoders where "could not parse" is the quorum answer

**Class Q2. (b).** SUB-MEASURED, source-quoted.

* `dregg-lean-ffi/src/distributed_ffi.rs:162` `decode_quorum_root` → `Option`. `None` is produced by
  `"NONE"` (**legitimately no quorum**), by `"ERR"`, by a malformed body, and explicitly by a stale
  v3-shaped archive reply. Consumed at `node/src/finalization_votes.rs:652`, whose doc reads
  *"`Ok(None)` ⇒ no quorum"*. A grammar-drifted or stale-archive node reports "no quorum reached"
  **forever**, indistinguishable from an honest sub-threshold tally.
* `distributed_ffi.rs:121` `verified_tau_order` → `Ok(decode(..).unwrap_or_default())`. Malformed ⇒
  **empty finalized total order**, identical to a legitimately empty one. Caller
  `node/src/finality_gate.rs:195`.
* `distributed_ffi.rs:64-76` `verdict_admits` / `verified_admits` → `Ok(false)` = "not admitted" ∪
  "ERR" ∪ malformed. Feeds the federation strand-admission decision
  (`exec-lean/src/distributed_gates.rs:67`, `node/src/strand_admission_gate.rs:19`).
* `distributed_ffi.rs:428` `verified_happened_before` — **note the polarity**: here `false` is the
  *permissive* answer in a causal-conflict check, so this one is not obviously fail-closed. Flagged
  for someone who knows the coord consumer; not fixed.

## BR-9 — ⚑⚑⚑ An un-marshalled cell is handed to the verified authority as "this signature is FORGED"

**Class Q2. (b).** MEASURED (re-verified at source by this lane).

`exec-lean/src/lean_shadow.rs:2422-2431` `sig_echo_wire`. The `None` arm even carries the comment
`// cell absent ⇒ cannot verify ⇒ fail-closed` — the author saw the distinction and then wrote it
to the same `false` that means "this signature is invalid": the verdict is `false` when the target
cell is **absent from the marshalled set** and when the pubkey **is not a curve point**, and that
`false` is rendered as the bit fed to the verified gate's WHO leg (:2380-2387). The differential
then reports a signature forgery where the truth is an un-marshalled cell. This is the exact
archetype (a *wire-render* function fusing malformed with reject).

## BR-10 — ⚑⚑⚑ Solana vote tally: a vote that fails to parse counts the same as one that voted differently

**Class Q2. (b).** MEASURED (re-verified at source by this lane).

`bridge/src/solana_wire.rs:495-502` `witness_binds(..) -> bool` with `Err(_) => false`. The tally
consumes it as `if !v.verify_signature() { continue; }` (`solana_consensus.rs:405`), so an
unparseable vote is **silently dropped from a stake-weighted supermajority computation**, exactly
as a vote for a different fork would be — and those two want opposite responses. A vote
transaction that fails to parse, or whose signatures fail, is the same value as one that parsed and
voted a **different** `(slot, bank_hash)`. Pure consensus caller chain:
`solana_consensus.rs:283 verify_signature` → `:405` `tally_votes` (`if !v.verify_signature() {
continue; }`) → `:420` `verify_supermajority`. The three negative assertions at
`solana_wire.rs:905-907` ("wrong account / wrong slot / wrong bank hash") are satisfiable by any
parse failure.

## BR-11 — ⚑⚑ Presentation / credential verifiers where five causes share one `None`

**Class Q2. (b).** SUB-MEASURED, source-quoted.

* `bridge/src/present.rs:2847` `verify_fact_attestation -> Option<BabyBear>`: `None` from root
  mismatch, state-root mismatch, unknown descriptor, undecodable postcard, **a panic**
  (`catch_unwind(..).unwrap_or(false)`, :2874), and a genuine failed STARK. Consumed as a verdict at
  :2947 inside `verify_predicate_proof_third_party -> bool`. Same construct at :2996.
* `circuit/src/presentation.rs:89-97` `verify_descriptor_wire -> Option<Vec<BabyBear>>`: five
  sources of `None`, `.unwrap_or(false)` at :96. Consumed at `bridge/src/present.rs:2340-2343` and
  `bridge/src/verifier.rs:352-354`.
* **Corroborating dead instruments:** `VerifyError::DeserializeFailed` and
  `VerifyError::MalformedPublicInputs` (`bridge/src/present.rs:2030, :2046`) are **never
  constructed** — the two variants that would name a malformed presentation do not exist in
  practice, which is what one expects when malformed has been folded into `false`. This path is
  documented (`present.rs`) as reachable from a public HTTP header via
  `app-framework/src/middleware.rs` → `sdk::embed::verify_presentation_bytes`.

## BR-12 — ⚑⚑ Note-bridge and capability refusals fused with local-config absence

**Class Q2. (b).** SUB-MEASURED, source-quoted.

* `cell-crypto/src/note_bridge.rs:1221-1244` `verify_bridge_receipt -> bool`: `false` for **no key
  registered for that destination federation** (:1229, local config), a registered key that is not a
  valid point (:1241), and a forged signature. Gates `finalize_bridge`, which **burns the owner's
  note**. Corroborating: `BridgeError::NullifierMismatch` and `BridgeError::ValueMismatch` are
  never constructed.
* `cell/src/interface.rs:441` `verify_route_membership -> bool` = `matches!(.., Ok(true))` — an
  undecodable `AirTrace` ≡ "the DFA rejects this method", on an **admission/dispatch** decision.
* `turn/src/turn.rs:951` `ConsumedCapability::verify -> bool` = `recompute_root() == Some(..)`,
  where `recompute_root`'s own doc (:922) says `None` means *malformed witness*. The docblock
  claims *"NON-vacuous — a tampered leaf field … makes this false"*; so does a witness that was
  never well-formed. (Q4.)
* `turn/src/composer.rs:405-416` `verify_coordinator_signature -> bool`: **not yet signed** (:406)
  ≡ malformed key ≡ forged.
* `turn/src/reversible.rs:940,978`: *"the history could not be replayed"* ≡ *"this turn is
  irreversible"*.

## BR-13 — ⚑⚑ Negative tests whose assertion is satisfied by their own setup failing

**Class Q3. (a).** SUB-MEASURED, source-quoted.

* `circuit-prove/src/private_shuffle_fair.rs:951` — `descriptor().unwrap()` is **inside** the
  `catch_unwind` closure, and the assertion is `refusal.is_err() || refusal.unwrap().is_err()`. If
  the descriptor stops building, or the trace shape drifts, the test passes. Same shape at
  `private_shuffle.rs:579` and `private_raid_assignment.rs:639`.
* `cell-crypto/src/oblivious_transfer.rs:511,535` — the OT **sender-privacy** property is
  `assert!(decrypted_m1.is_none() || decrypted_m1.unwrap() != m1)`, satisfied by `None` for any
  reason (truncated ciphertext, AEAD tag-length drift). A positive control earlier in the fn rescues
  the "totally broken" case but not a shape change.
* `dregg-lean-ffi/src/poa_bazaar_runtime_ffi.rs:228-235` — three untyped `is_err()` whose entire
  premise is that the archive is missing. On CI the cfg is false and the test does not exist; on a
  dev lane it passes because the setup failed.

Aggregate counts (SUB-MEASURED): **155** bare `is_err()`/`is_none()` assertions kernel-wide, of
which **109** are in refusal-named tests and **75** never check a variant or message; **38**
refusal-named tests with an untyped assertion and **no positive control in the fn**; **159**
`#[ignore]` in kernel crates (circuit-prove 138), including the forged-root refusal poles at
`circuit-prove/src/joint_turn_recursive.rs:1637,1680,2121,2169` and four in
`circuit-prove/tests/accumulator.rs`. `circuit-prove/src/custom_proof_bind.rs:49` self-documents:
*"Both are `#[ignore]`d and nothing in CI passes `--ignored`, so the deployed end-to-end poles are
not exercised in automation at HEAD."*

## BR-14 — ⚑⚑ Falsifier mutations with no "the substitution bit" guard

**Class Q3. (a).** SUB-MEASURED, source-quoted.

The repo knows this shape — `circuit/src/descriptor_ir2.rs:8435` reads
`assert_ne!(j, DEMO_V2, "the substitution must have bitten");`. Its sibling 100 lines down does
not: `:8540` `refuses_tampered_chip_params` does a `.replace("\"partial_rounds\":13", …)` with no
`assert_ne!` and **no positive control that `DEMO_V2` itself parses**. **27 of 53** in-test
`replace`/`replacen` mutation sites lack the guard. Worst of the rest:
`circuit/tests/direct_logic_descriptor_translation_validation.rs:327,331,621,625` — four mutations
plus four bare `is_err()`, and if the pinned BLAKE3 at :22 ever goes stale, `load_pinned` errors for
*every* input and both tests are permanently green while testing nothing.

## BR-15 — ⚑⚑ A VK-identity gate that is green wherever the check is impossible

**Class Q1. (a).** SUB-MEASURED.

`bridge/mina-zkapp/scripts/vk-identity-gate.ts`. Leg [1] checks the **producer script exists** — a
source question. Leg [2] compares pin-to-producer, but only `if (w.source === 'producer')`; the
producer key ring lives under gitignored `.fullchain/`, so on every clean checkout and every CI
runner it takes the `else` branch at :366-378, prints *"⚠ self-test: [2]'s DRIFT CHECK IS UNPROVEN
ON THIS MACHINE"*, and **continues**. The exit code does not carry the warning. A pin that drifted
from its 131 compiled VKs is accepted anywhere the chain was not compiled.

## BR-16 — ⚑ XMSS verification cannot report *why* it failed

**Class Q2. (a).** MEASURED.

`circuit/src/xmss.rs`. `XmssError::RootMismatch` (:32) and `XmssError::WotsVerifyFailed` (:34) are
defined, `Display`-formatted (:42-43), and never constructed, because `xmss_verify` (:277) returns
**bool** — both failure modes collapse to `false`. Low blast radius: the only non-test mention
outside the file is a docblock at `federation/src/epoch.rs:432`, so there is no production consumer
today. Recorded because it is the cheapest possible illustration of the class and because the
docblock at `federation/src/epoch.rs:432` advertises it as the "real, tested" key tree.

---

# Fixes landed, and what each repaired instrument immediately caught

## Fix 1 — `decode_gate_bit`: malformed is no longer a member of the verdict type (BR-1)

`dregg-lean-ffi/src/bridge_lc_ffi.rs`. All twelve wrappers now route through one strict decoder;
19 docblocks corrected.

**Red-proof (a), unit, constructive.** In `wire_grammar_matches_lean_decodeEthWire`:
`shadow_eth_lc_verify("garbage") == Ok("ERR")` is asserted FIRST — the plant lands and the gate
really is reached — and only then `decode_gate_bit(.., "ERR").is_err()`, plus `"1"`→`Ok(true)`,
`"0"`→`Ok(false)`, and `""`/`"2"`/`"1 "` all `Err` (an off-grammar token is archive/decoder drift,
not a `no`). The block this replaced *reproduced the buggy decoder inline* and asserted
`Ok(Reject)` — a test that enshrined the fusion.

**Red-proof (b), end-to-end through the real Lean gate.**
`a_malformed_projection_is_not_a_proof_chain_verdict` feeds `verified_mina_proof_chain_ok` a
coordinate that is not a decimal — the exact shape a `decimal_of_le32` drift produces. Leg 1
asserts the plant bit (`shadow_… == Ok("ERR")`) so a mutation that had quietly stopped biting
cannot pass. Leg 2 asserts the wrapper returns `Err`, never
`Ok(MinaProofChainVerdict::Reject)` — the value `mina_observer.rs:1192` converts into
`WrapProofNotChained`. A third leg proves the gate still answers `"1"`/`"0"` on a well-formed wire,
so the refusal is attributable to the malformation and not to a dead gate. **PASSES.**

### ⚑ What the repair caught, within one test run

`mina_fork_choice_decides_on_real_devnet_bytes_through_the_real_ffi` went **RED** on

```
left:  Err("the VERIFIED gate `dregg_mina_better_tip` REFUSED TO READ the wire … ")
right: Ok(KeepExisting)              // "bytes that are not a protocol state must not displace the head"
```

That assertion, and two more in `bridge/src/mina_head.rs`, are **the very assertions
`mina_head.rs:885-890` had already diagnosed** — *"the two assertions expecting `KeepExisting` …
were satisfied by a REFUSAL and would have stayed green with the decoder deleted."* The 2026-08-02
repair fixed the fixture hashes so the real cases decode; it left the decoder able to keep
manufacturing `KeepExisting` out of `"ERR"`, so the surviving refusal-shaped assertions still could
not tell a refusal from a verdict.

Three assertions fixed — and the fix **strengthens** them, it does not relax them. Each said "a
malformed/bogus input yields `Ok(KeepExisting)`", a value a genuine `select` also produces; each
now says "yields `Err`", which only a non-verdict can produce:

| site | was | now |
|---|---|---|
| `dregg-lean-ffi/src/bridge_lc_ffi.rs` (non-`Protocol_state` bytes) | `== Ok(KeepExisting)` | `.is_err()` + `assert_ne!(.., Ok(KeepExisting))` |
| `bridge/src/mina_head.rs` (bogus served hash `"1"`/`"1"`) | `== Ok(KeepExisting)` | `.is_err()` |
| `bridge/src/mina_head.rs` (mislabelled pair `"1"`/`"2"`) | `== Ok(KeepExisting)` | `.is_err()` |

The comment sitting directly above the first of these read *"A REFUSAL IS NOT A VERDICT COMPUTED
FROM WHAT DID PARSE"* — over an assertion that made it into one, while the sibling roll gate on the
next line correctly returned `Err` for the same `"ERR"`. Two gates, one input, two answers. They
now agree.

## Fix 2 — `discharge` refuses a non-verdict before comparing (BR-2)

`bridge/src/mina_accumulator_discharge.rs`. `gate_ok` is now built by a `match` on `"1"`/`"0"`,
with any other answer returning `GateDisagreed` **before** the comparison — so the fused case
(`computed == false` and gate `"ERR"`) can no longer read as concurrence. `GateDisagreed`'s
docblock claim *"or `ERR`"* is true for the first time.

## Fix 3 — `persist/` skip guards armed (BR-3)

Every guard now routes through `demand_lean`, so an absent archive PANICS naming the capability
instead of printing `ok`: `poa_world_activation.rs` (`require_native`),
`commit_log.rs` (`galley_native_available`, `install_active_poa_world`),
`poa_galley_authority.rs` (`native_available`, the substituted-world mid-test leg, the
activated-content conjunct), `poa_activated_content.rs` (`native_available`),
`persist/tests/poa_epoch2_multiplexed_world.rs` (`native_available`, the night-watch conjunct).

The one INVERTED guard (`absent_native_export_refuses_preparation_without_a_rust_twin`) is
deliberately left on a newly-separated raw `native_present()` bit, because the absence of the
export is that test's subject — with a comment saying so, and its residual named.

**Red-proof, constructive, three legs** (measured 2026-08-08 on a box where the archive IS linked,
so the absent case had to be planted):

| leg | state | result |
|---|---|---|
| A — control | plant compiled in but inactive | `rollback_requires_recorded_digest_and_exact_target_world` … **1 passed** (794 s of real work) |
| B — plant ACTIVE, guard armed (the default) | `native_present()` forced `false` | **FAILED**, `MISSING VERIFIED CAPABILITY: cannot exercise the PoA world-activation verified authority path (dregg_poa_world_activation_*)` |
| — | plant removed, worktree re-verified identical to the commit | `git diff` clean |

The plant was asserted to have landed (`grep -c` = 1) before leg B's verdict was read. **Leg B is
the whole finding**: that same state — no linked archive — printed `ok` before this change, for
this test and twenty others.

---

# Sound — checked and NOT ambiguous (the local fix vocabulary)

Worth naming, because these are the shapes the fixes above should imitate:

* **`dregg-lean-ffi/src/lib.rs:660-697`** `shadow_cross_cell_conserves` distinguishes bare `"0"`
  (malformed ⇒ `Err`) from `"0 <asset> <imbalance>"` (a real imbalance). **This is the model.**
  Same file, :719-758 (dated 2026-08-07) records the ML-DSA repair that introduced a **third**
  output `"2 <fault>"` after `"0"` had been both "forged" and "could not evaluate" on ~10 gating
  surfaces.
* **`exec-lean/src/constraint_oracle.rs:470,536`** — `None` = **DECLINE**, and
  `cell/src/program/eval.rs:403-417` refuses to read a decline as a verdict
  (`undecided_subset_disposition`).
* **`turn/src/executor/atomic.rs:743-776`** — oracle absent ⇒ `ConservationGateUnavailable`, never a
  conservation verdict.
* **`circuit/src/descriptor_by_name.rs:63-67`** — `GOLDEN_CACHE` is built with
  `filter_map(.. .ok())`, so a golden whose bytes stop decoding is silently dropped and dispatch
  answers `None`. That IS the class — but it is **already closed**: the module documents it at
  :850-858 and :948-960, and the table-DERIVED cover `every_static_golden_decodes_and_dispatches`
  (:1071) walks `STATIC_GOLDENS` itself rather than a transcribed name list, so a row that stops
  decoding goes red. Verdict **(c)**.
* **`bridge/mina-zkapp/scripts/emit-provenance.mjs:302-339`** `requireFreshFixture` — recomputes a
  112-module import-cone digest **from the current tree** and hard-refuses on four legs, plus a
  `--stale-self-test` proving the floor bites. **Exemplary**, and currently refusing (the sidecar's
  `git.head` is 700 commits behind). Its only weakness is that it is hand-invoked.
* **`bridge/src/present.rs:3621` / `circuit/src/descriptor_by_name.rs:1004`** — the
  free-substitution-gadget gate builds its specimen from a **parsed JSON wire string** rather than a
  Rust `VmConstraint2` tree, and asserts the detector fires on it **before** reading the verdict.
  A textbook constructive anti-vacuity control.
* **`exec-lean/`, `dregg-lean-ffi/`, `bridge/`** skip guards all route through `demand_lean` (which
  panics by default) — the honest shape, and the one `persist/` is missing (BR-3).
* **`turn/src/executor/execute.rs:1670`** — `TurnError::EffectsHashMismatch`, which `CLAUDE.md:29`
  records as *"constructed zero times"* on 2026-07-27, **is now constructed**. That defect is
  closed; the doctrine text is historical. Re-verified this pass so nobody re-opens it from the doc.

---

# Appendix — the 44 never-constructed variants

Mechanical sweep of 199 kernel enums whose name ends `Error|Reason|Verdict|Outcome|Refusal|
Rejection`: 1382 variants, of which 44 are constructed **nowhere in the repo** (`Self::X`
constructions inside the defining file are counted as constructions; `matches!`/`if let`/match-arm
occurrences are counted as handlers, not constructions). `dead_handlers` = how many places match on
a variant that can never arrive.

Flagged in the ranked findings above: `FastPathError::{NonceMismatch, BudgetExhausted, LockExpired,
HasDependencies}` (BR-6), `VerifyError::{DeserializeFailed, MalformedPublicInputs}` (BR-11),
`BridgeError::{NullifierMismatch, ValueMismatch}` (BR-12), `XmssError::{RootMismatch,
WotsVerifyFailed}` (BR-16).

Not yet triaged, listed so the next pass has them:

```
bridge/src/authorize.rs               AuthError::MissingSymbol
bridge/src/interchain_adapter.rs      AdapterError::Unbindable
bridge/src/mina.rs                    BridgeError::{NotConfirmed, NotInitialized,
                                                    PicklesWrapFailed, WitnessGenerationFailed}
bridge/tools/mina-tip/src/client.rs   ClientError::Binprot
cell-crypto/src/note_bridge.rs        BridgePhaseError::BridgeIdMismatch
cell/src/ledger.rs                    LedgerError::{InvalidFieldIndex, SovereignWitnessRequired}
cell/src/note.rs                      NoteError::ConservationViolation
cell/src/predicate.rs                 WitnessedPredicateError::ProofMissing
circuit/src/dsl/circuit.rs            ProgramError::{MissingWitness, UnknownProgram,
                                                     VerificationFailed}
circuit/src/predicate_program.rs      CompileError::TooManyPredicates
circuit/src/predicate_program.rs      ProveError::{MissingAttribute, MissingTemporalData,
                                                   NotSatisfiable, ProofGenerationFailed}
dregg-lean-ffi/src/marshal.rs         MarshalError::{AuthTagOutOfRange, MissingEnvelopeField,
                                                     NonNatField}
persist/src/lib.rs                    StoreError::{Crypto, NotFound}
turn/src/action.rs                    RefusalReason::NoAuthority           (2 dead handlers)
turn/src/action.rs                    StarkDelegationBindingError::TooFewPublicInputs
turn/src/composer.rs                  ComposeError::MissingAuthorization
turn/src/encrypted.rs                 EncryptedTurnError::NoDecryptionKey
turn/src/error.rs                     TurnError::InvalidFieldIndex
turn/src/eventual.rs                  PipelineError::InvalidOutputRef
turn/src/executor/migration.rs        MigrationCancelReason::TargetRejected
turn/src/umem.rs                      ReifyError::{CapNextSlotUnrecoverable,
                                                   CapTombstonesNotProjected}
```

⚠ A never-constructed variant is **evidence, not a verdict**. Some are honest forward declarations
for a seam not yet built (`BridgeError::PicklesWrapFailed`). The two that matter are the ones whose
*sibling* check exists and whose name promises it: that is how BR-6 and BR-11 were found. The two
highest-value untriaged rows on that basis are `cell/src/note.rs NoteError::ConservationViolation`
and `cell/src/ledger.rs LedgerError::SovereignWitnessRequired` — both name a check the kernel is
supposed to perform.

---

# What was NOT done

* **BR-3 through BR-16 are diagnosed, not fixed.** Only BR-1 and BR-2 landed this pass.
* The `Err` channel of the twelve wrappers still carries **one** string type, so a caller cannot
  *branch* on "archive absent" vs "gate could not read the wire" — it can only read the message.
  Making that a typed `GateFault` enum breaks ~10 `map_err(|why| ..)` sites across four crates;
  correct under greenfield doctrine, deliberately deferred here as a separate change rather than
  smuggled into a decode fix.
* The out-of-scope light-client crates (`eth-lightclient`, `cosmos-lightclient`) have docblocks
  saying *"`Ok(false)` is `"0"` **or** `"ERR"`"* which BR-1 has now made false. Their behaviour is
  correct (they refuse on `Err`); the prose needs a follow-up sweep.
* No Lean was touched, and no AIR or constraint was authored anywhere in this pass.
