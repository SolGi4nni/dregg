# The executed path: symmetry audit

**2026-07-26.** Scope: the hot path only — one real player move from `dregg-turn`'s executor through
`dregg-cell`'s program eval, the world-cell commit, the conservation/range/affine teeth, the receipt,
and the fold. Method: read the code that **executes**, not the code that is **defined**. No build was
run; nothing was proved; every claim below is a reading of the tree at HEAD with `file:line`.

**House law, restated because this document touches circuits.** AIR / constraints / gadgets are
**authored in Lean**; Rust only calls the artifact. An existing Rust AIR is **debt**, never a
foundation. **"Translation validation" between a Rust AIR and a spec is a lie** — TV needs a formal
semantics of the source and there is no semantics of Rust; a Rust case-test proves nothing about all
inputs and must never be called refinement or verification. Where this document says two things
"agree", it means *a human read both and they looked the same*, which is not a theorem.

---

## 0. Shipped claims that are false

Stated in those words, at the top, as asked.

1. **`Effect::linearity()`'s doc claimed a reader that does not exist.** `turn/src/action.rs:1923`
   said *"The conservation checker in the executor uses this to know whether to require a paired
   sibling effect."* There is no such use. `.linearity()`, `LinearityClass`,
   `requires_paired_sibling` and `is_disclosed_non_conservation` have **zero non-test callers in the
   entire tree** (the one hit outside `action.rs` is a doc comment in `sel4/persist-hosttest`). The
   single place where every effect is forced to answer the conservation question is a design
   checklist enforced by rustc, not a tooth. **Fixed** (doc corrected).

   > ⚑ **SUPERSEDED 2026-07-28 — the census stands, the remedy went further.** "Correct the doc"
   > was not enough: the checklist forces an *arm*, never a *correct* arm, and nothing consumes the
   > answer, so a wrong answer is free — and two already were (`Mint`/`Burn` colored `Generative`/
   > `Annihilative` while the deployed `apply_mint`/`apply_burn` are well-paired and conserve
   > exactly). `LinearityClass`, `Effect::linearity()`, both helpers and the 7 tests OF them are
   > **deleted**. The classification's real home is `metatheory/Dregg2/Spec/Conservation.lean`,
   > where it is PROVED — and SPEC-ONLY (no `@[export]`). The line numbers in items 1-2 below no
   > longer resolve. See `HORIZONLOG.md` B2.

2. **`is_disclosed_non_conservation()`'s doc claimed a receipt field that does not exist.**
   `turn/src/action.rs:976` said it is *"the predicate the executor's adversarial path uses to decide
   whether to require a `was_burn`/`was_mint` disclosure flag."* There is no `was_mint` field on
   `TurnReceipt` anywhere in the tree, and `was_burn` is set by a hand-written
   `matches!(Effect::Burn)` forest walk (`turn/src/executor/mod.rs:75-91`) that never consults this
   predicate. **Fixed** (doc corrected).

3. **`state_commit.rs` claimed a state-continuity check that `verify.rs` deliberately refuses to
   make.** The anchor doc asserted that `verify::verify_receipt_chain` checks
   `curr.pre_state_hash == prev.post_state_hash`. It does not, and `turn/src/verify.rs:147-153` says
   so on purpose and gives a sound reason. The two files contradicted each other about whether the
   protocol binds the pre-state a turn claims to have begun from. It does not (§4.2). **Fixed** (doc
   corrected, real consumer named).

4. **`Turn::hash`'s doc and the cipherclerk's doc both listed `conservation_proof` as covered by the
   v3 hash. It is not hashed at all.** `turn/src/turn.rs:394` and `sdk/src/cipherclerk.rs:4843`
   asserted coverage as the closure of the "proof-swap attack"; a read of the whole
   `hash_with_forest` body shows `conservation_proof` is absent. This one turns out to be
   **principled and unavoidable** — the Schnorr excess proof is verified *against* `turn.hash()`
   (`turn/src/executor/finalize.rs:269`), so hashing it in would be circular — but the docs
   asserted the opposite binding direction, which is the difference between "fails closed" and
   "forgeable". **Fixed** (both docs corrected; the residual is DoS-malleability, §5 rank 6).

5. **`absent_cell_commitment`'s "a removal is not a fixed point" is false for a colliding pair.**
   The claim is priced at ~124 bits by the 8-felt widening. But `cells_root` keys cells by a **one-felt
   ~31-bit address** and `compute_canonical_heap_root_8` **silently dedupes by that address**
   (`circuit/src/heap_root.rs:832`). Two cells colliding on the key share one leaf, so removing
   either leaves the signed anchor unchanged. The width fix priced the root; it never priced the key.
   **Fixed** (⚑ added at `turn/src/state_commit.rs`).

   ⚑ **UPDATE 2026-07-28 — the BEHAVIOUR is now fixed too, and the site count above was wrong.**
   There were **four** `dedup_by_key` sites, not one: `heap_root.rs` `CanonicalHeapTree::new`,
   `compute_canonical_heap_root_8`, `CanonicalHeapTree8::new`, and the in-file `dense_build` test
   oracle. All four are now `assert_addr_unique` — two leaves at one address are **REFUSED**, not
   merged. Driven demonstration (pre-fix oracle + post-fix refusal, both poles):
   `circuit/tests/heap_addr_collision_refusal.rs`. Note also that `as_u32()` was never a truncation
   — `BabyBear` is canonical in `[0, p-1]` — so "dedup on the full felt" would have been a no-op;
   the address is narrow because it is ONE felt.

6. **The SDK's operator-facing warning described the pre-fail-closed world.**
   `sdk/src/runtime.rs:452` told operators *"This does not fail closed; it silently decides"* for the
   missing conservation oracle — in a branch reachable only where `turn/src/executor/atomic.rs:497`
   **does** fail closed and the Rust twin is not even compiled. Stale in the safe direction, but it
   is the sentence an operator acts on. **Fixed.**

7. **A stale map-op histogram** in `circuit/src/descriptor_ir2.rs:544` (`write 4` / `read 0`; actual
   `write 6` / `read 2`). The load-bearing part — `insert 0` — was and is correct. **Fixed.**

Not false, but the single most important thing to say out loud: **the verified Lean executor does not
decide anything in production.** See §4.4.

---

## 1. The executed path, with the joints named

A player move (`spween-dregg`'s `WorldCell::apply_choice` → `dregg_app_framework::EmbeddedExecutor`)
lands here. Everything below is `dregg-turn`'s classical forest path — the one a turn with
`execution_proof: None` takes, which is **every turn a builder produces**
(`turn/src/builder.rs:363`).

| # | Joint | Where | What decides |
|---|---|---|---|
| J1 | `TurnExecutor::execute` | `turn/src/executor/execute.rs:227` | sole entry to ledger mutation |
| J2 | shadow capture + optional Lean veto | `execute.rs:247-315`, `turn/src/shadow.rs` | **off by default** (§4.4) |
| J3 | admission prologue (expiry, agent liveness, chain head, budget, freeze) | `execute.rs:~444-574` | Rust |
| J4 | forest walk, per-action authorize | `turn/src/executor/execute_tree.rs`, `authorize.rs` | Rust |
| J5 | `apply_effect` — the 36-arm dispatch | `turn/src/executor/apply.rs:135` | Rust |
| J6 | cell program eval (`StateConstraint`) | `cell/src/program/eval.rs:329` | **Lean oracle** on native release; Rust on wasm/zkVM/debug |
| J7 | `balance_change` → `excess` + `asset_deltas` | `execute_tree.rs:990-1049` | Rust accumulate |
| J8 | note conservation | `execute.rs:1222` → `finalize.rs:159` | Rust |
| J9 | scalar excess `== 0` | `execute.rs:1252` | Rust |
| J10 | per-asset `Σδ = 0` | `execute.rs:1287` → `atomic.rs:431` | **Lean oracle** on native release; **fail-closed** if absent; Rust twin on wasm/zkVM/debug |
| J11 | consensus state anchor (pre + post) | `turn/src/state_commit.rs` | Rust witness-gen |
| J12 | receipt build + executor signature | `turn/src/executor/finalize.rs`, `turn/src/turn.rs:837` | Rust |
| J13 | chain / fold verification | `turn/src/verify.rs:157`, `dreggnet-game-board/src/lib.rs:1159` | Rust |

**Two joints are genuinely Lean-decided (J6, J10)** and both are architecturally excellent: a runtime
trait seam (`cell/src/program/oracle.rs`, `turn/src/executor/conservation_oracle.rs`) so `dregg-turn`
and `dregg-cell` never link the archive, with the native-release no-oracle case **not merely
unreachable but not compiled** (`atomic.rs:497` / `:529`). That is the right shape and it should be
the template for everything else on this list. **Eleven of thirteen joints are trusted Rust.**

---

## 2. Every effect ↔ exactly one tooth

**Verdict: the correspondence is neither total nor injective, and it is not even a relation between
the same two sets.** The headline conservation gate is keyed on an **`Action` field**, not on the
`Effect` vocabulary at all.

### 2.1 The bipartite matching

`Effect` has **36 variants** (`turn/src/action.rs:1067`). The conservation surface is partitioned
into **six disjoint local teeth**, no one of which sees more than three variants:

| Tooth | Where | Effects it inspects |
|---|---|---|
| **T1** per-asset `Σδ = 0` | `atomic.rs:431`, live at `execute.rs:1287` | **NONE** — reads `Action::balance_change` only |
| **T2** scalar `excess == 0` | `execute.rs:1252` | **NONE** — same |
| **T3** mixed-atomic conservation | `atomic.rs:1555` (scan `:1440-1488`) | `Transfer`, `Burn`, `Mint` |
| **T4** note conservation | `finalize.rs:159` / collector `:512` | `NoteSpend`, `NoteCreate`, `BridgeMint` |
| **T5** committed Pedersen conservation | `finalize.rs:217` / collector `:314` | `NoteSpend`, `NoteCreate` |
| **T5b** shielded conservation | `apply.rs:1812` (injected verifier) | `ShieldedTransfer` |
| **R1** Bulletproof output range | `finalize.rs:374` | `NoteCreate` |
| **R2** apply-time range/shape | `apply.rs:2229`, `:2272` | `NoteCreate` |
| **R3** shielded range proofs | `apply.rs:1812` | `ShieldedTransfer` |
| **R4** `u64`/`i64` overflow guards | scattered per arm | `Transfer`, `Burn`, `Mint`, `RotatePqIdentity` |
| **R5** in-AIR 30-bit range lookup | `descriptor_ir2.rs:247` | 30 of 36; **0 lookups** on `AttenuateCapability`, `RevokeCapability`, `GrantCapability`, `Custom`, `setFieldDyn`, `heapWrite` |
| **L1** `linearity()` | `action.rs:1923` | all 36 — **and nothing reads it** |
| **L2** cap non-amplification | `apply.rs:783`, `:800`, `:2697`, `:3996`; `authorize.rs:455`, `:1569`, `:1588` | `GrantCapability`, `AttenuateCapability`, `ExerciseViaCapability` |
| **L3** in-circuit submask non-amp | `cap_delegation_nonamp_descriptor.rs:142` | **NONE — unrouted** |

**Effects with no conservation/range/affine tooth and no AIR row at all:** `SetProgram`, `Promise`,
`Notify`, `React`, `CreateHybridCell`, `RotatePqIdentity`. All six fall into `_ => {}` catch-alls at
`finalize.rs:559`, `finalize.rs:415`, and `effect_vm_bridge.rs:702`. The two PQ verbs are at least
**fail-closed at the projection** (`effect_vm_bridge.rs:774-783` returns
`PqIdentityEffect`), so they cannot be falsely proven — they simply cannot be proven. `SetProgram`,
`Promise`, `Notify` and `React` are silently dropped.

**Teeth with no effect (dead weight):**
- `L1 linearity()` — the *only* place the vocabulary is forced to answer "does this conserve?", read
  by nothing. **Accidental.**
- `L3 dregg-effectvm-attenuateA-v1-genuine-nonamp` — the only *in-circuit* anti-amplification tooth.
  Its own header says *"Nothing routes cap-graph rows to this descriptor"*
  (`cap_delegation_nonamp_descriptor.rs:77`). Non-amplification is therefore enforced **only in Rust**
  (L2). **Toy-era decision now load-bearing.**
- `build_conflict_set` (`turn/src/conflict.rs:146`) — no caller outside its own unit test. See §4.5.
- The three `*Sat*` descriptors, `dregg-pq-identity-rotation::v1`, `heapWrite`,
  `rotationCaveatProbe`, `dregg-effectvm-record-v1` — registry members no effect selector reaches.

### 2.2 Why the missing correspondence has not already killed the ledger

Because each value-moving effect carries a **bespoke local invariant** in its own `apply_*` arm, and
those invariants are individually sound:

- `Transfer` — debits `from`, credits `to`, same amount, **same asset enforced on the full 32 bytes**
  (`apply.rs:692`, comparing `asset()`, not the folded class). Locally conserving.
- `Mint` / `Burn` — well-paired: the issuer well carries `−supply`, so holder↔well moves conserve
  exactly per asset (`apply.rs:3774-3780`). This is why every live call site passes
  `declared_supply = &[]`.
- `CreateCell` — **cannot mint an opening balance** (`apply.rs:1100`, hard `Err`).

`apply.rs:686-689` states the architecture plainly and correctly:

> *"The apply-time Transfer path NEVER feeds the per-asset `asset_deltas` conservation accumulator
> (only an action's `balance_change` does, in `execute_tree`), so the turn-end per-asset `Σδ=0` gate
> cannot see this teleport — the guard MUST live here."*

**Classification: a toy-era decision now load-bearing.** When the vocabulary was `Transfer` plus
`balance_change`, "the global gate sees value moves" was nearly true. At 36 effects it is false, and
global conservation is now an **emergent property of six independent local arguments plus every
pairwise interaction between them** — a proof obligation nobody has written down and no gate
discharges. `linearity()` is the fossil of the design that would have made it total.

---

## 3. Known wounds, carried forward

### 3.1 MapOp arity — **the wound as recorded has the direction inverted, and is now closed**

Both sides are **arity 3** at HEAD.

- Lean: `metatheory/Dregg2/Circuit/IndexedMerkleTree.lean:133` —
  `imtLeafHash hash l := hash [l.addr, l.value, l.nextAddr]`
- Rust: `circuit/src/heap_root.rs:97` — `HEAP_LEAF_ARITY: usize = 3`; preimage `[addr, value,
  next_addr]` at `:279`
- AIR: `circuit/src/descriptor_ir2.rs:2231` — `[MAP_KEY, value_col, MAP_NEXT]`

The Lean docstring at `IndexedMerkleTree.lean:131` records that the **deployed** side was the arity-2
one and was widened to meet Lean (*"the deployed `HeapLeaf::digest8` gains the `nextAddr` felt: arity
2 → 3"*). The `.aafiInsert` live-host claim is confirmed (registry histogram: `aafi_insert` 24,
`absent` 24, `write` 6, `read` 2, **`insert` 0**), which makes the `.insert`-vs-`.aafiInsert` pairing
concern moot — `.insert` is unreachable.

**Hot path: NO for a plain move.** A `SetField`/`Transfer`/`EmitEvent` turn emits zero map ops
(`mapOpsOf_graduateV1 = []`, `EffectVmEmitV2.lean:192`). Map ops are reached by note spend/create,
cell create/spawn, revoke, heap write, and `custom`. **Adversary gains nothing from this wound.**
**The memory note should be corrected.**

### 3.2 The 1-felt MapOp key — **still present, and it is the sharpest thing in this audit**

- `circuit/src/descriptor_ir2.rs:590` — `pub key: LeanExpr`, one expression, beside 8-felt
  `root`/`new_root`. Lean twin `DescriptorIR2.lean:301-313`.
- `circuit/src/heap_root.rs:225` — `heap_addr(coll, key) = hash_many(&[coll, key])` → one `BabyBear`.
- `circuit/src/field.rs:11` — `BABYBEAR_P = 2^31 − 2^27 + 1`. **~30.9 bits.**
- ~~`circuit/src/heap_root.rs:832` — colliding addresses are **silently deduped**, no error.~~
  **CLOSED 2026-07-28.** It was FOUR sites, not one; all four now call
  `heap_root::assert_addr_unique` and **REFUSE**. The KEY WIDTH is unchanged and still narrow —
  this closes the silent merge, not the ~31-bit address.
- `turn/src/executor/apply.rs:36-40` — `shielded_nullifier_key` produces a 32-byte `Nullifier`
  carrying **4 bytes of entropy**. The wide type buys nothing.

Birthday ≈ 2^15.5 (~46k). Targeted second preimage ≈ 2^31 — seconds to minutes on one core.

**Hot path: YES, in two distinct places.**
1. **`cells_root`** (`turn/src/rotation_witness.rs:308-318`) keys **every cell in the ledger** by
   `hash_bytes(id)` and is a component of **every receipt's `pre_state_hash`/`post_state_hash`** — the
   value the executor signs and the federation QC aggregates. This runs on *every turn*, including a
   plain `SetField`. The function's own ⚑ already names the wound honestly; §0.5 records the
   consequence the ⚑ did not draw.
2. **The nullifier set**, on any note-spending turn (`EffectVmEmitRotationV3.lean:2380`, `:2391`:
   `key := .var NULLIFIER_PARAM_COL`).

**Correction to the memory index:** `Dregg2/Bignum.lean` is **not** the map-key fix — it is the
multi-limb arithmetic library, and nothing on the map-op path imports it. The map-key fix is
`metatheory/Dregg2/Circuit/MapOpWideKey.lean` (8-felt key, `MAP_LEAF_ARITY_WIDE = 17` at `:254`), and
its **deployed adoption is zero**: `MapOpW`, `wideEnc`, `Digest8Key`, `wide_key` have no hits in
`circuit/src`. The "~3% adoption" figure belongs to `Bignum`, which is a different fix for a
different wound. The refutations for the narrow case are already proved
(`MapOpWideKey.lean:347-356`: `narrowLeaf_conflates`,
`halfWideLeaf_forges_absence_of_present`) — this is a *known-proven* attack, not a hypothesis.

### 3.3 Custom-effect carve-out — **substantially narrowed; the gate flip is still not done**

There is no boolean and no feature flag. The gate is a **trait-method default**:
`cell/src/custom_effect.rs:225-231`, `fn app_write_binding(&self) -> Option<AppRootBinding> { None }`.
A verifier that has not opted in makes `enforce_custom_app_write_bindings`
(`turn/src/executor/proof_verify.rs:315`) skip **all** of its checks at `:358-360`.

What the carve-out does **not** bypass, which is the good news:
`Effect::Custom` on the classical path is a **hard refusal** (`apply.rs:506-509`,
`CustomEffectRequiresProofCarryingTurn`); registry dispatch refuses unregistered programs; the
state-binding weld pins the sub-proof's PI prefix to `[old_commit8, new_commit8]`
(`proof_verify.rs:476`); and `proof_verify.rs:1136` states the Effect VM still enforces
balance/nonce/fields/cap_root continuity.

**Hot path: NO.** Reachable only via `turn.execution_proof.is_some()`, and there is **no non-test
caller anywhere that sets it**. **Adversary gain if it were reachable:** app-semantic divergence —
the playable path and the proven path disagree about app state under a valid-looking receipt. Not
value inflation. Note the intersection with §3.2: `customVmDescriptor2R24` carries `aafi_insert` map
ops, so a custom turn rides the 31-bit key as well, and it is admitted with **no umem weld**
(`proof_verify.rs:1145-1150`, `LIVE_ONLY_BARE_KEYS`).

---

## 4. The six symmetries, classified

### 4.1 Every effect ↔ exactly one tooth — **toy-era, load-bearing.** §2.

### 4.2 Pre-state ↔ post-state — **principled at the executor, absent at the verifier**

The **executor** computes `pre_state_hash` itself from the live ledger; it never takes the turn's
word, so a live node cannot be lied to about where a turn began. **Principled.**

The **verifier** is another matter. `verify_receipt_chain` (`turn/src/verify.rs:157-208`) checks
genesis, agent consistency and `previous_receipt_hash` linkage — and **deliberately does not** check
`curr.pre_state_hash == prev.post_state_hash` (`:147-153`), for the sound reason that these snapshots
absorb executor-*global* roots that another agent legitimately moves between two of this agent's
receipts. So the causal link is per-agent hash-chaining; the state snapshots are authenticated
(executor signature) but not *linked*. `VerifyError::StateChainBreak` exists and is raised by exactly
one consumer, the federation exit path (`federation/src/types.rs:522`). **Principled, but the
principle is load-bearing and was documented contradictorily** (§0.3).

Inside the constraint vocabulary the pre/post split is clean and deliberate: `Monotonic`,
`Immutable`, `WriteOnce`, `DeltaBounded`, `BalanceDelta*` and the affine-delta arms take `old_state`
and fail closed without it (`TransitionCheckRequiresOldState`, `eval.rs:1993`, `:2011`, `:2031`);
`FieldEquals`/`FieldGte`/`FieldLte` read only `new_state` because that is what they mean.
**Principled.**

### 4.3 Prove ↔ verify — **opt-in, and nobody opts in**

`Turn::effect_binding_proofs` (`turn/src/turn.rs:369`) is the field that makes an effect's typed
parameters PI-bound. Its own doc: *"Empty by default — turns without binding proofs continue to apply
with **executor-trusted enforcement** (backwards compat). Turns with binding proofs get
strong-soundness enforcement."* Every one of the ~20 production construction sites passes
`Vec::new()`. The same is true of `cross_effect_dependencies` and `effect_witness_index_map`.

So the answer to "does the verifier check everything the prover committed to" is: **on the live path
there is no prover and no verifier — there is an executor everyone trusts.** The proof-carrying path
exists, is well built, and is not taken.

Two genuine free fields worth naming:
- **`iroot` is pinned to zero** on the consensus anchor (`state_commit.rs`, `consensus_ctx`). It is a
  1-felt left-leaning fold that contributes nothing today and becomes a ~31-bit waist the moment a
  live receipt-MMR root is threaded. The module's own residual #3b says so. **Principled today,
  a standing falsifier.**
- **`PI[ASSET_CLASS]` zero sentinel** (`atomic.rs:391`): when the prover has not surfaced the class,
  the executor falls back to its trusted ledger class. Sound for the executor, but it means the
  **pure light-client partition is trivial for multi-asset turns**. Named in-code as the remainder.

### 4.4 Host ↔ guest — **the largest asymmetry in the tree, and it has an exploit**

**First, the structural fact.** The verified Lean executor is a `ShadowObserver`
(`turn/src/shadow.rs:136`) gated on `DREGG_LEAN_SHADOW=1`, with the veto additionally gated on
`DREGG_LEAN_SHADOW_STRICT=1` (`exec-lean/src/lean_shadow.rs:341`). **Neither variable is set anywhere
in the tree outside tests.** The default is `NoOpShadowObserver`, which "compares nothing, captures
nothing, and never vetoes". The veto is one-directional (`lean=false ∧ rust=true`) and a `None`
verdict never vetoes. `lean_shadow.rs:339` states the intent honestly: *"OFF by default: the live path
stays Rust-decided until the marshaller covers every effect."*

This is a correct and conservative decision. It is also the answer to "is the executed thing the
specified thing": **for turn execution as a whole, no — they are a hopeful pair.** Only J6 and J10
are the same object.

**Second, the exploitable divergence.** The per-asset conservation twin truncates.
`turn/src/executor/atomic.rs:538-548`:

```rust
net_delta_mag: BabyBear::new_canonical(delta.unsigned_abs() as u32),
```

with `new_canonical(v) = v % BABYBEAR_P` (`circuit/src/field.rs:125-127`). The Lean branch receives
the raw `i64` (`dregg-lean-ffi/src/lib.rs:325-330`). Balances are `i64`
(`cell/src/state.rs:204`) and the deltas are raw `balance_change` values, so:

> the fallback decides `Σ ±((|δ| mod 2^32) mod 2013265921) == 0`; Lean decides `Σ ±δ == 0` over `Int`.

A cross-asset teleport of magnitude exactly `p = 2_013_265_921` (or any multiple of `p` or of `2^32`)
passes the scalar `excess` gate at `execute.rs:1252` (`−p + p = 0` in `i64`) and then reduces to
`0` on **both** legs of the per-asset gate, so every asset "conserves". Lean rejects it.

**Where this bites:** wasm32, the SP1 zkVM guest, and **any debug-profile node**. A deployed native
release node is safe — the twin is not compiled there. But the wasm build *is* the browser light
client, and the zkVM guest's accept is what gets **proven**. See §5 rank 2.

**Third, three more guest-only divergences** (all: guest admits, host refuses):
- `affine_sum` (`cell/src/program/eval.rs:2898`) accumulates `sum += k * x` in `i128` **unchecked**;
  the host marshaller declines out-of-envelope inputs and `eval.rs` then fails closed, but the guest
  wraps and a wrapped negative sum **admits an `AffineLe` that Lean refuses**. Exploit input is
  already pinned in the tree's own test: `AffineLe { terms: [(i64::MAX,0),(i64::MAX,1)], c: 0 }`.
  Third behaviour: a **debug** build *panics* on the same expression. One turn, three outcomes.
- `AnyOf`/`AllOf` with a class-c or `HeapField` branch, or over `MAX_LIST` / `MAX_COLL_CELLS`: the
  marshaller declines (`exec-lean/src/constraint_oracle.rs:514`, `:599`), the host fails closed, the
  guest evaluates and can **accept** (`eval.rs:1482-1499`).
- The SP1 guest (`circuit/sp1-guest/src/main.rs:366-381`) links the hand-written evaluator with
  `ctx = None` and commits its verdict as `program_valid`, and has two silent-accept catch-alls
  (`:359`, `:380`) that commit `true` on absent input.

**Classification: accidental for the truncation (a `u32` coercion nobody re-read); principled for the
guest keeping a labelled Rust evaluator (it genuinely cannot link the archive); toy-era for the
shadow being an env-var opt-in.**

**One real freeze-set gap found and fixed.** `collect_referenced_cells`
(`turn/src/executor/execute.rs:67`) claims to mirror `lean_shadow::collect_tree_ids`. It did not:
`effect_cells` (`exec-lean/src/lean_shadow.rs:1091`, `:1094`) registers `Mint { target }` and
`AttenuateCapability { cell }`; `collect_referenced_cells` dropped both into `_ => {}`. That is
exactly the **unsafe under-report** `ShadowHostCtx`'s host-obligation section names
(`turn/src/shadow.rs:38-45`): a `Mint` into a migration-frozen recipient reached the verified gate
with that cell absent from `frozen`, so the gate's frozen leg would **admit a turn the true-facts
gate rejects**. Latent only because the shadow is off. **Fixed** — the two arms are added; the change
can only enlarge the freeze set, so it strictly tightens. `SetProgram`, `RotatePqIdentity`, `Notify`,
`Promise` and `ExerciseViaCapability`'s **inner effects** are still dropped by both walkers; they are
unprojectable today (so the gate returns `None` and never vetoes), but they belong in the re-emit
list.

### 4.5 Read ↔ write — **reads are not constrained anywhere**

There is **no fog machinery on the executed path**. `Fog` does not appear in `turn/src`, `cell/src`
or `circuit/src` at all. What exists:

- `conflict::extract_access_sets` (`turn/src/conflict.rs:164`) computes `(read_set, write_set)`. All
  four production call sites bind the read set to `_read_set` and discard it:
  `execute.rs:534`, `fast_path.rs:269`, `:359`, `:475`, `execution_path.rs:66`.
- `build_conflict_set` (`conflict.rs:146`) — the function that would *use* both — has **no caller
  outside its own unit test**.
- `program::ReadSet` (`cell/src/program/types.rs:391`), the declared read-set for a `Custom`
  predicate, is `ReadSet::default()` at every construction site outside tests. Its own doc: *"Lets
  audit tools and (eventually) AIR enforcement reason about a custom predicate's structural
  footprint."* "Eventually" is the tell.

**A fog claim — "what this turn could see" — has no representation in the executed path.** The
vocabulary to name a read set was built twice and wired zero times. **Classification: accidental**
(nobody removed it, nobody finished it), and it is the cleanest greenfield on this list because
nothing depends on the current behaviour.

### 4.6 Single ↔ many — **the singletons that are now wrong**

| Singleton | Where | Verdict |
|---|---|---|
| **One universe + one `ProofAnchor` per `Game`** | `dreggnet-game-board/src/lib.rs:1195`, `:1233` | Confirms the sibling lane. `universes: BTreeMap<Game, UniverseId>`; `ensure_open` is idempotent and **ignores** every later anchor; the anchor pins `(VK, genesis_root, final_root)` and `match_anchor` (`:1159`) requires a submission to attest **those** roots. **The board structurally cannot rank two matches from different genesis states.** Pinning-once is the correct fix to the *capture* bug it was written for; "one match per game, forever" is the toy-era assumption still inside it. |
| **One asset per newborn cell — inherited, never chosen** | `apply.rs:1083-1088` `birth_asset` | **Principled and load-bearing far beyond its file.** A newborn inherits `parent.asset()`; only an absent action target falls back to `CellId::from_bytes(token_id)`. This is the *only* reason the ~31-bit `fold_token_id_to_asset` partition key (§5 rank 1) is not already an inflation bug. The invariant "a turn cannot introduce an asset class" is nowhere asserted and lives nowhere near the fold it protects. |
| **One `proof_verifier` per executor** | `turn/src/executor/mod.rs:825` | `Option<Box<dyn ProofVerifier>>` — one VK/proving system for the whole node. Fine at one ruleset, wrong the moment two coexist or a VK epoch rotates. |
| **One `local_federation_id`** | `mod.rs:854` | Baked into the signing message; cross-federation is a *rejection*, not a routing decision. |
| **One conservation oracle, one constraint oracle, process-wide** | `OnceLock` at `conservation_oracle.rs:57`, `oracle.rs:61` | Correct for one ruleset; unversioned. A ruleset epoch has nowhere to live. |
| **One `iroot`, pinned zero** | `state_commit.rs` `consensus_ctx` | §4.3. |

---

## 5. Ranked by what an adversary gains

**This list is separate from §6 ("ugly") on purpose.**

**1. `fold_token_id_to_asset` is a ~31-bit partition key on the conservation gate.**
`circuit/src/block_conservation.rs:88-92` takes **four bytes** of a BLAKE3 derived key and reduces
mod `p`. Its own doc says *"collision-resistant-to-the-field-modulus"* and *"the distinct-token-ids-
stay-distinct property is what the partition needs"* — the second is false at ~2^15.5 tokens, and a
targeted second preimage is ~2^31. If two assets share a folded class, a single turn with
`balance_change = +N` on a real-asset cell and `−N` on a worthless one passes `excess == 0` **and**
the per-asset gate, minting `N` from nothing. Routing through the verified Lean oracle does **not**
help: `conserves(rows: &[(u32, i64)])` receives the **already-folded** key, and the theorem
(`decision_conserves_iff_air_boundary`) is about `creditSum = debitSum` *given the partition*. The
partition itself is unproven and 31 bits wide.
**Not reachable today** — `birth_asset` prevents a turn from choosing an asset (§4.6), so the attacker
would need to already control two distinct asset classes. **This is one product decision away from
live inflation**, and that product (token issuance / launchpad / house-via-factory) is on the roadmap.
*Blast radius: unbounded inflation of any asset. Precondition: an asset-creation path with a
free 32-byte id.*

**2. The conservation twin truncates `i64 → u32 → mod p` on wasm / zkVM / debug.**
`atomic.rs:538-548` + `field.rs:125`. A cross-asset delta of magnitude `k·p` or `k·2^32` reads as
**zero imbalance** to the twin and as a violation to Lean. A deployed native release node is safe
(the twin is not compiled). **The browser light client and the zkVM guest are not.** The guest's
ACCEPT is committed as `program_valid` — i.e. this is a *proof* of the unverified evaluator's
acceptance. *Blast radius: consensus split between the native node and every light client; a
"verified" proof of an accepting run that the node would reject. Precondition: a second asset with
≥ `p` units.*

**3. The 1-felt heap key + silent dedup makes a cell removal invisible to the signed anchor.**
`rotation_witness.rs:311` + `heap_root.rs:832`. Grind a `(public_key, token_id)` whose `CellId`
collides with a victim's under `hash_bytes` (~2^31, minutes). Both cells then share one leaf in
`cells_root`. Destroying the victim leaves `pre_state_hash`/`post_state_hash` **unchanged** — the
executor signs and the federation QC certifies an anchor that does not distinguish the two ledgers.
On the nullifier set the same collision is a **double spend** (or a griefing pre-insert that
permanently blocks an honest note). The refutations are already proved in Lean
(`narrowLeaf_conflates`). *Blast radius: state-anchor forgery / double spend. Precondition: ~2^31
offline hashing.*

⚑ **CLOSED 2026-07-28 — the MERGE, not the WIDTH.** All four `dedup_by_key` sites in
`heap_root.rs` are now `assert_addr_unique`: two leaves at one address are REFUSED. The driven
demonstration is `circuit/tests/heap_addr_collision_refusal.rs` (pre-fix oracle: the anchor does
not move when the merged-away entry is removed; post-fix: all four builders refuse). Three
consequences worth carrying forward:

- The **address is still one ~31-bit felt**. Nothing here widens a key. What changes is that an
  ambiguous commitment is now a loud refusal instead of a silent wrong answer.
- The refusal **converts a silent soundness bug into a liveness one** on the surfaces where the
  colliding value is attacker-chosen (`cells_root` via `CellId::derive_raw`, and the four
  accumulators via `fold_bytes32_to_bb`). A ground collision now panics the commitment path. That
  is the right trade — a refusal beats a wrong anchor — but it is a real availability change and
  the durable fix remains the wider MapOp key epoch.
- It immediately caught a **live sentinel eviction**: `fold_bytes32_to_bb([0u8; 32]) == 0 ==
  SENTINEL_MIN`, so a nullifier folding to zero put a real leaf at the genesis sentinel's address
  and the dedup dropped **the sentinel** — the low bracket every non-membership opening rests on.
  Fixture pinned at `cell/src/nullifier_set.rs`.

**4. `affine_sum`'s unchecked `i128` admits on the guest what Lean refuses.**
`cell/src/program/eval.rs:2898`. A wrapped negative sum admits an `AffineLe`. Host fails closed,
release-guest wraps and admits, debug-guest panics. *Blast radius: a programmed cell's slot caveat
bypassed in the browser light client and inside the zkVM statement.*

**5. `AnyOf`/`AllOf` host/guest split.** Marshaller declines → host refuses → guest evaluates and
accepts (`constraint_oracle.rs:514`, `:599` vs `eval.rs:1482`). Same shape as 4, narrower.

**6. `conservation_proof` is signature-malleable.** Not in `Turn::hash` (necessarily — §0.4), so an
in-flight tamper keeps the signature valid and converts the turn into a rejection. **DoS/griefing,
not forgery.**

**7. Freeze-set under-report via `Mint` / `AttenuateCapability`.** **Fixed in this pass.** Latent
(shadow off) but it was the named unsafe direction, and it would have opened the day strict mode
shipped.

---

## 6. Ugly but not exploitable

- `linearity()` and its two helpers: the vocabulary's conservation checklist, read by nothing, with
  `Mint`/`Burn` still classified ex-nihilo (`Generative`/`Annihilative`) a full design generation
  after `apply_mint`/`apply_burn` became well-paired and exactly conserving.
- `build_conflict_set`, `ReadSet`, `_read_set` × 4 — a read-set vocabulary built twice, wired zero
  times.
- `L3` in-circuit non-amplification descriptor, authored and unrouted; the three `*Sat*` descriptors
  with no wide twin; `dregg-pq-identity-rotation::v1` Lean-proven with no registry, producer or VK.
- `SetProgram`, `Promise`, `Notify`, `React` — silently dropped by the VM projection's `_ => {}`
  (`effect_vm_bridge.rs:702`) rather than refused the way the two PQ verbs are.
- `R5`: `GrantCapability`, `RevokeCapability`, `AttenuateCapability`, `Custom`, `setFieldDyn`,
  `heapWrite` declare a `TID_RANGE` table and take **zero lookups** from it.

---

## 7. The plan

### Rename (a doc or a name is wrong; no behaviour moves) — **done in this pass**
1. `action.rs:1923`, `:976` — `linearity()` / `is_disclosed_non_conservation` claimed readers and a
   `was_mint` field that do not exist. ✅
2. `state_commit.rs` — named the wrong continuity consumer; now names `federation/src/types.rs:522`
   and records that the ordinary path checks nothing. ✅
3. `turn.rs:394` + `cipherclerk.rs:4843` — `conservation_proof` removed from the "covered" list, with
   the circularity argument and the DoS residual stated. ✅
4. `state_commit.rs` — ⚑ that "a removal is not a fixed point" is false for a colliding pair. ✅
5. `sdk/src/runtime.rs:452` — operator warning corrected to the fail-closed reality. ✅
6. `cell/src/program/oracle.rs` — stale "two copies exist" inventory. ✅
7. `descriptor_ir2.rs:544` — map-op histogram recount. ✅
8. `execute.rs` `collect_referenced_cells` — `Mint` + `AttenuateCapability` added so the walker
   actually mirrors `collect_tree_ids`; strictly tightening. ✅
9. **Memory index corrections owed:** the MapOp-arity wound has its direction inverted and is closed
   (§3.1); `Dregg2/Bignum.lean` is *not* the map-key fix — `MapOpWideKey.lean` is, at **0%** deployed
   adoption (§3.2).

### Re-emit (the object is right, the encoding is too narrow — Lean-side, then regenerate)
1. **Widen the asset-class partition key.** `fold_token_id_to_asset` → 8 felts, or drop the fold and
   partition on the full 32-byte `AssetId`. This is rank 1 and it is the cheapest of the three width
   fixes because the partition key never enters a Merkle path — it is a grouping key. **Do this
   first, and do it before any token-issuance product ships.**
2. **Adopt `MapOpWideKey.lean`.** The 8-felt `MapOpW` / arity-17 leaf is authored and proved beside
   the node with zero deployed adoption. This is the `MapOp` key epoch that `cells_root`'s own ⚑ and
   `MapOpWideKeyGate.lean` both point at. Ranks 3 and (partly) 2.
3. Widen `shielded_nullifier_key`'s 4-byte entropy to the full digest (`apply.rs:36`) — a 32-byte type
   carrying 4 bytes is a lie the type system is telling.
4. Route the `L3` non-amplification descriptor, or delete it and say plainly that non-amplification is
   Rust-enforced.
5. Complete the freeze-set / marshaller walkers together for `SetProgram`, `RotatePqIdentity`,
   `Notify`, `Promise`, and `ExerciseViaCapability`'s inner effects.

### Rewrite (the design was right for a toy and is wrong now)
1. **Make the conservation tooth total.** Today six disjoint local invariants plus an unwritten
   pairwise-interaction proof stand in for one gate. The shape that fixes it already exists in the
   vocabulary — `linearity()` is the fossil. The move: every value-moving effect declares its
   `(asset, signed_delta)` rows, `apply_*` **cannot** move a balance except by emitting a row, and
   T1 consumes the union. Then `Transfer`'s same-asset guard, the well-pairing argument and the
   `CreateCell` zero-balance rule become *consequences* rather than the load-bearing checks. This is
   the single highest-value structural change on the list.
2. **Kill the `i64 → u32` coercion in the twin** (`atomic.rs:538`). Better: delete
   `unverified_rust_conservation_fallback` entirely and make the guest fail closed too. The reason it
   exists — "wasm and the zkVM cannot link the archive" — is a statement about *linking*, not about
   *deciding*: the guest could carry the Lean-emitted decision procedure rather than a hand-written
   twin. Until then it is a Rust conservation decider on the inflation boundary, which is the exact
   thing House Law #1 retired on the host.
3. **Decide what to do about reads.** Either wire `extract_access_sets`' read set into a declared,
   checked read-set (and give a fog claim somewhere to live), or delete `build_conflict_set` and
   `ReadSet` and stop implying reads are constrained. The current state — vocabulary present,
   enforcement absent — is the worst of the three.
4. **Un-singleton the board.** `BTreeMap<Game, UniverseId>` with one immutable `ProofAnchor` cannot
   rank a second distinct match. The anchor should key on `(Game, genesis_root)` or the ranking
   should carry the anchor rather than the board.
5. **Flip the shadow, or stop calling it the authority.** `DREGG_LEAN_SHADOW` is set nowhere. The
   marshaller-coverage precondition is legible and honest; what is missing is a *plan with a date*
   and a list of the effects that still GAP. Until then, every description of turn execution should
   say "Rust-decided, with two Lean-decided joints (J6, J10)".

---

## 8. The one-line answer

**The hot path is coherent, and here are the three joints that are not:** the conservation tooth is
keyed on an `Action` field rather than the `Effect` vocabulary, so global conservation is an
emergent property of six local arguments (§2); the partition key that tooth groups by is ~31 bits
wide and is guarded only by an unstated invariant in a different file (§5.1, §4.6); and the verified
Lean executor — the thing the specification is about — is an env-var opt-in that nothing in the tree
turns on, so eleven of thirteen joints are trusted Rust (§4.4).
