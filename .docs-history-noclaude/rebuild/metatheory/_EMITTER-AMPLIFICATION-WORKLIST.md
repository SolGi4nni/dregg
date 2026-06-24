# EffectVM Verified-Emitter Amplification Work-List

Scope: amplify the verified-by-construction circuit emitter from the **transfer**
beachhead to all ~54 EffectVM selectors. Read-only scoping; every claim is cited
`file:line`. Paths are absolute.

Key files:
- Emitter IR: `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean`
- Transfer beachhead: `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/Emit/EffectVmEmitTransfer.lean`
- Running prover AIR (the target to reproduce): `/Users/ember/dev/breadstuffs/circuit/src/effect_vm_p3_full_air.rs`
- Descriptor interpreter (consumes the emitted IR): `/Users/ember/dev/breadstuffs/circuit/src/lean_descriptor_air.rs`
- Abstract circuit⟺intent triangle (a SEPARATE proof layer): `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Spec/CircuitSpecTriangle.lean`
- Effect enumeration: `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/TurnExecutorFull.lean` (`inductive FullActionA`)
- Selector indices: `/Users/ember/dev/breadstuffs/circuit/src/effect_vm/columns.rs` (`mod sel`)

---

## 1. The reusable emission pattern (the transfer skeleton)

The transfer beachhead is a 5-part skeleton. Every line below is what a new effect
must clone.

### 1a. The IR (shared, already complete — do NOT re-derive)
`EffectVmEmit.lean` supplies the whole emission IR and its denotation:
- `VmGate` / `VmGate.holds` (`EffectVmEmit.lean:132-138`): a per-row gate is an
  `EmittedExpr` body asserted to vanish on `env.loc` — term-for-term a Rust
  `tb.assert_zero(body)`.
- `VmConstraint` (`EffectVmEmit.lean:157-166`): the FOUR forms — `gate body`,
  `transition hi lo`, `boundary row body`, `piBinding row col piIndex`.
- `VmRowEnv` (`EffectVmEmit.lean:118-122`): the `loc`/`nxt`/`pub` triple (the Rust
  `eval`'s `local`/`next`/`public_values`).
- `VmConstraint.holdsVm` (`EffectVmEmit.lean:274-280`): the denotation. NOTE the
  boundary/PI clauses are guarded by `isFirst`/`isLast` (matching `when_first_row`
  / `when_last_row`); the `gate`/`transition` clauses are flag-INDEPENDENT.
- `VmHashSite` / `HashInput` (`EffectVmEmit.lean:181-192`): a Poseidon2 site with an
  ordered input list (`col`/`digest k`/`zero`), `digestCol`, `arity`. The site list
  ORDER is load-bearing: `siteDigestsAcc` (`EffectVmEmit.lean:217-222`) walks the
  list head-first so site `i` reads digests `0..i-1` — the Lean mirror of the Rust
  `digests.push(...)` loop (`effect_vm_p3_full_air.rs:461-469`). The carrier `hash :
  List ℤ → ℤ` is ABSTRACT (`EffectVmEmit.lean:231`) — never an in-Lean algebraic hash.
- `EffectVmDescriptor` (`EffectVmEmit.lean:252-258`) + `satisfiedVm`
  (`EffectVmEmit.lean:284-286`): the bundle and its full denotation
  (`∀ c ∈ constraints, holdsVm ∧ siteHoldsAll`).
- `emitVmJson` (`EffectVmEmit.lean:350-355`): the canonical wire string the Rust
  `parse_vm_descriptor` ingests.

### 1b. The per-effect skeleton (what each new effect clones)
From `EffectVmEmitTransfer.lean`, in order:

1. **Column-reader builders** `eSB`/`eSA`/`ePrm`/`eSelTransfer`/`eSelNoop`/`eSub`
   (`EffectVmEmitTransfer.lean:53-64`). Reusable as-is (rename `eSelTransfer` to the
   effect's selector). These build the `.var (sbCol off)` / `.var (saCol off)` /
   `.var (prmCol i)` ASTs = the prover's `sb`/`sa`/`prm` accessors.

2. **Gate bodies**, term-for-term the running prover's selector-specialized
   polynomials, e.g. `gBalLo` (`EffectVmEmitTransfer.lean:75-78`) ⟺
   `effect_vm_p3_full_air.rs:548-552`; `gNonce` (`:89-90`) ⟺ the global nonce gate
   `effect_vm_p3_full_air.rs:1326`; `gFieldPass i` (`:99-100`) ⟺ the `fld_a(i) -
   fld_b(i)` frame-freeze. NOTE these are emitted ALREADY SPECIALIZED to the hot row
   (i.e. the prover's `s_X * body` with `s_X = 1` factored out — see the comment at
   `EffectVmEmitTransfer.lean:66-72`).

3. **Transition + boundary** lists: `transitionAll` (`:112-113`) = whole-state
   continuity; `boundaryFirstPins`/`boundaryLastPins` (`:116-126`) = the PI pins.
   These are EFFECT-INDEPENDENT (every effect shares the state-block continuity and
   the same boundary identity pins) — reuse verbatim.

4. **Hash sites** `site0..site3` (`:134-160`) + `transferHashSites`
   (`:163`): the GROUP-4 state-commitment chain. Also EFFECT-INDEPENDENT for the
   commit chain — the per-effect ADDITIONAL sites (cap-root/queue-root) are the
   work for set-membership effects (§2).

5. **The descriptor** `transferVmDescriptor` (`:178-184`): `rowGates ++ transitionAll
   ++ boundaryFirstPins ++ boundaryLastPins`, plus `hashSites`, plus `ranges`
   (the two 30-bit balance-limb checks `:184`).

6. **The independent ROW INTENT** `TransferRowIntent` (`:196-211`): the field-level
   move written from protocol intent (NOT from the gate bodies) — direction-bit,
   signed-amount balance move, hi/frame/nonce pins. This is the faithfulness TARGET.

7. **The row hypothesis** `IsTransferRow` (`:220-221`): `loc sel.TRANSFER = 1 ∧ loc
   sel.NOOP = 0` (the selector-validity + sum-to-one of GROUP 1 forces exactly one
   hot selector; the per-effect proof relies on this factoring).

8. **The biconditional** `transferRowGates_holds_iff` / `transferVm_faithful`
   (`:231-304`): on a hot row, `(∀ c ∈ rowGates, c.holdsVm env false false) ↔
   RowIntent env`. Proof shape: forward = extract each gate from membership, unfold
   `holdsVm`, `rw [hsN]` (kill `s_noop`), close each with `linarith`/`nlinarith`/
   `mul_eq_zero`; backward = `rintro` the intent conjuncts, dispatch by gate via
   `rcases hc`, `rw` + `ring`.

9. **Anti-ghost teeth** `*_rejects_wrong_output` / `*_rejects_wrong_balance` /
   `*_rejects_wrong_nonce` (`:314-340`): contrapositives; one per pinned field.

10. **Boundary/hash faithfulness** `boundaryFirst_pins` / `boundaryLast_pins` /
    `transferHash_binds` (`:351-410`) + the assembled
    `transferVmDescriptor_pins_intent` (`:424-462`). Mostly reusable (the commit
    chain is shared).

11. **Non-vacuity witnesses** `goodRow` / `goodRow_realizes_intent` / `badRow` /
    `badRow_rejected` (`:474-542`): a concrete satisfying row AND a concrete
    rejected row. REQUIRED per effect (memory steer: a spec must witness TRUE and
    FALSE). NOTE `goodRow_realizes_intent`'s field-passthrough proof is a manual
    column-disjointness grind (`:512-526`) — this is the most tedious clone cost.

12. **Hygiene** `#guard` shape pins + `#assert_axioms` for every theorem
    (`:546-561`).

The pattern is genuinely reusable: steps 3/4/5(transition+boundary)/10 are
effect-independent; the real per-effect work is steps 2/6/8/9/11 + any extra hash
sites.

---

## 2. The 54 effects, grouped by GATE SHAPE

Grouping is by the STRUCTURE of the running AIR's per-selector gate block in
`effect_vm_p3_full_air.rs`. Selector indices from `columns.rs mod sel`. Effort:
**trivial** = clone-transfer (pure arithmetic over balance/frame, no hash, no aux);
**medium** = adds bit-decomposition / Lagrange / aux-inverse but no new hash root;
**hard** = adds a Poseidon2 set-membership/merkle site or atomic multi-root binding.

### GROUP A — pure balance-delta + frame-freeze (clone transfer EXACTLY). TRIVIAL.
Representative: **transfer** (DONE). Row predicate: `new_bal_lo = old_bal_lo ±
amount`, hi unchanged, cap/reserved/8-fields frozen, nonce tick. These differ from
transfer only by the sign/param of the balance gate; everything else is identical.

| Effect | sel | balance gate (AIR line) | RowIntent delta |
|---|---|---|---|
| mintA | 5 (NOTE_CREATE arm credits) / dedicated | n/a* | credit `+value` |
| burnA | BURN=46 | `:1215-1216` `+ burn_amount` (debit) + `burn_flag=1` | debit `-amount` |
| bridgeMintA | BRIDGE_MINT=40 | `:763` `- bm_val_lo` | credit `+value` |
| noteSpendA | NOTE_SPEND=4 | `:726-728` `- note_val_lo` | credit `+value` (+ nullifier PI, see Group F) |
| noteCreateA | NOTE_CREATE=5 | `:751-753` `+ nc_val_lo` | debit `-value` (+ commitment PI, Group F) |
| createEscrowA / bridgeLockA | 37 / 38 | `:776-778` `+ amount_lo` | debit `-amount` |
| createObligationA | CREATE_OBLIGATION=6 | `:788-789` `+ stake_lo` | debit `-stake` (+ hash sites 6,7 → Group E) |
| fulfillObligationA | FULFILL_OBLIGATION=7 | `:804-805` `- return_lo` | credit `+return` |
| allocateQueue | ALLOCATE_QUEUE=18 | `:1046-1048` `+ capacity*cost` | debit cost (+ hash site 21 → Group E) |

`*` mintA: the AIR has no distinct MINT selector; mint is realized through the
credit arm. Confirm the executor's selector mapping before cloning (the abstract
spec `mint_circuit_pins_intent` exists at `CircuitSpecTriangle.lean:169`, but the
ROW-LEVEL emitter must target whichever selector the trace generator sets).

Effort: each is a ~30-minute clone of `transferRowGates` with one balance gate
swapped. The bridges for the abstract layer already exist
(`intentCredit_eq_balCredit` / `intentDebit_eq_credit`, used at
`CircuitSpecTriangle.lean:180,447,473`), but those bridge the ABSTRACT layer, not
the row layer (§5).

### GROUP B — pure frame passthrough (no balance change, no hash). TRIVIAL.
These the AIR enforces via the `passthrough_bal_cap_fields!` macro
(`effect_vm_p3_full_air.rs:675-711`) or an inline copy: balance/cap/8-fields all
frozen, only nonce ticks. RowIntent = "everything frozen except nonce." This is
`TransferRowIntent` with the balance-delta clause replaced by `bal_lo` frozen — the
simplest possible clone.

| Effect | sel |
|---|---|
| emitEventA | EMIT_EVENT=25 (also pins 8 param↔PI, `:658-668`) |
| setPermissionsA | SET_PERMISSIONS=26 |
| setVKA | SET_VERIFICATION_KEY=27 |
| createSealPairA | CREATE_SEAL_PAIR=28 |
| refreshDelegationA | REFRESH_DELEGATION=29 |
| incrementNonceA | INCREMENT_NONCE=53 |
| revokeDelegationA | REVOKE_DELEGATION=30 |
| createCellA | CREATE_CELL=31 |
| spawnA | SPAWN_WITH_DELEGATION=32 |
| bridgeCancelA | BRIDGE_CANCEL=33 |
| exerciseA | EXERCISE_VIA_CAPABILITY=34 |
| introduceA | INTRODUCE=35 |
| pipelinedSendA | PIPELINED_SEND=36 |
| createCommittedEscrowA | CREATE_COMMITTED_ESCROW=39 |
| bridgeFinalizeA | BRIDGE_FINALIZE=41 |
| releaseEscrowA / refundEscrowA | 42 / 43 |
| releaseCommittedEscrowA / refundCommittedEscrowA | 44 / 45 |
| createCellFromFactoryA | CREATE_CELL_FROM_FACTORY=13 (`:932-941`, also reserved-freeze) |
| receiptArchiveA | RECEIPT_ARCHIVE=51 |
| refusalA | REFUSAL=52 |
| cellSealA / cellDestroyA | CELL_SEAL=49 / CELL_DESTROY=47 |
| customA (NoOp passthrough variant) | CUSTOM=8 (`:818-826`, + reserved-freeze + GROUP-7 count) |

WARNING (real, not clone): these effects are PASSTHROUGH at the row/balance level
but carry their actual semantics OFF the EffectVM row (in caps/log/escrow side
state). The row emitter can only pin "row frozen"; the genuine effect content (a
delegation edge, an escrow release) lives in the abstract `CircuitSpecTriangle`
layer, NOT the row. So a Group-B row-intent is HONEST but WEAK — it does not pin
the effect's real meaning. See §5.

### GROUP C — field-write with index selection (Lagrange / bit-decomp). MEDIUM.
Representative: **setFieldA** (SET_FIELD=2, `:564-638`). The AIR uses an 8-point
Lagrange basis (`lagrange_bit`, `:601-622`) to select the written field by index,
plus a field-index range gate (`:632-637`) and a single-field-diff sum
(`:575-581`). RowIntent: exactly one field at the param index changes to the param
value, all others + balance/cap frozen. Effort medium: the Lagrange selector must be
emitted as an `EmittedExpr` and its `holdsVm` proved equivalent to "field[idx] =
v ∧ ∀ j≠idx frozen" — needs a Lean Lagrange-interpolation lemma the transfer proof
never touched.

### GROUP D — reserved-flag lifecycle (pow2 bit-decomp). MEDIUM.
Effects that mutate the `RESERVED` flag-word via a power-of-two delta:
| Effect | sel | mechanism (AIR) |
|---|---|---|
| sealA | SEAL=10 | `:866-889` `new_reserved = old + 2^idx`, `seal_pow2 = lagrange_pow2(idx)` |
| unsealA | UNSEAL=11 | `:891-914` `old_reserved = new + 2^idx` |
| makeSovereignA | MAKE_SOVEREIGN=12 | `:917-929` `+256` + `mode_bit=0` |
| cellUnsealA | CELL_UNSEAL=50 | `:1273-1288` (target↔aux pin) |

Shared infra: the UNCONDITIONAL reserved bit-decomposition (`:589-599`) — 8 bits +
mode bit recomposing to `sb(RESERVED)`. The emitter must add a `VmRange`-like
reserved-decomposition tooth and a `lagrange_pow2` `EmittedExpr`. Effort medium;
once the Lagrange lemma from Group C exists, these reuse it.

### GROUP E — cap-root rewrite via ONE Poseidon2 site. HARD (set-membership).
The cap_root is updated to a hash of (old_cap_root, entry). The emitter must add the
extra hash site(s) AND prove the new `transferHash_binds`-style binding pins the
cap-root to the genuine digest.
| Effect | sel | sites (AIR) |
|---|---|---|
| delegate / GrantCapability | GRANT_CAP=3 | site 4 `H2(old_cap_root, cap_entry)`, `:640-643` |
| revoke / RevokeCapability | REVOKE_CAPABILITY=24 | site 5, `:713-722` |
| attenuateA | ATTENUATE_CAPABILITY=48 | sites 29,30 `leaf=H2(slot,narrower); exp=H2(root,leaf)`, `:1243-1257` |
| delegateAttenA | (routes via GRANT_CAP/ATTENUATE) | per executor mapping |
| createObligationA | CREATE_OBLIGATION=6 | sites 6,7 (nested), `:786-800` |
| slashObligationA | SLASH_OBLIGATION=9 | site 8, `:828-840` |

Effort hard but BOUNDED: the GROUP-4 state-commit chain already proves the
`siteHoldsAll`→genuine-digest pattern (`transferHash_binds`,
`EffectVmEmitTransfer.lean:392-410`). These effects add ONE more site and a
`new_cap_root = digest` gate. The new proof obligation is "cap_root pinned to the
genuine H2," structurally identical to `transferHash_binds`. The HARD part is that
the ROW only proves `new_cap_root = H2(old_cap_root, entry)`; whether that H2 is the
RIGHT capability move (attenuation ≤ held) lives in the abstract layer
(`attenuate_circuit_pins_intent`, `CircuitSpecTriangle.lean:685`) — §5.

### GROUP F — cross-binding PI pins (nullifier / commitment / topic). MEDIUM.
A param column is pinned EQUAL to a public input (no hash, no balance subtlety
beyond Group A):
| Effect | sel | PI pin (AIR) |
|---|---|---|
| noteSpendA | NOTE_SPEND=4 | `prm(NULLIFIER) = pv[NOTESPEND_NULLIFIER]`, `:734-737` |
| noteCreateA | NOTE_CREATE=5 | `prm(NOTE_COMMITMENT) = pv[NOTECREATE_COMMITMENT]`, `:739-742` |
| burnA | BURN=46 | `prm(BURN_TARGET) = pv[BURN_TARGET_PI]`, `:744-747` |
| emitEventA | EMIT_EVENT=25 | 8 param↔PI pins, `:658-668` |

These are `piBinding`-style gates (the IR already supports `piBinding`,
`EffectVmEmit.lean:165`). Effort medium: combine the Group-A balance clone with one
or more PI-equality gates. NOTE: nullifier UNIQUENESS / no-double-spend is NOT a row
constraint — the row only pins nullifier=PI; the set non-membership is enforced
elsewhere. The row-intent must NOT overclaim here (§5).

### GROUP G — merkle-path set-membership over a queue/handoff root. HARD.
The hardest: an aux-carried merkle leaf + sibling hashed up to a root pinned to a PI
or a field. Multiple ordered sites + aux columns + sometimes an aux-inverse
non-membership tooth.
| Effect | sel | sites / mechanism (AIR) |
|---|---|---|
| validateHandoffA / swissHandoffA | VALIDATE_HANDOFF=17 | sites 16–20 (5 sites), root = `pv[APPROVED_HANDOFFS_BASE]`, `:1016-1038` |
| enlivenRefA | ENLIVEN_REF=15 | sites 11,12,13 (3 sites) + field[4] root, `:962-986` |
| swissExportA (exportSturdyRef) | EXPORT_STURDY_REF=14 | sites 9,10 (swiss) + refcount field, `:943-960` |
| swissDropA (dropRef) | DROP_REF=16 | sites 14,15 + refcount-inverse aux, `:988-1014` |
| queueEnqueueA | ENQUEUE_MESSAGE=19 | sites 22,23,24 + program-vk-inverse, `:1062-1093` |
| queueDequeueA | DEQUEUE_MESSAGE=20 | site 25 + msg-inverse, `:1095-1118` |
| queueResizeA | RESIZE_QUEUE=21 | delta-sign bit + capacity arith (NO hash), `:1120-1150` — actually MEDIUM |
| queueAtomicTxA | ATOMIC_QUEUE_TX=22 | sites 26,27 (combined-root binding), `:1152-1175` |
| queuePipelineStepA | PIPELINE_STEP=23 | site 28 + pipeline-id-inverse, `:1177-1209` |

Effort hard: these need the multi-site ordered chain (the IR supports it via
`HashInput.digest k` + ordered `siteHoldsAll`) PLUS the aux-inverse non-zero gates
(e.g. `program_vk * program_vk_inv = 1`, `:1090`) which are a NEW proof idiom the
transfer beachhead never used. The merkle-path soundness ("leaf ∈ tree ⟺ chosen
root = pinned root") is the genuine set-membership tooth.

### Effort tally
- TRIVIAL (clone-transfer): Groups A + B = ~30 selectors. Do these first.
- MEDIUM (Lagrange / bit-decomp / PI-pin / inverse): Groups C, D, F + queueResize =
  ~8 selectors.
- HARD (Poseidon2 set-membership): Groups E + G = ~15 selectors.

---

## 3. `lean_descriptor_air.rs` — the Phase-2 RustInterpreter status

GOOD NEWS: the multi-row interpreter is **already built and load-bearing**, not a
gap. `EffectVmDescriptorAir` (`lean_descriptor_air.rs:1372-1502`) is a full p3 AIR
that consumes the emitted `emitVmJson`:
- reads `local` + `next` + `public_values` (`:1417-1421`);
- `gate` + `transition` on `when_transition` (rows 0..n-2, `:1469-1484`);
- `pi_binding` on `when_first_row`/`when_last_row` (`:1439-1465`);
- every `hash_site` arithmetized through the SAME `poseidon2_permute_expr` gadget
  the hand AIR uses, on the WHOLE domain, with `digests[k]` available to later sites
  (`:1426-1437`) — the anti-ghost state-commit tooth;
- range gates by bit-decomposition (`:1486-1500`);
- `parse_vm_descriptor` (`:1223`) decodes the four constraint forms + sites + ranges
  (`:1166-1219`, `:1089-1164`);
- `prove_vm_descriptor` / `verify_vm_descriptor` (`:1554`, `:1597`) +
  `extend_vm_trace` (`:1518`) run it through `p3-batch-stark`;
- round-trip + tamper tests exist (`:3984-4042`).

So the IR↔interpreter bridge is DONE for the transfer shape and is generic over
constraint count. What amplification needs from this file:

1. **No new constraint FORMS needed** for Groups A/B/E/F/G — they all decompose into
   `gate` + `transition` + `pi_binding` + `hash_site`, which the interpreter already
   evaluates. Adding effects is purely emitting more of the same JSON.

2. **The GLOBAL constraints are NOT in the descriptor path.** The running full AIR
   enforces GROUP 1 selector-validity + sum-to-one (`effect_vm_p3_full_air.rs:487-496`),
   GROUP 2a balance-limb range (`:498-515`), the nonce-increment global (`:1326`),
   GROUP 5 net_delta sign-bit (`:1329-1332`), GROUP 6 net_delta PI binding
   (`:1334-1346`), GROUP 7 custom-count running sum (`:1348-1354`), and the row-0
   sovereign/federation/owner boundary pins (`:1409-1445`). The transfer descriptor
   emits NONE of these (it emits only the transfer-specialized gates + the shared
   state-block transition/boundary/commit chain, `EffectVmEmitTransfer.lean:178-184`).
   For a SINGLE-effect single-row descriptor these globals are not yet load-bearing,
   but a faithful multi-effect EffectVM descriptor (the eventual goal of REPRODUCING
   the running AIR by construction) MUST emit them. They are not new IR forms —
   selector-validity and sum-to-one are `gate` bodies; the GROUP-6 net_delta PI
   binding is a `gate` reading `pv` (the interpreter's gates can read `pv`? — NO:
   `LeanExpr::eval_expr` only reads `local` (`:120-131`), it has no `pv` access).

   **REAL INTERPRETER GAP #1**: gates cannot reference public inputs. The running AIR
   has selector gates that pin params to PIs INSIDE a `when_transition` gate (e.g.
   emitEvent `:660`, noteSpend `:736`, GROUP-6 net_delta `:1343`). The descriptor IR
   models PI access ONLY through `piBinding` (a bare `local[col] = pv[k]`), which is
   `when_first/last_row`-guarded and cannot express "on every transition row,
   `s_emitevent * (prm(i) - pv[k]) = 0`." To emit Group-F cross-bindings as the
   running AIR does (per-row, selector-gated, not just boundary), the IR needs a gate
   form whose body can reference `pv` — i.e. extend `EmittedExpr` with a `pi k`
   variant and thread `pv` into `eval_expr` (`lean_descriptor_air.rs:120`) and into
   the Lean `EmittedExpr.eval`. Currently Group-F can only be emitted as a `piBinding`
   on a boundary row, which is a WEAKER constraint than the running AIR's per-row pin.

3. **REAL INTERPRETER GAP #2 (the multi-row transition window)**: `main_next_row_columns`
   (`:1391-1405`) only requests `next.state_before[hi]` for emitted `transition`
   constraints. GROUP 7's custom-count running sum reads `next[AUX_BASE+CUSTOM_COUNT_ACC]`
   (`effect_vm_p3_full_air.rs:1351`) — a `next` read of an AUX column, not a
   state-before column. The descriptor IR has no form for "next aux continuity," so a
   faithful multi-row descriptor can't yet express the GROUP-7 accumulator. Needs a
   generalized `transition` form `next[col] - f(local)` over arbitrary columns.

4. **Range/aux layout coupling**: `air_width` puts hash-aux blocks first, then range
   bits (`:978-982`), matching the hand AIR's `EFFECT_VM_WIDTH + i*PERM_AUX`. As more
   effects add sites, the aux layout grows; `extend_vm_trace` (`:1518`) and the trace
   generator must stay in lockstep on site ORDER (the same `hash_sites()` contract the
   hand AIR documents at `effect_vm_p3_full_air.rs:107-113`). This is a discipline
   constraint, not a code gap, but it is where drift will hide.

Bottom line: the interpreter handles Groups A, B, D (ranges), E, G (sites) as-is.
Groups F and the GLOBAL group need the two IR extensions above (`pi`-referencing
gate body; next-aux transition).

---

## 4. Honest ordering

**Phase 1 — clones (Groups A + B, ~30 selectors).** No interpreter change, no new
proof idiom. Each is a 30-min clone of the transfer skeleton with the balance gate
swapped (A) or removed (B). Do these first; they immediately widen coverage and
validate the skeleton's reusability. Land them in batches sharing the
transition/boundary/commit infra (steps 3/4/10 are literally copy-paste).
- BLOCKER for honesty: Group-B effects must state HONEST weak row-intents
  ("row frozen except nonce") and NOT pretend the row pins the delegation/escrow
  semantics (§5). Cross-reference the abstract `*_circuit_pins_intent` to document
  what the row does NOT cover.

**Phase 2 — index/flag effects (Groups C + D + queueResize, ~8).** Requires the Lean
Lagrange-interpolation lemma (8-point basis) — build it ONCE, reuse across setField /
seal / unseal / makeSovereign. Medium, self-contained.

**Phase 3 — PI-cross-binding (Group F, ~4).** BLOCKED on interpreter GAP #1
(`pi`-referencing gate body) IF we want per-row fidelity to the running AIR;
otherwise emit as boundary `piBinding` (weaker, but the IR supports it today). Decide
fidelity-vs-now explicitly.

**Phase 4 — cap-root hashing (Group E, ~6).** Each adds ONE site + a
`new_cap_root = digest` gate; the proof clones `transferHash_binds`. The state-commit
chain proof (`EffectVmEmitTransfer.lean:392-410`) is the template. The HARD CORE
beyond the row: whether the H2 input encodes the RIGHT capability move (attenuation
monotonicity, revocation root-of-trust) is the abstract layer, NOT the row — keep
those claims OUT of the row-intent.

**Phase 5 — merkle set-membership (Group G, ~15).** The genuine hard core. Needs:
(a) the multi-site ordered chain (IR supports it); (b) the aux-inverse non-zero
idiom (`x * x_inv = 1`, NEW to the emitter); (c) a merkle-path-membership lemma
("chosen root from leaf+siblings = pinned root ⟺ leaf ∈ tree"). What BLOCKS full
soundness here is the same authenticated-state-commitment dependency the project
memory flags: the row pins `chosen_root = pinned_PI_root`, but the PI root's
authenticity (that it is the genuine accumulated queue/handoff set, not an
attacker-chosen root) is a TURN-LEVEL binding, not a per-row one. Until the
authenticated turn-root chain pins these auxiliary roots the way GROUP-4 pins
state_commit, Group-G row-intents are conditional on "the PI root is genuine."

**Do NOT** attempt Group G before Groups A/B are landed and the skeleton's
reusability is proven on the easy bulk — and before deciding GAP #1/#2.

---

## 5. Where the ABSTRACT spec is NOT strong enough to drive a concrete gate

This is the load-bearing skepticism. The abstract `CircuitSpecTriangle` and the
concrete EffectVM emitter are **two different proof layers that do not yet meet**:

1. **Different state model.** `CircuitSpecTriangle` proves `*_circuit_pins_intent`
   over `RecordKernelState` / `RecChainedState` and an ABSTRACT circuit witness
   `satisfiedE2Triple` / `encodeE2Triple` (e.g. transfer at
   `CircuitSpecTriangle.lean:260-274`, queueEnqueue at `:1862-1878`). The EffectVM
   emitter proves `transferVm_faithful` over the 186-COLUMN ROW (`saCol`/`sbCol`/
   `prmCol`, `EffectVmEmitTransfer.lean:196-211`). NOTHING currently proves the row
   layout IS a faithful encoding of `RecordKernelState`. The bridge is the
   state-commitment (`recStateCommit` injective) — but the emitter's
   `transferHash_binds` (`:392-410`) pins `state_commit = H4(...row cells...)`,
   while the abstract spec's soundness rests on `D`/`logHashInjective`/`compressN`
   over the kernel record. **These two commitment notions are not proven equal.** So
   "amplifying the emitter" does NOT inherit the abstract triangle's intent
   guarantee for free; each effect's ROW intent is an INDEPENDENT statement that
   must itself be argued to capture the protocol move. The amplification will surface
   this gap on EVERY non-trivial effect.

2. **Group-B passthrough effects: the row says almost nothing.** For delegation /
   escrow-release / introduce / refresh (Group B), the row is balance/frame-frozen,
   so a ROW-level `RowIntent` can only assert "row unchanged except nonce." The
   genuine effect (a caps edge, an escrow state transition) is entirely in the
   abstract `caps`/`escrows`/`log` side-state that the EffectVM row does NOT carry as
   first-class columns (it only carries `cap_root`, a single hashed field). So for
   these effects the concrete emitted gate CANNOT pin the intent — the abstract spec
   is "stronger" in content but operates on a state the circuit row doesn't witness.
   Honest amplification must state the weak row-intent and explicitly defer the real
   semantics to the cap_root hash chain (Group E) or to the abstract layer.

3. **Set-membership / uniqueness is unstated at the row.** noteSpend's nullifier
   no-double-spend, queue FIFO ordering, handoff approved-set membership — the
   abstract specs DO pin these (`noteSpend_circuit_pins_intent`; queueEnqueue pins
   the FIFO tail-append `CircuitSpecTriangle.lean:1872-1874`). But the running ROW
   only pins `nullifier = PI` (`effect_vm_p3_full_air.rs:736`) or `chosen_root =
   PI_root` (`:1026-1028`). The non-membership / ordering is a TURN/accumulator
   property, not a per-row gate. A row-intent that claimed "this nullifier is fresh"
   would be FALSE for the row in isolation — the emitter must NOT overclaim. This is a
   genuine gap (the row is weaker than the abstract spec), not clone work.

4. **The aux-inverse "non-membership" gates are existence-witnessed, not
   set-checked.** queueEnqueue's `program_vk * program_vk_inv = 1`
   (`effect_vm_p3_full_air.rs:1090`) and dropRef's refcount inverse (`:998`) prove a
   value is NON-ZERO, not that it is a member of a set. The abstract spec's
   `queueEnqueueK ... = some k₁` (`CircuitSpecTriangle.lean:1872`) is a much stronger
   FIFO-correctness statement. The row inverse-gate is a necessary but NOT sufficient
   tooth; the row-intent must reflect only the non-zero fact.

5. **mintA selector ambiguity.** The abstract `mint_circuit_pins_intent` exists
   (`:169`) but the running AIR has no `MINT` selector — mint is folded into the
   credit/NOTE_CREATE machinery. Before cloning mintA at the row level, the doer must
   confirm which selector + param layout the trace generator emits for a mint, or the
   row-intent will pin the wrong column.

RECOMMENDATION: treat the row-emitter amplification as a DISTINCT deliverable from
the abstract triangle. For each effect, the row-intent should be (a) HONEST about
what the row pins (balance/frame/cap_root/PI-equality), and (b) explicitly annotated
where the genuine protocol semantics live in the abstract layer that the row cannot
reach. Do NOT relay "the abstract spec already proves intent" as if it discharges
the row obligation — it does not; the layers are not yet bridged.

---

## Appendix — non-vacuity / honesty checks already in place (do not regress)
- Transfer beachhead is genuinely non-vacuous: `goodRow_realizes_intent`
  (`EffectVmEmitTransfer.lean:497`) witnesses TRUE, `badRow_rejected` (`:537`)
  witnesses FALSE. EVERY new effect MUST ship both.
- `#assert_axioms` on all transfer theorems (`:551-561`) — kernel axioms only
  below the abstract crypto carrier. Hold this bar.
- The hash carrier is abstract `hash : List ℤ → ℤ` (`EffectVmEmit.lean:231`) — never
  an in-Lean algebraic hash. The Rust side uses the genuine `poseidon2_permute_expr`
  gadget (`lean_descriptor_air.rs:1431`). Keep this separation.
