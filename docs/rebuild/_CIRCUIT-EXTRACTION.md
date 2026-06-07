# Circuit extraction: verified-by-construction transfer + the amplification path

_Status 2026-06-07. The transfer EffectVM circuit the audited Plonky3 verifier checks is
EXTRACTED from Lean and proved faithful to the transfer intent. This doc records (1) what
"verified-by-construction" means here and the one residual assumption, (2) the
near-definitional differential that closes the loop, and (3) the concrete roadmap to
amplify from transfer to all 51 effects and to retire the bespoke `EffectVmAir`._

---

## 1. The extraction loop (what is now closed for transfer)

```
   CircuitSpecTriangle.intentTransfer        (protocol intent, abstract)
            │  EffectVM-row projection
            ▼
   TransferRowIntent                          (Lean, EffectVmEmitTransfer.lean §5)
            ▲
            │  transferVm_faithful  (gates ⇔ intent, §7; anti-ghost §8)
            ▼
   transferVmDescriptor  ── emitVmJson ──▶  TRANSFER_VM_DESCRIPTOR_JSON   (verbatim bytes)
   (Lean IR, EffectVmEmit.lean)                       │  parse_vm_descriptor
                                                      ▼
                                            EffectVmDescriptorAir          (Rust, the RUNNING AIR)
                                                      │  prove_vm_descriptor / verify_vm_descriptor
                                                      ▼
                                            AUDITED p3-batch-stark prover+verifier
```

Each edge is checked, not asserted:

* **intent ⇔ gates** — `EffectVmEmitTransfer.transferVm_faithful` (machine-checked, `#assert_axioms`
  clean, no `sorry`/`:= True`): on a transfer row the emitted descriptor's per-row gates hold IFF
  `TransferRowIntent` holds. Anti-ghost (`transferVm_rejects_wrong_balance/_nonce/_output`) +
  the GROUP-4 hash binding (`transferHash_binds`) + boundary pins (`boundaryFirst/Last_pins`) +
  the whole-descriptor corner (`transferVmDescriptor_pins_intent`). Non-vacuity is witnessed:
  `goodRow_realizes_intent` (TRUE) and `badRow_rejected` (FALSE).

* **descriptor → wire bytes** — `emitVmJson transferVmDescriptor` is the SINGLE source. The Rust
  `TRANSFER_VM_DESCRIPTOR_JSON` constant is the **byte-identical** output of that emit (3507 bytes,
  confirmed `EXACT MATCH: True` against `lake env lean --run` of the emit; structurally re-pinned by
  the `parse_vm_descriptor_transfer` test: 14 gates / 14 transitions / 7 pi-bindings / 4 ordered hash
  sites / 2 ranges, including the site-3 `Digest(0),Digest(1),Digest(2),Zero` chain and the
  ACTOR_NONCE/NEW_COMMIT pins).

* **wire bytes → running AIR** — `parse_vm_descriptor` decodes the JSON into `EffectVmDescriptor`;
  `EffectVmDescriptorAir::eval` interprets it term-for-term (gate bodies via the same `LeanExpr`
  recursion, transitions on `when_transition`, pi-bindings on `when_first/last_row`, hash sites via
  the SAME `poseidon2_permute_expr` gadget the bespoke air uses). The descriptor is the source; the
  AIR is a pure interpreter of it.

### Is transfer verified-by-construction now? YES, modulo one named residual.

The running transfer circuit (the descriptor-sourced AIR the audited verifier checks) is provably the
spec we prove about, because:

1. the AIR's accepted constraint set is a pure function of the descriptor (no hand-written transfer
   gate exists in `EffectVmDescriptorAir` — it only walks `desc`), and
2. the descriptor is the verbatim Lean emit, whose denotation is proved ⇔ the intent.

**The one residual assumption** (precisely): the Rust **interpreter** of the descriptor
(`EffectVmDescriptorAir::eval` + `extend_vm_trace` + `parse_vm_descriptor`) is a faithful transcription
of Lean's denotation (`EffectVmEmit.satisfiedVm`). This is the analogue of "trusting the extractor."
It is NOT proved in Lean (there is no Lean⟶Rust extraction certificate); it is pinned by the
**near-definitional differential** of §2 (denotation-vs-AIR over honest + 5 tamperings) and by the
`poseidon2_permute_expr` reuse (the hash gadget is literally the bespoke air's, already audited). The
residual shrinks to: "the Rust `denote_vm_descriptor` and `EffectVmDescriptorAir::eval` factor over the
same domains" — which the differential exercises directly. Removing it entirely would require either a
verified emitter (Lean → Rust extraction proof) or porting the descriptor interpreter into Lean and
proving `satisfiedVm`-equivalence; both are future work (§3, retirement track).

This is materially tighter than the prior story (a hand-ported AIR differential-tested against the
bespoke AIR), where the "spec" was a second hand-port and the bug surface was the port itself. Here
there is no transfer-specific hand-port in the running path at all.

---

## 2. The near-definitional differential (the loop-closing test)

`circuit/src/lean_descriptor_air.rs :: tests::lean_emitted_effectvm_transfer_differential`.

It computes the descriptor's **own denotation** in Rust — `denote_vm_descriptor`, the line-by-line
mirror of Lean's `EffectVmEmit.satisfiedVm`:

* every `Gate(body)` vanishes on the transition domain (rows `0..n-2`);
* every `Transition{hi,lo}` continuity holds on the transition domain;
* `PiBinding{first,…}` holds on row 0, `{last,…}` on row `n-1`;
* every hash site's `digest_col` carries its genuine Poseidon2 digest, on every row (site `i` reading
  earlier sites' digests — the ordered state-commit chain);
* every range wire's low `bits` bits fit (in-range).

It then asserts, **witness by witness**, that this denotation EQUALS what the audited p3 prover+verifier
ACCEPTS through `EffectVmDescriptorAir`. Result (all green):

| case                          | denotation | AIR-accepts | agree |
|-------------------------------|:----------:|:-----------:|:-----:|
| honest transfer               | accept     | accept      | ✓     |
| forged commitment (last row)  | reject     | reject      | ✓     |
| tampered ACTOR_NONCE (PI)     | reject     | reject      | ✓     |
| forged post-balance (row 0)   | reject     | reject      | ✓     |
| broken transition continuity  | reject     | reject      | ✓     |
| out-of-range balance (2³⁰)    | reject     | reject      | ✓     |

The honest case asserts BOTH accept (so the agreement is not vacuous always-reject); the five
tamperings exercise each constraint FORM (gate, transition, pi-binding-first, pi-binding-last, hash
site, range). This is the differential the task asked for: **the Lean-sourced AIR's accept/reject ≡
the Lean-emitted descriptor's denotation** — much tighter than a hand-port⟺bespoke differential,
because both sides here derive from the one verbatim descriptor.

The pre-existing `lean_emitted_effectvm_transfer_roundtrip` test remains: it drives the AIR over the
BESPOKE 186-col base trace (`generate_effect_vm_trace`) and checks honest-proves + 3 anti-ghost teeth,
i.e. the descriptor AIR agrees with the real witness generator on real traces. The two together pin
both "AIR = descriptor denotation" (§2) and "descriptor AIR accepts real bespoke witnesses" (roundtrip).

---

## 3. Amplification: transfer → all 51 effects, then retire the bespoke AIR

The EffectVM has **54 selectors** (`columns.rs::NUM_EFFECTS`); NoOp is padding, so ~51–53 real
effects carry per-effect constraints in `effect_vm/air.rs`. Transfer is the validated reference. The
work is mechanical-but-not-trivial; here is the concrete order.

### 3a. Per-effect emit (the bulk)

For each effect `E`, mirror what `EffectVmEmitTransfer.lean` did for transfer:

1. **Write `ERowIntent`** — the field-level move from protocol intent (the EffectVM-row projection of
   `CircuitSpecTriangle`'s intent for `E`). Most effects are *simpler* than transfer: `EmitEvent`,
   `SetPermissions`, `SetVerificationKey`, `IncrementNonce`, the seal/unseal family are **full-state
   passthrough + nonce tick + one bound hash param** — their intent is "frame fixed, one param binds
   into effects_hash." `Mint`/`Burn` are balance moves (like transfer's `gBalLo` with a fixed
   direction). The cap-touching family (`GrantCapability`/`RevokeCapability`/`CreateEscrow`/…) add a
   `new_cap_root == hash_2_to_1(old_cap_root, entry)` site (see §3b).
2. **Emit `EVmDescriptor`** through the existing `EffectVmEmit` IR (gates ++ transitions ++ boundary
   pins, hash sites, ranges). The IR already supports every form needed (gate/transition/pi-binding,
   ordered `VmHashSite`, range). No IR changes expected for the passthrough/balance families.
3. **Prove `EVm_faithful`** (gates ⇔ `ERowIntent`) + anti-ghost + non-vacuity witnesses, the same
   shape as §7–§11.5 of the transfer file. The transfer proof is a copy-adapt template; the
   passthrough effects collapse to near-trivial `linarith`/`ring` proofs.
4. **Pin the verbatim JSON** in `lean_descriptor_air.rs` (a `const E_VM_DESCRIPTOR_JSON`), confirm
   byte-identity against `emitVmJson`, and add the §2 differential for `E` (honest + per-form
   tamperings) and a roundtrip against `generate_effect_vm_trace` for `E`.

**Batching:** group by shape — (a) passthrough-only (~20 effects: events, perms, vk, nonce,
make-sovereign, receipt-archive, refusal, validate-handoff, …), (b) balance moves (mint, burn,
bridge mint/finalize/lock/cancel), (c) cap-root advance (grant/revoke/attenuate/delegate/escrow
family), (d) seal/swiss/sovereign-cell structural. (a) is a single afternoon's template fill; (b)/(c)
reuse transfer's `gBalLo`/hash-site machinery; (d) is the long tail.

### 3b. Hash-site coverage (the one IR-exercise that's new)

Transfer uses **4-arity** sites (the GROUP-4 state-commit chain). The cap-touching effects use
**2-arity** `hash_2_to_1` (`new_cap_root == hash_2_to_1(old_cap_root, entry[0])`, computed directly in
the bespoke evaluator at `air.rs:854/1027/1232`). The `VmHashSite` IR already carries `arity` and the
AIR's `vm_site_input_state` already tags position 4 with the arity capacity — so a 2-arity site is
expressible TODAY with `inputs = [Col(cap_root_before), Col(entry_limb0)]`, `arity = 2`. The only new
Lean work is the per-effect `hashSites` list + a `*Hash_binds` lemma per effect (the transfer
`transferHash_binds` is the template). `EmitEvent`/`SetPermissions` etc. bind their 8-limb param into
`effects_hash` (a Poseidon2 chain) — that is a multi-site fold; express it as an ordered site list
reading `Digest(i-1)` like the transfer GROUP-4 chain (the IR's left-to-right digest accumulator
already does exactly this).

### 3c. Retiring `effect_vm_p3_full_air.rs` + migrating the recursion crates

Today `effect_vm_p3_full_air::EffectVmP3Air` (and the bespoke `effect_vm/air.rs` it mirrors) is the
load-bearing single-effect AIR for `proof_forest` / `joint_turn` / `ivc`. To retire it:

1. **Per-effect parity gate** — once §3a covers all 51, add a differential that, for EVERY effect, the
   descriptor-sourced `EffectVmDescriptorAir` and the bespoke `EffectVmP3Air` accept the SAME witness
   set (honest + a tamper battery). This is the "the extracted AIR = the audited bespoke AIR on all
   effects" certificate. Until it is green for all 51, the bespoke AIR stays (cutover-ledger
   discipline: verified-replacement BEFORE deletion).
2. **Unify the trace generator** — `generate_effect_vm_trace` produces the 186-col base trace the
   descriptor AIR consumes via `extend_vm_trace`. Confirm `extend_vm_trace(desc, base)` reproduces the
   bespoke air's hash/range aux columns bit-for-bit for every effect (it already does for transfer —
   the roundtrip test). Then the descriptor path needs no bespoke witness code.
3. **Swap the recursion crates' inner AIR** — `proof_forest`/`joint_turn`/`ivc` instantiate
   `EffectVmP3Air`. Replace with `EffectVmDescriptorAir::new(descriptor_for(effect))`, keyed by the
   effect selector. The recursion machinery is AIR-generic (it takes a `StarkInstance`), so this is a
   constructor swap + a `descriptor_for : Effect → EffectVmDescriptor` table (built once from the 51
   Lean emits). Re-run the IVC/forest test suites as the parity gate.
4. **Delete** `effect_vm_p3_full_air.rs` and the bespoke `effect_vm/air.rs` constraint code only after
   (1)+(3) are green and the cutover ledger records the verified replacement. Keep `effect_vm/trace.rs`
   (the witness generator) until step 2's unification lands a descriptor-native generator, or keep it
   permanently as the base-trace producer (it is data, not constraints — no soundness role once the
   AIR is descriptor-sourced).

### 3d. Effort shape (honest)

* §3a passthrough batch (a): ~1 sitting, template fill, trivial proofs.
* §3a balance + cap batches (b/c): moderate — reuse transfer's gate/hash machinery, ~per-effect
  proof adaptation.
* §3a tail (d) + §3b multi-site effects_hash folds: the real work; the IR supports it but each needs
  its `*Hash_binds` lemma.
* §3c retirement: gated on §3a/§3b completeness + the per-effect parity differential; then a
  constructor swap + ledger entry. NOT a rewrite of the recursion crates.

The hard core is NOT the per-effect emit (mechanical) — it is the **per-effect parity differential
against the bespoke AIR** (§3c.1), which is what licenses deletion, and the residual-shrinking work of
§1 (a verified emitter or a Lean-side descriptor interpreter) if we want to remove the "trust the Rust
interpreter" assumption entirely.

---

## 4. Pointers

* Lean: `metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean`,
  `metatheory/Dregg2/Circuit/Emit/EffectVmEmitTransfer.lean` (registered in `Dregg2.lean`).
* Rust: `circuit/src/lean_descriptor_air.rs` PART 6 (decode/AIR/prove) + PART 6e (the §2 differential).
* Bespoke (to be retired): `circuit/src/effect_vm_p3_full_air.rs`, `circuit/src/effect_vm/air.rs`.
* The verbatim descriptor: `TRANSFER_VM_DESCRIPTOR_JSON` (= `emitVmJson transferVmDescriptor`, byte-identical).
