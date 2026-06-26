# Rust ↔ Lean executor parity — the justification for shipping the Rust executor by default

dregg has two executors for the same kernel transition:

- the **Rust executor** — `dregg_turn::TurnExecutor::execute` (`turn/src/executor/apply.rs`). Small,
  fast, no FFI, compiles to wasm. This is what the SDKs run.
- the **verified Lean executor** — `Dregg2.Exec.recKExec`, compiled into `libdregg_lean.a` and reached
  from Rust through `dregg-lean-ffi` (`dregg_exec_full_forest_auth`). This is the artifact the Lean
  metatheory proves `Exec ⊑ Spec` against. It is ~150MB linked and native-only.

The SDKs ship the **Rust** executor by default and treat the Lean kernel as an **opt-in shadow** (a
node may link it to gate or to differentially verify; see `dregg-exec-lean`). This document is the
justification for that default: *the Rust executor is at parity with the verified Lean spec.*

It states honestly what is **proven**, what is **audited**, what the **differential gauntlet** adds
empirically, and what the **residual** to a full equivalence *proof* is.

## What "parity" means here, and what it does not

There is no machine-checked theorem `TurnExecutor::execute = recKExec`. The Rust executor is not
formally specified in Lean; only the Lean executor is. So "parity" is **not** a proof of equality.
It is the conjunction of three things, each with its own evidence:

1. **The verified executor refines the spec** — proven in Lean (`Exec ⊑ Spec`,
   `docs/reference/lean-kernel.md`). This is the anchor: the Lean executor is a faithful, sound
   realization of the kernel. Parity to it inherits its soundness *to the extent the two agree*.
2. **The Rust executor is audited against the verified spec, gate by gate** — the equivalence audit
   (the perf-kernel-supply epoch) found that **state agreement is not rejection parity**: two
   executors can agree on the post-state of every turn they both accept and still disagree on which
   turns to *reject*. A soundness hole is exactly a turn the Rust executor commits while the verified
   kernel refuses (Rust under-enforces a gate). The audit built the rejection-parity harness
   (`exec-lean/tests/rejection_parity.rs`) and **aligned six Rust under-enforcements** to the
   verified spec (self-transfer `src==dst`, the lifecycle-liveness conjuncts across nine effect arms,
   archive, reserved slots, the mint authority gate, …).
3. **The two executors empirically agree turn-by-turn over a corpus** — accept/reject parity *and*
   byte-identical post-state, demonstrated by the differential gauntlet below.

This is **audited + differential parity, not proven equivalence.** That is the honest bar, and it is
the bar this document argues is sufficient to ship the Rust executor by default with the Lean kernel
as opt-in.

## The differential gauntlet

`exec-lean/tests/rust_lean_parity_gauntlet.rs` is the single consolidated artifact. It runs **one
corpus** of turns through **both** executors over the same pre-state and classifies each turn:

- `BothAcceptStateAgree` — both commit **and** the post-states are **byte-identical**: per-cell
  balance + nonce + state fields + `cap_root`, **and** the whole-ledger `.root()` (the Merkle
  commitment a light client checks). This is the load-bearing good result.
- `BothReject` — both refuse. The good result for an adversarial turn.
- `BothAcceptStateDiverge` — both commit but produce **different** states. A silent state bug; the
  worst outcome for ship-Rust. **The gauntlet hard-fails on any occurrence.**
- `RustAcceptsLeanRejects` — Rust commits a turn the verified kernel refuses (the under-enforcement
  direction). **The gauntlet hard-fails** unless the cohort is on the documented
  `SAFE_DIRECTION_RESIDUALS` allowlist (below).
- `RustRejectsLeanAccepts` — Rust is *stricter* than the spec (the safe divergence direction).
  Reported, never failed.
- `WireGap` — the turn is not marshallable to the Lean wire; cannot be compared. Reported, never
  faked.

### Coverage

The corpus covers the full effect **cohort** with a representative committing turn each, an edge-case
set, and an adversarial should-reject battery. As of the last green run:

- **17 cohort effects achieve `BothAcceptStateAgree`** (byte-identical post-state, including
  `.root()`): Transfer, SetField (developer and reserved slots), EmitEvent, IncrementNonce,
  NoteCreate, GrantCapability, Introduce, RevokeCapability, RevokeDelegation, CellSeal, CellDestroy,
  SetPermissions, SetVerificationKey, MakeSovereign, Refusal, ReceiptArchive.
- **8 adversarial turns achieve `BothReject`**: overspend, self-transfer, transfer-from-sealed,
  set-field-on-sealed, emit-on-sealed, proofless note-spend, unauthorized mint, cross-cell grant
  with no held edge.
- **0 `BothAcceptStateDiverge`** and **0 new under-enforcements** — the two teeth never bit.

The gauntlet also enforces a **non-vacuity floor** (≥12 byte-identical agreements, ≥5 shared
rejections) so it cannot pass by trivially gapping or rejecting everything.

The gauntlet self-skips (does not fail) when `lean_available()` is false — it cannot run the verified
kernel without the linked archive.

## The honest residual

Four cohort effects classify as `RustAcceptsLeanRejects` — Rust commits, the verified kernel refuses
— and are allowlisted as **characterised, safe-direction residuals**. The direction is safe because
the verified kernel is the *stricter* one: a shadow-gated node takes the Lean verdict as
authoritative and **vetoes** these commits. For the **pure-Rust SDK** (no Lean linked) these are the
honestly-named residuals — Rust would accept these turns where the verified spec would not:

- **`Burn`** — the scalar `Effect::Burn` (destroy balance, no destination) has no conserving image in
  the verified issuer-supply kernel (DREGG3 §2.2: `.burnA` is a return-to-well move). On the one-cell
  wire numbering it marshals to a self-burn of the well, which the kernel refuses outright. This
  closes when the staged Rust value-model migration makes apply.rs's burn the well move.
- **`Mint`** (authorized) — a **wire-faithfulness** limit, not under-enforcement. apply.rs's
  `apply_mint` gates on a control-grade `EFFECT_MINT` cap over the issuer well — the faithful image of
  Lean `mintAuthorizedB`. The `adv-mint-unauthorized` case proves the two gates **agree-reject** when
  the cap is absent. The authorized-mint asymmetry is purely that the shadow marshals `Mint` with the
  synthetic `asset: 0`, so the verified gate cannot see the held node-cap over the marshalled issuer.
  The native cap graph is exercised without the wire limit in
  `dregg-turn::conservation_mint_property`.
- **`AttenuateCapability`** and **`CellUnseal`** — cap-/lifecycle-reshape effects whose **commit bit**
  currently diverges in the safe direction: the held cap (for the monotone-narrowing check) and the
  sealed payload (for the unseal) are not faithfully numbered on the marshalled wire, so the verified
  kernel fail-closes. When both *do* commit, the reconstituted post-state agrees; only the commit bit
  diverges. Same wire-faithfulness class as `Mint`.

Each residual is a divergence **of the wire boundary or a staged value-model migration**, not a
demonstrated case of Rust committing an *unsound* state. None is a `BothAcceptStateDiverge`. The
deeper residual is the structural one named at the top: there is **no `TurnExecutor::execute =
recKExec` theorem**, because the Rust executor is not formally specified. Parity is audited +
differential, and a new effect or gate must be added to the corpus (and, ideally, the audit) for the
guarantee to extend to it.

## The bar for "ship Rust by default, Lean opt-in"

Shipping the Rust executor by default is justified when:

1. the verified executor refines the spec — **proven** (`Exec ⊑ Spec`);
2. the audited under-enforcements are aligned to the verified spec — **done** (the six alignments;
   `rejection_parity.rs` hard-fails on any *new* `ASYM-Rust-accepts`);
3. over the full cohort + adversarial corpus, the two executors show **accept/reject parity and
   byte-identical post-state**, with **zero silent state divergence** and **zero new
   under-enforcement** — **demonstrated** by `rust_lean_parity_gauntlet.rs`;
4. every divergence that remains is **named, characterised, and in the safe direction** (the verified
   kernel is stricter), with a closure path — **true** of the four residuals above.

All four hold. A node that wants the verified guarantee end-to-end links the Lean archive and runs it
as the authoritative shadow; the SDK default is the Rust executor, justified by the parity above.

## Where to look

- `exec-lean/tests/rust_lean_parity_gauntlet.rs` — the consolidated gauntlet (accept/reject parity +
  byte-identical post-state over the full cohort + adversarial battery).
- `exec-lean/tests/rejection_parity.rs` — the rejection-parity harness (the under-enforcement audit;
  hard-fails on any new dangerous asymmetry).
- `exec-lean/tests/lean_state_producer_differential.rs`, `…_coverage.rs`, `…_widen.rs` — the
  state-producer differentials (the verified Lean executor *as the state producer*; per-effect
  byte-identical post-state with negative teeth on each characterised gap).
- `exec-lean/tests/rust_lean_divergence_finder.rs` — the broad effect-by-effect divergence ledger.
- `docs/reference/lean-kernel.md` — `Exec ⊑ Spec`, the anchor the parity inherits from.
- `docs/reference/lean-conserve.md` — conservation & supply (the issuer-well model the `Burn`/`Mint`
  residuals close against).
