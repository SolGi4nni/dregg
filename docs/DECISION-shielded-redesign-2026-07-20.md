# DECISION BRIEF — the shielded pool (#10): fix, fence, or redesign?

**For: ember. From: Claude. 2026-07-20.** You asked to hear it straight after the workstream got
intermixed. Here it is: what's actually wrong, how bad, what the options cost, and what I'd do.

## TL;DR (my recommendation)

**Two moves, decoupled:**
1. **Do the honesty downgrade NOW** (zero code risk): the code/comments currently *claim* a
   post-quantum posture the deployed path does not have. That's a lie in the tree; fix it today
   regardless of the bigger question.
2. **Treat the real fix as a scoped *project*, gated on your priority call** — not a swarm lane.
   The clean fix (route the deployed transfer through the existing ring-clearing apex) closes all
   three seams coherently, but it's a **VK-affecting subsystem rewrite** with two named residuals.
   It's worth doing *if shielded is a near-term priority*; if not, **fence it** (it already
   fails-closed off the prover path) and spend the effort on the felt-width E2 batch instead.

The one thing I need from you: **is the shielded pool a near-term priority (→ commit to the
redesign), or a deferred subsystem (→ honesty-downgrade now, fence the rest)?**

## Stakes / reachability (so you can size it)

`apply_shielded_transfer` is `#[cfg(feature="prover")]` — the **verify-only / light-client build
fails it closed** (`InvalidEffect`). So every issue below is reachable **only in a prover-enabled
executor**, and shielded is **not in the committed VK** a light client checks. That bounds the blast
radius: it's a node-operator-trust surface, not a light-client-soundness surface.

## The three seams (what's actually wrong)

1. **#15 — `merkle_root` is prover-supplied, pinned to nothing. [worst]** `apply_shielded_transfer`
   rebuilds the membership tree `from_serialized_parts(payload.merkle_root, …)` and checks membership
   against **that** root — with no comparison to any committed accumulator root. A malicious prover
   supplies a root of their choosing and proves membership in a tree they built → **spend a note that
   was never created (theft/inflation).** This is larger than any felt-width birthday collision; the
   ~31-bit width is the entry point, not the wound.
2. **#16 — value-link is honest-prover-trusted.** `verify_value_link` (leaf-value ↔ Pedersen-leg-value)
   runs **only in tests**, never in `apply` (it needs the secret opening, so it *can't* run there as
   written). Deployed conservation proves only that the *Ristretto legs* balance, not that they equal
   the STARK-witnessed leaf values → a prover can mint by decoupling them.
3. **#17 — the PQ posture is overstated.** The circuit/docs declare the Poseidon2 `value_binding`
   authoritative and Ristretto "retired / not in the TCB" — but the **only no-mint gate that actually
   runs on the deployed path is the Ristretto DLog aggregate**, which is Shor-broken. The comments
   materially misdescribe the security posture.

Plus a standing debt: the `spend_circuit` AIR is **entirely Rust-authored** (house law #1 violation —
Lean only has *refinement* bricks over the Rust as ground truth), so it's a Lean-port target regardless.

## The convergence (why one fix closes all three)

The seams are not independent. The existing **`shielded_ring_clearing_nleg_air` + `shielded_spend_leaf_adapter`**
apex already, in-AIR: (a) connects `merkle_root` to a committed turn root (closes #15), (b) recomputes
`value_binding` and binds it to the leaf value under Poseidon2 collision-resistance + enforces
`Σ value == Σ out` (closes #16), (c) does the conservation in-AIR over Poseidon2 (enables the #17-B cut
to a PQ gate). So **routing the deployed single-transfer path through that apex** — as a degenerate
1-leg ring — closes all three at once, on Poseidon2 (PQ), and retires the Rust-authored AIR.

## Options

| Option | What it does | Cost | Closes |
|---|---|---|---|
| **A — route through the ring-clearing apex** (my strategic rec) | deployed transfer becomes a 1-leg case of the built ring-clearing AIR; Poseidon2-authoritative; merkle_root pinned to the committed accumulator; conservation in-AIR | **VK-affecting rewrite** away from standalone `verify_stark_side` (changes the shielded vk_hash); a real subsystem project; inherits 2 NAMED residuals ↓ | #15, #16, #17 |
| **B — honesty downgrade + defer** | correct the overstated #17 comments to match reality (Ristretto is the real gate); leave #15/#16 for later | ~zero code, ~zero risk; **but the theft seam #15 stays open** on the prover path | #17 (the *claim*), nothing structural |
| **C — fence shielded** | mark it explicitly deferred; lean on the fail-closed verify-only path; spend effort on felt-width E2 instead | zero; #15/#16 stay open on the prover path but are *documented* fenced | nothing structural |

**Named residuals of Option A (so it's not a false "done"):** `pedTwoGen` in the apex is an *abstraction*
of Ristretto, not the real curve (a research residual already flagged in `nleg_air.rs`); and BabyBear's
~31-bit field caps a conserving sum near `2^30/N`, so **large-amount range** needs an in-AIR Bulletproof
replacement. Option A closes the seams but leaves those two as the next honest frontier.

## What I'd do

- **Now, unconditionally: Option B's honesty downgrade.** The tree should not claim a PQ posture it
  lacks. Zero risk. (I can land this immediately.)
- **Then, your call: Option A as a project, or Option C fence.** If shielded is a near-term product
  priority, A is the right, coherent fix and I'll scope + drive it (it reuses the apex, so it's real
  but not from-scratch). If shielded is *not* near-term, fence it (C) — it's fail-closed off the prover
  path, and the felt-width E2 batch is higher marginal value right now.

**My honest lean:** B now + **C (fence) for the near term**, revisiting A when shielded becomes a
product priority — because the theft seam is real but *prover-path-only / not light-client*, the E2
felt-width widenings are cheaper wins, and A is a genuine subsystem project that deserves to be
scheduled deliberately, not squeezed in. But if you want the shielded pool *right*, A is the path and
I'll take it.

---

### Decision (ember to fill)

- [ ] **B now** (honesty downgrade) — _recommended, unconditional_
- [ ] then: **A** (redesign via the apex, as a scheduled project) — OR — **C** (fence, revisit later)
- notes:
