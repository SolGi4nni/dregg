# Circuit brief: compose the AMM pool leg into Cert-F batch clearing (+ close the binder)

*A precise, routable ask for the Cert-F / circuit lane (Lean-authored AIR — NOT hand-written).
Written 2026-07-19 by the fair-market-verification lane, grounded in the code below. Two changes
turn the existing pieces into a proven **coin/stock batch-cleared market**: (1) the pool leg inside
Cert-F clearing, (2) the clearing tuple inside the proof's public statement (the binder-closer).
Both are circuit/statement changes, deliberate, ember/circuit-lane-gated — surfaced as debt, not
fired from thin context.*

## What already exists (grounded)

- **`Market/CertF.lean`** — the verify-not-find clearing keystone. Clears the trade *graph*:
  `maximize wᵀf s.t. A·f = 0, 0 ≤ f ≤ c` with a primal-dual certificate
  (`A f=0, 0≤f≤c, s≥0, Aᵀπ+s≥w, cᵀs−wᵀf ≤ ε`), `certifies_epsilon_optimal` the keystone. `A` is
  the PUBLIC incidence matrix of the trade graph. **No pool leg** — it's order-flow circulation only.
- **`Market/DarkAmmPrivateSwap.lean`** + `DarkAmmPrivateDescriptor.lean` + `circuit-prove/dark_amm_private.rs`
  (630 lines, new) — a Lean-authored, in-circuit, **single** hidden-reserve constant-product step:
  `x' = x+dx, y' = y−dy, x'·y' = k` (only `k, old_root, new_root` public; reserves/amounts witness;
  proven through `HidingFriPcs`; emit-sound). Honest boundary (its own header): pure integer semantic
  relation — not yet BFV same-opening, threshold custody, or a state-cell weld; **single swap, not batch.**
- **`chain/contracts/launchpad/DreggProofAttestor.sol`** — the on-chain proof arm. Its named TRUSTED
  residual: *"that the bound dregg transition IS this launch's clearing. The binder asserts it; the
  circuit does not carry it. CLOSING this needs the clearing tuple committed INSIDE the proof's public
  statement."*
- Honest floor (FRI wave-2, machine-checked): the deployed wrap is **~51-bit-sound** (ε_C at |D⁰|=2²²,
  field-bound ~124); real lever = extension degree (deep, ember-gated). Everything below inherits this.

## Change 1 — the pool as a Cert-F graph node (the batch × pool compose)

**The seam:** Cert-F already clears a *graph* circulation `A·f=0`. A constant-product pool is just a
special **node** in that graph whose two incident edges (coin-leg, stock-leg) are coupled by the AMM
relation. So the compose is: **add the pool as a node in the trade graph, and pin its net flow to the
`DarkAmmPrivateSwap` relation, evaluated at the batch's uniform clearing price `p*`.**

Precisely, extend the Cert-F descriptor so that for the pool node with pre-reserves `(Rt, Rq)`, `k=Rt·Rq`:
- the pool's net token flow `Δt` (its incidence-row contribution to `A·f=0`) equals the batch's net
  order imbalance (already conserved by `A·f=0` — this is automatic once the pool is a node);
- the **price-taker pin (sqrt-free, integer):** `p* · (Rt ∓ Δt)² = k` (∓ = net-buy/net-sell), i.e. the
  pool sold exactly to bring its curve-marginal to `p*` — the same `g(p*)` the Solidity verifier checks
  (`CLEARING-FUNCTION-SPEC.md` check 4). This is the `DarkAmmPrivateSwap` `x'·y'` relation specialized:
  the pool trades AT the uniform price, so its quote leg is `p*·Δt` (not the curve integral);
- the **LVR-capture / solvency:** the post-reserve product `k' = (Rt∓Δt)(Rq±p*Δt) ≥ k` (k non-decreasing
  — the pool ends richer; this is the theorem that makes it strictly better than a continuous AMM), and
  reserves ≥ disclosed floors.

**What to prove (Lean, over the emitted AIR):** the composed clearing is still `certifies_epsilon_optimal`
(the pool node doesn't break the duality argument — it's a node with a convex feasible region), AND the
new pool-pin gates vanish exactly iff the price-taker + LVR-capture relations hold. Net theorem: *an
accepted composed clearing is uniform-price, conserving (incl. the pool leg), and pool-solvent-and-
LP-positive* — the batch-cleared coin/stock market's fairness, in-circuit.

**Honest scope:** start PUBLIC-reserve (the pool node's `(Rt,Rq)` public — the coin/stock LP case, which
is what the product needs). The HIDDEN-reserve dark pool (`dark_amm_private`) composes the same way but
adds the ct-mul / threshold-open carrier — a later rung. Single-batch first (the block IS the batch),
then N-batch is the existing scaling axis (market4 → parameterized).

## Change 2 — the clearing tuple in the public statement (the binder-closer)

**The gap:** `DreggProofAttestor`'s binder asserts "this proof = this launch's clearing"; the circuit
doesn't carry it. **Close it by committing the clearing tuple `(launch_id, p*, book_commit, Δt)` inside
the proof's public statement** — either as new statement lanes in the gnark `SettlementCircuit`, or a
Poseidon2 inclusion of the tuple under `final_root` verified on-chain. Then the on-chain attestor checks
the presented `(launch_id, p*, …)` against the statement, and the binder becomes **correct-by-proof, not
trusted** — a corrupt binder can't even mislink (today it can only stall). This retires the one named
TRUSTED residual in the attestor.

**Interaction with Change 1:** once the pool is a Cert-F node, `p*` and `Δt` are outputs of the composed
clearing — so committing `(launch_id, p*, book_commit, Δt)` in the statement is exactly what the on-chain
contract (Track B: Verifereum-proven) then verifies + binds + settles against. The three tracks meet here.

## Grading (stays honest)

- Change 1 = the coin/stock market's fairness proven *in-circuit* (was hand-written Solidity — this
  retires that duplication/substrate-drift). Inherits the ~51-bit FRI floor.
- Change 2 = retires the trusted binder (the attestor's whole named residual).
- Neither raises the FRI floor (extension-degree, separate, ember-gated). Neither claims BFV/threshold
  custody (the hidden-reserve dark rung).

## Routing

For the Cert-F / circuit lane (codex's wheelhouse — QP binding, dark_amm_private, FRI honesty are theirs
and active). This brief is the coin/stock-specific ask that composes their pieces; the on-chain half
(Track B) and the product (Track C) proceed in parallel and meet at the statement tuple.
