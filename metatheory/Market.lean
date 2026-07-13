/-
# Market — DrEX (Dragon's Egg Exchange): the Lean-first economic-refinement tower.

The multilateral MARKET layer over `Dregg2.Intent` — dregg-native DeFi proven sound in Lean.
Rung 1 = execution soundness: the book-allocation clearing (conserves per-asset + fair,
`Market/Clearing.lean`) plus the fairness half over the solver's actual cycles (every declared
limit respected, `Market/Fairness.lean`), composing with `Dregg2/Intent/Ring.lean`'s already-
proven conservation + atomicity. `Market/Clearing.lean`'s design header states the full DrEX
ladder (rung 2: order-book aggregation soundness; rung 3: shielded clearing + the custom
private-matching ZKP; rung 4: cross-chain proof-settlement).
-/
import Market.Clearing
import Market.Fairness
import Market.Aggregation
import Market.Priced
