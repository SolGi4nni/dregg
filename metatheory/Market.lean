/-
# Market — DrEX (Dragon's Egg Exchange): the Lean-first economic-refinement tower.

The multilateral MARKET layer over `Dregg2.Intent` — dregg-native DeFi proven sound in Lean.
Rung 1 = execution soundness: the book-allocation clearing (conserves per-asset + fair,
`Market/Clearing.lean`) plus the fairness half over the solver's actual cycles (every declared
limit respected, `Market/Fairness.lean`), composing with `Dregg2/Intent/Ring.lean`'s already-
proven conservation + atomicity. `Market/Clearing.lean`'s design header states the full DrEX
ladder (rung 2: order-book aggregation soundness; rung 3: shielded clearing + the custom
private-matching ZKP; rung 4: cross-chain proof-settlement).

Rung 3's SPEC is landed in `Market/ShieldedClearing.lean` (the marquee, private matching):
`shielded_ring_clears` — a shielded ring whose legs are shielded spends clears CONSERVING (per
asset, real ledger) + FAIR (every committed limit respected) + PRIVATE/NO-DOUBLE-SPEND (each leg a
fresh member spend, owner/value hidden), composing the shielded-spend leaf refinement + the ring +
the homomorphic hidden-value conservation (`shielded_ring_value_conserves_hidden`: the Pedersen
excess is zero over the commitments alone). The matcher clears the COMMITTED claims and settles by
spending nullifiers — deleting the `trustless.rs` DECRYPT committee. The circuit fold (N
shielded-spend leaves → a ring-clearing apex) is the NAMED finishing step.
-/
import Market.Clearing
import Market.Fairness
import Market.Aggregation
import Market.Priced
import Market.Optimality
import Market.Liquidity
import Market.LedgerRealization
import Market.CrossMargin
import Market.Lending
import Market.ShieldedClearing
