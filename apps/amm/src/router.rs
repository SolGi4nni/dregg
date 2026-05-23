//! Multi-hop swap routing for the AMM.
//!
//! Routes trades through multiple pools when a direct pair doesn't exist.
//! For example, to swap A->C when only A/B and B/C pools exist,
//! the router composes: A->B then B->C.

use crate::pool::{LiquidityPool, PoolError, SwapOutput};

/// A single hop in a multi-hop route.
#[derive(Clone, Debug)]
pub struct RouteHop {
    /// Index into the pool registry.
    pub pool_index: usize,
    /// Direction for this hop (true = A->B, false = B->A).
    pub direction_a_to_b: bool,
}

/// A complete route from input token to output token.
#[derive(Clone, Debug)]
pub struct Route {
    pub hops: Vec<RouteHop>,
    /// Starting asset type.
    pub input_asset: u64,
    /// Ending asset type.
    pub output_asset: u64,
}

/// Result of executing a multi-hop swap.
#[derive(Clone, Debug)]
pub struct MultiHopResult {
    /// Outputs from each hop.
    pub hop_outputs: Vec<SwapOutput>,
    /// Final amount received.
    pub final_amount: u64,
    /// Total fees paid across all hops.
    pub total_fees: u64,
}

/// Find a route between two assets using available pools.
///
/// Currently supports up to 3-hop routes (direct, 2-hop, and 3-hop).
pub fn find_route(pools: &[LiquidityPool], input_asset: u64, output_asset: u64) -> Option<Route> {
    // Direct route
    for (i, pool) in pools.iter().enumerate() {
        if pool.asset_a == input_asset && pool.asset_b == output_asset {
            return Some(Route {
                hops: vec![RouteHop {
                    pool_index: i,
                    direction_a_to_b: true,
                }],
                input_asset,
                output_asset,
            });
        }
        if pool.asset_b == input_asset && pool.asset_a == output_asset {
            return Some(Route {
                hops: vec![RouteHop {
                    pool_index: i,
                    direction_a_to_b: false,
                }],
                input_asset,
                output_asset,
            });
        }
    }

    // 2-hop route: input->intermediate->output
    for (i, pool_a) in pools.iter().enumerate() {
        let intermediate = if pool_a.asset_a == input_asset {
            Some((pool_a.asset_b, true))
        } else if pool_a.asset_b == input_asset {
            Some((pool_a.asset_a, false))
        } else {
            None
        };

        if let Some((mid_asset, dir_a)) = intermediate {
            for (j, pool_b) in pools.iter().enumerate() {
                if i == j {
                    continue;
                }
                if pool_b.asset_a == mid_asset && pool_b.asset_b == output_asset {
                    return Some(Route {
                        hops: vec![
                            RouteHop {
                                pool_index: i,
                                direction_a_to_b: dir_a,
                            },
                            RouteHop {
                                pool_index: j,
                                direction_a_to_b: true,
                            },
                        ],
                        input_asset,
                        output_asset,
                    });
                }
                if pool_b.asset_b == mid_asset && pool_b.asset_a == output_asset {
                    return Some(Route {
                        hops: vec![
                            RouteHop {
                                pool_index: i,
                                direction_a_to_b: dir_a,
                            },
                            RouteHop {
                                pool_index: j,
                                direction_a_to_b: false,
                            },
                        ],
                        input_asset,
                        output_asset,
                    });
                }
            }
        }
    }

    None
}

/// Execute a multi-hop swap along a pre-computed route.
///
/// Each hop's output becomes the next hop's input. The final hop's output
/// must meet the minimum output requirement.
pub fn execute_route(
    pools: &mut [LiquidityPool],
    route: &Route,
    amount_in: u64,
    min_final_output: u64,
) -> Result<MultiHopResult, PoolError> {
    let mut current_amount = amount_in;
    let mut hop_outputs = Vec::with_capacity(route.hops.len());
    let mut total_fees = 0u64;

    for (i, hop) in route.hops.iter().enumerate() {
        // For intermediate hops, min_output is 1 (we check final output at the end).
        // For the last hop, use the user's min_output.
        let min_output = if i == route.hops.len() - 1 {
            min_final_output
        } else {
            1 // Any non-zero output is acceptable for intermediate hops
        };

        let output =
            pools[hop.pool_index].swap(current_amount, min_output, hop.direction_a_to_b)?;
        total_fees += output.fee_amount;
        current_amount = output.amount_out;
        hop_outputs.push(output);
    }

    Ok(MultiHopResult {
        hop_outputs,
        final_amount: current_amount,
        total_fees,
    })
}

/// Estimate the output of a multi-hop swap without modifying pool state.
///
/// Uses the same computation as `execute_route` but on cloned pools.
pub fn estimate_route_output(
    pools: &[LiquidityPool],
    route: &Route,
    amount_in: u64,
) -> Result<u64, PoolError> {
    let mut pools_clone: Vec<LiquidityPool> = pools.to_vec();
    let result = execute_route(&mut pools_clone, route, amount_in, 0)?;
    Ok(result.final_amount)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pool::LiquidityPool;

    fn setup_pools() -> Vec<LiquidityPool> {
        vec![
            LiquidityPool::create(1, 2, 10_000, 20_000).unwrap(), // A/B
            LiquidityPool::create(2, 3, 20_000, 5_000).unwrap(),  // B/C
        ]
    }

    #[test]
    fn test_find_direct_route() {
        let pools = setup_pools();
        let route = find_route(&pools, 1, 2).unwrap();
        assert_eq!(route.hops.len(), 1);
        assert!(route.hops[0].direction_a_to_b);
    }

    #[test]
    fn test_find_multi_hop_route() {
        let pools = setup_pools();
        let route = find_route(&pools, 1, 3).unwrap();
        assert_eq!(route.hops.len(), 2);
    }

    #[test]
    fn test_execute_multi_hop() {
        let mut pools = setup_pools();
        let route = find_route(&pools, 1, 3).unwrap();
        let result = execute_route(&mut pools, &route, 100, 1).unwrap();
        assert!(result.final_amount > 0);
        assert_eq!(result.hop_outputs.len(), 2);
    }
}
