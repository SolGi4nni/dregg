//! Trading demo: place orders, execute trades, view book state.
//!
//! Demonstrates the orderbook matching engine with various order types.

use pyana_orderbook::{Order, OrderType, OrderbookEngine, Side, TimeInForce, TradingPair};
use pyana_types::CellId;

fn main() {
    println!("=== Pyana Orderbook Trading Demo ===\n");

    let pair = TradingPair::new("ETH", "USDC");
    let mut engine = OrderbookEngine::new(pair);

    let alice = CellId([1u8; 32]);
    let bob = CellId([2u8; 32]);
    let charlie = CellId([3u8; 32]);

    // Alice places several sell limit orders.
    println!("Alice places sells:");
    for (i, (price, amount)) in [(2000, 10), (2010, 15), (2020, 20)].iter().enumerate() {
        let order = Order::new(
            alice,
            OrderType::Limit {
                price: *price,
                amount: *amount,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            i as u64,
            1000 + i as u64,
        );
        engine.submit_order(order).unwrap();
        println!("  Sell {} @ {}", amount, price);
    }

    // Bob places buy limit orders.
    println!("\nBob places buys:");
    for (i, (price, amount)) in [(1990, 5), (1980, 10)].iter().enumerate() {
        let order = Order::new(
            bob,
            OrderType::Limit {
                price: *price,
                amount: *amount,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            i as u64,
            2000 + i as u64,
        );
        engine.submit_order(order).unwrap();
        println!("  Buy {} @ {}", amount, price);
    }

    println!("\n--- Book State ---");
    println!("Best bid: {:?}", engine.book.best_bid());
    println!("Best ask: {:?}", engine.book.best_ask());
    println!("Spread:   {:?}", engine.book.spread());
    println!("Orders:   {}", engine.book.order_count());

    // Charlie places a market buy that crosses the spread.
    println!("\n--- Charlie places a market buy for 25 ETH ---");
    let market_buy = Order::new(
        charlie,
        OrderType::Market {
            amount: 25,
            side: Side::Buy,
            slippage_bps: 200, // 2% slippage allowed
        },
        0,
        3000,
    );

    let result = engine.submit_order(market_buy).unwrap();
    println!("Fully filled: {}", result.fully_filled);
    println!("Total filled: {}", result.total_filled);
    println!("Fills:");
    for fill in &result.fills {
        println!(
            "  {} @ {} (maker: {:02x}{:02x}...)",
            fill.amount,
            fill.price,
            fill.maker.as_bytes()[0],
            fill.maker.as_bytes()[1]
        );
    }

    println!("\n--- Book State After Trade ---");
    println!("Best bid: {:?}", engine.book.best_bid());
    println!("Best ask: {:?}", engine.book.best_ask());
    println!("Spread:   {:?}", engine.book.spread());
    println!("Orders:   {}", engine.book.order_count());

    // Demonstrate cancellation.
    println!("\n--- Bob cancels his remaining buy order ---");
    let bob_orders: Vec<_> = [0u64, 1]
        .iter()
        .filter_map(|nonce| {
            let order = Order::new(
                bob,
                OrderType::Limit {
                    price: if *nonce == 0 { 1990 } else { 1980 },
                    amount: if *nonce == 0 { 5 } else { 10 },
                    side: Side::Buy,
                    time_in_force: TimeInForce::GTC,
                },
                *nonce,
                2000 + nonce,
            );
            if engine.book.contains_order(&order.id) {
                Some(order.id)
            } else {
                None
            }
        })
        .collect();

    for id in bob_orders {
        match engine.cancel_order(&id, &bob) {
            Ok(cancelled) => println!(
                "  Cancelled order (remaining: {})",
                cancelled.remaining_amount
            ),
            Err(e) => println!("  Cancel failed: {}", e),
        }
    }

    println!("\nFinal order count: {}", engine.book.order_count());
    println!("\n=== Demo Complete ===");
}
