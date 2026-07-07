use dregg_dsl::{dregg_caveat, dregg_effect};

pub mod dregg_definitions;

// --- Phase 1 caveats (preserved) ---

#[dregg_caveat]
fn not_after(token_expiry: u64, current_time: u64) {
    require!(current_time <= token_expiry);
}

#[dregg_caveat]
fn minimum_balance(balance: u64, threshold: u64) {
    require!(balance >= threshold);
}

#[dregg_caveat]
fn exact_match(expected: u64, actual: u64) {
    require!(expected == actual);
}

#[dregg_caveat]
fn different_parties(sender: u64, receiver: u64) {
    require!(sender != receiver);
}

// --- Phase 2: Multi-constraint composition ---

#[dregg_caveat]
fn compound_check(balance: u64, threshold: u64, sender: u64, receiver: u64) {
    require!(balance >= threshold);
    require!(sender != receiver);
}

// --- Phase 2: Set membership ---

#[dregg_caveat]
fn service_scope(allowed_services: &std::collections::HashSet<u64>, requested: u64) {
    require!(allowed_services.contains(requested));
}

// --- Phase 2: Effects with mutation ---

// DSL surface: modeled transfer direction; variants are only constructed in #[cfg(test)] arms.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    Outgoing,
    Incoming,
}

#[dregg_effect]
fn transfer(balance: &mut u64, amount: u64, direction: Direction) {
    match direction {
        Direction::Outgoing => {
            require!(*balance >= amount);
            *balance = *balance - amount;
        }
        Direction::Incoming => {
            *balance = *balance + amount;
        }
    }
}

// --- Phase 2: Effect with permission ---

#[dregg_effect(requires = "Send")]
fn guarded_transfer(balance: &mut u64, amount: u64) {
    require!(*balance >= amount);
    *balance = *balance - amount;
}

// --- Phase 2: Simple effect (no match) ---

#[dregg_effect]
fn decrement(counter: &mut u64, step: u64) {
    require!(*counter >= step);
    *counter = *counter - step;
}
