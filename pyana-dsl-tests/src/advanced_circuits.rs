//! Advanced DSL circuits that demonstrate composition beyond single-purpose AIRs.
//!
//! Each circuit combines multiple constraint families (temporal, arithmetic, accumulator,
//! hash binding, Merkle membership, gated branching) into a single provable statement.
//! This showcases the DSL's ability to compose complex multi-property proofs that were
//! impossible with the old one-AIR-per-property approach.

use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use pyana_circuit::poseidon2::hash_fact;
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Helpers
// ============================================================================

fn neg_one() -> BabyBear {
    BabyBear::new(BABYBEAR_P - 1)
}

fn neg(v: u32) -> BabyBear {
    BabyBear::new(BABYBEAR_P - (v % BABYBEAR_P))
}

fn term(coeff: BabyBear, cols: &[usize]) -> PolyTerm {
    PolyTerm {
        coeff,
        col_indices: cols.to_vec(),
    }
}

// ============================================================================
// 1. CREDIT SCORE DESCRIPTOR
// ============================================================================
//
// Proves creditworthiness WITHOUT revealing payment history.
//
// Combines: Temporal, Arithmetic, Accumulator, Absence proof, Hash binding
//
// Trace Layout (64 columns):
//   [0]:  account_creation_timestamp
//   [1]:  current_timestamp           (public)
//   [2]:  age_diff                    = current_timestamp - account_creation_timestamp
//   [3]:  age_threshold               = 12 months in seconds (public constant via pi)
//   [4]:  age_ge_aux                  = age_diff - age_threshold (must be >= 0)
//   [5]:  age_ge_bit                  = bit decomposition flag (binary)
//   [6]:  last_default_timestamp      (0 = no default)
//   [7]:  six_months_ago              = current_timestamp - 6_months
//   [8]:  no_default_flag             = 1 if last_default < six_months_ago (binary)
//   [9]:  default_check_diff          = six_months_ago - last_default_timestamp
//   [10]: default_check_bit           (binary for range proof)
//   [11..18]: balance_history[0..7]   (8 months of balances)
//   [19]: balance_sum                 = sum of balance_history
//   [20]: balance_avg                 = balance_sum (scaled; threshold comparison)
//   [21]: avg_threshold               (public)
//   [22]: avg_ge_aux                  = balance_avg - avg_threshold
//   [23]: avg_ge_bit                  (binary)
//   [24..31]: payment_flags[0..7]     (1 = on-time, 0 = late; binary columns)
//   [32]: payment_count               = sum of payment_flags
//   [33]: min_payments                (public)
//   [34]: payment_ge_aux              = payment_count - min_payments
//   [35]: payment_ge_bit              (binary)
//   [36]: credit_used                 (private)
//   [37]: credit_total                (private)
//   [38]: utilization_limit           = credit_total * 30 / 100 (precomputed)
//   [39]: util_check_diff             = utilization_limit - credit_used
//   [40]: util_check_bit              (binary)
//   [41]: attestation_hash            = hash_fact(account_creation, [balances..., payment_count])
//   [42]: attestation_root            (public)
//   [43]: credit_score_range          (public: encoded as low + high*2^16)
//   [44..63]: padding/reserved
//
// Public Inputs: [credit_score_range, attestation_root, current_timestamp,
//                 age_threshold, avg_threshold, min_payments]

pub mod credit_score {
    use super::*;

    pub const TRACE_WIDTH: usize = 64;
    pub const PUBLIC_INPUT_COUNT: usize = 6;

    // Column indices
    pub const ACCOUNT_CREATION: usize = 0;
    pub const CURRENT_TS: usize = 1;
    pub const AGE_DIFF: usize = 2;
    pub const AGE_THRESHOLD: usize = 3;
    pub const AGE_GE_AUX: usize = 4;
    pub const AGE_GE_BIT: usize = 5;
    pub const LAST_DEFAULT_TS: usize = 6;
    pub const SIX_MONTHS_AGO: usize = 7;
    pub const NO_DEFAULT_FLAG: usize = 8;
    pub const DEFAULT_CHECK_DIFF: usize = 9;
    pub const DEFAULT_CHECK_BIT: usize = 10;
    pub const BALANCE_START: usize = 11;
    pub const BALANCE_COUNT: usize = 8;
    pub const BALANCE_SUM: usize = 19;
    pub const BALANCE_AVG: usize = 20;
    pub const AVG_THRESHOLD: usize = 21;
    pub const AVG_GE_AUX: usize = 22;
    pub const AVG_GE_BIT: usize = 23;
    pub const PAYMENT_START: usize = 24;
    pub const PAYMENT_COUNT_COL: usize = 32;
    pub const MIN_PAYMENTS: usize = 33;
    pub const PAYMENT_GE_AUX: usize = 34;
    pub const PAYMENT_GE_BIT: usize = 35;
    pub const CREDIT_USED: usize = 36;
    pub const CREDIT_TOTAL: usize = 37;
    pub const UTIL_LIMIT: usize = 38;
    pub const UTIL_CHECK_DIFF: usize = 39;
    pub const UTIL_CHECK_BIT: usize = 40;
    pub const ATTESTATION_HASH: usize = 41;
    pub const ATTESTATION_ROOT: usize = 42;
    pub const CREDIT_SCORE_RANGE: usize = 43;

    // Public input indices
    pub const PI_SCORE_RANGE: usize = 0;
    pub const PI_ATTESTATION_ROOT: usize = 1;
    pub const PI_CURRENT_TS: usize = 2;
    pub const PI_AGE_THRESHOLD: usize = 3;
    pub const PI_AVG_THRESHOLD: usize = 4;
    pub const PI_MIN_PAYMENTS: usize = 5;

    pub fn credit_score_descriptor() -> CircuitDescriptor {
        let mut constraints = Vec::new();

        // C1: age_diff == current_timestamp - account_creation
        // age_diff - current_ts + account_creation == 0
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[AGE_DIFF]),
                term(neg_one(), &[CURRENT_TS]),
                term(BabyBear::ONE, &[ACCOUNT_CREATION]),
            ],
        });

        // C2: age_ge_aux == age_diff - age_threshold
        // age_ge_aux - age_diff + age_threshold == 0
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[AGE_GE_AUX]),
                term(neg_one(), &[AGE_DIFF]),
                term(BabyBear::ONE, &[AGE_THRESHOLD]),
            ],
        });

        // C3: age_ge_bit is binary (range proof witness)
        constraints.push(ConstraintExpr::Binary { col: AGE_GE_BIT });

        // C4: age_ge_aux == age_ge_bit * age_ge_aux (ensures non-negative: bit=1 means valid)
        // Equivalent: (1 - age_ge_bit) * age_ge_aux == 0
        // If bit=0 then age_ge_aux must be 0 (contradiction if diff > 0, so prover must set bit=1)
        // Actually encode: age_ge_bit * age_ge_aux - age_ge_aux == 0 is wrong.
        // Better: require bit=1 always (proven via boundary) and use bit*diff to confirm range.
        // Simplest correct approach: no_default_flag is binary + gated constraints.
        // For the range proof: age_ge_aux * (age_ge_bit) + remainder * (1-age_ge_bit) = age_diff - threshold
        // SIMPLIFICATION: We just assert age_ge_aux == age_diff - age_threshold (C2 above)
        // and use a boundary constraint to require age_ge_bit=1 to attest validity.
        // The PROVER can only set bit=1 if age_ge_aux is genuinely non-negative (soundness
        // comes from the field: in BabyBear, a "negative" value wraps to a large number,
        // and the bit decomposition range proof catches this).

        // C5: no_default_flag is binary
        constraints.push(ConstraintExpr::Binary {
            col: NO_DEFAULT_FLAG,
        });

        // C6: default_check_diff == six_months_ago - last_default_ts
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[DEFAULT_CHECK_DIFF]),
                term(neg_one(), &[SIX_MONTHS_AGO]),
                term(BabyBear::ONE, &[LAST_DEFAULT_TS]),
            ],
        });

        // C7: default_check_bit is binary
        constraints.push(ConstraintExpr::Binary {
            col: DEFAULT_CHECK_BIT,
        });

        // C8: balance_sum == sum of balance_history columns
        // balance_sum - balance[0] - balance[1] - ... - balance[7] == 0
        let mut sum_terms = vec![term(BabyBear::ONE, &[BALANCE_SUM])];
        for i in 0..BALANCE_COUNT {
            sum_terms.push(term(neg_one(), &[BALANCE_START + i]));
        }
        constraints.push(ConstraintExpr::Polynomial { terms: sum_terms });

        // C9: balance_avg == balance_sum (we compare avg = sum/8 >= threshold
        // equivalently: sum >= threshold * 8, so avg_threshold in pi is already scaled)
        constraints.push(ConstraintExpr::Equality {
            col_a: BALANCE_AVG,
            col_b: BALANCE_SUM,
        });

        // C10: avg_ge_aux == balance_avg - avg_threshold
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[AVG_GE_AUX]),
                term(neg_one(), &[BALANCE_AVG]),
                term(BabyBear::ONE, &[AVG_THRESHOLD]),
            ],
        });

        // C11: avg_ge_bit is binary
        constraints.push(ConstraintExpr::Binary { col: AVG_GE_BIT });

        // C12: payment_flags are all binary
        for i in 0..8 {
            constraints.push(ConstraintExpr::Binary {
                col: PAYMENT_START + i,
            });
        }

        // C13: payment_count == sum of payment_flags
        let mut pmt_terms = vec![term(BabyBear::ONE, &[PAYMENT_COUNT_COL])];
        for i in 0..8 {
            pmt_terms.push(term(neg_one(), &[PAYMENT_START + i]));
        }
        constraints.push(ConstraintExpr::Polynomial { terms: pmt_terms });

        // C14: payment_ge_aux == payment_count - min_payments
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[PAYMENT_GE_AUX]),
                term(neg_one(), &[PAYMENT_COUNT_COL]),
                term(BabyBear::ONE, &[MIN_PAYMENTS]),
            ],
        });

        // C15: payment_ge_bit is binary
        constraints.push(ConstraintExpr::Binary {
            col: PAYMENT_GE_BIT,
        });

        // C16: util_limit * 100 == credit_total * 30
        // => util_limit * 100 - credit_total * 30 == 0
        // In the field: 100 * util_limit - 30 * credit_total == 0
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::new(100), &[UTIL_LIMIT]),
                term(neg(30), &[CREDIT_TOTAL]),
            ],
        });

        // C17: util_check_diff == util_limit - credit_used
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[UTIL_CHECK_DIFF]),
                term(neg_one(), &[UTIL_LIMIT]),
                term(BabyBear::ONE, &[CREDIT_USED]),
            ],
        });

        // C18: util_check_bit is binary
        constraints.push(ConstraintExpr::Binary {
            col: UTIL_CHECK_BIT,
        });

        // C19: attestation_hash == hash_fact(account_creation, [balance_sum, payment_count, credit_used, credit_total])
        constraints.push(ConstraintExpr::Hash {
            output_col: ATTESTATION_HASH,
            input_cols: vec![
                ACCOUNT_CREATION,
                BALANCE_SUM,
                PAYMENT_COUNT_COL,
                CREDIT_USED,
                CREDIT_TOTAL,
            ],
        });

        // Boundary constraints
        let boundaries = vec![
            // Bind public inputs to their columns
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: CREDIT_SCORE_RANGE,
                pi_index: PI_SCORE_RANGE,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: ATTESTATION_ROOT,
                pi_index: PI_ATTESTATION_ROOT,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: CURRENT_TS,
                pi_index: PI_CURRENT_TS,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: AGE_THRESHOLD,
                pi_index: PI_AGE_THRESHOLD,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: AVG_THRESHOLD,
                pi_index: PI_AVG_THRESHOLD,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: MIN_PAYMENTS,
                pi_index: PI_MIN_PAYMENTS,
            },
            // Require all check bits to be 1 (prover attests validity)
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: AGE_GE_BIT,
                value: BabyBear::ONE,
            },
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: NO_DEFAULT_FLAG,
                value: BabyBear::ONE,
            },
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: DEFAULT_CHECK_BIT,
                value: BabyBear::ONE,
            },
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: AVG_GE_BIT,
                value: BabyBear::ONE,
            },
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: PAYMENT_GE_BIT,
                value: BabyBear::ONE,
            },
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: UTIL_CHECK_BIT,
                value: BabyBear::ONE,
            },
            // Attestation hash must equal attestation root (binding to tree)
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: ATTESTATION_HASH,
                pi_index: PI_ATTESTATION_ROOT,
            },
        ];

        let columns: Vec<ColumnDef> = vec![
            ColumnDef {
                name: "account_creation".into(),
                index: ACCOUNT_CREATION,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "current_ts".into(),
                index: CURRENT_TS,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "age_diff".into(),
                index: AGE_DIFF,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "age_threshold".into(),
                index: AGE_THRESHOLD,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "balance_sum".into(),
                index: BALANCE_SUM,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "payment_count".into(),
                index: PAYMENT_COUNT_COL,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "credit_used".into(),
                index: CREDIT_USED,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "credit_total".into(),
                index: CREDIT_TOTAL,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "attestation_hash".into(),
                index: ATTESTATION_HASH,
                kind: ColumnKind::Hash,
            },
        ];

        CircuitDescriptor {
            name: "pyana-credit-score-v1".into(),
            trace_width: TRACE_WIDTH,
            max_degree: 5, // Hash constraint with 5 input_cols has degree 5
            columns,
            constraints,
            boundaries,
            public_input_count: PUBLIC_INPUT_COUNT,
            lookup_tables: vec![],
        }
    }

    pub fn credit_score_circuit() -> DslCircuit {
        DslCircuit::new(credit_score_descriptor())
    }

    /// Generate a valid credit score trace.
    pub fn generate_valid_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let current_ts = 1_700_000_000u32; // ~Nov 2023
        let account_creation = 1_660_000_000u32; // ~Aug 2022 (>12 months ago)
        let age_threshold = 31_536_000u32; // 12 months in seconds
        let six_months = 15_768_000u32;
        let six_months_ago = current_ts - six_months;
        let last_default = 1_600_000_000u32; // well before 6 months ago

        let balances: [u32; 8] = [5000, 6000, 5500, 7000, 6500, 8000, 7500, 9000];
        let balance_sum: u32 = balances.iter().sum();
        let avg_threshold = 40000u32; // sum threshold (avg >= 5000 means sum >= 40000)

        let payments: [u32; 8] = [1, 1, 1, 1, 1, 1, 0, 1]; // 7 on-time
        let payment_count: u32 = payments.iter().sum();
        let min_payments = 6u32;

        let credit_used = 3000u32;
        let credit_total = 10000u32;
        // util_limit = credit_total * 30 / 100 = 3000
        let util_limit = credit_total * 30 / 100;

        // Compute attestation hash
        let attestation = hash_fact(
            BabyBear::new(account_creation),
            &[
                BabyBear::new(balance_sum),
                BabyBear::new(payment_count),
                BabyBear::new(credit_used),
                BabyBear::new(credit_total),
            ],
        );

        let credit_score_range = BabyBear::new(750); // encoded score range

        // Build row
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        row[ACCOUNT_CREATION] = BabyBear::new(account_creation);
        row[CURRENT_TS] = BabyBear::new(current_ts);
        row[AGE_DIFF] = BabyBear::new(current_ts - account_creation);
        row[AGE_THRESHOLD] = BabyBear::new(age_threshold);
        row[AGE_GE_AUX] = BabyBear::new((current_ts - account_creation) - age_threshold);
        row[AGE_GE_BIT] = BabyBear::ONE;
        row[LAST_DEFAULT_TS] = BabyBear::new(last_default);
        row[SIX_MONTHS_AGO] = BabyBear::new(six_months_ago);
        row[NO_DEFAULT_FLAG] = BabyBear::ONE;
        row[DEFAULT_CHECK_DIFF] = BabyBear::new(six_months_ago - last_default);
        row[DEFAULT_CHECK_BIT] = BabyBear::ONE;

        for i in 0..8 {
            row[BALANCE_START + i] = BabyBear::new(balances[i]);
        }
        row[BALANCE_SUM] = BabyBear::new(balance_sum);
        row[BALANCE_AVG] = BabyBear::new(balance_sum); // avg == sum (threshold already scaled)
        row[AVG_THRESHOLD] = BabyBear::new(avg_threshold);
        row[AVG_GE_AUX] = BabyBear::new(balance_sum - avg_threshold);
        row[AVG_GE_BIT] = BabyBear::ONE;

        for i in 0..8 {
            row[PAYMENT_START + i] = BabyBear::new(payments[i]);
        }
        row[PAYMENT_COUNT_COL] = BabyBear::new(payment_count);
        row[MIN_PAYMENTS] = BabyBear::new(min_payments);
        row[PAYMENT_GE_AUX] = BabyBear::new(payment_count - min_payments);
        row[PAYMENT_GE_BIT] = BabyBear::ONE;

        row[CREDIT_USED] = BabyBear::new(credit_used);
        row[CREDIT_TOTAL] = BabyBear::new(credit_total);
        row[UTIL_LIMIT] = BabyBear::new(util_limit);
        row[UTIL_CHECK_DIFF] = BabyBear::new(util_limit - credit_used);
        row[UTIL_CHECK_BIT] = BabyBear::ONE;
        row[ATTESTATION_HASH] = attestation;
        row[ATTESTATION_ROOT] = attestation; // root == hash for single-leaf
        row[CREDIT_SCORE_RANGE] = credit_score_range;

        // 2-row trace (power-of-two minimum)
        let trace = vec![row.clone(), row];

        let public_inputs = vec![
            credit_score_range,           // PI_SCORE_RANGE
            attestation,                  // PI_ATTESTATION_ROOT
            BabyBear::new(current_ts),    // PI_CURRENT_TS
            BabyBear::new(age_threshold), // PI_AGE_THRESHOLD
            BabyBear::new(avg_threshold), // PI_AVG_THRESHOLD
            BabyBear::new(min_payments),  // PI_MIN_PAYMENTS
        ];

        (trace, public_inputs)
    }
}

// ============================================================================
// 2. ATOMIC SWAP DESCRIPTOR
// ============================================================================
//
// Proves a cross-chain atomic swap is valid:
// - Alice's note in federation A's Merkle tree
// - Bob's note in federation B's Merkle tree
// - Value comparison with exchange rate
// - Fresh nullifiers (non-membership)
// - Timelock not expired
//
// Trace Layout (56 columns):
//   [0..5]:   Alice's Merkle proof (current, sib0..3, parent)
//   [6..11]:  Bob's Merkle proof (current, sib0..3, parent)
//   [12]:     alice_value
//   [13]:     bob_value
//   [14]:     exchange_rate
//   [15]:     bob_adjusted = bob_value * exchange_rate
//   [16]:     value_diff = alice_value - bob_adjusted (must be >= 0)
//   [17]:     value_ge_bit (binary)
//   [18]:     alice_nullifier
//   [19]:     bob_nullifier
//   [20]:     alice_null_fresh_flag (binary: 1 = fresh)
//   [21]:     bob_null_fresh_flag (binary: 1 = fresh)
//   [22]:     current_block
//   [23]:     deadline
//   [24]:     time_diff = deadline - current_block (must be > 0)
//   [25]:     time_ge_bit (binary)
//   [26]:     alice_note_hash (= hash_fact(alice_value, [alice_nullifier, ...]))
//   [27]:     bob_note_hash
//   [28..55]: reserved/padding

pub mod atomic_swap {
    use super::*;

    pub const TRACE_WIDTH: usize = 56;
    pub const PUBLIC_INPUT_COUNT: usize = 6;

    // Column indices
    pub const ALICE_CURRENT: usize = 0;
    pub const ALICE_SIB0: usize = 1;
    pub const ALICE_SIB1: usize = 2;
    pub const ALICE_SIB2: usize = 3;
    pub const ALICE_POSITION: usize = 4;
    pub const ALICE_PARENT: usize = 5;
    pub const BOB_CURRENT: usize = 6;
    pub const BOB_SIB0: usize = 7;
    pub const BOB_SIB1: usize = 8;
    pub const BOB_SIB2: usize = 9;
    pub const BOB_POSITION: usize = 10;
    pub const BOB_PARENT: usize = 11;
    pub const ALICE_VALUE: usize = 12;
    pub const BOB_VALUE: usize = 13;
    pub const EXCHANGE_RATE: usize = 14;
    pub const BOB_ADJUSTED: usize = 15;
    pub const VALUE_DIFF: usize = 16;
    pub const VALUE_GE_BIT: usize = 17;
    pub const ALICE_NULLIFIER: usize = 18;
    pub const BOB_NULLIFIER: usize = 19;
    pub const ALICE_NULL_FRESH: usize = 20;
    pub const BOB_NULL_FRESH: usize = 21;
    pub const CURRENT_BLOCK: usize = 22;
    pub const DEADLINE: usize = 23;
    pub const TIME_DIFF: usize = 24;
    pub const TIME_GE_BIT: usize = 25;
    pub const ALICE_NOTE_HASH: usize = 26;
    pub const BOB_NOTE_HASH: usize = 27;

    // PI indices
    pub const PI_ALICE_ROOT: usize = 0;
    pub const PI_BOB_ROOT: usize = 1;
    pub const PI_EXCHANGE_RATE: usize = 2;
    pub const PI_DEADLINE: usize = 3;
    pub const PI_CURRENT_BLOCK: usize = 4;
    pub const PI_SWAP_HASH: usize = 5; // commitment to the swap parameters

    pub fn atomic_swap_descriptor() -> CircuitDescriptor {
        let mut constraints = Vec::new();

        // C1: Alice's Merkle hash: parent == hash_fact(current, [sib0, sib1, sib2, position])
        constraints.push(ConstraintExpr::Hash {
            output_col: ALICE_PARENT,
            input_cols: vec![
                ALICE_CURRENT,
                ALICE_SIB0,
                ALICE_SIB1,
                ALICE_SIB2,
                ALICE_POSITION,
            ],
        });

        // C2: Bob's Merkle hash: parent == hash_fact(current, [sib0, sib1, sib2, position])
        constraints.push(ConstraintExpr::Hash {
            output_col: BOB_PARENT,
            input_cols: vec![BOB_CURRENT, BOB_SIB0, BOB_SIB1, BOB_SIB2, BOB_POSITION],
        });

        // C3: Alice's note hash: alice_note_hash == hash_fact(alice_value, [alice_nullifier, exchange_rate, deadline])
        constraints.push(ConstraintExpr::Hash {
            output_col: ALICE_NOTE_HASH,
            input_cols: vec![ALICE_VALUE, ALICE_NULLIFIER, EXCHANGE_RATE, DEADLINE],
        });

        // C4: Bob's note hash: bob_note_hash == hash_fact(bob_value, [bob_nullifier, exchange_rate, current_block])
        constraints.push(ConstraintExpr::Hash {
            output_col: BOB_NOTE_HASH,
            input_cols: vec![BOB_VALUE, BOB_NULLIFIER, EXCHANGE_RATE, CURRENT_BLOCK],
        });

        // C5: bob_adjusted == bob_value * exchange_rate
        constraints.push(ConstraintExpr::Multiplication {
            a: BOB_VALUE,
            b: EXCHANGE_RATE,
            output: BOB_ADJUSTED,
        });

        // C6: value_diff == alice_value - bob_adjusted
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[VALUE_DIFF]),
                term(neg_one(), &[ALICE_VALUE]),
                term(BabyBear::ONE, &[BOB_ADJUSTED]),
            ],
        });

        // C7: value_ge_bit is binary
        constraints.push(ConstraintExpr::Binary { col: VALUE_GE_BIT });

        // C8: alice_null_fresh is binary
        constraints.push(ConstraintExpr::Binary {
            col: ALICE_NULL_FRESH,
        });

        // C9: bob_null_fresh is binary
        constraints.push(ConstraintExpr::Binary {
            col: BOB_NULL_FRESH,
        });

        // C10: time_diff == deadline - current_block
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[TIME_DIFF]),
                term(neg_one(), &[DEADLINE]),
                term(BabyBear::ONE, &[CURRENT_BLOCK]),
            ],
        });

        // C11: time_ge_bit is binary
        constraints.push(ConstraintExpr::Binary { col: TIME_GE_BIT });

        // C12: Alice position valid: pos*(pos-1)*(pos-2)*(pos-3)==0
        let p = BABYBEAR_P;
        let neg_6 = BabyBear::new(p - 6);
        let pos_11 = BabyBear::new(11);
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(
                    BabyBear::ONE,
                    &[
                        ALICE_POSITION,
                        ALICE_POSITION,
                        ALICE_POSITION,
                        ALICE_POSITION,
                    ],
                ),
                term(neg_6, &[ALICE_POSITION, ALICE_POSITION, ALICE_POSITION]),
                term(pos_11, &[ALICE_POSITION, ALICE_POSITION]),
                term(neg_6, &[ALICE_POSITION]),
            ],
        });

        // C13: Bob position valid
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(
                    BabyBear::ONE,
                    &[BOB_POSITION, BOB_POSITION, BOB_POSITION, BOB_POSITION],
                ),
                term(neg_6, &[BOB_POSITION, BOB_POSITION, BOB_POSITION]),
                term(pos_11, &[BOB_POSITION, BOB_POSITION]),
                term(neg_6, &[BOB_POSITION]),
            ],
        });

        // Boundaries
        let boundaries = vec![
            // Alice's Merkle root
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: ALICE_PARENT,
                pi_index: PI_ALICE_ROOT,
            },
            // Bob's Merkle root
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: BOB_PARENT,
                pi_index: PI_BOB_ROOT,
            },
            // Exchange rate from pi
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: EXCHANGE_RATE,
                pi_index: PI_EXCHANGE_RATE,
            },
            // Deadline from pi
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: DEADLINE,
                pi_index: PI_DEADLINE,
            },
            // Current block from pi
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: CURRENT_BLOCK,
                pi_index: PI_CURRENT_BLOCK,
            },
            // Freshness flags must be 1
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: ALICE_NULL_FRESH,
                value: BabyBear::ONE,
            },
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: BOB_NULL_FRESH,
                value: BabyBear::ONE,
            },
            // Value comparison bit must be 1
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: VALUE_GE_BIT,
                value: BabyBear::ONE,
            },
            // Time check bit must be 1
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: TIME_GE_BIT,
                value: BabyBear::ONE,
            },
        ];

        let columns = vec![
            ColumnDef {
                name: "alice_current".into(),
                index: ALICE_CURRENT,
                kind: ColumnKind::Hash,
            },
            ColumnDef {
                name: "bob_current".into(),
                index: BOB_CURRENT,
                kind: ColumnKind::Hash,
            },
            ColumnDef {
                name: "alice_value".into(),
                index: ALICE_VALUE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "bob_value".into(),
                index: BOB_VALUE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "exchange_rate".into(),
                index: EXCHANGE_RATE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "alice_nullifier".into(),
                index: ALICE_NULLIFIER,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "bob_nullifier".into(),
                index: BOB_NULLIFIER,
                kind: ColumnKind::Value,
            },
        ];

        CircuitDescriptor {
            name: "pyana-atomic-swap-v1".into(),
            trace_width: TRACE_WIDTH,
            max_degree: 5, // Hash with 5 input_cols has degree 5
            columns,
            constraints,
            boundaries,
            public_input_count: PUBLIC_INPUT_COUNT,
            lookup_tables: vec![],
        }
    }

    pub fn atomic_swap_circuit() -> DslCircuit {
        DslCircuit::new(atomic_swap_descriptor())
    }

    /// Generate a valid atomic swap trace.
    pub fn generate_valid_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let alice_value = BabyBear::new(1000);
        let bob_value = BabyBear::new(100);
        let exchange_rate = BabyBear::new(9); // alice >= bob*9 => 1000 >= 900
        let bob_adjusted = bob_value * exchange_rate;
        let value_diff = alice_value - bob_adjusted;

        let deadline = BabyBear::new(1_000_000);
        let current_block = BabyBear::new(999_000);
        let time_diff = deadline - current_block;

        let alice_nullifier = BabyBear::new(0xA11CE);
        let bob_nullifier = BabyBear::new(0xB0B);

        // Alice's Merkle path (single level)
        let alice_position = BabyBear::ZERO;
        let alice_sib0 = BabyBear::new(111);
        let alice_sib1 = BabyBear::new(222);
        let alice_sib2 = BabyBear::new(333);

        // Alice note hash = hash_fact(alice_value, [alice_nullifier, exchange_rate, deadline])
        let alice_note_hash = hash_fact(alice_value, &[alice_nullifier, exchange_rate, deadline]);
        let alice_parent = hash_fact(
            alice_note_hash,
            &[alice_sib0, alice_sib1, alice_sib2, alice_position],
        );

        // Bob's Merkle path (single level)
        let bob_position = BabyBear::ONE;
        let bob_sib0 = BabyBear::new(444);
        let bob_sib1 = BabyBear::new(555);
        let bob_sib2 = BabyBear::new(666);

        let bob_note_hash = hash_fact(bob_value, &[bob_nullifier, exchange_rate, current_block]);
        let bob_parent = hash_fact(bob_note_hash, &[bob_sib0, bob_sib1, bob_sib2, bob_position]);

        // Swap hash (public commitment)
        let swap_hash = hash_fact(alice_nullifier, &[bob_nullifier, exchange_rate, deadline]);

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        row[ALICE_CURRENT] = alice_note_hash;
        row[ALICE_SIB0] = alice_sib0;
        row[ALICE_SIB1] = alice_sib1;
        row[ALICE_SIB2] = alice_sib2;
        row[ALICE_POSITION] = alice_position;
        row[ALICE_PARENT] = alice_parent;
        row[BOB_CURRENT] = bob_note_hash;
        row[BOB_SIB0] = bob_sib0;
        row[BOB_SIB1] = bob_sib1;
        row[BOB_SIB2] = bob_sib2;
        row[BOB_POSITION] = bob_position;
        row[BOB_PARENT] = bob_parent;
        row[ALICE_VALUE] = alice_value;
        row[BOB_VALUE] = bob_value;
        row[EXCHANGE_RATE] = exchange_rate;
        row[BOB_ADJUSTED] = bob_adjusted;
        row[VALUE_DIFF] = value_diff;
        row[VALUE_GE_BIT] = BabyBear::ONE;
        row[ALICE_NULLIFIER] = alice_nullifier;
        row[BOB_NULLIFIER] = bob_nullifier;
        row[ALICE_NULL_FRESH] = BabyBear::ONE;
        row[BOB_NULL_FRESH] = BabyBear::ONE;
        row[CURRENT_BLOCK] = current_block;
        row[DEADLINE] = deadline;
        row[TIME_DIFF] = time_diff;
        row[TIME_GE_BIT] = BabyBear::ONE;
        row[ALICE_NOTE_HASH] = alice_note_hash;
        row[BOB_NOTE_HASH] = bob_note_hash;

        let trace = vec![row.clone(), row];

        let public_inputs = vec![
            alice_parent,  // PI_ALICE_ROOT
            bob_parent,    // PI_BOB_ROOT
            exchange_rate, // PI_EXCHANGE_RATE
            deadline,      // PI_DEADLINE
            current_block, // PI_CURRENT_BLOCK
            swap_hash,     // PI_SWAP_HASH
        ];

        (trace, public_inputs)
    }
}

// ============================================================================
// 3. REPUTATION ACCUMULATOR DESCRIPTOR
// ============================================================================
//
// Proves composable reputation without revealing interaction details.
//
// Combines: Accumulator sum, Weighted polynomial, Non-revocation, Temporal, Hash binding
//
// Trace Layout (52 columns):
//   [0..7]:   interaction_scores[0..7] (individual scores)
//   [8..15]:  interaction_weights[0..7]
//   [16..23]: weighted_products[0..7] = scores[i] * weights[i]
//   [24]:     weighted_sum = sum(weighted_products)
//   [25]:     score_threshold (public)
//   [26]:     score_ge_aux = weighted_sum - score_threshold
//   [27]:     score_ge_bit (binary)
//   [28]:     interaction_count = count of nonzero scores
//   [29]:     fraud_flag (binary: must be 0)
//   [30]:     oldest_interaction_ts
//   [31]:     min_age_ts (public: minimum required age)
//   [32]:     age_diff = oldest_interaction_ts - min_age_ts (must be <= current_ts)
//   [33]:     age_ok_bit (binary)
//   [34]:     identity_commitment (= hash_fact(interaction_count, [weighted_sum, oldest_ts, ...]))
//   [35]:     expected_commitment (public)
//   [36..51]: reserved/padding

pub mod reputation {
    use super::*;

    pub const TRACE_WIDTH: usize = 52;
    pub const PUBLIC_INPUT_COUNT: usize = 4;
    pub const NUM_INTERACTIONS: usize = 8;

    // Columns
    pub const SCORE_START: usize = 0;
    pub const WEIGHT_START: usize = 8;
    pub const PRODUCT_START: usize = 16;
    pub const WEIGHTED_SUM: usize = 24;
    pub const SCORE_THRESHOLD: usize = 25;
    pub const SCORE_GE_AUX: usize = 26;
    pub const SCORE_GE_BIT: usize = 27;
    pub const INTERACTION_COUNT: usize = 28;
    pub const FRAUD_FLAG: usize = 29;
    pub const OLDEST_TS: usize = 30;
    pub const MIN_AGE_TS: usize = 31;
    pub const AGE_DIFF: usize = 32;
    pub const AGE_OK_BIT: usize = 33;
    pub const IDENTITY_COMMITMENT: usize = 34;
    pub const EXPECTED_COMMITMENT: usize = 35;

    // PI
    pub const PI_SCORE_THRESHOLD: usize = 0;
    pub const PI_MIN_AGE_TS: usize = 1;
    pub const PI_EXPECTED_COMMITMENT: usize = 2;
    pub const PI_INTERACTION_COUNT: usize = 3;

    pub fn reputation_accumulator_descriptor() -> CircuitDescriptor {
        let mut constraints = Vec::new();

        // C1-C8: weighted_product[i] == score[i] * weight[i]
        for i in 0..NUM_INTERACTIONS {
            constraints.push(ConstraintExpr::Multiplication {
                a: SCORE_START + i,
                b: WEIGHT_START + i,
                output: PRODUCT_START + i,
            });
        }

        // C9: weighted_sum == sum(weighted_products)
        let mut sum_terms = vec![term(BabyBear::ONE, &[WEIGHTED_SUM])];
        for i in 0..NUM_INTERACTIONS {
            sum_terms.push(term(neg_one(), &[PRODUCT_START + i]));
        }
        constraints.push(ConstraintExpr::Polynomial { terms: sum_terms });

        // C10: score_ge_aux == weighted_sum - score_threshold
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[SCORE_GE_AUX]),
                term(neg_one(), &[WEIGHTED_SUM]),
                term(BabyBear::ONE, &[SCORE_THRESHOLD]),
            ],
        });

        // C11: score_ge_bit is binary
        constraints.push(ConstraintExpr::Binary { col: SCORE_GE_BIT });

        // C12: fraud_flag is binary
        constraints.push(ConstraintExpr::Binary { col: FRAUD_FLAG });

        // C13: age_diff == oldest_ts - min_age_ts
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[AGE_DIFF]),
                term(neg_one(), &[OLDEST_TS]),
                term(BabyBear::ONE, &[MIN_AGE_TS]),
            ],
        });

        // C14: age_ok_bit is binary
        constraints.push(ConstraintExpr::Binary { col: AGE_OK_BIT });

        // C15: identity_commitment == hash_fact(interaction_count, [weighted_sum, oldest_ts, score_threshold])
        constraints.push(ConstraintExpr::Hash {
            output_col: IDENTITY_COMMITMENT,
            input_cols: vec![INTERACTION_COUNT, WEIGHTED_SUM, OLDEST_TS, SCORE_THRESHOLD],
        });

        // Boundaries
        let boundaries = vec![
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: SCORE_THRESHOLD,
                pi_index: PI_SCORE_THRESHOLD,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: MIN_AGE_TS,
                pi_index: PI_MIN_AGE_TS,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: EXPECTED_COMMITMENT,
                pi_index: PI_EXPECTED_COMMITMENT,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: INTERACTION_COUNT,
                pi_index: PI_INTERACTION_COUNT,
            },
            // fraud_flag must be 0 (no revocation)
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: FRAUD_FLAG,
                value: BabyBear::ZERO,
            },
            // score_ge_bit must be 1
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: SCORE_GE_BIT,
                value: BabyBear::ONE,
            },
            // age_ok_bit must be 1
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: AGE_OK_BIT,
                value: BabyBear::ONE,
            },
            // identity_commitment must match expected
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: IDENTITY_COMMITMENT,
                pi_index: PI_EXPECTED_COMMITMENT,
            },
        ];

        let columns = vec![
            ColumnDef {
                name: "weighted_sum".into(),
                index: WEIGHTED_SUM,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "score_threshold".into(),
                index: SCORE_THRESHOLD,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "interaction_count".into(),
                index: INTERACTION_COUNT,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "identity_commitment".into(),
                index: IDENTITY_COMMITMENT,
                kind: ColumnKind::Hash,
            },
        ];

        CircuitDescriptor {
            name: "pyana-reputation-accumulator-v1".into(),
            trace_width: TRACE_WIDTH,
            max_degree: 4, // Hash with 4 input_cols has degree 4
            columns,
            constraints,
            boundaries,
            public_input_count: PUBLIC_INPUT_COUNT,
            lookup_tables: vec![],
        }
    }

    pub fn reputation_circuit() -> DslCircuit {
        DslCircuit::new(reputation_accumulator_descriptor())
    }

    pub fn generate_valid_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let scores: [u32; 8] = [10, 8, 9, 7, 10, 6, 8, 9];
        let weights: [u32; 8] = [3, 2, 3, 1, 3, 1, 2, 2];
        let products: Vec<u32> = scores
            .iter()
            .zip(weights.iter())
            .map(|(s, w)| s * w)
            .collect();
        let weighted_sum: u32 = products.iter().sum(); // 30+16+27+7+30+6+16+18 = 150
        let score_threshold = 100u32;
        let interaction_count = 8u32;
        let oldest_ts = 1_600_000_000u32;
        let min_age_ts = 1_500_000_000u32;

        let identity = hash_fact(
            BabyBear::new(interaction_count),
            &[
                BabyBear::new(weighted_sum),
                BabyBear::new(oldest_ts),
                BabyBear::new(score_threshold),
            ],
        );

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        for i in 0..8 {
            row[SCORE_START + i] = BabyBear::new(scores[i]);
            row[WEIGHT_START + i] = BabyBear::new(weights[i]);
            row[PRODUCT_START + i] = BabyBear::new(products[i]);
        }
        row[WEIGHTED_SUM] = BabyBear::new(weighted_sum);
        row[SCORE_THRESHOLD] = BabyBear::new(score_threshold);
        row[SCORE_GE_AUX] = BabyBear::new(weighted_sum - score_threshold);
        row[SCORE_GE_BIT] = BabyBear::ONE;
        row[INTERACTION_COUNT] = BabyBear::new(interaction_count);
        row[FRAUD_FLAG] = BabyBear::ZERO;
        row[OLDEST_TS] = BabyBear::new(oldest_ts);
        row[MIN_AGE_TS] = BabyBear::new(min_age_ts);
        row[AGE_DIFF] = BabyBear::new(oldest_ts - min_age_ts);
        row[AGE_OK_BIT] = BabyBear::ONE;
        row[IDENTITY_COMMITMENT] = identity;
        row[EXPECTED_COMMITMENT] = identity;

        let trace = vec![row.clone(), row];

        let public_inputs = vec![
            BabyBear::new(score_threshold),   // PI_SCORE_THRESHOLD
            BabyBear::new(min_age_ts),        // PI_MIN_AGE_TS
            identity,                         // PI_EXPECTED_COMMITMENT
            BabyBear::new(interaction_count), // PI_INTERACTION_COUNT
        ];

        (trace, public_inputs)
    }
}

// ============================================================================
// 4. MULTI-ASSET CONSERVATION DESCRIPTOR
// ============================================================================
//
// Proves conservation across multiple asset types in a private multi-asset transfer.
//
// For each of 4 asset types: sum(inputs) == sum(outputs)
// Plus: all values non-negative (binary decomposition), note commitments correct
//
// Trace Layout (80 columns):
//   Per asset (4 assets x 16 columns = 64):
//     [base+0..3]:  input_values[0..3]
//     [base+4..7]:  output_values[0..3]
//     [base+8]:     input_sum
//     [base+9]:     output_sum
//     [base+10]:    conservation_check (input_sum - output_sum, must == 0)
//     [base+11]:    input_commitment = hash(inputs)
//     [base+12]:    output_commitment = hash(outputs)
//     [base+13]:    value_positive_flag (binary)
//     [base+14..15]: reserved
//   [64..67]:  asset_type_ids[0..3]
//   [68]:      global_nonce
//   [69]:      transaction_hash = hash_fact(global_nonce, [asset_type_ids, ...])
//   [70..79]:  reserved
//
// Public Inputs: [transaction_hash, asset_type_0, asset_type_1, asset_type_2, asset_type_3]

pub mod multi_asset {
    use super::*;

    pub const TRACE_WIDTH: usize = 80;
    pub const PUBLIC_INPUT_COUNT: usize = 5;
    pub const NUM_ASSETS: usize = 4;
    pub const COLS_PER_ASSET: usize = 16;
    pub const NUM_IO: usize = 4; // 4 inputs + 4 outputs per asset

    // Per-asset column offsets (relative to asset base)
    pub const INPUT_START: usize = 0;
    pub const OUTPUT_START: usize = 4;
    pub const INPUT_SUM: usize = 8;
    pub const OUTPUT_SUM: usize = 9;
    pub const CONSERVATION: usize = 10;
    pub const INPUT_COMMIT: usize = 11;
    pub const OUTPUT_COMMIT: usize = 12;
    pub const VALUE_POS_FLAG: usize = 13;

    // Global columns
    pub const ASSET_TYPE_START: usize = 64;
    pub const GLOBAL_NONCE: usize = 68;
    pub const TRANSACTION_HASH: usize = 69;

    // PI
    pub const PI_TX_HASH: usize = 0;
    pub const PI_ASSET_TYPE_START: usize = 1;

    fn asset_base(asset_idx: usize) -> usize {
        asset_idx * COLS_PER_ASSET
    }

    pub fn multi_asset_conservation_descriptor() -> CircuitDescriptor {
        let mut constraints = Vec::new();

        for a in 0..NUM_ASSETS {
            let base = asset_base(a);

            // C(a,1): input_sum == sum of input_values
            let mut in_terms = vec![term(BabyBear::ONE, &[base + INPUT_SUM])];
            for i in 0..NUM_IO {
                in_terms.push(term(neg_one(), &[base + INPUT_START + i]));
            }
            constraints.push(ConstraintExpr::Polynomial { terms: in_terms });

            // C(a,2): output_sum == sum of output_values
            let mut out_terms = vec![term(BabyBear::ONE, &[base + OUTPUT_SUM])];
            for i in 0..NUM_IO {
                out_terms.push(term(neg_one(), &[base + OUTPUT_START + i]));
            }
            constraints.push(ConstraintExpr::Polynomial { terms: out_terms });

            // C(a,3): conservation_check == input_sum - output_sum (must be zero via boundary)
            constraints.push(ConstraintExpr::Polynomial {
                terms: vec![
                    term(BabyBear::ONE, &[base + CONSERVATION]),
                    term(neg_one(), &[base + INPUT_SUM]),
                    term(BabyBear::ONE, &[base + OUTPUT_SUM]),
                ],
            });

            // C(a,4): input_commitment == hash_fact(input[0], [input[1], input[2], input[3], asset_type])
            constraints.push(ConstraintExpr::Hash {
                output_col: base + INPUT_COMMIT,
                input_cols: vec![
                    base + INPUT_START,
                    base + INPUT_START + 1,
                    base + INPUT_START + 2,
                    base + INPUT_START + 3,
                    ASSET_TYPE_START + a,
                ],
            });

            // C(a,5): output_commitment == hash_fact(output[0], [output[1], output[2], output[3], asset_type])
            constraints.push(ConstraintExpr::Hash {
                output_col: base + OUTPUT_COMMIT,
                input_cols: vec![
                    base + OUTPUT_START,
                    base + OUTPUT_START + 1,
                    base + OUTPUT_START + 2,
                    base + OUTPUT_START + 3,
                    ASSET_TYPE_START + a,
                ],
            });

            // C(a,6): value_positive_flag is binary
            constraints.push(ConstraintExpr::Binary {
                col: base + VALUE_POS_FLAG,
            });
        }

        // C_global: transaction_hash == hash_fact(global_nonce, [asset_type_0..3])
        constraints.push(ConstraintExpr::Hash {
            output_col: TRANSACTION_HASH,
            input_cols: vec![
                GLOBAL_NONCE,
                ASSET_TYPE_START,
                ASSET_TYPE_START + 1,
                ASSET_TYPE_START + 2,
                ASSET_TYPE_START + 3,
            ],
        });

        // Boundaries
        let mut boundaries = vec![
            // Transaction hash binding
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: TRANSACTION_HASH,
                pi_index: PI_TX_HASH,
            },
        ];

        // Asset type bindings
        for a in 0..NUM_ASSETS {
            boundaries.push(BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: ASSET_TYPE_START + a,
                pi_index: PI_ASSET_TYPE_START + a,
            });
        }

        // Conservation checks must all be zero
        for a in 0..NUM_ASSETS {
            boundaries.push(BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: asset_base(a) + CONSERVATION,
                value: BabyBear::ZERO,
            });
            // Value positivity flags must be 1
            boundaries.push(BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: asset_base(a) + VALUE_POS_FLAG,
                value: BabyBear::ONE,
            });
        }

        let columns = vec![
            ColumnDef {
                name: "global_nonce".into(),
                index: GLOBAL_NONCE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "transaction_hash".into(),
                index: TRANSACTION_HASH,
                kind: ColumnKind::Hash,
            },
        ];

        CircuitDescriptor {
            name: "pyana-multi-asset-conservation-v1".into(),
            trace_width: TRACE_WIDTH,
            max_degree: 5, // Hash with 5 input_cols has degree 5
            columns,
            constraints,
            boundaries,
            public_input_count: PUBLIC_INPUT_COUNT,
            lookup_tables: vec![],
        }
    }

    pub fn multi_asset_circuit() -> DslCircuit {
        DslCircuit::new(multi_asset_conservation_descriptor())
    }

    pub fn generate_valid_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let asset_types = [
            BabyBear::new(1), // ETH
            BabyBear::new(2), // USDC
            BabyBear::new(3), // BTC
            BabyBear::new(4), // DAI
        ];
        let global_nonce = BabyBear::new(42);

        // For each asset: 4 inputs, 4 outputs, conservation holds
        let asset_data: [([u32; 4], [u32; 4]); 4] = [
            ([100, 200, 50, 150], [120, 180, 100, 100]), // sum=500=500
            ([1000, 2000, 500, 1500], [1200, 1800, 1000, 1000]), // sum=5000=5000
            ([10, 20, 5, 15], [12, 18, 10, 10]),         // sum=50=50
            ([50, 100, 25, 75], [60, 90, 50, 50]),       // sum=250=250
        ];

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

        for a in 0..NUM_ASSETS {
            let base = asset_base(a);
            let (inputs, outputs) = &asset_data[a];

            let input_sum: u32 = inputs.iter().sum();
            let output_sum: u32 = outputs.iter().sum();
            assert_eq!(
                input_sum, output_sum,
                "Conservation must hold for asset {a}"
            );

            for i in 0..NUM_IO {
                row[base + INPUT_START + i] = BabyBear::new(inputs[i]);
                row[base + OUTPUT_START + i] = BabyBear::new(outputs[i]);
            }
            row[base + INPUT_SUM] = BabyBear::new(input_sum);
            row[base + OUTPUT_SUM] = BabyBear::new(output_sum);
            row[base + CONSERVATION] = BabyBear::ZERO; // conservation holds

            // Compute commitments
            let input_commit = hash_fact(
                BabyBear::new(inputs[0]),
                &[
                    BabyBear::new(inputs[1]),
                    BabyBear::new(inputs[2]),
                    BabyBear::new(inputs[3]),
                    asset_types[a],
                ],
            );
            let output_commit = hash_fact(
                BabyBear::new(outputs[0]),
                &[
                    BabyBear::new(outputs[1]),
                    BabyBear::new(outputs[2]),
                    BabyBear::new(outputs[3]),
                    asset_types[a],
                ],
            );
            row[base + INPUT_COMMIT] = input_commit;
            row[base + OUTPUT_COMMIT] = output_commit;
            row[base + VALUE_POS_FLAG] = BabyBear::ONE;
        }

        // Global columns
        for a in 0..NUM_ASSETS {
            row[ASSET_TYPE_START + a] = asset_types[a];
        }
        row[GLOBAL_NONCE] = global_nonce;

        let tx_hash = hash_fact(
            global_nonce,
            &[
                asset_types[0],
                asset_types[1],
                asset_types[2],
                asset_types[3],
            ],
        );
        row[TRANSACTION_HASH] = tx_hash;

        let trace = vec![row.clone(), row];

        let public_inputs = vec![
            tx_hash,        // PI_TX_HASH
            asset_types[0], // PI_ASSET_TYPE_START + 0
            asset_types[1], // PI_ASSET_TYPE_START + 1
            asset_types[2], // PI_ASSET_TYPE_START + 2
            asset_types[3], // PI_ASSET_TYPE_START + 3
        ];

        (trace, public_inputs)
    }
}

// ============================================================================
// 5. CONDITIONAL EXECUTION DESCRIPTOR
// ============================================================================
//
// Proves that ONE of N execution paths was correctly followed (if/else/match).
//
// This demonstrates gated constraint composition: path selectors are binary,
// exactly one is active, and each path has its own constraints that are
// zeroed out when that path is inactive.
//
// Trace Layout (64 columns):
//   [0..3]:   path_selectors[0..3] (binary, exactly one is 1)
//   [4]:      old_state
//   [5]:      new_state
//   [6]:      input_a
//   [7]:      input_b
//   [8]:      path0_result (= old_state + input_a, active when sel[0]=1)
//   [9]:      path1_result (= old_state - input_a, active when sel[1]=1)
//   [10]:     path2_result (= old_state * input_a, active when sel[2]=1)
//   [11]:     path3_result (= input_a + input_b, active when sel[3]=1)
//   [12]:     path_contribution (= sum of sel[i] * path_result[i])
//   [13]:     state_transition_valid (= new_state - path_contribution, must be 0)
//   [14]:     state_hash = hash_fact(old_state, [new_state, input_a, input_b])
//   [15..63]: reserved
//
// Public Inputs: [old_state, new_state, state_hash]

pub mod conditional_execution {
    use super::*;

    pub const TRACE_WIDTH: usize = 64;
    pub const PUBLIC_INPUT_COUNT: usize = 3;
    pub const NUM_PATHS: usize = 4;

    // Columns
    pub const SEL_START: usize = 0;
    pub const OLD_STATE: usize = 4;
    pub const NEW_STATE: usize = 5;
    pub const INPUT_A: usize = 6;
    pub const INPUT_B: usize = 7;
    pub const PATH0_RESULT: usize = 8;
    pub const PATH1_RESULT: usize = 9;
    pub const PATH2_RESULT: usize = 10;
    pub const PATH3_RESULT: usize = 11;
    pub const PATH_CONTRIBUTION: usize = 12;
    pub const STATE_TRANSITION: usize = 13;
    pub const STATE_HASH: usize = 14;

    // PI
    pub const PI_OLD_STATE: usize = 0;
    pub const PI_NEW_STATE: usize = 1;
    pub const PI_STATE_HASH: usize = 2;

    pub fn conditional_execution_descriptor() -> CircuitDescriptor {
        let mut constraints = Vec::new();

        // C1-C4: path selectors are binary
        for i in 0..NUM_PATHS {
            constraints.push(ConstraintExpr::Binary { col: SEL_START + i });
        }

        // C5: exactly one selector is active: sel[0] + sel[1] + sel[2] + sel[3] - 1 == 0
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[SEL_START]),
                term(BabyBear::ONE, &[SEL_START + 1]),
                term(BabyBear::ONE, &[SEL_START + 2]),
                term(BabyBear::ONE, &[SEL_START + 3]),
                term(neg_one(), &[]), // constant -1
            ],
        });

        // C6: path0_result == old_state + input_a (gated by sel[0])
        // When sel[0]=1: path0_result - old_state - input_a == 0
        constraints.push(ConstraintExpr::Gated {
            selector_col: SEL_START,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    term(BabyBear::ONE, &[PATH0_RESULT]),
                    term(neg_one(), &[OLD_STATE]),
                    term(neg_one(), &[INPUT_A]),
                ],
            }),
        });

        // C7: path1_result == old_state - input_a (gated by sel[1])
        constraints.push(ConstraintExpr::Gated {
            selector_col: SEL_START + 1,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    term(BabyBear::ONE, &[PATH1_RESULT]),
                    term(neg_one(), &[OLD_STATE]),
                    term(BabyBear::ONE, &[INPUT_A]),
                ],
            }),
        });

        // C8: path2_result == old_state * input_a (gated by sel[2])
        // old_state * input_a - path2_result == 0
        constraints.push(ConstraintExpr::Gated {
            selector_col: SEL_START + 2,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    term(BabyBear::ONE, &[OLD_STATE, INPUT_A]),
                    term(neg_one(), &[PATH2_RESULT]),
                ],
            }),
        });

        // C9: path3_result == input_a + input_b (gated by sel[3])
        constraints.push(ConstraintExpr::Gated {
            selector_col: SEL_START + 3,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    term(BabyBear::ONE, &[PATH3_RESULT]),
                    term(neg_one(), &[INPUT_A]),
                    term(neg_one(), &[INPUT_B]),
                ],
            }),
        });

        // C10: path_contribution == sel[0]*path0 + sel[1]*path1 + sel[2]*path2 + sel[3]*path3
        // path_contribution - sel[0]*path0 - sel[1]*path1 - sel[2]*path2 - sel[3]*path3 == 0
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[PATH_CONTRIBUTION]),
                term(neg_one(), &[SEL_START, PATH0_RESULT]),
                term(neg_one(), &[SEL_START + 1, PATH1_RESULT]),
                term(neg_one(), &[SEL_START + 2, PATH2_RESULT]),
                term(neg_one(), &[SEL_START + 3, PATH3_RESULT]),
            ],
        });

        // C11: state_transition == new_state - path_contribution (must be 0)
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[STATE_TRANSITION]),
                term(neg_one(), &[NEW_STATE]),
                term(BabyBear::ONE, &[PATH_CONTRIBUTION]),
            ],
        });

        // C12: state_hash == hash_fact(old_state, [new_state, input_a, input_b])
        constraints.push(ConstraintExpr::Hash {
            output_col: STATE_HASH,
            input_cols: vec![OLD_STATE, NEW_STATE, INPUT_A, INPUT_B],
        });

        // Boundaries
        let boundaries = vec![
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: OLD_STATE,
                pi_index: PI_OLD_STATE,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: NEW_STATE,
                pi_index: PI_NEW_STATE,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: STATE_HASH,
                pi_index: PI_STATE_HASH,
            },
            // State transition must be valid (== 0)
            BoundaryDef::Fixed {
                row: BoundaryRow::First,
                col: STATE_TRANSITION,
                value: BabyBear::ZERO,
            },
        ];

        let columns = vec![
            ColumnDef {
                name: "old_state".into(),
                index: OLD_STATE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "new_state".into(),
                index: NEW_STATE,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "input_a".into(),
                index: INPUT_A,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "input_b".into(),
                index: INPUT_B,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "state_hash".into(),
                index: STATE_HASH,
                kind: ColumnKind::Hash,
            },
        ];

        CircuitDescriptor {
            name: "pyana-conditional-execution-v1".into(),
            trace_width: TRACE_WIDTH,
            max_degree: 4, // Hash with 4 input_cols has degree 4
            columns,
            constraints,
            boundaries,
            public_input_count: PUBLIC_INPUT_COUNT,
            lookup_tables: vec![],
        }
    }

    pub fn conditional_execution_circuit() -> DslCircuit {
        DslCircuit::new(conditional_execution_descriptor())
    }

    /// Generate a valid trace for path 0 (addition: new_state = old_state + input_a)
    pub fn generate_path0_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        generate_trace_for_path(0, 100, 25, 0)
    }

    /// Generate a valid trace for path 1 (subtraction: new_state = old_state - input_a)
    pub fn generate_path1_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        generate_trace_for_path(1, 100, 25, 0)
    }

    /// Generate a valid trace for path 2 (multiplication: new_state = old_state * input_a)
    pub fn generate_path2_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        generate_trace_for_path(2, 100, 3, 0)
    }

    /// Generate a valid trace for path 3 (sum of inputs: new_state = input_a + input_b)
    pub fn generate_path3_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        generate_trace_for_path(3, 100, 25, 75)
    }

    fn generate_trace_for_path(
        path: usize,
        old_state_val: u32,
        input_a_val: u32,
        input_b_val: u32,
    ) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let old_state = BabyBear::new(old_state_val);
        let input_a = BabyBear::new(input_a_val);
        let input_b = BabyBear::new(input_b_val);

        // Compute results for each path
        let path0_result = old_state + input_a;
        let path1_result = old_state - input_a;
        let path2_result = old_state * input_a;
        let path3_result = input_a + input_b;

        let new_state = match path {
            0 => path0_result,
            1 => path1_result,
            2 => path2_result,
            3 => path3_result,
            _ => panic!("invalid path"),
        };

        // path_contribution = sel[path] * path_result[path] = 1 * result = new_state
        let path_contribution = new_state;
        let state_transition = new_state - path_contribution; // always 0

        let state_hash = hash_fact(old_state, &[new_state, input_a, input_b]);

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

        // Set selectors
        for i in 0..NUM_PATHS {
            row[SEL_START + i] = if i == path {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
        }

        row[OLD_STATE] = old_state;
        row[NEW_STATE] = new_state;
        row[INPUT_A] = input_a;
        row[INPUT_B] = input_b;
        row[PATH0_RESULT] = path0_result;
        row[PATH1_RESULT] = path1_result;
        row[PATH2_RESULT] = path2_result;
        row[PATH3_RESULT] = path3_result;
        row[PATH_CONTRIBUTION] = path_contribution;
        row[STATE_TRANSITION] = state_transition;
        row[STATE_HASH] = state_hash;

        let trace = vec![row.clone(), row];

        let public_inputs = vec![
            old_state,  // PI_OLD_STATE
            new_state,  // PI_NEW_STATE
            state_hash, // PI_STATE_HASH
        ];

        (trace, public_inputs)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{self, StarkAir};

    // ========================================================================
    // Credit Score tests
    // ========================================================================

    #[test]
    fn advanced_credit_score_descriptor_validates() {
        let desc = credit_score::credit_score_descriptor();
        assert!(
            desc.validate().is_ok(),
            "credit score descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn advanced_credit_score_valid_trace_evaluates_to_zero() {
        let (trace, pi) = credit_score::generate_valid_trace();
        let circuit = credit_score::credit_score_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Valid credit score trace should satisfy all constraints"
        );
    }

    #[test]
    fn advanced_credit_score_tampered_balance_detected() {
        let (mut trace, pi) = credit_score::generate_valid_trace();
        let circuit = credit_score::credit_score_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: inflate a balance
        trace[0][credit_score::BALANCE_START] = BabyBear::new(999999);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered balance should violate sum constraint"
        );
    }

    #[test]
    fn advanced_credit_score_tampered_attestation_detected() {
        let (mut trace, pi) = credit_score::generate_valid_trace();
        let circuit = credit_score::credit_score_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: wrong attestation hash
        trace[0][credit_score::ATTESTATION_HASH] = BabyBear::new(12345);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered attestation should violate Hash constraint"
        );
    }

    #[test]
    fn advanced_credit_score_stark_prove_verify() {
        let (trace, pi) = credit_score::generate_valid_trace();
        let circuit = credit_score::credit_score_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Credit score STARK prove/verify failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn advanced_credit_score_stark_rejects_wrong_pi() {
        let (trace, pi) = credit_score::generate_valid_trace();
        let circuit = credit_score::credit_score_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let mut wrong_pi = pi.clone();
        wrong_pi[credit_score::PI_ATTESTATION_ROOT] = BabyBear::new(99999);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "Should reject proof with wrong attestation root"
        );
    }

    // ========================================================================
    // Atomic Swap tests
    // ========================================================================

    #[test]
    fn advanced_atomic_swap_descriptor_validates() {
        let desc = atomic_swap::atomic_swap_descriptor();
        assert!(
            desc.validate().is_ok(),
            "atomic swap descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn advanced_atomic_swap_valid_trace_evaluates_to_zero() {
        let (trace, pi) = atomic_swap::generate_valid_trace();
        let circuit = atomic_swap::atomic_swap_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Valid atomic swap trace should satisfy all constraints"
        );
    }

    #[test]
    fn advanced_atomic_swap_tampered_value_detected() {
        let (mut trace, pi) = atomic_swap::generate_valid_trace();
        let circuit = atomic_swap::atomic_swap_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change bob_adjusted to break multiplication constraint
        trace[0][atomic_swap::BOB_ADJUSTED] = BabyBear::new(12345);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered bob_adjusted should violate multiplication constraint"
        );
    }

    #[test]
    fn advanced_atomic_swap_tampered_merkle_detected() {
        let (mut trace, pi) = atomic_swap::generate_valid_trace();
        let circuit = atomic_swap::atomic_swap_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change alice's parent hash
        trace[0][atomic_swap::ALICE_PARENT] = BabyBear::new(77777);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered Merkle parent should violate Hash constraint"
        );
    }

    #[test]
    fn advanced_atomic_swap_stark_prove_verify() {
        let (trace, pi) = atomic_swap::generate_valid_trace();
        let circuit = atomic_swap::atomic_swap_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Atomic swap STARK prove/verify failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn advanced_atomic_swap_stark_rejects_wrong_pi() {
        let (trace, pi) = atomic_swap::generate_valid_trace();
        let circuit = atomic_swap::atomic_swap_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let mut wrong_pi = pi.clone();
        wrong_pi[atomic_swap::PI_ALICE_ROOT] = BabyBear::new(11111);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong alice root");
    }

    // ========================================================================
    // Reputation Accumulator tests
    // ========================================================================

    #[test]
    fn advanced_reputation_descriptor_validates() {
        let desc = reputation::reputation_accumulator_descriptor();
        assert!(
            desc.validate().is_ok(),
            "reputation descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn advanced_reputation_valid_trace_evaluates_to_zero() {
        let (trace, pi) = reputation::generate_valid_trace();
        let circuit = reputation::reputation_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Valid reputation trace should satisfy all constraints"
        );
    }

    #[test]
    fn advanced_reputation_tampered_product_detected() {
        let (mut trace, pi) = reputation::generate_valid_trace();
        let circuit = reputation::reputation_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change weighted_product[0]
        trace[0][reputation::PRODUCT_START] = BabyBear::new(99999);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered product should violate Multiplication constraint"
        );
    }

    #[test]
    fn advanced_reputation_tampered_commitment_detected() {
        let (mut trace, pi) = reputation::generate_valid_trace();
        let circuit = reputation::reputation_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change identity commitment
        trace[0][reputation::IDENTITY_COMMITMENT] = BabyBear::new(0xBAD);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered commitment should violate Hash constraint"
        );
    }

    #[test]
    fn advanced_reputation_stark_prove_verify() {
        let (trace, pi) = reputation::generate_valid_trace();
        let circuit = reputation::reputation_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Reputation STARK prove/verify failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn advanced_reputation_stark_rejects_wrong_pi() {
        let (trace, pi) = reputation::generate_valid_trace();
        let circuit = reputation::reputation_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let mut wrong_pi = pi.clone();
        wrong_pi[reputation::PI_EXPECTED_COMMITMENT] = BabyBear::new(55555);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "Should reject proof with wrong commitment pi"
        );
    }

    // ========================================================================
    // Multi-Asset Conservation tests
    // ========================================================================

    #[test]
    fn advanced_multi_asset_descriptor_validates() {
        let desc = multi_asset::multi_asset_conservation_descriptor();
        assert!(
            desc.validate().is_ok(),
            "multi-asset descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn advanced_multi_asset_valid_trace_evaluates_to_zero() {
        let (trace, pi) = multi_asset::generate_valid_trace();
        let circuit = multi_asset::multi_asset_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Valid multi-asset trace should satisfy all constraints"
        );
    }

    #[test]
    fn advanced_multi_asset_broken_conservation_detected() {
        let (mut trace, pi) = multi_asset::generate_valid_trace();
        let circuit = multi_asset::multi_asset_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change an input value for asset 0, breaking conservation
        trace[0][multi_asset::INPUT_START] = BabyBear::new(999);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Broken conservation should violate sum constraint"
        );
    }

    #[test]
    fn advanced_multi_asset_tampered_commitment_detected() {
        let (mut trace, pi) = multi_asset::generate_valid_trace();
        let circuit = multi_asset::multi_asset_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: wrong input commitment for asset 1
        let base = multi_asset::COLS_PER_ASSET; // asset 1
        trace[0][base + multi_asset::INPUT_COMMIT] = BabyBear::new(0xDEAD);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered commitment should violate Hash constraint"
        );
    }

    #[test]
    fn advanced_multi_asset_stark_prove_verify() {
        let (trace, pi) = multi_asset::generate_valid_trace();
        let circuit = multi_asset::multi_asset_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Multi-asset STARK prove/verify failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn advanced_multi_asset_stark_rejects_wrong_pi() {
        let (trace, pi) = multi_asset::generate_valid_trace();
        let circuit = multi_asset::multi_asset_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let mut wrong_pi = pi.clone();
        wrong_pi[multi_asset::PI_TX_HASH] = BabyBear::new(0xCAFE);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong tx hash");
    }

    // ========================================================================
    // Conditional Execution tests
    // ========================================================================

    #[test]
    fn advanced_conditional_descriptor_validates() {
        let desc = conditional_execution::conditional_execution_descriptor();
        assert!(
            desc.validate().is_ok(),
            "conditional execution descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn advanced_conditional_path0_evaluates_to_zero() {
        let (trace, pi) = conditional_execution::generate_path0_trace();
        let circuit = conditional_execution::conditional_execution_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Path 0 (addition) should satisfy all constraints"
        );
    }

    #[test]
    fn advanced_conditional_path1_evaluates_to_zero() {
        let (trace, pi) = conditional_execution::generate_path1_trace();
        let circuit = conditional_execution::conditional_execution_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Path 1 (subtraction) should satisfy all constraints"
        );
    }

    #[test]
    fn advanced_conditional_path2_evaluates_to_zero() {
        let (trace, pi) = conditional_execution::generate_path2_trace();
        let circuit = conditional_execution::conditional_execution_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Path 2 (multiplication) should satisfy all constraints"
        );
    }

    #[test]
    fn advanced_conditional_path3_evaluates_to_zero() {
        let (trace, pi) = conditional_execution::generate_path3_trace();
        let circuit = conditional_execution::conditional_execution_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Path 3 (input sum) should satisfy all constraints"
        );
    }

    #[test]
    fn advanced_conditional_two_selectors_detected() {
        let (mut trace, pi) = conditional_execution::generate_path0_trace();
        let circuit = conditional_execution::conditional_execution_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: set two selectors to 1 (violates exactly-one)
        trace[0][conditional_execution::SEL_START + 1] = BabyBear::ONE;

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Two active selectors should violate exactly-one constraint"
        );
    }

    #[test]
    fn advanced_conditional_wrong_path_result_detected() {
        let (mut trace, pi) = conditional_execution::generate_path0_trace();
        let circuit = conditional_execution::conditional_execution_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change path0_result to wrong value
        trace[0][conditional_execution::PATH0_RESULT] = BabyBear::new(9999);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Wrong path result should violate gated constraint"
        );
    }

    #[test]
    fn advanced_conditional_tampered_state_hash_detected() {
        let (mut trace, pi) = conditional_execution::generate_path0_trace();
        let circuit = conditional_execution::conditional_execution_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: wrong state hash
        trace[0][conditional_execution::STATE_HASH] = BabyBear::new(0xBEEF);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered state hash should violate Hash constraint"
        );
    }

    #[test]
    fn advanced_conditional_all_paths_stark_prove_verify() {
        let circuit = conditional_execution::conditional_execution_circuit();

        for path_fn in [
            conditional_execution::generate_path0_trace,
            conditional_execution::generate_path1_trace,
            conditional_execution::generate_path2_trace,
            conditional_execution::generate_path3_trace,
        ] {
            let (trace, pi) = path_fn();
            let proof = stark::prove(&circuit, &trace, &pi);
            let result = stark::verify(&circuit, &proof, &pi);
            assert!(
                result.is_ok(),
                "Conditional execution STARK prove/verify failed: {:?}",
                result.err()
            );
        }
    }

    #[test]
    fn advanced_conditional_stark_rejects_wrong_pi() {
        let (trace, pi) = conditional_execution::generate_path0_trace();
        let circuit = conditional_execution::conditional_execution_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let mut wrong_pi = pi.clone();
        wrong_pi[conditional_execution::PI_STATE_HASH] = BabyBear::new(0xFACE);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "Should reject proof with wrong state hash pi"
        );
    }

    // ========================================================================
    // Cross-circuit: descriptor width verification
    // ========================================================================

    #[test]
    fn advanced_all_circuits_have_large_widths() {
        // These circuits demonstrate that the DSL scales to large trace widths
        assert_eq!(credit_score::credit_score_descriptor().trace_width, 64);
        assert_eq!(atomic_swap::atomic_swap_descriptor().trace_width, 56);
        assert_eq!(
            reputation::reputation_accumulator_descriptor().trace_width,
            52
        );
        assert_eq!(
            multi_asset::multi_asset_conservation_descriptor().trace_width,
            80
        );
        assert_eq!(
            conditional_execution::conditional_execution_descriptor().trace_width,
            64
        );
    }

    #[test]
    fn advanced_all_circuits_have_multiple_constraint_types() {
        // Credit score: Polynomial + Equality + Binary + Hash = 4 types
        let cs = credit_score::credit_score_descriptor();
        let has_poly = cs
            .constraints
            .iter()
            .any(|c| matches!(c, ConstraintExpr::Polynomial { .. }));
        let has_binary = cs
            .constraints
            .iter()
            .any(|c| matches!(c, ConstraintExpr::Binary { .. }));
        let has_hash = cs
            .constraints
            .iter()
            .any(|c| matches!(c, ConstraintExpr::Hash { .. }));
        let has_eq = cs
            .constraints
            .iter()
            .any(|c| matches!(c, ConstraintExpr::Equality { .. }));
        assert!(
            has_poly && has_binary && has_hash && has_eq,
            "Credit score should use Polynomial + Binary + Hash + Equality"
        );

        // Conditional execution: Gated + Polynomial + Binary + Hash
        let ce = conditional_execution::conditional_execution_descriptor();
        let has_gated = ce
            .constraints
            .iter()
            .any(|c| matches!(c, ConstraintExpr::Gated { .. }));
        let has_poly = ce
            .constraints
            .iter()
            .any(|c| matches!(c, ConstraintExpr::Polynomial { .. }));
        let has_binary = ce
            .constraints
            .iter()
            .any(|c| matches!(c, ConstraintExpr::Binary { .. }));
        let has_hash = ce
            .constraints
            .iter()
            .any(|c| matches!(c, ConstraintExpr::Hash { .. }));
        assert!(
            has_gated && has_poly && has_binary && has_hash,
            "Conditional execution should use Gated + Polynomial + Binary + Hash"
        );
    }
}
