//! The synthetic-receipt suite: Q1 (extraction, eval, classifier) and Q2
//! (the MMR false-witness suite mirroring `Dregg2/Lightclient/MMR.lean` §7,
//! plus the certificate-carrying answer end-to-end).

use dregg_query::*;

/// A synthetic 32-byte "receipt hash" — stands in for
/// `TurnReceipt::receipt_hash()` (any injective-enough tag works for tests;
/// the MMR hashes it again as a leaf).
fn rhash(i: u64) -> [u8; 32] {
    *blake3::hash(format!("synthetic-receipt-{i}").as_bytes()).as_bytes()
}

fn record(i: u64, height: u64, agent: &str, effects: Vec<EffectSummary>) -> ReceiptRecord {
    ReceiptRecord {
        chain_index: i,
        receipt_hash: hex::encode(rhash(i)),
        height,
        agent: agent.to_string(),
        effects,
    }
}

/// The synthetic receipt chain: six receipts, dense positions 0..=5.
fn chain() -> Vec<ReceiptRecord> {
    vec![
        record(
            0,
            1,
            "alice",
            vec![EffectSummary::Created {
                agent: "alice".into(),
                cell: "cellA".into(),
            }],
        ),
        record(
            1,
            2,
            "alice",
            vec![EffectSummary::Transfer {
                from: "alice".into(),
                to: "bob".into(),
                asset: "cmp".into(),
                amount: 150,
            }],
        ),
        record(
            2,
            3,
            "alice",
            vec![EffectSummary::Granted {
                from: "alice".into(),
                to: "bob".into(),
                cap: "cap1".into(),
            }],
        ),
        record(
            3,
            4,
            "carol",
            vec![
                EffectSummary::Transfer {
                    from: "carol".into(),
                    to: "bob".into(),
                    asset: "cmp".into(),
                    amount: 50,
                },
                EffectSummary::Other {
                    name: "emit_event".into(),
                },
            ],
        ),
        record(
            4,
            5,
            "alice",
            vec![EffectSummary::Revoked { cap: "cap1".into() }],
        ),
        record(
            5,
            6,
            "alice",
            vec![EffectSummary::Balance {
                cell: "cellA".into(),
                asset: "cmp".into(),
                amount: 850,
            }],
        ),
    ]
}

fn mmr_of(receipts: &[ReceiptRecord]) -> Mmr<Blake3Mmr> {
    let mut m = Mmr::new(Blake3Mmr);
    for r in receipts {
        m.push(r.receipt_hash_bytes().unwrap());
    }
    m
}

// ---------------------------------------------------------------- Q1: facts

#[test]
fn extraction_schema() {
    let base = extract_facts(&chain());
    // 6 receipts, 6 extractable effects (`Other` skipped).
    assert_eq!(base.len(), 6);
    assert!(base.iter().all(|f| f.well_formed()));
    assert_eq!(base.with_pred(Pred::Transfer).count(), 2);
    assert_eq!(base.with_pred(Pred::Created).count(), 1);
    assert_eq!(base.max_height(), 6);
    // height stamps ride the last argument
    let t: Vec<_> = base.with_pred(Pred::Transfer).collect();
    assert_eq!(t[0].height(), 2);
    assert_eq!(t[1].height(), 4);
}

// ----------------------------------------------------------------- Q1: eval

/// `?- transfer(From, bob, Asset, Amount, H), Amount > 100.`
fn big_transfers_to_bob() -> Query {
    Query::new()
        .atom(
            Pred::Transfer,
            vec![
                Term::var("From"),
                Term::sym("bob"),
                Term::var("Asset"),
                Term::var("Amount"),
                Term::var("H"),
            ],
        )
        .filter(Term::var("Amount"), CmpOp::Gt, Term::nat(100))
}

#[test]
fn eval_pattern_and_filter() {
    let base = extract_facts(&chain());
    let rows = eval(&base, &big_transfers_to_bob()).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["From"], Value::sym("alice"));
    assert_eq!(rows[0]["Amount"], Value::nat(150));
    assert_eq!(rows[0]["H"], Value::nat(2));
}

#[test]
fn eval_join_on_bindings() {
    // `?- granted(F, T, Cap, _), revoked(Cap, Hr).` — join on Cap.
    let base = extract_facts(&chain());
    let q = Query::new()
        .atom(
            Pred::Granted,
            vec![Term::var("F"), Term::var("T"), Term::var("Cap"), Term::Wild],
        )
        .atom(Pred::Revoked, vec![Term::var("Cap"), Term::var("Hr")]);
    let rows = eval(&base, &q).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["Cap"], Value::sym("cap1"));
    assert_eq!(rows[0]["Hr"], Value::nat(5));
}

#[test]
fn eval_negation_the_canonical_case() {
    // `reachable_cap`: granted and NOT revoked — empty here (cap1 was revoked).
    let base = extract_facts(&chain());
    let q = Query::new()
        .atom(
            Pred::Granted,
            vec![Term::Wild, Term::var("To"), Term::var("Cap"), Term::Wild],
        )
        .not_atom(Pred::Revoked, vec![Term::var("Cap"), Term::Wild]);
    let rows = eval(&base, &q).unwrap();
    assert!(rows.is_empty());

    // Drop the revocation receipt: the row appears — and that retraction
    // under append is exactly why the classifier grades this query
    // finalized-dependent.
    let shorter = &chain()[..4];
    let base = extract_facts(shorter);
    let rows = eval(&base, &q).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["To"], Value::sym("bob"));
}

#[test]
fn eval_rejects_unsafe_and_malformed() {
    let base = extract_facts(&chain());
    // unsafe: filter variable bound by no positive atom
    let q = Query::new()
        .atom(Pred::Revoked, vec![Term::var("Cap"), Term::Wild])
        .filter(Term::var("Amount"), CmpOp::Gt, Term::nat(0));
    assert!(matches!(eval(&base, &q), Err(QueryError::Unsafe(_))));
    // wrong arity
    let q = Query::new().atom(Pred::Revoked, vec![Term::var("Cap")]);
    assert!(matches!(eval(&base, &q), Err(QueryError::Arity { .. })));
}

// ----------------------------------------------------------- Q1: classifier

#[test]
fn classifier_grades_monotone_and_finalized() {
    let mono = classify(&big_transfers_to_bob());
    assert_eq!(mono.class, CoordinationClass::Monotone);
    assert!(mono.reasons.is_empty());

    let q = Query::new()
        .atom(
            Pred::Granted,
            vec![Term::Wild, Term::var("To"), Term::var("Cap"), Term::Wild],
        )
        .not_atom(Pred::Revoked, vec![Term::var("Cap"), Term::Wild]);
    let fin = classify(&q);
    assert_eq!(fin.class, CoordinationClass::FinalizedDependent);
    assert!(fin.reasons[0].contains("revoked"));
}

// ------------------------------------------------- Q2: MMR false witnesses

/// Witness TRUE: the exact answer verifies (`exact_range_verifies`).
#[test]
fn mmr_exact_answer_verifies() {
    let m = mmr_of(&chain());
    let root = m.root();
    let (vals, opening) = m.open_range(1, 4);
    let len = verify_range(&Blake3Mmr, &root, 1, 4, &vals, &opening).unwrap();
    assert_eq!(len, 6);
    // clipping at the committed length, like Lean `mrange demoLog 0 10`
    let (vals, opening) = m.open_range(0, 100);
    assert_eq!(vals.len(), 6);
    verify_range(&Blake3Mmr, &root, 0, 100, &vals, &opening).unwrap();
}

/// Witness FALSE: a SKIPPED position is rejected (`demo_skipped_rejected` —
/// density + the count are the whole argument).
#[test]
fn mmr_skipped_position_rejected() {
    let m = mmr_of(&chain());
    let root = m.root();
    let (mut vals, mut opening) = m.open_range(1, 4);
    vals.remove(1);
    opening.paths.remove(1);
    assert!(matches!(
        verify_range(&Blake3Mmr, &root, 1, 4, &vals, &opening),
        Err(MmrError::CountMismatch { .. })
    ));
}

/// Witness FALSE: a SUBSTITUTED value is rejected — right count, wrong value
/// (`demo_substituted_rejected`).
#[test]
fn mmr_substituted_value_rejected() {
    let m = mmr_of(&chain());
    let root = m.root();
    let (mut vals, opening) = m.open_range(1, 4);
    vals[0] = rhash(999);
    assert!(matches!(
        verify_range(&Blake3Mmr, &root, 1, 4, &vals, &opening),
        Err(MmrError::SlotMismatch { slot: 0 })
    ));
}

/// Witness FALSE: a REORDERED answer is rejected — each slot opens its own
/// dense position (`demo_reordered_rejected`).
#[test]
fn mmr_reordered_answer_rejected() {
    let m = mmr_of(&chain());
    let root = m.root();
    let (mut vals, mut opening) = m.open_range(1, 4);
    vals.swap(0, 1);
    opening.paths.swap(0, 1);
    assert!(matches!(
        verify_range(&Blake3Mmr, &root, 1, 4, &vals, &opening),
        Err(MmrError::SlotMismatch { .. })
    ));
}

/// The anti-ghost at the root: tamper / truncate / extend / reorder each
/// MOVE the root (`mroot_injective`'s executable shadow).
#[test]
fn mmr_root_moves_on_any_log_change() {
    let receipts = chain();
    let root = mmr_of(&receipts).root();

    // tamper one position
    let mut tampered = receipts.clone();
    tampered[2].receipt_hash = hex::encode(rhash(777));
    assert_ne!(mmr_of(&tampered).root(), root);

    // truncate (omission is visible at the root)
    assert_ne!(mmr_of(&receipts[..5]).root(), root);

    // extend (a forged extra receipt)
    let mut extended = receipts.clone();
    extended.push(record(6, 7, "mallory", vec![]));
    assert_ne!(mmr_of(&extended).root(), root);

    // reorder (position is part of the commitment)
    let mut reordered = receipts.clone();
    reordered.swap(0, 1);
    assert_ne!(mmr_of(&reordered).root(), root);
}

/// A forged frontier that bags to a DIFFERENT root is rejected; a forged
/// frontier claiming a different length cannot keep the root.
#[test]
fn mmr_forged_frontier_rejected() {
    let m = mmr_of(&chain());
    let root = m.root();
    let (vals, mut opening) = m.open_range(0, 5);
    // claim a shorter log by dropping the youngest peak
    opening.peaks.pop();
    let r = verify_range(&Blake3Mmr, &root, 0, 5, &vals, &opening);
    assert!(matches!(
        r,
        Err(MmrError::RootMismatch) | Err(MmrError::CountMismatch { .. })
    ));
    // non-mountains shape (duplicate heights) is structurally rejected
    let (vals, mut opening) = m.open_range(0, 5);
    let dup = opening.peaks[0].clone();
    opening.peaks.insert(0, dup);
    assert_eq!(
        verify_range(&Blake3Mmr, &root, 0, 5, &vals, &opening),
        Err(MmrError::BadFrontier)
    );
}

// --------------------------------------- Q2: the certificate-carrying answer

fn attested_slice(receipts: &[ReceiptRecord], lo: u64, hi: u64) -> AttestedSlice {
    let m = mmr_of(receipts);
    let (_vals, opening) = m.open_range(lo, hi);
    AttestedSlice {
        receipts: receipts[lo as usize..=(hi.min(m.len() - 1)) as usize].to_vec(),
        cert: RangeCertificate {
            root: m.root(),
            lo,
            hi,
            opening,
        },
    }
}

#[test]
fn attested_answer_end_to_end() {
    let receipts = chain();
    let trusted_root = mmr_of(&receipts).root();
    let slice = attested_slice(&receipts, 0, 5);

    let ans = answer(slice, big_transfers_to_bob()).unwrap();
    assert_eq!(ans.rows.len(), 1);
    assert!(ans.classification.is_monotone());
    assert_eq!(ans.fresh_as_of, 6);
    ans.verify(&Blake3Mmr, &trusted_root).unwrap();

    // ...and it survives a serde round-trip (the wire form is total).
    let json = serde_json::to_string(&ans).unwrap();
    let back: AttestedAnswer = serde_json::from_str(&json).unwrap();
    back.verify(&Blake3Mmr, &trusted_root).unwrap();
}

// ------------------------------------------------ Q2: coverage (whole-log vs range)
//
// The certificate proves the slice is EXACTLY positions [lo, hi] of the
// genuine log; coverage names how far that range-completeness reaches relative
// to the WHOLE log. A monotone query's unqualified "provably omitted nothing"
// is sound ONLY when the certified slice is the whole prefix [0, head] — and
// `verify` enforces that, so a sub-range answer cannot pose as whole-log.

/// Witness TRUE: a whole-log answer over the full prefix [0, head=5] verifies
/// (the default `answer` makes the honest `Range` claim; `answer_whole_log`
/// upgrades it to the unqualified whole-log claim, which holds here).
#[test]
fn coverage_whole_log_over_full_prefix_verifies() {
    let receipts = chain();
    let trusted_root = mmr_of(&receipts).root();
    let slice = attested_slice(&receipts, 0, 5);

    let ans = answer_whole_log(slice, big_transfers_to_bob()).unwrap();
    assert_eq!(ans.coverage, Coverage::WholeLog);
    assert!(ans.classification.is_monotone());
    ans.verify(&Blake3Mmr, &trusted_root).unwrap();

    // a clipping hi (>= head) still counts as whole-log — the certificate
    // pins the head at len-1 regardless of the over-large hi.
    let slice = attested_slice(&receipts, 0, 100);
    let ans = answer_whole_log(slice, big_transfers_to_bob()).unwrap();
    ans.verify(&Blake3Mmr, &trusted_root).unwrap();
}

/// Witness FALSE: a sub-range slice (lo != 0) that CLAIMS whole-log coverage is
/// rejected — its prefix [0, lo) is silently dropped, so "omitted nothing" is a
/// lie the certificate refutes (the slice is provably NOT the whole prefix).
#[test]
fn coverage_whole_log_over_non_prefix_rejected() {
    let receipts = chain();
    let trusted_root = mmr_of(&receipts).root();

    // The honest Range answer over [2, 5] verifies — it claims only its range.
    let slice = attested_slice(&receipts, 2, 5);
    let honest = answer(slice, big_transfers_to_bob()).unwrap();
    assert_eq!(honest.coverage, Coverage::Range);
    honest.verify(&Blake3Mmr, &trusted_root).unwrap();

    // The SAME slice re-labeled whole-log is rejected: lo = 2 != 0.
    let mut lying = honest;
    lying.coverage = Coverage::WholeLog;
    assert!(matches!(
        lying.verify(&Blake3Mmr, &trusted_root),
        Err(AttestError::CoverageNotWholeLog {
            lo: 2,
            len: 6,
            head: 5,
            ..
        })
    ));
}

/// Witness FALSE: a prefix slice that stops SHORT of the head and claims
/// whole-log coverage is rejected — the tail [hi+1, head] is dropped. This is
/// the omission a monotone query is most tempted to hide: the freshest rows.
#[test]
fn coverage_whole_log_short_of_head_rejected() {
    let receipts = chain();
    let trusted_root = mmr_of(&receipts).root();

    // [0, 3] is a genuine prefix but the log head is position 5.
    let slice = attested_slice(&receipts, 0, 3);
    let mut ans = answer(slice, big_transfers_to_bob()).unwrap();
    // honest Range claim verifies...
    ans.verify(&Blake3Mmr, &trusted_root).unwrap();
    // ...but the whole-log claim does not (hi = 3 < head = 5).
    ans.coverage = Coverage::WholeLog;
    assert!(matches!(
        ans.verify(&Blake3Mmr, &trusted_root),
        Err(AttestError::CoverageNotWholeLog {
            lo: 0,
            hi: 3,
            len: 6,
            head: 5
        })
    ));
}

/// Coverage rides the wire form: a whole-log answer round-trips through serde
/// and still verifies; re-labeling it on the wire is caught on re-verification.
#[test]
fn coverage_survives_serde_and_is_checked() {
    let receipts = chain();
    let trusted_root = mmr_of(&receipts).root();
    let slice = attested_slice(&receipts, 0, 5);
    let ans = answer_whole_log(slice, big_transfers_to_bob()).unwrap();

    let json = serde_json::to_string(&ans).unwrap();
    assert!(json.contains("whole_log"));
    let back: AttestedAnswer = serde_json::from_str(&json).unwrap();
    assert_eq!(back.coverage, Coverage::WholeLog);
    back.verify(&Blake3Mmr, &trusted_root).unwrap();
}

/// A server that hides the revocation receipt (the one that retracts the
/// finalized-dependent row) cannot produce a verifying certificate for the
/// full range — the omission breaks the count against the root-pinned length.
#[test]
fn attested_answer_cannot_hide_the_revocation() {
    let receipts = chain();
    let trusted_root = mmr_of(&receipts).root();

    // The dishonest slice: receipts [0..=5] minus position 4 (the revoke),
    // re-indexed densely to look like a complete [0,4] log of length 5.
    let mut hidden: Vec<ReceiptRecord> = receipts
        .iter()
        .filter(|r| r.chain_index != 4)
        .cloned()
        .collect();
    for (i, r) in hidden.iter_mut().enumerate() {
        r.chain_index = i as u64;
    }
    // The server can only open against ITS OWN (re-built) MMR — whose root
    // is not the trusted root.
    let forged = attested_slice(&hidden, 0, 4);
    let q = Query::new()
        .atom(
            Pred::Granted,
            vec![Term::Wild, Term::var("To"), Term::var("Cap"), Term::Wild],
        )
        .not_atom(Pred::Revoked, vec![Term::var("Cap"), Term::Wild]);
    let ans = answer(forged, q).unwrap();
    // the lie produced the retracted row...
    assert_eq!(ans.rows.len(), 1);
    // ...but it cannot verify against the trusted root.
    assert!(matches!(
        ans.verify(&Blake3Mmr, &trusted_root),
        Err(AttestError::UntrustedRoot)
    ));

    // Even claiming the TRUE root with the forged opening fails on the MMR.
    let m_forged = mmr_of(&hidden);
    let (_v, opening) = m_forged.open_range(0, 4);
    let forged2 = AttestedSlice {
        receipts: hidden,
        cert: RangeCertificate {
            root: trusted_root,
            lo: 0,
            hi: 4,
            opening,
        },
    };
    assert!(matches!(
        forged2.verify(&Blake3Mmr, &trusted_root),
        Err(AttestError::Mmr(_))
    ));
}

/// Tampered rows (server lies about the EVALUATION, not the input) are
/// caught by re-derivation.
#[test]
fn attested_answer_tampered_rows_rejected() {
    let receipts = chain();
    let trusted_root = mmr_of(&receipts).root();
    let slice = attested_slice(&receipts, 0, 5);
    let mut ans = answer(slice, big_transfers_to_bob()).unwrap();
    ans.rows[0].insert("From".into(), Value::sym("mallory"));
    assert!(matches!(
        ans.verify(&Blake3Mmr, &trusted_root),
        Err(AttestError::RowsMismatch)
    ));
}

/// A receipt presented at the wrong dense position is rejected before the
/// MMR even runs (chain_index IS the certified position).
#[test]
fn attested_slice_dense_index_binding() {
    let receipts = chain();
    let trusted_root = mmr_of(&receipts).root();
    let mut slice = attested_slice(&receipts, 0, 5);
    slice.receipts[3].chain_index = 7;
    assert!(matches!(
        slice.verify(&Blake3Mmr, &trusted_root),
        Err(AttestError::DenseIndex { slot: 3, .. })
    ));
}

// =====================================================================
// Richer EDB: burned / field / lifecycle / created facts
// =====================================================================

/// A chain exercising every new effect family: a cell birth, two burns of the
/// same asset, a state-field write, and a lifecycle seal.
fn rich_chain() -> Vec<ReceiptRecord> {
    vec![
        record(
            0,
            1,
            "alice",
            vec![EffectSummary::Created {
                agent: "alice".into(),
                cell: "vault".into(),
            }],
        ),
        record(
            1,
            2,
            "alice",
            vec![EffectSummary::Burned {
                cell: "vault".into(),
                asset: "gold".into(),
                amount: 30,
            }],
        ),
        record(
            2,
            3,
            "alice",
            vec![EffectSummary::Burned {
                cell: "vault".into(),
                asset: "gold".into(),
                amount: 70,
            }],
        ),
        record(
            3,
            4,
            "alice",
            vec![EffectSummary::Field {
                cell: "vault".into(),
                index: 2,
                value: "deadbeef".into(),
            }],
        ),
        record(
            4,
            5,
            "alice",
            vec![EffectSummary::Lifecycle {
                cell: "vault".into(),
                state: "sealed".into(),
            }],
        ),
    ]
}

#[test]
fn rich_extraction_schema() {
    let base = extract_facts(&rich_chain());
    assert_eq!(base.with_pred(Pred::Created).count(), 1);
    assert_eq!(base.with_pred(Pred::Burned).count(), 2);
    assert_eq!(base.with_pred(Pred::Field).count(), 1);
    assert_eq!(base.with_pred(Pred::Lifecycle).count(), 1);
    assert!(base.iter().all(|f| f.well_formed()));

    // A `field` write is queryable by slot index.
    let q = Query::new().atom(
        Pred::Field,
        vec![
            Term::sym("vault"),
            Term::nat(2),
            Term::var("V"),
            Term::var("H"),
        ],
    );
    let rows = eval(&base, &q).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["V"], Value::sym("deadbeef"));
    assert_eq!(rows[0]["H"], Value::nat(4));
}

// =====================================================================
// Q3: aggregation (group-by + count/sum/min/max)
// =====================================================================

#[test]
fn aggregate_sum_groups_by_asset() {
    let base = extract_facts(&rich_chain());
    // ?- burned(Cell, Asset, Amt, _) GROUP BY Asset; sum(Amt) AS total, count AS n.
    let q = Query::new()
        .atom(
            Pred::Burned,
            vec![
                Term::var("Cell"),
                Term::var("Asset"),
                Term::var("Amt"),
                Term::Wild,
            ],
        )
        .group_by(["Asset"])
        .aggregate(AggOp::Sum, Some("Amt"), "total")
        .aggregate(AggOp::Count, None::<String>, "n")
        .aggregate(AggOp::Max, Some("Amt"), "biggest");
    let rows = eval(&base, &q).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["Asset"], Value::sym("gold"));
    assert_eq!(rows[0]["total"], Value::nat(100)); // 30 + 70
    assert_eq!(rows[0]["n"], Value::nat(2));
    assert_eq!(rows[0]["biggest"], Value::nat(70));
}

#[test]
fn aggregate_global_count_no_group() {
    let base = extract_facts(&rich_chain());
    // ?- burned(...); count AS n. — one global row.
    let q = Query::new()
        .atom(
            Pred::Burned,
            vec![Term::Wild, Term::Wild, Term::var("A"), Term::Wild],
        )
        .aggregate(AggOp::Count, None::<String>, "n")
        .aggregate(AggOp::Min, Some("A"), "smallest");
    let rows = eval(&base, &q).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["n"], Value::nat(2));
    assert_eq!(rows[0]["smallest"], Value::nat(30));
}

#[test]
fn aggregate_grades_finalized_dependent() {
    // Aggregation is the second non-monotone operator: the value moves under
    // append (the sum grows as more burns arrive), so the query is
    // finalized-dependent even though every atom is monotone.
    let q = Query::new()
        .atom(
            Pred::Burned,
            vec![Term::Wild, Term::var("Asset"), Term::var("Amt"), Term::Wild],
        )
        .group_by(["Asset"])
        .aggregate(AggOp::Sum, Some("Amt"), "total");
    let c = classify(&q);
    assert_eq!(c.class, CoordinationClass::FinalizedDependent);
    assert!(c.reasons[0].contains("aggregate"));
}

#[test]
fn group_by_only_is_a_monotone_projection() {
    // group_by with NO aggregates is DISTINCT projection — still monotone.
    let base = extract_facts(&rich_chain());
    let q = Query::new()
        .atom(
            Pred::Burned,
            vec![
                Term::var("Cell"),
                Term::var("Asset"),
                Term::Wild,
                Term::Wild,
            ],
        )
        .group_by(["Asset"]);
    assert!(classify(&q).is_monotone());
    let rows = eval(&base, &q).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["Asset"], Value::sym("gold"));
    assert!(!rows[0].contains_key("Cell")); // projected away
}

#[test]
fn aggregate_validation_rejects_bad_shapes() {
    let base = extract_facts(&rich_chain());
    // Sum without an arg.
    let q = Query::new()
        .atom(
            Pred::Burned,
            vec![Term::Wild, Term::var("Asset"), Term::var("Amt"), Term::Wild],
        )
        .aggregate(AggOp::Sum, None::<String>, "total");
    assert!(matches!(
        eval(&base, &q),
        Err(QueryError::AggMissingArg { op: AggOp::Sum })
    ));
    // Output column collides with a positive variable.
    let q = Query::new()
        .atom(
            Pred::Burned,
            vec![Term::Wild, Term::var("Asset"), Term::var("Amt"), Term::Wild],
        )
        .aggregate(AggOp::Sum, Some("Amt"), "Amt");
    assert!(matches!(eval(&base, &q), Err(QueryError::AggCollision(_))));
    // Numeric aggregate over a symbol fails closed.
    let q = Query::new()
        .atom(
            Pred::Burned,
            vec![Term::Wild, Term::var("Asset"), Term::var("Amt"), Term::Wild],
        )
        .aggregate(AggOp::Sum, Some("Asset"), "bad");
    assert!(matches!(eval(&base, &q), Err(QueryError::AggType { .. })));
}

/// The certificate teeth bite over the AGGREGATE surface: an attested sum
/// verifies over the whole log, a tampered aggregate row is caught by
/// re-derivation, and an omitted burn receipt cannot produce a verifying
/// certificate (so the sum cannot be quietly understated).
#[test]
fn attested_aggregate_teeth_bite() {
    let receipts = rich_chain();
    let trusted_root = mmr_of(&receipts).root();
    let slice = attested_slice(&receipts, 0, 4);

    let q = Query::new()
        .atom(
            Pred::Burned,
            vec![Term::Wild, Term::var("Asset"), Term::var("Amt"), Term::Wild],
        )
        .group_by(["Asset"])
        .aggregate(AggOp::Sum, Some("Amt"), "total");

    let ans = answer_whole_log(slice, q.clone()).unwrap();
    assert_eq!(ans.rows.len(), 1);
    assert_eq!(ans.rows[0]["total"], Value::nat(100));
    // Aggregation ⇒ finalized-dependent, fresh as of the head height.
    assert!(!ans.classification.is_monotone());
    assert_eq!(ans.fresh_as_of, 5);
    ans.verify(&Blake3Mmr, &trusted_root).unwrap();

    // Tamper the aggregate value: re-derivation catches it.
    let mut lying = ans.clone();
    lying.rows[0].insert("total".into(), Value::nat(30));
    assert!(matches!(
        lying.verify(&Blake3Mmr, &trusted_root),
        Err(AttestError::RowsMismatch)
    ));

    // Hide a burn (position 2, the 70-unit burn) to understate the sum: the
    // re-indexed slice opens only against the server's OWN root, not trusted.
    let mut hidden: Vec<ReceiptRecord> = receipts
        .iter()
        .filter(|r| r.chain_index != 2)
        .cloned()
        .collect();
    for (i, r) in hidden.iter_mut().enumerate() {
        r.chain_index = i as u64;
    }
    let forged = attested_slice(&hidden, 0, 3);
    let understated = answer_whole_log(forged, q).unwrap();
    assert_eq!(understated.rows[0]["total"], Value::nat(30)); // the lie
    assert!(matches!(
        understated.verify(&Blake3Mmr, &trusted_root),
        Err(AttestError::UntrustedRoot)
    ));
}
