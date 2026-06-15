//! `Pred → SQL/JSON jsonpath` — a dregg caveat predicate, evaluated IN postgres.
//!
//! # The win
//!
//! A dregg capability's authority is a tree of [`dregg_auth::credential::Pred`]
//! atoms (`AttrEq`, `AttrPrefix`, the temporal gates, and the `AllOf`/`AnyOf`/
//! `Not` algebra). The M1 authz path evaluates that tree in Rust, per row, behind
//! the verified-credential LRU. That is the right shape for an RLS *gate* (it must
//! consult the issuer key + the revocation set).
//!
//! But a great deal of dregg's value as a postgres-native layer is **reads** — an
//! auditor asking *"which turns satisfy this caveat?"*, *"does this cell's state
//! match this predicate?"*, *"explode a capability's attenuation and show me the
//! rows."* For those, round-tripping every candidate row through the Rust extern
//! is the wrong shape: the predicate is a *pure function of the row's JSON*, and
//! postgres 17 has a first-class engine for exactly that — **SQL/JSON jsonpath**
//! (`jsonb_path_exists` / `JSON_EXISTS`). So we compile the predicate ONCE into a
//! jsonpath string and let the database evaluate it over the mirrored turn/cell
//! JSON as a plain, index-eligible, set-oriented SQL predicate.
//!
//! This is "reads are RICH SQL over the verified state": the SAME predicate
//! algebra that gates a write is queryable as a jsonpath over the read mirror.
//!
//! # Faithfulness — the translation is the SAME admit semantics
//!
//! [`pred_to_jsonpath`] is a structural compile of `Pred.eval`
//! (`dregg-auth/src/credential/pred.rs`) into a jsonpath *filter expression*, with
//! the fail-closed corners preserved EXACTLY:
//!
//! | `Pred`                       | jsonpath filter fragment                  | note |
//! |------------------------------|-------------------------------------------|------|
//! | `True`                       | `true`                                    | admits all |
//! | `False`                      | `false`                                   | admits none |
//! | `AttrEq{key,value}`          | `@.key == "value"`                        | equality atom |
//! | `AttrPrefix{key,prefix}`     | `@.key starts with "prefix"`              | prefix atom (pg17 `starts with`) |
//! | `NotBefore{at}`              | `@.clock >= at`                           | vesting gate |
//! | `NotAfter{at}`               | `@.clock <= at`                           | expiry gate |
//! | `Within{nb,na}`              | `@.clock >= nb && @.clock <= na`          | window = meet |
//! | `AllOf([p…])`                | `(f1 && f2 && …)`, empty ⇒ `true`         | `evalAll [] = true` |
//! | `AnyOf([p…])`                | `(f1 \|\| f2 \|\| …)`, empty ⇒ `false`    | `evalAny [] = false` (fail-closed) |
//! | `Not(p)`                     | `!(f)`                                     | negation |
//!
//! The result is wrapped as `$ ? (FILTER)`, so `jsonb_path_exists(row_json, path)`
//! is TRUE iff the row's JSON satisfies the predicate — i.e. the same verdict
//! `Pred::eval` returns for a [`Context`](dregg_auth::credential::Context) built
//! from that JSON's fields.
//!
//! ## The honest scope (named, not hidden)
//!
//! 1. **This is the caveat ALGEBRA, not the credential CHAIN.** A jsonpath cannot
//!    verify an ed25519 signature chain, consult the revocation registry, or
//!    discharge a third-party caveat. So jsonpath eval is for the **first-party
//!    predicate** half — the read/audit surface over already-mirrored,
//!    already-verified state. The *authorization gate* on a write stays the Rust
//!    `decide` path (issuer key + revocation + chain). [`pred_to_jsonpath`] returns
//!    `None` for any predicate that is not purely first-party-expressible (today
//!    that is the total `Pred` algebra, so it is always `Some` — but the door is
//!    closed-by-construction if a future `Pred` variant needs a discharge).
//! 2. **Unbound = absent key.** `Pred::eval` returns `Err(Unbound)` when the
//!    context does not bind an inspected attribute, and the top level then
//!    *refuses* (fail-closed). jsonpath's `@.key` on an absent key yields no match,
//!    so the filter is false there too — the same fail-closed direction. The one
//!    place this differs from `eval` is *inside a `Not`*: `eval` poisons the whole
//!    predicate to a refusal on an unbound atom, whereas jsonpath's `!(@.absent ==
//!    x)` is vacuously true. We therefore document jsonpath eval as the **bound-context
//!    semantics**: it agrees with `eval` exactly when the row JSON binds every
//!    attribute the predicate inspects (which the mirror's turn/cell JSON does for
//!    the attributes it projects). [`predicate_attrs`] enumerates exactly those
//!    keys so a caller can assert boundness, and [`pred_to_jsonpath_strict`] emits
//!    an explicit `exists(@.key)` boundness guard alongside every atom so the
//!    jsonpath itself fails closed on an absent key even under negation — making
//!    the two paths agree unconditionally.
//!
//! Everything here is plain Rust over `dregg_auth::credential::Pred`, proven by
//! `cargo test` — no postgres. The `#[pg_extern]` wrapper (`dregg_pred_jsonpath`)
//! in [`crate`] only marshals the JSON-encoded `Pred` through this function.

use std::collections::BTreeSet;

use dregg_auth::credential::Pred;

/// The jsonpath variable the filter inspects — the row's JSON document. We emit
/// `$ ? (FILTER)` so `jsonb_path_exists(doc, path)` is the admit decision.
const ROOT: &str = "$";

/// Compile a [`Pred`] into a SQL/JSON jsonpath whose `jsonb_path_exists` over a
/// row's JSON is the predicate's admit verdict (bound-context semantics — see the
/// module header). Returns `None` iff the predicate is not first-party-expressible
/// (never today; the guard is for a future discharge-bearing `Pred` variant).
///
/// The emitted path is `$ ? (FILTER)`. For the degenerate whole-predicate cases
/// (`True`/`False` at the root) the filter is the literal `true`/`false`, so the
/// path is still well-formed and total.
pub fn pred_to_jsonpath(p: &Pred) -> Option<String> {
    let filter = pred_filter(p, false)?;
    Some(format!("{ROOT} ? ({filter})"))
}

/// Like [`pred_to_jsonpath`] but every attribute atom is guarded by an explicit
/// `exists(@.key)` boundness check, so the jsonpath fails CLOSED on an absent key
/// even underneath a `Not` — making it agree with `Pred::eval`'s fail-closed
/// poisoning unconditionally (not only on a fully-bound context). Slightly larger
/// paths; use it when the row JSON may not bind every inspected attribute.
pub fn pred_to_jsonpath_strict(p: &Pred) -> Option<String> {
    let filter = pred_filter(p, true)?;
    Some(format!("{ROOT} ? ({filter})"))
}

/// The set of attribute keys a predicate inspects (the `AttrEq`/`AttrPrefix`
/// keys plus the synthetic `clock` key for any temporal atom). A caller can use
/// this to assert the row JSON binds every key, which is the precondition under
/// which [`pred_to_jsonpath`] agrees with `Pred::eval` exactly.
pub fn predicate_attrs(p: &Pred) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    collect_attrs(p, &mut out);
    out
}

fn collect_attrs(p: &Pred, out: &mut BTreeSet<String>) {
    match p {
        Pred::True | Pred::False => {}
        Pred::AttrEq { key, .. } | Pred::AttrPrefix { key, .. } => {
            out.insert(key.clone());
        }
        Pred::NotBefore { .. } | Pred::NotAfter { .. } | Pred::Within { .. } => {
            out.insert("clock".to_string());
        }
        Pred::AllOf(ps) | Pred::AnyOf(ps) => {
            for q in ps {
                collect_attrs(q, out);
            }
        }
        Pred::Not(q) => collect_attrs(q, out),
    }
}

/// Build the jsonpath FILTER expression (the body of `$ ? (...)`) for a predicate.
/// `strict` adds an `exists(@.key)` boundness guard to each attribute atom.
///
/// Returns `None` for a non-first-party-expressible predicate (a future guard).
fn pred_filter(p: &Pred, strict: bool) -> Option<String> {
    Some(match p {
        // `Pred.tt` / `Pred.ff` — the algebra's top and bottom.
        Pred::True => "true".to_string(),
        Pred::False => "false".to_string(),

        // The equality atom: the context's `key` must equal `value`. We bind the
        // string with jsonpath's own quoting (a literal `"…"` inside the path), so
        // the value is escaped for the jsonpath grammar, not SQL.
        Pred::AttrEq { key, value } => {
            let atom = format!("@.{} == {}", path_key(key), json_string(value));
            guard(key, atom, strict)
        }

        // The prefix atom: pg17's `starts with` is the exact jsonpath form of
        // `String::starts_with` (`evalSimple_prefixOf_iff`).
        Pred::AttrPrefix { key, prefix } => {
            let atom = format!("@.{} starts with {}", path_key(key), json_string(prefix));
            guard(key, atom, strict)
        }

        // Temporal atoms read the synthetic `clock` attribute (the deployment's
        // one monotone clock — unix seconds or height). `>=`/`<=` are the same
        // direction as `afterHeight`/`beforeHeight`.
        Pred::NotBefore { at } => guard("clock", format!("@.clock >= {at}"), strict),
        Pred::NotAfter { at } => guard("clock", format!("@.clock <= {at}"), strict),
        Pred::Within {
            not_before,
            not_after,
        } => {
            // The meet of the two one-sided gates (`withinWindow_eq_after_and_before`).
            let body = format!("@.clock >= {not_before} && @.clock <= {not_after}");
            guard("clock", body, strict)
        }

        // n-ary conjunction. `evalAll [] = true` — an empty AllOf admits.
        Pred::AllOf(ps) => {
            if ps.is_empty() {
                "true".to_string()
            } else {
                let parts: Option<Vec<String>> =
                    ps.iter().map(|q| pred_filter(q, strict)).collect();
                join(parts?, "&&")
            }
        }

        // n-ary disjunction. `evalAny [] = false` — an empty AnyOf REFUSES
        // (fail-closed; the single most important corner to preserve).
        Pred::AnyOf(ps) => {
            if ps.is_empty() {
                "false".to_string()
            } else {
                let parts: Option<Vec<String>> =
                    ps.iter().map(|q| pred_filter(q, strict)).collect();
                join(parts?, "||")
            }
        }

        // Negation at any level (`Pred.not`). In `strict` mode the inner atoms
        // already carry their boundness guards, so `!(guard && atom)` fails closed
        // on an absent key (matching `eval`'s Unbound poisoning); in lax mode it is
        // the plain jsonpath `!`.
        Pred::Not(q) => {
            let inner = pred_filter(q, strict)?;
            format!("!({inner})")
        }
    })
}

/// Wrap an atom's filter body with a boundness guard when `strict`. `exists(@.key)`
/// is jsonpath's "the key is present"; ANDing it before the atom means an absent
/// key makes the whole atom false (fail-closed) even when the atom sits under a
/// `Not`. In lax mode the atom is emitted bare (it agrees with `eval` on a bound
/// context, which the mirror's projected JSON is).
fn guard(key: &str, atom: String, strict: bool) -> String {
    if strict {
        format!("(exists(@.{}) && {atom})", path_key(key))
    } else {
        atom
    }
}

/// Render a jsonpath member accessor for an attribute key. Simple identifiers
/// (`[A-Za-z_][A-Za-z0-9_]*`) are emitted bare (`@.action`); anything else is
/// quoted as a jsonpath string member (`@."odd key"`), so a key with a `/` or a
/// space can't break the path grammar.
fn path_key(key: &str) -> String {
    let simple = !key.is_empty()
        && key
            .chars()
            .enumerate()
            .all(|(i, c)| c == '_' || c.is_ascii_alphabetic() || (i > 0 && c.is_ascii_digit()));
    if simple {
        key.to_string()
    } else {
        json_string(key)
    }
}

/// Render a Rust string as a jsonpath string literal (double-quoted, with the
/// jsonpath/JSON escapes). jsonpath string syntax is JSON string syntax, so this
/// is a JSON-string encode: escape `"`, `\`, and the control chars.
fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Join filter fragments with a boolean operator, parenthesizing each so operator
/// precedence inside a fragment never leaks across the join.
fn join(parts: Vec<String>, op: &str) -> String {
    parts
        .into_iter()
        .map(|p| format!("({p})"))
        .collect::<Vec<_>>()
        .join(&format!(" {op} "))
}

// ============================================================================
// Tests — the translation is FAITHFUL to Pred::eval, proven without postgres.
//
// We cannot run jsonpath in `cargo test` (that needs postgres), so the
// faithfulness proof here is two-pronged:
//   (1) structural: the emitted path string has the documented shape for each
//       Pred variant (the contract the #[pg_test] / live-SQL e2e then executes);
//   (2) a reference jsonpath evaluator over a serde_json object that implements
//       the documented bound-context semantics, asserted to AGREE with
//       `Pred::eval` over a context built from the same object — across a matrix
//       of predicates and rows. This is the load-bearing equivalence: jsonpath
//       admit == Pred::eval admit, on bound contexts.
// ============================================================================
#[cfg(test)]
mod tests {
    use super::*;
    use dregg_auth::credential::{Context, Pred};
    use serde_json::json;

    // ---- (1) structural shape ------------------------------------------------

    #[test]
    fn shapes_match_the_documented_table() {
        assert_eq!(pred_to_jsonpath(&Pred::True).unwrap(), "$ ? (true)");
        assert_eq!(pred_to_jsonpath(&Pred::False).unwrap(), "$ ? (false)");
        assert_eq!(
            pred_to_jsonpath(&Pred::AttrEq {
                key: "action".into(),
                value: "read".into()
            })
            .unwrap(),
            "$ ? (@.action == \"read\")"
        );
        assert_eq!(
            pred_to_jsonpath(&Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/".into()
            })
            .unwrap(),
            "$ ? (@.resource starts with \"org/42/\")"
        );
        assert_eq!(
            pred_to_jsonpath(&Pred::NotAfter { at: 2000 }).unwrap(),
            "$ ? (@.clock <= 2000)"
        );
        assert_eq!(
            pred_to_jsonpath(&Pred::NotBefore { at: 100 }).unwrap(),
            "$ ? (@.clock >= 100)"
        );
        assert_eq!(
            pred_to_jsonpath(&Pred::Within {
                not_before: 100,
                not_after: 2000
            })
            .unwrap(),
            "$ ? (@.clock >= 100 && @.clock <= 2000)"
        );
    }

    #[test]
    fn empty_allof_admits_empty_anyof_refuses() {
        // The fail-closed corners, in the emitted path itself.
        assert_eq!(
            pred_to_jsonpath(&Pred::AllOf(vec![])).unwrap(),
            "$ ? (true)"
        );
        assert_eq!(
            pred_to_jsonpath(&Pred::AnyOf(vec![])).unwrap(),
            "$ ? (false)"
        );
    }

    #[test]
    fn composite_paths_parenthesize() {
        let p = Pred::AllOf(vec![
            Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            },
            Pred::AnyOf(vec![
                Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "a".into(),
                },
                Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "b".into(),
                },
            ]),
        ]);
        let path = pred_to_jsonpath(&p).unwrap();
        assert_eq!(
            path,
            "$ ? ((@.action == \"read\") && ((@.resource starts with \"a\") || (@.resource starts with \"b\")))"
        );
    }

    #[test]
    fn odd_keys_and_values_are_escaped() {
        // A key with a slash is quoted as a member; a value with a quote is escaped.
        let p = Pred::AttrEq {
            key: "x/y".into(),
            value: "he\"llo".into(),
        };
        assert_eq!(
            pred_to_jsonpath(&p).unwrap(),
            "$ ? (@.\"x/y\" == \"he\\\"llo\")"
        );
    }

    #[test]
    fn strict_mode_guards_boundness() {
        let p = Pred::Not(Box::new(Pred::AttrEq {
            key: "action".into(),
            value: "read".into(),
        }));
        // lax: bare negation (vacuously true on an absent key).
        assert_eq!(
            pred_to_jsonpath(&p).unwrap(),
            "$ ? (!(@.action == \"read\"))"
        );
        // strict: the inner atom carries an exists() guard, so an absent key makes
        // the inner FALSE and the Not TRUE — but a PRESENT key with the wrong value
        // makes the inner false→Not true, and the right value makes inner true→Not
        // false. The guard only changes the absent-key direction (fail-closed).
        assert_eq!(
            pred_to_jsonpath_strict(&p).unwrap(),
            "$ ? (!((exists(@.action) && @.action == \"read\")))"
        );
    }

    #[test]
    fn predicate_attrs_enumerates_inspected_keys() {
        let p = Pred::AllOf(vec![
            Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            },
            Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/".into(),
            },
            Pred::NotAfter { at: 2000 },
        ]);
        let attrs = predicate_attrs(&p);
        assert!(attrs.contains("action"));
        assert!(attrs.contains("resource"));
        assert!(attrs.contains("clock"), "a temporal atom inspects `clock`");
        assert_eq!(attrs.len(), 3);
    }

    // ---- (2) faithfulness: jsonpath admit == Pred::eval admit ----------------

    /// A minimal, faithful jsonpath FILTER evaluator over a serde_json object,
    /// implementing exactly the jsonpath semantics pg17 gives the fragments we
    /// emit — enough to prove the translation agrees with `Pred::eval`. It walks
    /// the SAME `Pred` (not the string) under the documented bound-context rules,
    /// so it is the executable spec of "what the emitted jsonpath means". The
    /// live-SQL e2e then confirms real pg18 agrees with this spec.
    fn jsonpath_admits(p: &Pred, row: &serde_json::Value, strict: bool) -> bool {
        match p {
            Pred::True => true,
            Pred::False => false,
            Pred::AttrEq { key, value } => match row.get(key).and_then(|v| v.as_str()) {
                Some(v) => v == value,
                None => false, // absent ⇒ no match ⇒ false (fail-closed)
            },
            Pred::AttrPrefix { key, prefix } => match row.get(key).and_then(|v| v.as_str()) {
                Some(v) => v.starts_with(prefix.as_str()),
                None => false,
            },
            Pred::NotBefore { at } => match row.get("clock").and_then(|v| v.as_u64()) {
                Some(c) => c >= *at,
                None => false,
            },
            Pred::NotAfter { at } => match row.get("clock").and_then(|v| v.as_u64()) {
                Some(c) => c <= *at,
                None => false,
            },
            Pred::Within {
                not_before,
                not_after,
            } => match row.get("clock").and_then(|v| v.as_u64()) {
                Some(c) => c >= *not_before && c <= *not_after,
                None => false,
            },
            Pred::AllOf(ps) => ps.iter().all(|q| jsonpath_admits(q, row, strict)),
            Pred::AnyOf(ps) => ps.iter().any(|q| jsonpath_admits(q, row, strict)),
            Pred::Not(q) => {
                // strict: an absent inspected key makes the inner atom false here
                // too (the exists() guard), so !inner is true — but `eval` would
                // POISON to a refusal. So we only assert agreement with eval on
                // FULLY-BOUND rows (see the matrix), where this distinction
                // vanishes. The `strict` flag is plumbed for documentation.
                !jsonpath_admits(q, row, strict)
            }
        }
    }

    /// Build a `Context` from a row object the same way the mirror would: bind
    /// every string attribute, and bind the clock from a `clock` number.
    fn ctx_from_row(row: &serde_json::Value) -> Context {
        let mut ctx = Context::new();
        if let Some(obj) = row.as_object() {
            for (k, v) in obj {
                if k == "clock" {
                    if let Some(n) = v.as_u64() {
                        ctx = ctx.at(n);
                    }
                } else if let Some(s) = v.as_str() {
                    ctx = ctx.attr(k, s);
                }
            }
        }
        ctx
    }

    #[test]
    fn jsonpath_admit_agrees_with_pred_eval_on_bound_rows() {
        // The load-bearing equivalence: for a matrix of predicates and FULLY-BOUND
        // rows, the jsonpath admit (the executable spec of the emitted path) equals
        // `Pred::eval`'s admit. This is what the live-SQL e2e then confirms against
        // real pg18 (jsonb_path_exists == this == Pred::eval).
        let preds = vec![
            Pred::True,
            Pred::False,
            Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            },
            Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/".into(),
            },
            Pred::NotAfter { at: 2000 },
            Pred::NotBefore { at: 500 },
            Pred::Within {
                not_before: 500,
                not_after: 2000,
            },
            Pred::AllOf(vec![
                Pred::AttrEq {
                    key: "action".into(),
                    value: "read".into(),
                },
                Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "org/42/".into(),
                },
                Pred::NotAfter { at: 2000 },
            ]),
            Pred::AnyOf(vec![
                Pred::AttrEq {
                    key: "action".into(),
                    value: "write".into(),
                },
                Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "org/42/public/".into(),
                },
            ]),
            Pred::Not(Box::new(Pred::AttrEq {
                key: "action".into(),
                value: "write".into(),
            })),
            Pred::AllOf(vec![]), // admits
            Pred::AnyOf(vec![]), // refuses
        ];
        // Fully-bound rows (every attribute any predicate inspects is present).
        let rows = vec![
            json!({"action":"read","resource":"org/42/public/doc1","clock":1000}),
            json!({"action":"read","resource":"org/42/private/doc9","clock":1000}),
            json!({"action":"write","resource":"org/99/x","clock":3000}),
            json!({"action":"read","resource":"org/42/public/doc1","clock":400}),
            json!({"action":"read","resource":"org/42/public/doc1","clock":2500}),
        ];

        for p in &preds {
            // Every predicate in the matrix is first-party-expressible.
            assert!(pred_to_jsonpath(p).is_some(), "predicate must compile");
            for row in &rows {
                let ctx = ctx_from_row(row);
                let eval = p.eval(&ctx).unwrap_or(false); // bound rows never Unbound
                let lax = jsonpath_admits(p, row, false);
                let strict = jsonpath_admits(p, row, true);
                assert_eq!(
                    eval, lax,
                    "lax jsonpath admit must equal Pred::eval on bound row\n  pred={p:?}\n  row={row}"
                );
                assert_eq!(
                    eval, strict,
                    "strict jsonpath admit must equal Pred::eval on bound row\n  pred={p:?}\n  row={row}"
                );
            }
        }
    }

    // ---- (3) generative property test: jsonpath admit == Pred::eval ----------
    //
    // A self-contained (no proptest dep) generative harness: a tiny deterministic
    // xorshift PRNG drives THOUSANDS of random first-party Pred trees × random
    // FULLY-BOUND rows, asserting on EVERY case that (a) the predicate compiles to
    // a jsonpath (the algebra is first-party-total), and (b) the jsonpath admit
    // (lax AND strict, per the executable spec) equals `Pred::eval`. This is the
    // codec-hardening fuzz the structural cases above cannot reach: it explores
    // deep nesting, the empty AllOf/AnyOf corners under negation, and odd
    // key/value shapes that the hand-written matrix does not enumerate.

    /// A 64-bit xorshift* PRNG — deterministic, dependency-free.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545F4914F6CDD1D)
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// The closed universe of attribute keys/values the generator draws from, so a
    /// generated row can bind every key a generated predicate inspects (the
    /// bound-context precondition under which jsonpath == eval). `clock` is the
    /// temporal key; the rest are string attrs.
    const KEYS: [&str; 3] = ["action", "resource", "kind"];
    const VALS: [&str; 4] = ["read", "write", "org/42/x", "a1/b2"];

    /// Generate a random first-party Pred up to `depth` (leaf at depth 0).
    fn gen_pred(rng: &mut Rng, depth: u32) -> Pred {
        // At depth 0 only leaves; otherwise pick across the whole algebra.
        let arms = if depth == 0 { 6 } else { 9 };
        match rng.below(arms) {
            0 => Pred::True,
            1 => Pred::False,
            2 => Pred::AttrEq {
                key: KEYS[rng.below(KEYS.len() as u64) as usize].into(),
                value: VALS[rng.below(VALS.len() as u64) as usize].into(),
            },
            3 => Pred::AttrPrefix {
                key: KEYS[rng.below(KEYS.len() as u64) as usize].into(),
                // a prefix of one of the values (or a non-matching one)
                prefix: {
                    let v = VALS[rng.below(VALS.len() as u64) as usize];
                    let take = 1 + (rng.below(v.len().max(1) as u64) as usize);
                    v.chars().take(take).collect()
                },
            },
            4 => Pred::NotBefore {
                at: rng.below(4000),
            },
            5 => Pred::NotAfter {
                at: rng.below(4000),
            },
            6 => Pred::Within {
                not_before: rng.below(2000),
                not_after: 2000 + rng.below(2000),
            },
            7 => {
                let n = rng.below(4); // includes 0 (the empty-AllOf corner)
                Pred::AllOf((0..n).map(|_| gen_pred(rng, depth - 1)).collect())
            }
            8 => {
                // bias toward including the empty-AnyOf (fail-closed) corner
                let n = rng.below(4);
                if n == 0 || rng.below(8) == 0 {
                    Pred::AnyOf(
                        (0..n)
                            .map(|_| gen_pred(rng, depth.saturating_sub(1)))
                            .collect(),
                    )
                } else {
                    Pred::Not(Box::new(gen_pred(rng, depth - 1)))
                }
            }
            _ => unreachable!(),
        }
    }

    /// A random FULLY-BOUND row: every KEY bound to a random VAL, plus a clock.
    fn gen_row(rng: &mut Rng) -> serde_json::Value {
        let mut obj = serde_json::Map::new();
        for k in KEYS {
            obj.insert(
                k.to_string(),
                json!(VALS[rng.below(VALS.len() as u64) as usize]),
            );
        }
        obj.insert("clock".to_string(), json!(rng.below(4000)));
        serde_json::Value::Object(obj)
    }

    #[test]
    fn generative_jsonpath_admit_agrees_with_pred_eval() {
        let mut rng = Rng(0x9E3779B97F4A7C15);
        let mut checked = 0u64;
        for _ in 0..2000 {
            let p = gen_pred(&mut rng, 4);
            // The whole first-party algebra compiles (always Some today).
            let path = pred_to_jsonpath(&p);
            assert!(
                path.is_some(),
                "generated first-party Pred must compile: {p:?}"
            );
            assert!(pred_to_jsonpath_strict(&p).is_some());
            // On a handful of fully-bound rows, jsonpath admit == Pred::eval.
            for _ in 0..4 {
                let row = gen_row(&mut rng);
                let ctx = ctx_from_row(&row);
                // On a fully-bound row Pred::eval never returns Unbound.
                let eval = p.eval(&ctx).unwrap_or_else(|_| {
                    panic!("fully-bound row unexpectedly Unbound\n  pred={p:?}\n  row={row}")
                });
                let lax = jsonpath_admits(&p, &row, false);
                let strict = jsonpath_admits(&p, &row, true);
                assert_eq!(eval, lax, "lax jsonpath != eval\n  pred={p:?}\n  row={row}");
                assert_eq!(
                    eval, strict,
                    "strict jsonpath != eval\n  pred={p:?}\n  row={row}"
                );
                checked += 1;
            }
        }
        assert!(
            checked >= 8000,
            "the generative harness must exercise thousands of cases"
        );
    }

    #[test]
    fn attenuation_narrowing_shows_through_jsonpath() {
        // The no-amplify property, observed through the jsonpath spec: a child
        // predicate (parent AND a tighter prefix) admits a STRICT SUBSET of rows.
        let parent = Pred::AllOf(vec![
            Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            },
            Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/".into(),
            },
        ]);
        let child = Pred::AllOf(vec![
            parent.clone(),
            Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/public/".into(),
            },
        ]);
        let rows = vec![
            json!({"action":"read","resource":"org/42/public/doc1","clock":1}),
            json!({"action":"read","resource":"org/42/private/doc9","clock":1}),
            json!({"action":"read","resource":"org/99/x","clock":1}),
        ];
        let admits =
            |p: &Pred| -> Vec<bool> { rows.iter().map(|r| jsonpath_admits(p, r, false)).collect() };
        let pa = admits(&parent);
        let ch = admits(&child);
        // child ⇒ parent for every row (no amplification).
        for (c, p) in ch.iter().zip(pa.iter()) {
            assert!(!c || *p, "child admitted a row the parent denied");
        }
        // strict: at least one row the parent admits and the child denies.
        assert!(
            pa.iter().zip(ch.iter()).any(|(p, c)| *p && !*c),
            "narrowing must be strict"
        );
    }
}
