//! # pg-dregg — dregg verified object-capability authorization for PostgreSQL RLS
//!
//! An ordinary postgres-heavy app gates rows with dregg capabilities instead of
//! hand-rolled SQL RLS predicates. The SAME `dga1_…` token authorizes against
//! the dregg kernel and against your plain tables.
//!
//! ## Two layers, one decision
//!
//! * [`core`] — the postgres-independent authorization CORE: decode + verify a
//!   credential (delegated to the proven [`dregg_auth::credential`]), the
//!   verified-credential LRU, the instant-revocation registry, and the caveat /
//!   attenuation-narrowing evaluation. Proven by plain `cargo test` (no
//!   postgres). This is where the M1 thesis is verified.
//! * the `#[pg_extern]` wrappers below (gated behind the `pgrx` feature) — thin
//!   marshalling of SQL `text`/`bigint` into [`core`] calls, plus the
//!   `dregg.issuer_pubkey` GUC and the convenience `dregg_admits` wrapper.
//!
//! ## The assurance boundary (docs/PG-DREGG.md §4)
//!
//! The *capability decision* a policy makes is the verified dregg decision (the
//! Lean↔Rust differential on `dregg-auth` is the anchor). The *integration* —
//! the GUC plumbing, the LRU, the revocation registry, the per-row invocation —
//! is conventional extension code, tested directly in [`core`]. We do not claim
//! the postgres layer is formally verified; we name the seam.

pub mod authz;
pub mod mirror;

// The PG_MODULE_MAGIC block + the `__pgrx_marker` the schema generator links
// against MUST live at the crate ROOT (cargo-pgrx's pgrx_embed binary calls
// `pg_dregg::__pgrx_marker`). Feature-gated so the core build never sees it.
#[cfg(feature = "pgrx")]
pgrx::pg_module_magic!();

// ===========================================================================
// The postgres extension surface. Compiled only with the `pgrx` feature (which
// the pgNN features turn on); `cargo test` builds none of this.
// ===========================================================================
#[cfg(feature = "pgrx")]
mod pg {
    use crate::authz;
    use pgrx::guc::{GucContext, GucFlags, GucRegistry, GucSetting};
    use pgrx::prelude::*;

    // -----------------------------------------------------------------------
    // Issuer public key — the database trust root (docs/PG-DREGG.md §3.3).
    //
    // The PUBLIC key is publishable, so the GUC is DBA-visible/settable
    // (`GucContext::Sighup`). The PRIVATE key never lives in postgres. A
    // malformed/absent key makes every decision DENY (fail-closed).
    // -----------------------------------------------------------------------
    static ISSUER_PUBKEY: GucSetting<Option<std::ffi::CString>> =
        GucSetting::<Option<std::ffi::CString>>::new(None);

    #[pg_guard]
    pub extern "C-unwind" fn _PG_init() {
        GucRegistry::define_string_guc(
            c"dregg.issuer_pubkey",
            c"The dregg issuer PUBLIC key (64 hex chars). The database trust root.",
            c"Verification uses only the public key; the private key never enters postgres. \
              A malformed or absent key makes every dregg_cap_admits DENY (fail-closed).",
            &ISSUER_PUBKEY,
            GucContext::Sighup,
            GucFlags::empty(),
        );
    }

    /// Pull the issuer key from the GUC into the process-local core slot. Called
    /// at the head of every decision so a SIGHUP-changed key takes effect. Cheap
    /// (a hex parse); on a malformed/absent key it clears the slot ⇒ deny.
    fn sync_issuer_key() {
        match ISSUER_PUBKEY.get() {
            Some(cstring) => {
                let hex = cstring.to_str().unwrap_or("");
                authz::set_issuer_pubkey_hex(hex);
            }
            None => {
                // No key configured ⇒ ensure the slot reflects "deny".
                authz::clear_issuer_pubkey();
            }
        }
    }

    // -----------------------------------------------------------------------
    // The core decision (docs/PG-DREGG.md §2.1, §3.1).
    //
    // VOLATILITY: STABLE, not IMMUTABLE. See docs/PG-DREGG.md §6 + the report.
    // The decision depends on the revocation registry, which can change WITHIN a
    // statement (instant revocation, ember decision #1). An IMMUTABLE function
    // promises the planner the same inputs always give the same output and may
    // be folded/cached across rows; that is UNSOUND once revocation can flip a
    // verdict mid-statement. STABLE (constant within a single statement's
    // snapshot, may differ across statements) is the correct, sound class.
    // STRICT: a NULL token ⇒ NULL ⇒ the policy treats it as deny.
    // -----------------------------------------------------------------------

    /// `dregg_cap_admits(token, action, resource, now) -> bool`. TRUE iff the
    /// credential admits `action` on `resource` at `now`, verified offline
    /// against the configured issuer key, not revoked. Fail-closed.
    #[pg_extern(stable, parallel_safe, strict)]
    fn dregg_cap_admits(token: &str, action: &str, resource: &str, now: i64) -> bool {
        sync_issuer_key();
        authz::decide(token, action, resource, now).allowed()
    }

    /// `dregg_cap_explain(...) -> text`. The human-readable decision reason —
    /// `"allowed"`, or the first violated requirement (or "revoked" / "no issuer
    /// key configured"). For debugging policies and audit logging.
    #[pg_extern(stable, parallel_safe)]
    fn dregg_cap_explain(
        token: Option<&str>,
        action: &str,
        resource: &str,
        now: i64,
    ) -> Option<String> {
        let token = token?;
        sync_issuer_key();
        Some(authz::explain(token, action, resource, now))
    }

    /// `dregg_cap_subject(token) -> text`. The confined subject the token names,
    /// or NULL if the token's chain does not verify under the issuer key.
    #[pg_extern(stable, parallel_safe)]
    fn dregg_cap_subject(token: Option<&str>) -> Option<String> {
        let token = token?;
        sync_issuer_key();
        authz::subject(token)
    }

    /// `dregg_cap_id(token) -> text`. The stable per-credential id (hex of the
    /// chain-committing tail) the revocation registry keys on, or NULL if the
    /// token does not decode. Use it to populate `dregg.revoked`.
    #[pg_extern(immutable, parallel_safe)]
    fn dregg_cap_id(token: Option<&str>) -> Option<String> {
        authz::cap_id(token?)
    }

    /// `dregg_revoke(token) -> text`. Revoke the presented credential
    /// (extension-layer registry; backend-local). Returns the revoked id, or
    /// NULL if the token does not decode. In a clustered deployment this would
    /// write the `dregg.revoked` table; here it mirrors into the backend-local
    /// set the per-row check consults.
    #[pg_extern]
    fn dregg_revoke(token: Option<&str>) -> Option<String> {
        let id = authz::cap_id(token?)?;
        authz::revoke(&id);
        Some(id)
    }

    /// `dregg_unrevoke(id text) -> bool`. Lift a revocation by id.
    #[pg_extern]
    fn dregg_unrevoke(id: &str) -> bool {
        authz::unrevoke(id);
        true
    }

    // -----------------------------------------------------------------------
    // The terse convenience wrapper — reads the session GUC + clock so RLS
    // policies stay readable. STABLE (reads now() and the GUC).
    // -----------------------------------------------------------------------

    /// `dregg_admits(action, resource) -> bool`. Reads `current_setting(
    /// 'dregg.token', true)` and `now()`; the ergonomic face for
    /// `USING (dregg_admits('read', id::text))`.
    #[pg_extern(stable, parallel_safe)]
    fn dregg_admits(action: &str, resource: &str) -> bool {
        // current_setting('dregg.token', true) — missing-ok ⇒ NULL ⇒ deny.
        let token: Option<String> = Spi::get_one_with_args(
            "SELECT current_setting('dregg.token', true)",
            &[],
        )
        .unwrap_or(None);
        let Some(token) = token else { return false };
        // unix seconds: extract(epoch from now())::bigint
        let now: i64 = Spi::get_one("SELECT extract(epoch from now())::bigint")
            .ok()
            .flatten()
            .unwrap_or(0);
        sync_issuer_key();
        authz::decide(&token, action, resource, now).allowed()
    }

    // =======================================================================
    // #[pg_test]s — the M1 thesis THROUGH the SQL boundary.
    //
    // These run under `cargo pgrx test pgNN` against a managed postgres. They
    // mirror the core's cargo-test proofs, but observed through real SQL: an
    // RLS-gated table queried under a session GUC, as an unprivileged role so
    // the policy actually filters (superusers BYPASS RLS).
    //
    // The issuer key is configured at server start (crate::pg_test::
    // postgresql_conf_options — the Sighup path), and tokens are minted in Rust
    // (dregg_mint SQL is out of M1 scope, docs §5) and handed to SQL as text.
    // =======================================================================
    #[cfg(any(test, feature = "pg_test"))]
    #[pg_schema]
    mod tests {
        use super::*;
        use dregg_auth::credential::{Caveat, Pred, RootKey};

        fn root() -> RootKey {
            RootKey::from_seed([7u8; 32])
        }

        fn mint_org42(root: &RootKey) -> dregg_auth::credential::Credential {
            root.mint([
                Caveat::FirstParty(Pred::AttrEq {
                    key: "subject".into(),
                    value: "agent-1".into(),
                }),
                Caveat::FirstParty(Pred::AttrEq {
                    key: "action".into(),
                    value: "read".into(),
                }),
                Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "org/42/".into(),
                }),
                Caveat::FirstParty(Pred::NotAfter { at: 2000 }),
            ])
        }

        /// The issuer key is configured at server start by
        /// `crate::pg_test::postgresql_conf_options` (the `dregg.issuer_pubkey`
        /// GUC is `Sighup` — secure: a session cannot SET it to a key it
        /// controls and forge admits). All tests mint under the SAME fixed seed
        /// `[7u8; 32]`, whose public key is the configured one; this asserts the
        /// configured key matches, so the test is honest about what is trusted.
        fn assert_issuer(root: &RootKey) {
            let configured: Option<String> =
                Spi::get_one("SELECT current_setting('dregg.issuer_pubkey', true)").unwrap();
            assert_eq!(
                configured.as_deref(),
                Some(root.public().to_hex().as_str()),
                "the server's configured issuer key must be the test root's public key"
            );
        }

        #[pg_test]
        fn admits_and_attenuation_narrows_through_sql() {
            let root = root();
            assert_issuer(&root);
            let root_tok = mint_org42(&root).encode();
            let narrowed = mint_org42(&root)
                .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "org/42/public/".into(),
                })])
                .encode();

            // Direct dregg_cap_admits over the SQL boundary.
            let f = |t: &str, r: &str, n: i64| -> bool {
                Spi::get_one_with_args(
                    "SELECT dregg_cap_admits($1, 'read', $2, $3)",
                    &[t.into(), r.into(), n.into()],
                )
                .unwrap()
                .unwrap()
            };
            assert!(f(&root_tok, "org/42/private/doc9", 1000));
            assert!(f(&narrowed, "org/42/public/doc1", 1000));
            assert!(!f(&narrowed, "org/42/private/doc9", 1000)); // narrowing held
            assert!(!f(&narrowed, "org/42/public/doc1", 3000)); // past NotAfter
        }

        #[pg_test]
        fn rls_gated_table_narrows_row_visibility() {
            let root = root();
            assert_issuer(&root);

            // A documents table gated by a dregg capability.
            Spi::run(
                "CREATE TABLE documents (id text primary key);
                 INSERT INTO documents VALUES
                   ('org/42/public/doc1'),
                   ('org/42/public/doc2'),
                   ('org/42/private/doc9'),
                   ('org/99/public/doc1');
                 ALTER TABLE documents ENABLE ROW LEVEL SECURITY;
                 ALTER TABLE documents FORCE ROW LEVEL SECURITY;
                 CREATE POLICY cap_read ON documents FOR SELECT
                   USING (dregg_admits('read', id::text));
                 -- RLS is BYPASSED by superusers; query as an unprivileged role
                 -- so the policy actually filters. The role needs SELECT + the
                 -- right to read the dregg.token GUC (any role can read a custom
                 -- GUC it set itself).
                 CREATE ROLE app_reader NOLOGIN;
                 GRANT SELECT ON documents TO app_reader;",
            )
            .unwrap();

            let root_tok = mint_org42(&root).encode();
            let narrowed = mint_org42(&root)
                .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "org/42/public/".into(),
                })])
                .encode();

            // The clock the policy reads is now(); the token expires at 2000
            // (unix seconds), which is in the past, so we set a token that does
            // NOT expire for this visibility test — re-mint without NotAfter so
            // wall-clock now() does not trip the temporal caveat.
            let mk = |prefix: Option<&str>| -> String {
                let mut c = root.mint([
                    Caveat::FirstParty(Pred::AttrEq {
                        key: "action".into(),
                        value: "read".into(),
                    }),
                    Caveat::FirstParty(Pred::AttrPrefix {
                        key: "resource".into(),
                        prefix: "org/42/".into(),
                    }),
                ]);
                if let Some(p) = prefix {
                    c = c.attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                        key: "resource".into(),
                        prefix: p.into(),
                    })]);
                }
                c.encode()
            };
            let _ = (root_tok, narrowed); // the expiring ones exercise the direct test

            let count_under = |tok: &str| -> i64 {
                Spi::run(&format!("SET dregg.token = '{tok}'")).unwrap();
                // SET ROLE to the unprivileged reader so RLS is enforced; reset
                // after counting.
                Spi::run("SET ROLE app_reader").unwrap();
                let n = Spi::get_one::<i64>("SELECT count(*) FROM documents")
                    .unwrap()
                    .unwrap();
                Spi::run("RESET ROLE").unwrap();
                n
            };

            // Root token sees all three org/42 rows (not the org/99 one).
            let n_root = count_under(&mk(None));
            // Narrowed token sees ONLY the two org/42/public rows — a STRICT
            // subset. The no-amplify property, observed through real RLS.
            let n_narrow = count_under(&mk(Some("org/42/public/")));
            assert_eq!(n_root, 3, "root token should see the three org/42 rows");
            assert_eq!(n_narrow, 2, "narrowed token should see only org/42/public");
            assert!(n_narrow < n_root, "attenuation must strictly narrow visibility");
        }

        #[pg_test]
        fn instant_revocation_makes_rows_vanish() {
            let root = root();
            assert_issuer(&root);
            Spi::run(
                "CREATE TABLE docs2 (id text primary key);
                 INSERT INTO docs2 VALUES ('org/42/public/a'), ('org/42/public/b');
                 ALTER TABLE docs2 ENABLE ROW LEVEL SECURITY;
                 ALTER TABLE docs2 FORCE ROW LEVEL SECURITY;
                 CREATE POLICY cap_read ON docs2 FOR SELECT
                   USING (dregg_admits('read', id::text));
                 CREATE ROLE app_reader2 NOLOGIN;
                 GRANT SELECT ON docs2 TO app_reader2;",
            )
            .unwrap();

            let tok = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq {
                        key: "action".into(),
                        value: "read".into(),
                    }),
                    Caveat::FirstParty(Pred::AttrPrefix {
                        key: "resource".into(),
                        prefix: "org/42/".into(),
                    }),
                ])
                .encode();

            // Present the token, then read as the unprivileged role so RLS bites.
            Spi::run(&format!("SET dregg.token = '{tok}'")).unwrap();
            let count = |label: &str| -> i64 {
                Spi::run("SET ROLE app_reader2").unwrap();
                let n = Spi::get_one::<i64>("SELECT count(*) FROM docs2")
                    .unwrap_or_else(|e| panic!("count {label}: {e}"))
                    .unwrap();
                Spi::run("RESET ROLE").unwrap();
                n
            };
            assert_eq!(count("before"), 2, "token admits both rows before revocation");

            // Revoke the EXACT presented credential (as the privileged owner).
            Spi::run_with_args("SELECT dregg_revoke($1)", &[tok.as_str().into()]).unwrap();

            // The SAME query, next statement, returns ZERO rows — instant.
            assert_eq!(
                count("after"),
                0,
                "revocation must take effect on the next statement"
            );
        }

        #[pg_test]
        fn forged_and_expired_are_denied() {
            let root = root();
            assert_issuer(&root);
            let tok = mint_org42(&root).encode();

            let admits = |t: &str, r: &str, n: i64| -> bool {
                Spi::get_one_with_args(
                    "SELECT dregg_cap_admits($1, 'read', $2, $3)",
                    &[t.into(), r.into(), n.into()],
                )
                .unwrap()
                .unwrap()
            };

            // Wrong issuer.
            let other = RootKey::from_seed([9u8; 32]);
            let foreign = mint_org42(&other).encode();
            assert!(!admits(&foreign, "org/42/public/doc1", 1000));
            // Expired.
            assert!(!admits(&tok, "org/42/public/doc1", 9999));
            // Garbage.
            assert!(!admits("dga1_garbage", "org/42/public/doc1", 1000));
        }

        #[pg_test]
        fn subject_is_recovered() {
            let root = root();
            assert_issuer(&root);
            let tok = mint_org42(&root).encode();
            let subj: Option<String> =
                Spi::get_one_with_args("SELECT dregg_cap_subject($1)", &[tok.as_str().into()])
                    .unwrap();
            assert_eq!(subj.as_deref(), Some("agent-1"));
        }
    }
}

// pgrx's test harness entrypoint (cargo pgrx test).
#[cfg(feature = "pgrx")]
#[cfg(test)]
pub mod pg_test {
    pub fn setup(_options: Vec<&str>) {}

    /// Configure the managed test server. The issuer key is set HERE (server
    /// start, the secure `Sighup` path) rather than via a session `SET`, since
    /// the GUC is `Sighup` (a session must not be able to point verification at
    /// a key it controls). All #[pg_test]s mint under the fixed seed
    /// `RootKey::from_seed([7u8; 32])`; this is that root's public key.
    pub fn postgresql_conf_options() -> Vec<&'static str> {
        vec![
            "dregg.issuer_pubkey = 'ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c'",
        ]
    }
}
