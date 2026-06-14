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

pub mod attest;
pub mod authz;
pub mod jsonpath;
pub mod mirror;
pub mod synth;
pub mod workflow;

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

    // The PRIVATE key for minting is a SUPERUSER-ONLY GUC: it never appears in
    // SHOW ALL and cannot be read by non-superuser roles.  `dregg_mint` is
    // SECURITY DEFINER and checked via the DBA's GRANT.  The production
    // recommendation (docs/PG-DREGG.md §2.1) is to never place the private key
    // in postgres at all — mint tokens out-of-database and use this helper only
    // for convenience in dev / single-tenant deployments.
    static ISSUER_PRIVKEY: GucSetting<Option<std::ffi::CString>> =
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
        GucRegistry::define_string_guc(
            c"dregg.issuer_privkey",
            c"The dregg issuer PRIVATE key seed (64 hex chars). SUPERUSER ONLY.",
            c"Used only by dregg_mint (SECURITY DEFINER). The recommendation is to never \
              place the private key in postgres — mint tokens out-of-database and use \
              dregg.issuer_privkey only for dev/single-tenant deployments. A malformed or \
              absent key makes dregg_mint return an error (fail-closed).",
            &ISSUER_PRIVKEY,
            GucContext::Suset,   // superuser-set only
            GucFlags::NO_SHOW_ALL,
        );
    }

    /// Pull the issuer PUBLIC key from the GUC into the process-local core slot.
    /// Called at the head of every decision so a SIGHUP-changed key takes effect.
    /// Cheap (a hex parse); on a malformed/absent key it clears the slot ⇒ deny.
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

    /// Pull the issuer PRIVATE key from the SUPERUSER-ONLY GUC. Called at the
    /// head of `dregg_mint` only (not on every decision — the private key is not
    /// needed for verification). A SIGHUP rotation takes effect on the next mint.
    fn sync_mint_key() {
        match ISSUER_PRIVKEY.get() {
            Some(cstring) => {
                let hex = cstring.to_str().unwrap_or("");
                authz::set_mint_key_hex(hex);
            }
            None => {
                authz::clear_mint_key();
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

    /// `dregg_install_schema() -> text`. Install the Tier-B store schema (the
    /// `dregg.*` tables + the query-surface views + the read-side RLS + the
    /// write-lockdown role model), generated from the same Rust that defines the
    /// row types (`crate::mirror::ddl::tier_b`). Idempotent (`IF NOT EXISTS`), so
    /// it is safe to re-run. This is the dregg-developer entry point
    /// (`docs/QUICKSTART-dregg-dev.md` §2): one call stands up "postgres as the
    /// dregg store". Returns a short summary of what it created.
    ///
    /// Must be run by a role that can `CREATE TABLE`/`CREATE ROLE` in the target
    /// database (a DBA/migration role), NOT an application role.
    #[pg_extern]
    fn dregg_install_schema() -> String {
        let ddl = crate::mirror::ddl::tier_b();
        Spi::run(&ddl).expect("dregg_install_schema: Tier-B DDL failed");
        let tables = ddl.matches("CREATE TABLE").count();
        let views = ddl.matches("CREATE OR REPLACE VIEW").count();
        let policies = ddl.matches("CREATE POLICY").count();
        format!(
            "dregg Tier-B store installed: {tables} tables, {views} views, {policies} RLS policies in schema dregg"
        )
    }

    /// `dregg_install_tier_c() -> text`. Install the Tier-C verified-store gate
    /// (`docs/PG-DREGG.md` §10) on top of the Tier-B tables: the
    /// `dregg.commit_log` door + the `BEFORE INSERT` trigger that re-validates
    /// the chain (`dregg_verify_turn`) and materializes the post-image. After
    /// this, a state row exists ONLY as a verified-turn post-image submitted
    /// through `dregg.commit_log` — enforced by the database engine, not by
    /// trusting the writer. Requires [`dregg_install_schema`] to have run first
    /// (the state tables + `dregg.merge_cell` must exist). Idempotent.
    ///
    /// Run by a DBA/migration role (it creates a `SECURITY DEFINER` function and
    /// a trigger), NOT an application role.
    #[pg_extern]
    fn dregg_install_tier_c() -> String {
        let ddl = crate::mirror::ddl::tier_c();
        Spi::run(&ddl).expect("dregg_install_tier_c: Tier-C DDL failed");
        "dregg Tier-C verified-store gate installed: dregg.commit_log + the \
         verify_before_apply trigger (dregg_verify_turn chain re-validation; \
         the ONLY door to state)"
            .to_string()
    }

    /// `dregg_install_write_outbox() -> text`. Install the WRITE-path outbox
    /// (`docs/PG-DREGG.md` §11): the `dregg.submit_queue` table + the RLS gate so
    /// a pg role can submit a verified turn FROM postgres for exactly the agents
    /// its capabilities authorize. Requires [`dregg_install_schema`] first (the
    /// role model). Idempotent. The node-side drainer (queue → real executor →
    /// mirror) is the M3 follow-up; this installs the enqueue half + its gate.
    #[pg_extern]
    fn dregg_install_write_outbox() -> String {
        let ddl = crate::mirror::ddl::write_outbox();
        Spi::run(&ddl).expect("dregg_install_write_outbox: outbox DDL failed");
        "dregg write outbox installed: dregg.submit_queue + the submit_gate RLS \
         policy (a role submits only the turns its capabilities authorize; the \
         node drains the queue through the real verified executor)"
            .to_string()
    }

    /// `dregg_install_login_binding() -> text`. Install the pg17 LOGIN EVENT
    /// TRIGGER authz binding (`docs/PG-DREGG-PG18.md` §6): the
    /// `dregg.role_identity` map + the `ON login` event trigger that binds a
    /// connecting pg role to its dregg agent identity (sets the `dregg.token` /
    /// `dregg.agent` session GUCs from the role's row) at connection time.
    /// Requires [`dregg_install_schema`] first (the role model). Idempotent. After
    /// this, a DBA `INSERT`s `(pg_role, agent, default_token)` rows and every
    /// connection by that role is already capability-bound — the pg-native front
    /// door. A role with no row connects unbound (deny-by-default, fail-closed).
    ///
    /// Run by a DBA/migration role (it creates a `SECURITY DEFINER` function and
    /// an event trigger), NOT an application role.
    #[pg_extern]
    fn dregg_install_login_binding() -> String {
        let ddl = crate::mirror::ddl::login_binding();
        Spi::run(&ddl).expect("dregg_install_login_binding: login-binding DDL failed");
        "dregg login binding installed: dregg.role_identity + the dregg_login_bind \
         event trigger (a connecting role is bound to its dregg capability at login; \
         a role with no identity row connects unbound = deny-by-default)"
            .to_string()
    }

    /// `dregg_install_federation() -> text`. Install the FEDERATION publication
    /// (`docs/PG-DREGG.md` §15): a `CREATE PUBLICATION dregg_mirror` over the four
    /// state tables + `turns`, so a subscriber postgres tails this node's
    /// verified-turn stream by PostgreSQL's own logical replication
    /// (federation-via-pg). Run on the PUBLISHER. The subscriber side is a
    /// `pg_createsubscriber` runbook (`dregg_federation_subscriber_runbook`), not
    /// extension SQL. Idempotent. Requires [`dregg_install_schema`] first (the
    /// tables must exist to publish). The replicated chain is re-validated on the
    /// subscriber by `dregg_revalidate_replicated_chain` — a subscriber
    /// re-validates, it does not trust the stream.
    #[pg_extern]
    fn dregg_install_federation() -> String {
        let ddl = crate::mirror::ddl::federation_publication();
        Spi::run(&ddl).expect("dregg_install_federation: publication DDL failed");
        "dregg federation publication installed: CREATE PUBLICATION dregg_mirror over \
         dregg.turns/cells/capabilities/memory (a subscriber tails this verified-turn \
         stream; it re-validates the chain via dregg_revalidate_replicated_chain — \
         re-validate, do not trust)"
            .to_string()
    }

    /// `dregg_federation_subscriber_runbook(publisher_conninfo text) -> text`. The
    /// SUBSCRIBER-side runbook (`docs/PG-DREGG.md` §15): the `pg_createsubscriber`
    /// bootstrap + the `CREATE SUBSCRIPTION … WITH (failover = true)` that tails the
    /// publisher and survives its failover, with the publisher conninfo substituted.
    /// Returns the runbook as text (it is an operational procedure, not in-database
    /// SQL the extension runs). The subscriber then re-validates the replicated chain
    /// locally via `dregg_revalidate_replicated_chain`.
    #[pg_extern]
    fn dregg_federation_subscriber_runbook(publisher_conninfo: &str) -> String {
        crate::mirror::ddl::federation_subscriber(publisher_conninfo)
    }

    /// `dregg_load_role_identity_sql(csv_path text, reject_limit bigint) -> text`.
    /// The recommended pg18 `COPY … ON_ERROR ignore` bulk-load command for the
    /// OAuth→role bind map (`docs/PG-DREGG-PG18.md` §12), with the CSV path +
    /// reject limit substituted. Returns the ready-to-run SQL (COPY needs a literal
    /// path, so it is a template, not executed here): it stages
    /// `(pg_role, agent_hex, token)` rows — skipping malformed lines instead of
    /// aborting — then the DBA runs `SELECT * FROM dregg.promote_role_identity_load()`
    /// to validate + upsert each through the audited `dregg.bind_role` seam. A
    /// `reject_limit` of 0 omits the cap (tolerate any number of bad rows).
    #[pg_extern]
    fn dregg_load_role_identity_sql(csv_path: &str, reject_limit: i64) -> String {
        crate::mirror::ddl::load_role_identity_sql(csv_path, reject_limit.max(0) as u64)
    }

    /// `dregg_revalidate_replicated_chain() -> text`. The SUBSCRIBER-side
    /// re-validation sweep (`docs/PG-DREGG.md` §15): read the replicated
    /// `dregg.turns` as `(ordinal, prev_root, ledger_root)` ordered by ordinal and
    /// walk them through the SAME anti-substitution tooth the publisher ran
    /// (`crate::mirror::revalidate_replicated_chain`). Returns `'ok: N turns,
    /// head=…'` if the whole replicated chain re-validates, or `'REFUSED: …'`
    /// naming the first link that does not chain — a tampered / reordered /
    /// substituted / gapped replication stream is caught HERE, locally, with no
    /// call back to the publisher. This is what makes a replicated mirror a
    /// re-validating replica, not a trusted copy: the chain tooth survives
    /// replication because it is structural on the replicated rows.
    ///
    /// Run as a role that can read `dregg.turns` (the kernel/operator). It does NOT
    /// mutate; it is a read-only attestation of the replicated stream's integrity.
    #[pg_extern]
    fn dregg_revalidate_replicated_chain() -> String {
        let links = read_replicated_chain_links();
        match revalidate_replicated_turns(&links) {
            Ok(head) => format!(
                "ok: {} turns re-validated, head={}",
                links.len(),
                head.map(|h| h.iter().map(|b| format!("{b:02x}")).collect::<String>())
                    .unwrap_or_else(|| "<empty>".to_string())
            ),
            Err(e) => format!("REFUSED: {e}"),
        }
    }

    /// Read the replicated `dregg.turns` as `(ordinal, prev_root, ledger_root)`
    /// chain links, ordered by ordinal — the minimal projection the §15
    /// anti-substitution tooth re-validates. A malformed root in the stream is
    /// recorded as an impossible link (a `0xFF…` prev that cannot chain) so the
    /// sweep fails closed rather than silently skipping it. Shared by
    /// [`dregg_revalidate_replicated_chain`] and the conflict-triggered
    /// [`dregg_federation_health`] so both re-validate the IDENTICAL link set.
    fn read_replicated_chain_links() -> Vec<crate::mirror::ChainLink> {
        use crate::mirror::ChainLink;
        let mut links: Vec<ChainLink> = Vec::new();
        let _ = Spi::connect(|client| {
            let rows = client.select(
                "SELECT ordinal, encode(prev_root,'hex'), encode(ledger_root,'hex') \
                 FROM dregg.turns ORDER BY ordinal",
                None,
                &[],
            )?;
            for row in rows {
                let ordinal: i64 = row.get::<i64>(1)?.unwrap_or(-1);
                let prev_hex: String = row.get::<String>(2)?.unwrap_or_default();
                let post_hex: String = row.get::<String>(3)?.unwrap_or_default();
                if ordinal < 0 {
                    continue;
                }
                let (Some(prev), Some(post)) =
                    (decode_root_hex(&prev_hex), decode_root_hex(&post_hex))
                else {
                    // A malformed root in the stream ⇒ record an impossible link so
                    // the sweep refuses (fail-closed). Use a sentinel that breaks
                    // the chain.
                    links.push(ChainLink {
                        ordinal: ordinal as u64,
                        prev_root: [0xFF; 32],
                        ledger_root: [0x00; 32],
                    });
                    continue;
                };
                links.push(ChainLink {
                    ordinal: ordinal as u64,
                    prev_root: prev,
                    ledger_root: post,
                });
            }
            Ok::<(), pgrx::spi::Error>(())
        });
        links
    }

    /// Run the §15 anti-substitution tooth over the read replicated links. Pins
    /// genesis from the first link's `prev_root` (a subscriber bootstrapped from a
    /// consistent base inherits the publisher's genesis; the all-zero default
    /// matches a fresh chain). No external count expectation is imposed here — the
    /// per-link chaining is the tooth; a truncation check needs a published height
    /// the subscriber trusts separately, supplied out of band by a deployment.
    fn revalidate_replicated_turns(
        links: &[crate::mirror::ChainLink],
    ) -> Result<Option<[u8; 32]>, crate::mirror::ChainRefusal> {
        let genesis = links.first().map(|l| l.prev_root).unwrap_or([0u8; 32]);
        crate::mirror::revalidate_replicated_chain(genesis, links, None)
    }

    /// Read the REAL pg18 apply-conflict counters from `dregg.replication_conflicts`
    /// (`docs/PG-DREGG-PG18.md` §10) into a [`crate::mirror::ConflictReport`] — one
    /// [`crate::mirror::SubscriptionConflicts`] per subscription, the seven `confl_*`
    /// columns + the view's summed `conflicts_total`. Empty on a publisher (no
    /// subscriptions). This is what makes the alarm read the genuine pg18 counters,
    /// not a stub. A malformed/absent count coalesces to 0 (a NULL counter is "no
    /// conflict seen yet", not an error).
    fn read_replication_conflicts() -> crate::mirror::ConflictReport {
        use crate::mirror::{ConflictReport, SubscriptionConflicts};
        let mut subscriptions: Vec<SubscriptionConflicts> = Vec::new();
        let _ = Spi::connect(|client| {
            // Select the seven confl_* counters + the view's conflicts_total,
            // coalescing NULLs (a counter with no activity yet) to 0. `subname` is
            // cast to text: the real view sources it from `pg_subscription.subname`
            // (type `name`), which pgrx's `get::<String>` does NOT decode — the cast
            // makes the read robust whether the source is `name` or `text`.
            let rows = client.select(
                "SELECT subname::text, \
                        coalesce(confl_insert_exists,0), \
                        coalesce(confl_update_origin_differs,0), \
                        coalesce(confl_update_exists,0), \
                        coalesce(confl_update_missing,0), \
                        coalesce(confl_delete_origin_differs,0), \
                        coalesce(confl_delete_missing,0), \
                        coalesce(confl_multiple_unique_conflicts,0), \
                        coalesce(conflicts_total,0) \
                 FROM dregg.replication_conflicts ORDER BY subname",
                None,
                &[],
            )?;
            for row in rows {
                let subname: String = row.get::<String>(1)?.unwrap_or_default();
                let g = |i: usize| -> i64 { row.get::<i64>(i).ok().flatten().unwrap_or(0) };
                subscriptions.push(SubscriptionConflicts {
                    subname,
                    insert_exists: g(2),
                    update_origin_differs: g(3),
                    update_exists: g(4),
                    update_missing: g(5),
                    delete_origin_differs: g(6),
                    delete_missing: g(7),
                    multiple_unique_conflicts: g(8),
                    total: g(9),
                });
            }
            Ok::<(), pgrx::spi::Error>(())
        });
        ConflictReport { subscriptions }
    }

    /// `dregg_federation_health() -> text`. The SUBSCRIBER-side federation health
    /// check (`docs/PG-DREGG.md` §15, `docs/PG-DREGG-PG18.md` §10) — where the pg18
    /// apply-conflict counters DRIVE the chain re-validation. This is the wiring
    /// that makes the `dregg.replication_conflicts` alarm USEFUL rather than merely
    /// observable: it reads the real `confl_*` counters AND, when they fire, TRIGGERS
    /// `dregg_revalidate_replicated_chain`'s anti-substitution tooth over the
    /// replicated `dregg.turns`.
    ///
    /// The dregg federation model is SINGLE-WRITER FAN-OUT: the publisher is the
    /// only writer; a subscriber re-validates the replicated turn chain rather than
    /// accept local writes. So an apply conflict (a row it already holds, a missing
    /// update/delete target, a divergent origin) is BY CONSTRUCTION an anomaly — the
    /// stream is not the clean verified-turn feed the model assumes. The two checks
    /// COMPOSE on two layers, and pg detects each: the conflict counters catch an
    /// apply-level divergence pg saw while applying the stream; the chain tooth
    /// catches a substituted ROOT (turn N's `ledger_root` ≠ turn N+1's `prev_root`).
    /// A non-zero `conflicts_total` is exactly the trigger to stop trusting the
    /// replicated turns and re-run the tooth over them.
    ///
    /// Returns one of:
    ///   * `'ok: federation healthy — N subscription(s), 0 apply conflicts'`
    ///     (no conflict; the triggered tooth is not run — it is the triggered check);
    ///   * `'ALARM (K apply conflict(s)) but chain re-validates: head=…'`
    ///     (pg saw apply conflicts but the turn chain still re-validates — an anomaly
    ///     to chase: a conflicting writer or a botched bootstrap);
    ///   * `'CRITICAL (K apply conflict(s)) AND chain REFUSED: …'`
    ///     (apply conflicts AND a chain the tooth rejects — do NOT trust this replica).
    ///
    /// Run as a role that can read `dregg.replication_conflicts` and `dregg.turns`
    /// (the kernel/operator). Read-only: it never mutates; it is an attestation of
    /// the replicated stream's apply-and-chain integrity.
    #[pg_extern]
    fn dregg_federation_health() -> String {
        let report = read_replication_conflicts();
        // THE COMPOSITION: the conflict alarm DRIVES the chain re-validation. The
        // closure is the trigger target — it is invoked by `federation_health` ONLY
        // when the alarm fires (a clear report skips the then-unnecessary tooth).
        let verdict = crate::mirror::federation_health(&report, || {
            let links = read_replicated_chain_links();
            revalidate_replicated_turns(&links)
        });
        verdict.summary()
    }

    /// `dregg_attest_range(proof bytea, vk_anchor bytea, lo bigint, hi bigint)
    /// RETURNS SETOF (ordinal bigint, prev_root bytea, ledger_root bytea,
    /// proof_attested bool)`. The Tier-C PROOF gate (`docs/PG-DREGG.md` §10.2) — the
    /// whole-chain IVC RANGE attestation, as a set-returning function.
    ///
    /// This is the orthogonal soundness half `dregg_verify_turn` honestly does NOT
    /// do per-row: a `CommitRecord` carries no per-turn STARK, so per-row proof is
    /// impossible AND the wrong cost model. Instead, ONE succinct recursive proof
    /// (`circuit::ivc_turn_chain::verify_turn_chain_recursive`) attests that ALL
    /// turns in a receipt RANGE executed correctly and the root chain advanced — the
    /// verifier cost is independent of the range size. This SRF takes the serialized
    /// proof + the published VK anchor + the claimed window `[lo, hi]`, and — if the
    /// proof verifies against the anchor and does not over-claim — returns one row
    /// per ordinal in the attested window (read from `dregg.turns`), each tagged
    /// `proof_attested = true`. A consumer JOINs these against `dregg.turns` to mark
    /// the proof-attested prefix:
    ///
    /// ```sql
    /// SELECT t.ordinal, a.proof_attested
    /// FROM dregg.turns t
    /// LEFT JOIN dregg_attest_range(:proof, :vk, 0, 100) a USING (ordinal);
    /// ```
    ///
    /// **The circuit-link settle item (named, §10.2):** the IVC verifier takes an
    /// in-memory `WholeChainProof` (plonky3 proof objects), which is not yet
    /// serde-serializable, so the proof-bytes leg (`crate::attest::verify_serialized_proof`)
    /// is STUBBED behind the `tier-c` feature. With `tier-c` OFF (the default,
    /// circuit-free build), the SRF FAILS CLOSED — it attests NOTHING (returns zero
    /// rows), which is the only safe default (§10.3: a labeled proof gate that does
    /// not verify must say "unattested", never "attested"). Wiring it is settle
    /// items S1–S3 in `crate::attest`: serialize `WholeChainProof` (S1), the
    /// node-side proof producer + a `dregg.turn_proofs` table (S2), and the
    /// `tier-c` dep on the Lean-free circuit verifier (S3, §8.1-authorized).
    ///
    /// `dregg_attest_explain(proof, vk_anchor, lo, hi) -> text` returns the verdict
    /// reason (for debugging which requirement failed) without the row expansion.
    #[pg_extern]
    fn dregg_attest_range(
        proof: &[u8],
        vk_anchor: &[u8],
        lo: i64,
        hi: i64,
    ) -> TableIterator<
        'static,
        (
            name!(ordinal, i64),
            name!(prev_root, Vec<u8>),
            name!(ledger_root, Vec<u8>),
            name!(proof_attested, bool),
        ),
    > {
        let rows = attest_range_rows(proof, vk_anchor, lo, hi);
        TableIterator::new(rows.into_iter())
    }

    /// `dregg_attest_explain(...) -> text`. The verdict reason for a range
    /// attestation (the explain face of [`dregg_attest_range`]): `'attested: …'` or
    /// `'<refusal reason>'` (including, in the default build, the named circuit-link
    /// settle item). For debugging the proof gate.
    #[pg_extern]
    fn dregg_attest_explain(proof: &[u8], vk_anchor: &[u8], lo: i64, hi: i64) -> String {
        let Some(anchor) = slice_to_root(vk_anchor) else {
            return "REFUSED: vk_anchor must be exactly 32 bytes".to_string();
        };
        if lo < 0 || hi < 0 {
            return "REFUSED: lo/hi must be non-negative ordinals".to_string();
        }
        let req = crate::attest::AttestRequest {
            proof_bytes: proof,
            vk_anchor: anchor,
            lo: lo as u64,
            hi: hi as u64,
        };
        crate::attest::attest_range(&req).reason()
    }

    /// Shared logic for [`dregg_attest_range`]: verify the proof for `[lo, hi]`,
    /// and on success read the attested window's recorded turns from `dregg.turns`
    /// and tag them. Fail-closed: any refusal (bad anchor, unverified proof,
    /// over-claim, malformed args, or the unwired circuit-link stub) yields ZERO
    /// rows. Separated out so it is plain logic over SPI + the `crate::attest` core.
    fn attest_range_rows(
        proof: &[u8],
        vk_anchor: &[u8],
        lo: i64,
        hi: i64,
    ) -> Vec<(i64, Vec<u8>, Vec<u8>, bool)> {
        let Some(anchor) = slice_to_root(vk_anchor) else {
            return Vec::new(); // anchor must be 32 bytes ⇒ fail closed
        };
        if lo < 0 || hi < 0 {
            return Vec::new();
        }
        let req = crate::attest::AttestRequest {
            proof_bytes: proof,
            vk_anchor: anchor,
            lo: lo as u64,
            hi: hi as u64,
        };
        let verdict = crate::attest::attest_range(&req);
        if !verdict.attested() {
            return Vec::new(); // fail closed — attest nothing on a refusal
        }
        // Read the attested window's recorded turns to expand the verdict into
        // rows (the proof attests the WINDOW; the roots are the recorded ones,
        // re-tagged proof_attested=true).
        let mut recorded: Vec<crate::attest::AttestedTurn> = Vec::new();
        let _ = Spi::connect(|client| {
            let rows = client.select(
                "SELECT ordinal, encode(prev_root,'hex'), encode(ledger_root,'hex') \
                 FROM dregg.turns WHERE ordinal BETWEEN $1 AND $2 ORDER BY ordinal",
                None,
                &[lo.into(), hi.into()],
            )?;
            for row in rows {
                let ordinal: i64 = row.get::<i64>(1)?.unwrap_or(-1);
                let prev_hex: String = row.get::<String>(2)?.unwrap_or_default();
                let post_hex: String = row.get::<String>(3)?.unwrap_or_default();
                if let (true, Some(prev), Some(post)) = (
                    ordinal >= 0,
                    decode_root_hex(&prev_hex),
                    decode_root_hex(&post_hex),
                ) {
                    recorded.push(crate::attest::AttestedTurn {
                        ordinal: ordinal as u64,
                        prev_root: prev,
                        ledger_root: post,
                        proof_attested: false,
                    });
                }
            }
            Ok::<(), pgrx::spi::Error>(())
        });
        crate::attest::attested_rows(&verdict, &recorded)
            .into_iter()
            .map(|t| {
                (
                    t.ordinal as i64,
                    t.prev_root.to_vec(),
                    t.ledger_root.to_vec(),
                    t.proof_attested,
                )
            })
            .collect()
    }

    /// `dregg_bind_role(pg_role text, agent bytea, token text) -> bool`. Bind a
    /// connecting pg role to its dregg agent identity (`docs/PG-DREGG-PG18.md` §6):
    /// upsert the `dregg.role_identity` row the `ON login` trigger installs, so the
    /// role's session is capability-bound the moment it connects. This is the seam
    /// where pg18 OAuth meets dregg — OAuth (a `pg_hba.conf` deployment concern, not
    /// extension SQL) authenticates an external identity to a pg ROLE; this binds
    /// that role to a dregg capability. Calls the `SECURITY DEFINER`
    /// `dregg.bind_role` (which writes the PUBLIC-closed mapping table), so it must
    /// be run by a role the DBA granted `EXECUTE` on `dregg.bind_role`. `token` may
    /// be NULL (bind the agent identity without a default token; the role then
    /// presents its own). Requires [`dregg_install_login_binding`] first.
    #[pg_extern]
    fn dregg_bind_role(pg_role: &str, agent: &[u8], token: Option<&str>) -> bool {
        Spi::run_with_args(
            "SELECT dregg.bind_role($1, $2, $3)",
            &[pg_role.into(), agent.into(), token.into()],
        )
        .expect("dregg_bind_role: bind failed (login binding not installed, or no EXECUTE on dregg.bind_role)");
        true
    }

    /// `dregg_submit_turn(signed_turn bytea, agent bytea) -> uuid`. Submit a
    /// SIGNED turn FROM postgres (`docs/PG-DREGG.md` §11). `signed_turn` is the
    /// postcard `SignedTurn` bytes; `agent` is the turn's agent cell id. Enqueues
    /// the turn into `dregg.submit_queue` and returns the submission id; the node
    /// drains the queue, executes the turn through the REAL verified executor, and
    /// the post-image flows back via the mirror.
    ///
    /// The enqueue is RLS-gated by the `submit_gate` policy (`dregg_admits(
    /// 'submit', encode(agent,'hex'))`): the caller's presented capability (the
    /// `dregg.token` GUC) must admit `submit` on this agent, else the INSERT is
    /// refused by Row-Level Security — a role submits exactly the turns its caps
    /// authorize. This function is NOT `SECURITY DEFINER`: it runs as the calling
    /// role so the WITH CHECK policy bites. The turn stays UNexecuted until the
    /// node accepts it — writes are verified-only because the NODE, not postgres,
    /// executes.
    ///
    /// Returns the submission id (poll `dregg.submit_queue` for the outcome:
    /// `status` walks `pending → executed | refused`, with `receipt_hash` /
    /// `error` carrying the result). RAISEs if RLS refuses the enqueue.
    #[pg_extern]
    fn dregg_submit_turn(signed_turn: &[u8], agent: &[u8]) -> pgrx::Uuid {
        // Insert as the calling role so the submit_gate WITH CHECK policy (the
        // capability admission) gates the enqueue. RETURNING the generated id.
        let id: Option<pgrx::Uuid> = Spi::get_one_with_args(
            "INSERT INTO dregg.submit_queue (agent, signed_turn) VALUES ($1, $2) RETURNING id",
            &[agent.into(), signed_turn.into()],
        )
        .expect("dregg_submit_turn: enqueue failed (RLS refused, or the outbox is not installed)");
        id.expect("dregg_submit_turn: INSERT ... RETURNING id yielded no row")
    }

    /// `dregg_verify_turn(prev_root, ledger_root, ordinal) -> bool`. The Tier-C
    /// chain re-validator (`docs/PG-DREGG.md` §10): TRUE iff a turn with
    /// pre-state `prev_root` and `ordinal` chains onto the database's current
    /// head — i.e. `ordinal` is the next expected one AND `prev_root` equals the
    /// head root (the post-state root of turn *N* is the pre-state root of turn
    /// *N+1*). This is the REAL anti-substitution tooth: it runs the exact same
    /// gate the in-process mirror runs (`crate::mirror::verify_chain_step`, which
    /// `RootChain::extend` also calls), reading the head from `dregg.turns`. A
    /// tampered / reordered / forged batch is refused.
    ///
    /// What it is NOT (documented honestly, `docs/PG-DREGG.md` §10.2/§10.3): it
    /// is NOT a per-turn STARK re-proof. A `CommitRecord` carries no per-turn
    /// proof (proof soundness is the whole-chain IVC light client's job —
    /// `circuit::ivc_turn_chain::verify_turn_chain_recursive`), so the realizable
    /// per-row gate is this structural chain check. It is NOT stubbed to TRUE
    /// (the forbidden failure mode); it fails closed on any deviation.
    ///
    /// STABLE: depends on the current `dregg.turns` head, constant within a
    /// statement snapshot. `ledger_root` is accepted (the post-state the row
    /// claims to produce, recorded by the trigger) though the chain step itself
    /// gates on `prev_root`/`ordinal`; carrying it keeps the signature the
    /// verified-store door's shape.
    #[pg_extern(stable, parallel_safe, strict)]
    fn dregg_verify_turn(prev_root: &[u8], ledger_root: &[u8], ordinal: i64) -> bool {
        let _ = ledger_root; // recorded by the trigger; the chain gate is on prev_root/ordinal
        // Read the current head + next-expected ordinal from dregg.turns.
        // No rows ⇒ genesis (head = None, next = 0).
        let head_hex: Option<String> = Spi::get_one(
            "SELECT encode(ledger_root, 'hex') FROM dregg.turns ORDER BY ordinal DESC LIMIT 1",
        )
        .ok()
        .flatten();
        let next_ordinal: i64 = Spi::get_one(
            "SELECT coalesce(max(ordinal) + 1, 0) FROM dregg.turns",
        )
        .ok()
        .flatten()
        .unwrap_or(0);

        let head: Option<[u8; 32]> = head_hex.and_then(|h| decode_root_hex(&h));
        let Some(prev) = slice_to_root(prev_root) else {
            return false; // malformed prev_root ⇒ fail closed
        };
        if ordinal < 0 {
            return false;
        }
        crate::mirror::verify_chain_step(head, next_ordinal as u64, prev, ordinal as u64).is_ok()
    }

    /// Decode a 64-char hex string into a 32-byte root (fail-closed on bad len).
    fn decode_root_hex(h: &str) -> Option<[u8; 32]> {
        if h.len() != 64 {
            return None;
        }
        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&h[i * 2..i * 2 + 2], 16).ok()?;
        }
        Some(out)
    }

    /// A bytea slice from SQL into a fixed 32-byte root (fail-closed on bad len).
    fn slice_to_root(s: &[u8]) -> Option<[u8; 32]> {
        s.try_into().ok()
    }

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

    // -----------------------------------------------------------------------
    // Mint and attenuate helpers (docs/PG-DREGG.md §2.1).
    //
    // `dregg_mint` is SECURITY DEFINER and role-gated (the issuing role). The
    // private key is read from the SUPERUSER-ONLY `dregg.issuer_privkey` GUC;
    // it never appears in SHOW ALL. The production recommendation is to mint
    // out-of-database; these helpers are a dev/convenience surface.
    //
    // `dregg_attenuate` is IMMUTABLE + PARALLEL SAFE: it requires no issuer
    // private key (attenuation is the TOKEN HOLDER's right), is a pure function
    // of its inputs, and can only narrow — the `attenuate_subset` proof is the
    // no-amplify guarantee (docs/PG-DREGG.md §2.1, §4).
    // -----------------------------------------------------------------------

    /// `dregg_mint(subject, caveats, until) -> text`. Issue a fresh credential:
    /// `subject` is the bound identity (an `AttrEq{key:"subject"}` in block 0),
    /// `caveats` is a JSON ARRAY of `Pred` objects (the serde encoding of
    /// `dregg_auth::credential::Pred` — see docs/PG-DREGG.md §2.1 for the DSL),
    /// `until` is the unix-second `NotAfter` bound. Returns the encoded `dga1_…`
    /// string. Fails with an ERROR if `dregg.issuer_privkey` is not configured or
    /// the `caveats` JSON is malformed (fail-closed). SECURITY DEFINER so the
    /// private key GUC is readable; the DBA grants EXECUTE to the issuing role.
    #[pg_extern(security_definer)]
    fn dregg_mint(subject: &str, caveats: pgrx::JsonB, until: i64) -> String {
        sync_mint_key();
        let json = serde_json::to_string(&caveats.0)
            .unwrap_or_else(|_| "[]".to_string());
        authz::mint_token(subject, &json, until)
            .unwrap_or_else(|e| pgrx::error!("dregg_mint: {e}"))
    }

    /// `dregg_attenuate(token, caveats) -> text`. Narrow an existing credential
    /// by appending additional first-party caveats. The admitted set of the
    /// returned token is a STRICT SUBSET of the input token's (the
    /// `attenuate_subset` guarantee). `caveats` is a JSON array of `Pred` objects
    /// (same DSL as `dregg_mint`). Returns the encoded attenuated token. Fails
    /// with an ERROR if the token does not decode or the caveats are malformed.
    /// IMMUTABLE + PARALLEL SAFE: no issuer key needed; the holder may attenuate.
    #[pg_extern(immutable, parallel_safe, strict)]
    fn dregg_attenuate(token: &str, caveats: pgrx::JsonB) -> String {
        let json = serde_json::to_string(&caveats.0)
            .unwrap_or_else(|_| "[]".to_string());
        authz::attenuate_token(token, &json)
            .unwrap_or_else(|e| pgrx::error!("dregg_attenuate: {e}"))
    }

    // -----------------------------------------------------------------------
    // DEV-ONLY mint ergonomics + issuer-status discoverability
    // (docs/PG-DREGG-DX.md §4 S3, docs/FRONTIER-ROADMAP.md N19).
    //
    // `dregg_dev_mint` kills the on-ramp's first friction — hand-writing a `Pred`
    // JSON array — by composing the common (actions, resource-prefix, subject,
    // expiry) shape for the newcomer. It is DEV ONLY and explicitly labeled so.
    // CRITICALLY, it does NOT bypass the issuer-key discipline: it routes through
    // the SAME `authz::dev_mint` → `authz::mint_token` path as `dregg_mint`, so
    // with NO `dregg.issuer_privkey` it ERRORS LOUDLY (never silently mints a
    // token). The PRODUCTION posture — mint out-of-database, private key never in
    // pg — stays the default; this is the single-tenant/dev convenience only.
    //
    // `dregg_issuer_status` makes the silent fail-closed mode ("no issuer key ⇒
    // everything denies") DISCOVERABLE: it reports whether a verify key is set
    // (and its id), whether dev minting is enabled, and the loud warning when the
    // verify key is absent.
    // -----------------------------------------------------------------------

    /// `dregg_dev_mint(subject text, actions text[], resource_prefix text, ttl
    /// interval) -> text`. **DEV ONLY.** Compose the common capability shape — an
    /// allowed-action set (`actions`) confined to a `resource_prefix`, expiring
    /// `ttl` from now, naming `subject` — and mint it as a `dga1_…` token, so a
    /// newcomer never hand-writes `Pred` JSON. The composed caveats are exactly
    /// `action ∈ actions` (an `AnyOf` of equalities, or a single `AttrEq`) AND
    /// `resource` has `resource_prefix` (the canonical `examples/mint.rs` shape);
    /// `subject` + the `NotAfter` expiry are added by the shared mint path. The
    /// resulting token is admitted by `dregg_cap_admits` / a `dregg_admits` RLS
    /// policy with no further wiring.
    ///
    /// **Issuer-key discipline is intact.** This is `SECURITY DEFINER` so it can
    /// read the SUPERUSER-only `dregg.issuer_privkey`, and the DBA grants EXECUTE
    /// to the issuing dev role — but with NO mint key configured it RAISES (the
    /// same fail-closed error `dregg_mint` raises). It NEVER returns a
    /// silently-minted token. The production recommendation (mint out-of-database;
    /// the private key never enters postgres) is unchanged — `dregg_dev_mint` only
    /// spares the JSON for the dev/single-tenant on-ramp.
    ///
    /// Empty `actions` mints an `AnyOf([])` token that admits NO action (a
    /// deliberately-useless token, fail-closed — never wide-open). An empty
    /// `resource_prefix` is the unrestricted-resource case the caller opts into.
    /// A negative/zero `ttl` mints an already-expired token (denied immediately).
    #[pg_extern(security_definer)]
    fn dregg_dev_mint(
        subject: &str,
        actions: pgrx::Array<&str>,
        resource_prefix: &str,
        ttl: pgrx::datum::Interval,
    ) -> String {
        sync_mint_key();
        // Collect the action set (skip SQL NULL array elements).
        let actions: Vec<String> = actions
            .iter()
            .flatten()
            .map(|s| s.to_string())
            .collect();
        // Resolve the absolute expiry epoch with postgres's own interval
        // arithmetic (correct for months/days/DST), keeping the unix-seconds
        // clock contract dregg_admits reads. `now() + ttl`, as bigint seconds.
        let until: i64 = Spi::get_one_with_args(
            "SELECT extract(epoch from now() + $1)::bigint",
            &[ttl.into()],
        )
        .ok()
        .flatten()
        .unwrap_or_else(|| pgrx::error!("dregg_dev_mint: could not resolve ttl to an expiry"));
        authz::dev_mint(subject, &actions, resource_prefix, until)
            .unwrap_or_else(|e| pgrx::error!("dregg_dev_mint (DEV ONLY): {e}"))
    }

    /// `dregg_issuer_status() -> text`. Report the database's dregg key
    /// configuration in one human-readable line — so the silent fail-closed mode
    /// ("no issuer key ⇒ every `dregg_cap_admits` denies ⇒ all cap-gated rows
    /// vanish") is DISCOVERABLE, not a mystery. It states whether the issuer
    /// PUBLIC (verify) key is configured (and its id), whether dev minting is
    /// enabled (a `dregg.issuer_privkey` is set), and — when the verify key is
    /// absent — a LOUD warning naming the failure. It also flags a dev-mint key
    /// that MISMATCHES the verify key (tokens it mints would not verify here).
    ///
    /// The private key is NEVER reported (only whether it is present and its
    /// public half, for a match-check). Run it first when "everything denies":
    /// `SELECT dregg_issuer_status();`.
    #[pg_extern(stable)]
    fn dregg_issuer_status() -> String {
        sync_issuer_key();
        sync_mint_key();
        authz::issuer_status_text()
    }

    // -----------------------------------------------------------------------
    // Opt-in revocation check (docs/PG-DREGG.md §3.4, tier 2).
    //
    // The default revocation is bounded-staleness via TTL (short `NotAfter`).
    // `dregg_cap_not_revoked` is the opt-in synchronous tier: a policy adds
    // `AND dregg_cap_not_revoked(current_setting('dregg.token',true))` to get
    // instant-revocation semantics backed by the backend-local revocation set
    // (populated by `dregg_revoke`). In a clustered deployment the policy would
    // also join against a `dregg.revoked` table; the backend set is what the
    // `cargo test` / pgrx test suite proves the semantics of.
    //
    // The function's volatility is STABLE (not IMMUTABLE): the revocation set
    // can change between statements (a `dregg_revoke` call in a prior statement),
    // so the planner must not fold it across rows. Within a single statement's
    // snapshot the verdict is constant for a given token.
    // -----------------------------------------------------------------------

    /// `dregg_cap_not_revoked(token) -> bool`. TRUE iff the credential has NOT
    /// been revoked in the backend-local revocation registry (populated by
    /// `dregg_revoke`). NULL token ⇒ FALSE (fail-closed via STRICT). Use as
    /// `AND dregg_cap_not_revoked(current_setting('dregg.token',true))` to add
    /// instant-revocation semantics to a policy (docs/PG-DREGG.md §3.4 tier 2).
    /// STABLE (the revocation set can change between statements).
    #[pg_extern(stable, parallel_safe, strict)]
    fn dregg_cap_not_revoked(token: &str) -> bool {
        // cap_id decodes only (no issuer-key check needed for the revocation
        // lookup — the stable id is a commitment to the chain itself, forging
        // a chain that collides with a real id would require a BLAKE3 preimage).
        match authz::cap_id(token) {
            Some(id) => !authz::is_revoked_pub(&id),
            None => false, // non-decodable token ⇒ fail closed
        }
    }

    /// `dregg_cap_nonce(token) -> text`. The credential's stable per-issuance
    /// nonce (hex of the root block's random nonce), or NULL if the token does
    /// not decode. Useful for populating a `dregg.revoked(nonce)` table that
    /// covers ALL attenuated children minted from the same root credential (the
    /// root nonce survives attenuation; see docs/PG-DREGG.md §3.4). IMMUTABLE:
    /// a pure function of the token string.
    #[pg_extern(immutable, parallel_safe)]
    fn dregg_cap_nonce(token: Option<&str>) -> Option<String> {
        authz::cap_nonce(token?)
    }

    // -----------------------------------------------------------------------
    // pg17 SQL/JSON jsonpath: a dregg caveat predicate, compiled to a jsonpath
    // and evaluated IN postgres over the mirrored turn/cell JSON. The read/audit
    // half of the predicate algebra (docs/PG-DREGG-PG18.md §2). The authorization
    // GATE on a write stays the Rust `decide` path (chain + revocation); this is
    // "which mirrored rows satisfy this caveat?" as set-oriented SQL.
    // -----------------------------------------------------------------------

    /// `dregg_pred_jsonpath(pred_json text) -> text`. Compile a JSON-encoded
    /// dregg `Pred` (the caveat predicate algebra,
    /// `dregg_auth::credential::Pred`) into a SQL/JSON jsonpath whose
    /// `jsonb_path_exists(row, path)` is the predicate's admit verdict
    /// (bound-context semantics — `crate::jsonpath`). Returns the jsonpath string,
    /// or NULL if `pred_json` does not parse as a `Pred` (fail-closed: a caller
    /// that gets NULL and feeds it to `JSON_EXISTS` gets a clean error, never a
    /// silent admit). IMMUTABLE: a pure function of its argument.
    ///
    /// This is the bridge that makes the dregg predicate algebra a first-class
    /// pg17 jsonpath: mint/attenuate a credential in Rust, serialize one of its
    /// caveats' `Pred` to JSON, and `SELECT * FROM dregg.turn_effects WHERE
    /// jsonb_path_exists(doc, dregg_pred_jsonpath($1)::jsonpath)` filters the
    /// mirror by exactly that caveat — the same algebra that gates a write,
    /// queryable over the read mirror.
    #[pg_extern(immutable, parallel_safe, strict)]
    fn dregg_pred_jsonpath(pred_json: &str) -> Option<String> {
        let pred: dregg_auth::credential::Pred = serde_json::from_str(pred_json).ok()?;
        crate::jsonpath::pred_to_jsonpath(&pred)
    }

    /// `dregg_pred_jsonpath_strict(pred_json text) -> text`. As
    /// [`dregg_pred_jsonpath`] but every attribute atom carries an `exists(@.key)`
    /// boundness guard, so the jsonpath fails CLOSED on an absent key even under a
    /// `Not` — making it agree with the Rust `Pred::eval` fail-closed semantics
    /// unconditionally (not only on a fully-bound row). Use it when the row JSON
    /// may not bind every inspected attribute.
    #[pg_extern(immutable, parallel_safe, strict)]
    fn dregg_pred_jsonpath_strict(pred_json: &str) -> Option<String> {
        let pred: dregg_auth::credential::Pred = serde_json::from_str(pred_json).ok()?;
        crate::jsonpath::pred_to_jsonpath_strict(&pred)
    }

    /// `dregg_pred_matches(pred_json text, row jsonb) -> bool`. The ergonomic
    /// face: compile the predicate to a jsonpath and evaluate it over `row` in one
    /// call (`jsonb_path_exists`), so a policy or query reads
    /// `WHERE dregg_pred_matches($1, to_jsonb(t))`. TRUE iff `row` satisfies the
    /// caveat predicate; FALSE on a row that does not (or on a `pred_json` that
    /// does not parse — fail-closed). Uses the STRICT compile so an absent key
    /// fails closed even under negation, matching the Rust admit semantics.
    /// IMMUTABLE: pure in (predicate, row).
    #[pg_extern(immutable, parallel_safe, strict)]
    fn dregg_pred_matches(pred_json: &str, row: pgrx::JsonB) -> bool {
        let Ok(pred) = serde_json::from_str::<dregg_auth::credential::Pred>(pred_json) else {
            return false; // unparseable predicate ⇒ fail closed
        };
        let Some(path) = crate::jsonpath::pred_to_jsonpath_strict(&pred) else {
            return false;
        };
        // Evaluate the compiled jsonpath over the row via SPI (the same
        // jsonb_path_exists the read views use), so the in-SQL face and the view
        // face are the identical engine. Fail-closed on any SPI error.
        Spi::get_one_with_args(
            "SELECT jsonb_path_exists($1, $2::jsonpath)",
            &[row.into(), path.into()],
        )
        .ok()
        .flatten()
        .unwrap_or(false)
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

        // ===================================================================
        // Tier B THROUGH real SQL: the mirror's DDL + synthetic-turn rows, an
        // RLS-narrowing query, and the root-chain gate refusing a bad batch.
        //
        // This is the through-postgres twin of `examples/end_to_end.rs`: the
        // SAME synthetic ledger story (crate::synth), the SAME emitted DDL
        // (crate::mirror::ddl::tier_b), now installed in a real pg18 backend and
        // queried under real Row Level Security.
        // ===================================================================
        use crate::mirror::{MirrorBatch, RootChain};
        use crate::synth;

        /// Install the Tier-B schema from the Rust emitter (the exact SQL the
        /// extension ships), then load the synthetic committed turns as the
        /// `dregg_kernel` writer would. Returns nothing; the tables are live.
        fn install_tier_b_and_load_synth() {
            // The schema: via the dregg_install_schema() extern the quickstart
            // documents (which runs mirror::ddl::tier_b() — the same Rust that
            // defines the rows).
            let summary: String = Spi::get_one("SELECT dregg_install_schema()")
                .unwrap()
                .unwrap();
            assert!(summary.contains("Tier-B store installed"));

            // Load the synthetic story AS the kernel writer (the only role the
            // lockdown lets write). We run the root-chain tooth first — a row is
            // only written if its batch chained, mirroring Tier C's discipline.
            let story = synth::ledger_story();
            let mut chain = RootChain::resume(synth::GENESIS_ROOT, 0);
            for b in &story {
                chain.extend(b).expect("synthetic story must chain");
                write_batch(b);
            }
        }

        /// Render one accepted batch's rows as the writer's INSERTs and run them.
        /// The writer runs as the privileged connection role (a BYPASSRLS
        /// superuser in the harness) — exactly the trust position of the
        /// `dregg_kernel` SECURITY-DEFINER writer the emitted role model defines:
        /// it materializes verified-turn post-images wholesale, above the
        /// read-side RLS that gates applications. (The real M2 writer ships the
        /// MirrorBatch; here we inline it so the pg_test is node-free.)
        fn write_batch(b: &MirrorBatch) {
            let hx = |x: &[u8]| -> String { x.iter().map(|y| format!("{y:02x}")).collect() };
            let t = &b.turn;
            Spi::run(&format!(
                "INSERT INTO dregg.turns(ordinal,height,block_id,block_executed_up_to,\
                 turn_hash,creator,receipt_hash,ledger_root,prev_root) VALUES \
                 ({},{},'\\x{}',{},'\\x{}','\\x{}','\\x{}','\\x{}','\\x{}')",
                t.ordinal, t.height, hx(&t.block_id), t.block_executed_up_to,
                hx(&t.turn_hash), hx(&t.creator), hx(&t.receipt_hash),
                hx(&t.ledger_root), hx(&t.prev_root),
            ))
            .unwrap();
            for c in &b.cells {
                // Upsert via PostgreSQL 18 MERGE — the atomic node→pg row
                // materialization. The MERGE (with `merge_action()` + the pg18
                // `RETURNING old/new` balance delta) lives in the shipped
                // `dregg.merge_cell` function (the DDL emitter, crate::mirror::ddl);
                // we invoke it here through a plain SELECT so a later turn's
                // post-image overwrites the cell in one atomic statement, and the
                // returned '<ACTION> <DELTA>' tells us which arm fired and by how
                // much the balance moved. (docs/PG-DREGG-PG18.md §7.)
                let fj = c
                    .fields_json
                    .as_deref()
                    .map(|s| format!("'{}'::jsonb", s.replace('\'', "''")))
                    .unwrap_or_else(|| "NULL".to_string());
                let action: Option<String> = Spi::get_one(&format!(
                    "SELECT dregg.merge_cell('\\x{}'::bytea,'{}',{},{},'\\x'::bytea,{},\
                     '{}',{},'\\x{}'::bytea)",
                    hx(&c.cell_id), c.mode, c.balance, c.nonce, fj, c.lifecycle,
                    c.last_ordinal, hx(&c.cell_root),
                ))
                .unwrap();
                // pg18 dregg.merge_cell returns '<ACTION> <DELTA>' (e.g.
                // 'INSERT +1000000' / 'UPDATE -500') — merge_action() plus the
                // RETURNING old/new balance delta. Proof the MERGE arm fired.
                debug_assert!(
                    matches!(action.as_deref(), Some(a) if a.starts_with("INSERT ") || a.starts_with("UPDATE "))
                );
            }
            for cap in &b.caps {
                // The attenuation (allowed_effects) is carried so the pg17
                // JSON_TABLE view dregg.cap_attenuations can explode it into rows
                // (the no-amplification audit surface).
                let eff = cap
                    .allowed_effects_json
                    .as_deref()
                    .map(|s| format!("'{}'::jsonb", s.replace('\'', "''")))
                    .unwrap_or_else(|| "NULL".to_string());
                let exp = cap
                    .expires_at
                    .map(|e| e.to_string())
                    .unwrap_or_else(|| "NULL".to_string());
                Spi::run(&format!(
                    "INSERT INTO dregg.capabilities(holder,slot,target,permissions,\
                     allowed_effects,expires_at,last_ordinal) \
                     VALUES ('\\x{}',{},'\\x{}','{}'::jsonb,{},{},{})",
                    hx(&cap.holder), cap.slot, hx(&cap.target),
                    cap.permissions_json, eff, exp, cap.last_ordinal,
                ))
                .unwrap();
            }
        }

        /// A read-everything operator token and an ALICE-only attenuated token,
        /// minted under the test root (the configured issuer key).
        fn mirror_tokens(root: &RootKey) -> (String, String) {
            let operator = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
                ])
                .encode();
            let alice_only = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
                ])
                .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "a1".into(),
                })])
                .encode();
            (operator, alice_only)
        }

        /// Count `dregg.cells` rows visible under a token, as the unprivileged
        /// `dregg_reader` (so RLS actually filters; superusers BYPASS it).
        fn cells_visible(tok: &str) -> i64 {
            Spi::run(&format!("SET dregg.token = '{tok}'")).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let n = Spi::get_one::<i64>("SELECT count(*) FROM dregg.cells")
                .unwrap()
                .unwrap();
            Spi::run("RESET ROLE").unwrap();
            n
        }

        #[pg_test]
        fn tier_b_mirror_rls_narrows_cell_visibility() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            // Sanity: as the kernel/owner (RLS still FORCEd, but the cells_read
            // policy is TO dregg_reader; the writer sees its own rows only via a
            // direct count as a privileged role). Confirm three distinct cells
            // landed by counting AS the reader under a wide-open operator token.
            let (operator, alice_only) = mirror_tokens(&root);

            // Operator sees all three cells (TREASURY, ALICE, BOB).
            let n_op = cells_visible(&operator);
            assert_eq!(n_op, 3, "operator token should see all three mirror cells");

            // The ALICE-only attenuated token sees a STRICT SUBSET — only ALICE's
            // cell, whose id hex starts `a1`. The no-amplify property, through
            // real Tier-B RLS on the mirror.
            let n_alice = cells_visible(&alice_only);
            assert_eq!(n_alice, 1, "attenuated token should see only ALICE's cell");
            assert!(n_alice < n_op, "attenuation must strictly narrow mirror visibility");
        }

        #[pg_test]
        fn tier_b_query_surface_views_resolve() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            let (operator, _) = mirror_tokens(&root);

            // The dregg-developer query surface: the cell_balances view, the
            // cap_edges delegation view, and the receipt_chain all resolve and
            // are RLS-gated through the operator token.
            Spi::run(&format!("SET dregg.token = '{operator}'")).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();

            // Balance view: the richest cell is TREASURY at 999_500.
            let top: i64 = Spi::get_one("SELECT max(balance) FROM dregg.cell_balances")
                .unwrap()
                .unwrap();
            assert_eq!(top, 999_500, "TREASURY is the richest visible cell");

            // The delegation edge ALICE→BOB is in cap_edges (holder gated; the
            // operator can read it).
            let edges: i64 = Spi::get_one("SELECT count(*) FROM dregg.cap_edges")
                .unwrap()
                .unwrap();
            assert_eq!(edges, 1, "the grant turn's ALICE→BOB edge is queryable");

            // The receipt chain is walkable in order; four turns landed.
            let turns: i64 = Spi::get_one("SELECT count(*) FROM dregg.receipt_chain")
                .unwrap()
                .unwrap();
            assert_eq!(turns, 4, "all four committed turns are in the receipt chain");
            Spi::run("RESET ROLE").unwrap();
        }

        #[pg_test]
        fn tier_b_apps_cannot_write_state() {
            // The spine: applications (dregg_reader) get SELECT only — state
            // mutates ONLY through verified turns. We assert the privilege
            // lockdown declaratively via the catalog (has_table_privilege),
            // which does not abort the SPI transaction the way triggering the
            // ERROR would: the reader HAS select, and has NO insert/update/delete
            // on any dregg state table. (The emitted DDL's REVOKE + the
            // SELECT-only GRANT are what this verifies are in force.)
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            let can = |priv_: &str| -> bool {
                Spi::get_one::<bool>(&format!(
                    "SELECT has_table_privilege('dregg_reader', 'dregg.cells', '{priv_}')"
                ))
                .unwrap()
                .unwrap()
            };
            assert!(can("SELECT"), "the reader must be able to SELECT state");
            assert!(!can("INSERT"), "the reader must NOT be able to INSERT state");
            assert!(!can("UPDATE"), "the reader must NOT be able to UPDATE state");
            assert!(!can("DELETE"), "the reader must NOT be able to DELETE state");

            // And the kernel writer DOES hold the write privileges (the only
            // role that may materialize post-images).
            let kernel = |priv_: &str| -> bool {
                Spi::get_one::<bool>(&format!(
                    "SELECT has_table_privilege('dregg_kernel', 'dregg.cells', '{priv_}')"
                ))
                .unwrap()
                .unwrap()
            };
            assert!(kernel("INSERT"), "the kernel writer must hold INSERT");
            assert!(kernel("UPDATE"), "the kernel writer must hold UPDATE");
        }

        #[pg_test]
        fn pg17_merge_upsert_and_json_table_views() {
            // The pg17 feature leverage, through real SQL:
            //   (1) the MERGE-based mirror upsert in write_batch fires both arms
            //       across the synthetic story (ALICE is inserted at ord 1, then
            //       UPDATEd at ord 2 and ord 3 — a later turn's post-image wins);
            //   (2) the JSON_TABLE projection views (cap_attenuations, cell_fields)
            //       resolve and explode the embedded jsonb into rows.
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth(); // runs the MERGE path 6 times

            let (operator, _) = mirror_tokens(&root);
            Spi::run(&format!("SET dregg.token = '{operator}'")).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();

            // MERGE update arm won: ALICE's final post-image is nonce=2 (ord 3),
            // not the ord-1 insert's nonce=0 — a later turn overwrote in place,
            // and there is exactly ONE ALICE row (no duplicate from re-insert).
            // (Aggregates so the scalar read always yields a row.)
            let alice_hex: String =
                crate::synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();
            let alice_nonce: i64 = Spi::get_one(&format!(
                "SELECT coalesce(max(nonce), -1) FROM dregg.cells \
                 WHERE cell_id = '\\x{alice_hex}'::bytea"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(alice_nonce, 2, "MERGE update arm: ALICE's latest post-image wins");
            let alice_rows: i64 = Spi::get_one(&format!(
                "SELECT count(*) FROM dregg.cells WHERE cell_id = '\\x{alice_hex}'::bytea"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(alice_rows, 1, "MERGE keeps exactly one row per cell (no dup insert)");

            // JSON_TABLE view cell_fields: the decoded balance/nonce slots come
            // out of fields_json as typed columns. TREASURY's row shows 999_500.
            let treasury_bal: i64 = Spi::get_one(
                "SELECT coalesce(max(balance), -1) FROM dregg.cell_fields",
            )
            .unwrap()
            .unwrap();
            assert_eq!(treasury_bal, 999_500, "cell_fields JSON_TABLE projects the balance slot");

            // JSON_TABLE view cap_attenuations: the grant turn's allowed_effects
            // array `["transfer"]` is exploded into one effect row for ALICE→BOB.
            let n_effects: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.cap_attenuations",
            )
            .unwrap()
            .unwrap();
            assert_eq!(n_effects, 1, "exactly one attenuated effect across the story");
            let effect: Option<String> = Spi::get_one::<String>(
                "SELECT string_agg(effect, ',') FROM dregg.cap_attenuations",
            )
            .unwrap();
            assert_eq!(effect.as_deref(), Some("transfer"),
                "cap_attenuations JSON_TABLE explodes the allowed_effects array");
            Spi::run("RESET ROLE").unwrap();
        }

        // ===================================================================
        // The pg18 leverage, through real SQL (docs/PG-DREGG-PG18.md):
        //   (1) MERGE + RETURNING old/new — dregg.merge_cell returns the action
        //       AND the balance delta computed from the pre-image, in one atomic
        //       statement (impossible pre-18 without a separate pre-read);
        //   (2) VIRTUAL generated columns (the pg18 default) — cell_root_hex /
        //       balance_field are computed on READ and equal their canonical
        //       source, with no stored bytes;
        //   (3) uuidv7() — the submit_queue key is temporally sortable.
        // ===================================================================
        #[pg_test]
        fn pg18_merge_returning_delta_virtual_columns_and_uuidv7() {
            let root = root();
            assert_issuer(&root);
            let summary: String =
                Spi::get_one("SELECT dregg_install_schema()").unwrap().unwrap();
            assert!(summary.contains("Tier-B store installed"));
            Spi::run("SET ROLE dregg_kernel").unwrap(); // BYPASSRLS writer

            // A turns row to satisfy the cells FK (last_ordinal references it).
            Spi::run(
                "INSERT INTO dregg.turns(ordinal,height,block_id,block_executed_up_to,\
                 turn_hash,creator,receipt_hash,ledger_root,prev_root) VALUES \
                 (0,0,'\\x22',0,'\\x33','\\xc0','\\x44','\\x11','\\x00')",
            )
            .unwrap();

            // (1a) INSERT arm: merge a fresh cell at balance 1_000_000. pg18
            // RETURNING old/new ⇒ old.balance is NULL ⇒ delta = +1000000.
            let cid = "c000000000000000000000000000000000000000000000000000000000000000";
            let ins: String = Spi::get_one(&format!(
                "SELECT dregg.merge_cell('\\x{cid}'::bytea,'Hosted',1000000,0,'\\x'::bytea,\
                 '{{\"balance\":1000000,\"nonce\":0}}'::jsonb,'Active',0,'\\x{cid}'::bytea)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(ins, "INSERT +1000000", "pg18 RETURNING new-old delta on the INSERT arm");

            // (1b) UPDATE arm: re-merge the same cell down to 999_500. pg18 reads
            // old.balance = 1_000_000 in the same statement ⇒ delta = -500.
            let upd: String = Spi::get_one(&format!(
                "SELECT dregg.merge_cell('\\x{cid}'::bytea,'Hosted',999500,1,'\\x'::bytea,\
                 '{{\"balance\":999500,\"nonce\":1}}'::jsonb,'Active',0,'\\x{cid}'::bytea)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(upd, "UPDATE -500", "pg18 RETURNING new-old delta on the UPDATE arm");

            // (2) VIRTUAL generated columns: cell_root_hex / balance_field are
            // read-time projections equal to their canonical source, with no
            // stored bytes. (cell_hex stays STORED because it is indexed.)
            let consistent: i64 = Spi::get_one(&format!(
                "SELECT count(*) FROM dregg.cells WHERE cell_id='\\x{cid}'::bytea \
                 AND cell_root_hex = encode(cell_root,'hex') \
                 AND balance_field = (fields_json->>'balance')::bigint"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(consistent, 1, "VIRTUAL generated columns equal their canonical source on read");
            // pg_attribute records cell_root_hex / balance_field as virtual
            // (attgenerated='v') and cell_hex as stored ('s') — the pg18 kinds.
            let kinds: Option<String> = Spi::get_one(
                "SELECT string_agg(attname || ':' || attgenerated::text, ',' ORDER BY attname) \
                 FROM pg_attribute \
                 WHERE attrelid = 'dregg.cells'::regclass \
                   AND attname IN ('cell_hex','cell_root_hex','balance_field')",
            )
            .unwrap();
            assert_eq!(
                kinds.as_deref(),
                Some("balance_field:v,cell_hex:s,cell_root_hex:v"),
                "pg18 generated-column kinds: cell_hex STORED (indexed), the rest VIRTUAL"
            );
            Spi::run("RESET ROLE").unwrap();

            // (3) uuidv7(): the submit_queue id default is the temporally-sortable
            // v7 (version nibble 7), so two rows inserted in order sort by id.
            let o: String = Spi::get_one("SELECT dregg_install_write_outbox()").unwrap().unwrap();
            assert!(o.contains("write outbox installed"));
            let ver: Option<i32> = Spi::get_one(
                "SELECT get_byte(uuid_send(uuidv7()), 6) >> 4",
            )
            .unwrap();
            assert_eq!(ver, Some(7), "uuidv7() mints a version-7 (temporally sortable) uuid");
        }

        // ===================================================================
        // The pg17 SQL/JSON jsonpath predicate surface (docs/PG-DREGG-PG18.md
        // §2): a dregg `Pred` compiled to a jsonpath and evaluated IN postgres,
        // proven to AGREE with the real chain-verified `dregg_cap_admits`.
        // ===================================================================

        #[pg_test]
        fn pred_jsonpath_matches_agree_with_real_authz() {
            let root = root();
            assert_issuer(&root);

            // The SAME authority, two shapes: a minted credential (the real
            // chain-verified authz path) AND its `Pred` as JSON (the jsonpath
            // read path). They must give the identical admit verdict per row.
            // read on org/42/ until clock 2000, the canonical M1 caveat shape.
            let tok = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "org/42/".into() }),
                    Caveat::FirstParty(Pred::NotAfter { at: 2000 }),
                ])
                .encode();
            // The matching Pred (the algebra the caveat chain encodes), as JSON.
            let pred_json = serde_json::to_string(&Pred::AllOf(vec![
                Pred::AttrEq { key: "action".into(), value: "read".into() },
                Pred::AttrPrefix { key: "resource".into(), prefix: "org/42/".into() },
                Pred::NotAfter { at: 2000 },
            ]))
            .unwrap();

            // The compiled jsonpath is well-formed and non-empty.
            let path: Option<String> = Spi::get_one_with_args(
                "SELECT dregg_pred_jsonpath($1)",
                &[pred_json.as_str().into()],
            )
            .unwrap();
            let path = path.expect("a first-party Pred compiles to a jsonpath");
            assert!(path.starts_with("$ ? ("), "the path is a filter expression: {path}");

            // A matrix of rows: the chain-verified `dregg_cap_admits` verdict and
            // the `dregg_pred_matches` (jsonpath) verdict must be EQUAL on each.
            let cases = [
                ("org/42/public/doc1", 1000_i64),
                ("org/42/private/doc9", 1000),
                ("org/99/x", 1000),
                ("org/42/public/doc1", 3000), // past NotAfter
            ];
            for (res, clk) in cases {
                let authz: bool = Spi::get_one_with_args(
                    "SELECT dregg_cap_admits($1, 'read', $2, $3)",
                    &[tok.as_str().into(), res.into(), clk.into()],
                )
                .unwrap()
                .unwrap();
                let jsonpath: bool = Spi::get_one_with_args(
                    "SELECT dregg_pred_matches($1, jsonb_build_object('action','read','resource',$2::text,'clock',$3::bigint))",
                    &[pred_json.as_str().into(), res.into(), clk.into()],
                )
                .unwrap()
                .unwrap();
                assert_eq!(
                    authz, jsonpath,
                    "the jsonpath of a Pred must admit exactly what the chain-verified \
                     authz admits (res={res}, clk={clk}): authz={authz} jsonpath={jsonpath}"
                );
            }

            // An unparseable predicate fails closed (NULL path / false match).
            let bad_path: Option<String> =
                Spi::get_one_with_args("SELECT dregg_pred_jsonpath($1)", &["not json".into()])
                    .unwrap();
            assert!(bad_path.is_none(), "a non-Pred string yields NULL (fail-closed)");
            let bad_match: bool = Spi::get_one_with_args(
                "SELECT dregg_pred_matches($1, '{}'::jsonb)",
                &["not json".into()],
            )
            .unwrap()
            .unwrap();
            assert!(!bad_match, "an unparseable predicate matches nothing (fail-closed)");
        }

        #[pg_test]
        fn pred_jsonpath_filters_the_mirror_as_a_read() {
            // The read win: the compiled jsonpath used DIRECTLY in a SQL query over
            // the mirror — "which cells' state satisfies this caveat?" as plain SQL,
            // no per-row extern. We build a small jsonb-state table and filter it by
            // a Pred-derived jsonpath via jsonb_path_exists.
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            // A predicate over the cell state JSON: balance >= 500 is not in the
            // Pred algebra (it is attribute/prefix/temporal), so we filter on a
            // resource-prefix predicate over a synthesized doc per cell instead:
            // "the cell hex starts with c0" (TREASURY only).
            let pred_json = serde_json::to_string(&Pred::AttrPrefix {
                key: "cell".into(),
                prefix: "c0".into(),
            })
            .unwrap();

            // For each cell, build {cell: <hex>} and keep those the jsonpath admits.
            Spi::run("SET ROLE dregg_kernel").unwrap(); // BYPASSRLS so we see all cells
            let matched: i64 = Spi::get_one_with_args(
                "SELECT count(*) FROM dregg.cells \
                 WHERE jsonb_path_exists(jsonb_build_object('cell', encode(cell_id,'hex')), \
                                         dregg_pred_jsonpath($1)::jsonpath)",
                &[pred_json.as_str().into()],
            )
            .unwrap()
            .unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(matched, 1, "exactly one cell (TREASURY, c0…) matches the c0 prefix predicate");
        }

        // ===================================================================
        // The pg17 turn-effects JSON_TABLE view + canonical_cells (builtin-C
        // collation) over the verified store (docs/PG-DREGG-PG18.md §3,§5).
        // ===================================================================

        #[pg_test]
        fn turn_effects_and_canonical_views_resolve_over_the_store() {
            let root = root();
            assert_issuer(&root);
            // Land the well-formed story through the Tier-C commit_log gate, so the
            // commit_log carries the touched-cell payloads turn_effects explodes.
            install_tier_c_and_submit_story();

            // turn_effects: one row per (ordinal, touched cell). The genesis turn
            // funded TREASURY; the transfer touched TREASURY + ALICE. So ordinal 0
            // has 1 effect row and ordinal 1 has 2.
            Spi::run("SET ROLE dregg_kernel").unwrap();
            let ord0: i64 = Spi::get_one("SELECT count(*) FROM dregg.turn_effects WHERE ordinal = 0")
                .unwrap()
                .unwrap();
            let ord1: i64 = Spi::get_one("SELECT count(*) FROM dregg.turn_effects WHERE ordinal = 1")
                .unwrap()
                .unwrap();
            assert_eq!(ord0, 1, "genesis turn has one touched-cell effect row (TREASURY)");
            assert!(ord1 >= 2, "the transfer turn touched at least TREASURY + ALICE");

            // canonical_cells: the builtin-C-collation byte-order. The first row by
            // cell_hex is ALICE (a1…) before TREASURY (c0…) — deterministic,
            // version-stable ordering (a1 < c0 byte-wise).
            let first: Option<String> =
                Spi::get_one("SELECT cell_hex FROM dregg.canonical_cells LIMIT 1").unwrap();
            assert_eq!(
                first.as_deref().map(|s| &s[..2]),
                Some("a1"),
                "canonical_cells orders by builtin-C byte order: a1 (ALICE) sorts first"
            );

            // The generated columns materialized: cell_hex + cell_root_hex are the
            // pg-maintained hex of the canonical bytea (cannot drift).
            let hexes_consistent: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.cells \
                 WHERE cell_hex IS DISTINCT FROM encode(cell_id,'hex') \
                    OR cell_root_hex IS DISTINCT FROM encode(cell_root,'hex')",
            )
            .unwrap()
            .unwrap();
            assert_eq!(hexes_consistent, 0, "generated hex columns equal the canonical bytea's hex");
            Spi::run("RESET ROLE").unwrap();
        }

        // ===================================================================
        // The pg17 LOGIN EVENT TRIGGER authz binding (docs/PG-DREGG-PG18.md §6):
        // a role's session is bound to its dregg capability AT LOGIN, so a plain
        // SELECT is already RLS-narrowed with no app-side token presentation.
        //
        // NOTE: the `login` event fires on a NEW connection, which the in-backend
        // #[pg_test] cannot trigger (it runs inside one already-open connection).
        // So this test asserts the BINDING LOGIC directly — calling the same
        // body the event trigger runs (dregg.on_login via a manual invocation of
        // its effect) and confirming the GUC is set + RLS then narrows. The live
        // cross-connection proof is in sql/e2e-live.sql (a real psql reconnect).
        // ===================================================================

        #[pg_test]
        fn login_binding_sets_the_session_token_and_narrows_rls() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            let o: String = Spi::get_one("SELECT dregg_install_login_binding()").unwrap().unwrap();
            assert!(o.contains("login binding installed"));

            // Map a role to an ALICE-only token (read on a1*). The event trigger
            // would set dregg.token from this row on connect; here we apply that
            // same effect (set_config) to assert the downstream RLS narrowing, the
            // observable consequence the trigger exists to produce.
            let alice_tok = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "a1".into() }),
                ])
                .encode();
            let alice_hex: String = synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();
            Spi::run_with_args(
                "INSERT INTO dregg.role_identity (pg_role, agent, default_token) \
                 VALUES ('dregg_reader', decode($1,'hex'), $2) \
                 ON CONFLICT (pg_role) DO UPDATE SET default_token = EXCLUDED.default_token",
                &[alice_hex.as_str().into(), alice_tok.as_str().into()],
            )
            .unwrap();

            // The identity row is readable by the kernel (the SECURITY DEFINER hook
            // runs as), proving the lookup the trigger does resolves.
            let bound: Option<String> = Spi::get_one(
                "SELECT default_token FROM dregg.role_identity WHERE pg_role = 'dregg_reader'",
            )
            .unwrap();
            assert!(bound.is_some(), "the role's identity row carries its bound token");

            // Apply the trigger's effect (set the session token from the row) and
            // confirm the RLS then narrows: as dregg_reader, only ALICE's cell is
            // visible — the same outcome a login-bound connection gets.
            Spi::run(&format!("SET dregg.token = '{}'", bound.unwrap())).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let visible: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(visible, 1, "the login-bound token narrows the reader to ALICE's cell only");
        }

        #[pg_test]
        fn root_chain_gate_refuses_a_tampered_batch() {
            // The Tier-C anti-substitution tooth (the cheap structural half the
            // even read-only mirror enforces), exercised in the backend process:
            // the RootChain accepts the well-formed story and REFUSES a forged
            // ord-2 batch whose prev_root was substituted, leaving the head put.
            let story = synth::ledger_story();
            let mut chain = RootChain::resume(synth::GENESIS_ROOT, 0);
            chain.extend(&story[0]).unwrap();
            chain.extend(&story[1]).unwrap();
            let head_before = chain.head();
            let err = chain.extend(&synth::tampered_batch_at_2()).unwrap_err();
            assert!(
                matches!(err, crate::mirror::ChainRefusal::RootMismatch { .. }),
                "a tampered batch must be refused by the root-chain tooth"
            );
            assert_eq!(chain.head(), head_before, "a refused batch must not move the head");
        }

        // ===================================================================
        // TIER C THROUGH real SQL: the verified-store gate on a live pg18. The
        // commit_log is the ONLY door to state; its trigger runs the REAL chain
        // re-validator (dregg_verify_turn, backed by mirror::verify_chain_step)
        // and materializes the post-image — and REFUSES a tampered batch by the
        // database engine itself. This is the load-bearing "pg re-validates,
        // never trusts" proof (docs/PG-DREGG.md §10).
        // ===================================================================

        /// Install Tier B + Tier C, then submit one batch's verified post-image
        /// through `dregg.commit_log` (the turn metadata + the touched-cell
        /// post-images as the trigger's jsonb payload, `MirrorBatch::cells_json`).
        /// Returns the SPI result of the INSERT (so the caller can assert it
        /// succeeded or, for a tamper, that it RAISEd).
        fn submit_through_commit_log(b: &MirrorBatch) -> Result<(), pgrx::spi::Error> {
            let hx = |x: &[u8]| -> String { x.iter().map(|y| format!("{y:02x}")).collect() };
            let t = &b.turn;
            let cells_json = b.cells_json().replace('\'', "''");
            Spi::run(&format!(
                "INSERT INTO dregg.commit_log(ordinal,height,block_id,block_executed_up_to,\
                 turn_hash,creator,receipt_hash,ledger_root,prev_root,cells) VALUES \
                 ({},{},'\\x{}',{},'\\x{}','\\x{}','\\x{}','\\x{}','\\x{}','{}'::jsonb)",
                t.ordinal, t.height, hx(&t.block_id), t.block_executed_up_to,
                hx(&t.turn_hash), hx(&t.creator), hx(&t.receipt_hash),
                hx(&t.ledger_root), hx(&t.prev_root), cells_json,
            ))
        }

        /// Install Tier B + Tier C and submit the well-formed synthetic story
        /// through the `dregg.commit_log` gate. Returns the four batches (so the
        /// caller can build a forged follow-up). Each INSERT runs the trigger:
        /// `dregg_verify_turn` (chain re-validation) → record turn →
        /// MERGE-materialize cells.
        fn install_tier_c_and_submit_story() -> Vec<MirrorBatch> {
            let summary: String =
                Spi::get_one("SELECT dregg_install_schema()").unwrap().unwrap();
            assert!(summary.contains("Tier-B store installed"));
            let c_summary: String =
                Spi::get_one("SELECT dregg_install_tier_c()").unwrap().unwrap();
            assert!(c_summary.contains("Tier-C verified-store gate installed"));
            let story = synth::ledger_story();
            for b in &story {
                submit_through_commit_log(b).unwrap_or_else(|e| {
                    panic!("the gate refused a well-formed turn {}: {e}", b.turn.ordinal)
                });
            }
            story
        }

        #[pg_test]
        fn tier_c_commit_log_gate_materializes_verified_turns() {
            let root = root();
            assert_issuer(&root);
            // Submit the well-formed story THROUGH the verifying gate (the ONLY
            // door to state). All four turns are admitted by dregg_verify_turn and
            // their post-images materialized in the same transaction.
            let _story = install_tier_c_and_submit_story();

            // The post-state is materialized: four turns recorded, three distinct
            // cells (TREASURY/ALICE/BOB) with the LATEST post-image — ALICE's nonce
            // is 2 (from ord 3): the MERGE update arm won, exactly as the mirror
            // path materializes. State exists ONLY because a verified turn produced
            // it through the gate.
            let turns: i64 = Spi::get_one("SELECT count(*) FROM dregg.turns").unwrap().unwrap();
            assert_eq!(turns, 4, "all four verified turns recorded through the gate");
            let cells: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();
            assert_eq!(cells, 3, "three distinct cells materialized (TREASURY/ALICE/BOB)");
            let alice_hex: String =
                crate::synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();
            let alice_nonce: i64 = Spi::get_one(&format!(
                "SELECT max(nonce) FROM dregg.cells WHERE cell_id = '\\x{alice_hex}'::bytea"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(alice_nonce, 2, "the gate materialized ALICE's latest post-image (MERGE)");

            // The receipt chain the gate built is a walkable hash chain: each row's
            // prev_root is the prior row's ledger_root (the light-client tooth).
            let breaks: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.turns t \
                 JOIN dregg.turns p ON p.ordinal = t.ordinal - 1 \
                 WHERE t.prev_root IS DISTINCT FROM p.ledger_root",
            )
            .unwrap()
            .unwrap();
            assert_eq!(breaks, 0, "the gate-built turns table is an unbroken hash chain");
        }

        /// THE anti-substitution proof, through the database engine: after the
        /// well-formed story (head at ord 3, next-expected ord 4), a forged ord-4
        /// batch whose `prev_root` was substituted is REFUSED by the trigger's
        /// `dregg_verify_turn` — the INSERT RAISEs the exact anti-substitution
        /// error, so no forged state can enter. `#[pg_test(error = …)]` asserts
        /// the precise message: the gate, not a trusted writer, refuses.
        #[pg_test(error = "dregg: turn 4 does not chain onto the head root — refused (anti-substitution)")]
        fn tier_c_gate_refuses_a_tampered_batch_by_raising() {
            let root = root();
            assert_issuer(&root);
            install_tier_c_and_submit_story();
            // A forged ord-4 (next-expected, so the ordinal gap check passes) whose
            // prev_root is the substituted [0x99;32], NOT the real head root. The
            // gate's dregg_verify_turn returns false ⇒ the trigger RAISEs.
            let mut forged = synth::tampered_batch_at_2();
            forged.turn.ordinal = 4;
            forged.cells[0].last_ordinal = 4;
            submit_through_commit_log(&forged)
                .expect("submit returns; the RAISE surfaces as the test's expected ERROR");
        }

        // ===================================================================
        // THE WRITE PATH through real SQL: a pg-user submits a verified turn
        // FROM postgres, RLS-gated to exactly the agents its capability admits
        // `submit` on (docs/PG-DREGG.md §11). dregg_submit_turn enqueues into
        // dregg.submit_queue; the node drains it through the real executor.
        // ===================================================================

        /// A token that admits `submit` on the agent whose hex starts `prefix`
        /// (e.g. "a1" for ALICE), minted under the test root.
        fn submit_token(root: &RootKey, prefix: &str) -> String {
            root.mint([
                Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "submit".into() }),
                Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: prefix.into() }),
            ])
            .encode()
        }

        #[pg_test]
        fn write_path_submit_turn_enqueues_under_an_authorized_token() {
            let root = root();
            assert_issuer(&root);
            let summary: String =
                Spi::get_one("SELECT dregg_install_schema()").unwrap().unwrap();
            assert!(summary.contains("Tier-B store installed"));
            let o_summary: String =
                Spi::get_one("SELECT dregg_install_write_outbox()").unwrap().unwrap();
            assert!(o_summary.contains("write outbox installed"));

            let alice_hex: String = synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();
            // Present an ALICE-submit token and enqueue a turn FOR ALICE as the
            // unprivileged dregg_reader (so the submit_gate RLS policy bites).
            Spi::run(&format!("SET dregg.token = '{}'", submit_token(&root, "a1"))).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let id: Option<pgrx::Uuid> = Spi::get_one(&format!(
                "SELECT dregg_submit_turn('\\xdeadbeef'::bytea, '\\x{alice_hex}'::bytea)"
            ))
            .unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert!(id.is_some(), "an authorized submit must enqueue and return an id");

            // The row landed as 'pending' for ALICE (the node will drain it).
            let pending: i64 = Spi::get_one(&format!(
                "SELECT count(*) FROM dregg.submit_queue \
                 WHERE agent = '\\x{alice_hex}'::bytea AND status = 'pending'"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(pending, 1, "the authorized turn is queued pending for the node");
        }

        #[pg_test(error = "new row violates row-level security policy for table \"submit_queue\"")]
        fn write_path_rls_refuses_submitting_for_an_unauthorized_agent() {
            let root = root();
            assert_issuer(&root);
            Spi::get_one::<String>("SELECT dregg_install_schema()").unwrap();
            Spi::get_one::<String>("SELECT dregg_install_write_outbox()").unwrap();

            let bob_hex: String = synth::BOB.iter().map(|b| format!("{b:02x}")).collect();
            // Present an ALICE-only submit token, then try to submit a turn FOR
            // BOB. The submit_gate WITH CHECK (dregg_admits('submit', bob_hex))
            // is FALSE under an a1-prefixed token, so RLS refuses the INSERT — a
            // role cannot submit a turn its capability does not authorize.
            Spi::run(&format!("SET dregg.token = '{}'", submit_token(&root, "a1"))).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            // This RAISEs the RLS violation, which is the test's expected ERROR.
            let _: Option<pgrx::Uuid> = Spi::get_one(&format!(
                "SELECT dregg_submit_turn('\\xdeadbeef'::bytea, '\\x{bob_hex}'::bytea)"
            ))
            .unwrap();
        }

        // ===================================================================
        // The pg18 leverage WIRED in the thoroughness pass (docs/PG-DREGG-PG18.md
        // §4/§6/§7/§8 + docs/PG-DREGG.md §14.3), each executed on the live pg18.
        // ===================================================================

        /// pg18 B-tree SKIP SCAN: the composite `cells_by_mode_balance (mode,
        /// balance)` index serves a `WHERE balance = …` query whose LEADING column
        /// (`mode`) is unconstrained — the planner skips through the few `mode`
        /// prefixes rather than seq-scanning. We assert the chosen plan is an
        /// index scan over that index (with seqscan disabled to force the planner
        /// to use the index path it can, which pre-18 it could not for an
        /// unconstrained leading column). This is real pg18 leverage, on real rows.
        #[pg_test]
        fn pg18_skip_scan_serves_balance_with_unconstrained_leading_mode() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            Spi::run("SET ROLE dregg_kernel").unwrap(); // BYPASSRLS writer

            // Load enough rows that the planner prefers the index (a tiny table is
            // always a seq scan). Insert many Hosted cells with distinct balances,
            // chaining off the existing turns (last_ordinal references turn 0).
            Spi::run(
                "INSERT INTO dregg.cells \
                   (cell_id, mode, balance, nonce, fields, fields_json, lifecycle, last_ordinal, cell_root) \
                 SELECT decode(lpad(to_hex(1000 + g), 64, '0'), 'hex'), \
                        CASE WHEN g % 2 = 0 THEN 'Hosted' ELSE 'Sovereign' END, \
                        g, 0, '\\x'::bytea, \
                        jsonb_build_object('balance', g, 'nonce', 0), 'Active', 0, \
                        decode(lpad(to_hex(1000 + g), 64, '0'), 'hex') \
                 FROM generate_series(1, 4000) g \
                 ON CONFLICT (cell_id) DO NOTHING",
            )
            .unwrap();
            Spi::run("ANALYZE dregg.cells").unwrap();
            // Force the index path so we observe skip scan (pre-18 this query would
            // have to fall back to a seq scan or full index scan).
            Spi::run("SET enable_seqscan = off").unwrap();

            // Collect the plain-text EXPLAIN rows and assert the (mode,balance) index
            // serves a balance-only predicate — `mode` (the leading column) is
            // unconstrained, so the index path IS pg18 skip scan.
            let lines: Vec<String> = Spi::connect(|client| {
                let mut out = Vec::new();
                let tup = client
                    .select(
                        "EXPLAIN (COSTS off) SELECT cell_id FROM dregg.cells WHERE balance = 2000",
                        None,
                        &[],
                    )
                    .expect("EXPLAIN runs");
                for row in tup {
                    if let Ok(Some(s)) = row.get::<String>(1) {
                        out.push(s);
                    }
                }
                out
            });
            Spi::run("SET enable_seqscan = on").unwrap();
            Spi::run("RESET ROLE").unwrap();
            let joined = lines.join("\n");
            assert!(
                joined.contains("cells_by_mode_balance"),
                "the (mode,balance) index serves a balance-only query via skip scan; plan was:\n{joined}"
            );
            // And the Index Cond is on balance (the leading mode column is skipped).
            assert!(
                joined.contains("balance = 2000") || joined.to_lowercase().contains("index cond"),
                "the index condition is on balance (mode skipped); plan was:\n{joined}"
            );
        }

        /// pg15 SECURITY_INVOKER views (docs/PG-DREGG.md §14.3, wired): the dev
        /// views run with the INVOKER's privileges, so the base-table RLS narrows a
        /// reader THROUGH the view. We assert (a) the reloption is set on every
        /// dev-view, and (b) the narrowing actually bites: an ALICE-only token sees
        /// only ALICE's cell through `dregg.cell_balances` (the view), not just the
        /// base table — RLS-through-views by declaration, not incidentally.
        #[pg_test]
        fn pg15_security_invoker_views_enforce_rls_through_the_view() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            // (a) every dev-view carries security_invoker=true in its reloptions.
            let non_invoker: i64 = Spi::get_one(
                "SELECT count(*) FROM pg_class c \
                 JOIN pg_namespace n ON n.oid = c.relnamespace \
                 WHERE n.nspname = 'dregg' AND c.relkind = 'v' \
                   AND c.relname IN ('cap_edges','cell_balances','receipt_chain', \
                                     'cap_attenuations','cell_fields','canonical_cells') \
                   AND NOT (coalesce(array_to_string(c.reloptions, ','), '') \
                            LIKE '%security_invoker=true%')",
            )
            .unwrap()
            .unwrap();
            assert_eq!(non_invoker, 0, "every dev-view must be security_invoker=true");

            // (b) the narrowing bites THROUGH the view. Grant the reader SELECT on
            // the view, present an ALICE-only token, and count cell_balances rows as
            // the unprivileged reader: only ALICE's cell (a1…) is visible.
            let alice_only = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "a1".into() }),
                ])
                .encode();
            Spi::run(&format!("SET dregg.token = '{alice_only}'")).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let visible: i64 = Spi::get_one("SELECT count(*) FROM dregg.cell_balances")
                .unwrap()
                .unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(
                visible, 1,
                "the security_invoker view narrows the reader to ALICE's cell — RLS through the view"
            );
        }

        /// pg18 `RETURNING WITH (OLD/NEW)` typed applicator (docs/PG-DREGG-PG18.md
        /// §7, wired): `dregg.merge_cell_delta` returns (action, balance_delta,
        /// nonce_delta) read from the pre-image in one atomic MERGE. We exercise
        /// the INSERT arm (delta = full amount), the UPDATE arm (signed delta +
        /// nonce delta), AND — the payoff — assert CONSERVATION directly off the
        /// applicator: the per-cell balance deltas of a transfer sum to zero.
        #[pg_test]
        fn pg18_merge_cell_delta_typed_and_conservation_off_the_applicator() {
            let root = root();
            assert_issuer(&root);
            let summary: String =
                Spi::get_one("SELECT dregg_install_schema()").unwrap().unwrap();
            assert!(summary.contains("Tier-B store installed"));
            Spi::run("SET ROLE dregg_kernel").unwrap();
            Spi::run(
                "INSERT INTO dregg.turns(ordinal,height,block_id,block_executed_up_to,\
                 turn_hash,creator,receipt_hash,ledger_root,prev_root) VALUES \
                 (0,0,'\\x22',0,'\\x33','\\xc0','\\x44','\\x11','\\x00')",
            )
            .unwrap();

            // The OUT params are read via a positional SELECT against the function
            // (portable + explicit across pgrx versions).
            // Fresh cell: INSERT arm ⇒ balance_delta = full amount, nonce_delta = 0.
            let fid = "f000000000000000000000000000000000000000000000000000000000000000";
            let ins = Spi::get_one::<String>(&format!(
                "SELECT action||' '||balance_delta||' '||nonce_delta \
                 FROM dregg.merge_cell_delta('\\x{fid}'::bytea,'Hosted',5000,0,\
                 '\\x'::bytea,'{{\"balance\":5000,\"nonce\":0}}'::jsonb,'Active',0,'\\x{fid}'::bytea)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(ins, "INSERT 5000 0", "INSERT arm: balance_delta is the full amount, no pre-image nonce");
            // UPDATE arm on the same cell: signed balance delta (−500) + nonce delta (+1).
            let upd = Spi::get_one::<String>(&format!(
                "SELECT action||' '||balance_delta||' '||nonce_delta \
                 FROM dregg.merge_cell_delta('\\x{fid}'::bytea,'Hosted',4500,1,\
                 '\\x'::bytea,'{{\"balance\":4500,\"nonce\":1}}'::jsonb,'Active',0,'\\x{fid}'::bytea)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(upd, "UPDATE -500 1", "UPDATE arm: signed balance + nonce deltas from the pre-image");

            // CONSERVATION off the applicator: a transfer TREASURY→ALICE→BOB whose
            // per-cell balance deltas (read from the pre-image by the pg18 RETURNING
            // WITH) sum to ZERO. Seed three cells, then apply the transfer and SUM
            // the reported balance deltas. (Seed first so the deltas below are the
            // transfer's, not the funding's.)
            for (id, bal) in [("c0", 1_000_000_i64), ("a1", 0), ("b0", 0)] {
                let full = format!("{id}00000000000000000000000000000000000000000000000000000000000000");
                Spi::run(&format!(
                    "SELECT dregg.merge_cell('\\x{full}'::bytea,'Hosted',{bal},0,'\\x'::bytea,\
                     '{{\"balance\":{bal},\"nonce\":0}}'::jsonb,'Active',0,'\\x{full}'::bytea)"
                ))
                .unwrap();
            }
            // The transfer: TREASURY 1_000_000→999_500 (−500), ALICE 0→400 (+400),
            // BOB 0→100 (+100). Σδ = 0.
            let transfer = [
                ("c0", 999_500_i64, 1u64),
                ("a1", 400, 1),
                ("b0", 100, 1),
            ];
            let mut sum: i64 = 0;
            for (id, bal, nonce) in transfer {
                let full = format!("{id}00000000000000000000000000000000000000000000000000000000000000");
                let d: i64 = Spi::get_one(&format!(
                    "SELECT balance_delta FROM dregg.merge_cell_delta('\\x{full}'::bytea,'Hosted',{bal},{nonce},\
                     '\\x'::bytea,'{{\"balance\":{bal},\"nonce\":{nonce}}}'::jsonb,'Active',0,'\\x{full}'::bytea)"
                ))
                .unwrap()
                .unwrap();
                sum += d;
            }
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(sum, 0, "conservation: the per-cell balance deltas the applicator reported sum to zero");
        }

        /// pg18 `uuidv7()` key as an AUDIT SIGNAL (docs/PG-DREGG-PG18.md §6, wired):
        /// `dregg.submit_queue_audit` recovers the enqueue time + version FROM the
        /// key itself (uuid_extract_timestamp / uuid_extract_version). We assert the
        /// recovered version is 7, the key-derived enqueued_at agrees with the
        /// submitted_at clock (so the key really is time-ordered), and rows come out
        /// in key (arrival) order.
        #[pg_test]
        fn pg18_submit_queue_audit_recovers_time_from_the_uuidv7_key() {
            let root = root();
            assert_issuer(&root);
            Spi::get_one::<String>("SELECT dregg_install_schema()").unwrap();
            let o: String = Spi::get_one("SELECT dregg_install_write_outbox()").unwrap().unwrap();
            assert!(o.contains("write outbox installed"));

            // Enqueue two rows as the table owner (the harness superuser) so the
            // audit view has data — the queue's INSERT grant is to dregg_reader (the
            // submitter), NOT dregg_kernel (which drains): a real find baked into the
            // role model, so we do NOT SET ROLE kernel to write here.
            let a_hex = "a100000000000000000000000000000000000000000000000000000000000000";
            Spi::run(&format!(
                "INSERT INTO dregg.submit_queue(agent, signed_turn) VALUES \
                 ('\\x{a_hex}'::bytea, '\\x01'::bytea), ('\\x{a_hex}'::bytea, '\\x02'::bytea)"
            ))
            .unwrap();
            Spi::run("SET ROLE dregg_kernel").unwrap(); // BYPASSRLS so we see all rows

            // Every row's key is a v7 and its key-derived enqueued_at is within a
            // few seconds of submitted_at (the key carries the time).
            let bad: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.submit_queue_audit \
                 WHERE id_version <> 7 \
                    OR abs(extract(epoch FROM (enqueued_at - submitted_at))) > 5",
            )
            .unwrap()
            .unwrap();
            assert_eq!(bad, 0, "every queue key is a v7 whose embedded time matches submitted_at");

            // The audit view yields rows in key (arrival) order: the first row's
            // enqueued_at is <= the last row's.
            let ordered: bool = Spi::get_one(
                "SELECT (SELECT enqueued_at FROM dregg.submit_queue_audit ORDER BY id LIMIT 1) \
                      <= (SELECT enqueued_at FROM dregg.submit_queue_audit ORDER BY id DESC LIMIT 1)",
            )
            .unwrap()
            .unwrap();
            assert!(ordered, "uuidv7 keys order the audit view by enqueue time");
            Spi::run("RESET ROLE").unwrap();
        }

        /// The OAuth → role → dregg-cap bind seam (docs/PG-DREGG-PG18.md §6, wired):
        /// `dregg_bind_role` is the tested code path that turns a pg role (e.g. one
        /// an OAuth `pg_hba` method authenticated) into a dregg capability. We bind
        /// `dregg_reader` to an ALICE-only token via the extern, confirm the
        /// `role_bindings` introspection view shows the binding WITHOUT leaking the
        /// token, then apply the login hook's effect and confirm RLS narrows — the
        /// whole chain as one tested path. (OAuth itself is pg_hba config, honestly
        /// out of extension SQL; this is the composition point it lands on.)
        #[pg_test]
        fn oauth_bind_role_seam_binds_then_rls_narrows() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            let o: String = Spi::get_one("SELECT dregg_install_login_binding()").unwrap().unwrap();
            assert!(o.contains("login binding installed"));

            let alice_tok = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "a1".into() }),
                ])
                .encode();
            let alice_hex: String = synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();

            // Bind the role through the EXTERN (the OAuth composition seam): the same
            // call an IdP-provisioning step or a DBA migration makes.
            let bound: bool = Spi::get_one(&format!(
                "SELECT dregg_bind_role('dregg_reader', '\\x{alice_hex}'::bytea, '{alice_tok}')"
            ))
            .unwrap()
            .unwrap();
            assert!(bound, "dregg_bind_role upserts the role→cap binding");

            // The introspection view shows the binding but NOT the token text.
            Spi::run("SET ROLE dregg_kernel").unwrap();
            let (agent, has_token): (String, bool) = {
                let a: String = Spi::get_one(
                    "SELECT agent FROM dregg.role_bindings WHERE pg_role = 'dregg_reader'",
                )
                .unwrap()
                .unwrap();
                let h: bool = Spi::get_one(
                    "SELECT has_token FROM dregg.role_bindings WHERE pg_role = 'dregg_reader'",
                )
                .unwrap()
                .unwrap();
                (a, h)
            };
            assert_eq!(agent, alice_hex, "role_bindings shows the bound agent");
            assert!(has_token, "role_bindings reports a token is present");
            // The view's columns do NOT include the raw token (no default_token col).
            let leaks_token: i64 = Spi::get_one(
                "SELECT count(*) FROM information_schema.columns \
                 WHERE table_schema='dregg' AND table_name='role_bindings' \
                   AND column_name='default_token'",
            )
            .unwrap()
            .unwrap();
            assert_eq!(leaks_token, 0, "the introspection view must not expose the token text");
            Spi::run("RESET ROLE").unwrap();

            // Apply the login hook's effect (set the session token from the bound
            // row, exactly as dregg.on_login does on a real connection) and confirm
            // RLS narrows the reader to ALICE's cell.
            let installed: Option<String> = Spi::get_one(
                "SELECT default_token FROM dregg.role_identity WHERE pg_role = 'dregg_reader'",
            )
            .unwrap();
            Spi::run(&format!("SET dregg.token = '{}'", installed.unwrap())).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let visible: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(visible, 1, "the OAuth-bound role's capability narrows RLS to ALICE's cell");
        }

        /// pg18 AIO observability (docs/PG-DREGG-PG18.md §8, wired): the
        /// `dregg.mirror_io_stats` view over `pg_stat_io` resolves and reports the
        /// read/cache mix for the read-heavy mirror. We scan the mirror (driving
        /// real relation I/O), then assert the view has rows for the `normal`
        /// relation context and the cache_hit_ratio is a sane fraction in [0,1].
        #[pg_test]
        fn pg18_mirror_io_stats_view_reports_the_io_mix() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            Spi::run("SET ROLE dregg_kernel").unwrap();
            // Drive some relation reads against the mirror so pg_stat_io has counts.
            let _scan: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();

            // The view resolves and has at least one relation/normal row.
            let rows: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.mirror_io_stats WHERE context = 'normal'",
            )
            .unwrap()
            .unwrap();
            assert!(rows >= 1, "mirror_io_stats reports the normal relation I/O context");

            // Where a cache_hit_ratio is reported it is a valid fraction in [0,1].
            let bad_ratio: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.mirror_io_stats \
                 WHERE cache_hit_ratio IS NOT NULL \
                   AND (cache_hit_ratio < 0 OR cache_hit_ratio > 1)",
            )
            .unwrap()
            .unwrap();
            assert_eq!(bad_ratio, 0, "cache_hit_ratio is a fraction in [0,1]");
            Spi::run("RESET ROLE").unwrap();
        }

        /// pg18 DATA CHECKSUMS by default (docs/PG-DREGG-PG18.md §11, wired): the
        /// integrity FLOOR under the dregg root thesis is page-level checksums, and
        /// pg18's `initdb` enables them by default. The `dregg.integrity_status`
        /// view makes that legible in-db; we assert the cluster the mirror runs on
        /// actually has checksums on (the cargo-pgrx pg18 cluster was initdb'd under
        /// the pg18 default), and that `data_checksums` reads back `'on'`.
        #[pg_test]
        fn pg18_data_checksums_are_on_and_integrity_status_reports_it() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            // The read-only GUC pg sets from the control file: 'on' under the pg18
            // initdb default (a fresh pg18 cluster is checksummed unless
            // --no-data-checksums was passed; cargo-pgrx uses the default).
            let dc: Option<String> =
                Spi::get_one("SELECT current_setting('data_checksums')").unwrap();
            assert_eq!(
                dc.as_deref(),
                Some("on"),
                "pg18 enables data checksums by default — the mirror's integrity floor"
            );

            // The introspection view reports the same, with the boolean + block size.
            let (enabled, dc_view): (bool, String) = Spi::get_two(
                "SELECT checksums_enabled, data_checksums FROM dregg.integrity_status",
            )
            .map(|(a, b)| (a.unwrap_or(false), b.unwrap_or_default()))
            .unwrap();
            assert!(enabled, "dregg.integrity_status reports checksums_enabled = true");
            assert_eq!(dc_view, "on", "the view's data_checksums matches the GUC");
        }

        /// pg18 AIO IN-FLIGHT view (docs/PG-DREGG-PG18.md §8, wired): pg18 ships
        /// `pg_aios` (the live async-I/O handles), the companion to the cumulative
        /// `pg_stat_io`. `dregg.mirror_aio_inflight` surfaces it. The in-flight set
        /// is transient (usually empty at rest), so we assert the view RESOLVES and
        /// is countable — that the pg18 view exists and the mirror surfaces it —
        /// rather than pinning a non-deterministic depth.
        #[pg_test]
        fn pg18_mirror_aio_inflight_view_resolves_over_pg_aios() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            // pg_aios (via pg_get_aios()) is a PRIVILEGED stats surface — it needs
            // superuser / pg_read_all_stats, exactly like the underlying function.
            // The operator reads it as such; the pgrx test session is the bootstrap
            // superuser, so we do NOT drop to dregg_kernel here. Drive a scan first
            // so AIO has had work, then the view resolves (>= 0 rows on pg18).
            let _scan: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();
            let inflight: i64 =
                Spi::get_one("SELECT count(*) FROM dregg.mirror_aio_inflight").unwrap().unwrap();
            assert!(inflight >= 0, "dregg.mirror_aio_inflight resolves over pg18 pg_aios");
        }

        /// pg18 logical-replication CONFLICT observability (docs/PG-DREGG-PG18.md
        /// §10, wired): pg18 newly counts apply conflicts per-subscription in
        /// `pg_stat_subscription_stats` (the `confl_*` columns).
        /// `dregg.replication_conflicts` surfaces them with a `conflicts_total`
        /// alarm. On this single node there are no subscriptions, so the view is
        /// EMPTY — but it must RESOLVE (the pg18 columns exist and the view binds
        /// them), which is the property a publisher/subscriber both rely on. We
        /// assert it resolves and exposes the conflicts_total alarm column.
        #[pg_test]
        fn pg18_replication_conflicts_view_resolves_with_the_total_alarm() {
            let root = root();
            assert_issuer(&root);
            install_tier_c_and_submit_story();
            let _fed: String = Spi::get_one("SELECT dregg_install_federation()").unwrap().unwrap();

            // No subscriptions here ⇒ zero rows, but the view RESOLVES (the pg18
            // confl_* columns exist and conflicts_total computes over them).
            let rows: i64 =
                Spi::get_one("SELECT count(*) FROM dregg.replication_conflicts").unwrap().unwrap();
            assert_eq!(rows, 0, "no subscriptions on this node ⇒ empty (but resolvable) view");
            // The alarm column is bound (selecting it does not error on a fresh
            // pg18). `sum` over zero rows is numeric ⇒ cast to bigint to read it.
            let total: Option<i64> = Spi::get_one(
                "SELECT coalesce(sum(conflicts_total), 0)::bigint FROM dregg.replication_conflicts",
            )
            .unwrap();
            assert_eq!(total, Some(0), "conflicts_total sums the seven pg18 confl_* counters");
        }

        /// §15 federation health — the pg18 conflict counters DRIVE re-validation,
        /// composing the apply-divergence alarm with the chain tooth (the wiring
        /// this lane adds). Three SQL-level assertions, all against the live store:
        ///
        ///   1. CLEAN: on a node with no apply conflict, `dregg_federation_health()`
        ///      reads the REAL `dregg.replication_conflicts` view and returns the
        ///      healthy verdict — and does NOT need the chain tooth.
        ///   2. CONFLICT ⇒ TRIGGER ⇒ chain intact: when a conflict counter is
        ///      non-zero, the alarm fires AND the re-validation triggers over the real
        ///      `dregg.turns`; with a faithful chain the verdict is the "ALARM but
        ///      chain re-validates" composition.
        ///   3. CONFLICT ⇒ TRIGGER ⇒ chain broken: with the same conflict AND a
        ///      tampered turn, the triggered tooth REFUSES ⇒ the CRITICAL do-not-trust
        ///      verdict — proving the conflict alarm really pulls the chain check, not
        ///      just reports a number.
        ///
        /// The genuine pg18 `confl_*` counter read is proven by the resolves-test
        /// above + the live multi-DB harness (`sql/federation-conflict-live.sql`,
        /// which stands up a real subscription + a real apply conflict). Here we drive
        /// the COMPOSITION through real SQL by pointing the health read at a fixture
        /// view of the SAME shape (`subname` + the seven `confl_*` + `conflicts_total`)
        /// carrying a non-zero count — so the extern's read → alarm → trigger → tooth
        /// path is exercised end-to-end on the live engine, deterministically.
        #[pg_test]
        fn federation_health_conflict_alarm_triggers_the_chain_tooth() {
            let root = root();
            assert_issuer(&root);
            // A real, gate-built 4-turn hash chain in dregg.turns (what replication
            // would carry), plus the real federation publication + conflicts view.
            install_tier_c_and_submit_story();
            let _fed: String = Spi::get_one("SELECT dregg_install_federation()").unwrap().unwrap();
            Spi::run("SET ROLE dregg_kernel").unwrap();

            // (1) CLEAN: the real dregg.replication_conflicts view is empty on this
            // single node ⇒ healthy, and the chain tooth is NOT the load-bearing part.
            let healthy: String =
                Spi::get_one("SELECT dregg_federation_health()").unwrap().unwrap();
            assert!(
                healthy.starts_with("ok: federation healthy") && healthy.contains("0 apply conflicts"),
                "a node with no apply conflict is healthy: {healthy}"
            );

            // Now drive the COMPOSITION. The health extern reads dregg.replication_conflicts;
            // replace it (same column shape) with a fixture carrying a NON-ZERO conflict
            // so the alarm fires deterministically — the genuine pg18 confl_* read is
            // covered separately (the resolves-test + the live multi-DB harness).
            Spi::run("RESET ROLE").unwrap();
            // DROP+CREATE (a REPLACE cannot change a column type, and the real view's
            // `subname` is type `name` from pg_subscription); the fixture matches the
            // column types (`subname name`, the seven counters + total `bigint`).
            Spi::run("DROP VIEW dregg.replication_conflicts").unwrap();
            Spi::run(
                "CREATE VIEW dregg.replication_conflicts AS \
                 SELECT 'dregg_tail'::name AS subname, \
                        1::bigint AS confl_insert_exists, \
                        0::bigint AS confl_update_origin_differs, \
                        0::bigint AS confl_update_exists, \
                        2::bigint AS confl_update_missing, \
                        0::bigint AS confl_delete_origin_differs, \
                        0::bigint AS confl_delete_missing, \
                        0::bigint AS confl_multiple_unique_conflicts, \
                        3::bigint AS conflicts_total, \
                        now() AS stats_reset",
            )
            .expect("fixture conflicts view (same shape) installs");
            Spi::run("GRANT SELECT ON dregg.replication_conflicts TO dregg_kernel").unwrap();
            Spi::run("SET ROLE dregg_kernel").unwrap();

            // (2) CONFLICT ⇒ TRIGGER ⇒ chain intact. The alarm fires (conflicts_total=3)
            // AND the re-validation triggers over the real, faithful dregg.turns ⇒ the
            // "ALARM but chain re-validates" composition.
            let alarmed: String =
                Spi::get_one("SELECT dregg_federation_health()").unwrap().unwrap();
            assert!(
                alarmed.starts_with("ALARM (3 apply conflict(s))") && alarmed.contains("chain re-validates"),
                "a non-zero conflict fires the alarm AND triggers re-validation (chain intact): {alarmed}"
            );

            // (3) CONFLICT ⇒ TRIGGER ⇒ chain broken. Tamper ord-2's prev_root so the
            // triggered tooth REFUSES ⇒ the CRITICAL do-not-trust verdict. This is the
            // proof the alarm PULLS the chain check: same conflict, but now the chain is
            // broken and the composed verdict escalates.
            Spi::run("RESET ROLE").unwrap();
            Spi::run(
                "UPDATE dregg.turns SET prev_root = '\\x9999999999999999999999999999999999999999999999999999999999999999' \
                 WHERE ordinal = 2",
            )
            .unwrap();
            Spi::run("SET ROLE dregg_kernel").unwrap();
            let critical: String =
                Spi::get_one("SELECT dregg_federation_health()").unwrap().unwrap();
            assert!(
                critical.starts_with("CRITICAL (3 apply conflict(s))") && critical.contains("chain REFUSED"),
                "a conflict AND a tampered chain ⇒ the CRITICAL do-not-trust verdict: {critical}"
            );
            Spi::run("RESET ROLE").unwrap();
        }

        /// pg18 COPY ON_ERROR bulk-load of the OAuth→role bind map
        /// (docs/PG-DREGG-PG18.md §12, wired): a bulk onboarding CSV with a
        /// MALFORMED row must SKIP the bad line (pg18 `ON_ERROR ignore`) and land
        /// the good ones, then promote them through the audited `dregg.bind_role`
        /// seam — the bulk path never writes role_identity unchecked. We COPY FROM
        /// PROGRAM (the pgrx test runs as superuser) one good + one type-bad row
        /// into the staging table, assert ON_ERROR skipped the bad one, then promote
        /// and assert the good binding reached role_identity via the seam.
        #[pg_test]
        fn pg18_copy_on_error_bulk_loads_bind_map_skipping_bad_rows() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            // The login-binding DDL ships role_identity_load + promote_role_identity_load.
            let lb: String =
                Spi::get_one("SELECT dregg_install_login_binding()").unwrap().unwrap();
            assert!(lb.contains("login binding installed"));
            // COPY FROM PROGRAM needs pg_execute_server_program (a privileged
            // bootstrap/DBA action — exactly who runs a bulk onboarding load), so we
            // stay the pgrx superuser session rather than dropping to dregg_kernel.

            // The `agent` column of role_identity_load is TEXT, so a non-integer is
            // fine there; to exercise ON_ERROR we COPY into a 2-int scratch table
            // where a non-int row is a genuine parse error pg18 ON_ERROR ignores.
            Spi::run("CREATE TEMP TABLE on_err_probe (a int, b int)").unwrap();
            // Three rows: two well-typed, one (the middle) with a non-int in `a`.
            // pg18 ON_ERROR ignore lands the 2 good rows and skips the bad one;
            // pre-18 the whole COPY would abort.
            Spi::run(
                "COPY on_err_probe (a, b) FROM PROGRAM \
                 'printf ''1,10\\nNOTANINT,20\\n3,30\\n'' ' \
                 WITH (FORMAT csv, ON_ERROR ignore, LOG_VERBOSITY silent)",
            )
            .expect("pg18 COPY ON_ERROR ignore must parse + run");
            let good: i64 = Spi::get_one("SELECT count(*) FROM on_err_probe").unwrap().unwrap();
            assert_eq!(good, 2, "pg18 ON_ERROR ignore landed the 2 good rows, skipped the bad one");

            // Now the REAL bind-map path: stage two role rows (one with a bad hex
            // agent), promote, and assert only the valid one reached the seam.
            let alice = "a111111111111111111111111111111111111111111111111111111111111111";
            Spi::run(&format!(
                "INSERT INTO dregg.role_identity_load (pg_role, agent_hex, token) VALUES \
                 ('alice_role', '{alice}', NULL), \
                 ('bad_role', 'ZZNOTHEX', NULL)",
            ))
            .unwrap();
            let (promoted, skipped): (i64, i64) = Spi::get_two(
                "SELECT promoted, skipped FROM dregg.promote_role_identity_load()",
            )
            .map(|(p, s)| (p.unwrap_or(-1), s.unwrap_or(-1)))
            .unwrap();
            assert_eq!(promoted, 1, "the valid staged binding is promoted through bind_role");
            assert_eq!(skipped, 1, "the bad-hex staged row is skipped, never written unchecked");
            // The promoted binding is now in role_identity (via the audited seam).
            let bound: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.role_identity WHERE pg_role = 'alice_role'",
            )
            .unwrap()
            .unwrap();
            assert_eq!(bound, 1, "the bulk-loaded role reached role_identity via dregg.bind_role");
            // The bad row never created a binding.
            let unbound: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.role_identity WHERE pg_role = 'bad_role'",
            )
            .unwrap()
            .unwrap();
            assert_eq!(unbound, 0, "the malformed staged row created no binding");
        }

        // ===================================================================
        // The §15 FEDERATION re-validation through real SQL: the publication
        // installs, and the subscriber-side sweep (dregg_revalidate_replicated_chain)
        // re-validates the store's turns chain and REFUSES a tampered one — a
        // subscriber re-validates, it does not trust the stream.
        // ===================================================================

        #[pg_test]
        fn federation_publishes_and_revalidates_the_replicated_chain() {
            let root = root();
            assert_issuer(&root);
            // Land the well-formed story through the Tier-C gate (so dregg.turns is
            // a real, gate-built hash chain — exactly what would be replicated).
            install_tier_c_and_submit_story();

            // The publisher installs the publication over the state tables.
            let fed: String = Spi::get_one("SELECT dregg_install_federation()").unwrap().unwrap();
            assert!(fed.contains("federation publication installed"));
            let pubs: i64 = Spi::get_one(
                "SELECT count(*) FROM pg_publication WHERE pubname = 'dregg_mirror'",
            )
            .unwrap()
            .unwrap();
            assert_eq!(pubs, 1, "CREATE PUBLICATION dregg_mirror landed");

            // The subscriber-side sweep re-validates the (here, local) turns chain:
            // it walks dregg.turns through the SAME anti-substitution tooth and
            // reports ok with the head — a subscriber re-validates locally.
            Spi::run("SET ROLE dregg_kernel").unwrap();
            let verdict: String =
                Spi::get_one("SELECT dregg_revalidate_replicated_chain()").unwrap().unwrap();
            assert!(
                verdict.starts_with("ok:") && verdict.contains("4 turns"),
                "the faithfully-replicated chain re-validates: {verdict}"
            );

            // Now simulate a tampered replication stream: substitute ord-2's
            // prev_root so it no longer chains. The sweep REFUSES it locally — the
            // tooth survives replication, caught on the subscriber side.
            Spi::run(
                "UPDATE dregg.turns SET prev_root = '\\x9999999999999999999999999999999999999999999999999999999999999999' \
                 WHERE ordinal = 2",
            )
            .unwrap();
            let refused: String =
                Spi::get_one("SELECT dregg_revalidate_replicated_chain()").unwrap().unwrap();
            assert!(
                refused.starts_with("REFUSED:"),
                "a tampered replicated chain must be refused by the subscriber sweep: {refused}"
            );
            Spi::run("RESET ROLE").unwrap();

            // The subscriber runbook substitutes the publisher conninfo + names the
            // re-validation sweep (it is an operational procedure, returned as text).
            let runbook: String = Spi::get_one(
                "SELECT dregg_federation_subscriber_runbook('host=pub dbname=dregg')",
            )
            .unwrap()
            .unwrap();
            assert!(runbook.contains("pg_createsubscriber"));
            assert!(runbook.contains("host=pub dbname=dregg"));
            assert!(runbook.contains("dregg_revalidate_replicated_chain"));
        }

        // ===================================================================
        // The §10.2.1 Tier-C RANGE-ATTEST SRF through real SQL: with the
        // circuit-link UNWIRED (the default, circuit-free build), the proof gate
        // FAILS CLOSED — it attests NOTHING (zero rows) and the explain names the
        // settle item. This is the §10.3 safe direction: a labeled proof gate that
        // does not verify must say "unattested", never "attested".
        // ===================================================================

        #[pg_test]
        fn tier_c_range_attest_srf_fails_closed_until_wired() {
            let root = root();
            assert_issuer(&root);
            install_tier_c_and_submit_story(); // dregg.turns has 4 turns

            let vk = "0000000000000000000000000000000000000000000000000000000000000000";
            // A non-empty (but unverifiable, since the link is stubbed) proof + a
            // claimed window [0,3]. The SRF must return ZERO rows (fail-closed).
            let attested: i64 = Spi::get_one(&format!(
                "SELECT count(*) FROM dregg_attest_range('\\xdeadbeef'::bytea, '\\x{vk}'::bytea, 0, 3)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(attested, 0, "the unwired proof gate attests NOTHING (fail-closed)");

            // The explain names the circuit-link settle item (not a silent deny).
            let why: String = Spi::get_one(&format!(
                "SELECT dregg_attest_explain('\\xdeadbeef'::bytea, '\\x{vk}'::bytea, 0, 3)"
            ))
            .unwrap()
            .unwrap();
            assert!(
                why.contains("not yet wired") || why.contains("settle item"),
                "the refusal names the circuit-link settle item: {why}"
            );

            // A bad VK anchor (wrong length) is refused, not panicked.
            let bad_vk: String = Spi::get_one(
                "SELECT dregg_attest_explain('\\xde'::bytea, '\\x00'::bytea, 0, 1)",
            )
            .unwrap()
            .unwrap();
            assert!(bad_vk.contains("32 bytes"), "a malformed VK anchor fails closed: {bad_vk}");

            // An inverted/empty window is refused too (zero rows).
            let inverted: i64 = Spi::get_one(&format!(
                "SELECT count(*) FROM dregg_attest_range('\\xde'::bytea, '\\x{vk}'::bytea, 5, 4)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(inverted, 0, "an inverted window attests nothing");
        }

        // ===================================================================
        // dregg_dev_mint + dregg_issuer_status (FRONTIER-ROADMAP N19)
        // ===================================================================

        /// The DEV mint composes the common shape and produces a token that
        /// `dregg_cap_admits` / `dregg_cap_explain` accept — through real SQL, with
        /// the `ttl interval` resolved by postgres's own clock. The privkey GUC is
        /// configured by the harness (the dev posture; production mints
        /// out-of-database).
        #[pg_test]
        fn dev_mint_produces_a_token_the_admit_path_accepts() {
            // Mint via SQL: read+write under "org/42/", subject alice, ttl 1 hour.
            let tok: String = Spi::get_one(
                "SELECT dregg_dev_mint('alice', ARRAY['read','write'], 'org/42/', interval '1 hour')",
            )
            .unwrap()
            .expect("dregg_dev_mint returns a token when the mint key is configured");
            assert!(tok.starts_with("dga1"), "a dga1_… credential string: {tok}");

            // It verifies under the SAME issuer the harness configured, and is
            // admitted for both actions under the prefix, at the current clock.
            let admits = |action: &str, resource: &str| -> bool {
                Spi::get_one_with_args(
                    "SELECT dregg_cap_admits($1, $2, $3, extract(epoch from now())::bigint)",
                    &[tok.as_str().into(), action.into(), resource.into()],
                )
                .unwrap()
                .unwrap()
            };
            assert!(admits("read", "org/42/public/doc1"), "read admitted under prefix");
            assert!(admits("write", "org/42/public/doc1"), "write admitted under prefix");
            // An action not in the set, and a resource outside the prefix: denied.
            assert!(!admits("delete", "org/42/public/doc1"), "delete is not in the action set");
            assert!(!admits("read", "org/99/other/doc1"), "outside the resource prefix");

            // The subject is embedded + recovered; explain says allowed.
            let subj: Option<String> = Spi::get_one_with_args(
                "SELECT dregg_cap_subject($1)",
                &[tok.as_str().into()],
            )
            .unwrap();
            assert_eq!(subj.as_deref(), Some("alice"));
            let why: String = Spi::get_one_with_args(
                "SELECT dregg_cap_explain($1, 'read', 'org/42/public/doc1', extract(epoch from now())::bigint)",
                &[tok.as_str().into()],
            )
            .unwrap()
            .unwrap();
            assert_eq!(why, "allowed", "dregg_cap_explain confirms the dev-minted token: {why}");

            // A single-action dev-mint uses a bare AttrEq and still admits.
            let one: String = Spi::get_one(
                "SELECT dregg_dev_mint('bob', ARRAY['read'], '', interval '1 hour')",
            )
            .unwrap()
            .unwrap();
            let one_admits: bool = Spi::get_one_with_args(
                "SELECT dregg_cap_admits($1, 'read', 'anything', extract(epoch from now())::bigint)",
                &[one.as_str().into()],
            )
            .unwrap()
            .unwrap();
            assert!(one_admits, "empty prefix admits any resource for the listed action");
        }

        /// The dev-minted token narrows row visibility through a real RLS-gated
        /// table — the same no-amplify thesis as `rls_gated_table_narrows_row_
        /// visibility`, but with the token minted IN-SQL via `dregg_dev_mint` (the
        /// on-ramp's first friction removed) then attenuated.
        #[pg_test]
        fn dev_mint_token_narrows_rows_through_rls() {
            Spi::run(
                "CREATE TABLE dm_docs (id text primary key);
                 INSERT INTO dm_docs VALUES
                   ('org/42/public/doc1'),
                   ('org/42/public/doc2'),
                   ('org/42/private/doc9'),
                   ('org/99/public/doc1');
                 ALTER TABLE dm_docs ENABLE ROW LEVEL SECURITY;
                 ALTER TABLE dm_docs FORCE ROW LEVEL SECURITY;
                 CREATE POLICY cap_read ON dm_docs FOR SELECT
                   USING (dregg_admits('read', id::text));
                 CREATE ROLE dm_reader NOLOGIN;
                 GRANT SELECT ON dm_docs TO dm_reader;",
            )
            .unwrap();

            // Dev-mint a read token under org/42/ (1h ttl so now() does not expire it).
            let root_tok: String = Spi::get_one(
                "SELECT dregg_dev_mint('alice', ARRAY['read'], 'org/42/', interval '1 hour')",
            )
            .unwrap()
            .unwrap();
            // Attenuate it (the holder's right) to org/42/public/ only.
            let narrowed: String = Spi::get_one_with_args(
                "SELECT dregg_attenuate($1, '[{\"AttrPrefix\":{\"key\":\"resource\",\"prefix\":\"org/42/public/\"}}]'::jsonb)",
                &[root_tok.as_str().into()],
            )
            .unwrap()
            .unwrap();

            let count_under = |tok: &str| -> i64 {
                Spi::run(&format!("SET dregg.token = '{tok}'")).unwrap();
                Spi::run("SET ROLE dm_reader").unwrap();
                let n = Spi::get_one::<i64>("SELECT count(*) FROM dm_docs").unwrap().unwrap();
                Spi::run("RESET ROLE").unwrap();
                n
            };
            // Root dev-minted token: the three org/42 rows (not org/99).
            assert_eq!(count_under(&root_tok), 3, "dev-minted org/42 token sees 3 rows");
            // Narrowed: only the two public rows — a strict subset.
            assert_eq!(count_under(&narrowed), 2, "attenuated token sees only org/42/public");
        }

        /// **The issuer-key discipline is intact.** With NO mint key configured,
        /// `dregg_dev_mint` RAISES — it does NOT silently mint a token. We clear
        /// the privkey GUC for this connection (SET on a `Suset` GUC is allowed in
        /// the test's superuser session) and assert the dev mint errors.
        #[pg_test]
        fn dev_mint_without_a_key_raises_not_silently_mints() {
            // Clear the mint key for this session, then attempt to dev-mint.
            Spi::run("SET dregg.issuer_privkey = ''").unwrap();
            let result = std::panic::catch_unwind(|| {
                Spi::get_one::<String>(
                    "SELECT dregg_dev_mint('alice', ARRAY['read'], 'org/42/', interval '1 hour')",
                )
            });
            assert!(
                result.is_err(),
                "dregg_dev_mint MUST raise (not return a token) when no mint key is configured"
            );
            // Restore the GUC for any subsequent statements in this backend.
            Spi::run(&format!(
                "SET dregg.issuer_privkey = '{}'",
                "0707070707070707070707070707070707070707070707070707070707070707"
            ))
            .unwrap();
        }

        /// `dregg_issuer_status` reports the configured verify key id and that dev
        /// minting is enabled+matching (the harness configures both keys from the
        /// same seed). The LOUD verify-key-ABSENT path ("everything denies") is
        /// proven in the postgres-free core test
        /// (`authz::tests::issuer_status_reports_the_loud_no_key_mode`) — it cannot
        /// be exercised in-session here because `dregg.issuer_pubkey` is a `Sighup`
        /// GUC that a session is (correctly) forbidden to `SET` (a session must not
        /// repoint the verify key). Here we confirm the SQL surface reports the
        /// live verify-key state AND that toggling the SUPERUSER-settable mint key
        /// (`Suset`) flips the dev-minting line — both observable through real SQL.
        #[pg_test]
        fn issuer_status_reports_the_configured_keys() {
            let status: String = Spi::get_one("SELECT dregg_issuer_status()").unwrap().unwrap();
            // The verify key is configured (the harness sets it) → reports its id.
            assert!(status.contains("CONFIGURED"), "verify key reported configured: {status}");
            assert!(
                status.contains("ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c"),
                "the verify key id is named: {status}"
            );
            // Dev minting is enabled (privkey configured) and MATCHES the verify key.
            assert!(status.contains("ENABLED"), "dev minting reported enabled: {status}");
            assert!(status.contains("MATCHES"), "matching keys flagged: {status}");

            // The mint key IS session-settable (`Suset`, superuser): clear it and
            // the status flips to "DISABLED" (the production posture — verify in
            // pg, no private key present). This is the discoverable dev-minting
            // state on the SQL surface.
            Spi::run("SET dregg.issuer_privkey = ''").unwrap();
            let no_mint: String = Spi::get_one("SELECT dregg_issuer_status()").unwrap().unwrap();
            assert!(
                no_mint.contains("DISABLED"),
                "with no mint key, dev minting reads disabled: {no_mint}"
            );
            // The verify key is still configured, so admits still work — the loud
            // "EVERYTHING DENIES" only fires when the VERIFY key is absent.
            assert!(no_mint.contains("CONFIGURED"), "verify key still set: {no_mint}");
            // Restore the mint key for subsequent statements in this backend.
            Spi::run(
                "SET dregg.issuer_privkey = '0707070707070707070707070707070707070707070707070707070707070707'",
            )
            .unwrap();
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
    ///
    /// The PRIVATE key (seed `[7u8;32]` = `07`×32 hex) is ALSO configured here so
    /// the dev-mint pg_tests (`dregg_dev_mint`) can exercise the full mint path
    /// against the managed server. In PRODUCTION the private key is NOT placed in
    /// postgres (mint out-of-database) — this is the dev posture the dev-mint
    /// on-ramp is explicitly scoped to. The no-key-fails-loudly behavior is
    /// proven in the postgres-free core test
    /// (`authz::tests::dev_mint_fails_loudly_without_a_mint_key`) and reasserted
    /// here by clearing the GUC within a test.
    pub fn postgresql_conf_options() -> Vec<&'static str> {
        vec![
            "dregg.issuer_pubkey = 'ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c'",
            "dregg.issuer_privkey = '0707070707070707070707070707070707070707070707070707070707070707'",
        ]
    }
}
