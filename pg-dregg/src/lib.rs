//! # pg-dregg — dregg verified object-capability authorization for PostgreSQL RLS
//!
//! **SKELETON.** This file sketches the SQL surface and the `dregg-auth`
//! marshalling described in `docs/PG-DREGG.md`. The function *signatures* and
//! the *body sketches* are real; the file is NOT expected to compile against a
//! live postgres without a `cargo pgrx init` toolchain, and `cargo pgrx` is NOT
//! run from the proposal lane.
//!
//! The thesis: an ordinary postgres-heavy app gates rows with dregg
//! capabilities instead of hand-rolled SQL RLS predicates. The SAME `dga1_…`
//! token authorizes against the dregg kernel and against your plain tables.
//!
//! All authorization logic lives in `dregg_auth::credential` (the proven core,
//! semantics machine-checked in `metatheory/Dregg2/Authority/`). This crate is
//! a thin marshalling shell: text/bigint across the SQL boundary into
//! `Credential::verify`. The integration plumbing is conventional extension
//! code; the *capability decision* is the verified dregg decision (see
//! `docs/PG-DREGG.md` §4 for the precise assurance boundary).

// use pgrx::prelude::*;
// use std::cell::OnceCell;
// use dregg_auth::credential::{Context, Credential, PublicKey};

// pgrx::pg_module_magic!();

// =============================================================================
// Issuer public key — the database's trust root (docs/PG-DREGG.md §3.3)
// =============================================================================

/// The issuer public key, read once from the `dregg.issuer_pubkey` GUC and
/// cached process-local. A malformed or absent key makes every decision DENY
/// (fail-closed). The key is *public* — safe to publish — so the GUC is
/// DBA-visible (`GucContext::Sighup`); the PRIVATE key never lives in postgres
/// (minting happens out-of-database).
///
/// ```ignore
/// thread_local! {
///     static ISSUER_PK: OnceCell<Option<PublicKey>> = OnceCell::new();
/// }
/// fn issuer_pk() -> Option<PublicKey> {
///     ISSUER_PK.with(|c| {
///         c.get_or_init(|| {
///             let hex = pgrx::guc::GucSetting::<Option<&str>>::... // "dregg.issuer_pubkey"
///             PublicKey::from_hex(hex?).ok()
///         }).clone()
///     })
/// }
/// ```
mod issuer_key_sketch {}

// =============================================================================
// dregg_cap_admits — the core decision (docs/PG-DREGG.md §2.1, §3.1)
// =============================================================================

/// The core RLS decision. Returns `true` iff `token` admits `action` on
/// `resource` at `now`, verified OFFLINE against the configured issuer key.
/// Any verification failure (bad signature, expired, caveat refused, missing
/// discharge, no issuer key) returns `false` — fail-closed.
///
/// SQL:
/// ```sql
/// CREATE FUNCTION dregg_cap_admits(token text, action text, resource text, now bigint)
///   RETURNS boolean IMMUTABLE PARALLEL SAFE STRICT;
/// ```
///
/// Body sketch (backed by `dregg_auth::credential`):
/// ```ignore
/// #[pg_extern(immutable, parallel_safe, strict)]
/// fn dregg_cap_admits(token: &str, action: &str, resource: &str, now: i64) -> bool {
///     let Some(pk) = issuer_pk() else { return false };          // no key ⇒ deny
///     let Ok(now) = u64::try_from(now) else { return false };    // negative ⇒ deny
///     let Ok(cred) = Credential::decode(token) else { return false };
///     let ctx = Context::new()
///         .at(now)
///         .attr("action", action)
///         .attr("resource", resource);
///     cred.verify(&pk, &ctx).is_ok()                             // the verified decision
/// }
/// ```
///
/// Performance (docs/PG-DREGG.md §6): milestone-2 caches the decoded+verified
/// `Credential` per token string in a backend-local LRU so the per-row cost
/// collapses from an ed25519 chain verify to a `Pred` re-evaluation over the
/// row's resource.
fn dregg_cap_admits_sketch() {}

/// Same decision, returning the human-readable `Refusal` reason instead of a
/// bool — the explain discipline at the SQL boundary, for policy debugging and
/// audit. `"allowed"` on success; otherwise the first violated requirement.
///
/// ```sql
/// CREATE FUNCTION dregg_cap_explain(token text, action text, resource text, now bigint)
///   RETURNS text IMMUTABLE PARALLEL SAFE;
/// ```
/// ```ignore
/// match cred.verify(&pk, &ctx) {
///     Ok(())  => "allowed".into(),
///     Err(r)  => r.to_string(),   // Refusal Display names the failed requirement
/// }
/// ```
fn dregg_cap_explain_sketch() {}

/// The confined subject (agent identity) the token names, or NULL if it does
/// not verify. For `actor = dregg_cap_subject(...)` joins and audit columns.
///
/// ```sql
/// CREATE FUNCTION dregg_cap_subject(token text) RETURNS text IMMUTABLE PARALLEL SAFE;
/// ```
fn dregg_cap_subject_sketch() {}

/// Convenience wrapper so policies stay terse: reads the `dregg.token` session
/// GUC and the current clock. STABLE (reads `now()` + the GUC), not IMMUTABLE.
///
/// ```sql
/// CREATE FUNCTION dregg_admits(action text, resource text) RETURNS boolean
///   STABLE PARALLEL SAFE;
/// -- dregg_admits('read', id::text)
/// --   == dregg_cap_admits(current_setting('dregg.token', true),
/// --                       'read', id::text, extract(epoch from now())::bigint)
/// ```
fn dregg_admits_sketch() {}

// =============================================================================
// dregg_attenuate — narrowing only (docs/PG-DREGG.md §2.1, §3.1)
// =============================================================================

/// Append caveats to a presented token — NEVER widening. The SQL face of
/// `Credential::attenuate`; the proof `attenuate_subset` is the guarantee the
/// SQL boundary cannot amplify. `caveats` is a small JSON DSL mapping 1:1 onto
/// the `Pred` algebra (`{"attr_prefix":{"key":"resource","value":"org/42/"}}`,
/// `{"not_after":2000}`, `{"all_of":[…]}`, …).
///
/// ```sql
/// CREATE FUNCTION dregg_attenuate(token text, caveats jsonb) RETURNS text
///   IMMUTABLE PARALLEL SAFE;
/// ```
/// ```ignore
/// let cred = Credential::decode(token)?;
/// let preds = parse_caveats(caveats)?;   // JSON DSL ⇄ Vec<Caveat::FirstParty(Pred)>
/// cred.attenuate(preds).encode()
/// ```
fn dregg_attenuate_sketch() {}

/// Mint a credential carrying caveats, expiring at `until`. PRIVILEGED: holds
/// the issuer secret, so this is `SECURITY DEFINER` and role-gated; the secret
/// is read from a superuser-only, `NO_SHOW_ALL` GUC (better: minting happens
/// out-of-database and only verification lives in pg).
///
/// ```sql
/// CREATE FUNCTION dregg_mint(subject text, caveats jsonb, until bigint) RETURNS text
///   SECURITY DEFINER;   -- callable only by the issuing role
/// ```
fn dregg_mint_sketch() {}

// =============================================================================
// The caveat JSON DSL ⇄ dregg_auth::credential::Pred (docs/PG-DREGG.md §3.2)
// =============================================================================

/// The mint/attenuate caveat DSL is the `Pred` algebra, 1:1:
/// ```json
/// {"true": null}                                          // Pred::True
/// {"false": null}                                         // Pred::False
/// {"attr_eq":    {"key":"action","value":"read"}}         // Pred::AttrEq
/// {"attr_prefix":{"key":"resource","value":"org/42/"}}    // Pred::AttrPrefix
/// {"not_before": 1000}                                     // Pred::NotBefore
/// {"not_after":  2000}                                     // Pred::NotAfter
/// {"within":     {"not_before":1000,"not_after":2000}}     // Pred::Within
/// {"all_of":     [ … ]}                                    // Pred::AllOf
/// {"any_of":     [ … ]}                                    // Pred::AnyOf
/// {"not":        { … }}                                    // Pred::Not
/// ```
/// Nothing new is invented — the DSL is a serde view of the proven `Pred` enum.
mod caveat_dsl_sketch {}

// =============================================================================
// Milestone-1 test (docs/PG-DREGG.md §5): the no-amplify property THROUGH SQL
// =============================================================================

/// ```ignore
/// #[cfg(any(test, feature = "pg_test"))]
/// #[pgrx::pg_schema]
/// mod tests {
///     use super::*;
///
///     #[pg_test]
///     fn attenuated_token_is_narrowed_at_the_sql_boundary() {
///         // 1. Mint (in Rust): read on any "org/42/" resource, until clock 2000.
///         // 2. Attenuate to ONLY "org/42/public/".
///         // 3. Through SQL dregg_cap_admits(narrowed, ...):
///         //      ('read','org/42/public/doc1', 1000) => TRUE
///         //      ('read','org/42/private/doc9',1000) => FALSE  (narrowing held)
///         //      ('read','org/42/public/doc1', 3000) => FALSE  (past NotAfter)
///         // 4. Through a real RLS-gated `documents` table:
///         //      SET dregg.token = <narrowed>;
///         //      SELECT count(*) FROM documents;  -- only org/42/public rows
///     }
/// }
/// ```
mod milestone_1_test_sketch {}
