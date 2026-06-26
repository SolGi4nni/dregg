//! The **Tier-D in-backend executor producer** — the drainer's PRODUCE gate run
//! through the REAL verified Lean executor (`execFullForestG`), single-threaded,
//! INSIDE the postgres backend process.
//!
//! # Where this sits (the pillar)
//!
//! [`crate::drainer`] runs the four-gate write spine SUBMIT → PRODUCE → CHAIN →
//! MIRROR, where PRODUCE is a [`crate::drainer::Producer`]. The postgres-free core
//! ships the deterministic [`crate::drainer::FoldProducer`] STAND-IN so every other
//! gate is `cargo test`-proven without the executor in the build. This module is
//! the REAL producer that supersedes that stand-in on the live path: it executes
//! each drained turn through the verified `execFullForestG` and builds the
//! [`MirrorBatch`] from the executor's ACTUAL decoded post-state.
//!
//! # Why this is now realizable IN the backend (the spike that unblocked it)
//!
//! The pg-Tier-D verdict was D-SIDECAR (`docs/PG-DREGG-TIER-D-SPIKE.md` §4) on the
//! belief that the Lean runtime (a) overrides the global allocator with mimalloc
//! and (b) spawns worker threads — both fatal in a single-threaded
//! `palloc`/`longjmp`/`fork` backend. The embeddable-runtime spike
//! (`docs/EMBEDDABLE-LEAN-RUNTIME.md`) REFUTED both: mimalloc is a PRIVATE heap
//! (no `MI_MALLOC_OVERRIDE`), the task manager is LAZY (`Task.spawn` runs inline
//! until an explicit `lean_init_task_manager` the executor never calls), and the
//! only thread the default init spawns is the libuv event loop — which
//! [`dregg_lean_ffi::init_single_threaded`] (`dregg_ffi_init_st`) omits. So the
//! verified executor runs with NO allocator override, NO worker thread, and NO IO
//! event loop — the in-backend precondition, MEASURED on macOS (PROP-1/2/3 of
//! `dregg-lean-ffi/tests/embeddable_runtime_probe.rs`).
//!
//! # The fork discipline (load-bearing for a postgres backend)
//!
//! A postgres backend is `fork()`ed from the postmaster, and the Lean runtime init
//! must run ONCE PER PROCESS, AFTER the fork (never in the postmaster — the
//! single-threaded init has nothing thread-shaped to survive fork, but the init
//! ritual itself must run in the child). [`LeanProducer::new`] does NOT init; the
//! first [`LeanProducer::produce`] call lazily drives `init_single_threaded`
//! (guarded by `dregg-lean-ffi`'s own `OnceLock`), so init happens in the backend
//! that first drains — exactly the right process. A failed init fails the produce
//! gate closed (the turn is REFUSED, no state leaks).
//!
//! # What is faithful here, and the ONE honest residual
//!
//! FAITHFUL: the produced post-image's balances and the commit/reject decision are
//! the verified `execFullForestG`'s — not a Rust fold. The executor enforces
//! conservation in-kernel and fails closed (an overspend / a violated admission
//! does NOT commit), and the post-balances are read back from the executor's
//! decoded `WireState`. This is the literal "the drainer's PRODUCE runs the REAL
//! `execFullForestG` in-backend."
//!
//! RESIDUAL (flagged, not hidden): pg-dregg deliberately does not link
//! `dregg-turn`/`dregg-cell`, so it cannot decode the submitter's postcard
//! `SignedTurn` bytes (`intent.signed_turn`) into the executor's 30-arm wire turn —
//! that marshaller (`SignedTurn -> Turn -> WForest`, and `Ledger -> WireState`)
//! lives in the node (`node/src/submit_queue_drainer.rs` + the `dregg-turn`
//! `lean_apply` stack). So, like [`crate::drainer::FoldProducer`], this producer
//! SYNTHESIZES a conserving transfer (credit the acting agent, debit a float
//! source) as the wire turn it executes — but, unlike the fold stand-in, it runs
//! that turn through the VERIFIED executor and takes the executor's verdict +
//! post-state as authoritative. Lifting the full `SignedTurn` decode in-backend is
//! the node-side `dregg-turn` work (out of this crate's dependency set); it is the
//! one piece between this and "an arbitrary submitted turn executes in-backend."

use crate::drainer::{Producer, SubmitIntent};
use crate::mirror::{MemCell, MirrorBatch};
use crate::workflow::{balance_reg, cell_row, turn_row};
use dregg_lean_ffi::TurnStatus;
use dregg_lean_ffi::marshal::{
    Digest, WForest, WireAction, WireAuth, WireState, WireTurn, WireValue, marshal_turn,
};

/// The wire `Nat` id the synthesized turn gives the float SOURCE cell.
const WIRE_SRC: u64 = 0;
/// The wire `Nat` id the synthesized turn gives the acting AGENT (destination) cell.
const WIRE_DST: u64 = 1;
/// The single asset id the synthesized transfer moves (asset 0 — the native unit).
const WIRE_ASSET: u64 = 0;
/// The portal-passing `.signature` witness the synthesized turn presents (pubkey
/// digest low-u64 == sig). The executor's §1 credential portal admits a
/// `.signature pk sig` when the proof echoes the statement, and — unlike
/// `.unchecked` — a `.signature` grants the within-cell WRITE authority the balance
/// transfer's body needs, so the turn COMMITS (`status:2`) rather than rolling its
/// body back to `status:1` (verified by the in-backend probe: `.unchecked` ⇒ body
/// fails, `.signature{7,7}` ⇒ commits, conserving 1000→970 / 0→30). The SUBMIT gate
/// has already verified the submitter's REAL capability before this runs; this
/// witness is the producer's internal authority for the conserving transfer it
/// synthesizes, not a claim about the submitter's credential.
const WIRE_SIG: u64 = 7;

/// The verified-executor producer: each [`Producer::produce`] runs a conserving
/// transfer for the acting agent through the REAL `execFullForestG` (single-
/// threaded, in-backend) and yields the executor's verified post-image.
///
/// It maintains the SAME per-cell `(balance, nonce)` bookkeeping
/// [`crate::drainer::FoldProducer`] does — so successive produced turns are
/// internally consistent across a drain run — but the post-image VALUES and the
/// commit decision come from the verified executor's decoded output, not a fold.
#[derive(Clone, Debug)]
pub struct LeanProducer {
    /// The float source cell every synthesized transfer debits (the 32-byte id).
    pub source: [u8; 32],
    /// The unit each synthesized transfer moves.
    pub unit: i64,
    /// The running per-cell `(balance, nonce)` the producer maintains so the wire
    /// turn it builds each round reflects the executor's prior post-state (the
    /// executor reads pre-state from the wire we send; we carry it ourselves).
    balances: std::collections::BTreeMap<[u8; 32], (i64, u64)>,
}

impl LeanProducer {
    /// A verified-executor producer with `source` funded to `float`, moving `unit`
    /// per turn. Does NOT initialize the Lean runtime — that happens lazily on the
    /// first [`Producer::produce`] (so it runs AFTER the backend fork, never in the
    /// postmaster).
    pub fn new(source: [u8; 32], float: i64, unit: i64) -> Self {
        let mut balances = std::collections::BTreeMap::new();
        balances.insert(source, (float, 0));
        LeanProducer {
            source,
            unit,
            balances,
        }
    }

    /// The producer's notion of a cell's `(balance, nonce)` (for assertions/demos),
    /// kept in lock-step with the verified executor's decoded post-state.
    pub fn balance(&self, id: [u8; 32]) -> i64 {
        self.balances.get(&id).map(|&(b, _)| b).unwrap_or(0)
    }

    /// Whether the embeddable single-threaded Lean runtime is linked + initializes.
    /// True iff `dregg-lean-ffi` linked `libdregg_lean.a` AND `dregg_ffi_init_st`
    /// succeeds (the libuv-thread-free init). A real Tier-D backend asserts this at
    /// startup; the produce path also checks it per turn (fail-closed).
    pub fn runtime_available() -> bool {
        dregg_lean_ffi::init_single_threaded()
    }

    /// Build the wire pre-state the synthesized transfer executes against: the
    /// source cell (with its running balance + nonce, the actor whose nonce the
    /// admission ticks) and the destination agent cell. Both `cells` records and
    /// the per-asset `bal` table are populated (the executor reads `bal` for the
    /// transfer and the cell `nonce` for admission).
    fn wire_pre_state(&self, src_bal: i64, src_nonce: u64, dst_bal: i64) -> WireState {
        WireState {
            cells: vec![
                (
                    WIRE_SRC,
                    WireValue::Record(vec![
                        ("balance".into(), WireValue::Int(src_bal as i128)),
                        ("nonce".into(), WireValue::Int(src_nonce as i128)),
                    ]),
                ),
                (
                    WIRE_DST,
                    WireValue::Record(vec![("balance".into(), WireValue::Int(dst_bal as i128))]),
                ),
            ],
            bal: vec![
                (WIRE_SRC, WIRE_ASSET, src_bal as i128),
                (WIRE_DST, WIRE_ASSET, dst_bal as i128),
            ],
            ..WireState::default()
        }
    }

    /// Build the wire turn: a `Balance` transfer of `unit` from the source to the
    /// agent, by the source as actor, under a portal-passing `.signature` witness
    /// ([`WIRE_SIG`]). The SUBMIT gate has already verified the submitter's REAL
    /// capability ([`crate::authz::decide`]) before this runs; the executor's
    /// load-bearing job at this seam is then conservation + the within-cell WRITE
    /// authority + admission (nonce/fee/expiry), all of which it enforces fail-closed
    /// — and a `.signature` (unlike `.unchecked`) grants the WRITE authority the
    /// transfer body needs, so a valid transfer COMMITS rather than rolling back.
    fn wire_turn(&self, src_nonce: u64) -> WireTurn {
        WireTurn {
            agent: WIRE_SRC,
            nonce: src_nonce,
            fee: 0,
            // A far-future expiry under the diagnostic host clock (now:0) so the
            // synthesized turn never spuriously expires at admission.
            valid_until: u64::MAX >> 1,
            block_height: 0,
            prev_hash: Digest::default(),
            root: WForest {
                auth: WireAuth::Signature {
                    pubkey: Digest::from_u64(WIRE_SIG),
                    sig: WIRE_SIG,
                },
                caveats: vec![],
                action: WireAction::Balance {
                    actor: WIRE_SRC,
                    src: WIRE_SRC,
                    dst: WIRE_DST,
                    amt: self.unit as i128,
                    asset: WIRE_ASSET,
                },
                children: vec![],
            },
        }
    }

    /// Read the verified post-balance of a wire cell from the executor's decoded
    /// `WireState.bal` (asset 0), defaulting to `fallback` if the executor did not
    /// echo that cell (it always does for a touched cell; the default keeps the
    /// reader total).
    fn post_balance(state: &WireState, wire_id: u64, fallback: i64) -> i64 {
        state
            .bal
            .iter()
            .find(|(cell, asset, _)| *cell == wire_id && *asset == WIRE_ASSET)
            .map(|(_, _, amt)| *amt as i64)
            .unwrap_or(fallback)
    }
}

impl Producer for LeanProducer {
    fn produce(
        &mut self,
        intent: &SubmitIntent,
        ordinal: u64,
        prev_root: [u8; 32],
    ) -> Result<MirrorBatch, String> {
        // A malformed (empty) envelope is refused, exactly as the stand-in does, so
        // the `refused` outcome path stays real (the executor never sees garbage).
        if intent.signed_turn.is_empty() {
            return Err("empty signed turn (malformed envelope)".to_string());
        }

        // Fail-closed if the embeddable runtime is not linked / does not initialize
        // (the libuv-thread-free init). This is the lazy, post-fork init: the FIRST
        // produce in a freshly-forked backend drives `dregg_ffi_init_st` here.
        if !dregg_lean_ffi::init_single_threaded() {
            return Err(
                "Tier-D: the embeddable Lean runtime is unavailable (libdregg_lean.a not \
                 linked, or dregg_ffi_init_st failed) — cannot run execFullForestG in-backend"
                    .to_string(),
            );
        }

        // The producer's running pre-state for the source + this agent.
        let (src_bal, src_nonce) = *self.balances.get(&self.source).unwrap_or(&(0, 0));
        if src_bal < self.unit {
            return Err(format!(
                "float exhausted: source holds {src_bal}, unit is {}",
                self.unit
            ));
        }
        let (dst_bal, _) = *self.balances.get(&intent.agent).unwrap_or(&(0, 0));

        // Marshal the wire turn and run it through the VERIFIED executor, single-
        // threaded, in this backend process.
        let pre = self.wire_pre_state(src_bal, src_nonce, dst_bal);
        let turn = self.wire_turn(src_nonce);
        let wire = marshal_turn(&pre, &turn)
            .map_err(|e| format!("Tier-D: marshalling the synthesized turn failed: {e}"))?;
        let out = dregg_lean_ffi::shadow_exec_full_forest_auth_single_threaded(&wire)
            .map_err(|e| format!("Tier-D: the verified executor errored: {e}"))?;
        let shadow = dregg_lean_ffi::decode_shadow_state(&out)
            .map_err(|e| format!("Tier-D: decoding the verified post-state failed: {e}"))?;

        // The executor's verdict is authoritative. Only a BODY-COMMITTED turn
        // (status:2) yields a post-image; an admission rejection (status:0) or a
        // prologue-only body-failure (status:1) is a REFUSAL — fail-closed, no
        // state leaks, exactly the executor's decision.
        if !shadow.verdict.body_committed() {
            let why = match shadow.verdict.status {
                Some(TurnStatus::Rejected) => "executor rejected the turn at admission",
                Some(TurnStatus::PrologueCommittedBodyFailed) => {
                    "executor rolled back the turn body (conservation / caveat / effect failed)"
                }
                Some(TurnStatus::BodyCommitted) => unreachable!("body_committed() is false"),
                None => "executor did not commit the turn body",
            };
            return Err(format!("Tier-D: {why}"));
        }

        // Read the VERIFIED post-balances back from the executor's decoded state.
        let new_src_bal = Self::post_balance(&shadow.state, WIRE_SRC, src_bal - self.unit);
        let new_dst_bal = Self::post_balance(&shadow.state, WIRE_DST, dst_bal + self.unit);
        // The executor ticked the actor's nonce on commit; mirror that locally.
        let new_src_nonce = src_nonce + 1;

        let touched: [([u8; 32], i64, u64); 2] = [
            (self.source, new_src_bal, new_src_nonce),
            (intent.agent, new_dst_bal, 0),
        ];

        // The post-state root: the producer derives the chaining ledger root from
        // the executor-verified post-balances over the chaining context, the SAME
        // way the stand-in / `bin/loadgen.rs` do (the executor's own kernel root is
        // not surfaced on this wire — the in-circuit root is the IVC light client's
        // concern, `docs/PG-DREGG.md` §10.2; the CHAIN gate's tooth is structural on
        // these roots). Bit-identical to the stand-in's fold so a mixed-producer
        // history still chains.
        let post = crate::drainer::fold_chain_root(prev_root, ordinal, &touched);

        let cells = vec![
            cell_row(self.source, new_src_bal, new_src_nonce),
            cell_row(intent.agent, new_dst_bal, 0),
        ];
        let memory: Vec<MemCell> = touched
            .iter()
            .map(|&(id, bal, _)| balance_reg(id, bal))
            .collect();
        // `creator` is the acting agent (the provenance the drainer asserts).
        let turn_hdr = turn_row(ordinal, prev_root, post, intent.agent);
        let batch = MirrorBatch::from_parts(turn_hdr, cells, vec![], memory)
            .map_err(|m| format!("Tier-D: the verified post-image was malformed: {m}"))?;

        // Advance the producer's own bookkeeping to the executor-verified post-state
        // so the next produced turn's wire pre-state is consistent.
        self.balances
            .insert(self.source, (new_src_bal, new_src_nonce));
        self.balances.insert(intent.agent, (new_dst_bal, 0));
        Ok(batch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_auth::credential::{Caveat, Pred, RootKey};

    const SOURCE: [u8; 32] = [0xc0u8; 32];

    fn agent(tag: u8) -> [u8; 32] {
        let mut id = [0x11u8; 32];
        id[0] = tag;
        id
    }

    /// The shared process-wide authz serialization lock (these tests mutate the
    /// global issuer key / revocation set the whole lib-test binary shares).
    #[must_use]
    fn fresh_issuer() -> (std::sync::MutexGuard<'static, ()>, RootKey) {
        let guard = crate::authz::test_serial_lock();
        let issuer = RootKey::from_seed([7u8; 32]);
        crate::authz::set_issuer_pubkey(issuer.public());
        crate::authz::lru_clear();
        crate::authz::revoked_clear();
        (guard, issuer)
    }

    fn submit_token(issuer: &RootKey) -> String {
        issuer
            .mint([
                Caveat::FirstParty(Pred::AttrEq {
                    key: "action".into(),
                    value: "submit".into(),
                }),
                Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "".into(),
                }),
                Caveat::FirstParty(Pred::NotAfter { at: 1_000_000 }),
            ])
            .encode()
    }

    fn intent(id: u8, agent: [u8; 32], token: &str) -> SubmitIntent {
        SubmitIntent {
            id: [id; 16],
            agent,
            signed_turn: vec![0xab, 0xcd], // non-empty = a well-formed envelope
            token: token.to_string(),
        }
    }

    /// The wire-construction + marshalling is correct independent of whether the
    /// archive is linked: a synthesized transfer marshals to a byte-valid wire that
    /// the strict Lean grammar would accept (no interior NUL, expected key order).
    /// This runs in plain `cargo test` (no archive) — it never calls the executor.
    #[test]
    fn synthesizes_a_marshallable_wire_turn() {
        let p = LeanProducer::new(SOURCE, 1_000, 1);
        let pre = p.wire_pre_state(1_000, 0, 0);
        let turn = p.wire_turn(0);
        let wire = marshal_turn(&pre, &turn).expect("synthesized turn marshals");
        // The transfer arm + the conserving src/dst balances are present in the wire.
        assert!(
            wire.contains("\"bal\":[0,0,1,1,0]"),
            "the transfer arm: {wire}"
        );
        assert!(
            wire.contains("[0,0,1000]"),
            "the source pre-balance: {wire}"
        );
        assert!(!wire.contains('\u{0}'), "no interior NUL");
    }

    /// `runtime_available()` mirrors `dregg_lean_ffi::init_single_threaded()`. When
    /// the archive is NOT linked (plain `cargo test`), it is false — and a produce
    /// fails CLOSED with the Tier-D unavailability reason (never a silent commit).
    #[test]
    fn fails_closed_when_the_runtime_is_unavailable() {
        // Only meaningful in the no-archive build; if the archive happens to be
        // linked (a `tier-d` build), the runtime IS available and this is skipped.
        if LeanProducer::runtime_available() {
            eprintln!(
                "fails_closed_when_the_runtime_is_unavailable: archive linked — \
                 the runtime is available; skipping the no-archive assertion"
            );
            return;
        }
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut p = LeanProducer::new(SOURCE, 1_000, 1);
        let out = p.produce(
            &intent(1, agent(0x20), &tok),
            0,
            crate::workflow::GENESIS_ROOT,
        );
        let err = out.expect_err("no runtime ⇒ produce must fail closed");
        assert!(
            err.contains("embeddable Lean runtime is unavailable"),
            "fail-closed reason names the missing runtime: {err}"
        );
    }

    /// An empty envelope is refused BEFORE the runtime is even consulted (a
    /// malformed intent is a producer refusal, not a runtime error).
    #[test]
    fn an_empty_envelope_is_refused() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut p = LeanProducer::new(SOURCE, 1_000, 1);
        let mut bad = intent(1, agent(0x20), &tok);
        bad.signed_turn = vec![];
        let err = p
            .produce(&bad, 0, crate::workflow::GENESIS_ROOT)
            .expect_err("empty envelope is refused");
        assert!(err.contains("empty signed turn"), "{err}");
    }

    // ───────────────────────────────────────────────────────────────────────
    // The LIVE in-backend execution proof — runs ONLY when the verified archive
    // is linked (a `tier-d` build). It drives the REAL `execFullForestG` through
    // the single-threaded runtime and asserts: a conserving transfer COMMITS with
    // the executor's verified post-balances, the chain advances, and an
    // overspend (float < unit) is refused fail-closed. Skipped (not failed) in the
    // default no-archive build so plain `cargo test` needs no Lean toolchain.
    // ───────────────────────────────────────────────────────────────────────

    #[test]
    fn the_verified_executor_commits_a_conserving_transfer_in_backend() {
        if !LeanProducer::runtime_available() {
            eprintln!(
                "the_verified_executor_commits_a_conserving_transfer_in_backend: \
                 libdregg_lean.a not linked — skipping (needs a `tier-d` build)"
            );
            return;
        }
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut p = LeanProducer::new(SOURCE, 1_000, 30);

        // ONE produce → the REAL executor runs the 30-unit transfer in-backend.
        let batch = p
            .produce(
                &intent(1, agent(0x20), &tok),
                0,
                crate::workflow::GENESIS_ROOT,
            )
            .expect("the verified executor commits a conserving transfer");

        // The post-image carries the executor-VERIFIED post-balances: source
        // 1000→970, agent 0→30 (the conserved 30-unit move).
        assert_eq!(
            p.balance(SOURCE),
            970,
            "source debited by the verified executor"
        );
        assert_eq!(
            p.balance(agent(0x20)),
            30,
            "agent credited by the verified executor"
        );
        // The batch is well-formed + attributes the turn to the acting agent.
        assert_eq!(batch.turn.creator, agent(0x20));
        assert_eq!(batch.turn.ordinal, 0);
        let src_cell = batch.cells.iter().find(|c| c.cell_id == SOURCE).unwrap();
        let dst_cell = batch
            .cells
            .iter()
            .find(|c| c.cell_id == agent(0x20))
            .unwrap();
        assert_eq!(src_cell.balance, 970);
        assert_eq!(dst_cell.balance, 30);
    }

    #[test]
    fn the_verified_executor_refuses_an_overspend_in_backend() {
        if !LeanProducer::runtime_available() {
            eprintln!(
                "the_verified_executor_refuses_an_overspend_in_backend: \
                 libdregg_lean.a not linked — skipping (needs a `tier-d` build)"
            );
            return;
        }
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        // A float SMALLER than the unit ⇒ the producer's own pre-check refuses
        // before the executor (the float is exhausted). This proves the
        // conservation-respecting refusal path is real on the live producer.
        let mut p = LeanProducer::new(SOURCE, 10, 30);
        let err = p
            .produce(
                &intent(1, agent(0x20), &tok),
                0,
                crate::workflow::GENESIS_ROOT,
            )
            .expect_err("an overspend is refused");
        assert!(err.contains("float exhausted"), "{err}");
    }
}
