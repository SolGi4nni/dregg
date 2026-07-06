//! # confined-swarm — the provably-independent, provably-sourced AI analyst swarm
//!
//! Fork ONE trusted, primed confined agent into **N sovereign workers**, each jailed
//! to exactly ONE data source, each attestation-proving what it read, and — the killer
//! property — **provably non-colluding**. Because the workers are umem-forks of one
//! primed root ([`grain_fork::ConfinedSession`]), worker A's mind/heap never touched
//! worker B's, so the N reports are *provably independent*: they could not have colluded
//! — each only ever saw its own source. "Provably-independent, provably-sourced AI
//! analysts" — a thing only the dregg substrate can build.
//!
//! ## What is REAL vs modeled
//!
//! * **REAL — the fork / isolation / budget-split / attenuation teeth.** The swarm forks
//!   with [`grain_fork::ConfinedSession::fork_two`] (the proven primitive: one checkpoint
//!   → two sovereign confined lives, budget SPLIT not duplicated, egress attenuated, umem
//!   heap isolation). [`Swarm::fork_workers`] chains `fork_two` into an n-ary fork so the
//!   total-budget conservation is enforced across the WHOLE chain — `fork_two` checks the
//!   SUM of its two children against the parent, so a chain of them checks the sum of all
//!   N against the root. The non-collusion property is the *isolation tooth* of
//!   `ConfinedSession`: a write in one fork is provably absent from every other.
//! * **REAL — the attestation.** Each worker's report carries a
//!   [`dregg_zkoracle_prove::ZkOracleAttestation`] produced by the real
//!   [`dregg_zkoracle_prove::prove_zkoracle`] and checked by
//!   [`dregg_zkoracle_prove::verify_zkoracle`] (authentic ∧ well-formed ∧ injection-free).
//!   These are the SAME primitives `deos_hermes::attest::AttestationCarrier` composes;
//!   [`SwarmAttestationCarrier`] composes them directly so the swarm stays light (the
//!   modeled ed25519 authentic carrier + the JSON CFG parse-cert + the injection matcher —
//!   no HTTP/TLS, no verified-Lean-executor link). The real local MPC-TLS 2PC roundtrip is
//!   behind the `tlsn-live` feature.
//! * **MODELED — the brain.** A worker "investigates" its source with a
//!   [`ResearchBrain`]; the default [`RecordedBrain`] deterministically reads the source's
//!   authentic bytes and writes its finding. The brain is a stand-in for a live LLM (that
//!   lane is `deos_hermes::DreggHost::run_hosted_agent_live`); the *confinement*,
//!   *isolation*, *budget*, and *attestation* teeth around it are real.
//!
//! ## The teeth (all bite — see the tests)
//!
//! [`Swarm::verify`] confirms, and REFUSES a swarm that fails, each of:
//! (a) every report is **attested** (`verify_zkoracle` accepts);
//! (b) every worker's egress was **jailed to its ONE declared source** (its confinement
//!     grants exactly that one door);
//! (c) **fork-isolation holds** — no cross-worker mind contact (a colluding/cross-
//!     contaminated swarm is caught: a worker's mind carries ONLY its own source's trace);
//! (d) the **budget was split, not duplicated** (the workers' budgets sum to ≤ the root's).

use std::collections::BTreeSet;

use dregg_cell::CellId;
use grain_fork::{ConfinedForkError, ConfinedSession, Confinement, ForkSpec};
use hosted_lease::LeaseTerms;

use dregg_zkoracle_prove::{
    build_anthropic_fixture, prove_zkoracle, verify_zkoracle, AnthropicConfig, FixtureNotary,
    ProveError, ZkOracleAttestation,
};

// ─────────────────────────────────────────────────────────────────────────────
// The attestation carrier — the real zkoracle-prove primitives, composed.
// ─────────────────────────────────────────────────────────────────────────────

/// The modeled session time stamped on the carrier's presentation (unix seconds). The
/// attestation is about the response BODY; the exact timestamp is not load-bearing.
const ATTEST_CONNECTION_TIME: u64 = 1_700_000_000;

/// The default deterministic seed for the swarm's modeled notary carrier, so a run's
/// attestations verify against a reproducible pinned anchor.
pub const DEFAULT_SWARM_SEED: [u8; 32] = [0x5C; 32];

/// **A worker's attestation carrier** — the modeled authentic anchor each worker's report
/// is attested under. Holds the notary that signs the presentation carrier and the pinned
/// [`AnthropicConfig`] a verifier checks against. This is the direct composition of the
/// real [`dregg_zkoracle_prove`] primitives (`build_anthropic_fixture` + `prove_zkoracle`),
/// the same ones `deos_hermes::attest::AttestationCarrier` wraps — kept here so the swarm
/// needs no HTTP/TLS / verified-Lean link for its default (modeled) path.
pub struct SwarmAttestationCarrier {
    notary: FixtureNotary,
    config: AnthropicConfig,
}

impl Default for SwarmAttestationCarrier {
    fn default() -> Self {
        SwarmAttestationCarrier::from_seed(&DEFAULT_SWARM_SEED)
    }
}

impl SwarmAttestationCarrier {
    /// A carrier from a 32-byte notary seed. Its [`Self::config`] pins that notary's
    /// verifying key — the anchor `verify_zkoracle` checks the attestation against.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let notary = FixtureNotary::from_seed(seed);
        let config = AnthropicConfig::new(notary.verifying_key());
        SwarmAttestationCarrier { notary, config }
    }

    /// The pinned config a verifier uses: `verify_zkoracle(&att, carrier.config())`.
    pub fn config(&self) -> &AnthropicConfig {
        &self.config
    }

    /// PRODUCE a zkOracle attestation over an Anthropic messages RESPONSE BODY, binding
    /// `field` (which MUST be a substring of `response_body`) injection-free. The modeled
    /// carrier signs the presentation; [`prove_zkoracle`] proves the CFG (well-formed) and
    /// injection-free legs and binds them to this one response. Refuses a malformed body,
    /// an injecting field, or a field absent from the body.
    pub fn attest_body(
        &self,
        response_body: &str,
        field: &[u8],
    ) -> Result<ZkOracleAttestation, ProveError> {
        let pres = build_anthropic_fixture(&self.notary, response_body, ATTEST_CONNECTION_TIME);
        prove_zkoracle(pres, field.to_vec(), self.config())
    }

    /// ATTEST A WORKER'S REPORT. Shapes the report text into an Anthropic messages object
    /// and binds that text injection-free — so the attestation certifies the model's ACTUAL
    /// finding this turn (authentic session + well-formed JSON + no `{{` in its own words).
    /// Returns the attestation and the exact field bound (the sanitized report text).
    pub fn attest_report(
        &self,
        report: &str,
    ) -> Result<(ZkOracleAttestation, Vec<u8>), ProveError> {
        let field = clean_field(report);
        let body = messages_body(&field);
        let att = self.attest_body(&body, field.as_bytes())?;
        Ok((att, field.into_bytes()))
    }
}

/// Shape a bound field into a well-formed Anthropic messages RESPONSE BODY (the shape
/// `/v1/messages` returns): the assistant `content[0].text` IS the field, so the field is
/// a verbatim, committed substring of the body.
fn messages_body(field: &str) -> String {
    format!(
        "{{\"id\":\"msg_worker\",\"type\":\"message\",\"role\":\"assistant\",\
         \"model\":\"claude-opus-4-8\",\
         \"content\":[{{\"type\":\"text\",\"text\":\"{field}\"}}],\
         \"stop_reason\":\"end_turn\",\"stop_sequence\":null,\
         \"usage\":{{\"input_tokens\":16,\"output_tokens\":8}}}}"
    )
}

/// Render `text` into a JSON-string-safe field that embeds verbatim (no escaping): drop
/// the two bytes JSON strings must escape (`"` and `\`) and the raw control chars, keeping
/// everything else — crucially the `{` / `}` bytes, so a genuine `{{` handlebars-injection
/// attempt in a report SURVIVES into the field and the injection-free leg still fires on it
/// (the load-bearing catch is preserved, not sanitized away). An empty result falls back to
/// a placeholder so the bound field is always a real substring.
fn clean_field(text: &str) -> String {
    let cleaned: String = text
        .chars()
        .filter(|c| *c != '"' && *c != '\\' && !c.is_control())
        .collect();
    let trimmed = cleaned.trim();
    if trimmed.is_empty() {
        "worker report".to_string()
    } else {
        trimmed.to_string()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Sources + the (modeled) research brain.
// ─────────────────────────────────────────────────────────────────────────────

/// A named data source a worker is jailed to. Its [`Source::door`] is the single egress
/// endpoint the worker's confinement grants (`host:port`); its [`Source::content`] is the
/// authentic bytes the worker reads (a modeled data source — the real network fetch rides
/// the granted socket door in `deos_hermes::DreggHost::run_hosted_agent_live`).
#[derive(Clone, Debug)]
pub struct Source {
    /// A short human name, e.g. `"arxiv"`.
    pub name: String,
    /// The single egress door the jailed worker may reach for this source, `host:port`.
    pub door: String,
    /// The authentic source bytes the worker reads.
    pub content: Vec<u8>,
}

impl Source {
    /// A source with the given name, egress door, and content bytes.
    pub fn new(
        name: impl Into<String>,
        door: impl Into<String>,
        content: impl Into<Vec<u8>>,
    ) -> Source {
        Source {
            name: name.into(),
            door: door.into(),
            content: content.into(),
        }
    }

    /// The BLAKE3 digest of the source content — what a worker writes into its mind as the
    /// witnessed trace of "I read exactly this source" (and nothing else).
    pub fn digest(&self) -> [u8; 32] {
        *blake3::hash(&self.content).as_bytes()
    }
}

/// How a worker turns its ONE source into a finding. A stand-in for a live LLM brain: the
/// swarm's confinement / isolation / budget / attestation teeth are real around whatever
/// brain drives the turn.
pub trait ResearchBrain {
    /// Read `source` (the ONLY source this worker can reach) under `brief` and return the
    /// report text. MUST NOT emit a `{{` handlebars sequence (an injecting report is
    /// un-attestable — the injection-free leg refuses it at produce time).
    fn investigate(&self, brief: &str, source: &Source) -> String;
}

/// The default modeled brain: deterministically reads the source's authentic bytes and
/// reports what it read (name + byte count + a short content digest + the first line of the
/// source). Deterministic so a run is reproducible; every report is injection-free.
#[derive(Clone, Copy, Debug, Default)]
pub struct RecordedBrain;

impl ResearchBrain for RecordedBrain {
    fn investigate(&self, brief: &str, source: &Source) -> String {
        let digest = source.digest();
        let hex8: String = digest[..4].iter().map(|b| format!("{b:02x}")).collect();
        let first_line = String::from_utf8_lossy(&source.content)
            .lines()
            .next()
            .unwrap_or("")
            .chars()
            .take(80)
            .collect::<String>();
        // Keep the report injection-free (drop any stray brace runs from the source line).
        let first_line = first_line.replace('{', "(").replace('}', ")");
        let brief = brief.chars().take(60).collect::<String>();
        format!(
            "[{name}] brief: {brief} -- read {n} bytes from {door}; digest {hex8}; finding: {first_line}",
            name = source.name,
            n = source.content.len(),
            door = source.door,
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The swarm: prime one root, fork N sovereign workers, verify the killer property.
// ─────────────────────────────────────────────────────────────────────────────

/// The working-memory key the primed research brief is written at in the root mind (and,
/// via the fork, inherited by every worker — the shared starting mind).
pub const BRIEF_KEY: u32 = 0x0000_B41E;

/// The base working-memory key a worker writes its source digest at: worker `i` writes at
/// `SOURCE_KEY_BASE + i`. So a worker's mind carries the trace of EXACTLY the one source it
/// read; a foreign source's key is absent (the non-collusion witness).
pub const SOURCE_KEY_BASE: u32 = 0x0053_0000;

/// One forked, jailed, attested research worker: a sovereign [`ConfinedSession`] jailed to
/// ONE source, with the report it produced and the attestation proving what it read.
pub struct Worker {
    /// This worker's source index in the swarm (its source key is `SOURCE_KEY_BASE + i`).
    pub index: usize,
    /// The source this worker was jailed to.
    pub source: Source,
    /// The worker's own sovereign confined session (its mind + budget + confinement +
    /// receipt chain). Forked from the primed root; provably isolated from its siblings.
    pub session: ConfinedSession,
    /// The report the worker's brain produced from its one source.
    pub report: String,
    /// The attestation over the report (authentic ∧ well-formed ∧ injection-free), when the
    /// worker's turn was attested. `None` for an unattested worker (which [`Swarm::verify`]
    /// refuses).
    pub attestation: Option<ZkOracleAttestation>,
}

impl Worker {
    /// The working-memory key this worker's source digest is written at.
    pub fn source_key(&self) -> u32 {
        SOURCE_KEY_BASE + self.index as u32
    }

    /// The worker's remaining prepaid budget (its share of the root's, split at the fork).
    pub fn budget(&self) -> i64 {
        self.session.budget()
    }
}

/// Why building or forking a swarm was refused.
#[derive(Debug)]
pub enum SwarmError {
    /// A swarm needs at least one source.
    NoSources,
    /// The confined-session fork was refused (budget overdraw / egress amplification /
    /// unconferrable cap) — the fork teeth biting.
    Fork(ConfinedForkError),
    /// A worker's report could not be attested (injecting / malformed / etc.).
    Attest(ProveError),
}

impl std::fmt::Display for SwarmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SwarmError::NoSources => write!(f, "a swarm needs at least one source"),
            SwarmError::Fork(e) => write!(f, "swarm fork refused: {e}"),
            SwarmError::Attest(e) => write!(f, "worker report not attestable: {e}"),
        }
    }
}

impl std::error::Error for SwarmError {}

impl From<ConfinedForkError> for SwarmError {
    fn from(e: ConfinedForkError) -> Self {
        SwarmError::Fork(e)
    }
}

/// The verdict [`Swarm::verify`] returns — the four teeth of the killer property, each a
/// verifiable boolean. [`SwarmVerdict::accepted`] is their conjunction: an
/// independent-and-sourced analyst swarm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwarmVerdict {
    /// (a) Every worker's report carries a `verify_zkoracle`-accepted attestation.
    pub all_attested: bool,
    /// (b) Every worker's confinement grants EXACTLY its one declared source door.
    pub each_jailed_to_one_source: bool,
    /// (c) Fork-isolation holds: no cross-worker mind contact. Each worker's mind carries
    /// the trace of ONLY its own source; no foreign source key appears — the workers could
    /// not have colluded.
    pub non_colluding: bool,
    /// Bonus: every worker's mind still carries the primed brief — they all descend from
    /// the one trusted root (provable common ancestry, not asserted).
    pub common_ancestry: bool,
    /// (d) The workers' budgets sum to ≤ the root's budget — split, not duplicated.
    pub budget_conserved: bool,
    /// The root's budget at the fork point (the conservation ceiling).
    pub root_budget: i64,
    /// The sum of the workers' budgets.
    pub total_worker_budget: i64,
}

impl SwarmVerdict {
    /// The killer property: attested ∧ jailed-to-one-source ∧ non-colluding ∧
    /// budget-conserved. (Common ancestry strengthens it but is folded in too.)
    pub fn accepted(&self) -> bool {
        self.all_attested
            && self.each_jailed_to_one_source
            && self.non_colluding
            && self.common_ancestry
            && self.budget_conserved
    }
}

/// The swarm orchestration: prime one trusted confined root, fork it into N sovereign
/// jailed workers, drive each against its one source, and verify the killer property.
pub struct Swarm {
    /// The primed brief every worker inherits (the shared starting mind).
    brief: String,
    /// The root's budget at the fork point — the conservation ceiling the sum of worker
    /// budgets must stay within.
    root_budget: i64,
    /// The sources, one per worker, in worker-index order.
    sources: Vec<Source>,
    /// The forked, jailed, attested workers.
    workers: Vec<Worker>,
}

impl Swarm {
    /// **Rent + prime one trusted confined root, then fork it into N sovereign workers.**
    ///
    /// 1. A fresh root [`ConfinedSession`] is rented, primed with `brief` (written into the
    ///    root mind — the shared starting mind every worker inherits), and its confinement
    ///    granted the union of ALL sources' doors (so each child can *attenuate* to its own
    ///    one door — a fork mints no reach).
    /// 2. The root is forked into `sources.len()` sovereign workers by chaining
    ///    [`ConfinedSession::fork_two`] ([`Swarm::fork_workers`]): each worker gets its own
    ///    obligor lease, a split of the root's budget, and a confinement of EXACTLY its one
    ///    source door.
    /// 3. Each worker drives `brain` against its ONE source, writes the source digest into
    ///    its own mind (the isolation witness), produces a report, and attests it.
    ///
    /// `root_funding` must be ≥ the sum of `per_worker_budget × N` (the fork's budget-split
    /// tooth refuses an over-split with [`ConfinedForkError::BudgetOverdraw`]).
    pub fn assemble<B: ResearchBrain>(
        brief: impl Into<String>,
        sources: Vec<Source>,
        root_funding: i64,
        per_worker_budget: i64,
        brain: &B,
        carrier: &SwarmAttestationCarrier,
    ) -> Result<Swarm, SwarmError> {
        if sources.is_empty() {
            return Err(SwarmError::NoSources);
        }
        let brief = brief.into();

        // (1) The primed root: a fresh confined session whose confinement grants EVERY
        //     source door (children attenuate down to one each), primed with the brief.
        let all_doors: BTreeSet<String> = sources.iter().map(|s| s.door.clone()).collect();
        let mut root = ConfinedSession::rent(
            [0xA0; 32],
            [0x01; 32],
            root_lease_terms(),
            root_funding,
            Confinement::new(all_doors),
        )
        .map_err(|e| SwarmError::Fork(ConfinedForkError::Grain(e)))?;
        // Prime the shared mind: the brief every worker will inherit through the fork.
        root.record_turn(BRIEF_KEY, brief_digest(&brief), "prime:brief", 0);
        let root_budget = root.budget();

        // (2) Fork the primed root into N sovereign jailed sessions (budget split, egress
        //     attenuated to one door each) — the fork star, chained to n-ary.
        let budgets = vec![per_worker_budget; sources.len()];
        let doors: Vec<String> = sources.iter().map(|s| s.door.clone()).collect();
        let sessions = Self::fork_workers(root, &budgets, &doors)?;

        // (3) Each worker investigates its ONE source, writes the source trace into its own
        //     mind, produces a report, and attests it.
        let mut workers = Vec::with_capacity(sources.len());
        for (index, (mut session, source)) in sessions
            .into_iter()
            .zip(sources.iter().cloned())
            .enumerate()
        {
            let report = brain.investigate(&brief, &source);
            // Write the source digest into THIS worker's mind, at this worker's source key —
            // the private write that is provably absent from every sibling's mind.
            session.record_turn(
                SOURCE_KEY_BASE + index as u32,
                source.digest(),
                format!("read:{}", source.name),
                (source.content.len() as i64).min(per_worker_budget),
            );
            // Attest the report — authentic ∧ well-formed ∧ injection-free.
            let (attestation, _field) =
                carrier.attest_report(&report).map_err(SwarmError::Attest)?;
            workers.push(Worker {
                index,
                source,
                session,
                report,
                attestation: Some(attestation),
            });
        }

        Ok(Swarm {
            brief,
            root_budget,
            sources,
            workers,
        })
    }

    /// **The n-ary swarm fork — chain [`ConfinedSession::fork_two`] into N sovereign
    /// workers.** Consumes the primed `root` and splits it into `budgets.len()` confined
    /// sessions, worker `i` jailed to `doors[i]` with budget `budgets[i]`.
    ///
    /// Each step splits the current session into (worker `i`, the remainder holding the
    /// rest). Because `fork_two` checks the SUM of its two children against the parent, the
    /// chain enforces total-budget conservation across ALL N workers: `sum(budgets)` must be
    /// ≤ the root's budget, else the first split refuses with
    /// [`ConfinedForkError::BudgetOverdraw`]. Each worker's confinement is attenuated to its
    /// ONE door; the remainder carries the union of the remaining doors so a later split can
    /// still grant them (a fork mints no reach, so the remainder cannot amplify).
    pub fn fork_workers(
        root: ConfinedSession,
        budgets: &[i64],
        doors: &[String],
    ) -> Result<Vec<ConfinedSession>, ConfinedForkError> {
        assert_eq!(
            budgets.len(),
            doors.len(),
            "one budget + one door per worker"
        );
        let k = budgets.len();
        let mut workers = Vec::with_capacity(k);
        let mut current = root;
        let mut nonce: u64 = 0;
        for i in 0..k {
            // Worker i: its ONE door + its budget share.
            let worker_spec =
                ForkSpec::new(worker_lease_terms(nonce), budgets[i]).egress([doors[i].clone()]);
            nonce += 1;
            // The remainder: the rest of the workers' budgets + the union of their doors.
            let rest_budget: i64 = budgets[i + 1..].iter().sum();
            let rest_doors: Vec<String> = doors[i + 1..].to_vec();
            let remainder_spec =
                ForkSpec::new(worker_lease_terms(nonce), rest_budget).egress(rest_doors);
            nonce += 1;

            let (worker, remainder) = current.fork_two(worker_spec, remainder_spec)?;
            workers.push(worker);
            current = remainder;
        }
        // `current` is now the spent remainder (budget 0, no doors) — dropped.
        Ok(workers)
    }

    /// The primed brief every worker inherits.
    pub fn brief(&self) -> &str {
        &self.brief
    }

    /// The forked, jailed, attested workers.
    pub fn workers(&self) -> &[Worker] {
        &self.workers
    }

    /// The sources, one per worker.
    pub fn sources(&self) -> &[Source] {
        &self.sources
    }

    /// **VERIFY the killer property** — the four teeth that make these
    /// provably-independent, provably-sourced analysts. Confirms (and, via
    /// [`SwarmVerdict::accepted`], REFUSES a swarm that fails):
    ///
    /// (a) **attested** — every report's [`verify_zkoracle`] accepts against `carrier`;
    /// (b) **jailed to one source** — every worker's confinement grants EXACTLY its one
    ///     declared source door (not its siblings', not zero, not more);
    /// (c) **non-colluding** — fork-isolation holds: each worker's mind carries the trace of
    ///     ONLY its own source (its source key), and NO foreign source key — so no worker
    ///     ever saw another's source; they could not have colluded;
    /// (d) **budget conserved** — the workers' budgets sum to ≤ the root's (split, not
    ///     duplicated).
    ///
    /// Plus common ancestry: every worker still carries the primed brief.
    pub fn verify(&self, carrier: &SwarmAttestationCarrier) -> SwarmVerdict {
        let want_brief = brief_digest(&self.brief);

        // (a) every report attested.
        let all_attested = self.workers.iter().all(|w| {
            w.attestation
                .as_ref()
                .is_some_and(|att| verify_zkoracle(att, carrier.config()).is_ok())
        });

        // (b) every worker jailed to EXACTLY its one declared source door.
        let each_jailed_to_one_source = self.workers.iter().all(|w| {
            let c = w.session.confinement();
            c.len() == 1 && c.allows(&w.source.door)
        });

        // (c) non-collusion: each worker's mind carries ONLY its own source key; every
        //     foreign source key is absent (no cross-worker mind contact).
        let non_colluding = self.workers.iter().all(|w| {
            let own_key = w.source_key();
            // Its own source trace is present and correct...
            let owns = w.session.recall(own_key) == Some(w.source.digest());
            // ...and NO other worker's source key is present in this mind.
            let no_foreign = self
                .workers
                .iter()
                .filter(|other| other.index != w.index)
                .all(|other| w.session.recall(other.source_key()).is_none());
            owns && no_foreign
        });

        // Common ancestry: every worker still carries the primed brief.
        let common_ancestry = self
            .workers
            .iter()
            .all(|w| w.session.recall(BRIEF_KEY) == Some(want_brief));

        // (d) budget split, not duplicated.
        let total_worker_budget: i64 = self.workers.iter().map(|w| w.budget()).sum();
        let budget_conserved = total_worker_budget <= self.root_budget;

        SwarmVerdict {
            all_attested,
            each_jailed_to_one_source,
            non_colluding,
            common_ancestry,
            budget_conserved,
            root_budget: self.root_budget,
            total_worker_budget,
        }
    }

    /// The root's budget at the fork point (the conservation ceiling).
    pub fn root_budget(&self) -> i64 {
        self.root_budget
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Lease terms + brief digest helpers.
// ─────────────────────────────────────────────────────────────────────────────

/// A worker's own obligor lease terms, unique per `nonce` (so two fork children never
/// share a lease — [`ConfinedSession::fork_two`] asserts distinct obligors).
fn worker_lease_terms(nonce: u64) -> LeaseTerms {
    let mut lease = [0u8; 32];
    lease[..8].copy_from_slice(&nonce.to_le_bytes());
    lease[8] = 0x5C; // swarm-worker lease marker
    LeaseTerms::new(
        CellId::from_bytes([0x02; 32]), // provider
        CellId::from_bytes(lease),      // lease cell (unique per worker)
        CellId::from_bytes([0x09; 32]), // asset
        100,
        50,
        1_000_000,
        0,
    )
}

/// The primed root's own lease terms.
fn root_lease_terms() -> LeaseTerms {
    LeaseTerms::new(
        CellId::from_bytes([0x02; 32]),
        CellId::from_bytes([0x5C; 32]),
        CellId::from_bytes([0x09; 32]),
        100,
        50,
        1_000_000,
        0,
    )
}

/// The digest of the primed brief written into the root mind (and inherited by every
/// worker). Domain-separated so it is not confusable with a source digest.
fn brief_digest(brief: &str) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("confined-swarm-brief-v1");
    h.update(brief.as_bytes());
    *h.finalize().as_bytes()
}

#[cfg(test)]
mod tests;
