//! **Fork-a-confined-session** — the umem "scale IS fork" superpower applied to a
//! live *confined agent session*.
//!
//! A confined session is a jailed agent body driven behind the grain's `AgentBrain`
//! seam (`grain_jail::ConfinedBrain`): every action it proposes is cap-gated, metered
//! against a prepaid budget, and receipted. Its *state* is not the live channel — it
//! is (a) the grain's committed mind (working memory + authority), (b) the prepaid
//! budget in the hosting lease, (c) the **confinement**: the egress surface the jailed
//! body may reach, and (d) the session's receipt chain. A [`ConfinedSession`] bundles
//! exactly those four so a live confined session can **checkpoint** and **fork into two
//! sovereign lives** — the thing a bare [`Grain`] could not, because a grain models the
//! mind/budget/authority but not the jail's egress surface nor the session receipt chain.
//!
//! ## What a fork guarantees (the four teeth)
//!
//! [`ConfinedSession::fork_two`] takes ONE checkpoint and yields TWO independent
//! sovereign sessions. Each is:
//!
//! 1. **Sovereign** — its own grain (own lease/obligor, own committed mind), its own
//!    confinement, its own receipt chain. Consuming the parent (`self` by value) is
//!    deliberate: the checkpoint becomes the shared fork point and the two children ARE
//!    the two lives — the parent budget is not double-counted.
//! 2. **Attenuated, never amplified** — a child's egress doors must be a SUBSET of the
//!    parent's ([`ConfinedForkError::EgressNotAttenuated`]) and its conferred caps a
//!    subset of what the parent holds (the underlying [`Grain::fork`]'s
//!    [`GrainError::UnconferrableCap`]). A fork mints no reach.
//! 3. **Budget-conserving** — the two children's budgets must SUM to no more than the
//!    parent had at the checkpoint ([`ConfinedForkError::BudgetOverdraw`]). You cannot
//!    mint budget by forking; the prepaid reserve is SPLIT, not duplicated.
//! 4. **Independently verifiable + isolated** — each child's receipt chain is a fresh
//!    hash chain rooted at the SHARED checkpoint root (the fork point), so a third party
//!    recomputes each child's head from `(fork_root, that child's turns)` alone. A turn
//!    in one child touches neither the other child's mind (umem heap isolation, from
//!    [`Grain::fork`]) nor its receipt chain.
//!
//! The mind/budget/authority conservation is [`Grain::fork`]'s (proven-composed); this
//! module adds the confinement-attenuation tooth, the budget-split tooth, and the
//! per-fork receipt chain that a confined *session* — not a bare grain — needs.

use std::collections::BTreeSet;

use dregg_cell::CellId;
use hosted_lease::LeaseTerms;

use crate::{Grain, GrainError};

/// The confined body's granted **egress surface** — the `host:port` doors a jailed body
/// may reach, and nothing else. This is what makes a session *confined* rather than a
/// bare grain: the grain models the mind (heap), the budget (lease), and the authority
/// (c-list of [`CellId`] caps), but not the jail's network surface. A fork ATTENUATES
/// it: a child's doors must be a subset of the parent's.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Confinement {
    egress: BTreeSet<String>,
}

impl Confinement {
    /// A confinement granting exactly `doors` (each a `host:port`).
    pub fn new<I, S>(doors: I) -> Confinement
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Confinement {
            egress: doors.into_iter().map(Into::into).collect(),
        }
    }

    /// A fully closed confinement — no egress at all (the default jail floor).
    pub fn closed() -> Confinement {
        Confinement {
            egress: BTreeSet::new(),
        }
    }

    /// Whether the body may reach `door`.
    pub fn allows(&self, door: &str) -> bool {
        self.egress.contains(door)
    }

    /// The granted doors, sorted.
    pub fn doors(&self) -> impl Iterator<Item = &str> {
        self.egress.iter().map(String::as_str)
    }

    /// How many doors are open.
    pub fn len(&self) -> usize {
        self.egress.len()
    }

    /// Whether no door is open.
    pub fn is_empty(&self) -> bool {
        self.egress.is_empty()
    }

    /// Whether `child` is an **attenuation** of `self`: every door the child grants is
    /// one `self` already grants (`child ⊆ self`). The subset check the fork enforces.
    pub fn attenuates(&self, child: &Confinement) -> bool {
        child.egress.is_subset(&self.egress)
    }
}

/// One receipted turn of a confined session: the body's action label and its metered
/// cost. The atomic unit a fork's two lives diverge by.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Turn {
    /// The action the confined body took (e.g. a tool name).
    pub label: String,
    /// The cost the host metered it at (cents).
    pub cost: i64,
}

/// The domain-separated receipt-chain link: `H(prev ‖ label ‖ cost)`. The genesis link
/// of a session's chain is its `chain_root` — the checkpoint root it (or its fork)
/// descends from — so a chain is verifiable back to the shared fork point with nothing
/// but the root and the turns.
fn chain_link(prev: &[u8; 32], turn: &Turn) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("grain-fork-confined-receipt-v1");
    h.update(prev);
    h.update(&(turn.label.len() as u64).to_le_bytes());
    h.update(turn.label.as_bytes());
    h.update(&turn.cost.to_le_bytes());
    *h.finalize().as_bytes()
}

/// Fold a receipt chain from `root` over `turns`, returning the head. A verifier given
/// only the shared fork root and a child's turns recomputes the child's head — no access
/// to the child's live state required.
pub fn fold_receipts(root: [u8; 32], turns: &[Turn]) -> [u8; 32] {
    turns.iter().fold(root, |prev, t| chain_link(&prev, t))
}

/// How to shape one child of a [`ConfinedSession::fork_two`]: its lease, its share of
/// the parent's budget, the caps to confer (⊆ parent-held), and the egress doors to
/// grant (⊆ parent's confinement).
#[derive(Clone, Debug)]
pub struct ForkSpec {
    /// The child's OWN lease terms (own obligor — two forks never share a lease).
    pub terms: LeaseTerms,
    /// This child's share of the parent's budget. The two shares must sum to ≤ the
    /// parent's budget at the checkpoint (the conservation tooth).
    pub budget: i64,
    /// Caps to confer onto the child — each must be one the parent actually holds
    /// ([`Grain::fork`] refuses an unheld one). A fork mints no authority.
    pub confer: Vec<CellId>,
    /// Egress doors to grant the child — each must be one the parent's confinement
    /// already grants. A fork mints no reach.
    pub egress: Vec<String>,
}

impl ForkSpec {
    /// A spec with the given lease + budget, no caps and no egress (the tightest child).
    pub fn new(terms: LeaseTerms, budget: i64) -> ForkSpec {
        ForkSpec {
            terms,
            budget,
            confer: Vec::new(),
            egress: Vec::new(),
        }
    }

    /// Confer these caps onto the child (each must be parent-held).
    pub fn confer(mut self, caps: impl IntoIterator<Item = CellId>) -> ForkSpec {
        self.confer.extend(caps);
        self
    }

    /// Grant these egress doors to the child (each must be in the parent's confinement).
    pub fn egress(mut self, doors: impl IntoIterator<Item = String>) -> ForkSpec {
        self.egress.extend(doors);
        self
    }
}

/// Why a confined-session fork was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfinedForkError {
    /// **Conservation tooth.** The two forks' budgets sum to MORE than the parent had at
    /// the checkpoint — a fork cannot mint budget; the prepaid reserve is split, not
    /// duplicated.
    BudgetOverdraw {
        /// The sum of the requested child budgets.
        requested: i64,
        /// The parent's budget at the checkpoint (the ceiling).
        available: i64,
    },
    /// **Attenuation tooth.** A child asked for an egress door the parent's confinement
    /// does not grant — a fork cannot amplify reach.
    EgressNotAttenuated {
        /// The door that is not in the parent's confinement.
        door: String,
    },
    /// The underlying grain fork refused (an unconferrable cap, a lapsed lease, …).
    Grain(GrainError),
}

impl std::fmt::Display for ConfinedForkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConfinedForkError::BudgetOverdraw {
                requested,
                available,
            } => write!(
                f,
                "fork refused: the forks request {requested} budget but the parent has only {available} (a fork cannot mint budget)"
            ),
            ConfinedForkError::EgressNotAttenuated { door } => write!(
                f,
                "fork refused: egress door `{door}` is not in the parent's confinement (a fork cannot amplify reach)"
            ),
            ConfinedForkError::Grain(e) => write!(f, "fork refused: {e:?}"),
        }
    }
}

impl std::error::Error for ConfinedForkError {}

impl From<GrainError> for ConfinedForkError {
    fn from(e: GrainError) -> Self {
        ConfinedForkError::Grain(e)
    }
}

/// A **forkable confined agent session**: a jailed body's committed mind + prepaid
/// budget + authority (the [`Grain`]) welded to its egress [`Confinement`] and its
/// receipt chain. Checkpoints, and forks into two sovereign lives. See the module docs.
pub struct ConfinedSession {
    grain: Grain,
    confinement: Confinement,
    /// The checkpoint root this session's live receipt chain descends from — its fork
    /// point (or, for a root session, its genesis). The receipt chain's genesis link.
    chain_root: [u8; 32],
    /// The receipted turns since `chain_root`.
    turns: Vec<Turn>,
}

impl ConfinedSession {
    /// **Rent a fresh root confined session** — a fresh grain (own mind + lease funded
    /// to `funding`) behind the `confinement` egress surface. The receipt chain is
    /// rooted at the grain's genesis committed root.
    pub fn rent(
        mind_pk: [u8; 32],
        token: [u8; 32],
        terms: LeaseTerms,
        funding: i64,
        confinement: Confinement,
    ) -> Result<ConfinedSession, GrainError> {
        let grain = Grain::rent(mind_pk, token, terms, funding)?;
        let chain_root = grain.root();
        Ok(ConfinedSession {
            grain,
            confinement,
            chain_root,
            turns: Vec::new(),
        })
    }

    /// Wrap an existing grain as a confined session behind `confinement`. The receipt
    /// chain is rooted at the grain's current committed root.
    pub fn wrap(grain: Grain, confinement: Confinement) -> ConfinedSession {
        let chain_root = grain.root();
        ConfinedSession {
            grain,
            confinement,
            chain_root,
            turns: Vec::new(),
        }
    }

    /// The confined body's committed mind + budget + authority.
    pub fn grain(&self) -> &Grain {
        &self.grain
    }

    /// Mutable access to the grain (to grant caps, meter rent, …).
    pub fn grain_mut(&mut self) -> &mut Grain {
        &mut self.grain
    }

    /// The egress surface the jailed body may reach.
    pub fn confinement(&self) -> &Confinement {
        &self.confinement
    }

    /// The session's remaining prepaid budget — the hosting lease's funded balance (what
    /// a fork's two shares must sum within).
    pub fn budget(&self) -> i64 {
        self.grain.lease().cell().state.balance()
    }

    /// The mind identity (shared across a fork — a fork IS the same mind, diverging).
    pub fn mind_id(&self) -> CellId {
        self.grain.mind_id()
    }

    /// The mind's current committed boundary root.
    pub fn root(&self) -> [u8; 32] {
        self.grain.root()
    }

    /// The checkpoint root this session's receipt chain descends from (its fork point).
    pub fn chain_root(&self) -> [u8; 32] {
        self.chain_root
    }

    /// The receipted turns since the fork point.
    pub fn turns(&self) -> &[Turn] {
        &self.turns
    }

    /// The receipt-chain head — `fold_receipts(chain_root, turns)`. A verifier recomputes
    /// it from the shared fork root and this session's turns alone.
    pub fn receipt_head(&self) -> [u8; 32] {
        fold_receipts(self.chain_root, &self.turns)
    }

    /// **Verify** this session's receipt chain: recompute the head from `chain_root` over
    /// the turns. Always true for an unmutated session — the point is that a third party
    /// can run the SAME fold from the public `(chain_root, turns)` and get `receipt_head`,
    /// with no access to live state.
    pub fn verify_receipt_chain(&self) -> bool {
        fold_receipts(self.chain_root, &self.turns) == self.receipt_head()
    }

    /// **Record a confined turn** — the jailed body wrote `value` at working-memory `key`
    /// and the host receipted it at `cost`. Writes BOTH the mind (grain state) and the
    /// receipt chain. This is the atomic unit two forked lives diverge by: a turn in one
    /// touches neither the other's mind (umem heap isolation) nor its receipt chain.
    pub fn record_turn(&mut self, key: u32, value: [u8; 32], label: impl Into<String>, cost: i64) {
        self.grain.learn(key, value);
        self.turns.push(Turn {
            label: label.into(),
            cost,
        });
    }

    /// Read a working-memory value the confined body wrote.
    pub fn recall(&self, key: u32) -> Option<[u8; 32]> {
        self.grain.recall(key)
    }

    /// **Checkpoint** the session — commit the mind's state to the timeline + advance the
    /// lease cursor (delegates to [`Grain::checkpoint`]). Returns the committed root. The
    /// receipt chain continues across a checkpoint; a FORK is where two chains diverge.
    pub fn checkpoint(&mut self) -> Result<[u8; 32], GrainError> {
        self.grain.checkpoint()
    }

    /// **Fork into two sovereign lives** — the umem "scale IS fork" superpower on a live
    /// confined session. Checkpoints the parent (the shared fork point), then splits it
    /// into two independent confined sessions per `spec_a` / `spec_b`. Fail-closed on any
    /// tooth, leaving nothing minted:
    ///
    /// * **Budget conservation** — `spec_a.budget + spec_b.budget` must be ≤ the parent's
    ///   budget at the checkpoint, else [`ConfinedForkError::BudgetOverdraw`].
    /// * **Egress attenuation** — every door each spec grants must be in the parent's
    ///   confinement, else [`ConfinedForkError::EgressNotAttenuated`].
    /// * **Authority attenuation** — each conferred cap must be parent-held (the
    ///   underlying [`Grain::fork`]'s [`GrainError::UnconferrableCap`]).
    ///
    /// Each child's receipt chain is rooted at the SHARED checkpoint root, so both lives
    /// descend verifiably from one fork point. Consuming `self` is deliberate: the parent
    /// checkpoint becomes the fork point and the two children ARE the two lives.
    pub fn fork_two(
        mut self,
        spec_a: ForkSpec,
        spec_b: ForkSpec,
    ) -> Result<(ConfinedSession, ConfinedSession), ConfinedForkError> {
        // Commit the fork point first, so both children descend from a real checkpoint.
        let fork_root = self.grain.checkpoint()?;

        // Conservation tooth: the two shares cannot exceed what the parent had. Checked on
        // the SUM (saturating, so a hostile i64 overflow can never wrap under the ceiling).
        let available = self.budget();
        let requested = spec_a.budget.saturating_add(spec_b.budget);
        if requested > available {
            return Err(ConfinedForkError::BudgetOverdraw {
                requested,
                available,
            });
        }

        // Attenuation + spawn each child from the SAME committed parent grain. `build_child`
        // enforces egress ⊆ parent; `Grain::fork` enforces caps ⊆ parent-held.
        let child_a = self.build_child(fork_root, &spec_a)?;
        let child_b = self.build_child(fork_root, &spec_b)?;
        Ok((child_a, child_b))
    }

    /// Fork a SINGLE attenuated child (own lease, own confinement, receipt chain rooted at
    /// the parent's checkpoint). Its budget must not exceed the parent's, and its egress +
    /// caps must attenuate the parent's. Unlike [`fork_two`](ConfinedSession::fork_two)
    /// this borrows the parent (it survives as the other live session).
    pub fn fork(&mut self, spec: ForkSpec) -> Result<ConfinedSession, ConfinedForkError> {
        let fork_root = self.grain.checkpoint()?;
        if spec.budget > self.budget() {
            return Err(ConfinedForkError::BudgetOverdraw {
                requested: spec.budget,
                available: self.budget(),
            });
        }
        self.build_child(fork_root, &spec)
    }

    /// Spawn one attenuated child from this (already-checkpointed) parent grain at
    /// `fork_root`. Enforces egress attenuation here; delegates cap attenuation + the
    /// no-value-minted mind copy to [`Grain::fork`].
    fn build_child(
        &self,
        fork_root: [u8; 32],
        spec: &ForkSpec,
    ) -> Result<ConfinedSession, ConfinedForkError> {
        // Egress attenuation tooth: refuse any door the parent does not already grant.
        let child_conf = Confinement::new(spec.egress.iter().cloned());
        if !self.confinement.attenuates(&child_conf) {
            let door = spec
                .egress
                .iter()
                .find(|d| !self.confinement.allows(d))
                .cloned()
                .unwrap_or_default();
            return Err(ConfinedForkError::EgressNotAttenuated { door });
        }
        // Grain::fork copies the committed mind (no value minted), opens the child's OWN
        // lease funded to its budget share, and confers ONLY caps the parent holds.
        let child_grain = self
            .grain
            .fork(spec.terms.clone(), spec.budget, &spec.confer)?;
        Ok(ConfinedSession {
            grain: child_grain,
            confinement: child_conf,
            // The child's receipt chain is rooted at the SHARED fork point.
            chain_root: fork_root,
            turns: Vec::new(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    /// provider, lease-cell, asset; rent 100 every 50 blocks from 1000.
    fn terms(lease: u8) -> LeaseTerms {
        LeaseTerms::new(cid(2), cid(lease), cid(9), 100, 50, 1000, 0)
    }

    /// A root confined session with a two-door egress surface and a 1_000_000 budget.
    fn parent_session() -> ConfinedSession {
        ConfinedSession::rent(
            [0xA0; 32],
            [0x01; 32],
            terms(7),
            1_000_000,
            Confinement::new(["api.openai.com:443", "index.crates.io:443"]),
        )
        .expect("rent a root confined session")
    }

    /// THE HEADLINE — checkpoint → fork into two → each sovereign, isolated, verifiable,
    /// with budget SPLIT not duplicated.
    #[test]
    fn checkpoint_fork_two_sovereign_isolated_verifiable_sessions() {
        let mut parent = parent_session();
        // The confined body does some work, then the session is checkpointed.
        parent.record_turn(0, [0x11; 32], "read_docs", 100);
        let fork_root = parent
            .checkpoint()
            .expect("checkpoint the confined session");
        let parent_budget = parent.budget();

        // Fork into two lives. A keeps only the openai door; B keeps only crates.io. The
        // budgets SPLIT (400k + 600k = 1M = the parent's budget), neither amplifies reach.
        let (mut a, mut b) = parent
            .fork_two(
                ForkSpec::new(terms(70), 400_000).egress(["api.openai.com:443".into()]),
                ForkSpec::new(terms(71), 600_000).egress(["index.crates.io:443".into()]),
            )
            .expect("fork the confined session into two");

        // ── SOVEREIGN: distinct obligors, distinct confinements, SAME mind identity. ──
        assert_ne!(a.grain().obligor(), b.grain().obligor(), "own leases");
        assert_eq!(
            a.mind_id(),
            b.mind_id(),
            "a fork IS the same mind, diverging"
        );
        assert!(a.confinement().allows("api.openai.com:443"));
        assert!(
            !a.confinement().allows("index.crates.io:443"),
            "A did not keep B's door"
        );
        assert!(b.confinement().allows("index.crates.io:443"));
        assert!(
            !b.confinement().allows("api.openai.com:443"),
            "B did not keep A's door"
        );

        // Both descend from the shared fork point + carry the pre-fork learning.
        assert_eq!(a.chain_root(), fork_root);
        assert_eq!(b.chain_root(), fork_root);
        assert_eq!(a.recall(0), Some([0x11; 32]));
        assert_eq!(b.recall(0), Some([0x11; 32]));

        // ── ISOLATION: a turn in A touches neither B's mind nor B's receipt chain. ──
        let a_head_before = a.receipt_head();
        let b_head_before = b.receipt_head();
        assert_eq!(a_head_before, b_head_before, "identical at the fork point");
        a.record_turn(1, [0xAA; 32], "a_writes", 250);
        assert_eq!(a.recall(1), Some([0xAA; 32]));
        assert_eq!(
            b.recall(1),
            None,
            "A's write never touches B's mind (umem isolation)"
        );
        assert_ne!(
            a.receipt_head(),
            a_head_before,
            "A's receipt chain advanced"
        );
        assert_eq!(
            b.receipt_head(),
            b_head_before,
            "B's receipt chain is untouched"
        );
        // And the reverse.
        b.record_turn(2, [0xBB; 32], "b_writes", 250);
        assert_eq!(b.recall(2), Some([0xBB; 32]));
        assert_eq!(a.recall(2), None, "B's write never touches A's mind");
        assert_ne!(a.receipt_head(), b.receipt_head(), "the two lives diverged");

        // ── INDEPENDENTLY VERIFIABLE: a third party recomputes each head from the shared
        //    fork root + that child's turns alone. ──
        assert_eq!(a.receipt_head(), fold_receipts(fork_root, a.turns()));
        assert_eq!(b.receipt_head(), fold_receipts(fork_root, b.turns()));
        assert!(a.verify_receipt_chain() && b.verify_receipt_chain());

        // ── BUDGET SPLIT, not duplicated: the shares sum to the parent's budget. ──
        assert_eq!(a.budget(), 400_000);
        assert_eq!(b.budget(), 600_000);
        assert_eq!(
            a.budget() + b.budget(),
            parent_budget,
            "conserved, not minted"
        );
    }

    /// CONSERVATION TOOTH — the two shares cannot sum past the parent's budget: a fork
    /// cannot mint budget.
    #[test]
    fn fork_cannot_mint_budget() {
        let mut parent = parent_session();
        parent.checkpoint().unwrap();
        let budget = parent.budget();

        // 600k + 600k = 1.2M > the parent's 1M — refused, nothing minted.
        match parent.fork_two(
            ForkSpec::new(terms(70), 600_000),
            ForkSpec::new(terms(71), 600_000),
        ) {
            Err(ConfinedForkError::BudgetOverdraw {
                requested,
                available,
            }) => {
                assert_eq!(requested, 1_200_000);
                assert_eq!(available, budget);
            }
            other => panic!("a budget-minting fork was NOT refused: {:?}", other.is_ok()),
        }
    }

    /// A split summing to EXACTLY the budget is allowed (the tooth is `>`, not over-broad).
    #[test]
    fn an_exact_split_is_allowed() {
        let mut parent = parent_session();
        parent.checkpoint().unwrap();
        let budget = parent.budget();
        let (a, b) = parent
            .fork_two(
                ForkSpec::new(terms(70), budget / 2),
                ForkSpec::new(terms(71), budget - budget / 2),
            )
            .expect("an exact split forks fine");
        assert_eq!(a.budget() + b.budget(), budget);
    }

    /// ATTENUATION TOOTH (egress) — a child cannot open a door the parent's confinement
    /// does not grant: a fork cannot amplify reach.
    #[test]
    fn fork_cannot_amplify_egress() {
        let mut parent = parent_session();
        parent.checkpoint().unwrap();

        match parent.fork_two(
            ForkSpec::new(terms(70), 100).egress(["evil.example.com:443".into()]),
            ForkSpec::new(terms(71), 100),
        ) {
            Err(ConfinedForkError::EgressNotAttenuated { door }) => {
                assert_eq!(door, "evil.example.com:443");
            }
            other => panic!(
                "an egress-amplifying fork was NOT refused: {:?}",
                other.is_ok()
            ),
        }
    }

    /// ATTENUATION TOOTH (authority) — conferring a cap the parent does not hold is
    /// refused by the underlying grain fork: a fork mints no authority.
    #[test]
    fn fork_cannot_mint_authority() {
        let mut parent = parent_session();
        let held = cid(0x91);
        let unheld = cid(0xEE);
        parent.grain_mut().grant(held);
        parent.checkpoint().unwrap();

        // Conferring the unheld cap is refused (surfaced as a Grain error).
        match parent.fork(ForkSpec::new(terms(70), 100).confer([unheld])) {
            Err(ConfinedForkError::Grain(GrainError::UnconferrableCap(t))) => {
                assert_eq!(t, unheld)
            }
            other => panic!("a cap-minting fork was NOT refused: {:?}", other.is_ok()),
        }

        // Conferring the HELD cap forks fine, and the child holds exactly it.
        let child = parent
            .fork(ForkSpec::new(terms(70), 100).confer([held]))
            .expect("conferring a held cap forks");
        assert!(child.grain().holds(held));
        assert!(!child.grain().holds(unheld));
    }

    /// The egress attenuation is not over-broad: a child keeping a SUBSET of the parent's
    /// doors forks fine.
    #[test]
    fn a_subset_of_doors_attenuates() {
        let mut parent = parent_session();
        parent.checkpoint().unwrap();
        let child = parent
            .fork(ForkSpec::new(terms(70), 100).egress(["api.openai.com:443".into()]))
            .expect("a subset of doors is an attenuation");
        assert!(child.confinement().allows("api.openai.com:443"));
        assert_eq!(child.confinement().len(), 1);
    }

    /// A confined body's receipt chain binds label AND cost — tampering with either is
    /// detectable by a re-fold (the chain is not a bare count).
    #[test]
    fn the_receipt_chain_binds_label_and_cost() {
        let genesis = [0x07; 32];
        let honest = [
            Turn {
                label: "a".into(),
                cost: 100,
            },
            Turn {
                label: "b".into(),
                cost: 200,
            },
        ];
        let head = fold_receipts(genesis, &honest);

        // Change the cost of one turn → a different head.
        let tampered_cost = [
            Turn {
                label: "a".into(),
                cost: 100,
            },
            Turn {
                label: "b".into(),
                cost: 999,
            },
        ];
        assert_ne!(fold_receipts(genesis, &tampered_cost), head);

        // Change the label of one turn → a different head.
        let tampered_label = [
            Turn {
                label: "a".into(),
                cost: 100,
            },
            Turn {
                label: "c".into(),
                cost: 200,
            },
        ];
        assert_ne!(fold_receipts(genesis, &tampered_label), head);

        // A different fork root → a different head (the chain is bound to its fork point).
        assert_ne!(fold_receipts([0x08; 32], &honest), head);
    }
}
