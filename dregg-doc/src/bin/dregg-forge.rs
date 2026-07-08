//! `dregg-forge` — the command-line face of the dregg-native code forge
//! (docs/deos/DREGG-FORGE.md).
//!
//! The forge core lives in `dregg-doc`: a [`PullRequest`] is a fork offered
//! against a base, `merge` is the categorical pushout (conflicts are OBJECTS,
//! not failures), landing drives cap-gated finalized turns through the real
//! executor, and CI is receipted turns (the proof IS the pass — no trusted
//! runner). This binary gives that core a terminal.
//!
//! THE DREGGIC PROPERTY: every forge command is a CAP-GATED RECEIPTED TURN, not
//! a mutation. `dregg-forge land` IS a verified turn that leaves a receipt,
//! refused in-band if you do not hold the merge cap. This is `git` with no
//! server that can lie to you.
//!
//! Needs the executor substrate: build/run with `--features substrate`. Without
//! it the binary still compiles (and says so).
//!
//! Named follow-up (live-repo wiring): every scenario below operates on an
//! in-memory demo forge (`ExecutorDrivenDoc::new_at` over a hand-built
//! `History`). Operating on a real `DocHeapCell` / a `cell_git` working tree —
//! so `dregg-forge` drives an on-disk repository instead of the demo — is the
//! next slice.

#[cfg(not(feature = "substrate"))]
fn main() {
    eprintln!("dregg-forge is the executor-driven forge CLI — it needs the substrate.");
    eprintln!("build with:  cargo run --bin dregg-forge --features substrate -- demo");
}

#[cfg(feature = "substrate")]
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    forge::run(&args);
}

#[cfg(feature = "substrate")]
mod forge {
    use dregg_doc::{
        AtomId, Author, CheckWitness, ExecutorDrivenDoc, History, Op, Patch, PatchId, PullRequest,
        PullRequestError, content,
    };
    use dregg_turn::{TurnError, TurnReceipt};

    /// RFC 8032 §7.1 TEST 1 Ed25519 (seed, verifying-key) pair — the same real
    /// pair the crate's CI-gate tests use. Stands in for the forge's TRUSTED
    /// EXECUTOR KEY (repo policy in the real forge): the executor derives this
    /// verifying key from this 32-byte seed by standard Ed25519 key generation,
    /// so a receipt this seed signs verifies against this key.
    pub const CI_SIGNING_SEED: [u8; 32] = [
        0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c,
        0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae,
        0x7f, 0x60,
    ];
    pub const CI_VERIFYING_KEY: [u8; 32] = [
        0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07,
        0x3a, 0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07,
        0x51, 0x1a,
    ];

    // ── the entry point ─────────────────────────────────────────────────────

    pub fn run(args: &[String]) {
        let cmd = args.first().map(String::as_str).unwrap_or("demo");
        let non_holder = args.iter().any(|a| a == "--as-non-holder");
        match cmd {
            "demo" => demo(),
            "status" => status(),
            "diff" => diff(),
            "review" => review(),
            "land" => land_cmd(!non_holder),
            "comment" => {
                let text = args
                    .iter()
                    .skip(1)
                    .find(|a| !a.starts_with("--"))
                    .cloned()
                    .unwrap_or_else(|| "looks good to me".to_string());
                comment_cmd(!non_holder, &text);
            }
            "help" | "-h" | "--help" => usage(),
            other => {
                eprintln!("dregg-forge: unknown subcommand `{other}`\n");
                usage();
            }
        }
    }

    fn usage() {
        println!("dregg-forge — the terminal face of the dregg-native code forge");
        println!();
        println!("USAGE: dregg-forge <command> [flags]");
        println!();
        println!("COMMANDS:");
        println!(
            "  demo                  the flagship: the whole cap-gated + receipted forge loop"
        );
        println!("  status                the merge gate (clean / N conflicts) for the demo PRs");
        println!(
            "  diff                  the three-way diff (conflicts rendered against the base)"
        );
        println!(
            "  review                post a comment + an approval as receipted turns; read the thread"
        );
        println!(
            "  land [--as-non-holder]     land the demo PR (cap-gated); --as-non-holder shows the in-band refusal"
        );
        println!(
            "  comment [text] [--as-non-holder]   post a review comment; --as-non-holder shows the in-band refusal"
        );
        println!();
        println!(
            "Every mutating verb is a turn: cap-gated, receipted, refused in-band without the cap."
        );
    }

    // ── scenario builders (a base doc + a fork) ─────────────────────────────

    /// A shared two-atom history ("one\n" then "two\n") — the base doc both
    /// forks diverge from.
    fn shared_history() -> (History, AtomId, AtomId) {
        let mut h = History::new();
        let (s1, op1) = Patch::add(1, "one\n", AtomId::ROOT);
        let (s2, op2) = Patch::add(2, "two\n", s1);
        h.commit(Patch::by(Author(0), [op1]));
        h.commit(Patch::by(Author(0), [op2]));
        (h, s1, s2)
    }

    /// A CLEAN PR: base tombstones "one\n", head appends "three\n" — disjoint,
    /// non-conflicting edits on a shared ancestor.
    pub fn clean_pr() -> PullRequest {
        let (shared, s1, s2) = shared_history();
        let mut base = shared.branch();
        base.commit(Patch::by(Author(1), [Op::Delete { id: s1 }]));
        let mut head = shared.branch();
        head.commit(Patch::by(Author(2), [Patch::add(3, "three\n", s2).1]));
        PullRequest::open(base, head)
    }

    /// A CONFLICTING PR: base and head each insert a different line after the
    /// same anchor — a genuine antichain (a pushout with a live conflict object).
    pub fn conflicting_pr() -> PullRequest {
        let (shared, _s1, s2) = shared_history();
        let mut base = shared.branch();
        base.commit(Patch::by(Author(1), [Patch::add(10, "alpha\n", s2).1]));
        let mut head = shared.branch();
        head.commit(Patch::by(Author(2), [Patch::add(11, "beta\n", s2).1]));
        PullRequest::open(base, head)
    }

    /// A thread/CI backing document whose executor SIGNS its receipts (the
    /// non-fabricable part of a committed-receipt witness), holding its region
    /// cap.
    pub fn signing_thread_doc() -> ExecutorDrivenDoc {
        let mut doc = ExecutorDrivenDoc::new(7, 8, true);
        doc.set_receipt_signing_key(CI_SIGNING_SEED);
        doc
    }

    /// The provenance [`Author`] BOUND to an executor-authenticated editor cell
    /// — a comment/approval MUST claim exactly this author or the review post is
    /// refused with `InvalidAuthorization` (blame is non-forgeable).
    ///
    /// This mirrors `dregg_doc::review::author_of_editor`, which is `pub` but not
    /// re-exported from the crate root (the `review` module is private) — so an
    /// external consumer cannot reach it today. Re-exporting it (plus an
    /// `ExecutorDrivenDoc::bound_author()` convenience) is the named follow-up;
    /// the fold itself is stable and documented, so the CLI reproduces it.
    pub fn bound_author(doc: &ExecutorDrivenDoc) -> Author {
        let mut acc: u64 = 0x9E37_79B9_7F4A_7C15;
        for chunk in doc.editor_id().as_bytes().chunks_exact(8) {
            let w = u64::from_le_bytes(chunk.try_into().unwrap());
            acc ^= w;
            acc = acc.wrapping_mul(0xBF58_476D_1CE4_E5B9);
            acc ^= acc >> 31;
        }
        Author(acc)
    }

    // ── the reusable flow (shared by the CLI verbs AND the tests) ───────────

    /// Land the clean PR with (or without) the merge cap, carrying NO checks —
    /// isolates the executor's cap gate. Returns the land result plus the
    /// document commitment before/after (for the receipt-less assertion: a
    /// refused land leaves the commitment untouched).
    pub fn land_plain(
        hold_cap: bool,
    ) -> (
        Result<Vec<TurnReceipt>, PullRequestError>,
        [u8; 32],
        [u8; 32],
    ) {
        let pr = clean_pr();
        let mut doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, hold_cap);
        let pre = doc.state_commitment();
        let result = pr.land(&mut doc);
        let post = doc.state_commitment();
        (result, pre, post)
    }

    /// The full checked-and-approved landing flow: open the clean PR, post a
    /// comment + an approval (receipted turns), bind the merge to an
    /// approval-as-required-check, then attempt to land it — first WITHOUT the
    /// witness (the check gate refuses, untouched), then WITH it.
    ///
    /// `hold_cap` controls the merger's edit cap on the base region: `true`
    /// lands as finalized cap-gated turns; `false` shows the in-band cap refusal
    /// AFTER the check is satisfied (checks and caps are independent gates).
    pub struct DemoRun {
        pub comment: TurnReceipt,
        pub approval: TurnReceipt,
        /// `Some((check, reason))` — the land refusal while no witness was
        /// presented (the CI gate, before any merge turn).
        pub refused_without_witness: Option<(String, String)>,
        pub land: Result<Vec<TurnReceipt>, PullRequestError>,
        pub pre_commitment: [u8; 32],
        pub post_commitment: [u8; 32],
        pub landed_content: String,
        pub projection_ok: bool,
    }

    pub fn run_checked_land(hold_cap: bool) -> DemoRun {
        let mut pr = clean_pr();
        let mut thread_doc = signing_thread_doc();
        let reviewer = bound_author(&thread_doc);

        // Review = receipted turns: a comment, then an approval.
        let comment = pr
            .comment(&mut thread_doc, reviewer, "LGTM — both edits are disjoint")
            .expect("a cap-holding reviewer's comment lands");

        // CI AS RECEIPTED TURNS: require an approval, bound to the EXACT approval
        // turn the reviewer is about to post (named before it runs).
        let check = pr
            .review()
            .planned_approval_check(&thread_doc, "approved", vec![CI_VERIFYING_KEY])
            .expect("the approval turn has a projection delta");
        pr = pr.with_required_check(check);
        let approval = pr
            .approve(&mut thread_doc, reviewer)
            .expect("the approval posts");

        // Land against the base document (the merger is this doc's editor).
        let mut land_doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, hold_cap);
        let pre = land_doc.state_commitment();

        // POLE 1: no witness → the check gate refuses BEFORE any merge turn.
        let refused_without_witness = match pr.land(&mut land_doc) {
            Err(PullRequestError::CheckNotSatisfied { check, reason }) => {
                Some((check.as_str().to_string(), format!("{reason:?}")))
            }
            _ => None,
        };

        // POLE 2: present the committed, signed approval receipt → it verifies.
        pr.present_witness("approved", CheckWitness::Receipt(approval.clone()));
        let land = pr.land(&mut land_doc);
        let post = land_doc.state_commitment();

        DemoRun {
            comment,
            approval,
            refused_without_witness,
            land,
            pre_commitment: pre,
            post_commitment: post,
            landed_content: content(land_doc.graph()).to_marked_string(),
            projection_ok: land_doc.commitment_matches_projection(),
        }
    }

    // ── the CLI verbs ───────────────────────────────────────────────────────

    fn demo() {
        banner(
            "dregg-forge demo — a cap-gated, receipted forge loop (git with no server that can lie)",
        );

        // 1. open a pull request.
        section("1. open a pull request  (a forked head offered against a base)");
        let pr = clean_pr();
        println!("   base:  tombstones \"one\\n\"      head: appends \"three\\n\"");
        print_diff(&pr);
        print_gate(&pr);
        println!(
            "   merged preview: {:?}",
            content(&pr.merged_graph()).to_marked_string()
        );

        // 2. merge is a pushout — conflicts are objects.
        section("2. merge is a pushout — a conflict is a first-class OBJECT, not a failure");
        let mut cpr = conflicting_pr();
        println!("   a rival PR inserts a different line at the SAME anchor:");
        print_diff(&cpr);
        print_gate(&cpr);
        if let Err(PullRequestError::UnresolvedConflict(cs)) = cpr.merge() {
            println!(
                "   merge() REFUSED: {} unresolved conflict(s) — the merge carries it as a state",
                cs.len()
            );
        }
        let menu = cpr.resolution_choices(Author(3));
        let order = menu[0]
            .choices
            .iter()
            .find(|c| c.keeps_all())
            .expect("a keep-both order choice")
            .clone();
        let rid = cpr.resolve(&order);
        println!(
            "   reviewer resolves (keep-both order) → resolution patch {}",
            short_pid(&rid)
        );
        print_gate(&cpr);

        // 3–5. the receipted, cap-gated, checked land.
        let run = run_checked_land(true);

        section("3. review is receipted turns — comment + approval leave SIGNED receipts");
        println!(
            "   comment  turn={} receipt={} finality={:?}",
            short(&run.comment.turn_hash),
            short(&run.comment.receipt_hash()),
            run.comment.finality
        );
        println!(
            "   approval turn={} receipt={} finality={:?} signed={}",
            short(&run.approval.turn_hash),
            short(&run.approval.receipt_hash()),
            run.approval.finality,
            run.approval.executor_signature.is_some()
        );
        println!("   the PR now requires check \"approved\" — bound to that exact approval turn");

        section("4. no trusted CI — the check gates the merge  (the proof IS the pass)");
        match &run.refused_without_witness {
            Some((check, reason)) => println!(
                "   land REFUSED: check \"{check}\" unsatisfied ({reason}) — ledger byte-untouched",
            ),
            None => println!("   (unexpected: the check did not refuse without a witness)"),
        }
        println!("   present the committed, signed approval receipt as the witness → verified");

        section("5. land — cap-gated FINALIZED turns, receipt-chained");
        match &run.land {
            Ok(receipts) => {
                for (i, r) in receipts.iter().enumerate() {
                    println!(
                        "   turn #{}: turn={} receipt={} finality={:?} prev={}",
                        i + 1,
                        short(&r.turn_hash),
                        short(&r.receipt_hash()),
                        r.finality,
                        r.previous_receipt_hash
                            .map(|h| short(&h))
                            .unwrap_or_else(|| "genesis".to_string()),
                    );
                }
                println!("   landed content: {:?}", run.landed_content);
                println!(
                    "   commitment moved: {}   projection-consistent: {}",
                    run.pre_commitment != run.post_commitment,
                    run.projection_ok
                );
            }
            Err(e) => println!("   (unexpected land refusal: {e:?})"),
        }

        // 6. cap-gating is real — a non-holder is refused in-band, receipt-less.
        section("6. cap-gating is REAL — a non-holder is refused in-band (no receipt)");
        let (result, pre, post) = land_plain(false);
        match result {
            Err(PullRequestError::Refused(TurnError::CapabilityNotHeld { actor, target })) => {
                println!("   land REFUSED in-band: CapabilityNotHeld");
                println!(
                    "       actor={} holds no edit cap on region={}",
                    short(actor.as_bytes()),
                    short(target.as_bytes())
                );
                println!(
                    "       receipts produced: 0    commitment untouched: {}",
                    pre == post
                );
            }
            other => println!("   (unexpected: {other:?})"),
        }

        println!();
        println!(
            "   every verb was a turn: cap-gated (refusal is real), receipted (hashes above),"
        );
        println!(
            "   merge = pushout (conflicts were objects), no trusted CI (the proof was the pass)."
        );
    }

    fn status() {
        banner("dregg-forge status — the merge gate for the demo PRs");
        section("clean PR (base tombstones \"one\", head appends \"three\")");
        let pr = clean_pr();
        print_diff(&pr);
        print_gate(&pr);
        section("conflicting PR (base + head insert different lines at one anchor)");
        let cpr = conflicting_pr();
        print_diff(&cpr);
        print_gate(&cpr);
        println!();
        println!(
            "a required check would add `awaiting checks` to the gate — see `dregg-forge demo`."
        );
    }

    fn diff() {
        banner(
            "dregg-forge diff — the three-way (diff3) view, conflicts rendered against the base",
        );
        section("clean PR — no conflicts, both edits compose");
        let pr = clean_pr();
        print_diff(&pr);
        println!(
            "   merged: {:?}",
            content(&pr.merged_graph()).to_marked_string()
        );
        section("conflicting PR — each conflict region shows its BASE column + every side");
        let cpr = conflicting_pr();
        print_diff(&cpr);
    }

    fn review() {
        banner("dregg-forge review — comments + approvals as OWNED, receipted document atoms");
        let mut pr = clean_pr();
        let mut thread_doc = signing_thread_doc();
        let who = bound_author(&thread_doc);
        let c1 = pr
            .comment(&mut thread_doc, who, "needs a test for the delete path")
            .expect("comment lands");
        let c2 = pr
            .comment(&mut thread_doc, who, "test added — LGTM")
            .expect("comment lands");
        let a = pr.approve(&mut thread_doc, who).expect("approval lands");
        println!(
            "   comment #1 receipt={} finality={:?}",
            short(&c1.receipt_hash()),
            c1.finality
        );
        println!(
            "   comment #2 receipt={} prev={}",
            short(&c2.receipt_hash()),
            short(&c2.previous_receipt_hash.unwrap())
        );
        println!(
            "   approval   receipt={} signed={}",
            short(&a.receipt_hash()),
            a.executor_signature.is_some()
        );
        section("the thread, read back off the committed atoms (attributable by blame)");
        for (i, cm) in pr.review().comments(&thread_doc).iter().enumerate() {
            println!(
                "   comment #{} by author {}: {:?}",
                i + 1,
                cm.author.0,
                cm.text
            );
        }
        println!("   approvals: {}", pr.review().approval_count(&thread_doc));
        println!();
        println!(
            "blame is BOUND to the authenticated editor — a forged author is refused before any turn."
        );
    }

    fn land_cmd(hold_cap: bool) {
        banner(
            "dregg-forge land — the merge as cap-gated finalized turns through the real executor",
        );
        let run = run_checked_land(hold_cap);
        println!(
            "   review: comment receipt={}  approval receipt={} (signed={})",
            short(&run.comment.receipt_hash()),
            short(&run.approval.receipt_hash()),
            run.approval.executor_signature.is_some()
        );
        if let Some((check, reason)) = &run.refused_without_witness {
            println!("   check \"{check}\" refused the land until witnessed ({reason})");
        }
        match run.land {
            Ok(receipts) => {
                println!(
                    "   LANDED as {} finalized, receipt-chained turn(s):",
                    receipts.len()
                );
                for (i, r) in receipts.iter().enumerate() {
                    println!(
                        "     turn #{}: receipt={} finality={:?}",
                        i + 1,
                        short(&r.receipt_hash()),
                        r.finality
                    );
                }
                println!("   content: {:?}", run.landed_content);
            }
            Err(PullRequestError::Refused(TurnError::CapabilityNotHeld { actor, target })) => {
                println!("   REFUSED in-band (no merge cap): CapabilityNotHeld");
                println!(
                    "     actor={} region={}  commitment untouched: {}",
                    short(actor.as_bytes()),
                    short(target.as_bytes()),
                    run.pre_commitment == run.post_commitment
                );
                println!(
                    "     receipts produced: 0  (the land left NO receipt — nothing happened)"
                );
            }
            Err(e) => println!("   refused: {e:?}"),
        }
    }

    fn comment_cmd(hold_cap: bool, text: &str) {
        banner("dregg-forge comment — a review comment as a cap-gated receipted turn");
        let mut pr = clean_pr();
        let mut doc = signing_thread_doc_with_cap(hold_cap);
        let who = bound_author(&doc);
        let pre = doc.state_commitment();
        match pr.comment(&mut doc, who, text) {
            Ok(r) => {
                println!("   comment LANDED: {text:?}");
                println!(
                    "     turn={} receipt={} finality={:?} signed={}",
                    short(&r.turn_hash),
                    short(&r.receipt_hash()),
                    r.finality,
                    r.executor_signature.is_some()
                );
            }
            Err(TurnError::CapabilityNotHeld { actor, target }) => {
                println!("   REFUSED in-band (no review cap): CapabilityNotHeld");
                println!(
                    "     actor={} region={}  thread untouched: {}",
                    short(actor.as_bytes()),
                    short(target.as_bytes()),
                    pre == doc.state_commitment()
                );
                println!("     receipts produced: 0  (a comment you cannot own does not land)");
            }
            Err(e) => println!("   refused: {e:?}"),
        }
    }

    fn signing_thread_doc_with_cap(hold_cap: bool) -> ExecutorDrivenDoc {
        let mut doc = ExecutorDrivenDoc::new(1, 2, hold_cap);
        doc.set_receipt_signing_key(CI_SIGNING_SEED);
        doc
    }

    // ── printing helpers ────────────────────────────────────────────────────

    fn banner(title: &str) {
        println!("┌─ {title}");
    }

    fn section(title: &str) {
        println!();
        println!("── {title}");
    }

    /// The divergence + any conflict regions (three-way rendered).
    fn print_diff(pr: &PullRequest) {
        let (base_suffix, head_suffix) = pr.divergence();
        println!(
            "   merge-base: {} patch(es)   base +{}   head +{}",
            pr.merge_base().len(),
            base_suffix.len(),
            head_suffix.len()
        );
        for (i, c) in pr.conflicts().iter().enumerate() {
            let base_col = if c.base_text.is_empty() {
                "∅ (pure concurrent insert)".to_string()
            } else {
                format!("{:?}", c.base_text)
            };
            println!("   conflict #{}: base={}", i + 1, base_col);
            for s in &c.sides {
                println!(
                    "       side by author {}: {:?}",
                    s.author.0,
                    s.text.trim_end_matches('\n')
                );
            }
        }
    }

    fn print_gate(pr: &PullRequest) {
        if pr.is_clean() {
            println!("   merge gate: CLEAN (0 conflicts) — mergeable");
        } else {
            println!(
                "   merge gate: BLOCKED — {} conflict(s) outstanding (resolve to merge)",
                pr.conflicts().len()
            );
        }
    }

    /// First 6 bytes of a 32-byte hash, hex — enough to eyeball, full value is
    /// in the receipt.
    fn short(bytes: &[u8]) -> String {
        let n = bytes.len().min(6);
        let hex: String = bytes[..n].iter().map(|b| format!("{b:02x}")).collect();
        format!("{hex}…")
    }

    fn short_pid(pid: &PatchId) -> String {
        format!("{:016x}…", pid.0 as u64)
    }
}

// ── the demo flow, asserted programmatically ────────────────────────────────

#[cfg(all(test, feature = "substrate"))]
mod tests {
    use super::forge::*;
    use dregg_doc::{Author, PullRequestError};
    use dregg_turn::TurnError;

    /// The clean-PR demo lands with receipts, and the merge moves the document
    /// commitment (a real finalized turn was driven).
    #[test]
    fn clean_pr_lands_with_receipts() {
        let (result, pre, post) = land_plain(/* hold_cap */ true);
        let receipts = result.expect("a cap-holding merger lands");
        assert!(!receipts.is_empty(), "the land produced receipts");
        assert_ne!(pre, post, "the merge moved the commitment");
    }

    /// The conflict demo refuses-until-resolved: `merge()` is refused while the
    /// antichain stands; a review resolution settles it; then it merges.
    #[test]
    fn conflict_demo_refuses_until_resolved() {
        let mut pr = conflicting_pr();
        assert!(!pr.is_clean(), "the PR carries a live conflict object");
        match pr.merge() {
            Err(PullRequestError::UnresolvedConflict(cs)) => assert_eq!(cs.len(), 1),
            other => panic!("expected UnresolvedConflict, got {other:?}"),
        }
        // Review is resolution: take the keep-both order choice off the menu.
        let menu = pr.resolution_choices(Author(3));
        let order = menu[0]
            .choices
            .iter()
            .find(|c| c.keeps_all())
            .expect("a keep-both order choice")
            .clone();
        pr.resolve(&order);
        assert!(pr.is_clean(), "the resolution settled the conflict");
        pr.merge().expect("a resolved PR merges");
    }

    /// The non-holder refusal is IN-BAND (a Result error, not a panic) and
    /// RECEIPT-LESS (nothing landed — the commitment is untouched).
    #[test]
    fn non_holder_refusal_is_in_band_and_receiptless() {
        let (result, pre, post) = land_plain(/* hold_cap */ false);
        match result {
            Err(PullRequestError::Refused(TurnError::CapabilityNotHeld { .. })) => {}
            other => panic!("expected an in-band CapabilityNotHeld refusal, got {other:?}"),
        }
        assert_eq!(pre, post, "a refused land leaves the commitment untouched");
    }

    /// The full checked land: the CI gate refuses the merge until the committed,
    /// signed approval receipt is presented, then the PR lands as finalized
    /// cap-gated turns (review + check + cap all exercised end to end).
    #[test]
    fn approval_checked_pr_refuses_until_witnessed_then_lands() {
        let run = run_checked_land(/* hold_cap */ true);
        // The check refused the land while no witness was presented.
        let (check, _reason) = run
            .refused_without_witness
            .as_ref()
            .expect("the check gate refused the un-witnessed land");
        assert_eq!(check, "approved");
        // The comment + approval were real signed, finalized receipts.
        assert!(
            run.approval.executor_signature.is_some(),
            "the approval is executor-signed"
        );
        // With the witness presented, the PR lands.
        let receipts = run.land.expect("a checked, cap-holding PR lands");
        assert!(!receipts.is_empty(), "the checked land produced receipts");
        assert_ne!(
            run.pre_commitment, run.post_commitment,
            "the merge moved the commitment"
        );
        assert!(
            run.projection_ok,
            "the landed commitment matches the projection"
        );
        assert_eq!(
            run.landed_content, "two\nthree\n",
            "both sides' edits landed"
        );
    }

    /// The non-holder path THROUGH the checked flow: the check is satisfied yet
    /// the cap-less merger is still refused in-band (checks and caps are
    /// independent gates), receipt-less.
    #[test]
    fn checks_and_caps_are_independent_capless_still_refused() {
        let run = run_checked_land(/* hold_cap */ false);
        match run.land {
            Err(PullRequestError::Refused(TurnError::CapabilityNotHeld { .. })) => {}
            other => panic!("expected the cap refusal after the check passed, got {other:?}"),
        }
        assert_eq!(
            run.pre_commitment, run.post_commitment,
            "nothing landed — the capless merge left no receipt"
        );
    }
}
