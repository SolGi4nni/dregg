//! # `attribution` — **the ONE vocabulary for "how do we know who did this".**
//!
//! A receipt already distinguished a signed turn from an asserted one
//! ([`crate::lib`]'s receipt gloss, and [`dreggnet_offerings::Attribution`] underneath it). A
//! **board row did not.** On a leaderboard whose entire pitch is that it cannot be faked, a run
//! played by a phrase-holder whose device signed every move and a run typed in by an anonymous
//! visitor rendered as the same row, in the same type, with nothing to tell them apart. The board
//! was not lying — it was silent, which on a page that sells verifiability reads as a claim.
//!
//! This module is the vocabulary that fixes that, in one place, so the Descent board, `/you`, the
//! crown board and the link page cannot drift into three different words for one fact. It is
//! deliberately tiny and has no I/O: a grade, the copy for it, and the markup.
//!
//! ## ⚑ THE REGISTER: a fact, never a badge of shame
//!
//! The copy here was written against one rule, and it is the rule to hold the line on when somebody
//! adds a fourth grade: **an asserted row is not cheating.** It is the ordinary way to play on the
//! web, it is what every player did before there was any other option, and it is what a visitor who
//! just wants to click a game will always do. What it *is* is a **weaker claim** — the name was
//! taken at face value — and a page that shows a result owes the reader the difference between "we
//! checked" and "we took their word for it" without dressing the second one up as a transgression.
//!
//! Concretely, the rules the strings below keep:
//!
//! * No red. No warning triangle. No "unverified" (which reads as *dis*proved), no "unsigned"
//!   (which frames the player as having failed to do something), no exclamation of any kind.
//! * The grades are described by **what was checked**, not by how much we trust the player:
//!   "signed on their own device", "signed by the bot's key", "attributed". A reader can act on
//!   that; "trusted / untrusted" is a verdict on a person.
//! * The **stronger** grade carries the visual weight. Marking the weak one is what makes a badge
//!   of shame; marking the strong one is what makes a distinction.
//!
//! ## Why three grades and not two
//!
//! Because the product genuinely has three custody stories and collapsing them would launder the
//! most interesting one. A Discord turn IS signed — [`dreggnet_offerings::Custody::Custodial`] —
//! but with a key `BLAKE3(bot secret, your account id)` that the operator can derive for anybody, so
//! calling it simply "signed" beside a phrase-holder's device signature would tell the reader the
//! two mean the same thing, and they do not. That distinction is already carried as DATA
//! ([`Custody`]) all the way to the receipt; this module is the first thing that renders it.

use dreggnet_offerings::{Attribution, Custody};

use crate::esc;

// ─────────────────────────────────────────────────────────────────────────────
// THE GRADE
// ─────────────────────────────────────────────────────────────────────────────

/// **How a result's actor was established.** The rendering-side join of
/// [`Attribution`] (was a signature consumed?) and [`Custody`] (whose machine held the key?) —
/// the two facts the substrate already carries separately and no surface previously showed.
///
/// Ordered weakest-first so a `max` over a run's moves is the run's honest floor: a run is only as
/// strongly attributed as its weakest move, which is the direction that cannot overstate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActorGrade {
    /// **No signature was consumed.** The name rode in a cookie or a query parameter and was taken
    /// at face value. Every browser turn before the device-key path, and every browser turn today
    /// on a browser that has not enrolled one.
    Asserted,
    /// **A signature verified, under a key the operator can also derive.** The chat surfaces: the
    /// bot holds one identity secret and derives every user's key from it, so the signature proves
    /// the bot's derivation of that user signed — not that a device only that user controls did.
    SignedCustodial,
    /// **A signature verified, under a key that never left the player's device.** The browser
    /// extension, the `dregg` CLI, and (as of the device-key path) an ordinary browser that
    /// enrolled one.
    SignedUserHeld,
}

impl ActorGrade {
    /// The grade a landed move's provenance names. `None` provenance is
    /// [`ActorGrade::Asserted`] — the floor, never the stronger claim, exactly as
    /// [`Custody`]'s own wire decoding treats a missing tag.
    pub fn of(attribution: Option<&Attribution>, custody: Option<Custody>) -> ActorGrade {
        match attribution {
            Some(Attribution::Signed { .. }) => match custody {
                Some(Custody::UserHeld) => ActorGrade::SignedUserHeld,
                // A signed move whose custody we did not record is CUSTODIAL here, not user-held:
                // understating custody is safe, overstating it is the wound `Custody` exists to
                // close.
                _ => ActorGrade::SignedCustodial,
            },
            _ => ActorGrade::Asserted,
        }
    }

    /// The grade for a surface that knows only its own custody story (a bot rendering its own
    /// board rows, where every move it wrote was signed by its own derivation).
    pub fn signed_with(custody: Custody) -> ActorGrade {
        match custody {
            Custody::UserHeld => ActorGrade::SignedUserHeld,
            Custody::Custodial => ActorGrade::SignedCustodial,
        }
    }

    /// The two-or-three word tag beside a name. Lowercase on purpose: it is an annotation, not a
    /// title, and a shouty tag on the weakest grade is the badge of shame this module refuses.
    pub fn tag(self) -> &'static str {
        match self {
            ActorGrade::SignedUserHeld => "signed",
            ActorGrade::SignedCustodial => "signed by the bot",
            ActorGrade::Asserted => "attributed",
        }
    }

    /// The one sentence that says WHAT WAS CHECKED. Shown on hover (`title=`) and spelled out in
    /// the legend; never abbreviated per-row, because a three-word tag cannot carry a custody
    /// story and a reader who wants one should not have to guess.
    pub fn sentence(self) -> &'static str {
        match self {
            ActorGrade::SignedUserHeld => {
                "Every move carried a signature made on the player's own device. This server never \
                 held the key that made it."
            }
            ActorGrade::SignedCustodial => {
                "Every move carried a signature, made with the key the chat bot derives for that \
                 account. Whoever runs the bot can derive that key too."
            }
            ActorGrade::Asserted => {
                "The name is the one the player was signed in as, recorded without a signature. \
                 This is how playing in a browser normally works."
            }
        }
    }

    /// Whether this grade consumed a signature at all — the one bit a caller that only wants
    /// "checked / not checked" should read, so it does not re-derive the split itself.
    pub fn is_signed(self) -> bool {
        !matches!(self, ActorGrade::Asserted)
    }

    /// The CSS modifier class the chip wears.
    fn class(self) -> &'static str {
        match self {
            ActorGrade::SignedUserHeld => "att att-self",
            ActorGrade::SignedCustodial => "att att-bot",
            ActorGrade::Asserted => "att att-plain",
        }
    }

    /// **The chip that rides beside a name on a board row.**
    ///
    /// ⚑ It is rendered for EVERY grade, including the weakest. A chip that appears only on strong
    /// rows makes its own absence the message, and an absence cannot be hovered, cannot be read by
    /// a screen reader, and cannot be told apart from a rendering bug. Naming all three costs one
    /// short word per row and makes the distinction legible instead of inferable.
    pub fn chip(self) -> String {
        format!(
            "<span class=\"{cls}\" title=\"{why}\">{tag}</span>",
            cls = self.class(),
            why = esc(self.sentence()),
            tag = esc(self.tag()),
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE LEGEND + THE STYLE
// ─────────────────────────────────────────────────────────────────────────────

/// The chip styling. Shared by every board so three surfaces cannot render the same fact three
/// sizes. Weight is on the STRONGEST grade (see the register note in the module doc): the
/// user-held chip gets the border and the ink, the asserted chip is quiet rather than alarmed.
pub const ATTRIBUTION_STYLE: &str = r##"<style>
.att{display:inline-block;margin-left:.45rem;padding:.05rem .4rem;border-radius:999px;
 font-size:.7rem;letter-spacing:.03em;line-height:1.5;white-space:nowrap;vertical-align:.08em;
 border:1px solid transparent}
.att-self{border-color:rgba(120,200,150,.55);color:rgba(150,220,175,.95);background:rgba(120,200,150,.08)}
.att-bot{border-color:rgba(140,160,220,.45);color:rgba(165,180,225,.9);background:rgba(140,160,220,.07)}
/* ⚑ Deliberately NOT red, NOT amber, and NOT bordered. An asserted row is the ordinary case, so it
   reads as a quiet annotation; anything warmer would turn "we took your word for it" into an
   accusation against a player who did nothing wrong. It still meets the body-text contrast floor
   the identity page's word-index note pins (opacity .72 on this shell measures above 7:1). */
.att-plain{color:inherit;opacity:.72}
.att-legend{margin:1rem 0 0;padding:.75rem .9rem;border:1px solid var(--line,#2a2a2a);border-radius:4px;
 background:rgba(255,255,255,.015);font-size:.86rem;line-height:1.6}
.att-legend h3{margin:0 0 .4rem;font-size:.78rem;letter-spacing:.04em;text-transform:uppercase;opacity:.7}
.att-legend dt{margin-top:.5rem}
.att-legend dd{margin:.1rem 0 0;opacity:.85}
</style>"##;

/// **The legend a board prints ONCE, under the rows.**
///
/// Every board that renders [`ActorGrade::chip`]s must render this too. That is not a style rule:
/// three words in a pill are an abbreviation, and an abbreviation nobody expands is how a
/// distinction becomes decoration. The last paragraph is the one that must survive editing — it is
/// the sentence that stops the weakest grade reading as an accusation.
pub fn legend() -> String {
    let rows: String = [
        ActorGrade::SignedUserHeld,
        ActorGrade::SignedCustodial,
        ActorGrade::Asserted,
    ]
    .iter()
    .map(|grade| {
        format!(
            "<dt>{chip}</dt><dd>{why}</dd>",
            chip = grade.chip(),
            why = esc(grade.sentence()),
        )
    })
    .collect();
    format!(
        "<div class=\"att-legend\"><h3>How each name on this board was established</h3>\
         <dl>{rows}</dl>\
         <p>All three are real play and all three count. The difference is what was checked, not \
         how good the run was: a signed row is a stronger claim about <em>who</em> played it, and \
         an attributed row is the ordinary way a browser plays. If you want your own rows signed, \
         <a href=\"/identity\">your identity page</a> has the one switch that does it.</p></div>"
    )
}

/// The same distinction in ONE sentence, for a surface with no room for the legend (a compact
/// card, a fragment re-render). Says the same thing the legend says; kept beside it so the two
/// cannot drift.
pub fn one_line_note() -> &'static str {
    "Rows marked signed carried a signature this server checked; rows marked attributed were \
     filed under the name the player was signed in as, which is how a browser normally plays."
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The floor is ASSERTED, from every direction a caller can approach it. Overstating a grade
    /// is the only failure here that matters: it would put "signed" beside a row nothing checked.
    #[test]
    fn the_grade_floor_is_asserted_and_unknown_custody_never_reaches_user_held() {
        assert_eq!(ActorGrade::of(None, None), ActorGrade::Asserted);
        assert_eq!(
            ActorGrade::of(None, Some(Custody::UserHeld)),
            ActorGrade::Asserted,
            "custody without a verified signature is not a signature"
        );
        let asserted = Attribution::Asserted {
            label: "visitor-1".into(),
        };
        assert_eq!(
            ActorGrade::of(Some(&asserted), Some(Custody::UserHeld)),
            ActorGrade::Asserted
        );
        let signed = Attribution::Signed {
            pubkey_hex: "ab".repeat(32),
        };
        assert_eq!(
            ActorGrade::of(Some(&signed), None),
            ActorGrade::SignedCustodial,
            "a signed move with NO recorded custody must read as custodial, never user-held"
        );
        assert_eq!(
            ActorGrade::of(Some(&signed), Some(Custody::Custodial)),
            ActorGrade::SignedCustodial
        );
        assert_eq!(
            ActorGrade::of(Some(&signed), Some(Custody::UserHeld)),
            ActorGrade::SignedUserHeld
        );
        // Ordered weakest-first, so folding a run's moves with `min` gives its honest floor.
        assert!(ActorGrade::Asserted < ActorGrade::SignedCustodial);
        assert!(ActorGrade::SignedCustodial < ActorGrade::SignedUserHeld);
    }

    /// ⚑ THE REGISTER TOOTH. The copy rule in the module doc is the whole point of the module, and
    /// a rule with no test is a rule the next edit deletes by accident.
    #[test]
    fn no_grade_is_described_as_a_transgression() {
        // Words that frame the player rather than naming the check.
        const ACCUSATIONS: &[&str] = &[
            "unverified",
            "unsigned",
            "not verified",
            "untrusted",
            "unproven",
            "fake",
            "cheat",
            "suspicious",
            "warning",
            "beware",
            "!",
        ];
        for grade in [
            ActorGrade::SignedUserHeld,
            ActorGrade::SignedCustodial,
            ActorGrade::Asserted,
        ] {
            let copy = format!("{} {}", grade.tag(), grade.sentence()).to_lowercase();
            for bad in ACCUSATIONS {
                assert!(
                    !copy.contains(bad),
                    "the {:?} copy frames the player instead of naming the check ({bad}): {copy}",
                    grade
                );
            }
            // Every grade says what WAS established, so no row is described only by a lack.
            assert!(
                !grade.tag().is_empty() && !grade.sentence().is_empty(),
                "every grade must name itself; an unlabelled row makes absence the message"
            );
        }
        let legend = legend().to_lowercase();
        for bad in ACCUSATIONS {
            assert!(!legend.contains(bad), "the legend accuses ({bad})");
        }
        // …and it must carry the sentence that keeps the weak grade legitimate.
        assert!(
            legend.contains("all three are real play"),
            "the legend must say plainly that an attributed row is not a lesser run"
        );
    }

    /// Every grade renders a chip — including the weakest. An absent chip cannot be hovered, read
    /// aloud, or told apart from a bug.
    #[test]
    fn every_grade_renders_a_chip_with_its_sentence() {
        for grade in [
            ActorGrade::SignedUserHeld,
            ActorGrade::SignedCustodial,
            ActorGrade::Asserted,
        ] {
            let chip = grade.chip();
            assert!(chip.contains(grade.tag()), "{chip}");
            assert!(
                chip.contains("title="),
                "the sentence must be reachable: {chip}"
            );
            assert!(
                ATTRIBUTION_STYLE.contains(grade.class().split(' ').nth(1).expect("modifier")),
                "the chip's modifier class has no style: {}",
                grade.class()
            );
        }
    }
}
