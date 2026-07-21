//! Audience-scoped rendering for offering surfaces.
//!
//! A per-viewer projection is an information release, not merely a prettier
//! rendering. Passing a `viewer` through every frontend independently made it
//! too easy to paint that release into a shared Discord/Telegram message.
//! [`Audience`] makes the transport audience explicit and [`project`] chooses
//! the only safe projection for it:
//!
//! * [`Audience::Shared`] has **no viewer identity** and can only call
//!   [`Offering::render`] / [`Offering::actions`];
//! * [`Audience::Private`] is a single-reader channel and may call
//!   [`Offering::render_for`] / [`Offering::actions_for`].
//!
//! This is a presentation boundary. It does not turn host-visible secrets into
//! cryptographic no-viewer custody; it prevents an already-authorized private
//! projection from being copied onto a multi-reader surface.

use crate::{Action, DreggIdentity, Offering, Surface};

/// Who can read the surface a frontend is about to publish.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Audience {
    /// More than one reader (a Discord channel, Telegram group, stream, or
    /// projector). Deliberately carries no identity, so a shared renderer
    /// cannot accidentally request one participant's private projection.
    Shared,
    /// One authenticated reader. The identity selects that reader's cap-gated
    /// affordances and, where declared, their own private state.
    Private(DreggIdentity),
}

impl Audience {
    /// A shared, viewer-blind audience.
    pub const fn shared() -> Self {
        Self::Shared
    }

    /// A private, single-reader audience.
    pub fn private(viewer: DreggIdentity) -> Self {
        Self::Private(viewer)
    }

    /// Whether this audience is structurally single-reader.
    pub const fn is_private(&self) -> bool {
        matches!(self, Self::Private(_))
    }
}

/// One audience-safe surface and exactly the affordances painted beside it.
#[derive(Debug, Clone)]
pub struct AudienceProjection {
    /// The view tree selected for the audience.
    pub surface: Surface,
    /// The affordances selected under the same audience rule.
    pub actions: Vec<Action>,
    /// Whether the offering says its private projection may reveal hidden
    /// state. This remains `true` on a shared projection: the shared surface is
    /// safe, while the flag tells an adapter that a private companion is useful.
    pub hidden_information: bool,
    /// Whether this particular projection was selected for one private reader.
    pub private: bool,
}

/// Select an offering's surface and actions for an explicit audience.
///
/// The shared branch never evaluates `render_for` or `actions_for`. Testing
/// only that two values happen to be equal is unsafe before a hand is dealt or
/// a move is sealed, because equality can change later in the same session.
pub fn project<O: Offering>(
    offering: &O,
    session: &O::Session,
    audience: &Audience,
) -> AudienceProjection {
    let hidden_information = offering.hidden_information();
    match audience {
        Audience::Shared => AudienceProjection {
            surface: offering.render(session),
            actions: offering.actions(session),
            hidden_information,
            private: false,
        },
        Audience::Private(viewer) => AudienceProjection {
            surface: offering.render_for(session, viewer),
            actions: offering.actions_for(session, viewer),
            hidden_information,
            private: true,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{OfferingError, Outcome, RunCost, SessionConfig, VerifyReport};
    use deos_view::ViewNode;
    use std::cell::Cell;

    struct LeakCanary {
        private_calls: Cell<usize>,
    }

    impl LeakCanary {
        fn new() -> Self {
            Self {
                private_calls: Cell::new(0),
            }
        }
    }

    impl Offering for LeakCanary {
        type Session = ();

        fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
            Ok(())
        }

        fn actions(&self, _session: &Self::Session) -> Vec<Action> {
            vec![Action::new("public action", "public", 0, true)]
        }

        fn actions_for(&self, _session: &Self::Session, _viewer: &DreggIdentity) -> Vec<Action> {
            self.private_calls.set(self.private_calls.get() + 1);
            vec![Action::new("SECRET ROLE: warden", "secret", 7, true)]
        }

        fn advance(
            &self,
            _session: &mut Self::Session,
            _input: Action,
            _actor: DreggIdentity,
        ) -> Outcome {
            Outcome::Refused("not used".to_string())
        }

        fn verify(&self, _session: &Self::Session) -> VerifyReport {
            VerifyReport::ok(0)
        }

        fn render(&self, _session: &Self::Session) -> Surface {
            Surface(ViewNode::Text("sealed move: fog".to_string()))
        }

        fn render_for(&self, _session: &Self::Session, _viewer: &DreggIdentity) -> Surface {
            self.private_calls.set(self.private_calls.get() + 1);
            Surface(ViewNode::Text(
                "SECRET CARD #73; SEALED MOVE e2-e4".to_string(),
            ))
        }

        fn hidden_information(&self) -> bool {
            true
        }

        fn price(&self, _input: &Action) -> RunCost {
            RunCost::free()
        }
    }

    fn text(projection: &AudienceProjection) -> String {
        format!("{:?} {:?}", projection.surface.view(), projection.actions)
    }

    #[test]
    fn shared_projection_never_evaluates_the_viewer_release() {
        let offering = LeakCanary::new();
        let projection = project(&offering, &(), &Audience::Shared);
        let visible = text(&projection);
        assert!(projection.hidden_information);
        assert!(!projection.private);
        assert!(visible.contains("fog") && visible.contains("public action"));
        assert!(!visible.contains("SECRET CARD"));
        assert!(!visible.contains("SEALED MOVE e2-e4"));
        assert!(!visible.contains("SECRET ROLE"));
        assert_eq!(
            offering.private_calls.get(),
            0,
            "the shared branch must not even evaluate the private renderer"
        );
    }

    #[test]
    fn private_projection_releases_only_when_the_audience_carries_a_viewer() {
        let offering = LeakCanary::new();
        let projection = project(
            &offering,
            &(),
            &Audience::private(DreggIdentity("viewer:alice".to_string())),
        );
        let visible = text(&projection);
        assert!(projection.hidden_information);
        assert!(projection.private);
        assert!(visible.contains("SECRET CARD #73"));
        assert!(visible.contains("SEALED MOVE e2-e4"));
        assert!(visible.contains("SECRET ROLE: warden"));
        assert_eq!(
            offering.private_calls.get(),
            2,
            "the private branch selects both viewer-aware halves of the projection"
        );
    }

    #[test]
    fn erased_host_boundary_preserves_the_shared_no_viewer_rule() {
        let mut host = crate::OfferingHost::new();
        host.register("leak-canary", "Leak canary", LeakCanary::new());
        let id = host.open("leak-canary").expect("open canary");

        let shared = host
            .project("leak-canary", &id, &Audience::Shared)
            .expect("shared projection");
        let shared_text = text(&shared);
        assert!(!shared_text.contains("SECRET CARD"));
        assert!(!shared_text.contains("SEALED MOVE e2-e4"));
        assert!(!shared_text.contains("SECRET ROLE"));

        let private = host
            .project(
                "leak-canary",
                &id,
                &Audience::private(DreggIdentity("viewer:alice".to_string())),
            )
            .expect("private projection");
        assert!(text(&private).contains("SECRET CARD #73"));
    }
}
