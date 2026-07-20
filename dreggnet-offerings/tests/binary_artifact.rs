//! Strict read-only artifact exports through the heterogeneous OfferingHost.

use deos_view::ViewNode;
use dreggnet_offerings::{
    Action, BinaryArtifactDescriptor, BinaryArtifactError, BinaryArtifactVisibility, DreggIdentity,
    HostArtifactError, Offering, OfferingError, OfferingHost, Outcome, RunCost, SessionConfig,
    SessionId, Surface, VerifyReport,
};

const PUBLIC: &str = "worker-task.v1";
const AUTHENTICATED: &str = "committee-task.v1";

#[derive(Clone, Copy)]
enum Fixture {
    Valid,
    OversizedBody,
    InvalidMediaType,
}

struct ArtifactOffering(Fixture);

impl ArtifactOffering {
    fn descriptor(name: &str, visibility: BinaryArtifactVisibility) -> BinaryArtifactDescriptor {
        BinaryArtifactDescriptor {
            name: name.to_string(),
            title: "Canonical worker task".to_string(),
            media_type: "application/vnd.dregg.worker-task-v1".to_string(),
            max_bytes: 16,
            disclosure: "Contains public task bindings and no witness material.".to_string(),
            visibility,
        }
    }
}

impl Offering for ArtifactOffering {
    type Session = ();

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(())
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        Vec::new()
    }

    fn advance(
        &self,
        _session: &mut Self::Session,
        _input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        Outcome::Refused("read-only fixture".to_string())
    }

    fn verify(&self, _session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(0)
    }

    fn render(&self, _session: &Self::Session) -> Surface {
        Surface(ViewNode::Text("artifact fixture".to_string()))
    }

    fn binary_artifacts(&self, _session: &Self::Session) -> Vec<BinaryArtifactDescriptor> {
        let mut public = Self::descriptor(PUBLIC, BinaryArtifactVisibility::Public);
        if matches!(self.0, Fixture::InvalidMediaType) {
            public.media_type = "application/octet-stream; secret=maybe".to_string();
        }
        vec![
            public,
            Self::descriptor(AUTHENTICATED, BinaryArtifactVisibility::Authenticated),
        ]
    }

    fn export_binary_artifact(
        &self,
        _session: &Self::Session,
        name: &str,
    ) -> Result<Vec<u8>, BinaryArtifactError> {
        match name {
            PUBLIC if matches!(self.0, Fixture::OversizedBody) => Ok(vec![0xEE; 17]),
            PUBLIC => Ok(b"public-task-v1".to_vec()),
            AUTHENTICATED => Ok(b"member-task-v1".to_vec()),
            _ => Err(BinaryArtifactError::UnknownArtifact(name.to_string())),
        }
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn fixture_host(fixture: Fixture) -> (OfferingHost, SessionId) {
    let mut host = OfferingHost::new();
    host.register("fixture", "Artifact fixture", ArtifactOffering(fixture));
    let id = SessionId::new("live");
    host.open_session("fixture", id.clone(), SessionConfig::default())
        .expect("fixture opens");
    (host, id)
}

#[test]
fn public_and_authenticated_exports_are_explicit_bounded_and_digest_exact() {
    let (host, id) = fixture_host(Fixture::Valid);

    let public = host
        .export_binary_artifact("fixture", &id, PUBLIC, None)
        .expect("explicit public artifact is anonymously readable");
    assert_eq!(public.name, PUBLIC);
    assert_eq!(public.media_type, "application/vnd.dregg.worker-task-v1");
    assert_eq!(public.bytes, b"public-task-v1");
    assert_eq!(public.digest, *blake3::hash(&public.bytes).as_bytes());

    assert_eq!(
        host.export_binary_artifact("fixture", &id, AUTHENTICATED, None),
        Err(HostArtifactError::Artifact(
            BinaryArtifactError::AuthenticationRequired
        ))
    );
    let member = DreggIdentity("committee-member".to_string());
    assert_eq!(
        host.export_binary_artifact("fixture", &id, AUTHENTICATED, Some(&member))
            .expect("attributed viewer passes the explicit gate")
            .bytes,
        b"member-task-v1"
    );
}

#[test]
fn exact_routing_and_descriptor_body_caps_fail_closed() {
    let (host, id) = fixture_host(Fixture::Valid);
    assert!(matches!(
        host.export_binary_artifact("fixture", &SessionId::new("absent"), PUBLIC, None),
        Err(HostArtifactError::UnknownSession { .. })
    ));
    assert!(matches!(
        host.export_binary_artifact("fixture", &id, "other-task.v1", None),
        Err(HostArtifactError::Artifact(
            BinaryArtifactError::UnknownArtifact(_)
        ))
    ));

    let (oversized, id) = fixture_host(Fixture::OversizedBody);
    assert!(matches!(
        oversized.export_binary_artifact("fixture", &id, PUBLIC, None),
        Err(HostArtifactError::Artifact(
            BinaryArtifactError::InvalidArtifact(_)
        ))
    ));

    let (invalid_media, id) = fixture_host(Fixture::InvalidMediaType);
    assert!(matches!(
        invalid_media.binary_artifacts("fixture", &id),
        Err(HostArtifactError::Artifact(
            BinaryArtifactError::InvalidArtifact(_)
        ))
    ));
}
