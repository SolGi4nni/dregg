//! Cross-federation CapTP-delivered Turn integration tests.
//!
//! This is the **Silver-Vision E2E core**: Alice on F1 creates a bearer
//! cap, Bob on F2 receives via three-party handoff, Bob exercises →
//! CapTP message → Alice's executor produces a Turn with
//! `Authorization::CapTpDelivered`, the resulting WitnessedReceipt
//! scope-2 chain is verifiable across the federation boundary.
//!
//! All tests in this file currently `#[ignore]` on either:
//!   - CapTP cross-federation transport (no live wire today — exposure
//!     is via `dregg_captp::SwissTable` + `validate_handoff`, but the
//!     end-to-end CapTP→Turn pipeline is not yet wired through the
//!     teasting harness),
//!   - `Authorization::CapTpDelivered` executor dispatch with
//!     introducer + recipient signature checks,
//!   - WitnessedReceipt scope-2 chain verification across federations.
//!
//! See SILVER-VISION-E2E-VERIFICATION.md, AUDIT-federation.md §8,
//! AUTHORIZATION-CUSTOM-DESIGN.md, and demo/silver-vision-e2e/expected.json.
