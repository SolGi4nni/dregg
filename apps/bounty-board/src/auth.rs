//! Admin authentication — delegated to `dregg-app-framework`.
//!
//! The bounty board uses the framework's [`AdminAuth`] extractor and [`AdminToken`]
//! type for all admin endpoint protection. This module re-exports the relevant types
//! for backward compatibility with code that imports from `dregg_bounty_board::auth`.
//!
//! The framework implementation provides:
//! - Constant-time token comparison (timing side-channel resistant)
//! - `DREGG_ADMIN_TOKEN` environment variable reading
//! - Fail-closed behavior when token is not configured (`AdminMode::Disabled`)
//! - `AdminAuth` axum extractor via the `HasAdminToken` trait

pub use dregg_app_framework::auth::{
    AdminAuth, AdminAuthRejection, AdminMode, AdminToken, HasAdminToken,
};
