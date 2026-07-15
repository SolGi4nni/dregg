//! Resource quotas + per-owner rate limiting — the DoS teeth on the publish path.
//!
//! The bare publish path used to `serde_json::from_slice` an unbounded request body
//! into memory: a holder of one valid cap could POST a multi-GB bundle and OOM the
//! host, and could hammer publish with no per-owner ceiling. A "Cloudflare for
//! agents" needs quotas tied to the lease, enforced BEFORE the expensive decode.
//!
//! [`PublishLimits`] bounds a single publish (body / per-asset / asset-count / total
//! site bytes) and returns a `413`. [`RateLimiter`] bounds publish FREQUENCY per
//! owner over a sliding window and returns a `429`. Both are cheap to check and are
//! applied by [`crate::publish::SitePublishHandler`] at the earliest safe point.

use std::collections::BTreeMap;
use std::sync::Mutex;

use crate::lock::lock_recover;
use crate::site::SiteContent;

/// The size ceilings a single publish must satisfy. Defaults are generous for a
/// static microsite yet bounded well below an OOM.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PublishLimits {
    /// Max encoded request-body bytes, checked BEFORE decode (the OOM guard).
    pub max_body_bytes: usize,
    /// Max bytes in any single asset body.
    pub max_asset_bytes: usize,
    /// Max number of assets in a site.
    pub max_asset_count: usize,
    /// Max total served bytes across all assets in a site.
    pub max_total_bytes: usize,
}

impl Default for PublishLimits {
    fn default() -> PublishLimits {
        PublishLimits {
            max_body_bytes: 8 * 1024 * 1024,   // 8 MiB encoded bundle
            max_asset_bytes: 4 * 1024 * 1024,  // 4 MiB per asset
            max_asset_count: 512,              // 512 files
            max_total_bytes: 16 * 1024 * 1024, // 16 MiB per site
        }
    }
}

/// A quota that a publish exceeded — mapped to a `413` by the handler.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuotaError {
    /// The encoded request body exceeded [`PublishLimits::max_body_bytes`].
    BodyTooLarge { got: usize, max: usize },
    /// A single asset exceeded [`PublishLimits::max_asset_bytes`].
    AssetTooLarge {
        path: String,
        got: usize,
        max: usize,
    },
    /// The site had more assets than [`PublishLimits::max_asset_count`].
    TooManyAssets { got: usize, max: usize },
    /// The site's total bytes exceeded [`PublishLimits::max_total_bytes`].
    SiteTooLarge { got: usize, max: usize },
}

impl std::fmt::Display for QuotaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuotaError::BodyTooLarge { got, max } => {
                write!(f, "publish body is {got} bytes, over the {max}-byte limit")
            }
            QuotaError::AssetTooLarge { path, got, max } => write!(
                f,
                "asset `{path}` is {got} bytes, over the {max}-byte per-asset limit"
            ),
            QuotaError::TooManyAssets { got, max } => {
                write!(f, "site has {got} assets, over the {max}-asset limit")
            }
            QuotaError::SiteTooLarge { got, max } => {
                write!(f, "site is {got} bytes, over the {max}-byte total limit")
            }
        }
    }
}

impl std::error::Error for QuotaError {}

impl PublishLimits {
    /// Check the encoded body length BEFORE decode — the OOM guard on the hot path.
    pub fn check_body(&self, body_len: usize) -> Result<(), QuotaError> {
        if body_len > self.max_body_bytes {
            return Err(QuotaError::BodyTooLarge {
                got: body_len,
                max: self.max_body_bytes,
            });
        }
        Ok(())
    }

    /// Check a decoded bundle against the per-asset / count / total ceilings.
    pub fn check_content(&self, content: &SiteContent) -> Result<(), QuotaError> {
        if content.assets.len() > self.max_asset_count {
            return Err(QuotaError::TooManyAssets {
                got: content.assets.len(),
                max: self.max_asset_count,
            });
        }
        let mut total = 0usize;
        for (path, asset) in &content.assets {
            let n = asset.body.len();
            if n > self.max_asset_bytes {
                return Err(QuotaError::AssetTooLarge {
                    path: path.clone(),
                    got: n,
                    max: self.max_asset_bytes,
                });
            }
            total = total.saturating_add(n);
        }
        if total > self.max_total_bytes {
            return Err(QuotaError::SiteTooLarge {
                got: total,
                max: self.max_total_bytes,
            });
        }
        Ok(())
    }
}

/// A per-owner fixed-window rate limiter: at most `max_per_window` publishes per
/// `window` clock-units for a given owner subject. Keyed off the authenticated owner
/// (never the request), so a single cap cannot be used to hammer the plane.
///
/// The window uses the handler's own `now` clock (the same monotone clock the lease
/// lapse is driven by), so the limiter needs no wall-clock of its own.
pub struct RateLimiter {
    max_per_window: u32,
    window: u64,
    buckets: Mutex<BTreeMap<String, Window>>,
}

#[derive(Clone, Copy)]
struct Window {
    start: u64,
    count: u32,
}

impl RateLimiter {
    /// A limiter allowing `max_per_window` publishes per `window` clock-units per
    /// owner.
    pub fn new(max_per_window: u32, window: u64) -> RateLimiter {
        RateLimiter {
            max_per_window: max_per_window.max(1),
            window: window.max(1),
            buckets: Mutex::new(BTreeMap::new()),
        }
    }

    /// Record a publish attempt by `owner` at `now`; `Ok(())` if under the ceiling,
    /// `Err(retry_after)` (clock-units until the window rolls) if the owner is over.
    pub fn check(&self, owner: &str, now: u64) -> Result<(), u64> {
        let mut buckets = lock_recover(&self.buckets);
        let w = buckets.entry(owner.to_string()).or_insert(Window {
            start: now,
            count: 0,
        });
        if now.saturating_sub(w.start) >= self.window {
            // The window rolled — reset.
            w.start = now;
            w.count = 0;
        }
        if w.count >= self.max_per_window {
            let retry_after = self.window - now.saturating_sub(w.start);
            return Err(retry_after);
        }
        w.count += 1;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn body_and_content_quotas_bite() {
        let limits = PublishLimits {
            max_body_bytes: 100,
            max_asset_bytes: 50,
            max_asset_count: 2,
            max_total_bytes: 80,
        };
        assert!(limits.check_body(100).is_ok());
        assert!(matches!(
            limits.check_body(101),
            Err(QuotaError::BodyTooLarge { .. })
        ));

        // Too many assets.
        let many = SiteContent::new()
            .with("/a.txt", "a")
            .with("/b.txt", "b")
            .with("/c.txt", "c");
        assert!(matches!(
            limits.check_content(&many),
            Err(QuotaError::TooManyAssets { got: 3, max: 2 })
        ));

        // One oversized asset.
        let big = SiteContent::new().with("/a.txt", vec![b'x'; 60]);
        assert!(matches!(
            limits.check_content(&big),
            Err(QuotaError::AssetTooLarge { .. })
        ));

        // Total over budget (2 × 45 = 90 > 80) though each is under per-asset.
        let total = SiteContent::new()
            .with("/a.txt", vec![b'x'; 45])
            .with("/b.txt", vec![b'y'; 45]);
        assert!(matches!(
            limits.check_content(&total),
            Err(QuotaError::SiteTooLarge { .. })
        ));

        // Within every ceiling.
        let ok = SiteContent::new().with("/a.txt", vec![b'x'; 40]);
        assert!(limits.check_content(&ok).is_ok());
    }

    #[test]
    fn rate_limiter_bounds_per_owner_and_rolls() {
        let rl = RateLimiter::new(2, 100);
        assert!(rl.check("alice", 1000).is_ok());
        assert!(rl.check("alice", 1001).is_ok());
        // Third within the window is refused.
        assert_eq!(rl.check("alice", 1002), Err(98));
        // A different owner is independent.
        assert!(rl.check("bob", 1002).is_ok());
        // Once the window rolls, alice is allowed again.
        assert!(rl.check("alice", 1100).is_ok());
    }
}
