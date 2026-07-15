//! Bounded, paginated reads.
//!
//! The retired reads did a full scan of the whole store and serialized *everything*
//! into one JSON array — a large tenant returned its entire record set in a single
//! unbounded response. Every list surface here goes through [`Page`]: a `?limit=&offset=`
//! window with a per-request cap ([`MAX_LIMIT`]) and a default ([`DEFAULT_LIMIT`]), so a
//! response is bounded regardless of how much a tenant owns. The scoped reads also index
//! by owner (see [`crate::machines::MachineStore::list_for_owner`]) so the *scan* is
//! O(owned), not O(all) — pagination bounds the response, the index bounds the work.

/// The window size when a request names none.
pub const DEFAULT_LIMIT: usize = 100;
/// The largest window a request may ask for (a bigger `limit` is clamped to this).
pub const MAX_LIMIT: usize = 1000;

/// A parsed, clamped pagination window.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Page {
    /// Records to return (clamped to `1..=MAX_LIMIT`).
    pub limit: usize,
    /// Records to skip from the front of the (stably-ordered) set.
    pub offset: usize,
}

impl Default for Page {
    fn default() -> Page {
        Page {
            limit: DEFAULT_LIMIT,
            offset: 0,
        }
    }
}

impl Page {
    /// Parse `?limit=&offset=` from a request target, clamping `limit` to
    /// `1..=MAX_LIMIT` and defaulting a missing / unparseable value. `offset` defaults
    /// to 0. Robust to junk (a non-numeric value falls back to the default).
    pub fn from_target(target: &str) -> Page {
        let query = target.split_once('?').map(|(_, q)| q).unwrap_or("");
        let mut limit = DEFAULT_LIMIT;
        let mut offset = 0usize;
        for pair in query.split('&') {
            if let Some((k, v)) = pair.split_once('=') {
                match k {
                    "limit" => {
                        if let Ok(n) = v.parse::<usize>() {
                            limit = n.clamp(1, MAX_LIMIT);
                        }
                    }
                    "offset" => {
                        if let Ok(n) = v.parse::<usize>() {
                            offset = n;
                        }
                    }
                    _ => {}
                }
            }
        }
        Page { limit, offset }
    }

    /// Apply this window to `items` (already stably ordered): skip `offset`, take
    /// `limit`.
    pub fn apply<T>(&self, items: Vec<T>) -> Vec<T> {
        items
            .into_iter()
            .skip(self.offset)
            .take(self.limit)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_when_absent() {
        let p = Page::from_target("/api/machines");
        assert_eq!(p.limit, DEFAULT_LIMIT);
        assert_eq!(p.offset, 0);
    }

    #[test]
    fn parses_and_clamps() {
        let p = Page::from_target("/api/machines?limit=5&offset=10");
        assert_eq!(p.limit, 5);
        assert_eq!(p.offset, 10);
        // Over-cap limit clamps; zero clamps up to 1; junk falls back.
        assert_eq!(Page::from_target("/x?limit=99999").limit, MAX_LIMIT);
        assert_eq!(Page::from_target("/x?limit=0").limit, 1);
        assert_eq!(Page::from_target("/x?limit=abc").limit, DEFAULT_LIMIT);
    }

    #[test]
    fn windows_the_set() {
        let all: Vec<u32> = (0..10).collect();
        let p = Page {
            limit: 3,
            offset: 4,
        };
        assert_eq!(p.apply(all), vec![4, 5, 6]);
        // An offset past the end yields empty, not a panic.
        assert!(
            Page {
                limit: 5,
                offset: 100
            }
            .apply((0..3).collect())
            .is_empty()
        );
    }
}
