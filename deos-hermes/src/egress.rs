//! THE STRUCTURED EGRESS DOOR — the ONE cap-gated, off-by-default, revocable way
//! a jailed agent reaches a SPECIFIC outside resource.
//!
//! ## Why this exists (the third leg of dregg-as-host)
//!
//! The jail ([`crate::confined`]) denies the agent ALL ambient authority: its own
//! base shell / file tools hit the OS sandbox walls and go inert. dregg's tools
//! ([`crate::mcp_server`]) are then the agent's only *effective* effect-path —
//! but they route to OUR containers (a deos-js World, a confined PD), never the
//! host. So by construction the jailed agent has NO reach to the real outside.
//!
//! That total denial is the safe default, but a USEFUL agent sometimes must touch
//! one specific external thing (a project directory, a docs tree). The structured
//! egress is exactly that and nothing more: a HOST-granted [`EgressGrant`] naming
//! ONE host path (or, later, one endpoint), read-only, that the host threads into
//! the jail's sandbox profile as a single SBPL/Landlock allow-rule. Everything
//! else stays denied.
//!
//! ## The three load-bearing properties (each provable by running)
//!
//!   1. **Off by default.** A jail launched with [`EgressPolicy::sealed`] (the
//!      default) carries no grant → the sandbox profile is the Endpoint-only jail
//!      → the granted path is DENIED inside the PD exactly like any other path.
//!   2. **Granted = a specific door, not a hole.** [`EgressPolicy::grant_read`]
//!      names ONE subpath. Inside the PD that subpath becomes readable; a SIBLING
//!      path (outside the grant) stays denied. The door is to a specific resource,
//!      not "the filesystem".
//!   3. **Revocable.** [`EgressPolicy::revoke`] drops the grant; the NEXT jail
//!      launched under the policy is sealed again. A grant is a capability the
//!      host holds and can take back — it never becomes ambient.
//!
//! The grant is consulted by the host when it builds the confined PD's
//! [`Confinement`](dregg_firmament::sandbox::Confinement) (via
//! [`EgressPolicy::confinement_for`]); the agent never mints its own egress.

#![cfg(unix)]

/// ONE granted egress door: a read-only host path the jailed agent may reach.
///
/// This is the capability the HOST holds. It is deliberately minimal — a single
/// canonical subpath, read-only — so the door is to a *named resource*, not a
/// class of authority. (A network-endpoint variant is the next slice; the same
/// shape — a specific, granted, revocable target — applies.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EgressGrant {
    /// The host filesystem subpath the agent is granted read access to. Becomes
    /// exactly one `(allow file-read* (subpath "<path>"))` SBPL rule on macOS / a
    /// Landlock read rule on Linux — and NOTHING else opens.
    pub read_path: String,
}

impl EgressGrant {
    /// A read-only grant for one host subpath.
    pub fn read(path: impl Into<String>) -> EgressGrant {
        EgressGrant { read_path: path.into() }
    }
}

/// THE EGRESS POLICY — the host's standing set of granted doors for a jailed
/// agent. Sealed (no doors) by default; the host opens specific doors with
/// [`Self::grant_read`] and takes them back with [`Self::revoke`].
///
/// The policy is the bridge between a cap-gated grant and the OS sandbox profile:
/// [`Self::confinement_for`] folds every live grant into the
/// [`Confinement`](dregg_firmament::sandbox::Confinement) the host hands to
/// [`ProcessKernel::spawn_pd_confined_with`](dregg_firmament::process_kernel::ProcessKernel::spawn_pd_confined_with).
#[derive(Clone, Debug, Default)]
pub struct EgressPolicy {
    grants: Vec<EgressGrant>,
}

impl EgressPolicy {
    /// The default: SEALED — no egress doors. A jail built from this denies every
    /// host path (the agent reaches the outside only through dregg's tools, which
    /// route to our containers).
    pub fn sealed() -> EgressPolicy {
        EgressPolicy { grants: Vec::new() }
    }

    /// Whether the policy currently grants no egress (the safe default state).
    pub fn is_sealed(&self) -> bool {
        self.grants.is_empty()
    }

    /// GRANT a read-only door to one specific host subpath. Idempotent on the same
    /// path. This is the explicit, opt-in act the host performs to let the agent
    /// reach a named outside resource; without it the path stays denied.
    pub fn grant_read(&mut self, path: impl Into<String>) -> &mut EgressPolicy {
        let g = EgressGrant::read(path);
        if !self.grants.contains(&g) {
            self.grants.push(g);
        }
        self
    }

    /// REVOKE the door to `path` (if granted). The next jail built from this policy
    /// is sealed against that path again — the grant was a capability the host
    /// held, now taken back; it never became ambient authority the agent keeps.
    pub fn revoke(&mut self, path: &str) -> &mut EgressPolicy {
        self.grants.retain(|g| g.read_path != path);
        self
    }

    /// The live grants (the doors currently open), for the mandate inspector.
    pub fn grants(&self) -> &[EgressGrant] {
        &self.grants
    }

    /// Whether `path` is reachable under THIS policy — i.e. it is at or beneath a
    /// granted subpath. The host uses this to decide whether an egress request is
    /// admissible BEFORE it ever threads a path into the sandbox; the OS sandbox is
    /// the enforcing backstop (a path not granted is physically denied in the PD).
    pub fn admits_read(&self, path: &str) -> bool {
        self.grants.iter().any(|g| path_under(path, &g.read_path))
    }

    /// Fold every live grant into a confined-PD profile: the Endpoint-only jail
    /// (`control_fd` kept; file/net/exec denied) PLUS exactly the granted read
    /// paths. Hand the result to
    /// [`ProcessKernel::spawn_pd_confined_with`](dregg_firmament::process_kernel::ProcessKernel::spawn_pd_confined_with).
    ///
    /// Sealed policy ⇒ an Endpoint-only [`Confinement`] (identical to the implicit
    /// jail). Each grant ⇒ one allow-subpath rule and nothing more.
    pub fn confinement_for(
        &self,
        control_fd: std::os::unix::io::RawFd,
    ) -> dregg_firmament::sandbox::Confinement {
        let mut c = dregg_firmament::sandbox::Confinement::endpoint_only(control_fd);
        for g in &self.grants {
            // The OS sandbox (macOS Seatbelt `subpath` / Linux Landlock) matches the
            // CANONICAL (symlink-resolved) path the kernel sees after `open` follows
            // symlinks — e.g. macOS `$TMPDIR` (`/var/folders/…`) resolves to
            // `/private/var/folders/…`. Grant the resolved path so the rule the
            // kernel checks against actually matches the granted resource. (Falls
            // back to the literal path if it cannot be resolved yet.)
            let resolved = std::fs::canonicalize(&g.read_path)
                .ok()
                .and_then(|p| p.to_str().map(|s| s.to_string()))
                .unwrap_or_else(|| g.read_path.clone());
            c = c.with_read_path(resolved);
        }
        c
    }
}

/// Whether `path` is at or beneath the granted `base` subpath (a textual subpath
/// check mirroring SBPL/Landlock `subpath` semantics: `base` itself, or `base/…`).
fn path_under(path: &str, base: &str) -> bool {
    if path == base {
        return true;
    }
    let with_sep = if base.ends_with('/') {
        base.to_string()
    } else {
        format!("{base}/")
    };
    path.starts_with(&with_sep)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sealed_by_default_admits_nothing() {
        let p = EgressPolicy::sealed();
        assert!(p.is_sealed());
        assert!(!p.admits_read("/tmp/anything"));
    }

    #[test]
    fn grant_opens_exactly_one_door_revoke_closes_it() {
        let mut p = EgressPolicy::sealed();
        p.grant_read("/tmp/deos_egress");
        assert!(!p.is_sealed());
        // The granted subpath + things beneath it are admitted.
        assert!(p.admits_read("/tmp/deos_egress"));
        assert!(p.admits_read("/tmp/deos_egress/notes.txt"));
        // A SIBLING outside the grant is NOT a door.
        assert!(!p.admits_read("/tmp/deos_egress_evil"));
        assert!(!p.admits_read("/etc/passwd"));
        // Revoke closes it.
        p.revoke("/tmp/deos_egress");
        assert!(p.is_sealed());
        assert!(!p.admits_read("/tmp/deos_egress"));
    }

    #[test]
    fn confinement_carries_the_grant_into_the_profile() {
        let mut p = EgressPolicy::sealed();
        // Sealed → endpoint-only (no read paths).
        let sealed = p.confinement_for(7);
        assert!(sealed.read_paths.is_empty());
        // Granted → exactly that read path in the profile.
        p.grant_read("/tmp/deos_egress");
        let open = p.confinement_for(7);
        assert_eq!(open.read_paths, vec!["/tmp/deos_egress".to_string()]);
    }
}
