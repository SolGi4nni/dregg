//! # The dreggic deployer-gate
//!
//! Anti-scam launchpads have two independent surfaces to defend:
//!
//! 1. **The mechanism** (already ours): `chain/contracts/launchpad/DreggLaunchpad.sol`
//!    makes the *contract* unruggable — disclosed supply that must close, a
//!    single one-shot mint, sealed commit→reveal, uniform-price clearing proved
//!    in Lean, a creator vesting-lock, and a solvency-floored graduated pool.
//!    The contract *cannot* rug.
//!
//! 2. **The deployer** (this crate): *who* is allowed to register a launch at
//!    all. `registerLaunch` today gates *bidders* (`ILaunchEligibility`, line
//!    274 of `DreggLaunchpad.sol`) but not the *deployer* — anyone can create a
//!    launch. The community insight (ember): "launchpads should tokengate or
//!    socially gatekeep the deployers; thousands of scam coins would disappear."
//!
//! This crate builds surface (2) the *dreggic* way — **gate the deployer
//! privately**. A deployer must present a **deploy capability**: an attenuable,
//! proof-carrying token (a real [`dregg_macaroon::Macaroon`]) that the operator
//! issues only when a **gate arm** is satisfied, and that the launchpad
//! re-checks at deploy time. The through-line the whole system is built on —
//! *"a turn = the exercise of an attenuable proof-carrying token over owned
//! state"* — is exactly this: **deploying is a turn, and the deploy capability
//! is the token.**
//!
//! ## The pluggable gate arms (the operator picks one or a combination)
//!
//! - [`GateArm::Bond`] — economic. The deployer stakes a conduct bond,
//!   slashable by the launchpad fraud-proof on a rug. Nothing to fake: a
//!   scammer must put real money at risk that they lose if they rug.
//! - [`GateArm::Interview`] — social, **the marquee**. The deployer sits a
//!   *structured interview with a hard-to-convince Claude Opus 4.8*, briefed to
//!   probe for rug-intent, vaporware, and scam-signals and to refuse to be
//!   moved by hype (see `interview/interviewer-prompt.md` + the two captured
//!   runs in `interview/runs/` — real Opus output, produced once, offline; a
//!   LIVE per-applicant interview is the named wire-later, see
//!   [`interview`]'s honest-scope note). A PASS issues the capability. This beats a
//!   whitelist/token-gate because a scammer cannot hype their way past a skeptic
//!   asking real questions, and it does **not doxx** — it interrogates the
//!   *project*, not the person's KYC.
//! - [`GateArm::Audit`] — the token spec cleared the dregg audit pipeline
//!   (`tools/dregg-audit`), referenced by report hash.
//!
//! ## Gate the deployer *without doxxing* (the differentiator)
//!
//! The [`GateArm::Interview`] arm carries only a **hiding commitment** to the
//! verdict (see [`private`]). The launchpad authorizes on membership of that
//! commitment in the trusted *passed-and-attested* set — it learns **only
//! "gated: true"**, never the interview content, the deployer's identity, or
//! *which* interview. A scammer cannot produce the commitment (they failed the
//! interview); an honest builder is not KYC-doxxed. The full *unlinkable* ZK
//! (a membership proof so the gate does not even see which commitment, plus a
//! zkTLS/DECO attestation that the interview happened with the *real* Opus
//! endpoint and passed) is the honestly-named weld reusing `DreggCredentialGate`
//! (on-chain) and `zkoracle-prove` (the repo's DECO/TLSNotary carrier) — see
//! [`private::zktls`].

use std::collections::HashSet;

use dregg_macaroon::{Access, Caveat, CaveatError, Macaroon, MacaroonError, WireCaveat};
use sha2::{Digest, Sha256};

pub mod interview;
pub mod private;

// ─── Caveat type IDs (user-defined range, 48+; see macaroon/src/caveat.rs) ───

/// Binds a capability to one launch's parameters (attenuation scope).
pub const CAV_DEPLOY_SCOPE: u16 = 48;
/// Validity window: the capability is void after `not_after`.
pub const CAV_DEPLOY_EXPIRY: u16 = 49;
/// The gate arm the capability was issued on, re-checked at deploy time.
pub const CAV_DEPLOY_ARM: u16 = 50;

/// A stable per-deployer identifier (an address, pubkey hash, or opaque handle).
/// It is the macaroon's key-id; it is NOT an identity to be doxxed — under the
/// private arm it can itself be an unlinkable per-launch pseudonym.
pub type DeployerId = [u8; 32];

/// A commitment to a launch's disclosed parameters — the same
/// `keccak(abi.encode(Schedule))` the launchpad commits at `registerLaunch`
/// (`DreggLaunchpad.sol:238`), here as an opaque 32-byte scope handle.
pub type LaunchParamsHash = [u8; 32];

// ─── The gate arms ───────────────────────────────────────────────────────────

/// The pluggable condition that issues (and re-authorizes) a deploy capability.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateArm {
    /// (a) Economic: the deployer must hold at least `min_bond_wei` staked in
    /// the conduct bond, slashable on a proven rug.
    Bond { min_bond_wei: u128 },
    /// (b) Social (**marquee**): a hard-to-convince Opus-4.8 interview PASS,
    /// referenced by a hiding [`private::VerdictCommitment`] so the arm reveals
    /// nothing about the interview or the deployer.
    Interview { verdict_commitment: [u8; 32] },
    /// (c) Audit: the token spec cleared `dregg-audit`, referenced by report hash.
    Audit { report_hash: [u8; 32] },
}

impl GateArm {
    fn encode(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(33);
        match self {
            GateArm::Bond { min_bond_wei } => {
                v.push(0u8);
                v.extend_from_slice(&min_bond_wei.to_le_bytes());
            }
            GateArm::Interview { verdict_commitment } => {
                v.push(1u8);
                v.extend_from_slice(verdict_commitment);
            }
            GateArm::Audit { report_hash } => {
                v.push(2u8);
                v.extend_from_slice(report_hash);
            }
        }
        v
    }

    fn decode(body: &[u8]) -> Result<Self, GateError> {
        match body.first() {
            Some(0) if body.len() == 17 => {
                let mut b = [0u8; 16];
                b.copy_from_slice(&body[1..17]);
                Ok(GateArm::Bond {
                    min_bond_wei: u128::from_le_bytes(b),
                })
            }
            Some(1) if body.len() == 33 => {
                let mut c = [0u8; 32];
                c.copy_from_slice(&body[1..33]);
                Ok(GateArm::Interview {
                    verdict_commitment: c,
                })
            }
            Some(2) if body.len() == 33 => {
                let mut h = [0u8; 32];
                h.copy_from_slice(&body[1..33]);
                Ok(GateArm::Audit { report_hash: h })
            }
            _ => Err(GateError::MalformedCaveat),
        }
    }
}

// ─── The live gate context (bond ledger / trusted verdicts / audit registry) ──

/// The operator's live gating state. It is consulted at BOTH issuance time
/// (mint only if gated now) and deploy time (re-check, so a bond slashed or an
/// attestation revoked *after* issuance still fails-closed).
#[derive(Clone, Debug, Default)]
pub struct GateContext {
    /// Live conduct-bond ledger: deployer → wei currently staked (slashing
    /// reduces this).
    pub bonds: std::collections::HashMap<DeployerId, u128>,
    /// Commitments of interviews that PASSED and are attested (see [`private`]).
    /// A revoked/expired attestation is removed from this set.
    pub trusted_interview_commitments: HashSet<[u8; 32]>,
    /// Report hashes that CLEARED the dregg audit pipeline.
    pub audit_registry: HashSet<[u8; 32]>,
}

impl GateContext {
    /// Is `arm` satisfied for `deployer` under the current live state?
    fn satisfied(&self, deployer: &DeployerId, arm: &GateArm) -> bool {
        match arm {
            GateArm::Bond { min_bond_wei } => {
                self.bonds.get(deployer).copied().unwrap_or(0) >= *min_bond_wei
            }
            GateArm::Interview { verdict_commitment } => self
                .trusted_interview_commitments
                .contains(verdict_commitment),
            GateArm::Audit { report_hash } => self.audit_registry.contains(report_hash),
        }
    }
}

// ─── The per-deploy access request (what caveats are cleared against) ─────────

/// The request a deploy capability is authorized against. Owns its data
/// (`Access: Any` requires `'static`), snapshotted from [`GateContext`] for the
/// one deployer + scope being checked.
pub struct DeployRequest {
    now: i64,
    deployer_bond_wei: u128,
    interview_ok: HashSet<[u8; 32]>,
    audit_ok: HashSet<[u8; 32]>,
    launch_params_hash: LaunchParamsHash,
}

impl DeployRequest {
    /// Snapshot the live context for one `deployer` deploying `launch_params_hash`.
    pub fn new(
        now: i64,
        deployer: &DeployerId,
        launch_params_hash: LaunchParamsHash,
        ctx: &GateContext,
    ) -> Self {
        DeployRequest {
            now,
            deployer_bond_wei: ctx.bonds.get(deployer).copied().unwrap_or(0),
            interview_ok: ctx.trusted_interview_commitments.clone(),
            audit_ok: ctx.audit_registry.clone(),
            launch_params_hash,
        }
    }
}

impl Access for DeployRequest {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn now(&self) -> i64 {
        self.now
    }
}

// ─── The caveats (real `dregg_macaroon::Caveat` implementations) ──────────────

/// Binds the capability to exactly one launch's disclosed parameters. Adding a
/// *tighter* scope is valid attenuation; the deploy request must match.
pub struct ScopeCaveat {
    pub launch_params_hash: LaunchParamsHash,
}

impl Caveat for ScopeCaveat {
    fn caveat_type(&self) -> u16 {
        CAV_DEPLOY_SCOPE
    }
    fn name(&self) -> &str {
        "deploy-scope"
    }
    fn prohibits(&self, access: &dyn Access) -> Result<(), CaveatError> {
        let req = access
            .as_any()
            .downcast_ref::<DeployRequest>()
            .ok_or_else(|| CaveatError::Prohibited("deploy-scope: wrong access type".into()))?;
        if req.launch_params_hash == self.launch_params_hash {
            Ok(())
        } else {
            Err(CaveatError::Prohibited(
                "deploy-scope: capability not issued for this launch".into(),
            ))
        }
    }
    fn encode_body(&self) -> Vec<u8> {
        self.launch_params_hash.to_vec()
    }
}

/// Validity window. The capability is void once `access.now() > not_after`.
pub struct ExpiryCaveat {
    pub not_after: i64,
}

impl Caveat for ExpiryCaveat {
    fn caveat_type(&self) -> u16 {
        CAV_DEPLOY_EXPIRY
    }
    fn name(&self) -> &str {
        "deploy-expiry"
    }
    fn prohibits(&self, access: &dyn Access) -> Result<(), CaveatError> {
        if access.now() <= self.not_after {
            Ok(())
        } else {
            Err(CaveatError::Prohibited(
                "deploy-expiry: capability expired".into(),
            ))
        }
    }
    fn encode_body(&self) -> Vec<u8> {
        self.not_after.to_le_bytes().to_vec()
    }
}

/// The gate arm, re-checked at deploy time against the live snapshot. This is
/// the tooth: even a perfectly-formed capability fails if the bond was slashed,
/// the interview attestation revoked, or the audit withdrawn after issuance.
pub struct ArmCaveat {
    pub arm: GateArm,
}

impl Caveat for ArmCaveat {
    fn caveat_type(&self) -> u16 {
        CAV_DEPLOY_ARM
    }
    fn name(&self) -> &str {
        "deploy-arm"
    }
    fn prohibits(&self, access: &dyn Access) -> Result<(), CaveatError> {
        let req = access
            .as_any()
            .downcast_ref::<DeployRequest>()
            .ok_or_else(|| CaveatError::Prohibited("deploy-arm: wrong access type".into()))?;
        let ok = match &self.arm {
            GateArm::Bond { min_bond_wei } => req.deployer_bond_wei >= *min_bond_wei,
            GateArm::Interview { verdict_commitment } => {
                req.interview_ok.contains(verdict_commitment)
            }
            GateArm::Audit { report_hash } => req.audit_ok.contains(report_hash),
        };
        if ok {
            Ok(())
        } else {
            Err(CaveatError::Prohibited(
                "deploy-arm: gate condition not satisfied at deploy time".into(),
            ))
        }
    }
    fn encode_body(&self) -> Vec<u8> {
        self.arm.encode()
    }
}

// ─── Errors ───────────────────────────────────────────────────────────────────

#[derive(Debug, thiserror::Error)]
pub enum GateError {
    /// The deployer does not satisfy the gate arm — issuance refused. A scammer
    /// who failed the interview / posted no bond / failed audit lands here.
    #[error("deployer is not gated for the requested arm (issuance refused)")]
    NotGated,
    /// The presented capability failed macaroon verification (forged, tampered
    /// tail, wrong root key, or removed caveat).
    #[error("capability failed cryptographic verification: {0}")]
    BadCapability(#[from] MacaroonError),
    /// The capability verified, but a caveat is not satisfied by the deploy
    /// request (expired, wrong scope, or gate condition no longer holds).
    #[error("capability rejected by caveat: {0}")]
    CaveatRejected(String),
    /// A caveat body did not decode.
    #[error("malformed deploy caveat")]
    MalformedCaveat,
}

// ─── The gate ─────────────────────────────────────────────────────────────────

/// The launchpad operator's deployer-gate. Holds the issuing root key.
pub struct DeployerGate {
    root_key: [u8; 32],
    location: String,
}

impl DeployerGate {
    pub fn new(root_key: [u8; 32], location: impl Into<String>) -> Self {
        DeployerGate {
            root_key,
            location: location.into(),
        }
    }

    /// **Issuance gate.** Mint a deploy capability for `deployer`, scoped to
    /// `launch_params_hash`, on `arm` — but ONLY if `arm` is satisfied under the
    /// live `ctx` right now. A deployer who is not gated gets [`GateError::NotGated`]
    /// and no token; there is no capability to present later.
    pub fn issue(
        &self,
        deployer: DeployerId,
        arm: GateArm,
        launch_params_hash: LaunchParamsHash,
        not_after: i64,
        ctx: &GateContext,
    ) -> Result<Macaroon, GateError> {
        if !ctx.satisfied(&deployer, &arm) {
            return Err(GateError::NotGated);
        }
        let mut mac = Macaroon::new(&self.root_key, deployer.to_vec(), self.location.clone());
        mac.add_first_party(&ScopeCaveat { launch_params_hash });
        mac.add_first_party(&ArmCaveat { arm });
        mac.add_first_party(&ExpiryCaveat { not_after });
        Ok(mac)
    }

    /// **Authorization gate** (the launchpad's `registerLaunch` hook). Verify the
    /// presented capability's HMAC chain against the issuing root key (rejects
    /// forged / tampered / caveat-stripped tokens), then clear every first-party
    /// caveat against the live deploy request (rejects expired / wrong-scope /
    /// no-longer-gated). Returns `Ok(())` iff the deploy is authorized.
    ///
    /// The intended 3-line hook in `DreggLaunchpad.registerLaunch`, mirroring the
    /// bidder gate at line 274:
    /// ```solidity
    /// if (address(deployerGate) != address(0)
    ///     && !deployerGate.authorizeDeploy(msg.sender, scheduleCommit, capability))
    ///     revert DeployerNotGated(msg.sender);
    /// ```
    pub fn authorize_deploy(
        &self,
        capability: &Macaroon,
        request: &DeployRequest,
    ) -> Result<(), GateError> {
        // 1. Cryptographic integrity: replay the HMAC chain. A forged token, a
        //    tampered tail, a wrong root key, or a removed caveat all fail here.
        let cleared = capability.verify(&self.root_key, &[])?;

        // 2. Clear every first-party caveat against the live request.
        for wire in cleared.first_party_caveats() {
            self.clear_one(wire, request)?;
        }
        Ok(())
    }

    fn clear_one(&self, wire: &WireCaveat, request: &DeployRequest) -> Result<(), GateError> {
        let result = match wire.caveat_type {
            CAV_DEPLOY_SCOPE => {
                if wire.body.len() != 32 {
                    return Err(GateError::MalformedCaveat);
                }
                let mut h = [0u8; 32];
                h.copy_from_slice(&wire.body);
                ScopeCaveat {
                    launch_params_hash: h,
                }
                .prohibits(request)
            }
            CAV_DEPLOY_EXPIRY => {
                if wire.body.len() != 8 {
                    return Err(GateError::MalformedCaveat);
                }
                let mut b = [0u8; 8];
                b.copy_from_slice(&wire.body);
                ExpiryCaveat {
                    not_after: i64::from_le_bytes(b),
                }
                .prohibits(request)
            }
            CAV_DEPLOY_ARM => {
                let arm = GateArm::decode(&wire.body)?;
                ArmCaveat { arm }.prohibits(request)
            }
            // Unknown caveat type: fail-closed. A capability we cannot fully
            // interpret must never be authorized.
            other => {
                return Err(GateError::CaveatRejected(format!(
                    "unknown caveat type {other} — fail-closed"
                )))
            }
        };
        result.map_err(|e| GateError::CaveatRejected(e.to_string()))
    }
}

/// Domain-separated commitment to a launch's disclosed schedule bytes — a
/// convenience mirroring `keccak(abi.encode(Schedule))` for the PoC (SHA-256).
pub fn launch_params_hash(schedule_bytes: &[u8]) -> LaunchParamsHash {
    let mut h = Sha256::new();
    h.update(b"dregg-deployer-gate/launch-params/v1");
    h.update(schedule_bytes);
    h.finalize().into()
}
