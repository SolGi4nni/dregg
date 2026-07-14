//! The type system — a product's TYPE and the admissibility judgment.
//!
//! In fhIR a product's type carries three things
//! (`FHEGG-PRODUCT-ORDER-FRONTIER.md` headline; `DREGGFI-PRIVACY-TIERS.md` §3):
//!
//! 1. the **convex-program shape** ([`ProgramType`]) — its curvature, its
//!    matrices each flagged PUBLIC or PRIVATE, its cones, its size, and any
//!    integer/disjunctive features;
//! 2. the **tier** it is admissible at ([`crate::tier::Tier`]);
//! 3. the **certificate kind** ([`CertKind`]) it compiles to.
//!
//! The typing rule ([`ProgramType::admissible_at`]) is the load-bearing content:
//!
//! > A product type-checks at tier `T` iff its convex-program shape is
//! > `T`-tractable — and the operative boundary is **the matrices, not the
//! > curvature**: the cheap (Dark/FHE) regime needs the constraint/objective
//! > matrices PUBLIC (the FHE matvec is a linear combination with public scalars
//! > over encrypted data — a private matrix destroys the public-matvec
//! > advantage, `PRIVATE-CONVEX-ENGINE.md` precision-correction #4).
//!
//! **Honest scope.** [`ProgramType::admissible_at`] realizes the admissibility
//! *direction* only — **compiles ⇒ runnable at that tier**. The full
//! "admissible **iff** it compiles" is the six-part theorem
//! (`FHEGG-PRODUCT-ORDER-FRONTIER.md`), a NAMED research target for the Lean
//! lane, NOT discharged here. fhIR-0 is the type-checker; the theorem is the
//! target it is being built to justify.

use crate::tier::Tier;
use serde::Serialize;
use std::fmt;

/// PUBLIC vs PRIVATE — the visibility flag on a matrix (the cheap-regime
/// boundary). "Public" = structural, known to everyone (a tick grid, a clearing
/// topology, a mandate's linear constraints). "Private" = private-from-the-world
/// data (a covariance, a hidden constraint matrix). The Dark tier requires
/// public matrices; Shielded lets the solver see private ones.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
pub enum Visibility {
    Public,
    Private,
}

/// The curvature of the objective (`FHEGG-PRODUCT-ORDER-FRONTIER.md` R2.3 typed
/// fragments). fhIR-0 handles `Affine` (LP / aggregation) and `Convex` (QP with
/// `P ⪰ 0`); `Concave`/`Discrete` are named for completeness.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
pub enum Curvature {
    /// Linear objective `cᵀx` — LP / aggregation.
    Affine,
    /// Convex quadratic `½xᵀPx + qᵀx`, `P ⪰ 0` — QP.
    Convex,
    Concave,
    Discrete,
}

/// The approved cone library. fhIR-0 core `𝔎₀` = {zero, nonneg-orthant, box}
/// (`PRIVATE-CONVEX-ENGINE.md` §1.3 core cones); PSD and the exponential cone
/// are **excluded from v0** (PSD needs a hidden eigendecomposition, exp-cone
/// needs exp/log/reciprocal) and are the fhIR-1 frontier.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
pub enum Cone {
    Zero,
    NonNeg,
    Box,
    /// Second-order (SOC) — fhIR-1, not approved in fhIR-0.
    SecondOrder,
    /// Positive-semidefinite — excluded from v0.
    Psd,
    /// Exponential cone — excluded from v0.
    Exp,
}

impl Cone {
    /// The fhIR-0 approved core `𝔎₀`.
    pub fn approved_v0(self) -> bool {
        matches!(self, Cone::Zero | Cone::NonNeg | Cone::Box)
    }
}

/// What role a matrix plays — used only for precise error messages.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
pub enum MatrixRole {
    /// The constraint matrix `A` (`Ax ≤ b` / incidence).
    Constraint,
    /// The quadratic objective matrix `P` (Hessian / covariance).
    Objective,
}

impl fmt::Display for MatrixRole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MatrixRole::Constraint => f.write_str("constraint matrix A"),
            MatrixRole::Objective => f.write_str("objective matrix P (Hessian/covariance)"),
        }
    }
}

/// A matrix in the program, with its visibility (the type-level fact the tier
/// judgment reads).
#[derive(Clone, Copy, Debug, Serialize)]
pub struct MatrixFlag {
    pub role: MatrixRole,
    pub visibility: Visibility,
}

/// An integer / disjunctive feature — the cliff that breaks the continuous cheap
/// regime (`FHEGG-PRODUCT-ORDER-FRONTIER.md` R2.2: AON/FOK/OCO/if-then =
/// integer, break the continuous regime). Any such feature forces Tier 2 Open in
/// fhIR-0 (the compiler does NOT dress it up as a cheaper tier).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
pub enum IntegerFeature {
    /// All-or-none (fill the whole order or none).
    AllOrNone,
    /// Fill-or-kill.
    FillOrKill,
    /// One-cancels-other as an OPTIMIZATION disjunction (not the receipt-XOR
    /// encoding, which is a Tier-1 sequencing trick, `R2.2` encoding #2).
    OcoDisjunction,
}

impl fmt::Display for IntegerFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntegerFeature::AllOrNone => f.write_str("all-or-none fill"),
            IntegerFeature::FillOrKill => f.write_str("fill-or-kill"),
            IntegerFeature::OcoDisjunction => {
                f.write_str("OCO exclusivity as an optimizer disjunction")
            }
        }
    }
}

/// The kind of program a product lowers to — selects the solver + certificate.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
pub enum ProgramKind {
    /// Uniform-price aggregation (fold + one crossing, `T=1`).
    Aggregation,
    /// Volume-max circulation flow-LP `max wᵀf s.t. Af=0, 0≤f≤c`.
    FlowLp,
    /// Quadratic program `min ½xᵀPx+qᵀx s.t. l≤Ax≤u`.
    Qp,
    /// State-price LP for derivative pricing (Price-Cert superhedging LP).
    StatePriceLp,
    /// Snell-envelope LP for American/Bermudan early-exercise pricing — the
    /// optimal-stopping member of the Price-Cert family (LP, not mixed-integer).
    SnellLp,
    /// Discriminatory / pay-as-bid clearing — the gains-from-trade flow-LP
    /// winner-determination (linear, same Cert-F engine) + a pay-as-bid payment.
    Discriminatory,
    /// Welfare-max / Fisher-market equilibrium — the Eisenberg–Gale convex
    /// program `max Σ bᵢ log Uᵢ s.t. supply` (concave, entropic prox).
    WelfareMax,
    /// CFMM optimal routing — `max Σ gᵢ(δᵢ) s.t. Σδ≤Δ` over public pool curves
    /// (concave, water-filling on the marginal price).
    CfmmRouting,
}

/// The certificate a product compiles to (`FHEGG-PRODUCT-ORDER-FRONTIER.md`
/// Price-Cert; `PRIVATE-CONVEX-ENGINE.md` §2.3 Cert-F, §3 CertQp).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
pub enum CertKind {
    /// The conserving uniform-price allocation certificate — the `T=1`
    /// degenerate of Cert-F (Σ-balance = the duality gap of the exact clearing,
    /// `exact_clears_iff`). Named separately because the aggregation clearing
    /// carries a conservation certificate, not a primal-dual `(f,π,s)` triple.
    Aggregation,
    /// The primal-dual flow-LP certificate `(f,π,s)`
    /// (`fhegg_solver::cert::CertF`).
    CertF,
    /// The QP KKT-residual certificate `(x,y)` (`fhegg_solver::qp::CertQp`).
    CertQp,
    /// The state-price / superhedging LP certificate (Price-Cert). Its shape is
    /// typed in fhIR-0; a dedicated runner is the fhIR-1 lane.
    PriceCert,
    /// The Fisher-market competitive-equilibrium certificate `(x, p)` — the
    /// Eisenberg–Gale KKT witness (`fhegg_solver::fisher::CertEq`). Bilinear in
    /// the witness (`βᵢuᵢⱼ`, `xᵢⱼpⱼ`), `O(n·g)`.
    CertEq,
    /// The CFMM routing certificate `(δ, λ)` — the water-filling KKT witness
    /// (`fhegg_solver::cfmm::CertRoute`). Nonlinear in the witness (`gᵢ'`), `O(N)`.
    CertRoute,
}

/// The extracted convex-program TYPE — what the tier judgment reads. This is the
/// "shape" the six-part admissibility theorem quantifies over.
#[derive(Clone, Debug, Serialize)]
pub struct ProgramType {
    pub kind: ProgramKind,
    pub curvature: Curvature,
    /// The matrices, each flagged public/private.
    pub matrices: Vec<MatrixFlag>,
    /// The cones the program uses.
    pub cones: Vec<Cone>,
    /// Integer/disjunctive features (empty = continuous cheap regime).
    pub integer_features: Vec<IntegerFeature>,
    /// Problem size: `N` orders for aggregation, `m` edges/vars otherwise. Used
    /// for the FHE (Dark) envelope check.
    pub size: usize,
    /// The certificate this shape carries.
    pub cert: CertKind,
}

/// The FHE (Dark) size envelope, per kind. From `DREGGFI-PRIVACY-TIERS.md` §1
/// ("N ≈ 32–512 orders per pair at minute cadence"): uniform-price aggregation
/// packs to a few-hundred orders; a small circulation / state-price LP stays in
/// the cheap FHE half only at small `m`. These are the honest Stage-1 bounds —
/// deliberately conservative, upgraded on the FHE trajectory.
pub const DARK_AGGREGATION_ENVELOPE: usize = 512;
pub const DARK_LP_ENVELOPE: usize = 64;

impl ProgramType {
    /// The first PRIVATE matrix, if any (with its role) — the Dark-tier
    /// obstruction.
    pub fn private_matrix(&self) -> Option<MatrixRole> {
        self.matrices
            .iter()
            .find(|m| m.visibility == Visibility::Private)
            .map(|m| m.role)
    }

    /// The first unapproved (fhIR-0) cone, if any.
    pub fn unapproved_cone(&self) -> Option<Cone> {
        self.cones.iter().copied().find(|c| !c.approved_v0())
    }

    /// The first integer/disjunctive feature, if any.
    pub fn integer_feature(&self) -> Option<IntegerFeature> {
        self.integer_features.first().copied()
    }

    /// Whether the size is inside the FHE (Dark) envelope for this kind. A QP
    /// (quadratic prox / PSD) is never in the aggregation core, so it is treated
    /// as out-of-envelope regardless of size (the size check is moot — the
    /// quadratic-objective check rejects it first).
    fn within_dark_envelope(&self) -> bool {
        match self.kind {
            ProgramKind::Aggregation => self.size <= DARK_AGGREGATION_ENVELOPE,
            ProgramKind::FlowLp
            | ProgramKind::StatePriceLp
            | ProgramKind::SnellLp
            | ProgramKind::Discriminatory => self.size <= DARK_LP_ENVELOPE,
            ProgramKind::Qp => false,
            // WelfareMax / CfmmRouting have a Concave (log / rational) objective,
            // so the curvature check rejects them at Dark before this is reached;
            // the bound is moot but kept exhaustive.
            ProgramKind::WelfareMax | ProgramKind::CfmmRouting => self.size <= DARK_LP_ENVELOPE,
        }
    }

    /// **The typing judgment.** Is this shape admissible at `tier`? `Ok(())` = it
    /// type-checks (and hence — the admissibility DIRECTION — is runnable at
    /// that tier); `Err` names the precise structural obstruction.
    ///
    /// The judgment is monotone by construction: `Dark` first requires the
    /// `Shielded` obligations, so Dark-admissible ⇒ Shielded-admissible ⇒
    /// Open-admissible (`DREGGFI-PRIVACY-TIERS.md` §3).
    pub fn admissible_at(&self, tier: Tier) -> Result<(), TypeError> {
        match tier {
            // Public-general: anything expressible to the general matcher — in
            // fhIR-0 every typed shape is (integrality/private data are fine when
            // everything is public and general).
            Tier::Open => Ok(()),

            // STARK-tractable: a bounded oblivious convex circuit. The solver
            // sees plaintext, so PRIVATE matrices are fine here (private-from-the
            // -world, not private-from-the-solver). What breaks it: an integer/
            // disjunctive feature (not oblivious/continuous) or an unapproved
            // cone.
            Tier::Shielded => {
                if let Some(feat) = self.integer_feature() {
                    return Err(TypeError::IntegerFeature {
                        feature: feat,
                        tier,
                    });
                }
                if let Some(cone) = self.unapproved_cone() {
                    return Err(TypeError::UnapprovedCone { cone, tier });
                }
                Ok(())
            }

            // FHE-tractable: everything Shielded needs, PLUS (a) all matrices
            // PUBLIC (the FHE matvec needs public structure — the operative
            // boundary), (b) an affine/aggregation objective (no quadratic /
            // PSD prox — excluded from FHE v0), (c) inside the FHE size envelope.
            Tier::Dark => {
                self.admissible_at(Tier::Shielded)?; // Dark ⇒ Shielded prerequisites
                if let Some(role) = self.private_matrix() {
                    return Err(TypeError::PrivateMatrix { role, tier });
                }
                if self.curvature == Curvature::Convex {
                    return Err(TypeError::QuadraticObjective { tier });
                }
                if self.curvature == Curvature::Concave {
                    return Err(TypeError::EntropicObjective { tier });
                }
                if !self.within_dark_envelope() {
                    return Err(TypeError::SizeExceedsEnvelope {
                        size: self.size,
                        envelope: match self.kind {
                            ProgramKind::Aggregation => DARK_AGGREGATION_ENVELOPE,
                            _ => DARK_LP_ENVELOPE,
                        },
                        tier,
                    });
                }
                Ok(())
            }
        }
    }
}

/// The precise reason a product fails to type-check at a tier. Every variant
/// names the *structural* obstruction — the compiler never rejects vaguely.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub enum TypeError {
    /// A matrix is private → the FHE matvec needs public structure → not
    /// admissible at this (Dark) tier.
    PrivateMatrix { role: MatrixRole, tier: Tier },
    /// The objective is a convex quadratic → PSD/quadratic prox is outside the
    /// FHE v0 aggregation core → not Dark-admissible.
    QuadraticObjective { tier: Tier },
    /// The objective is concave-nonlinear (`log` welfare / rational CFMM output)
    /// → the entropic/mirror-descent prox is outside the FHE v0 aggregation core
    /// (exp/log/reciprocal) → not Dark-admissible (Shielded is fine).
    EntropicObjective { tier: Tier },
    /// An unapproved cone (SOC/PSD/exp) → outside fhIR-0's cone library.
    UnapprovedCone { cone: Cone, tier: Tier },
    /// An integer/disjunctive feature → breaks the continuous oblivious regime →
    /// Tier 2 Open only.
    IntegerFeature { feature: IntegerFeature, tier: Tier },
    /// Size exceeds the FHE envelope at the Dark tier.
    SizeExceedsEnvelope {
        size: usize,
        envelope: usize,
        tier: Tier,
    },
    /// The author claimed a MORE-private tier than the math delivers. Carries
    /// the honest tier and the underlying obstruction.
    OverClaimsTier {
        claimed: Tier,
        honest: Tier,
        because: Box<TypeError>,
    },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::PrivateMatrix { role, tier } => write!(
                f,
                "requires a private {role} → the FHE matvec needs PUBLIC matrices → not {}-admissible",
                tier.short(),
            ),
            TypeError::QuadraticObjective { tier } => write!(
                f,
                "convex-quadratic objective (PSD/quadratic prox) is outside the FHE v0 aggregation core → not {}-admissible",
                tier.short(),
            ),
            TypeError::EntropicObjective { tier } => write!(
                f,
                "concave-nonlinear objective (log-welfare / rational CFMM output; entropic/mirror-descent prox = exp/log/reciprocal) is outside the FHE v0 aggregation core → not {}-admissible",
                tier.short(),
            ),
            TypeError::UnapprovedCone { cone, tier } => write!(
                f,
                "uses the unapproved cone {cone:?} (fhIR-0 core = zero/nonneg/box) → not {}-admissible",
                tier.short(),
            ),
            TypeError::IntegerFeature { feature, tier } => write!(
                f,
                "uses {feature} — an integer/disjunctive constraint that breaks the continuous oblivious regime → not {}-admissible (Tier 2 Open only)",
                tier.short(),
            ),
            TypeError::SizeExceedsEnvelope { size, envelope, tier } => write!(
                f,
                "size {size} exceeds the FHE {} envelope ({envelope}) → runs at the next tier (scale is the FHE frontier)",
                tier.short(),
            ),
            TypeError::OverClaimsTier { claimed, honest, because } => write!(
                f,
                "OVER-CLAIMS PRIVACY: promises {} but the math only delivers {} — {because}",
                claimed.short(), honest.short(),
            ),
        }
    }
}

impl std::error::Error for TypeError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn public_affine(kind: ProgramKind, size: usize, cert: CertKind) -> ProgramType {
        ProgramType {
            kind,
            curvature: Curvature::Affine,
            matrices: vec![MatrixFlag {
                role: MatrixRole::Constraint,
                visibility: Visibility::Public,
            }],
            cones: vec![Cone::Zero, Cone::Box],
            integer_features: vec![],
            size,
            cert,
        }
    }

    #[test]
    fn public_small_aggregation_is_dark() {
        let t = public_affine(ProgramKind::Aggregation, 8, CertKind::Aggregation);
        assert!(t.admissible_at(Tier::Dark).is_ok());
        assert!(t.admissible_at(Tier::Shielded).is_ok());
        assert!(t.admissible_at(Tier::Open).is_ok());
    }

    #[test]
    fn quadratic_is_not_dark_but_is_shielded() {
        let mut t = public_affine(ProgramKind::Qp, 6, CertKind::CertQp);
        t.curvature = Curvature::Convex;
        assert!(matches!(
            t.admissible_at(Tier::Dark),
            Err(TypeError::QuadraticObjective { .. })
        ));
        assert!(t.admissible_at(Tier::Shielded).is_ok());
    }

    #[test]
    fn private_matrix_is_not_dark() {
        let mut t = public_affine(ProgramKind::FlowLp, 8, CertKind::CertF);
        t.matrices[0].visibility = Visibility::Private;
        assert!(matches!(
            t.admissible_at(Tier::Dark),
            Err(TypeError::PrivateMatrix { .. })
        ));
        // ...but Shielded is fine (solver sees plaintext).
        assert!(t.admissible_at(Tier::Shielded).is_ok());
    }

    #[test]
    fn integer_feature_forces_open() {
        let mut t = public_affine(ProgramKind::Aggregation, 8, CertKind::Aggregation);
        t.integer_features = vec![IntegerFeature::AllOrNone];
        assert!(t.admissible_at(Tier::Dark).is_err());
        assert!(matches!(
            t.admissible_at(Tier::Shielded),
            Err(TypeError::IntegerFeature { .. })
        ));
        assert!(t.admissible_at(Tier::Open).is_ok());
    }

    #[test]
    fn oversize_lp_falls_off_dark_to_shielded() {
        let t = public_affine(ProgramKind::FlowLp, DARK_LP_ENVELOPE + 1, CertKind::CertF);
        assert!(matches!(
            t.admissible_at(Tier::Dark),
            Err(TypeError::SizeExceedsEnvelope { .. })
        ));
        assert!(t.admissible_at(Tier::Shielded).is_ok());
    }

    #[test]
    fn unapproved_cone_rejected_even_shielded() {
        let mut t = public_affine(ProgramKind::FlowLp, 8, CertKind::CertF);
        t.cones.push(Cone::Psd);
        assert!(matches!(
            t.admissible_at(Tier::Shielded),
            Err(TypeError::UnapprovedCone {
                cone: Cone::Psd,
                ..
            })
        ));
        assert!(t.admissible_at(Tier::Open).is_ok());
    }
}
