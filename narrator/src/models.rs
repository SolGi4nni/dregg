//! The MODEL PRICE REGISTRY — the one place a model's cost is pinned.
//!
//! **The security property: the ledger refuses any model it has no pinned price for.** You
//! cannot enforce a budget on a model whose cost you do not know — so an unregistered model id
//! yields [`crate::NarratorError::UnpricedModel`], fail-closed, with NO network call. Adding a
//! model is a deliberate act: pin its rate here (or override via env), with an honest
//! [`PriceSource`].

use std::collections::BTreeMap;

use crate::ledger::{env_f64, PriceSource, Pricing};

/// The DEFAULT model — Anthropic Claude Haiku 4.5 on Bedrock, via its INFERENCE-PROFILE id.
/// The bare `anthropic.claude-haiku-4-5-20251001-v1:0` errors with a ValidationException; the
/// `us.` prefix is required (the same trap as the Nova models).
pub const CLAUDE_HAIKU_4_5: &str = "us.anthropic.claude-haiku-4-5-20251001-v1:0";
/// The cheap, price-VERIFIED fallback — Amazon Nova Lite (inference-profile id).
pub const NOVA_2_LITE: &str = "us.amazon.nova-2-lite-v1:0";
/// Amazon Nova Pro — available, price-verified, NOT the default (its prose isn't better than
/// Lite's). Works without the `us.` prefix.
pub const NOVA_PRO: &str = "amazon.nova-pro-v1:0";

/// The model the narrator uses first when nothing overrides it.
pub const DEFAULT_MODEL: &str = CLAUDE_HAIKU_4_5;

/// A pinned price book. Cheap to clone.
#[derive(Clone, Debug)]
pub struct ModelRegistry {
    entries: BTreeMap<String, Pricing>,
}

impl ModelRegistry {
    /// The built-in registry (with any `DREGG_NARRATOR_PRICE_*` env override applied to the
    /// default model's entry).
    pub fn builtin() -> ModelRegistry {
        let mut entries = BTreeMap::new();

        // DEFAULT — Claude Haiku 4.5. Haiku 4.5 has NO machine-readable AWS price (the bulk
        // Bedrock price list + the Pricing API + the public pricing page all lack it, checked
        // 2026-07-10). We pin the PUBLISHED Claude Sonnet-tier rates ($2/M in, $10/M out), which
        // strictly dominate Haiku 4.5 — a GUARANTEED upper bound. The ceiling can only trip
        // early. Tighten once a verified rate is obtained from the Bedrock console.
        entries.insert(
            CLAUDE_HAIKU_4_5.to_string(),
            Pricing {
                input_per_1k: 0.002,
                output_per_1k: 0.010,
                source: PriceSource::ConservativeUpperBound {
                    rationale: "Haiku 4.5 has no machine-readable AWS price (bulk price list + \
                                Pricing API + public pricing page all lack it, checked 2026-07-10). \
                                Pinned to the PUBLISHED Claude Sonnet-tier rates ($2/M in, $10/M \
                                out), which strictly dominate Haiku 4.5 — a guaranteed upper bound. \
                                Tighten once a verified Bedrock-console rate is obtained."
                        .to_string(),
                },
            },
        );

        // Nova Lite — VERIFIED cheap fallback.
        entries.insert(
            NOVA_2_LITE.to_string(),
            Pricing {
                input_per_1k: 0.00006,
                output_per_1k: 0.00024,
                source: PriceSource::Verified {
                    api: "AWS Pricing API + bulk price list, us-east-1".to_string(),
                    date: "2026-07-10".to_string(),
                },
            },
        );

        // Nova Pro — VERIFIED, available, not the default.
        entries.insert(
            NOVA_PRO.to_string(),
            Pricing {
                input_per_1k: 0.0008,
                output_per_1k: 0.0032,
                source: PriceSource::Verified {
                    api: "AWS Pricing API + bulk price list, us-east-1".to_string(),
                    date: "2026-07-10".to_string(),
                },
            },
        );

        let mut reg = ModelRegistry { entries };
        reg.apply_env_override();
        reg
    }

    /// An empty registry — an operator must register every model.
    pub fn empty() -> ModelRegistry {
        ModelRegistry {
            entries: BTreeMap::new(),
        }
    }

    /// Pin `model`'s price (overwriting any existing entry).
    pub fn register(&mut self, model: impl Into<String>, pricing: Pricing) {
        self.entries.insert(model.into(), pricing);
    }

    /// The pinned price for `model`, or `None` (→ an [`crate::NarratorError::UnpricedModel`]
    /// refusal at the metered layer).
    pub fn pricing_for(&self, model: &str) -> Option<Pricing> {
        self.entries.get(model).cloned()
    }

    /// If `DREGG_NARRATOR_PRICE_INPUT_PER_1K` / `_OUTPUT_PER_1K` are set, pin the rate for the
    /// ACTIVE model — `DREGG_NARRATOR_MODEL` when set (e.g. a Chutes catalog id on the OpenAI
    /// path), else [`DEFAULT_MODEL`] — marked as an operator-set rate.
    ///
    /// This is how an arbitrary hosted model (one the registry has no built-in price for) gets a
    /// price so the metered layer will run it: name it in `DREGG_NARRATOR_MODEL` and pin both rates.
    /// A missing rate falls back to the model's existing built-in entry; if the model has NO built-in
    /// entry and either rate is left unset, the entry is NOT created — the model stays unpriced and
    /// the metered layer refuses it fail-closed (never priced at a silent zero).
    fn apply_env_override(&mut self) {
        let (in_o, out_o) = (
            env_f64("DREGG_NARRATOR_PRICE_INPUT_PER_1K"),
            env_f64("DREGG_NARRATOR_PRICE_OUTPUT_PER_1K"),
        );
        let target = std::env::var("DREGG_NARRATOR_MODEL")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| DEFAULT_MODEL.to_string());
        self.apply_price_override(&target, in_o, out_o);
    }

    /// The PURE rule behind [`ModelRegistry::apply_env_override`]: pin `target`'s rate from the
    /// supplied overrides, falling back per-axis to `target`'s existing entry.
    ///
    /// Public + env-free so the operator-override path is testable for an ARBITRARY model id —
    /// e.g. an attested Chutes `…-TEE` model, which has no built-in entry and is priced per token
    /// like its non-TEE twin (Chutes charges no confidential-compute premium). Both rates must be
    /// supplied for such a model or it stays UNPRICED and the metered layer refuses it fail-closed.
    pub fn apply_price_override(
        &mut self,
        target: &str,
        input_override: Option<f64>,
        output_override: Option<f64>,
    ) {
        if input_override.is_none() && output_override.is_none() {
            return;
        }
        let target = target.trim().to_string();
        if target.is_empty() {
            return;
        }
        let (in_o, out_o) = (input_override, output_override);

        let base = self.entries.get(&target).cloned();
        let input = in_o.or_else(|| base.as_ref().map(|b| b.input_per_1k));
        let output = out_o.or_else(|| base.as_ref().map(|b| b.output_per_1k));
        // Only pin when BOTH rates are known — a half-specified price on a new model would silently
        // charge zero on one axis. Leave it unpriced (fail-closed) otherwise.
        if let (Some(input_per_1k), Some(output_per_1k)) = (input, output) {
            self.entries.insert(
                target,
                Pricing {
                    input_per_1k,
                    output_per_1k,
                    // Honest provenance: an operator-set rate is trusted at their discretion and is
                    // NOT necessarily an upper bound — do not launder it as `ConservativeUpperBound`.
                    source: PriceSource::OperatorOverride,
                },
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An attested Chutes `-TEE` model has no built-in entry. The documented operator path —
    /// `DREGG_NARRATOR_MODEL=<id>` + BOTH `DREGG_NARRATOR_PRICE_*_PER_1K` — must price it, or the
    /// metered layer refuses every attested call as `UnpricedModel`.
    #[test]
    fn tee_model_is_priceable_through_the_operator_override() {
        const TEE: &str = "Qwen/Qwen3-32B-TEE";
        let mut reg = ModelRegistry::builtin();
        assert!(
            reg.pricing_for(TEE).is_none(),
            "no invented built-in price for a -TEE model"
        );

        reg.apply_price_override(TEE, Some(0.0003), Some(0.0009));
        let p = reg.pricing_for(TEE).expect("operator-priced -TEE model");
        assert_eq!(p.input_per_1k, 0.0003);
        assert_eq!(p.output_per_1k, 0.0009);
        assert_eq!(p.source.tag(), "operator-override");
    }

    /// FAIL-CLOSED: half a price on a model with no built-in entry pins NOTHING — the model stays
    /// unpriced rather than silently charging zero on the missing axis.
    #[test]
    fn half_specified_price_on_a_new_model_pins_nothing() {
        const TEE: &str = "deepseek-ai/DeepSeek-R1-TEE";
        let mut reg = ModelRegistry::builtin();
        reg.apply_price_override(TEE, Some(0.0003), None);
        assert!(reg.pricing_for(TEE).is_none());
        reg.apply_price_override(TEE, None, Some(0.0009));
        assert!(reg.pricing_for(TEE).is_none());
        reg.apply_price_override(TEE, Some(0.0003), Some(0.0009));
        assert!(reg.pricing_for(TEE).is_some());
    }

    /// A single override axis on a model that DOES have a built-in entry keeps the other axis.
    #[test]
    fn single_axis_override_on_a_known_model_keeps_the_other_axis() {
        let mut reg = ModelRegistry::builtin();
        let before = reg.pricing_for(NOVA_2_LITE).unwrap();
        reg.apply_price_override(NOVA_2_LITE, Some(0.5), None);
        let after = reg.pricing_for(NOVA_2_LITE).unwrap();
        assert_eq!(after.input_per_1k, 0.5);
        assert_eq!(after.output_per_1k, before.output_per_1k);
    }

    #[test]
    fn no_overrides_changes_nothing() {
        let mut reg = ModelRegistry::builtin();
        reg.apply_price_override("some/new-model", None, None);
        assert!(reg.pricing_for("some/new-model").is_none());
    }
}
