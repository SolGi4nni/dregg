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
        if in_o.is_none() && out_o.is_none() {
            return;
        }
        let target = std::env::var("DREGG_NARRATOR_MODEL")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| DEFAULT_MODEL.to_string());

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
