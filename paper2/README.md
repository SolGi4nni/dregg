# paper2 — dregg: a verified distributed object-capability substrate

Markdown source for the paper. One file per section; the order below is the
paper's order. Typesetting (typst/LaTeX) is a separate step; these files are
the content of record.

Citations to the mechanization use Lean declaration names
(`Module.theorem_name`) resolvable in `metatheory/Dregg2/`; every such name is
`#assert_axioms`-pinned in the source tree, so the paper's claims are
checkable against the build.

## Table of contents

| § | file | contents |
|---|------|----------|
| 0 | [00-abstract.md](00-abstract.md) | Abstract |
| 1 | [01-model.md](01-model.md) | The model: four substances, eight verbs, turns |
| 2 | [02-authority.md](02-authority.md) | Authority as constructive knowledge: the production law, non-forgeability |
| 3 | [03-guards.md](03-guards.md) | The guard algebra: one Pred, four polarities, two dials |
| 4 | [04-receipts.md](04-receipts.md) | Receipts and Q: aggregation and the light-client theorem |
| 5 | [05-assurance.md](05-assurance.md) | The assurance case, by guarantee; the assumption floor |
| 6 | [06-realization.md](06-realization.md) | The realization: the Lean kernel as the executor, the descriptor circuit, the factory userspace |
| 7 | [07-related.md](07-related.md) | Related work |
| 8 | [08-limitations.md](08-limitations.md) | Limitations |

## Source-of-truth discipline

Where a section states an enumerable fact (the verb roster, the guarantee
list, the assumption floor), the canonical machine-readable form is the
generated catalogs in `site/src/_includes/studio/*.generated.json`,
drift-checked against the Lean/Rust sources. The paper quotes those facts; it
does not own them.
