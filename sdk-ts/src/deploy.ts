/**
 * `@dregg/sdk` — DreggDL, the checkable deployment spec (CapDL for dregg).
 *
 * Write a dregg capability layout **once**, declaratively (TOML / JSON), and
 * `check()` it for the four static guarantees — conservation,
 * non-amplification, well-formedness, ring-balance — over the WHOLE declared
 * authority layout BEFORE submitting, exactly like the Rust
 * `dregg-deploy check` CLI.
 *
 * ## Wired to the REAL checker — nothing is reimplemented in TypeScript
 *
 * The lowering (DreggDL text → the ordered `dregg_turn::CallForest`) and the
 * userspace-verify (`dregg_userspace_verify::analyze`) live ONCE, in the
 * verified-adjacent `dregg-deploy` Rust crate. This module is a thin binding:
 * {@link DeployChecker.check} / {@link DeployChecker.lower} call straight into
 * the `dregg-deploy` functions through the `dregg-wasm` bindings
 * (`deploy_check` / `deploy_lower`). So a deployment audited from TypeScript is
 * audited by the EXACT same code as from Rust or Python — there is no
 * TS-side re-implementation of the lowering, the `CallForest` construction, or
 * the checks.
 *
 * @example
 * ```ts
 * import init from "dregg-wasm";
 * import { DeployChecker } from "@dregg/sdk";
 *
 * const wasm = await init();
 * const deploy = new DeployChecker(wasm);
 *
 * const verdict = deploy.check(toml);
 * if (!verdict.pass) {
 *   for (const f of verdict.assurance.findings) {
 *     console.error(`${f.guarantee}: ${f.message} @ ${f.locus.display}`);
 *   }
 * }
 * ```
 *
 * @packageDocumentation
 */

import type {
  DeployVerdict,
  LoweredDeployment,
} from "./types";

/**
 * The DreggDL checker, bound to a `dregg-wasm` module instance.
 *
 * Both methods drive the REAL `dregg-deploy` pipeline through wasm; they throw
 * a plain `Error` (carrying the crate's message, which names the offending row)
 * on a parse / lowering failure.
 */
export class DeployChecker {
  private wasm: typeof import("dregg-wasm");

  constructor(wasm: typeof import("dregg-wasm")) {
    this.wasm = wasm;
  }

  /**
   * Parse DreggDL → lower to the real `CallForest` → run the static assurance
   * over the whole declared authority layout → return the {@link DeployVerdict}.
   *
   * This is exactly what `dregg-deploy check <file>` runs (the same lowering +
   * the same `dregg_userspace_verify::analyze`).
   *
   * @param text DreggDL surface text — TOML, or JSON when it starts with `{`.
   * @param ring When `true`, also run the ring-balance check (a settlement
   *   ring declared as bare funding transfers must net to zero).
   * @throws Error naming the offending row on a parse / lowering error.
   */
  check(text: string, ring = false): DeployVerdict {
    const json = (this.wasm as any).deploy_check(text, ring) as string;
    return JSON.parse(json) as DeployVerdict;
  }

  /**
   * Run only the real `Lowered::from_deployment` lowering (no check) and return
   * the resolved artifact: the ordered births → funds → grants `CallForest` the
   * checker consumes, the resolved federation id, and the resolved
   * factory / cell content-addresses. This is `dregg-deploy lower <file>`.
   *
   * @throws Error naming the offending row on a parse / lowering error.
   */
  lower(text: string): LoweredDeployment {
    const json = (this.wasm as any).deploy_lower(text) as string;
    return JSON.parse(json) as LoweredDeployment;
  }
}
