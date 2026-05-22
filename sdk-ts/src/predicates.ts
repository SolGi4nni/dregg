/**
 * Predicate proof helpers: Datalog evaluation and higher-level predicate
 * composition for authorization policies.
 */

import type {
  DatalogResult,
  DatalogFact,
  DatalogRequest,
} from "./types";

/**
 * PredicateEvaluator wraps the pyana Datalog authorization engine,
 * providing a high-level interface for policy evaluation.
 *
 * The Datalog engine uses a standard policy with built-in rules for
 * authorization decisions. Facts represent the state of the world,
 * and the request describes what access is being requested.
 *
 * @example
 * ```ts
 * import { PredicateEvaluator } from "@pyana/sdk";
 *
 * const evaluator = new PredicateEvaluator(wasm);
 *
 * const result = await evaluator.evaluate(
 *   [
 *     { predicate: "member", terms: ["alice", "admin"] },
 *     { predicate: "permission", terms: ["admin", "read", "docs"] },
 *   ],
 *   { app_id: "myapp", action: "read", service: "docs" }
 * );
 *
 * console.log(result.conclusion); // "allow" or "deny"
 * console.log(result.num_derivation_steps); // how many rules fired
 * ```
 */
export class PredicateEvaluator {
  private wasm: typeof import("pyana-wasm");

  constructor(wasm: typeof import("pyana-wasm")) {
    this.wasm = wasm;
  }

  /**
   * Evaluate a Datalog authorization request against a set of facts.
   *
   * Uses the standard pyana policy rules to derive an allow/deny conclusion.
   * The derivation trace is returned for debugging and auditability.
   *
   * @param facts - The facts representing the current authorization state.
   * @param request - The authorization request to evaluate.
   * @returns The evaluation result with conclusion and derivation trace.
   * @throws Error if the facts or request are malformed.
   */
  async evaluate(
    facts: DatalogFact[],
    request: DatalogRequest
  ): Promise<DatalogResult> {
    const factsJson = JSON.stringify(facts);
    const requestJson = JSON.stringify(request);

    try {
      return this.wasm.evaluate_datalog(
        factsJson,
        requestJson
      ) as DatalogResult;
    } catch (e) {
      throw new Error(`Failed to evaluate Datalog: ${extractError(e)}`);
    }
  }

  /**
   * Check if a specific action is allowed given a set of facts.
   *
   * Convenience method that wraps `evaluate()` and returns a boolean.
   *
   * @param facts - The authorization facts.
   * @param action - The action to check.
   * @param service - The service context (optional).
   * @param appId - The application ID (optional).
   * @returns True if the action is allowed.
   */
  async isAllowed(
    facts: DatalogFact[],
    action: string,
    service?: string,
    appId?: string
  ): Promise<boolean> {
    const request: DatalogRequest = { action };
    if (service) request.service = service;
    if (appId) request.app_id = appId;

    const result = await this.evaluate(facts, request);
    return result.conclusion === "allow";
  }

  /**
   * Build a set of facts from a simplified permission map.
   *
   * Converts a record of `{ role: actions[] }` into Datalog facts
   * suitable for the standard policy engine.
   *
   * @param permissions - A map of role names to allowed actions.
   * @param userRole - The user's role.
   * @param userId - The user's ID.
   * @returns An array of DatalogFact objects.
   *
   * @example
   * ```ts
   * const facts = evaluator.buildFacts(
   *   { admin: ["read", "write", "delete"], viewer: ["read"] },
   *   "admin",
   *   "alice"
   * );
   * ```
   */
  buildFacts(
    permissions: Record<string, string[]>,
    userRole: string,
    userId: string
  ): DatalogFact[] {
    const facts: DatalogFact[] = [];

    // User has role
    facts.push({ predicate: "member", terms: [userId, userRole] });

    // Role has permissions
    for (const [role, actions] of Object.entries(permissions)) {
      for (const action of actions) {
        facts.push({ predicate: "permission", terms: [role, action] });
      }
    }

    return facts;
  }
}

function extractError(e: unknown): string {
  if (e instanceof Error) return e.message;
  return String(e);
}
