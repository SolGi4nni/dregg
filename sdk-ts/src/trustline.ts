/**
 * **Trustline** — the bilateral line of credit as an SDK noun
 * (`docs/ORGANS.md` §1; Lean twin `metatheory/Dregg2/Apps/Trustline.lean`).
 *
 * "Issuer A extends holder B a line of N" is an ATTENUATED CAPABILITY whose
 * exercise debits a shared counter — the granted ⊆ held relation made
 * QUANTITATIVE. The cell is born from a per-line content-addressed factory
 * whose installed program the executor re-evaluates on EVERY touch: `drawn ≤
 * ceiling` for life, terms pinned, settlement monotone.
 *
 * ## Honest scope (what THIS client can and cannot do)
 *
 * Birthing a trustline cell requires the per-line factory descriptor — a
 * Poseidon2 commitment over the slot schema that the Rust SDK / node compute
 * from `dregg_cell::blueprint`. That machinery is NOT in the TS wire layer
 * (which models the seven typed effects, not factory blueprints). So this
 * client drives the trustline through the **node's operator-local trustline
 * service** (`node/src/trustline_service.rs`, routes `POST /trustline/{open,
 * draw,repay,settle,close}` + `GET /trustline/status/{cell}`): the node
 * computes the descriptor, signs the four-turn funded birth with its own
 * cipherclerk, and welds the Stingray budget coordinator. The enforcement
 * tooth is the executor-installed cell program either way — this client is
 * the ergonomic face of those routes.
 *
 * These routes are operator-gated (the node operator IS the issuer); pass a
 * `devnetKey` on the [`NodeClient`].
 *
 * ```ts
 * const tl = runtime.node.trustline();
 * const line = await tl.open(holderCellHex, 1000n);     // four-turn funded birth
 * await tl.draw(line.trustline, 250n);                  // debit the shared counter
 * await tl.repay(line.trustline, 100n);                 // restore the line
 * const status = await tl.status(line.trustline);       // { line, drawn, remaining, ... }
 * await tl.settle(line.trustline);                      // redeem outstanding to holder
 * await tl.close(line.trustline);                       // residual back to issuer
 * ```
 */

import type { NodeClient } from "./client";
import { hexEncode } from "./internal/bytes";
import type { CellId } from "./internal/wire";

function asHex(cell: CellId | string): string {
  return typeof cell === "string" ? cell : hexEncode(cell);
}

/** `POST /trustline/open` response — the four-turn funded birth. */
export interface TrustlineOpened {
  /** The trustline cell id (hex) — the handle for every later operation. */
  trustline: string;
  /** The issuer (operator) cell id (hex). */
  issuer: string;
  /** The holder (counterparty) cell id (hex). */
  holder: string;
  /** The line N escrowed in full at open (fullReserve). */
  line: number;
  /** Computrons currently escrowed backing the line. */
  escrow: number;
  /** The Stingray budget coordinator's remaining headroom. */
  coordinator_remaining: number;
  /** The four lifecycle turn hashes (birth, fund, adopt, open), hex. */
  turn_hashes: string[];
}

/** `POST /trustline/draw` response. */
export interface TrustlineDraw {
  trustline: string;
  /** The draw digest (hex) — one-shot; a replay of the same digest refuses. */
  digest: string;
  amount: number;
  /** Total drawn after this debit. */
  drawn: number;
  /** Line headroom remaining (`line − drawn`). */
  remaining: number;
  coordinator_remaining: number;
  turn_hash: string;
}

/** `POST /trustline/repay` response. */
export interface TrustlineRepay {
  trustline: string;
  amount: number;
  drawn: number;
  remaining: number;
  coordinator_remaining: number;
  turn_hash: string;
}

/** `POST /trustline/settle` response (redeem outstanding draws to holders). */
export interface TrustlineSettle {
  epoch: number;
  certificates: number;
  settlements: Array<{ trustline: string; holder: string; amount: number; turn_hash: string }>;
  /** Settlement entries whose ledger application failed (a non-empty list is
   * a counter↔ledger divergence; the node re-carries + re-attempts). */
  failures: string[];
}

/** `POST /trustline/close` response. */
export interface TrustlineClose {
  trustline: string;
  /** `"fullReserve"` | `"pureCredit"`. */
  collateral: string;
  /** Outstanding draw settled to the holder at close (fullReserve only). */
  settled_to_holder: number;
  /** Residual escrow returned to the issuer (`escrow − outstanding`). */
  residual_to_issuer: number;
  turn_hash: string;
}

/** `GET /trustline/status/{cell}` response. */
export interface TrustlineStatus {
  trustline: string;
  issuer: string;
  holder: string;
  collateral: string;
  line: number;
  drawn: number;
  settled: number;
  remaining: number;
  escrow: number;
  open: boolean;
  coordinator_remaining: number | null;
  coordinator_version: number | null;
}

/**
 * The trustline organ client — the ergonomic face of the node's
 * operator-local trustline service. Reach it via [`NodeClient.trustline`].
 */
export class TrustlineClient {
  constructor(private readonly node: NodeClient) {}

  /**
   * Open a directional line `operator → holder` of `line`, escrowed in full
   * (fullReserve). The node births the per-line cell, funds it, grants the
   * holder + operator their capabilities, and opens it — four turns.
   *
   * `salt` disambiguates multiple lines to the same holder.
   */
  open(holder: CellId | string, line: number | bigint, salt?: string): Promise<TrustlineOpened> {
    const body: Record<string, unknown> = { holder: asHex(holder), line: Number(line) };
    if (salt !== undefined) body.salt = salt;
    return this.node.postJson<TrustlineOpened>("/trustline/open", body);
  }

  /**
   * Draw `amount` against the line (debits the shared counter). Supply a
   * `digest` (hex) for client-side replay protection across retries; the
   * node derives one otherwise. Draws are one-shot per digest.
   */
  draw(trustline: CellId | string, amount: number | bigint, digest?: string): Promise<TrustlineDraw> {
    const body: Record<string, unknown> = { trustline: asHex(trustline), amount: Number(amount) };
    if (digest !== undefined) body.digest = digest;
    return this.node.postJson<TrustlineDraw>("/trustline/draw", body);
  }

  /** Repay `amount`, restoring the line (never resurrects a burned digest). */
  repay(trustline: CellId | string, amount: number | bigint): Promise<TrustlineRepay> {
    return this.node.postJson<TrustlineRepay>("/trustline/repay", {
      trustline: asHex(trustline),
      amount: Number(amount),
    });
  }

  /** Settle outstanding draws as ledger moves to the holders (epoch sweep). */
  settle(trustline: CellId | string): Promise<TrustlineSettle> {
    return this.node.postJson<TrustlineSettle>("/trustline/settle", { trustline: asHex(trustline) });
  }

  /** Close the line: settle outstanding to the holder, residual to the issuer. */
  close(trustline: CellId | string): Promise<TrustlineClose> {
    return this.node.postJson<TrustlineClose>("/trustline/close", { trustline: asHex(trustline) });
  }

  /** Live position: line / drawn / remaining / escrow / coordinator state. */
  status(trustline: CellId | string): Promise<TrustlineStatus> {
    return this.node.getJson<TrustlineStatus>(`/trustline/status/${asHex(trustline)}`);
  }
}
