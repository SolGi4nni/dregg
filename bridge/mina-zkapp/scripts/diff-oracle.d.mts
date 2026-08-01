// Type surface for diff-oracle.mjs — lets a `.ts` oracle import the harness under strict NodeNext tsc
// (no TS7016) as well as run under ts-node --transpile-only. The runtime lives in diff-oracle.mjs.

export type OracleValue = bigint | number | string | { row: number; col: number } | unknown;

/** A producer may return `{name,value}` records or bare primitives (auto-named by index). */
export type VectorEntry = { name?: string | number; value: OracleValue } | OracleValue;
export type Vector = VectorEntry[];
export type Producer = () => Vector | Promise<Vector>;

export type NormalEntry = { name: string; value: OracleValue };
export type DiffResult = {
  ok: boolean;
  kind?: 'name' | 'value' | 'length';
  index?: number;
  name?: string;
  ref?: string;
  cand?: string;
  matched?: number;
};

export interface RunOracleOptions {
  shape: 'gates' | 'statement' | 'field';
  label: string;
  reference: Producer;
  candidate: Producer;
  /** Shape-specific provenance/falsifiers run after the vector diff; throwing exits RED. */
  extra?: (ctx: { ref: NormalEntry[]; cand: NormalEntry[]; result: DiffResult }) => void | Promise<void>;
  /** Force the RED-path self-test; otherwise read from `--self-test` in argv. */
  selfTest?: boolean;
}

export function canon(v: OracleValue): string;
export function normalize(out: unknown, tag?: string): NormalEntry[];
export function diffVectors(ref: NormalEntry[], cand: NormalEntry[]): DiffResult;
export function selfTestBite(ref: NormalEntry[]): { ok: boolean; detail: string };
/** Runs the diff, prints, optionally self-tests, then `process.exit`s — control does not return. */
export function runOracle(opts: RunOracleOptions): Promise<never>;
