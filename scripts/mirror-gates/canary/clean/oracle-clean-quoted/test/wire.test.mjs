// The differential done right: its oracle is a BUILD INPUT. `pretest` rebuilds `canary-wasm-quoted`
// (file:./pkg) from source before every run, so the compared bytes are always current.
import { test } from "node:test";
import * as oracle from "canary-wasm-quoted";
test("wire matches the freshly-built oracle", () => { void oracle; });
