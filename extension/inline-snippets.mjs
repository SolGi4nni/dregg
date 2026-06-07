// Inline wasm-bindgen `no-modules` JS snippets into the glue so the extension
// loads in a service worker (no `require`, no external snippet files).
//
// wasm-bindgen emits, for each `#[wasm_bindgen(inline_js = ...)]` dependency:
//   const importN = require("./snippets/<pkg>/inlineK.js");
//   ... "./snippets/<pkg>/inlineK.js": importN,
// `require` is undefined in a browser worker. We replace the `require(...)`
// with an inline object literal `{ fn: function(){...}, ... }` built from the
// snippet's `export function fn(...) {...}` declarations.
//
// Usage: node inline-snippets.mjs <glue.js> <snippetsDir>
import fs from "node:fs";
import path from "node:path";

const [, , gluePath, snippetsDir] = process.argv;
if (!gluePath || !snippetsDir) {
  console.error("usage: inline-snippets.mjs <glue.js> <snippetsDir>");
  process.exit(2);
}

let glue = fs.readFileSync(gluePath, "utf8");

// Parse a snippet's `export function NAME(args) { body }` decls into a JS
// object-literal source `{ NAME: function(args){ body }, ... }`.
function snippetToObjectLiteral(src) {
  const entries = [];
  const re = /export\s+function\s+([A-Za-z_$][\w$]*)\s*\(([^)]*)\)\s*\{/g;
  let m;
  while ((m = re.exec(src)) !== null) {
    const name = m[1];
    const args = m[2];
    // Walk braces from the opening `{` to find the matching close.
    let depth = 1;
    let i = re.lastIndex;
    for (; i < src.length && depth > 0; i++) {
      if (src[i] === "{") depth++;
      else if (src[i] === "}") depth--;
    }
    const body = src.slice(re.lastIndex, i - 1);
    entries.push(`${name}: function(${args}) {${body}}`);
    re.lastIndex = i;
  }
  return `{ ${entries.join(", ")} }`;
}

// Replace each `const importN = require("<rel>");` whose <rel> is a snippet.
const requireRe =
  /const\s+(import\d+)\s*=\s*require\(\s*["'](\.\/snippets\/[^"']+)["']\s*\)\s*;/g;
let count = 0;
glue = glue.replace(requireRe, (full, importVar, rel) => {
  const file = path.join(path.dirname(gluePath), rel);
  if (!fs.existsSync(file)) {
    console.error(`  snippet not found: ${file} (leaving require in place)`);
    return full;
  }
  const obj = snippetToObjectLiteral(fs.readFileSync(file, "utf8"));
  count++;
  return `const ${importVar} = ${obj};`;
});

fs.writeFileSync(gluePath, glue);
console.log(`  Inlined ${count} snippet import(s) into ${path.basename(gluePath)}`);
