// Report the pairs corpus checks as a node --test run over the real OCaml code.
// The corpus binary is the thing under test; this runner executes it and asserts
// every check passed.
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";
import test from "node:test";
import assert from "node:assert/strict";

const here = dirname(fileURLToPath(import.meta.url));
const gravity = resolve(here, "..", "..");

test("pairs corpus against the real OCaml Utils.pairs code (15 checks)", () => {
  const out = execFileSync("dune", ["exec", "test/pairs_corpus.exe"], {
    cwd: gravity,
    encoding: "utf8",
  });
  const oks = (out.match(/^ok   /gm) || []).length;
  assert.match(out, /PASS$/m, "corpus run did not end with PASS");
  assert.equal(oks, 15, "expected 15 passing corpus checks");
});
