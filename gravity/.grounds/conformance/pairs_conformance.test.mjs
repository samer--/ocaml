// Report the utils-pairs model vectors against the real OCaml code as a
// node --test run. The OCaml conformance binary reads the committed
// vectors file (.grounds/conformance/utils-pairs.vectors.json), binds
// each input to a call of the real Utils.pairs, and compares the result
// with the model's expected output. This wrapper asserts every vector
// agreed (7/7) and that the run ended successfully.
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";
import test from "node:test";
import assert from "node:assert/strict";

const here = dirname(fileURLToPath(import.meta.url));
const gravity = resolve(here, "..", "..");

test("utils-pairs vector conformance against the real OCaml Utils.pairs (7 vectors)", () => {
  const out = execFileSync(
    "dune", ["exec", "test/pairs_conformance.exe", "--", ".grounds/conformance"],
    { cwd: gravity, encoding: "utf8" },
  );
  assert.match(out, /conformance: 7\/7 vectors agreed$/m, "expected all 7 vectors to agree");
});