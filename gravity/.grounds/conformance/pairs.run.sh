#!/bin/sh
# Binding runner for the utils-pairs model vectors: runs the real OCaml
# Utils.pairs (gravity/lib/utils.ml) against every vector committed in
# this directory.
# Usage (from the gravity/ project root):
#   sh .grounds/conformance/pairs.run.sh
cd "$(dirname "$0")/../.." || exit 1
dune exec test/pairs_conformance.exe -- .grounds/conformance
