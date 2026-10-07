#!/bin/sh
# Binding runner for the symdiff model vectors: runs the real OCaml Sym
# functions (gravity/lib/symbolic.ml) against every vector committed in
# this directory, one test per vector named by its id.
# Usage (from the gravity/ project root):
#   sh .grounds/conformance/symdiff.run.sh
cd "$(dirname "$0")/../.." || exit 1
dune exec test/symdiff_conformance.exe -- .grounds/conformance
