#!/usr/bin/env bash
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT

# Run in an environment with Coq 8.16, MathComp 1.15, OCaml and dune.
# Preserve an already checked-out translator version (including newer commits).
if [ ! -f firrtl2coq/_CoqProject ]; then
  git submodule update --init --recursive -- firrtl2coq
fi
mill chiselModule.runMain mini.CoqMain --target-dir "$work"
(
  cd firrtl2coq
  coq_makefile -f _CoqProject -o Makefile
  make -j"${JOBS:-4}"
  cd src/ocaml
  dune exec ./bin/main.exe -- "$work/CoreSoc.hi.fir" "$work/CoreSoc.v"
)
coqc -Q firrtl2coq/lib/simplssrlib simplssrlib \
     -Q firrtl2coq/lib/nbits nbits -R firrtl2coq/src firrtl \
     "$work/CoreSoc.v"

# Publish only the source artifacts, after successful Coq compilation.
mkdir -p formal
cp "$work/CoreSoc.hi.fir" "$work/CoreSoc.v" formal/
