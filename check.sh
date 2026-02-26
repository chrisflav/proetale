#!/bin/bash
# Wrapper to compile a single Lean file without lake (avoids git errors)
# Usage: ./check.sh Proetale/Algebra/IndZariski.lean
cd /AI4M/users/wb/CLI/ralph_loop_test/proetale

LEAN_PATH=""
for pkg in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib checkdecls; do
  p=".lake/packages/${pkg}/.lake/build/lib/lean"
  if [ -d "$p" ]; then
    LEAN_PATH="${LEAN_PATH:+${LEAN_PATH}:}$p"
  fi
done
LEAN_PATH="${LEAN_PATH}:.lake/build/lib/lean"

export LEAN_PATH
exec lean "$@"
