# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
# Only the `Proetale` library is checked: the `Challenge` and `Solution` comparator
# libraries use `srcDir = "Comparator"`, so their names don't match a top-level folder
# and `mk_all` (which is folder-based) cannot manage them. This mirrors mk_all's own
# guidance for projects downstream of mathlib (`lake exe mk_all --lib MyProject`).
lake exe mk_all --lib Proetale --git --check || exit 1

# Fetch build cache
lake exe cache get

# Verify everything builds.
lake build --wfail
