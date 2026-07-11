# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported. Only check the `Proetale` library: the
# `Challenge`/`Solution` comparator libs (`srcDir = "Comparator"`) would otherwise make
# `mk_all` demand bogus empty root-level `Challenge.lean`/`Solution.lean` umbrellas.
lake exe mk_all --lib Proetale --git --check || exit 1

# Fetch build cache
lake exe cache get

# Verify everything builds.
lake build --wfail
