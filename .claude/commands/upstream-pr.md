Make a pull request to the main proetale repository (chrisflav/proetale).

If the user specifies a statement to upstream, use that. Otherwise, select one yourself by finding a statement in `Proetale/` that:
- Has a complete, sorry-free proof
- Has only a few dependencies, all of which also have complete, sorry-free proofs
- Forms a meaningful, self-contained contribution

The PR should be around 100 lines of new/changed code (excluding imports and module docstrings).

## Steps

1. **Select code to upstream**: Compare this fork against upstream/master to identify candidates:
   ```
   git fetch upstream
   git diff upstream/master...master -- Proetale/
   ```
   Pick a self-contained chunk. Verify it has no `sorry`, no `axiom`, no `set_option maxHeartbeats`.

2. **Create a PR branch from upstream/master**:
   ```
   git fetch upstream
   git checkout -b pr/short-description upstream/master
   ```

3. **Add the formalized code**: Cherry-pick or manually copy the selected declarations into the appropriate file(s) on the new branch.

4. **Polish the code** following the style guidelines in CLAUDE.md section 9:
   - Add docstrings to all important declarations
   - Follow Mathlib naming conventions
   - Use minimal necessary imports
   - Remove debugging artifacts, commented-out code, TODO comments
   - No `set_option maxHeartbeats`
   - Put general helper lemmas in the correct `Proetale/Mathlib/` subfolder
   - In `have` statements, put binders left of the colon
   - Use `refine` instead of nested tactic mode or `;` chaining
   - Prefer terminal `simp`
   - No `change`, no `include`

5. **Verify compilation**: `lake env lean <file>` for each modified file.

6. **Commit and push**:
   ```
   git add <files>
   git commit -m "feat(Path/To/File): short description"
   git push origin pr/short-description
   ```

7. **Create the PR** targeting chrisflav/proetale:
   ```
   gh pr create --repo chrisflav/proetale --base master \
     --title "feat(Path/To/File): short description" \
     --body "Description of main results added."
   ```
   Keep the PR description minimal: just list the main declarations added. No bold text, no headings, no "Summary" or "Test plan" sections.

8. **Return the PR URL** to the user.

## Checklist before pushing
- [ ] At most ~100 lines of meaningful code
- [ ] No `sorry`
- [ ] No `set_option maxHeartbeats`
- [ ] No `axiom` declarations
- [ ] All important declarations have docstrings
- [ ] File compiles cleanly
- [ ] Self-contained — does not require other unmerged code from this fork
- [ ] Follows Mathlib naming and style conventions
- [ ] Branch is based on `upstream/master`, not `origin/master`
