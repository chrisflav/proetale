import Lake.CLI.Main

/-!
# Blueprint declaration checker

Local replacement for the `checkdecls` executable from
https://github.com/PatrickMassot/checkdecls, which the blueprint CI step runs as
`lake exe checkdecls blueprint/lean_decls`. The upstream version imports the roots of
*every* `lean_lib` of the package into a single environment. That fails for this project
because `Challenge` and `Solution` (the comparator pair in `Comparator/`) intentionally
declare the same names. This version skips those libraries; the blueprint only references
declarations from the remaining ones.
-/

open Lake Lean

/-- Libraries whose roots must not be imported when checking blueprint declarations,
because they duplicate each other's declaration names by design. -/
def excludedLibs : Array Name := #[`Challenge, `Solution]

unsafe def main (args : List String) : IO UInt32 := do
  unless args.length == 1 do
    println! "This command takes exactly one argument: \
      the path to a file containing a list of declarations to check."
    return 1
  let filename : System.FilePath := args[0]!
  unless ← filename.pathExists do
    println! "Could not find declaration list {filename}."
    return 1
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let (ws?, log) ← (loadWorkspace config).run?
  log.replay (logger := .stderr)
  let some ws := ws? | return 1
  let libs := ws.root.leanLibs.filter fun lib ↦ !excludedLibs.contains lib.name
  let imports := libs.flatMap (·.config.roots.map fun module ↦ { module })
  -- see comments in https://github.com/leanprover/lean4/pull/6325
  enableInitializersExecution
  let env ← Lean.importModules imports {}
  let mut ok := true
  for line in ← IO.FS.lines filename do
    unless env.contains line.toName do
      println! "{line} is missing."
      ok := false
  return if ok then 0 else 1
