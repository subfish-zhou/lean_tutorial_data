import Lake
open Lake DSL

package «lean_tutorial_benchmark» where
  -- add package configuration options here

lean_lib «LeanTutorialBenchmark» where
  -- add library configuration options here

@[default_target]
lean_exe «lean_tutorial_benchmark» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require mathlib from git
    "https://github.com/leanprover-community/mathlib4" @ "v4.6.0-rc1"
