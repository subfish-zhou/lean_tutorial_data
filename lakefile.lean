import Lake
open Lake DSL

package «lean_tutorial_benchmark» where
  -- add package configuration options here

@[default_target]
lean_lib «LeanTutorialBenchmark» where
  -- add library configuration options here

@[default_target]
lean_exe «greeting» where
  root := `Main
  supportInterpreter := true

require mathlib from git
    "https://github.com/leanprover-community/mathlib4" @ "v4.6.0-rc1"