import Lake
open Lake DSL

package «lean_zfc» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib LeanZfc
