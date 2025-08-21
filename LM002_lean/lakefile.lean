import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

package logical_mechanics

lean_lib LogicalMechanics

@[default_target]
lean_lib LeanProofs {
  srcDir := "lean_proofs"
}

@[default_target]
lean_exe logical_mechanics {
  root := `Main
}
