import Lake
open Lake DSL

package "LogicalMechanics" where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib "LogicalMechanics" where
  srcDir := "lean_proofs"
  globs := #[.submodules `lean_proofs]
