import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

package logical_mechanics {
  srcDir := "lean_proofs"
}
