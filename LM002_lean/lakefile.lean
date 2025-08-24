import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

package logical_mechanics

-- Automatically includes all .lean files in the LogicalMechanics directory
-- Lake will discover all .lean files without needing to list them individually
lean_lib LogicalMechanics where
  srcDir := "."
