-- filepath: c:\Users\jdlon\Documents\logical_mechanics\lakefile.lean
import Lake
open Lake DSL

package logical_mechanics

lean_lib LogicalMechanics

@[default_target]
lean_exe logical_mechanics {
  root := `Main
}
