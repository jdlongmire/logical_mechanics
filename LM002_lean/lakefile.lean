import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

package logical_mechanics

-- ====================================================================
-- Phase 1: Foundational Proofs
-- ====================================================================

lean_lib L001_Pauli_Exclusion where
  srcDir := "lean_proofs"
  roots := #[`L001_Pauli_Exclusion]

lean_lib L001_Pauli_Exclusion_2 where
  srcDir := "lean_proofs"
  roots := #[`L001_Pauli_Exclusion_2]

-- ====================================================================
-- Phase 2: Golden Quartet
-- ====================================================================

lean_lib L002_Uncertainty_Principle where
  srcDir := "lean_proofs"
  roots := #[`L002_Uncertainty_Principle]

lean_lib L003_Measurement where
  srcDir := "lean_proofs"
  roots := #[`L003_Measurement]

lean_lib L004_Entanglement where
  srcDir := "lean_proofs"
  roots := #[`L004_Entanglement]

-- ====================================================================
-- Phase 3: Analysis and Assessment
-- ====================================================================

lean_lib L005_Constraint_Proximity where
  srcDir := "lean_proofs"
  roots := #[`L005_Constraint_Proximity]

lean_lib L006_Assumption_Analysis where
  srcDir := "lean_proofs"
  roots := #[`L006_Assumption_Analysis]

lean_lib L007_Scope_Assessment where
  srcDir := "lean_proofs"
  roots := #[`L007_Scope_Assessment]

-- ====================================================================
-- Phase 4: Finitude Breakthrough (Golden Quartet Plus One)
-- ====================================================================

lean_lib L008_Finitude_2 where
  srcDir := "lean_proofs"
  roots := #[`L008_Finitude_2]

lean_lib L008_Finitude_Ergodic where
  srcDir := "lean_proofs"
  roots := #[`L008_Finitude_Ergodic]

lean_lib L009_Justify_Eventual_Actualization where
  srcDir := "lean_proofs"
  roots := #[`L009_Justify_Eventual_Actualization]

lean_lib L009_Justify_Eventual_Actualization_v2 where
  srcDir := "lean_proofs"
  roots := #[`L009_Justify_Eventual_Actualization_v2]

-- ====================================================================
-- Phase 5: Information-Theoretic ToE Framework
-- ====================================================================

lean_lib L010_Info_Theory where
  srcDir := "lean_proofs"
  roots := #[`L010_Info_Theory]

lean_lib L011_Relativity_ToE where
  srcDir := "lean_proofs"
  roots := #[`L011_Relativity_ToE]
