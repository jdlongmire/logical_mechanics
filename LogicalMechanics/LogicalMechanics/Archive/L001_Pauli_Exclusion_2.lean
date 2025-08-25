/-
Pauli Exclusion from Logical Identity Constraints (refactored)

Changes vs. previous draft:
• Removed circular axioms (no “logical_distinctness_requirement”, no trivial fermion axiom).
• Replaced indistinguishability axiom with a provable lemma:
    if two entries of a configuration are equal, swapping them leaves the
    configuration identical as a function (Fin n → state).
• Kept only what’s needed to derive Pauli exclusion from antisymmetry.
• Uses a general field K with CharZero (so 2 ≠ 0).
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Algebra.Subsemiring
import Mathlib.Algebra.CharZero
import Mathlib.Tactic -- safe convenience; can be removed if desired

namespace PauliFromLogic

-- ============================================================
-- Configurations and swaps
-- ============================================================

/-- An n-particle configuration as a function assigning a single-particle
    state to each particle label. -/
def NParticleConfig (SingleParticleState : Type) (n : ℕ) : Type :=
  Fin n → SingleParticleState

/-- If entries at i and j are equal, swapping i and j leaves the configuration unchanged. -/
lemma comp_swap_eq_self_of_eq
  {A : Type} {n : ℕ}
  (config : NParticleConfig A n) (i j : Fin n)
  (hij : config i = config j) :
  (config ∘ (Equiv.swap i j)) = config := by
  -- Pointwise functional extensionality
  funext x
  -- Unfold the composition and swap
  classical
  -- `Equiv.swap_apply_def` gives a case split
  by_cases hx_i : x = i
  · subst hx_i
    -- (swap i j) i = j
    -- LHS: config j, RHS: config i
    -- use hij : config i = config j
    simpa [Function.comp, Equiv.swap_apply_def, hij]
  · by_cases hx_j : x = j
    · subst hx_j
      -- (swap i j) j = i
      -- LHS: config i, RHS: config j
      simpa [Function.comp, Equiv.swap_apply_def, hij.symm]
    · -- x ≠ i and x ≠ j: swap leaves x fixed
      simp [Function.comp, Equiv.swap_apply_def, hx_i, hx_j]

/-- Two particles (i, j) are in identical single-particle states. -/
def identical_single_particle_states
  {A : Type} {n : ℕ}
  (config : NParticleConfig A n) (i j : Fin n) : Prop :=
  config i = config j

/-- “Identical fermion configuration” = distinct labels occupying identical states. -/
def identical_fermion_configuration
  {A : Type} {n : ℕ}
  (config : NParticleConfig A n) (i j : Fin n) : Prop :=
  i ≠ j ∧ config i = config j

-- ============================================================
-- Wavefunctions and (anti)symmetry
-- ============================================================

/-- A wavefunction assigns an amplitude in a field `K` to each configuration. -/
def Wavefunction (A : Type) (K : Type) [Field K] (n : ℕ) : Type :=
  NParticleConfig A n → K

/-- Antisymmetric wavefunction: swapping two labels flips the sign of the amplitude. -/
def antisymmetric_wavefunction
  {A K : Type} [Field K] {n : ℕ}
  (ψ : Wavefunction A K n) : Prop :=
  ∀ (config : NParticleConfig A n) (i j : Fin n),
    ψ (config ∘ (Equiv.swap i j)) = - (ψ config)

-- (Symmetric case not needed for Pauli; omitted deliberately.)

-- ============================================================
-- Pauli exclusion from antisymmetry
-- ============================================================

/-- If two labels occupy the same single-particle state, the configuration is fixed by swapping them. -/
lemma swap_fixes_config_of_identical
  {A : Type} {n : ℕ}
  (config : NParticleConfig A n) (i j : Fin n)
  (h : identical_single_particle_states config i j) :
  (config ∘ (Equiv.swap i j)) = config :=
  comp_swap_eq_self_of_eq config i j h

/-- Main lemma: For an antisymmetric wavefunction over a CharZero field,
    any configuration with two identical fermions has amplitude 0. -/
theorem pauli_exclusion_from_antisymmetry
  {A K : Type} [Field K] [CharZero K] {n : ℕ}
  (ψ : Wavefunction A K n)
  (hAnti : antisymmetric_wavefunction ψ)
  (config : NParticleConfig A n) (i j : Fin n)
  (hIdent : identical_fermion_configuration config i j) :
  ψ config = 0 := by
  classical
  -- Extract equality of the single-particle states from the hypothesis
  have hij : config i = config j := hIdent.2
  -- Antisymmetry: ψ(config ∘ swap i j) = - ψ(config)
  have hAntiEq : ψ (config ∘ (Equiv.swap i j)) = - (ψ config) :=
    hAnti config i j
  -- But swapping equal entries leaves the configuration unchanged:
  have hFix : (config ∘ (Equiv.swap i j)) = config :=
    swap_fixes_config_of_identical config i j hij
  -- Therefore ψ config = - ψ config
  have hEqNeg : ψ config = - (ψ config) := by simpa [hFix] using hAntiEq
  -- Convert to ψ + ψ = 0
  have hAddSelfZero : ψ config + ψ config = 0 := by
    -- from x = -x, we get x + x = 0 via rewriting x + (-x)
    simpa [hEqNeg] using add_right_neg_self (ψ config)
  -- In a CharZero field: (2 : K) * ψ = 0  ⇒ ψ = 0
  have hTwoMul : (2 : K) * ψ config = 0 := by
    simpa [two_mul] using hAddSelfZero
  -- 2 ≠ 0 in CharZero fields
  have hTwoNe : (2 : K) ≠ 0 := by
    -- `Nat.cast_ne_zero` is available under `CharZero K`
    exact_mod_cast (by decide : (2 : Nat) ≠ 0)
  -- Conclude
  exact (mul_eq_zero.mp hTwoMul).resolve_left hTwoNe

/-- Corollary form: If a wavefunction is antisymmetric, then
    for any configuration with two identical fermions its amplitude vanishes. -/
theorem pauli_exclusion_for_antisymmetric
  {A K : Type} [Field K] [CharZero K] {n : ℕ}
  (ψ : Wavefunction A K n)
  (hAnti : antisymmetric_wavefunction ψ) :
  ∀ (config : NParticleConfig A n) (i j : Fin n),
    identical_fermion_configuration config i j → ψ config = 0 :=
by
  intro config i j h
  exact pauli_exclusion_from_antisymmetry ψ hAnti config i j h

-- ============================================================
-- Notes (non-executable documentation):
-- • No circular axioms: the only “empirical” ingredient used is equality
--   at two labels ⇒ swap leaves the configuration unchanged, which is proved (not assumed).
-- • Antisymmetry is the single structural assumption; Pauli exclusion is then a theorem.
-- • This file is ready to serve as a Lean-verified core for a short LM/LFT paper.
-- ============================================================

end PauliFromLogic
