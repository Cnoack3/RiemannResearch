/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusCovarianceMinimum
import RiemannResearch.Analysis.FiniteGramCapacityIncrement

/-!
# Actual signed Möbius capacity increments

Source: user-provided Pareto capacity handoff, Section 11. This identifies the
exact gain and saturation obstruction for adding actual canonical candidates.
The estimates retain the complete infinite tails and all signed inner products.
No asymptotic lower bound or Riemann-hypothesis assertion is assumed implicitly.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Unnormalized tail vector representing the coefficient-sum functional. -/
def capacityNormal (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) : ThresholdHilbert :=
  Fintype.linearCombination ℝ (tailFamily N k) (normal N k hk)

theorem capacityNormal_energy (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) :
    ‖capacityNormal N k hk‖ ^ 2 = capacity N k hk :=
  normal_synthesis_energy _ _ (normal_equations N k hk)

theorem capacityNormal_equations (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (i : ι) : inner ℝ (tailFamily N k i) (capacityNormal N k hk) = 1 :=
  congrFun (normal_equations N k hk) i

/-- Exact additive change of the actual capacity under family enlargement. -/
theorem capacity_increment_eq_normal_distance_sq
    (N : ℕ) (k : ι → ℕ) (l : κ → ℕ)
    (hk : ∀ i, 0 < k i) (hl : ∀ j, 0 < l j)
    (e : ι → κ) (he : ∀ i, k i = l (e i)) :
    capacity N l hl - capacity N k hk =
      ‖capacityNormal N l hl - capacityNormal N k hk‖ ^ 2 := by
  apply normal_mass_increment_of_family_map
    (tailFamily N k) (tailFamily N l) (normal N k hk) (normal N l hl)
    (normal_equations N k hk) (normal_equations N l hl) e
  intro i
  simp only [tailFamily, he i]

/-- Capacity saturation can be tested on the newly included conductors. -/
theorem capacity_eq_iff_all_normal_equations
    (N : ℕ) (k : ι → ℕ) (l : κ → ℕ)
    (hk : ∀ i, 0 < k i) (hl : ∀ j, 0 < l j)
    (e : ι → κ) (he : ∀ i, k i = l (e i)) :
    capacity N l hl = capacity N k hk ↔
      ∀ j, inner ℝ (tailFamily N l j) (capacityNormal N k hk) = 1 := by
  apply normal_mass_eq_iff_new_normal_equations
    (tailFamily N k) (tailFamily N l) (normal N k hk) (normal N l hl)
    (normal_equations N k hk) (normal_equations N l hl) e
  intro i
  simp only [tailFamily, he i]

theorem capacity_normal_defect_sq_le_gain
    (N : ℕ) (k : ι → ℕ) (l : κ → ℕ)
    (hk : ∀ i, 0 < k i) (hl : ∀ j, 0 < l j)
    (e : ι → κ) (he : ∀ i, k i = l (e i)) (j : κ) :
    (1 - inner ℝ (tailFamily N l j) (capacityNormal N k hk)) ^ 2 ≤
      ‖tailFamily N l j‖ ^ 2 * (capacity N l hl - capacity N k hk) := by
  apply normal_equation_defect_sq_le_gain
    (tailFamily N k) (tailFamily N l) (normal N k hk) (normal N l hl)
    (normal_equations N k hk) (normal_equations N l hl) e _ j
  intro i
  simp only [tailFamily, he i]

/-- Any signed prediction using the old tail family can screen a newly added
conductor. Small prediction error and a surviving signed source force gain. -/
theorem capacity_normal_defect_sq_le_screened_gain
    (N : ℕ) (k : ι → ℕ) (l : κ → ℕ)
    (hk : ∀ i, 0 < k i) (hl : ∀ j, 0 < l j)
    (e : ι → κ) (he : ∀ i, k i = l (e i)) (c : ι → ℝ) (j : κ) :
    (1 - inner ℝ (tailFamily N l j) (capacityNormal N k hk)) ^ 2 ≤
      ‖tailFamily N l j - Fintype.linearCombination ℝ (tailFamily N k) c‖ ^ 2 *
        (capacity N l hl - capacity N k hk) := by
  apply normal_equation_defect_sq_le_screened_gain
    (tailFamily N k) (tailFamily N l) (normal N k hk) c (normal N l hl)
    (normal_equations N k hk) (normal_equations N l hl) e _ j
  intro i
  simp only [tailFamily, he i]

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
