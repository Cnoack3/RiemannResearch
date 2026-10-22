import RiemannResearch.RH.CriticalLineZeros
import RiemannResearch.RH.ProjectedDualMassObstruction

/-!
# Unconditional strict-margin coefficient-mass obstruction

The critical-zero input of ProjectedDualMassObstruction is discharged by
RiemannResearch.RH.exists_critical_zero from CriticalLineZeros.
The imported Alpöge–Furman/Zeta23 theorem is used only to obtain an actual
zero of Mathlib's riemannZeta on the critical line. The complete arithmetic
provider supplies the positive exponent in the premise-free specialization.
RH, endpoint mass budgets, and the signed-pairing provider remain open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis

/-- The critical zero is supplied unconditionally; the arithmetic energy exponent is preserved. -/
theorem coefficient_mass_stretched_barrier
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))) :
    ∃ d : ℕ, (d = 2 ∨ d = 3) ∧ ∀ b : ℝ, b < a →
      Tendsto (fun n : ℕ => Real.exp (-b * logProductPower (1 / 11)
        (6 + Real.log (n : ℝ))) * projectedDualCoefficientMass n d ^ 2) atTop atTop := by
  obtain ⟨s, hz, hs⟩ := RiemannResearch.RH.exists_critical_zero
  exact coefficient_mass_stretched_barrier_of_critical_zero ha hC henergy s hs hz

/-- A premise-free lower-growth obstruction at one fixed column d in {2,3}. -/
theorem exists_coefficient_mass_stretched_barrier :
    ∃ a : ℝ, 0 < a ∧ ∃ d : ℕ, (d = 2 ∨ d = 3) ∧ ∀ b : ℝ, b < a →
      Tendsto (fun n : ℕ => Real.exp (-b * logProductPower (1 / 11)
        (6 + Real.log (n : ℝ))) * projectedDualCoefficientMass n d ^ 2) atTop atTop := by
  obtain ⟨s, hz, hs⟩ := RiemannResearch.RH.exists_critical_zero
  exact exists_coefficient_mass_stretched_barrier_of_critical_zero s hs hz

/-- Separate cofinal sets and strict exponents for each column cannot satisfy the mass budget. -/
theorem not_cofinal_stretched_coefficient_mass
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))) :
    ¬ (∀ d : ℕ, 1 < d → ∃ b : ℝ, b < a ∧ ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
      Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
        projectedDualCoefficientMass n d ^ 2 ≤ K) := by
  obtain ⟨s, hz, hs⟩ := RiemannResearch.RH.exists_critical_zero
  exact not_cofinal_stretched_coefficient_mass_of_critical_zero ha hC henergy s hs hz

/-- The effective-support/l2 budget is impossible at a strict exponent margin. -/
theorem not_cofinal_stretched_l2_concentration
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))) :
    ¬ (∀ d : ℕ, 1 < d → ∃ b : ℝ, b < a ∧ ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
      ∃ (I : Finset (Fin n)) (ρ : ℝ), 0 ≤ ρ ∧
        (∑ i ∈ Iᶜ, projectedDualColumn n d i ^ 2) ≤
          ρ * projectedDualColumnEnergy n d ∧
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
          (((I.card : ℝ) + (Iᶜ.card : ℝ) * ρ) * projectedDualColumnEnergy n d) ≤ K) := by
  obtain ⟨s, hz, hs⟩ := RiemannResearch.RH.exists_critical_zero
  exact not_cofinal_stretched_l2_concentration_of_critical_zero ha hC henergy s hs hz

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
