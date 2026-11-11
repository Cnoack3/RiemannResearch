import RiemannResearch.Analysis.FiniteWeightedQuadraticDual
import RiemannResearch.RH.ChebyshevParetoEnergy
import RiemannResearch.RH.ChebyshevDiscreteEnergy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact dual tests for the actual Chebyshev error

Source: user-provided `V_vector_space_RH.pdf`, Sections 7--8.
This module strengthens its finite energy decomposition with an attained
dual formula, including the complete nonnegative gap. It specializes uniform
dual boundedness to the actual Chebyshev error, not to free jump coefficients.

The all-positive-damping implication uses the already proved Mellin
pole-exclusion theorem. Uniform dual boundedness is an explicit open arithmetic
obligation. No pair-correlation asymptotic or RH is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ChebyshevEnergyDual
open RiemannResearch.Analysis.FiniteWeightedQuadraticDual
open RiemannResearch.Analysis.WeightedScalarEnergy
open ChebyshevMidpoint

/-- Prescribed centered level on each actual unit cell. -/
def cellError (n : ℕ) : ℝ := psiNat (n + 1) - RiemannResearch.ChebyshevCell.center ((n : ℝ) + 1)

/-- Signed dual test for the critical finite-window energy. -/
def cellDual (N : ℕ) (y : ℕ → ℝ) : ℝ :=
  deterministicDefect N + dualValue (Finset.range N) paretoKernel cellError y

theorem cell_energy_eq (N : ℕ) :
    square (Finset.range N) paretoKernel cellError = shiftedParetoEnergy N := by
  unfold square shiftedParetoEnergy paretoKernel cellError
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Exact dual gap, including the deterministic geometric defect. -/
theorem continuousEnergy_dual_gap (N : ℕ) (y : ℕ → ℝ) :
    continuousEnergy N - cellDual N y =
      square (Finset.range N) paretoKernel (fun n => cellError n - y n) := by
  rw [continuousEnergy_eq_shiftedPareto_add_defect, cellDual,
    ← cell_energy_eq]
  have h := gap (Finset.range N) paretoKernel cellError y
  linarith

theorem cellDual_le_continuousEnergy (N : ℕ) (y : ℕ → ℝ) :
    cellDual N y ≤ continuousEnergy N := by
  have hg := continuousEnergy_dual_gap N y
  have hn := square_nonneg (Finset.range N) paretoKernel
    (fun n => cellError n - y n) (fun n _ => paretoKernel_nonneg n)
  linarith

theorem cellDual_attained (N : ℕ) :
    cellDual N cellError = continuousEnergy N := by
  rw [cellDual, attained, cell_energy_eq,
    continuousEnergy_eq_shiftedPareto_add_defect]
  ring

theorem continuousEnergy_le_iff_cellDual_le (N : ℕ) (C : ℝ) :
    continuousEnergy N ≤ C ↔ ∀ y : ℕ → ℝ, cellDual N y ≤ C := by
  constructor
  · intro h y
    exact (cellDual_le_continuousEnergy N y).trans h
  · intro h
    simpa only [cellDual_attained] using h cellError

/-- Damped discrete Pareto weight, including its harmless zero value at zero. -/
def dampedWeight (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-a) / ((n : ℝ) * ((n : ℝ) + 1))

def actualError (n : ℕ) : ℝ := Chebyshev.psi (n : ℝ) - (n : ℝ)

def dampedDual (a : ℝ) (N : ℕ) (y : ℕ → ℝ) : ℝ :=
  dualValue (Finset.range N) (dampedWeight a) actualError y

theorem dampedWeight_nonneg (a : ℝ) (n : ℕ) : 0 ≤ dampedWeight a n := by
  unfold dampedWeight
  positivity

theorem dampedTerm_eq (a : ℝ) (n : ℕ) :
    dampedWeight a n * actualError n ^ 2 = ChebyshevDiscreteEnergy.paretoTerm a n := by
  unfold dampedWeight actualError ChebyshevDiscreteEnergy.paretoTerm
  ring

/-- The uniform dual bound is exactly summability of the actual error energy. -/
theorem summable_pareto_iff_uniform_dual_bound (a : ℝ) :
    Summable (ChebyshevDiscreteEnergy.paretoTerm a) ↔
      ∃ C : ℝ, ∀ N (y : ℕ → ℝ), dampedDual a N y ≤ C := by
  simpa only [dampedDual, dampedTerm_eq] using
    summable_iff_uniform_dual_bound (dampedWeight a) actualError (dampedWeight_nonneg a)

/-- Conditional research reduction. The displayed uniform dual bounds remain open. -/
theorem riemannHypothesis_of_all_damped_dual_bounds
    (h : ∀ a : ℝ, 0 < a →
      ∃ C : ℝ, ∀ N (y : ℕ → ℝ), dampedDual a N y ≤ C) :
    RiemannHypothesis :=
  ChebyshevDiscreteEnergy.riemannHypothesis_of_all_discrete_pareto_damping
    (fun a ha => (summable_pareto_iff_uniform_dual_bound a).mpr (h a ha))

/-- A hypothetical off-line zero forces arbitrarily large finite dual witnesses
even at its endpoint damping exponent. -/
theorem dual_unbounded_at_offline_zero_endpoint {ρ : ℂ}
    (hhalf : (1 / 2 : ℝ) < ρ.re) (hone : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) (C : ℝ) :
    ∃ (N : ℕ) (y : ℕ → ℝ), C < dampedDual (2 * ρ.re - 1) N y := by
  by_contra! h
  have hs := (summable_pareto_iff_uniform_dual_bound (2 * ρ.re - 1)).mpr ⟨C, h⟩
  have he := ChebyshevDiscreteEnergy.continuousEnergy_of_summable_pareto
    (by linarith : 0 < 2 * ρ.re - 1) hs
  have he' : ChebyshevMellin.ErrorFiniteEnergy (2 * ρ.re) := by
    convert he using 1 <;> ring
  exact ChebyshevMellin.not_errorFiniteEnergy_at_offline_zero_endpoint
    hhalf hone hzero he'

end RiemannResearch.RH.ChebyshevEnergyDual
