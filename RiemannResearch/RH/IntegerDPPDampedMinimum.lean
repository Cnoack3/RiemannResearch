import RiemannResearch.Probability.MultiplicativeOccupancy
import RiemannResearch.RH.IntegerDPPWindowGenerating

/-!
# Exact weighted determinant saturation for the limiting arithmetic DPP

Source: user-provided damped Fredholm determinant argument, 2026-09-20.
This module proves the finite multiplicative minimum criterion for the actual
limiting law. A window containing the first site already detects the full
residue-density condition. The infinite trace-class identification is separate.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical
namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.Occupancy
open CoefficientStabilization

/-- A finite damped determinant using the actual limiting arithmetic kernel. -/
def dampedWindowDeterminant (m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ) : ℝ :=
  (1 - Matrix.diagonal a * Matrix.of (fun i j => limitingKernel (e i) (e j))).det

theorem dampedWindowDeterminant_eq_integral
    (m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ) :
    dampedWindowDeterminant m e a =
      ∫ x, product a (fun i => x (e i)) ∂limitingLaw := by
  simp only [product]
  rw [limitingLaw_window_generating]
  unfold dampedWindowDeterminant
  congr 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul]
  ring

theorem dampedWindowDeterminant_eq_benchmark_iff
    (m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i < 1) :
    dampedWindowDeterminant m e a = benchmark a ↔
      ∀ᵐ x ∂limitingLaw, ∀ i, x (e i) = true := by
  rw [dampedWindowDeterminant_eq_integral]
  exact integral_product_eq_benchmark_iff limitingLaw a ha
    (fun x i => x (e i)) (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i)))

/-- One observed first site makes weighted minimum equality equivalent to the
actual zero-vacancy criterion, irrespective of the other sites in the window. -/
theorem dampedWindowDeterminant_minimum_iff_zero_vacancy
    (m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i < 1) (i₀ : Fin m) (hi₀ : e i₀ = 0) :
    dampedWindowDeterminant m e a = benchmark a ↔ limitingVacancy = 0 := by
  rw [dampedWindowDeterminant_eq_benchmark_iff m e a ha]
  constructor
  · intro h
    have hs : ∀ᵐ x ∂limitingLaw, x 0 = true := by
      filter_upwards [h] with x hx
      simpa [hi₀] using hx i₀
    have hk := (limitingLaw_isDPP.mem_ae_iff 0).mp hs
    rw [limitingVacancy_eq_kernel_complement, hk]
    ring
  · intro h
    have htop := limitingVacancy_zero_iff_top.mp h
    have hall : ∀ᵐ x ∂limitingLaw, {i | x i = true} = Set.univ := by
      apply limitingLaw_isDPP.full_occupation_ae_iff.mpr
      intro i
      apply (limitingKernel_diagonal_one_iff i).mpr
      rw [htop]
      trivial
    filter_upwards [hall] with x hx
    intro i
    have hm : e i ∈ ({j | x j = true} : Set ℕ) := by rw [hx]; trivial
    exact hm

theorem riemannHypothesis_of_dampedWindowDeterminant_minimum
    (m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i < 1) (i₀ : Fin m) (hi₀ : e i₀ = 0)
    (h : dampedWindowDeterminant m e a = benchmark a) : RiemannHypothesis := by
  have hz := (dampedWindowDeterminant_minimum_iff_zero_vacancy m e a ha i₀ hi₀).mp h
  exact riemannHypothesis_of_vacancy_tendsto_zero
    (vacancy_tendsto_zero_iff_limitingVacancy_zero.mpr hz)

end RiemannResearch.RH.Pareto.IntegerDPP
