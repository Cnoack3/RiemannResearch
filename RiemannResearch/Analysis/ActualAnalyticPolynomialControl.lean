import RiemannResearch.Analysis.ActualDirichletPolynomialGram
import RiemannResearch.Analysis.EmpiricalCompactCircleControl
import RiemannResearch.Analysis.AnalyticDirichletPolynomial

/-!
# Genuine compact analytic control for actual zeta-zero samples

All samples are actual zeta zeros with their actual multiplicities. The scalar
second-moment bound remains explicit. The compact analytic step is discharged
by the proved Cauchy circle-control theorem, without RH.
-/

noncomputable section
open Complex Set Metric Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualAnalyticPolynomialControl
open ActualZeroOrdinate AnalyticCircleSquareBounds AnalyticDirichletPolynomial

/-- Exact agreement with the already established actual-ordinate Gram polynomial. -/
theorem dirichletPolynomial_eq_gram_polynomial (Y : ℕ) (c : ℕ → ℂ) (s : ℂ) (t : ℝ) :
    dirichletPolynomial Y c s t =
      ActualDirichletPolynomialGram.polynomial (Finset.Icc 1 Y)
        (fun n => c n * Complex.exp (-s * (Real.log n : ℂ))) t := by
  unfold dirichletPolynomial ActualDirichletPolynomialGram.polynomial ZeroOrdinate.phase
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Empirical average over actual positive-height zeros, counting every copy. -/
def empiricalMean (T : ℝ) (g : ℂ → ℝ) : ℝ :=
  realSum T g / (Ncount 0 T : ℝ)

theorem empiricalMean_eq_weighted_sum (T : ℝ) (g : ℂ → ℝ) :
    empiricalMean T g = ∑ ρ ∈ cutoff T,
      ((zeroMult ρ : ℝ) / (Ncount 0 T : ℝ)) * g ρ := by
  simp only [empiricalMean, realSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

/-- This discharges compact analytic control. Only the scalar second-moment
bound remains an input, and it is needed merely on fixed circles inside U. -/
theorem exists_actual_compact_control {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (f : ℂ → ℂ → ℂ) (B : ℝ),
      (∀ ρ ∈ cutoff T, DifferentiableOn ℂ (f ρ) U) →
      (∀ z ∈ U, empiricalMean T (fun ρ => ‖f ρ z‖ ^ 2) ≤ B) →
      empiricalMean T (fun ρ => compactSquareSup K (f ρ)) ≤ C * B := by
  obtain ⟨S, R, hR, hbound⟩ := exists_weighted_compactSquareSup_control hK hU hKU
  refine ⟨4 * (S.card : ℝ), by positivity, ?_⟩
  intro T f B hf hs
  rw [empiricalMean_eq_weighted_sum]
  apply hbound (cutoff T) (fun ρ => (zeroMult ρ : ℝ) / (Ncount 0 T : ℝ)) f B
  · intro ρ hρ
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact hf
  · intro c hc z hz
    rw [← empiricalMean_eq_weighted_sum]
    apply hs
    apply (hR c).2
    exact sphere_subset_closedBall (by simpa [abs_of_pos (hR c).1] using hz)

/-- A scalar residual-square bound for the actual sampled polynomials upgrades
uniformly to their compact residual-square average. -/
theorem exists_polynomial_compact_control {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (Y : ℕ) (a b : ℕ → ℂ) (B : ℝ),
      (∀ z ∈ U, empiricalMean T (fun ρ =>
        ‖dirichletPolynomial Y a z ρ.im * dirichletPolynomial Y b z ρ.im - 1‖ ^ 2) ≤ B) →
      empiricalMean T (fun ρ => compactSquareSup K (fun z =>
        dirichletPolynomial Y a z ρ.im * dirichletPolynomial Y b z ρ.im - 1)) ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := exists_actual_compact_control hK hU hKU
  refine ⟨C, hC, ?_⟩
  intro T Y a b B hs
  apply hbound T _ B _ hs
  intro ρ hρ
  exact (differentiable_product_error Y a b ρ.im).differentiableOn

end RiemannResearch.Analysis.ActualAnalyticPolynomialControl
