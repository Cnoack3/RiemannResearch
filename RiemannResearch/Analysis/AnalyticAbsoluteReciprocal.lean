import RiemannResearch.Analysis.AnalyticDirichletPolynomial
import RiemannResearch.Analysis.AbsoluteReciprocalCompatibility

/-!
# Exact bridge from analytic Dirichlet polynomials to L-series truncations

This identifies the original entire polynomial, including its ordinate shift
and the cutoff `n ≤ Y`, with Mathlib's finite L-series partial sum. Consequently
the unconditional absolute-convergence estimate applies to that same polynomial
at every real ordinate. The theorem is confined to `re s > 1`.
-/

noncomputable section

open Complex Finset

namespace RiemannResearch.Analysis.AnalyticAbsoluteReciprocal

open AnalyticDirichletPolynomial

lemma LSeries_term_eq_weight (c : ℕ → ℂ) (s : ℂ) (t : ℝ) {n : ℕ}
    (hn : n ≠ 0) :
    LSeries.term c (s - (t : ℂ) * Complex.I) n =
      c n * TruncatedMobiusConvolution.dirichletWeight s t n := by
  rw [LSeries.term_of_ne_zero hn, TruncatedMobiusConvolution.dirichletWeight,
    div_eq_mul_inv, ← Complex.cpow_neg]
  congr 1
  congr 1
  ring

/-- Exact equality of the entire exponential definition and the finite
L-series definition, including the cutoff and ordinate sign. -/
theorem dirichletPolynomial_eq_partialSum (Y : ℕ) (c : ℕ → ℂ) (s : ℂ) (t : ℝ) :
    dirichletPolynomial Y c s t =
      AbsoluteReciprocalCompatibility.partialSum c
        (s - (t : ℂ) * Complex.I) (Y + 1) := by
  rw [dirichletPolynomial_eq_weight_sum]
  unfold AbsoluteReciprocalCompatibility.partialSum
  calc
    (∑ n ∈ Icc 1 Y, c n * TruncatedMobiusConvolution.dirichletWeight s t n) =
        ∑ n ∈ Icc 1 Y, LSeries.term c (s - (t : ℂ) * Complex.I) n := by
      apply sum_congr rfl
      intro n hn
      exact (LSeries_term_eq_weight c s t
        (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)).symm
    _ = ∑ n ∈ range (Y + 1), LSeries.term c (s - (t : ℂ) * Complex.I) n := by
      apply sum_subset
      · intro n hn
        exact mem_range.mpr (Nat.lt_succ_iff.mpr (mem_Icc.mp hn).2)
      · intro n hnrange hnnot
        by_cases hnzero : n = 0
        · simp [hnzero]
        · exact False.elim (hnnot (mem_Icc.mpr
            ⟨Nat.one_le_iff_ne_zero.mpr hnzero,
              Nat.lt_succ_iff.mp (mem_range.mp hnrange)⟩))

/-- Fully explicit reciprocal compatibility for the original analytic
polynomials, uniformly in every real ordinate, without averaging or RH. -/
theorem zeta_moebius_product_error_explicit {σ : ℝ} (hσ : 1 < σ)
    {Y : ℕ} (hY : 1 ≤ Y) {s : ℂ} (hs : σ ≤ s.re) (t : ℝ) :
    ‖dirichletPolynomial Y (fun _ => 1) s t *
        dirichletPolynomial Y (fun n => (ArithmeticFunction.moebius n : ℂ)) s t - 1‖
      ≤ 2 * (1 + 1 / (σ - 1)) * ((Y : ℝ) ^ (1 - σ) / (σ - 1)) := by
  have hshift : σ ≤ (s - (t : ℂ) * Complex.I).re := by simpa using hs
  have hcut : 2 ≤ Y + 1 := Nat.succ_le_succ hY
  simp only [dirichletPolynomial_eq_partialSum]
  have hone : (fun _ : ℕ => (1 : ℂ)) = (1 : ℕ → ℂ) := by
    funext n
    rfl
  rw [hone]
  simpa [AbsoluteReciprocalCompatibility.zetaPartial,
    AbsoluteReciprocalCompatibility.moebiusPartial, Nat.cast_add, Nat.cast_one] using
    AbsoluteReciprocalCompatibility.reciprocal_product_error_explicit hσ hshift hcut

end RiemannResearch.Analysis.AnalyticAbsoluteReciprocal
