import RiemannResearch.RH.ParetoGibbsGammaTruncation

/-!
# Uniform defect for the truncated Gamma vectors

The cross-boundary term is bounded by the exact infinite Pareto tail.
Consequently the Rayleigh defect is bounded while the squared norm diverges.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem paretoWeight_shift_tsum (N : ℕ) :
    (∑' m : ℕ, paretoWeight (m+N)) = 1 / ((N : ℝ)+1) := by
  have h := paretoWeight_hasSum.summable.sum_add_tsum_nat_add N
  rw [paretoWeight_hasSum.tsum_eq, paretoWeight_partial_sum] at h
  linarith

theorem gibbsSchur_weighted_tail_le (N n : ℕ) :
    gibbsSchurWeight n *
      (gibbsSchurRow n - gibbsSchurFiniteRow (Finset.range N) n) ≤ 1 / ((N : ℝ)+1) := by
  have hf : Summable (fun m => gibbsSchurWeight n *
      (gibbsComplementKernel n m * gibbsSchurWeight m)) :=
    (gibbsSchurGamma_row_hasSum n).summable.mul_left _
  have hsum := hf.sum_add_tsum_nat_add N
  have htail : gibbsSchurWeight n *
      (gibbsSchurRow n - gibbsSchurFiniteRow (Finset.range N) n) =
        ∑' m : ℕ, gibbsSchurWeight n *
          (gibbsComplementKernel n (m+N) * gibbsSchurWeight (m+N)) := by
    have hfull : (∑' m : ℕ, gibbsSchurWeight n *
        (gibbsComplementKernel n m * gibbsSchurWeight m)) =
        gibbsSchurWeight n * gibbsSchurRow n := tsum_mul_left
    rw [← Finset.mul_sum, hfull] at hsum
    change gibbsSchurWeight n * gibbsSchurFiniteRow (Finset.range N) n +
      (∑' m : ℕ, gibbsSchurWeight n *
        (gibbsComplementKernel n (m+N) * gibbsSchurWeight (m+N))) =
      gibbsSchurWeight n * gibbsSchurRow n at hsum
    linarith
  rw [htail, ← paretoWeight_shift_tsum N]
  apply Summable.tsum_le_tsum _ ((summable_nat_add_iff N).mpr hf)
    ((summable_nat_add_iff N).mpr paretoWeight_hasSum.summable)
  intro m
  calc
    _ = gibbsComplementKernel n (m+N) * gibbsSchurWeight n * gibbsSchurWeight (m+N) := by ring
    _ ≤ _ := gibbsSchur_pair_le_weight n (m+N)

theorem gibbsSchur_truncation_defect_identity (N : ℕ) :
    (Real.pi/4)*gibbsSchurSquareSum N - gibbsSchurQuadraticSum N =
      (∑ n ∈ Finset.range N,
        ((Real.pi/4)*gibbsSchurWeight n^2 - gibbsSchurWeight n*gibbsSchurRow n)) +
      ∑ n ∈ Finset.range N, gibbsSchurWeight n *
        (gibbsSchurRow n - gibbsSchurFiniteRow (Finset.range N) n) := by
  have hQ : gibbsSchurQuadraticSum N =
      ∑ n ∈ Finset.range N, gibbsSchurWeight n*gibbsSchurFiniteRow (Finset.range N) n := by
    unfold gibbsSchurQuadraticSum gibbsSchurFiniteRow
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hQ]
  unfold gibbsSchurSquareSum
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- A uniform analytic error estimate, valid for every cutoff. -/
theorem gibbsSchur_truncation_defect_le (N : ℕ) :
    (Real.pi/4)*gibbsSchurSquareSum N - gibbsSchurQuadraticSum N ≤ Real.pi/4+1 := by
  rw [gibbsSchur_truncation_defect_identity]
  have hI : (∑ n ∈ Finset.range N,
      ((Real.pi/4)*gibbsSchurWeight n^2 - gibbsSchurWeight n*gibbsSchurRow n)) ≤ Real.pi/4 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, (Real.pi/4)*paretoWeight n :=
        Finset.sum_le_sum (fun n hn => gibbsSchur_internal_defect_le n)
      _ = (Real.pi/4)*(1-1/((N : ℝ)+1)) := by
        rw [← Finset.mul_sum, paretoWeight_partial_sum]
      _ ≤ Real.pi/4 := by
        have hq : 0 ≤ Real.pi/4 := by positivity
        have ht : 0 ≤ 1/((N : ℝ)+1) := by positivity
        nlinarith
  have hT : (∑ n ∈ Finset.range N, gibbsSchurWeight n *
      (gibbsSchurRow n - gibbsSchurFiniteRow (Finset.range N) n)) ≤ 1 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, 1/((N : ℝ)+1) :=
        Finset.sum_le_sum (fun n hn => gibbsSchur_weighted_tail_le N n)
      _ = (N : ℝ)/((N : ℝ)+1) := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  linarith

end
end RiemannResearch.RH.Pareto
