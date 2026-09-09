import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ParetoGibbsSchur

/-!
# Exact Gibbs matrix in the orthonormal tail basis

The proof uses the exact finite marginal identities of the full Gibbs
kernel, retaining the constant and infinite tail through its actual Hilbert
vector. This identifies the matrix to which the Gamma Schur estimate applies;
no spectral identity or equality of operators is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The physical point vectors give the original complete Gibbs kernel. -/
theorem paretoPoint_gibbs_inner (i j : ℕ) :
    inner ℝ (paretoPointHilbert i) (hilbertGibbs (paretoPointHilbert j)) =
      geometricKernel i j := by
  rw [real_inner_comm, inner_paretoPoint, hilbertGibbs_physical,
    gibbsAction_weight_mul]
  simp only [hilbertGibbsPhysical_paretoPoint, mul_ite, mul_one, mul_zero]
  simp

private theorem hilbertGibbs_tailBasis (m : ℕ) :
    hilbertGibbs (tailBasisHilbert m) =
      ((m:ℝ)+2) • hilbertGibbs (paretoPointHilbert m) +
        (∑ k ∈ Finset.range m, hilbertGibbs (paretoPointHilbert k)) - hilbertOne := by
  change hilbertGibbsLinear (((m:ℝ)+2) • paretoPointHilbert m +
    (∑ k ∈ Finset.range m, paretoPointHilbert k) - hilbertOne) = _
  rw [map_sub, map_add, map_smul, map_sum]
  change ((m:ℝ)+2) • hilbertGibbs (paretoPointHilbert m) +
    (∑ k ∈ Finset.range m, hilbertGibbs (paretoPointHilbert k)) -
      hilbertGibbs hilbertOne = _
  rw [hilbertGibbs_one]

/-- The complete infinite tail becomes the retained shifted Pareto mass. -/
theorem paretoPoint_gibbs_tail_inner (i m : ℕ) :
    inner ℝ (paretoPointHilbert i) (hilbertGibbs (tailBasisHilbert m)) =
      ((m:ℝ)+2) * geometricKernel i m - paretoWeight (i+m) := by
  rw [hilbertGibbs_tailBasis, inner_sub_right, inner_add_right,
    inner_smul_right, inner_sum, paretoPoint_gibbs_inner, paretoPoint_inner_one]
  simp_rw [paretoPoint_gibbs_inner]
  rw [geometricKernel_partial_sum]
  ring

private theorem paretoWeight_shift_partial_sum (m N : ℕ) :
    (∑ k ∈ Finset.range N, paretoWeight (m+k)) =
      1/((m:ℝ)+1) - 1/((m:ℝ)+(N:ℝ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, paretoWeight_eq_inv_sub]
    push_cast
    ring

/-- A second exact telescoping identity, before the final matrix simplification. -/
theorem sum_paretoPoint_gibbs_tail_inner (n m : ℕ) :
    (∑ i ∈ Finset.range n,
      inner ℝ (paretoPointHilbert i) (hilbertGibbs (tailBasisHilbert m))) =
      (n:ℝ) * paretoWeight (n+m) := by
  simp_rw [paretoPoint_gibbs_tail_inner]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hK : (∑ i ∈ Finset.range n, geometricKernel i m) =
      paretoWeight m - paretoWeight (m+n) := by
    calc
      _ = ∑ i ∈ Finset.range n, geometricKernel m i :=
        Finset.sum_congr rfl fun i _ => geometricKernel_symm i m
      _ = _ := geometricKernel_partial_sum m n
  have hw : (∑ i ∈ Finset.range n, paretoWeight (i+m)) =
      1/((m:ℝ)+1) - 1/((m:ℝ)+(n:ℝ)+1) := by
    simpa only [Nat.add_comm] using paretoWeight_shift_partial_sum m n
  rw [hK, hw]
  unfold paretoWeight
  push_cast
  have h1 : (m:ℝ)+1 ≠ 0 := by positivity
  have h2 : (m:ℝ)+2 ≠ 0 := by positivity
  have h3 : (m:ℝ)+(n:ℝ)+1 ≠ 0 := by positivity
  have h4 : (m:ℝ)+(n:ℝ)+2 ≠ 0 := by positivity
  have h5 : (n:ℝ)+(m:ℝ)+1 ≠ 0 := by positivity
  have h6 : (n:ℝ)+(m:ℝ)+2 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The actual infinite-dimensional Gibbs operator has exactly the complement
matrix used in the Gamma Schur estimate. -/
theorem tailBasis_gibbs_inner (n m : ℕ) :
    inner ℝ (tailBasisHilbert n) (hilbertGibbs (tailBasisHilbert m)) =
      gibbsComplementKernel n m := by
  have hmean : inner ℝ hilbertOne (hilbertGibbs (tailBasisHilbert m)) = 0 := by
    rw [real_inner_comm, hilbertGibbs_mean_inner, tailBasis_inner_one]
  conv_lhs => lhs; unfold tailBasisHilbert
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, sum_inner,
    hmean, paretoPoint_gibbs_tail_inner, sum_paretoPoint_gibbs_tail_inner]
  unfold gibbsComplementKernel geometricKernel paretoWeight
  push_cast
  have h1 : (n:ℝ)+(m:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+(m:ℝ)+2 ≠ 0 := by positivity
  have h3 : (n:ℝ)+(m:ℝ)+3 ≠ 0 := by positivity
  field_simp
  <;> ring

end
end RiemannResearch.RH.Pareto
