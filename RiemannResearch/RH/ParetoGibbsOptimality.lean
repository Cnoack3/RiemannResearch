import RiemannResearch.RH.ParetoGibbsGammaDefect
import RiemannResearch.RH.ParetoGibbsSpectralGap

/-!
# The pi/4 bound is the actual optimal operator bound

Finite Gamma-weighted tail-basis vectors have squared norms tending to
infinity and uniformly bounded Rayleigh defects. Thus every smaller
constant fails for the actual infinite Gibbs operator on its mean-zero
Hilbert space. This establishes optimality, without claiming an entire
spectral interval or importing a spectral formula from the literature.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

def gibbsSchurTruncation (N : ℕ) : ThresholdHilbert :=
  ∑ n ∈ Finset.range N, gibbsSchurWeight n • tailBasisHilbert n

theorem gibbsSchurTruncation_mean_zero (N : ℕ) :
    inner ℝ (gibbsSchurTruncation N) hilbertOne = 0 := by
  unfold gibbsSchurTruncation
  simp only [sum_inner, inner_smul_left, RCLike.conj_to_real, tailBasis_inner_one,
    mul_zero, Finset.sum_const_zero]

theorem gibbsSchurTruncation_norm_sq (N : ℕ) :
    ‖gibbsSchurTruncation N‖^2 = gibbsSchurSquareSum N :=
  tailBasis_sum_norm_sq (Finset.range N) gibbsSchurWeight

theorem gibbsSchurTruncation_quadratic (N : ℕ) :
    inner ℝ (gibbsSchurTruncation N) (hilbertGibbs (gibbsSchurTruncation N)) =
      gibbsSchurQuadraticSum N :=
  tailBasis_sum_gibbs_quadratic (Finset.range N) gibbsSchurWeight

/-- Explicit finite-basis vectors witness failure of every smaller bound.
Their images are evaluated by the full infinite Gibbs operator. -/
theorem gibbsSchurTruncation_beats_constant (c : ℝ) (hc : c < Real.pi/4) :
    ∃ N : ℕ, gibbsSchurTruncation N ≠ 0 ∧
      c * ‖gibbsSchurTruncation N‖ < ‖hilbertGibbs (gibbsSchurTruncation N)‖ := by
  have hd : 0 < Real.pi/4-c := sub_pos.mpr hc
  have hq : 0 < Real.pi/4+1 := by positivity
  obtain ⟨N, hN⟩ := gibbsSchurSquareSum_unbounded ((Real.pi/4+1)/(Real.pi/4-c))
  have hS : 0 < gibbsSchurSquareSum N :=
    lt_trans (div_pos hq hd) hN
  have hlarge : Real.pi/4+1 < gibbsSchurSquareSum N*(Real.pi/4-c) :=
    (div_lt_iff₀ hd).mp hN
  refine ⟨N, ?_, ?_⟩
  · intro hz
    have hzero : gibbsSchurSquareSum N = 0 := by
      rw [← gibbsSchurTruncation_norm_sq, hz, norm_zero]
      norm_num
    linarith
  · by_contra hnot
    have hle : ‖hilbertGibbs (gibbsSchurTruncation N)‖ ≤ c * ‖gibbsSchurTruncation N‖ :=
      le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_left hle (norm_nonneg (gibbsSchurTruncation N))
    have hinner := real_inner_le_norm (gibbsSchurTruncation N)
      (hilbertGibbs (gibbsSchurTruncation N))
    rw [gibbsSchurTruncation_quadratic] at hinner
    have hnorm := gibbsSchurTruncation_norm_sq N
    have hdefect := gibbsSchur_truncation_defect_le N
    nlinarith

theorem hilbertGibbs_meanZero_lower_witness (c : ℝ) (hc : c < Real.pi/4) :
    ∃ f : ThresholdHilbert, inner ℝ f hilbertOne = 0 ∧ f ≠ 0 ∧
      c * ‖f‖ < ‖hilbertGibbs f‖ := by
  obtain ⟨N, hN, hbound⟩ := gibbsSchurTruncation_beats_constant c hc
  exact ⟨gibbsSchurTruncation N, gibbsSchurTruncation_mean_zero N, hN, hbound⟩

/-- Exactly the constants at least pi/4 bound the actual operator on the
whole mean-zero space. In particular, pi/4 is its optimal norm bound. -/
theorem hilbertGibbs_meanZero_optimal_constant_iff (c : ℝ) :
    (∀ f : ThresholdHilbert, inner ℝ f hilbertOne = 0 →
      ‖hilbertGibbs f‖ ≤ c * ‖f‖) ↔ Real.pi/4 ≤ c := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨f, hf, hne, hlt⟩ := hilbertGibbs_meanZero_lower_witness c (lt_of_not_ge hc)
    exact (not_lt_of_ge (h f hf)) hlt
  · intro hc f hf
    exact (hilbertGibbs_meanZero_norm_le f hf).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg f))

/-- The actual Gibbs operator restricted to the closed mean-zero subspace. -/
def hilbertGibbsMeanZeroContinuous : tailBasisSpan.topologicalClosure →L[ℝ] ThresholdHilbert :=
  hilbertGibbsContinuous.comp tailBasisSpan.topologicalClosure.subtypeL

/-- Exact operator norm of the actual restriction to the mean-zero space. -/
theorem hilbertGibbsMeanZeroContinuous_norm : ‖hilbertGibbsMeanZeroContinuous‖ = Real.pi/4 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    change ‖hilbertGibbs (f : ThresholdHilbert)‖ ≤ (Real.pi/4)*‖(f : ThresholdHilbert)‖
    exact hilbertGibbs_meanZero_norm_le _
      ((tailBasis_mem_closure_iff_mean_zero _).mp f.property)
  · apply (hilbertGibbs_meanZero_optimal_constant_iff ‖hilbertGibbsMeanZeroContinuous‖).mp
    intro f hf
    let g : tailBasisSpan.topologicalClosure :=
      ⟨f, (tailBasis_mem_closure_iff_mean_zero f).mpr hf⟩
    exact hilbertGibbsMeanZeroContinuous.le_opNorm g

end
end RiemannResearch.RH.Pareto
