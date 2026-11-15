import RiemannResearch.RH.ExactHeadResidualTail
import Mathlib.Tactic.Linarith

/-!
# Exact head/tail correlations in the Pareto Hilbert space

Source: continuation of the user-provided signed-head detection catalog,
14 November 2026. Reuse the established shifted l2 tail. The primary
identity retains the signed tail correlation. The subsequent estimate
applies Cauchy--Schwarz only to the omitted coordinates.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Exact head/tail correlation split, without a vanishing-head assumption.
Source: signed-head detection continuation, 14 November 2026. -/
theorem hilbertTailShift_inner_sub_head (f g : ThresholdHilbert) (N : ℕ) :
    inner ℝ (hilbertTailShift f N) (hilbertTailShift g N) =
      inner ℝ f g - ∑ n ∈ Finset.range N, f n * g n := by
  have h := (hilbert_coordinate_mul_summable f g).sum_add_tsum_nat_add N
  have hf : inner ℝ f g = ∑' n, f n * g n := by
    simp only [lp.inner_eq_tsum, RCLike.inner_apply, conj_trivial, mul_comm]
  have ht : inner ℝ (hilbertTailShift f N) (hilbertTailShift g N) =
      ∑' n, f (n+N) * g (n+N) := by
    simp only [lp.inner_eq_tsum, RCLike.inner_apply, conj_trivial, mul_comm, hilbertTailShift]
  rw [hf, ht]
  linarith only [h]

/-- Cauchy--Schwarz bounds just the omitted correlation, with exact tail energies. -/
theorem hilbertTailShift_correlation_bound (f g : ThresholdHilbert) (N : ℕ) :
    |inner ℝ f g - ∑ n ∈ Finset.range N, f n*g n| ≤
      Real.sqrt ((‖f‖^2 - ∑ n ∈ Finset.range N, (f n)^2) *
        (‖g‖^2 - ∑ n ∈ Finset.range N, (g n)^2)) := by
  rw [← hilbertTailShift_norm_sq, ← hilbertTailShift_norm_sq, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_norm, abs_norm,
    ← hilbertTailShift_inner_sub_head]
  exact abs_real_inner_le_norm _ _

end RiemannResearch.RH.Pareto
