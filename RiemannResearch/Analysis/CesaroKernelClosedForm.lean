import RiemannResearch.Analysis.CesaroPosteriorKernel
import Mathlib.Tactic

/-!
# Closed expression for the actual conditional-row kernel

Source: user-provided conditional-iid manuscript, Section 4. The finite endpoint
formula is sent to infinity only after all series and vanishing boundaries have
been justified.
-/
noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative

private theorem inverse_square_summable_from (m : ℕ) (hm : 0 < m) :
    Summable (fun k : ℕ => 1 / (((m + k : ℕ) : ℝ) ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hasSum_weight_from m hm).summable.mul_left 2)
  have hp : (1 : ℝ) ≤ ((m + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + k by omega)
  calc
    _ ≤ 2 / (((m + k : ℕ) : ℝ) * (((m + k : ℕ) : ℝ) + 1)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    _ = 2 * weight (m + k) := by unfold weight; ring

private theorem reciprocal_shift_tendsto (m : ℕ) :
    Tendsto (fun R : ℕ => 1 / ((m + R : ℕ) : ℝ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.add_comm] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat m)

/-- The exact infinite closed kernel, with no suppressed boundary remainder. -/
theorem rowKernel_closed_form (m : ℕ) (hm : 0 < m) :
    rowKernel m = (∑' k : ℕ, 1 / (((m + k : ℕ) : ℝ) ^ 2)) -
      3 / (2 * (m : ℝ)) + 1 / (2 * ((m : ℝ) + 1)) := by
  have h1 : Tendsto (fun R : ℕ => 3 / (2 * ((m + R : ℕ) : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    convert (reciprocal_shift_tendsto m).const_mul (3 / 2 : ℝ) using 1
    · funext R
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · ring
  have h2 : Tendsto (fun R : ℕ => 1 / (2 * (((m + R : ℕ) : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
    convert (reciprocal_shift_tendsto (m + 1)).const_mul (1 / 2 : ℝ) using 1
    · funext R
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · ring
  have hr := ((((inverse_square_summable_from m hm).hasSum.tendsto_sum_nat.sub_const
    (3 / (2 * (m : ℝ)))).add_const (1 / (2 * ((m : ℝ) + 1)))).add h1).sub h2
  have hl := (rowKernel_summable m hm).hasSum.tendsto_sum_nat
  have he : Tendsto (fun R : ℕ => ∑ k ∈ Finset.range R,
      mixtureWeight (m + k) / (((m + k : ℕ) : ℝ) ^ 2)) atTop
      (𝓝 ((∑' k : ℕ, 1 / (((m + k : ℕ) : ℝ) ^ 2)) -
        3 / (2 * (m : ℝ)) + 1 / (2 * ((m : ℝ) + 1)))) := by
    simpa only [rowKernel_finite_boundary m _ hm, add_zero, sub_zero] using hr
  exact tendsto_nhds_unique hl he

end RiemannResearch.Analysis.Cesaro
