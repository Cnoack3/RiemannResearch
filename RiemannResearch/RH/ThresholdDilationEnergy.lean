import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Tactic.Linarith

/-!
# Dilation on all square-summable Pareto sequences

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, September 7, 2026,
Sections 2 and 10. These statements remove the bounded-sequence restriction
from the existing Pareto dilation norm and expectation identities. The only
analytic hypothesis is the defining weighted square summability of H.
No Nyman--Beurling criterion or arithmetic approximation estimate is used.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Nonnegative integrable functions remain integrable under raw pullback,
including the complete mass of the first block. -/
theorem weighted_rawPullback_summable {f : ℕ → ℝ}
    (hf0 : ∀ k, 0 ≤ f k) (hf : Summable (fun k => positiveWeight k * f k))
    (m : ℕ) (hm : 0 < m) :
    Summable (fun k => positiveWeight k * rawPullback m f k) := by
  apply summable_of_sum_range_le
    (fun k => mul_nonneg (positiveWeight_nonneg k) (hf0 (k / m)))
    (c := paretoMean f / m + (1 - 1 / (m : ℝ)) * f 0)
  intro N
  calc
    (∑ k ∈ Finset.range N, positiveWeight k * rawPullback m f k) ≤
        ∑ k ∈ Finset.range (m * (N+1)), positiveWeight k * rawPullback m f k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply Finset.range_mono
        exact le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_left (N+1) hm)
      · intro k hk hk'
        exact mul_nonneg (positiveWeight_nonneg k) (hf0 (k / m))
    _ = (∑ j ∈ Finset.range (N+1), positiveWeight j * f j) / m +
        (1 - 1 / (m : ℝ)) * f 0 := rawPullback_partial_sum m N hm f
    _ ≤ paretoMean f / m + (1 - 1 / (m : ℝ)) * f 0 := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
      exact Summable.sum_le_tsum (Finset.range (N+1))
        (fun k hk => mul_nonneg (positiveWeight_nonneg k) (hf0 k)) hf

/-- Every member of the weighted square-summable space has an absolutely
convergent mean; boundedness of the sequence is not required. -/
theorem weighted_summable_of_square {f : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2)) :
    Summable (fun k => positiveWeight k * f k) := by
  apply (hf.add positiveWeight_summable).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (positiveWeight_nonneg k)]
  have hb : |f k| ≤ (f k)^2 + 1 := by
    have h := sq_nonneg (|f k| - 1)
    have he := sq_abs (f k)
    nlinarith
  simpa [mul_add] using mul_le_mul_of_nonneg_left hb (positiveWeight_nonneg k)

/-- Dilations preserve weighted square summability for every integer parameter.
The input may have an arbitrary value at zero. -/
theorem weighted_square_dilation_summable {f : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2)) (m : ℕ) (hm : 0 < m) :
    Summable (fun k => positiveWeight k * (dilation m f k)^2) := by
  have hd := weighted_rawPullback_summable (fun k => sq_nonneg (f k)) hf m hm
  have he : (fun k => positiveWeight k * (dilation m f k)^2) =
      (fun k => (m : ℝ)^2 * (positiveWeight k * rawPullback m (fun j => (f j)^2) k)) := by
    funext k
    simp only [dilation, rawPullback]
    ring
  rw [he]
  exact hd.mul_left ((m : ℝ)^2)

/-- Full squared-energy identity, including the exact nonzero-anchor anomaly. -/
theorem weighted_square_dilation_boundary {f : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2)) (m : ℕ) (hm : 0 < m) :
    (∑' k, positiveWeight k * (dilation m f k)^2) =
      (m : ℝ) * (∑' k, positiveWeight k * (f k)^2) +
        ((m : ℝ)^2 - m) * (f 0)^2 := by
  have hd := weighted_rawPullback_summable (fun k => sq_nonneg (f k)) hf m hm
  have hr := rawPullback_tsum m hm (fun k => (f k)^2) hf hd
  have he : (fun k => positiveWeight k * (dilation m f k)^2) =
      (fun k => (m : ℝ)^2 * (positiveWeight k * rawPullback m (fun j => (f j)^2) k)) := by
    funext k
    simp only [dilation, rawPullback]
    ring
  rw [he, hd.tsum_mul_left]
  change (m : ℝ)^2 * paretoMean (rawPullback m (fun j => (f j)^2)) = _
  rw [hr]
  unfold paretoMean
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The paper's norm-squared identity for every H sequence, not only bounded ones. -/
theorem weighted_square_dilation {f : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2)) (hf0 : f 0 = 0)
    (m : ℕ) (hm : 0 < m) :
    (∑' k, positiveWeight k * (dilation m f k)^2) =
      (m : ℝ) * (∑' k, positiveWeight k * (f k)^2) := by
  simpa [hf0] using weighted_square_dilation_boundary hf m hm

/-- Expectation preservation on the entire real weighted H, with no unproved
output-summability assumption. -/
theorem paretoMean_dilation_of_square {f : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2)) (hf0 : f 0 = 0)
    (m : ℕ) (hm : 0 < m) : paretoMean (dilation m f) = paretoMean f := by
  exact dilation_tsum m hm f hf0 (weighted_summable_of_square hf)
    (weighted_summable_of_square (weighted_square_dilation_summable hf m hm))

/-- Every mixed inner product of two H sequences is absolutely convergent. -/
theorem weighted_product_summable_of_square {f g : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2))
    (hg : Summable (fun k => positiveWeight k * (g k)^2)) :
    Summable (fun k => positiveWeight k * (f k * g k)) := by
  apply (hf.add hg).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (positiveWeight_nonneg k), abs_mul]
  have hb : |f k| * |g k| ≤ (f k)^2 + (g k)^2 := by
    nlinarith [sq_nonneg (|f k| - |g k|), sq_nonneg (f k), sq_nonneg (g k),
      sq_abs (f k), sq_abs (g k)]
  simpa [mul_add] using mul_le_mul_of_nonneg_left hb (positiveWeight_nonneg k)

/-- Raw mixed inner-product pushforward for all square-summable sequences. -/
theorem paretoInner_rawPullback_of_square {f g : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2))
    (hg : Summable (fun k => positiveWeight k * (g k)^2)) (m : ℕ) (hm : 0 < m) :
    paretoInner (rawPullback m f) (rawPullback m g) = paretoInner f g / m +
      (1 - 1 / (m : ℝ)) * (f 0 * g 0) := by
  have hrf : Summable (fun k => positiveWeight k * (rawPullback m f k)^2) :=
    weighted_rawPullback_summable (fun k => sq_nonneg (f k)) hf m hm
  have hrg : Summable (fun k => positiveWeight k * (rawPullback m g k)^2) :=
    weighted_rawPullback_summable (fun k => sq_nonneg (g k)) hg m hm
  exact rawPullback_tsum m hm (fun k => f k * g k)
    (weighted_product_summable_of_square hf hg)
    (weighted_product_summable_of_square hrf hrg)

/-- Full mixed law for all H sequences, including the exact boundary anomaly. -/
theorem paretoInner_dilation_boundary_of_square {f g : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2))
    (hg : Summable (fun k => positiveWeight k * (g k)^2)) (m : ℕ) (hm : 0 < m) :
    paretoInner (dilation m f) (dilation m g) =
      (m : ℝ) * paretoInner f g + ((m : ℝ)^2 - m) * (f 0 * g 0) := by
  have hrf : Summable (fun k => positiveWeight k * (rawPullback m f k)^2) :=
    weighted_rawPullback_summable (fun k => sq_nonneg (f k)) hf m hm
  have hrg : Summable (fun k => positiveWeight k * (rawPullback m g k)^2) :=
    weighted_rawPullback_summable (fun k => sq_nonneg (g k)) hg m hm
  have hd := weighted_product_summable_of_square hrf hrg
  have he : (fun k => positiveWeight k * (dilation m f k * dilation m g k)) =
      (fun k => (m : ℝ)^2 *
        (positiveWeight k * (rawPullback m f k * rawPullback m g k))) := by
    funext k
    simp only [dilation, rawPullback]
    ring
  unfold paretoInner
  rw [he, hd.tsum_mul_left]
  change (m : ℝ)^2 * paretoInner (rawPullback m f) (rawPullback m g) = _
  rw [paretoInner_rawPullback_of_square hf hg m hm]
  unfold paretoInner
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Exact all-H inner-product scaling. Only one zero anchor is needed to remove
the mixed boundary term. -/
theorem paretoInner_dilation_of_square {f g : ℕ → ℝ}
    (hf : Summable (fun k => positiveWeight k * (f k)^2))
    (hg : Summable (fun k => positiveWeight k * (g k)^2)) (hf0 : f 0 = 0)
    (m : ℕ) (hm : 0 < m) :
    paretoInner (dilation m f) (dilation m g) = (m : ℝ) * paretoInner f g := by
  simpa [hf0] using paretoInner_dilation_boundary_of_square hf hg m hm

end
end RiemannResearch.RH.Pareto
