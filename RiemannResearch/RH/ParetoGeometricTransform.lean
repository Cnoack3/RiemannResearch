import RiemannResearch.RH.ParetoGeometricMixture
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannResearch.RH.ParetoGeometricEnergy
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
Source: user-provided total-variance geometric-mixture research note §2.
This module constructs the actual infinite geometric transform and proves its
mean equals the complete Pareto mean. Indices n represent positive integers n+1.
-/

open scoped BigOperators
open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The actual conditional geometric transform, with the full infinite series. -/
def geometricTransform (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, f n * geometricProbability n t

private theorem geometricProbability_continuous (n : ℕ) :
    Continuous (geometricProbability n) := by
  exact (continuous_const.sub continuous_id).mul (continuous_id.pow n)

private theorem geometricProbability_set_integral (n : ℕ) :
    (∫ t : ℝ in Set.Ioc 0 1, geometricProbability n t) = paretoWeight n := by
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact geometricProbability_integral n

/-- The absolute integral of every series term is its exact Pareto mass. -/
theorem geometricTransform_term_integral_norm (f : ℕ → ℝ) (n : ℕ) :
    (∫ t : ℝ in Set.Ioc 0 1, ‖f n * geometricProbability n t‖) =
      |f n| * paretoWeight n := by
  calc
    _ = ∫ t : ℝ in Set.Ioc 0 1, |f n| * geometricProbability n t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (geometricProbability_nonneg n ht')]
    _ = |f n| * paretoWeight n := by
      rw [integral_const_mul, geometricProbability_set_integral]

/-- Absolute Pareto summability justifies the entire geometric mixture interchange. -/
theorem geometricTransform_integral_of_summable (f : ℕ → ℝ)
    (hf : Summable (fun n => |f n| * paretoWeight n)) :
    (∫ t : ℝ in 0..1, geometricTransform f t) =
      ∑' n, paretoWeight n * f n := by
  have hi (n : ℕ) : Integrable (fun t : ℝ => f n * geometricProbability n t)
      (volume.restrict (Set.Ioc 0 1)) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)).mp
        ((continuous_const.mul (geometricProbability_continuous n)).intervalIntegrable 0 1)
  have hnorm : Summable (fun n =>
      ∫ t : ℝ in Set.Ioc 0 1, ‖f n * geometricProbability n t‖) := by
    simpa only [geometricTransform_term_integral_norm] using hf
  have hswap := integral_tsum_of_summable_integral_norm hi hnorm
  unfold geometricTransform
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), ← hswap]
  apply tsum_congr
  intro n
  rw [integral_const_mul, geometricProbability_set_integral]
  ring

/-- Every bounded sequence satisfies the absolute interchange requirement. -/
theorem paretoWeight_mul_abs_summable {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) : Summable (fun n => |f n| * paretoWeight n) := by
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (paretoWeight_pos n).le)
    (fun n => mul_le_mul_of_nonneg_right (hf n) (paretoWeight_pos n).le)
    (paretoWeight_hasSum.summable.mul_left C)

/-- The law of total expectation for the actual bounded-sequence geometric transform.
There is no truncation and no assumed interchange in this statement. -/
theorem geometricTransform_integral {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    (∫ t : ℝ in 0..1, geometricTransform f t) =
      ∑' n, paretoWeight n * f n :=
  geometricTransform_integral_of_summable f (paretoWeight_mul_abs_summable hf)

end
end RiemannResearch.RH.Pareto


/-!
Source: user-provided geometric-mixture research note §§2 and 4.
The exact squared-transform integral is the full product-index Hankel quadratic
form. All interchange and absolute convergence requirements are discharged for
bounded sequences.
-/

open scoped BigOperators
open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Absolute convergence of the actual conditional series at each t < 1. -/
theorem geometricTransform_norm_summable {f : ℕ → ℝ} {C t : ℝ}
    (hf : ∀ n, |f n| ≤ C) (ht : t ∈ Set.Ico 0 1) :
    Summable (fun n => ‖f n * geometricProbability n t‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) ((geometricProbability_hasSum ht).summable.mul_left C)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (geometricProbability_nonneg n ⟨ht.1, ht.2.le⟩)]
  exact mul_le_mul_of_nonneg_right (hf n)
    (geometricProbability_nonneg n ⟨ht.1, ht.2.le⟩)

/-- Pointwise squaring of the geometric transform keeps every pair of indices. -/
theorem geometricTransform_sq_eq_tsum {f : ℕ → ℝ} {C t : ℝ}
    (hf : ∀ n, |f n| ≤ C) (ht : t ∈ Set.Icc 0 1) :
    geometricTransform f t ^ 2 = ∑' p : ℕ × ℕ,
      (f p.1 * f p.2) * (geometricProbability p.1 t * geometricProbability p.2 t) := by
  by_cases ht1 : t = 1
  · subst t
    simp [geometricTransform, geometricProbability]
  · have htlt : t < 1 := by
      rcases lt_or_eq_of_le ht.2 with h | h
      · exact h
      · exact False.elim (ht1 h)
    have ht' : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht.1, htlt⟩
    have hs := geometricTransform_norm_summable hf ht'
    unfold geometricTransform
    rw [pow_two, tsum_mul_tsum_of_summable_norm hs hs]
    apply tsum_congr
    intro p
    ring

/-- The actual infinite transform's squared integral equals its full kernel form. -/
theorem geometricTransform_sq_integral {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    (∫ t : ℝ in 0..1, geometricTransform f t ^ 2) =
      ∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * (f p.1 * f p.2) := by
  let G : ℕ × ℕ → ℝ → ℝ := fun p t =>
    (f p.1 * f p.2) * (geometricProbability p.1 t * geometricProbability p.2 t)
  have hK (p : ℕ × ℕ) :
      (∫ t : ℝ in Set.Ioc 0 1,
        geometricProbability p.1 t * geometricProbability p.2 t) =
          geometricKernel p.1 p.2 := by
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact geometricProbability_product_integral p.1 p.2
  have hcont (n : ℕ) : Continuous (geometricProbability n) :=
    (continuous_const.sub continuous_id).mul (continuous_id.pow n)
  have hi (p : ℕ × ℕ) : Integrable (G p) (volume.restrict (Set.Ioc 0 1)) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)).mp
      ((continuous_const.mul ((hcont p.1).mul (hcont p.2))).intervalIntegrable 0 1)
  have hnorm (p : ℕ × ℕ) :
      (∫ t : ℝ in Set.Ioc 0 1, ‖G p t‖) =
        |f p.1 * f p.2| * geometricKernel p.1 p.2 := by
    calc
      _ = ∫ t : ℝ in Set.Ioc 0 1, |f p.1 * f p.2| *
          (geometricProbability p.1 t * geometricProbability p.2 t) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        have hpos := mul_nonneg (geometricProbability_nonneg p.1 ht')
          (geometricProbability_nonneg p.2 ht')
        change ‖(f p.1 * f p.2) *
          (geometricProbability p.1 t * geometricProbability p.2 t)‖ = _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
      _ = _ := by rw [integral_const_mul, hK]
  have hcross (p : ℕ × ℕ) : |f p.1 * f p.2| ≤ C ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hf p.1) (hf p.2) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hf p.1))
  have hs : Summable (fun p : ℕ × ℕ =>
      |f p.1 * f p.2| * geometricKernel p.1 p.2) :=
    Summable.of_nonneg_of_le
      (fun p => mul_nonneg (abs_nonneg _) (geometricKernel_pos p.1 p.2).le)
      (fun p => mul_le_mul_of_nonneg_right (hcross p)
        (geometricKernel_pos p.1 p.2).le)
      (geometricKernel_prod_summable.mul_left (C ^ 2))
  have hsNorm : Summable (fun p : ℕ × ℕ =>
      ∫ t : ℝ in Set.Ioc 0 1, ‖G p t‖) := by
    simpa only [hnorm] using hs
  have hswap := integral_tsum_of_summable_integral_norm hi hsNorm
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  calc
    _ = ∫ t : ℝ in Set.Ioc 0 1, ∑' p : ℕ × ℕ, G p t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact geometricTransform_sq_eq_tsum hf ⟨ht.1.le, ht.2⟩
    _ = ∑' p : ℕ × ℕ, ∫ t : ℝ in Set.Ioc 0 1, G p t := hswap.symm
    _ = _ := by
      apply tsum_congr
      intro p
      change (∫ t : ℝ in Set.Ioc 0 1, (f p.1 * f p.2) *
        (geometricProbability p.1 t * geometricProbability p.2 t)) = _
      rw [integral_const_mul, hK]
      ring

/-- The complete positive arithmetic energy is exactly the second-moment loss
under the genuine conditional geometric transform. -/
theorem geometricTransform_full_energy {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    (∑' n, paretoWeight n * f n ^ 2) -
      (∫ t : ℝ in 0..1, geometricTransform f t ^ 2) =
        (1 / 2 : ℝ) * (∑' p : ℕ × ℕ,
          geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2) := by
  rw [geometricTransform_sq_integral hf]
  exact (geometricKernel_infinite_energy_identity hf).symm

end
end RiemannResearch.RH.Pareto


/-!
Source: user-provided geometric-mixture total-variance research note §2.
The complete Pareto approximation error splits into the actual geometric
transform's approximation error and the full positive arithmetic energy.
-/

open scoped BigOperators
open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Complementation commutes with the actual transform at each admissible latent parameter. -/
theorem geometricTransform_one_sub {f : ℕ → ℝ} {C t : ℝ}
    (hf : ∀ n, |f n| ≤ C) (ht : t ∈ Set.Ico 0 1) :
    geometricTransform (fun n => 1 - f n) t = 1 - geometricTransform f t := by
  have hs := (geometricTransform_norm_summable hf ht).of_norm
  have hp := geometricProbability_hasSum ht
  unfold geometricTransform
  have hterm (n : ℕ) : (1 - f n) * geometricProbability n t =
      geometricProbability n t - f n * geometricProbability n t := by ring
  simp_rw [hterm]
  rw [hp.summable.tsum_sub hs, hp.tsum_eq]

/-- Exact full error decomposition for every bounded sequence, retaining the
positive double-series energy and both infinite tails. -/
theorem geometricTransform_full_error_identity {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    (∑' n, paretoWeight n * (1 - f n) ^ 2) =
      (∫ t : ℝ in 0..1, (1 - geometricTransform f t) ^ 2) +
        (1 / 2 : ℝ) * (∑' p : ℕ × ℕ,
          geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2) := by
  have hg (n : ℕ) : |1 - f n| ≤ 1 + C := by
    calc
      |1 - f n| ≤ 1 + |f n| := by
        simpa only [Real.norm_eq_abs, abs_one] using norm_sub_le (1 : ℝ) (f n)
      _ ≤ 1 + C := add_le_add le_rfl (hf n)
  have hI : (∫ t : ℝ in 0..1, geometricTransform (fun n => 1 - f n) t ^ 2) =
      ∫ t : ℝ in 0..1, (1 - geometricTransform f t) ^ 2 := by
    simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Set.Ioc (0 : ℝ) 1)).ae_ne 1] with t ht htne
    have htlt : t < 1 := by
      rcases lt_or_eq_of_le ht.2 with h | h
      · exact h
      · exact False.elim (htne h)
    rw [geometricTransform_one_sub hf ⟨ht.1.le, htlt⟩]
  have hE : (∑' p : ℕ × ℕ, geometricKernel p.1 p.2 *
      ((1 - f p.1) - (1 - f p.2)) ^ 2) =
      ∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2 := by
    apply tsum_congr
    intro p
    ring
  have h := geometricTransform_full_energy hg
  rw [hI, hE] at h
  linarith

end
end RiemannResearch.RH.Pareto
