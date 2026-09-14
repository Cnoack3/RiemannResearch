import RiemannResearch.RH.ParetoExponentialRealization
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact dilation law for ordinary Pareto log moments

Source: the user-provided Ramanujan--Laguerre continuation, Sections 3--7.
Exponential coordinates convert integer dilation to translation. The exact
binomial identity is used to construct the actual dyadic coefficient matrix.
The zero-coordinate hypothesis removes the negative-coordinate boundary.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre

theorem exponentialLift_eq_zero_of_neg {F : ℕ → ℝ} (hF : F 0 = 0)
    {t : ℝ} (ht : t < 0) : exponentialLift F t = 0 := by
  simp only [exponentialLift, Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr ht), hF]

theorem ordinaryMoment_eq_full_integral {F : ℕ → ℝ} (hF : F 0 = 0) (j : ℕ) :
    ordinaryMoment F j = ∫ t : ℝ, exponentialLift F t * t ^ j * Real.exp (-t) := by
  unfold ordinaryMoment
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [exponentialLift_eq_zero_of_neg hF (lt_of_not_ge ht), zero_mul, zero_mul]

theorem ordinaryMoment_full_integrable {F : ℕ → ℝ}
    (hF : F 0 = 0) (hI : AllMomentsIntegrable F) (j : ℕ) :
    Integrable (fun t : ℝ => exponentialLift F t * t ^ j * Real.exp (-t)) := by
  apply (hI j).integrable_of_forall_notMem_eq_zero
  intro t ht
  rw [exponentialLift_eq_zero_of_neg hF (lt_of_not_ge ht), zero_mul, zero_mul]

theorem exponentialLift_dilation_translate (F : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (t : ℝ) :
    exponentialLift (dilation q F) (t + Real.log q) = (q : ℝ) * exponentialLift F t := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hfloor : ⌊Real.exp (t + Real.log q)⌋₊ / q = ⌊Real.exp t⌋₊ := by
    rw [← Nat.floor_div_natCast, Real.exp_add, Real.exp_log hqR]
    congr 1
    field_simp [ne_of_gt hqR]
  simp only [exponentialLift, dilation, hfloor]

theorem ordinaryMoment_dilation {F : ℕ → ℝ} (hF : F 0 = 0)
    (hI : AllMomentsIntegrable F) (q : ℕ) (hq : 0 < q) (j : ℕ) :
    ordinaryMoment (dilation q F) j =
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * Real.log q ^ i * ordinaryMoment F (j - i) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hD : dilation q F 0 = 0 := by simp [dilation, hF]
  rw [ordinaryMoment_eq_full_integral hD]
  rw [← integral_add_right_eq_self
    (fun t : ℝ => exponentialLift (dilation q F) t * t ^ j * Real.exp (-t))
    (Real.log q)]
  have hshift : (fun t : ℝ => exponentialLift (dilation q F) (t + Real.log q) *
      (t + Real.log q) ^ j * Real.exp (-(t + Real.log q))) =
      (fun t : ℝ => exponentialLift F t * (Real.log q + t) ^ j * Real.exp (-t)) := by
    funext t
    rw [exponentialLift_dilation_translate F q hq t]
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log q), Real.exp_log hqR]
    field_simp [ne_of_gt hqR]
    ring
  rw [hshift]
  have hexpand : (fun t : ℝ => exponentialLift F t * (Real.log q + t) ^ j *
      Real.exp (-t)) = fun t : ℝ =>
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Real.log q ^ i *
        (exponentialLift F t * t ^ (j - i) * Real.exp (-t)) := by
    funext t
    rw [add_pow, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hexpand, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul, ← ordinaryMoment_eq_full_integral hF]
  · intro i hi
    exact (ordinaryMoment_full_integrable hF hI (j - i)).const_mul _

end RiemannResearch.RH.Pareto.RamanujanLaguerre
