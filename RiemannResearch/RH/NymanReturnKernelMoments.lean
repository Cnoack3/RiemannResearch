import RiemannResearch.RH.NymanReturnKernelBounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Integrability, all polynomial moments, and positive mass of the actual kernel

The actual cumulative-beta kernel is measurable because it is a fixed
function of the natural floor of exp(t). Its support and pointwise bounds
give domination by exp(-|t|/2), including every polynomial moment.
Its mass is strictly positive because the kernel is positive throughout
the interval (0, log 2). No integrability, moment, or positivity assumption
on the output kernel is retained.
-/

open MeasureTheory Set Filter

namespace RiemannResearch.RH

noncomputable section

theorem measurable_nymanReturnKernel (n : ℕ) : Measurable (nymanReturnKernel n) := by
  have hm : Measurable (fun t : ℝ =>
      (⌊Real.exp t⌋₊ : ℝ) / n - (⌊Real.exp t⌋₊ / n : ℕ)) :=
    (measurable_from_nat (f := fun M : ℕ => (M : ℝ) / n - (M / n : ℕ))).comp
      (Nat.measurable_floor.comp Real.continuous_exp.measurable)
  have he : Measurable (fun t : ℝ => Real.exp (-t / 2)) := by fun_prop
  change Measurable (fun t : ℝ =>
    Real.exp (-t / 2) * nymanCumulativeBeta n (Real.exp t))
  convert he.mul hm using 1 <;>
    first | rfl | (funext t; simp only [nymanCumulativeBeta_eq, Pi.mul_apply])

private theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => Real.exp (-a * |t|)) := by
  have hp : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [abs_of_pos (show 0 < t from ht)]
  have hn : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic ha 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    simp only [abs_of_nonpos (show t ≤ 0 from ht), mul_neg, neg_mul, neg_neg]
  have hu := hn.union hp
  rwa [Iic_union_Ioi, integrableOn_univ] at hu

private theorem integrable_pow_abs_mul_exp_half (j : ℕ) :
    Integrable (fun t : ℝ => |t| ^ j * Real.exp (-(1 / 2 : ℝ) * |t|)) := by
  have hp : Integrable (fun t : ℝ => Real.exp ((-(1 / 2 : ℝ) + 1 / 4) * |t|)) := by
    convert integrable_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4) using 1
    norm_num
  have hm : Integrable (fun t : ℝ => Real.exp ((-(1 / 2 : ℝ) - 1 / 4) * |t|)) := by
    convert integrable_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 3 / 4) using 1
    norm_num
  simpa only [abs_abs, neg_div] using
    ProbabilityTheory.integrable_pow_abs_mul_exp_of_integrable_exp_mul
      (X := fun t : ℝ => |t|) (v := -(1 / 2 : ℝ)) (t := (1 / 4 : ℝ))
      (by norm_num) hp hm j

theorem nymanReturnKernel_le_exp_abs {n : ℕ} (hn : 0 < n) (t : ℝ) :
    nymanReturnKernel n t ≤ Real.exp (-(1 / 2 : ℝ) * |t|) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    convert nymanReturnKernel_le_exp hn t using 1 <;> congr 1 <;> ring
  · rw [nymanReturnKernel_eq_zero_of_neg n (lt_of_not_ge ht)]
    exact Real.exp_nonneg _

/-- Every absolute polynomial moment of the concrete positive kernel is finite. -/
theorem integrable_pow_abs_nymanReturnKernel {n : ℕ} (hn : 0 < n) (j : ℕ) :
    Integrable (fun t : ℝ => |t| ^ j * nymanReturnKernel n t) := by
  apply (integrable_pow_abs_mul_exp_half j).mono'
  · exact ((continuous_abs.pow j).measurable.mul
      (measurable_nymanReturnKernel n)).aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (abs_nonneg t) j) (nymanReturnKernel_nonneg hn t))]
    exact mul_le_mul_of_nonneg_left (nymanReturnKernel_le_exp_abs hn t)
      (pow_nonneg (abs_nonneg t) j)

theorem integrable_nymanReturnKernel {n : ℕ} (hn : 0 < n) :
    Integrable (nymanReturnKernel n) := by
  simpa only [pow_zero, one_mul] using integrable_pow_abs_nymanReturnKernel hn 0

/-- The first absolute moment in the exact form needed by the scaled-kernel
approximation theorem. -/
theorem integrable_abs_mul_abs_nymanReturnKernel {n : ℕ} (hn : 0 < n) :
    Integrable (fun t : ℝ => |t| * |nymanReturnKernel n t|) := by
  convert integrable_pow_abs_nymanReturnKernel hn 1 using 1
  ext t
  rw [pow_one, abs_of_nonneg (nymanReturnKernel_nonneg hn t)]

/-- The actual kernel has strictly positive mass for every conductor n ≥ 2. -/
theorem integral_nymanReturnKernel_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < ∫ t : ℝ, nymanReturnKernel n t := by
  have hn0 : 0 < n := by omega
  apply (integral_pos_iff_support_of_nonneg
    (nymanReturnKernel_nonneg hn0) (integrable_nymanReturnKernel hn0)).2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Ioo (0 : ℝ) (Real.log 2) ⊆ Function.support (nymanReturnKernel n) := by
    intro t ht
    exact (nymanReturnKernel_pos hn ht.1.le ht.2).ne'
  have hv : 0 < volume (Ioo (0 : ℝ) (Real.log 2)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact hv.trans_le (measure_mono hs)

end
end RiemannResearch.RH
