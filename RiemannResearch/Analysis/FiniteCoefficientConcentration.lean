import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Finite coefficient concentration bounds

Elementary Cauchy--Schwarz consequences for absolute coefficient mass.
The concrete consumer is RH.ProjectedDualColumnConcentration. Source:
the user's request to isolate l2 energy and effective support, 28 September 2026.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis
/-- Finite l1-to-l2 comparison with its exact dimension factor. -/
theorem finite_sum_abs_sq_le_card_energy {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, |x i|) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, x i ^ 2 := by
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs]
    using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => |x i|)

/-- Weighted finite l1-to-l2 comparison, retaining the chosen weights. -/
theorem finite_sum_abs_sq_le_weighted_energy {ι : Type*} (s : Finset ι)
    (x w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, |x i|) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, x i ^ 2 / w i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => (hw i hi).le)
    (fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le)
  intro i hi
  apply le_of_eq
  rw [sq_abs]
  field_simp [(hw i hi).ne']

/-- Two-set concentration estimate retaining the complete complement energy. -/
theorem finite_sum_abs_sq_le_split_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) :
    (∑ i, |x i|) ^ 2 ≤
      2 * ((s.card : ℝ) * (∑ i ∈ s, x i ^ 2) +
        (sᶜ.card : ℝ) * (∑ i ∈ sᶜ, x i ^ 2)) := by
  rw [← Finset.sum_add_sum_compl s (fun i => |x i|)]
  have h1 := finite_sum_abs_sq_le_card_energy s x
  have h2 := finite_sum_abs_sq_le_card_energy sᶜ x
  nlinarith [sq_nonneg ((∑ i ∈ s, |x i|) - ∑ i ∈ sᶜ, |x i|)]
end RiemannResearch.Analysis
