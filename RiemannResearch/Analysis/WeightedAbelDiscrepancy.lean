import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Weighted Abel summation with an exact discrepancy

Source: user-provided argument, `RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`
§3 and §9.2, supporting the discrepancy decomposition and proof strategy.
This reusable theorem retains both endpoints. In the full prime-power
application the weights are Λ(n)/sqrt(n) and F(x)=2(sqrt(x)-1).
-/

open scoped BigOperators
open MeasureTheory Set
namespace RiemannResearch.Analysis

/-- Exact weighted integer counting, including the integer upper endpoint. -/
noncomputable def abelCounting (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, w n

/-- A finite exact Abel formula with an arbitrary differentiable comparison
primitive F. No estimate or positivity assumption on w or the discrepancy
is used. The lower comparison boundary is retained as well. -/
theorem weighted_abel_discrepancy (w : ℕ → ℝ) (hw : w 0 = 0)
    (g F F' : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b)
    (hg : ∀ x ∈ Icc 1 b, DifferentiableAt ℝ g x)
    (hg' : ContinuousOn (deriv g) (Icc 1 b))
    (hF : ∀ x ∈ Icc 1 b, HasDerivAt F (F' x) x)
    (hF' : ContinuousOn F' (Icc 1 b)) :
    -2 * (∑ n ∈ Finset.Icc 0 ⌊b⌋₊, w n * g n) =
      -2 * g b * (abelCounting w b - F b) - 2 * g 1 * F 1
      -2 * (∫ x in Ioc 1 b, g x * F' x)
      +2 * ∫ x in Ioc 1 b, deriv g x * (abelCounting w x - F x) := by
  have hcF : ContinuousOn F (Icc 1 b) := by
    intro x hx
    exact (hF x hx).continuousAt.continuousWithinAt
  have hiL : IntegrableOn (fun x => deriv g x * F x) (Icc 1 b) :=
    (hg'.mul hcF).integrableOn_Icc
  have hiA := integrableOn_mul_sum_Icc w (m := 0)
    (by norm_num : (0 : ℝ) ≤ 1) hg'.integrableOn_Icc
  have hiE : IntegrableOn (fun x => deriv g x * (abelCounting w x - F x))
      (Icc 1 b) := by
    convert hiA.sub hiL using 1
    ext x
    simp only [abelCounting, Pi.sub_apply]
    ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (v := F) (u' := deriv g) (v' := F') (a := 1) (b := b)
    (by simpa only [uIcc_of_le hb] using fun x hx => (hg x hx).hasDerivAt)
    (by simpa only [uIcc_of_le hb] using hF)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr hg'.integrableOn_Icc)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr hF'.integrableOn_Icc)
  simp only [intervalIntegral.integral_of_le hb] at hparts
  have hsplit : (∫ x in Ioc 1 b, deriv g x * abelCounting w x) =
      (∫ x in Ioc 1 b, deriv g x * F x) +
      (∫ x in Ioc 1 b, deriv g x * (abelCounting w x - F x)) := by
    rw [← integral_add (hiL.mono_set Ioc_subset_Icc_self)
      (hiE.mono_set Ioc_subset_Icc_self)]
    congr 1
    ext x
    ring
  have hs := sum_mul_eq_sub_integral_mul₀ w hw b hg hg'.integrableOn_Icc
  simp_rw [mul_comm (w _) (g _)]
  change ∑ n ∈ Finset.Icc 0 ⌊b⌋₊, g n * w n =
    g b * abelCounting w b - ∫ x in Ioc 1 b, deriv g x * abelCounting w x at hs
  rw [hs, hsplit, hparts]
  ring

end RiemannResearch.Analysis
