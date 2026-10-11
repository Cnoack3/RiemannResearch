import RiemannResearch.Analysis.FiniteStrictTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
Finite conditional transfer from a strict-tail density bound to the hyperbolic
correction. The hypotheses explicitly contain the density estimate; this file
does not prove Selberg's theorem or assert RH.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ZeroDensityTransfer

lemma exponential_sinh_eq (a y t : ℝ) :
    Real.exp (-a * t) * Real.sinh (y * t) =
      (Real.exp ((y - a) * t) - Real.exp ((-y - a) * t)) / 2 := by
  rw [Real.sinh_eq, ← mul_div_assoc, mul_sub,
    ← Real.exp_add, ← Real.exp_add]
  congr 1 <;> congr 1 <;> ring

theorem integrableOn_exponential_sinh {a y : ℝ}
    (hy : 0 ≤ y) (hya : y < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Real.sinh (y * t)) (Ioi 0) := by
  have h₁ : y - a < 0 := sub_neg.mpr hya
  have h₂ : -y - a < 0 := by linarith
  simp_rw [exponential_sinh_eq]
  exact ((integrableOn_exp_mul_Ioi h₁ 0).sub
    (integrableOn_exp_mul_Ioi h₂ 0)).div_const 2

/-- The exact improper integral, retaining both exponential terms. -/
theorem integral_exponential_sinh {a y : ℝ}
    (hy : 0 ≤ y) (hya : y < a) :
    (∫ t : ℝ in Ioi 0, Real.exp (-a * t) * Real.sinh (y * t)) =
      y / (a ^ 2 - y ^ 2) := by
  have h₁ : y - a < 0 := sub_neg.mpr hya
  have h₂ : -y - a < 0 := by linarith
  have hn₁ : y - a ≠ 0 := ne_of_lt h₁
  have hn₂ : -y - a ≠ 0 := ne_of_lt h₂
  have hden : a ^ 2 - y ^ 2 ≠ 0 := by
    have hp : 0 < (a - y) * (a + y) := mul_pos (by linarith) (by linarith)
    apply ne_of_gt
    nlinarith
  simp_rw [exponential_sinh_eq]
  rw [MeasureTheory.integral_div, MeasureTheory.integral_sub
    (integrableOn_exp_mul_Ioi h₁ 0)
    (integrableOn_exp_mul_Ioi h₂ 0),
    integral_exp_mul_Ioi h₁ 0,
    integral_exp_mul_Ioi h₂ 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  <;> ring

/-- Truncating the nonnegative kernel only decreases its integral. -/
theorem intervalIntegral_exponential_sinh_le {a y M : ℝ}
    (hy : 0 ≤ y) (hya : y < a) (hM : 0 ≤ M) :
    (∫ t in (0 : ℝ)..M, Real.exp (-a * t) * Real.sinh (y * t)) ≤
      y / (a ^ 2 - y ^ 2) := by
  rw [intervalIntegral.integral_of_le hM]
  rw [← integral_exponential_sinh hy hya]
  apply MeasureTheory.setIntegral_mono_set (integrableOn_exponential_sinh hy hya)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hy ht.le))
  · exact Filter.Eventually.of_forall (fun t ht => ht.1)

/-- The rational improvement from `y < L/4` to `y ≤ L/8`. -/
theorem density_rational_eighth {C T L y : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hL : 0 < L)
    (hy : 0 ≤ y) (hyL : y ≤ L / 8) :
    2 * C * T * L * y ^ 2 / (L ^ 2 / 16 - y ^ 2) ≤
      (128 * C / 3) * T * y ^ 2 / L := by
  have hySq : y ^ 2 ≤ L ^ 2 / 64 := by
    have hprod : 0 ≤ (L / 8 - y) * (L / 8 + y) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hlower : 3 * L ^ 2 / 64 ≤ L ^ 2 / 16 - y ^ 2 := by nlinarith
  have hden : 0 < L ^ 2 / 16 - y ^ 2 := by
    have hsq : 0 < L ^ 2 := sq_pos_of_pos hL
    nlinarith
  apply (div_le_div_iff₀ hden hL).mpr
  convert mul_le_mul_of_nonneg_right hlower
    (show 0 ≤ (128 * C / 3) * T * y ^ 2 by positivity) using 1 <;> ring

variable {ι : Type*}

/-- Every displacement is retained. The tail estimate is an explicit premise. -/
theorem finite_cosh_density_transfer (s : Finset ι) (x : ι → ℝ)
    (C T L y : ℝ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hL : 0 < L) (hy : 0 ≤ y) (hyL : y < L / 4)
    (hx : ∀ i ∈ s, x i ∈ Icc (0 : ℝ) (1 / 2))
    (hdensity : ∀ v ∈ Icc (0 : ℝ) (1 / 2),
      FiniteStrictTail.tail s x v ≤
        2 * C * T * L * Real.exp (-(L / 4) * v)) :
    (∑ i ∈ s, (Real.cosh (y * x i) - 1)) ≤
      2 * C * T * L * y ^ 2 / (L ^ 2 / 16 - y ^ 2) := by
  classical
  have hf : Continuous (fun t : ℝ => y * Real.sinh (y * t)) := by fun_prop
  have heq : (∑ i ∈ s, (Real.cosh (y * x i) - 1)) =
      FiniteStrictTail.badSum s x (fun t => Real.cosh (y * t) - 1) 0 := by
    unfold FiniteStrictTail.badSum
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hi0 : 0 < x i
    · simp [hi0]
    · have hiEq : x i = 0 := le_antisymm (le_of_not_gt hi0) (hx i hi).1
      simp [hiEq]
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t => Real.cosh (y * t) - 1)
        (y * Real.sinh (y * t)) t := by
    intro t
    simpa only [Function.comp_def, mul_one, mul_comm] using
      ((Real.hasDerivAt_cosh (y * t)).comp t
        ((hasDerivAt_id t).const_mul y)).sub_const 1
  have hcake := FiniteStrictTail.layerCake s x
    (fun t => Real.cosh (y * t) - 1)
    (fun t => y * Real.sinh (y * t)) hf hderiv 0 (1 / 2)
    (by norm_num) (fun i hi => (hx i hi).2)
  rw [heq, hcake]
  simp only [mul_zero, Real.cosh_zero, sub_self, zero_mul, zero_add]
  calc
    (∫ v in (0 : ℝ)..(1 / 2),
        FiniteStrictTail.tail s x v * (y * Real.sinh (y * v)))
        ≤ ∫ v in (0 : ℝ)..(1 / 2),
          (2 * C * T * L * Real.exp (-(L / 4) * v)) *
            (y * Real.sinh (y * v)) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (FiniteStrictTail.intervalIntegrable_tail_mul s x _ hf 0 (1 / 2))
        (by apply Continuous.intervalIntegrable; fun_prop)
      intro v hv
      exact mul_le_mul_of_nonneg_right (hdensity v hv)
        (mul_nonneg hy (Real.sinh_nonneg_iff.mpr (mul_nonneg hy hv.1)))
    _ = (2 * C * T * L * y) *
        (∫ v in (0 : ℝ)..(1 / 2),
          Real.exp (-(L / 4) * v) * Real.sinh (y * v)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v hv
      ring
    _ ≤ (2 * C * T * L * y) * (y / ((L / 4) ^ 2 - y ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral_exponential_sinh_le hy hyL (by norm_num))
        (by positivity)
    _ = 2 * C * T * L * y ^ 2 / (L ^ 2 / 16 - y ^ 2) := by
      rw [show (L / 4) ^ 2 = L ^ 2 / 16 by ring]
      ring

/-- The explicit `128 C/3` constant, still conditional on the supplied density. -/
theorem finite_cosh_density_eighth (s : Finset ι) (x : ι → ℝ)
    (C T L y : ℝ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hL : 0 < L) (hy : 0 ≤ y) (hyL : y ≤ L / 8)
    (hx : ∀ i ∈ s, x i ∈ Icc (0 : ℝ) (1 / 2))
    (hdensity : ∀ v ∈ Icc (0 : ℝ) (1 / 2),
      FiniteStrictTail.tail s x v ≤
        2 * C * T * L * Real.exp (-(L / 4) * v)) :
    (∑ i ∈ s, (Real.cosh (y * x i) - 1)) ≤
      (128 * C / 3) * T * y ^ 2 / L := by
  exact (finite_cosh_density_transfer s x C T L y hC hT hL hy
    (by linarith) hx hdensity).trans
      (density_rational_eighth hC hT hL hy hyL)

end RiemannResearch.Analysis.ZeroDensityTransfer
