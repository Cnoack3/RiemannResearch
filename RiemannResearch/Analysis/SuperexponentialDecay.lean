import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Superexponential decay and actual cross-correlations

Source: the user-provided Nyman--Weil note, section 2. The estimates below
justify convergence only; they do not replace any signed arithmetic identity.
-/

open MeasureTheory Set Filter

namespace RiemannResearch.Analysis

/-- Every positive exponential weight is bounded. No differentiability is
included; smoothness is imposed independently when derivatives are needed. -/
def SuperexponentialDecay {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) : Prop :=
  ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 < C ∧
    ∀ y : ℝ, ‖f y‖ ≤ C * Real.exp (-a * |y|)

noncomputable section

theorem integrable_exp_neg_abs : Integrable (fun y : ℝ => Real.exp (-|y|)) := by
  have hp : IntegrableOn (fun y : ℝ => Real.exp (-|y|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simp [abs_of_pos (show 0 < y from hy)]
  have hn : IntegrableOn (fun y : ℝ => Real.exp (-|y|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    simp [abs_of_nonpos (show y ≤ 0 from hy)]
  have hu := hn.union hp
  have hs : Iic (0 : ℝ) ∪ Ioi 0 = univ := by
    ext y
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt y 0
  rw [hs] at hu
  exact integrableOn_univ.mp hu

/-- Every ordinary exponentially weighted L¹ norm is finite for a continuous
superexponentially decreasing function. The integrability is a conclusion. -/
theorem SuperexponentialDecay.integrable_weighted_norm {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hcont : Continuous f) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun y : ℝ => Real.exp (a * |y|) * ‖f y‖) := by
  obtain ⟨C, hC, hbound⟩ := hf (a + 1) (by linarith)
  apply (integrable_exp_neg_abs.const_mul C).mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      hcont.norm).aestronglyMeasurable
  · apply ae_of_all
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      Real.exp (a * |y|) * ‖f y‖ ≤
          Real.exp (a * |y|) * (C * Real.exp (-(a + 1) * |y|)) :=
        mul_le_mul_of_nonneg_left (hbound y) (Real.exp_nonneg _)
      _ = C * Real.exp (-|y|) := by
        rw [show Real.exp (a * |y|) * (C * Real.exp (-(a + 1) * |y|)) =
          C * (Real.exp (a * |y|) * Real.exp (-(a + 1) * |y|)) by ring,
          ← Real.exp_add]
        congr 2
        ring

/-- Actual correlation, with the first function translated to the left. -/
def crossCorrelation (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, f (y + t) * star (g y)

theorem norm_crossCorrelation_integrand_le {f g : ℝ → ℂ} {A a : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hf : ∀ y, ‖f y‖ ≤ A * Real.exp (-a * |y|)) (t y : ℝ) :
    ‖f (y + t) * star (g y)‖ ≤
      (A * Real.exp (-a * |t|)) * (Real.exp (a * |y|) * ‖g y‖) := by
  have htri : |t| ≤ |y + t| + |y| := by
    have h := abs_sub (y + t) y
    simpa only [add_sub_cancel_left] using h
  have he : Real.exp (-a * |y + t|) ≤
      Real.exp (-a * |t|) * Real.exp (a * |y|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [norm_mul, norm_star]
  calc
    ‖f (y + t)‖ * ‖g y‖ ≤ (A * Real.exp (-a * |y + t|)) * ‖g y‖ :=
      mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
    _ ≤ (A * (Real.exp (-a * |t|) * Real.exp (a * |y|))) * ‖g y‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hA) (norm_nonneg _)
    _ = _ := by ring

/-- Correlation integrability and decay follow from the actual weighted norm,
not an abstract operator norm or a postulated Weil form. -/
theorem crossCorrelation_integrable_and_bound {f g : ℝ → ℂ} {A a : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hfc : Continuous f) (hgc : Continuous g)
    (hf : ∀ y, ‖f y‖ ≤ A * Real.exp (-a * |y|))
    (hg : Integrable (fun y : ℝ => Real.exp (a * |y|) * ‖g y‖)) (t : ℝ) :
    Integrable (fun y : ℝ => f (y + t) * star (g y)) ∧
      ‖crossCorrelation f g t‖ ≤
        (A * (∫ y : ℝ, Real.exp (a * |y|) * ‖g y‖)) * Real.exp (-a * |t|) := by
  have hmajor := hg.const_mul (A * Real.exp (-a * |t|))
  have hbound := norm_crossCorrelation_integrand_le (g := g) hA ha hf t
  constructor
  · apply hmajor.mono'
    · have hc : Continuous (fun y : ℝ => f (y + t) * star (g y)) := by fun_prop
      exact hc.aestronglyMeasurable
    · exact ae_of_all _ hbound
  · unfold crossCorrelation
    calc
      ‖∫ y : ℝ, f (y + t) * star (g y)‖ ≤
          ∫ y : ℝ, (A * Real.exp (-a * |t|)) *
            (Real.exp (a * |y|) * ‖g y‖) :=
        norm_integral_le_of_norm_le hmajor (ae_of_all _ hbound)
      _ = _ := by rw [integral_const_mul]; ring

/-- Cross-correlations of continuous superexponentially decreasing functions
again decrease faster than every exponential. -/
theorem SuperexponentialDecay.crossCorrelation {f g : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hg : SuperexponentialDecay g)
    (hfc : Continuous f) (hgc : Continuous g) :
    SuperexponentialDecay (crossCorrelation f g) := by
  intro a ha
  obtain ⟨A, hA, hbound⟩ := hf a ha
  let J : ℝ := ∫ y : ℝ, Real.exp (a * |y|) * ‖g y‖
  have hJ : 0 ≤ J := integral_nonneg (fun y => by positivity)
  refine ⟨A * J + 1, by positivity, ?_⟩
  intro t
  have h := (crossCorrelation_integrable_and_bound hA.le ha.le hfc hgc hbound
    (hg.integrable_weighted_norm hgc ha.le) t).2
  exact h.trans (by
    change (A * J) * Real.exp (-a * |t|) ≤
      (A * J + 1) * Real.exp (-a * |t|)
    nlinarith [Real.exp_pos (-a * |t|)])

end
end RiemannResearch.Analysis
