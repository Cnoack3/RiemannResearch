import RiemannResearch.RH.ParetoMellinGramOptimization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact changes of finite Mellin target signatures

Source: the user's fourth Ramanujan transfer program, October 2026.
Every cross term, the complete correction capacity, and the complete Mellin
remainder are retained before any approximate-data estimate is taken.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinSourceCross (s b e : ι → ℂ) : ℝ :=
  (∑ i, starRingEnd ℂ (mellinInverseCoefficients s b i) * e i).re

theorem mellinInverseCoefficients_sub_source (s b e : ι → ℂ) :
    mellinInverseCoefficients s (b - e) =
      mellinInverseCoefficients s b - mellinInverseCoefficients s e := by
  unfold mellinInverseCoefficients
  exact Matrix.mulVec_sub _ _ _

theorem mellinCharge_sub_source (s b e c : ι → ℂ) :
    mellinCharge s (b - e) c = mellinCharge s b c -
      2 * (∑ i, starRingEnd ℂ (c i) * e i).re := by
  simp only [mellinCharge, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    Complex.sub_re]
  ring

/-- Exact polarization of the inverse capacity under a source correction. -/
theorem mellinInverseCapacity_sub_source (s b e : ι → ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinInverseCapacity s (b - e) =
      mellinInverseCapacity s b - 2 * mellinSourceCross s b e +
        mellinInverseCapacity s e := by
  have h := mellinCharge_completion s (b - e) (mellinInverseCoefficients s b)
    (mellinInverseCoefficients s (b - e))
    (mellinInverseCoefficients_normal s (b - e) hdet)
  have hd : mellinInverseCoefficients s b - mellinInverseCoefficients s (b - e) =
      mellinInverseCoefficients s e := by
    rw [mellinInverseCoefficients_sub_source]
    funext i
    simp only [Pi.sub_apply]
    ring
  have he := congrArg Complex.re (mellinGramQuadratic_eq_of_normal s
    (mellinInverseCoefficients s e) e (mellinInverseCoefficients_normal s e hdet))
  change (mellinGramQuadratic s (mellinInverseCoefficients s e)).re =
    mellinInverseCapacity s e at he
  rw [mellinCharge_inverse s (b - e) hdet, mellinCharge_sub_source,
    mellinCharge_inverse s b hdet, hd, he] at h
  simpa only [mellinSourceCross] using h

theorem mellinSourceCross_le_norm_sum (s b e : ι → ℂ) :
    mellinSourceCross s b e ≤
      ∑ i, ‖mellinInverseCoefficients s b i‖ * ‖e i‖ := by
  calc
    _ ≤ ‖∑ i, starRingEnd ℂ (mellinInverseCoefficients s b i) * e i‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ i, ‖starRingEnd ℂ (mellinInverseCoefficients s b i) * e i‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

theorem mellinSourceCross_le_budget (s b e : ι → ℂ) (ε : ι → ℝ)
    (hε : ∀ i, ‖e i‖ ≤ ε i) :
    mellinSourceCross s b e ≤ ∑ i, ‖mellinInverseCoefficients s b i‖ * ε i := by
  apply (mellinSourceCross_le_norm_sum s b e).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (hε i) (norm_nonneg _)

/-- The exact finite source correction and the complete analytic remainder. -/
theorem finiteMellinKernel_perturbed_inverse_completion
    (f : ThresholdHilbert) (s b e : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0)
    (hsig : ∀ i, paretoMellin f (s i) = b i - e i) :
    ‖f‖ ^ 2 = mellinInverseCapacity s b - 2 * mellinSourceCross s b e +
      mellinInverseCapacity s e +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep f x - starRingEnd ℂ
          (finiteMellinKernel s (mellinInverseCoefficients s (b - e)) x)‖ ^ 2 := by
  have h := finiteMellinKernel_inverse_completion f s hs hdet
  have he : (fun i => paretoMellin f (s i)) = b - e := funext hsig
  rw [he, mellinInverseCapacity_sub_source s b e hdet] at h
  exact h

/-- A norm budget is only a corollary of the full signed identity. -/
theorem finiteMellinKernel_perturbed_budget_lower
    (f : ThresholdHilbert) (s b e : ι → ℂ) (ε : ι → ℝ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0)
    (hsig : ∀ i, paretoMellin f (s i) = b i - e i)
    (hε : ∀ i, ‖e i‖ ≤ ε i) :
    mellinInverseCapacity s b -
      2 * (∑ i, ‖mellinInverseCoefficients s b i‖ * ε i) ≤ ‖f‖ ^ 2 := by
  have h := finiteMellinKernel_perturbed_inverse_completion f s b e hs hdet hsig
  have hc := mellinSourceCross_le_budget s b e ε hε
  have he := mellinInverseCapacity_nonneg s e hs hdet
  have hr : 0 ≤ ∫ x in Ioi (1 : ℝ),
      ‖mellinWeightedStep f x - starRingEnd ℂ
        (finiteMellinKernel s (mellinInverseCoefficients s (b - e)) x)‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

end RiemannResearch.RH.Pareto
