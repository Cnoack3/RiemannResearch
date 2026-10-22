import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The actual square-integral L2 norm and finite-translate bounds -/

open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Analysis

/-- The ordinary Lebesgue L2 norm, written directly as a square integral. -/
noncomputable def actualL2Norm (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (∫ y : ℝ, ‖f y‖ ^ 2)

theorem actualL2Norm_nonneg (f : ℝ → ℂ) : 0 ≤ actualL2Norm f := Real.sqrt_nonneg _

private theorem eLpNorm_two_eq_actualL2Norm {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) : eLpNorm f 2 volume = ENNReal.ofReal (actualL2Norm f) := by
  have h := MemLp.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤) hf
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    actualL2Norm] using h

theorem actualL2Norm_add_le {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    actualL2Norm (f + g) ≤ actualL2Norm f + actualL2Norm g := by
  have h := eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable
    (by norm_num : (1 : ENNReal) ≤ 2)
  rw [eLpNorm_two_eq_actualL2Norm (hf.add hg), eLpNorm_two_eq_actualL2Norm hf,
    eLpNorm_two_eq_actualL2Norm hg,
    ← ENNReal.ofReal_add (actualL2Norm_nonneg f) (actualL2Norm_nonneg g)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (actualL2Norm_nonneg f)
    (actualL2Norm_nonneg g))).mp h

theorem actualL2Norm_neg (f : ℝ → ℂ) : actualL2Norm (-f) = actualL2Norm f := by
  simp only [actualL2Norm, Pi.neg_apply, norm_neg]

theorem actualL2Norm_sub_le {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    actualL2Norm (f - g) ≤ actualL2Norm f + actualL2Norm g := by
  simpa only [sub_eq_add_neg, actualL2Norm_neg] using actualL2Norm_add_le hf hg.neg

theorem actualL2Norm_const_smul (c : ℝ) (f : ℝ → ℂ) :
    actualL2Norm (c • f) = |c| * actualL2Norm f := by
  unfold actualL2Norm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg |c|), Real.sqrt_sq_eq_abs, abs_abs]

theorem actualL2Norm_translate (f : ℝ → ℂ) (t : ℝ) :
    actualL2Norm (fun y => f (y - t)) = actualL2Norm f := by
  unfold actualL2Norm
  congr 1
  exact integral_sub_right_eq_self (fun y : ℝ => ‖f y‖ ^ 2) t

theorem memLp_two_translate {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hc : Continuous f) (t : ℝ) : MemLp (fun y => f (y - t)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (hc.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).mpr
  exact hf.norm.integrable_sq.comp_sub_right t

theorem actualL2Norm_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ k ∈ S, MemLp (f k) 2 volume) :
    actualL2Norm (∑ k ∈ S, f k) ≤ ∑ k ∈ S, actualL2Norm (f k) := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty => intro hf; simp [actualL2Norm]
  | @insert k S hk ih =>
    intro hf
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have hfS : ∀ i ∈ S, MemLp (f i) 2 volume :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (actualL2Norm_add_le (hf k (Finset.mem_insert_self k S))
      (memLp_finset_sum' S hfS)).trans (add_le_add le_rfl (ih hfS))

/-- Ordinary L2 triangle inequality for the actual finite translated sum. -/
theorem actualL2Norm_sum_smul_translate_le {ι : Type*} (S : Finset ι)
    (c t : ι → ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 volume) (hc : Continuous f) :
    actualL2Norm (∑ k ∈ S, c k • (fun y => f (y - t k))) ≤
      (∑ k ∈ S, |c k|) * actualL2Norm f := by
  have h := actualL2Norm_sum_le S (fun k => c k • (fun y => f (y - t k)))
    (fun k _ => (memLp_two_translate hf hc (t k)).const_smul (c k))
  simpa only [actualL2Norm_const_smul, actualL2Norm_translate, Finset.sum_mul] using h

/-- Exact agreement of squared norm with the ordinary energy integral. -/
theorem actualL2Norm_sq (f : ℝ → ℂ) :
    actualL2Norm f ^ 2 = ∫ y : ℝ, ‖f y‖ ^ 2 := by
  unfold actualL2Norm
  exact Real.sq_sqrt (integral_nonneg (fun y => sq_nonneg ‖f y‖))

/-- Exact translation-difference energy, retaining the complete square
remainder. Source: direct expansion for the user's exact energy-accounting
program; no domain-specific hypotheses are introduced. -/
theorem actualL2Norm_sub_smul_translate_sq_exact (a b t : ℝ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (hc : Continuous f) :
    actualL2Norm (a • f - b • (fun y => f (y - t))) ^ 2 =
      (a - b) ^ 2 * actualL2Norm f ^ 2 +
        a * b * actualL2Norm (f - (fun y => f (y - t))) ^ 2 := by
  let g : ℝ → ℂ := fun y => f (y - t)
  have hg : MemLp g 2 volume := memLp_two_translate hf hc t
  have hif : Integrable (fun y => ‖f y‖ ^ 2) := hf.norm.integrable_sq
  have hig : Integrable (fun y => ‖g y‖ ^ 2) := hg.norm.integrable_sq
  have hid : Integrable (fun y => ‖f y - g y‖ ^ 2) :=
    (hf.sub hg).norm.integrable_sq
  have h₁ := hif.const_mul ((a - b) ^ 2)
  have h₂ := hid.const_mul (a * b)
  have h₃ : Integrable (fun y => b * (b - a) * (‖g y‖ ^ 2 - ‖f y‖ ^ 2)) :=
    (hig.sub hif).const_mul (b * (b - a))
  have h₁₂ : Integrable (fun y =>
      (a - b) ^ 2 * ‖f y‖ ^ 2 + a * b * ‖f y - g y‖ ^ 2) := h₁.add h₂
  have hpoint (z w : ℂ) :
      ‖a • z - b • w‖ ^ 2 =
        (a - b) ^ 2 * ‖z‖ ^ 2 + a * b * ‖z - w‖ ^ 2 +
          b * (b - a) * (‖w‖ ^ 2 - ‖z‖ ^ 2) := by
    simp only [Complex.real_smul, Complex.sq_norm, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hgintegral : (∫ y : ℝ, ‖g y‖ ^ 2) = ∫ y : ℝ, ‖f y‖ ^ 2 :=
    integral_sub_right_eq_self (fun y : ℝ => ‖f y‖ ^ 2) t
  simp only [actualL2Norm_sq, Pi.sub_apply, Pi.smul_apply]
  change (∫ y : ℝ, ‖a • f y - b • g y‖ ^ 2) =
    (a - b) ^ 2 * (∫ y : ℝ, ‖f y‖ ^ 2) +
      a * b * (∫ y : ℝ, ‖f y - g y‖ ^ 2)
  calc
    _ = ∫ y : ℝ, ((a - b) ^ 2 * ‖f y‖ ^ 2 +
        a * b * ‖f y - g y‖ ^ 2 +
        b * (b - a) * (‖g y‖ ^ 2 - ‖f y‖ ^ 2)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y => hpoint (f y) (g y)))
    _ = (a - b) ^ 2 * (∫ y : ℝ, ‖f y‖ ^ 2) +
        a * b * (∫ y : ℝ, ‖f y - g y‖ ^ 2) +
        b * (b - a) * ((∫ y : ℝ, ‖g y‖ ^ 2) - ∫ y : ℝ, ‖f y‖ ^ 2) := by
      rw [integral_add h₁₂ h₃, integral_add h₁ h₂,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_sub hig hif]
    _ = _ := by rw [hgintegral]; ring

/-- Reverse triangle bound with the translation norm evaluated exactly. -/
theorem actualL2Norm_sub_smul_translate_lower_bound (a b t : ℝ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (hc : Continuous f) :
    (|b| - |a|) * actualL2Norm f ≤
      actualL2Norm (a • f - b • (fun y => f (y - t))) := by
  have hT := (memLp_two_translate hf hc t).const_smul b
  have hA := hf.const_smul a
  have h := actualL2Norm_sub_le hA (hA.sub hT)
  have heq : a • f - (a • f - b • (fun y => f (y - t))) =
      b • (fun y => f (y - t)) := sub_sub_cancel _ _
  rw [heq, actualL2Norm_const_smul, actualL2Norm_translate,
    actualL2Norm_const_smul] at h
  nlinarith

end RiemannResearch.Analysis
