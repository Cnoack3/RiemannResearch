import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.NormNum

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

end RiemannResearch.Analysis
