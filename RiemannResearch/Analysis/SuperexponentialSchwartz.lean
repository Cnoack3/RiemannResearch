import RiemannResearch.Analysis.ScaledKernelWeightedApproximation
import RiemannResearch.Analysis.SuperexponentialDecay
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-! # Actual Schwartz maps from smooth superexponential functions -/

open MeasureTheory Set Filter
open scoped Topology SchwartzMap
namespace RiemannResearch.Analysis

theorem SuperexponentialDecay.exists_polynomialWeight_bound
    {F : Type*} [NormedAddCommGroup F] {f : ℝ → F}
    (hf : SuperexponentialDecay f) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, polynomialWeight k x * ‖f x‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := hf ((k:ℝ)+1) (by positivity)
  refine ⟨C,hC,fun x => ?_⟩
  have hw : polynomialWeight k x ≤ Real.exp ((k:ℝ)* |x|) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    simpa only [add_comm] using Real.add_one_le_exp |x|
  calc
    _ ≤ Real.exp ((k:ℝ)* |x|) * (C*Real.exp (-((k:ℝ)+1)* |x|)) :=
      mul_le_mul hw (hbound x) (norm_nonneg _) (Real.exp_nonneg _)
    _ = C*Real.exp (- |x|) := by
      rw [show Real.exp ((k:ℝ)* |x|)*(C*Real.exp (-((k:ℝ)+1)* |x|)) =
        C*(Real.exp ((k:ℝ)* |x|)*Real.exp (-((k:ℝ)+1)* |x|)) by ring,
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ C := mul_le_of_le_one_right hC.le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _)))

noncomputable def schwartzMapOfSmoothSuperexponential
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hd : ∀ j, SuperexponentialDecay (iteratedDeriv j f)) : SchwartzMap ℝ F where
  toFun := f
  smooth' := hf
  decay' k j := by
    obtain ⟨C,_,hC⟩ := (hd j).exists_polynomialWeight_bound k
    refine ⟨C,fun x => ?_⟩
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg x) (by linarith : |x| ≤ 1+ |x|) k)
      (norm_nonneg _)).trans (hC x)

@[simp] theorem schwartzMapOfSmoothSuperexponential_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hd : ∀ j, SuperexponentialDecay (iteratedDeriv j f)) (x : ℝ) :
    schwartzMapOfSmoothSuperexponential f hf hd x = f x := rfl

theorem tendsto_schwartzMap_of_weighted_iteratedDeriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → SchwartzMap ℝ F) (g : SchwartzMap ℝ F)
    (h : ∀ k j : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop, ∀ x : ℝ,
      polynomialWeight k x * ‖iteratedDeriv j (f R) x-iteratedDeriv j g x‖ < ε) :
    Tendsto f atTop (𝓝 g) := by
  apply ((schwartz_withSeminorms ℝ ℝ F).tendsto_nhds f g).2
  intro ij ε hε
  obtain ⟨k,j⟩ := ij
  filter_upwards [h k j (ε/2) (by linarith)] with R hR
  have hbound : SchwartzMap.seminorm ℝ k j (f R-g) ≤ ε/2 := by
    apply SchwartzMap.seminorm_le_bound' ℝ k j (f R-g) (by linarith)
    intro x
    change |x| ^k * ‖iteratedDeriv j ((f R : ℝ → F) - (g : ℝ → F)) x‖ ≤ ε/2
    rw [iteratedDeriv_sub ((f R).contDiffAt j) (g.contDiffAt j)]
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg x) (by linarith : |x| ≤ 1+ |x|) k)
      (norm_nonneg _)).trans (hR x).le
  exact hbound.trans_lt (by linarith)

end RiemannResearch.Analysis
