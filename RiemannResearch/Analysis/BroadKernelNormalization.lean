import RiemannResearch.Analysis.BroadKernelProfile
import Mathlib.Analysis.SpecialFunctions.Sqrt

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual broad-profile squared norm and normalization limits

All limits are derived from the explicit O(1/R) sup approximation and the
actual uniform L¹ estimate. No normalization asymptotic is an assumption.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.Analysis

noncomputable def broadKernelEnergy (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ x, broadKernelProfile h f R x ^ 2

noncomputable def broadKernelNorm (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ) (R : ℝ) : ℝ :=
  Real.sqrt (broadKernelEnergy h f R)

noncomputable def normalizedBroadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (R x : ℝ) : ℝ := broadKernelProfile h f R x / broadKernelNorm h f R

/-- A concrete squared-norm error estimate for the actual broad family. -/
theorem broadKernelEnergy_error_bound (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j)) (hfc : ∀ j, Continuous (f j))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x y, |f 0 x-f 0 y| ≤ K*|x-y|)
    (hmoment : Integrable (fun v => |v| * |h v|)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      |broadKernelEnergy h f R - (-(∫ v,h v)/8)^2*(∫ x,f 0 x^2)| ≤ C/R := by
  let H : ℝ := ∫ v, |h v|
  let J : ℝ := ∫ v, |v| * |h v|
  let m : ℝ := -(∫ v,h v)/8
  let L : ℝ := H*((∫x,|f 3 x|)+(∫x,|f 2 x|)+(∫x,|f 1 x|)+(∫x,|f 0 x|))
  let E : ℝ := H*(M 3+M 2+M 1)+K*J
  have hH0 : 0 ≤ H := integral_nonneg (fun v => abs_nonneg _)
  have hJ0 : 0 ≤ J := integral_nonneg (fun v => by positivity)
  have hMj (j : ℕ) : 0 ≤ M j := (abs_nonneg (f j 0)).trans (hM j 0)
  have hM0 := hMj 0
  have hM1 := hMj 1
  have hM2 := hMj 2
  have hM3 := hMj 3
  have hL0 : 0 ≤ L := by unfold L; positivity
  have hE0 : 0 ≤ E := by unfold E; positivity
  let C := E*(L+|m| * (∫x,|f 0 x|))
  refine ⟨C, by unfold C; positivity, ?_⟩
  intro R hR
  have hR0 : 0 < R := by linarith
  have hB := integrable_broadKernelProfile h f hh hfi hfc R
  have hG := (hfi 0).const_mul m
  have hBg := abs_broadKernelProfile_le h f hh M hM hR
  have hGg (x : ℝ) : |m*f 0 x| ≤ |m| * M 0 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM 0 x) (abs_nonneg _)
  have hdiff (x : ℝ) : |broadKernelProfile h f R x-m*f 0 x| ≤ E/R :=
    abs_broadKernelProfile_sub_limit_le h f hh (hfc 0) M hM K hK0 hK hmoment hR x
  have hb := abs_integral_sq_sub_le (broadKernelProfile h f R) (fun x => m*f 0 x)
    hB hG (H*(M 3+M 2+M 1+M 0)) (|m| * M 0) (E/R) hBg hGg hdiff
  have hg2 : (∫ x,(m*f 0 x)^2) = m^2*(∫x,f 0 x^2) := by
    calc
      _ = ∫ x,m^2*f 0 x^2 := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by ring)
      _ = _ := integral_const_mul _ _
  have hg1 : (∫ x,|m*f 0 x|) = |m| * (∫x,|f 0 x|) := by
    simp_rw [abs_mul]
    exact integral_const_mul _ _
  rw [hg2,hg1] at hb
  have hL := integral_abs_broadKernelProfile_le h f hh hfi hfc hR
  have hscale := mul_le_mul_of_nonneg_left
    (add_le_add hL (le_refl (|m| * (∫x,|f 0 x|)))) (div_nonneg hE0 hR0.le)
  change |broadKernelEnergy h f R-m^2*(∫x,f 0 x^2)| ≤ C/R
  exact hb.trans (hscale.trans_eq (by unfold C; ring))

/-- The actual squared norm converges to the nonzero-multiplier profile norm. -/
theorem tendsto_broadKernelEnergy (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j)) (hfc : ∀ j, Continuous (f j))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x y, |f 0 x-f 0 y| ≤ K*|x-y|)
    (hmoment : Integrable (fun v => |v| * |h v|)) :
    Tendsto (broadKernelEnergy h f) atTop
      (𝓝 ((-(∫ v,h v)/8)^2*(∫x,f 0 x^2))) := by
  obtain ⟨C,hC0,hC⟩ := broadKernelEnergy_error_bound h f hh hfi hfc M hM K hK0 hK hmoment
  have hlim : Tendsto (fun R : ℝ => C/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul C
  have he : Tendsto (fun R => broadKernelEnergy h f R-
      (-(∫v,h v)/8)^2*(∫x,f 0 x^2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    simpa only [Real.norm_eq_abs] using hC R hR
  have ht := he.add_const ((-(∫v,h v)/8)^2*(∫x,f 0 x^2))
  simpa only [sub_add_cancel,zero_add] using ht

/-- Normalization convergence follows from the proved energy limit. -/
theorem tendsto_broadKernelNorm (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j)) (hfc : ∀ j, Continuous (f j))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x y, |f 0 x-f 0 y| ≤ K*|x-y|)
    (hmoment : Integrable (fun v => |v| * |h v|)) :
    Tendsto (broadKernelNorm h f) atTop
      (𝓝 (Real.sqrt ((-(∫v,h v)/8)^2*(∫x,f 0 x^2)))) :=
  Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_broadKernelEnergy h f hh hfi hfc M hM K hK0 hK hmoment)

/-- The actual normalized mean, with no limiting replacement of the return. -/
theorem integral_normalizedBroadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j)) (hfc : ∀ j, Continuous (f j))
    (hz1 : (∫x,f 1 x)=0) (hz2 : (∫x,f 2 x)=0) (hz3 : (∫x,f 3 x)=0) (R : ℝ) :
    (∫x,normalizedBroadKernelProfile h f R x) =
      ((-(∫v,h v)/8)*(∫x,f 0 x))/broadKernelNorm h f R := by
  unfold normalizedBroadKernelProfile
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,integral_broadKernelProfile h f hh hfi hfc hz1 hz2 hz3]
  ring

/-- Positivity of the actual kernel mass and of the original bump's L² mass
makes normalization bounded away from zero eventually. -/
theorem eventually_broadKernelNorm_lower_bound (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j)) (hfc : ∀ j, Continuous (f j))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x y, |f 0 x-f 0 y| ≤ K*|x-y|)
    (hmoment : Integrable (fun v => |v| * |h v|))
    (hH : 0 < ∫v,h v) (hf0 : 0 < ∫x,f 0 x^2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ R : ℝ in atTop, δ ≤ broadKernelNorm h f R := by
  let N := Real.sqrt ((-(∫v,h v)/8)^2*(∫x,f 0 x^2))
  have hN0 : 0 < N := Real.sqrt_pos.mpr (mul_pos
    (sq_pos_of_ne_zero (div_ne_zero (neg_ne_zero.mpr hH.ne') (by norm_num))) hf0)
  refine ⟨N/2,by positivity,?_⟩
  have ht := tendsto_broadKernelNorm h f hh hfi hfc M hM K hK0 hK hmoment
  have he := ht.eventually (Ioi_mem_nhds (show N/2 < N by linarith))
  exact he.mono (fun R hR => le_of_lt hR)

end RiemannResearch.Analysis
