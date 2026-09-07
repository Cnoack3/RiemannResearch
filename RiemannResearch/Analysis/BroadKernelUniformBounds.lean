import RiemannResearch.Analysis.BroadKernelNormalization

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Uniform normalized broad-profile bounds

A single positive normalization lower bound, proved from the actual energy
limit, controls every shifted derivative array. These estimates become the
actual derivative bounds when the differentiated kernel identity is used.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.Analysis

noncomputable def normalizedBroadKernelDerivative (h : ℝ → ℝ)
    (f : ℕ → ℝ → ℝ) (j : ℕ) (R x : ℝ) : ℝ :=
  broadKernelProfile h (fun k => f (k+j)) R x / broadKernelNorm h f R

/-- One positive normalization bound supplies uniform L¹ and sup bounds for
every actual shifted differential profile, with constants depending on j. -/
theorem eventually_normalizedBroadKernel_bounds (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j)) (hfc : ∀ j, Continuous (f j))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x y, |f 0 x-f 0 y| ≤ K*|x-y|)
    (hmoment : Integrable (fun v => |v| * |h v|))
    (hH : 0 < ∫v,h v) (hf0 : 0 < ∫x,f 0 x^2) :
    ∀ j : ℕ, ∃ L S : ℝ, 0 ≤ L ∧ 0 ≤ S ∧ ∀ᶠ R : ℝ in atTop,
      Integrable (normalizedBroadKernelDerivative h f j R) ∧
      (∫x,|normalizedBroadKernelDerivative h f j R x|) ≤ L ∧
      ∀ x, |normalizedBroadKernelDerivative h f j R x| ≤ S := by
  obtain ⟨δ,hδ,hN⟩ := eventually_broadKernelNorm_lower_bound h f hh hfi hfc M hM K
    hK0 hK hmoment hH hf0
  intro j
  let f' : ℕ → ℝ → ℝ := fun k => f (k+j)
  let A : ℝ := (∫v,|h v|)*
    ((∫x,|f (3+j) x|)+(∫x,|f (2+j) x|)+(∫x,|f (1+j) x|)+(∫x,|f j x|))
  let B : ℝ := (∫v,|h v|)*(M (3+j)+M (2+j)+M (1+j)+M j)
  have hMj (i : ℕ) : 0 ≤ M i := (abs_nonneg (f i 0)).trans (hM i 0)
  have hM0 := hMj j
  have hM1 := hMj (1+j)
  have hM2 := hMj (2+j)
  have hM3 := hMj (3+j)
  have hA0 : 0 ≤ A := by unfold A; positivity
  have hB0 : 0 ≤ B := by unfold B; positivity
  refine ⟨A/δ,B/δ,div_nonneg hA0 hδ.le,div_nonneg hB0 hδ.le,?_⟩
  filter_upwards [hN,eventually_ge_atTop (1:ℝ)] with R hNR hR
  have hNR0 : 0 < broadKernelNorm h f R := lt_of_lt_of_le hδ hNR
  have hi := integrable_broadKernelProfile h f' hh (fun k => hfi (k+j))
    (fun k => hfc (k+j)) R
  refine ⟨hi.div_const _,?_,?_⟩
  · have he : (∫x,|normalizedBroadKernelDerivative h f j R x|) =
        (∫x,|broadKernelProfile h f' R x|)/broadKernelNorm h f R := by
      unfold normalizedBroadKernelDerivative
      simp_rw [abs_div,abs_of_pos hNR0]
      simp_rw [div_eq_mul_inv]
      exact integral_mul_const _ _
    rw [he]
    have hbound := integral_abs_broadKernelProfile_le h f' hh (fun k => hfi (k+j))
      (fun k => hfc (k+j)) hR
    have hbound' : (∫x,|broadKernelProfile h f' R x|) ≤ A := by
      simpa only [A,f',Nat.zero_add] using hbound
    exact (div_le_div_of_nonneg_right hbound' hNR0.le).trans
      (div_le_div_of_nonneg_left hA0 hδ hNR)
  · intro x
    change |broadKernelProfile h f' R x/broadKernelNorm h f R| ≤ B/δ
    rw [abs_div,abs_of_pos hNR0]
    have hbound := abs_broadKernelProfile_le h f' hh (fun k => M (k+j))
      (fun k => hM (k+j)) hR x
    have hbound' : |broadKernelProfile h f' R x| ≤ B := by
      simpa only [B,Nat.zero_add] using hbound
    exact (div_le_div_of_nonneg_right hbound' hNR0.le).trans
      (div_le_div_of_nonneg_left hB0 hδ hNR)

/-- The normalized profile has exactly unit squared norm whenever its actual
normalization is positive. -/
theorem integral_sq_normalizedBroadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (R : ℝ) (hN : 0 < broadKernelNorm h f R) :
    (∫x,normalizedBroadKernelProfile h f R x^2) = 1 := by
  have hE0 : 0 ≤ broadKernelEnergy h f R := integral_nonneg (fun x => sq_nonneg _)
  have hN2 : broadKernelNorm h f R ^ 2 = broadKernelEnergy h f R := Real.sq_sqrt hE0
  calc
    _ = (∫x,broadKernelProfile h f R x^2)/broadKernelNorm h f R^2 := by
      unfold normalizedBroadKernelProfile
      simp_rw [div_pow]
      simp_rw [div_eq_mul_inv]
      exact integral_mul_const _ _
    _ = broadKernelNorm h f R^2/broadKernelNorm h f R^2 := by
      rw [show (∫x,broadKernelProfile h f R x^2)=broadKernelEnergy h f R from rfl,←hN2]
    _ = 1 := div_self (pow_ne_zero 2 hN.ne')

/-- The actual normalized mean tends to its explicitly computed limit. -/
theorem tendsto_mean_normalizedBroadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j)) (hfc : ∀ j, Continuous (f j))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x y, |f 0 x-f 0 y| ≤ K*|x-y|)
    (hmoment : Integrable (fun v => |v| * |h v|))
    (hH : 0 < ∫v,h v) (hf0 : 0 < ∫x,f 0 x^2)
    (hz1 : (∫x,f 1 x)=0) (hz2 : (∫x,f 2 x)=0) (hz3 : (∫x,f 3 x)=0) :
    Tendsto (fun R : ℝ => ∫x,normalizedBroadKernelProfile h f R x) atTop
      (𝓝 (((-(∫v,h v)/8)*(∫x,f 0 x)) /
        Real.sqrt ((-(∫v,h v)/8)^2*(∫x,f 0 x^2)))) := by
  have hN0 : 0 < Real.sqrt ((-(∫v,h v)/8)^2*(∫x,f 0 x^2)) := Real.sqrt_pos.mpr
    (mul_pos (sq_pos_of_ne_zero (div_ne_zero (neg_ne_zero.mpr hH.ne') (by norm_num))) hf0)
  have hconst : Tendsto (fun _ : ℝ => (-(∫v,h v)/8)*(∫x,f 0 x)) atTop
      (𝓝 ((-(∫v,h v)/8)*(∫x,f 0 x))) := tendsto_const_nhds
  have ht := hconst.div
    (tendsto_broadKernelNorm h f hh hfi hfc M hM K hK0 hK hmoment) hN0.ne'
  simp_rw [integral_normalizedBroadKernelProfile h f hh hfi hfc hz1 hz2 hz3]
  convert ht using 1 <;> rfl

end RiemannResearch.Analysis
