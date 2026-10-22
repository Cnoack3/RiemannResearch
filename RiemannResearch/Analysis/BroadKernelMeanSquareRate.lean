import RiemannResearch.Analysis.BroadKernelUniformBounds

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Quantitative normalized mean-square limit

The exact mean and the proved O(1/R) energy error imply an O(1/R) error
for the actual normalized mean squared. Multiplication by R therefore
leaves a bounded error in the linear square-sector main term.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.Analysis

private theorem reciprocal_error_bound {A x y C R : ℝ}
    (hA : 0 ≤ A) (hy : 0 < y) (hx : y/2 ≤ x) (hC : 0 ≤ C)
    (hR : 0 < R) (he : |x-y| ≤ C/R) :
    |A/x-A/y| ≤ (2*A*C/y^2)/R := by
  have hx0 : 0 < x := lt_of_lt_of_le (half_pos hy) hx
  have hd : 0 < (y/2)*y := mul_pos (half_pos hy) hy
  have hden : (y/2)*y ≤ x*y := mul_le_mul_of_nonneg_right hx hy.le
  calc
    _ = A*|x-y|/(x*y) := by
      rw [show A/x-A/y = -(A*(x-y)/(x*y)) by field_simp [hx0.ne',hy.ne']; ring]
      rw [abs_neg,abs_div,abs_mul,abs_mul,abs_of_nonneg hA,
        abs_of_pos hx0,abs_of_pos hy]
    _ ≤ A*(C/R)/(x*y) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hA)
        (mul_nonneg hx0.le hy.le)
    _ ≤ A*(C/R)/((y/2)*y) :=
      div_le_div_of_nonneg_left (mul_nonneg hA (div_nonneg hC hR.le)) hd hden
    _ = _ := by field_simp [hy.ne',hR.ne']

/-- The normalized actual mean squared has the seed ratio as limit with a
bounded R-multiplied error. Every estimate is obtained from the kernel data. -/
theorem eventually_mean_sq_normalizedBroadKernelProfile_error
    (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j)) (hfc : ∀ j, Continuous (f j))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x y, |f 0 x-f 0 y| ≤ K*|x-y|)
    (hmoment : Integrable (fun v => |v| * |h v|))
    (hH : 0 < ∫v,h v) (hf0 : 0 < ∫x,f 0 x^2)
    (hz1 : (∫x,f 1 x)=0) (hz2 : (∫x,f 2 x)=0) (hz3 : (∫x,f 3 x)=0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ R : ℝ in atTop,
      R * |(∫x,normalizedBroadKernelProfile h f R x)^2 -
        (∫x,f 0 x)^2/(∫x,f 0 x^2)| ≤ C := by
  let m : ℝ := -(∫v,h v)/8
  let E0 : ℝ := m^2*(∫x,f 0 x^2)
  let A : ℝ := (m*(∫x,f 0 x))^2
  have hm : m ≠ 0 := div_ne_zero (neg_ne_zero.mpr hH.ne') (by norm_num)
  have hE0 : 0 < E0 := mul_pos (sq_pos_of_ne_zero hm) hf0
  have hA : 0 ≤ A := sq_nonneg _
  obtain ⟨C,hC0,hC⟩ := broadKernelEnergy_error_bound h f hh hfi hfc M hM K hK0 hK hmoment
  have ht := tendsto_broadKernelEnergy h f hh hfi hfc M hM K hK0 hK hmoment
  have hlower : ∀ᶠ R : ℝ in atTop, E0/2 ≤ broadKernelEnergy h f R := by
    have he := ht.eventually (Ioi_mem_nhds (show E0/2 < E0 by linarith))
    exact he.mono (fun R hR => le_of_lt hR)
  refine ⟨2*A*C/E0^2,by positivity,?_⟩
  filter_upwards [hlower,eventually_ge_atTop (1:ℝ)] with R hER hR
  have hR0 : 0 < R := by linarith
  have hnorm : broadKernelNorm h f R ^ 2 = broadKernelEnergy h f R :=
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))
  have hmean : (∫x,normalizedBroadKernelProfile h f R x)^2 =
      A/broadKernelEnergy h f R := by
    rw [integral_normalizedBroadKernelProfile h f hh hfi hfc hz1 hz2 hz3,
      div_pow,hnorm]
  have hratio : A/E0 = (∫x,f 0 x)^2/(∫x,f 0 x^2) := by
    unfold A E0
    field_simp [hm,hf0.ne']
  rw [hmean,←hratio]
  have hb := reciprocal_error_bound hA hE0 hER hC0 hR0 (hC R hR)
  exact (mul_le_mul_of_nonneg_left hb hR0.le).trans_eq (by field_simp)

end RiemannResearch.Analysis
