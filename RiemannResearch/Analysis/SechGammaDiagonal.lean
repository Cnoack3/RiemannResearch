import RiemannResearch.Analysis.SechGammaBounds
import RiemannResearch.Analysis.EvenIntegralHalfLine
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-!
# The regulated diagonal of the sech gamma kernel

Exact half-csch regularization and a quantitative remainder estimate for
Sections 6.1–6.4 of `MontgomeryGammaAudit20261110.md`.
The rescaled integral is evaluated with its endpoint constant, and the normalized
mean-zero remainder is bounded by `11 M₁ / (48 T² log T)`.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.SechGammaDiagonal
def remainder (t : ℝ) : ℝ :=
  SechGammaBounds.kernel t - 1 / (2*t)

theorem cosh_le_two {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.cosh t ≤ 2 := by
  have hc : Real.cosh t ≤ Real.cosh 1 := Real.cosh_le_cosh.mpr (by
    simpa [abs_of_nonneg ht] using ht1)
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h1 := Real.exp_one_lt_three
  have h2 : Real.cosh 1 ≤ 2 := by
    rw [Real.cosh_eq]
    linarith
  exact hc.trans h2

theorem sinh_le_two_mul {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sinh t ≤ 2*t := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => 2*y-Real.sinh y) (2-Real.cosh x) x := by
    convert! ((hasDerivAt_id x).const_mul 2).sub (Real.hasDerivAt_sinh x) using 1 <;> ring
  have hm : MonotoneOn (fun x : ℝ => 2*x-Real.sinh x) (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (by fun_prop)
    · intro x hx; exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x).deriv]
      exact sub_nonneg.mpr (cosh_le_two (interior_subset hx).1 (interior_subset hx).2)
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) ⟨ht, ht1⟩ ht
  simpa using h

theorem cosh_le_one_add_sq {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.cosh t ≤ 1+t^2 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => 1+y^2-Real.cosh y)
      (2*x-Real.sinh x) x := by
    convert! ((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)).sub
      (Real.hasDerivAt_cosh x) using 1 <;> (try simp only [id_eq]) <;> ring
  have hm : MonotoneOn (fun x : ℝ => 1+x^2-Real.cosh x) (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (by fun_prop)
    · intro x hx; exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x).deriv]
      exact sub_nonneg.mpr (sinh_le_two_mul (interior_subset hx).1 (interior_subset hx).2)
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) ⟨ht, ht1⟩ ht
  norm_num at h
  linarith

theorem sinh_sub_self_le_cube {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sinh t-t ≤ t^3/3 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y+y^3/3-Real.sinh y)
      (1+x^2-Real.cosh x) x := by
    convert! ((hasDerivAt_id x).add (((hasDerivAt_id x).pow 3).div_const 3)).sub
      (Real.hasDerivAt_sinh x) using 1 <;> (try simp only [id_eq]) <;> ring
  have hm : MonotoneOn (fun x : ℝ => x+x^3/3-Real.sinh x) (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (by fun_prop)
    · intro x hx; exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x).deriv]
      exact sub_nonneg.mpr (cosh_le_one_add_sq (interior_subset hx).1 (interior_subset hx).2)
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) ⟨ht, ht1⟩ ht
  norm_num at h
  linarith

theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh t ≤ t*Real.cosh t := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y*Real.cosh y-Real.sinh y)
      (x*Real.sinh x) x := by
    convert! ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1 <;> (try simp only [id_eq]) <;> ring
  have hm : MonotoneOn (fun x : ℝ => x*Real.cosh x-Real.sinh x) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    · intro x hx; exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x).deriv]
      exact mul_nonneg (interior_subset hx) (Real.sinh_nonneg_iff.mpr (interior_subset hx))
  have h := hm (by simp : (0 : ℝ) ∈ Ici 0) ht ht
  norm_num at h
  linarith

theorem remainder_error_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |remainder t-1/4| ≤ 11*t/48 := by
  have hs := Real.sinh_pos_iff.mpr ht
  have hc := Real.cosh_pos (t/2)
  have hst := Real.self_le_sinh_iff.mpr ht.le
  have hcube := sinh_sub_self_le_cube ht.le ht1
  have hleft : |1/(2*Real.sinh t)-1/(2*t)| ≤ t/6 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le (by positivity) (by linarith)))]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
    have hid : -(1/(2*Real.sinh t)-1/(2*t)) =
        (Real.sinh t-t)/(2*t*Real.sinh t) := by field_simp; ring
    rw [hid]
    have h := (div_le_iff₀ (by positivity : 0 < 2*t*Real.sinh t)).mpr
      (show Real.sinh t-t ≤ (t/6)*(2*t*Real.sinh t) by nlinarith [sq_nonneg t])
    nlinarith
  have hright : |1/(4*Real.cosh (t/2)^2)-1/4| ≤ t^2/16 := by
    have hp := sinh_le_mul_cosh (by linarith : 0 ≤ t/2)
    have hn := Real.sinh_nonneg_iff.mpr (by linarith : 0 ≤ t/2)
    have hsq := mul_self_le_mul_self hn hp
    have he := Real.cosh_sq_sub_sinh_sq (t/2)
    have hcos1 := Real.one_le_cosh (t/2)
    rw [abs_of_nonpos (sub_nonpos.mpr (by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)).mpr
      nlinarith))]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    have hid : -(1/(4*Real.cosh (t/2)^2)-1/4) =
        Real.sinh (t/2)^2/(4*Real.cosh (t/2)^2) := by
      field_simp; nlinarith [he]
    rw [hid]
    have h := (div_le_iff₀ (by positivity : 0 < 4*Real.cosh (t/2)^2)).mpr
      (show Real.sinh (t/2)^2 ≤ (t^2/16)*(4*Real.cosh (t/2)^2) by nlinarith [hsq])
    nlinarith
  have hsplit : remainder t-1/4 =
      (1/(2*Real.sinh t)-1/(2*t)) + (1/(4*Real.cosh (t/2)^2)-1/4) := by
    unfold remainder SechGammaBounds.kernel
    ring
  rw [hsplit]
  calc
    _ ≤ |1/(2*Real.sinh t)-1/(2*t)| + |1/(4*Real.cosh (t/2)^2)-1/4| := abs_add_le _ _
    _ ≤ t/6+t^2/16 := add_le_add hleft hright
    _ ≤ 11*t/48 := by nlinarith
end RiemannResearch.Analysis.SechGammaDiagonal

namespace RiemannResearch.Analysis.SechGammaDiagonal
def halfCsch (t : ℝ) : ℝ := 1/(2*Real.sinh t)
def cschPrimitive (t : ℝ) : ℝ :=
  (Real.log (1-Real.exp (-t))-Real.log (1+Real.exp (-t)))/2

theorem hasDerivAt_cschPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt cschPrimitive (halfCsch t) t := by
  have hm : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp : 0 < Real.exp (-t) := Real.exp_pos _
  have hd := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
  have hdm := ((hasDerivAt_const t (1 : ℝ)).sub hd).log (by change 1-Real.exp (-t)≠0; linarith)
  have hdp := ((hasDerivAt_const t (1 : ℝ)).add hd).log (by change 1+Real.exp (-t)≠0; positivity)
  convert! (hdm.sub hdp).div_const 2 using 1
  simp only [halfCsch, Real.sinh_eq, Function.comp_def, Pi.sub_apply, Pi.add_apply]
  have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hem : Real.exp t-Real.exp (-t) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))).ne'
  have hprod : Real.exp t*Real.exp (-t) = 1 := by rw [←Real.exp_add]; simp
  field_simp [(sub_pos.mpr hm).ne', (show 1+Real.exp (-t) ≠ 0 by positivity), hem]
  nlinarith [hprod, congrArg (fun x : ℝ => x*Real.exp (-t)^2) hprod]

theorem cschPrimitive_tendsto_atTop :
    Tendsto cschPrimitive atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero
  have hm := (tendsto_const_nhds.sub h).log (by norm_num : (1 : ℝ)-0≠0)
  have hp := (tendsto_const_nhds.add h).log (by norm_num : (1 : ℝ)+0≠0)
  change Tendsto (fun t => (Real.log (1-Real.exp (-t))-Real.log (1+Real.exp (-t)))/2) atTop (𝓝 0)
  convert! (hm.sub hp).div_const 2 using 1 <;> norm_num

theorem cschPrimitive_sub_log_tendsto_zero :
    Tendsto (fun t => cschPrimitive t-Real.log t/2) (𝓝[>] 0)
      (𝓝 (-Real.log 2/2)) := by
  have hd : HasDerivAt (fun t : ℝ => 1-Real.exp (-t)) 1 0 := by
    convert! (hasDerivAt_const 0 (1 : ℝ)).sub
      ((Real.hasDerivAt_exp (-(0 : ℝ))).comp 0 (hasDerivAt_neg 0)) using 1 <;> norm_num
  have hr : Tendsto (fun t : ℝ => (1-Real.exp (-t))/t) (𝓝[>] 0) (𝓝 1) := by
    simpa [div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((by fun_prop : ContinuousAt (fun t : ℝ => Real.exp (-t)) 0).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  have hl := (hr.log (by norm_num : (1 : ℝ)≠0)).sub
    ((tendsto_const_nhds.add he).log (by norm_num : (1 : ℝ)+1≠0))
  have hh : Tendsto (fun t : ℝ =>
      (Real.log ((1-Real.exp (-t))/t)-Real.log (1+Real.exp (-t)))/2)
      (𝓝[>] 0) (𝓝 (-Real.log 2/2)) := by
    convert! hl.div_const 2 using 1 <;> norm_num
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hne : 1-Real.exp (-t)≠0 := (sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (by linarith : -t < 0))).ne'
  rw [Real.log_div hne (ne_of_gt ht)]
  unfold cschPrimitive
  ring

theorem halfCsch_integrable_tail {a : ℝ} (ha : 0 < a) :
    IntegrableOn halfCsch (Ioi a) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    (hasDerivAt_cschPrimitive ha).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_cschPrimitive (ha.trans hx))
    (fun x hx => by
      have hs := Real.sinh_pos_iff.mpr (ha.trans hx)
      dsimp [halfCsch]; positivity)
    cschPrimitive_tendsto_atTop

theorem halfCsch_integral_tail {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi a, halfCsch t) = -cschPrimitive a := by
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_cschPrimitive ha).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_cschPrimitive (ha.trans hx))
    (halfCsch_integrable_tail ha) cschPrimitive_tendsto_atTop
end RiemannResearch.Analysis.SechGammaDiagonal

namespace RiemannResearch.Analysis.SechGammaDiagonal

theorem halfCsch_remainder_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |halfCsch t-1/(2*t)| ≤ t/6 := by
  have hs := Real.sinh_pos_iff.mpr ht
  have hst := Real.self_le_sinh_iff.mpr ht.le
  have hcube := sinh_sub_self_le_cube ht.le ht1
  dsimp only [halfCsch]
  rw [abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le (by positivity) (by linarith)))]
  have hid : -(1/(2*Real.sinh t)-1/(2*t)) =
      (Real.sinh t-t)/(2*t*Real.sinh t) := by field_simp; ring
  rw [hid]
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith [sq_nonneg t])

theorem halfCsch_remainder_integrable {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (fun t => halfCsch t-1/(2*t)) (Ioc 0 a) := by
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 a) :=
    (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply hi.mono' (by unfold halfCsch; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact (halfCsch_remainder_bound ht.1 (ht.2.trans ha1)).trans (by linarith [ht.2])

theorem halfCsch_remainder_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ t in Ioc 0 a, halfCsch t-1/(2*t)) =
      cschPrimitive a-Real.log a/2+Real.log 2/2 := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun t => cschPrimitive t-Real.log t/2)
        (halfCsch x-1/(2*x)) x := by
    convert! (hasDerivAt_cschPrimitive hx).sub
      ((Real.hasDerivAt_log hx.ne').div_const 2) using 1 <;> ring
  have hi : IntervalIntegrable (fun t => halfCsch t-1/(2*t)) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr
      (halfCsch_remainder_integrable ha ha1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ha
    (fun x hx => hd x hx.1) hi cschPrimitive_sub_log_tendsto_zero
    ((hd a ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [intervalIntegral.integral_of_le ha.le] at h
  simpa only [neg_div, sub_neg_eq_add] using h

def cutoffCsch (a t : ℝ) : ℝ :=
  if t ≤ a then halfCsch t-1/(2*t) else halfCsch t

theorem cutoffCsch_integrable {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (cutoffCsch a) (Ioi 0) := by
  have hunion : Ioc 0 a ∪ Ioi a = Ioi 0 := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact ha.trans ht
    · intro ht
      rcases le_or_gt t a with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
  rw [←hunion]
  apply IntegrableOn.union
  · apply (halfCsch_remainder_integrable ha ha1).congr_fun _ measurableSet_Ioc
    intro t ht
    simp [cutoffCsch, ht.2]
  · apply (halfCsch_integrable_tail ha).congr_fun _ measurableSet_Ioi
    intro t ht
    simp [cutoffCsch, not_le.mpr (show a < t from ht)]

theorem cutoffCsch_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ t in Ioi 0, cutoffCsch a t) = (Real.log 2-Real.log a)/2 := by
  have hunion : Ioc 0 a ∪ Ioi a = Ioi 0 := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact ha.trans ht
    · intro ht
      rcases le_or_gt t a with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
  have hi := cutoffCsch_integrable ha ha1
  have his : IntegrableOn (cutoffCsch a) (Ioc 0 a) := hi.mono_set Ioc_subset_Ioi_self
  have hit : IntegrableOn (cutoffCsch a) (Ioi a) := hi.mono_set (Ioi_subset_Ioi ha.le)
  rw [←hunion, setIntegral_union (by
    rw [Set.disjoint_left]
    intro t ht hta
    exact (not_lt.mpr ht.2) hta) measurableSet_Ioi his hit]
  have hs : (∫ t in Ioc 0 a, cutoffCsch a t) =
      ∫ t in Ioc 0 a, halfCsch t-1/(2*t) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht; simp [cutoffCsch, ht.2]
  have ht : (∫ t in Ioi a, cutoffCsch a t) = ∫ t in Ioi a, halfCsch t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht; simp [cutoffCsch, not_le.mpr (show a < t from ht)]
  rw [hs, ht, halfCsch_remainder_integral ha ha1, halfCsch_integral_tail ha]
  ring
end RiemannResearch.Analysis.SechGammaDiagonal

namespace RiemannResearch.Analysis.SechGammaDiagonal

theorem integral_positive_eq_Ioc {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hzero : ∀ t, a < t → g t = 0) :
    (∫ t in Ioi 0, g t) = ∫ t in Ioc 0 a, g t := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro t ht
  apply hzero
  by_contra h
  exact ht.2 ⟨ht.1, le_of_not_gt h⟩

theorem integrable_positive_of_Ioc {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hi : IntegrableOn g (Ioc 0 a)) (hzero : ∀ t, a < t → g t = 0) :
    IntegrableOn g (Ioi 0) := by
  have hu : Ioc 0 a ∪ Ioi a = Ioi 0 := by
    ext t; constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact ha.trans_lt ht
    · intro ht
      rcases le_or_gt t a with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
  rw [←hu]
  apply hi.union
  apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi a) volume).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (hzero t ht).symm

theorem integral_Ioc_comp_mul (g : ℝ → ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) :
    (∫ t in Ioc 0 a, g (T*t)) = (1/T)*(∫ x in Ioc 0 (T*a), g x) := by
  have h := intervalIntegral.integral_comp_mul_left (a:=0) (b:=a) g hT.ne'
  rw [intervalIntegral.integral_of_le ha] at h
  rw [mul_zero, intervalIntegral.integral_of_le (mul_nonneg hT.le ha)] at h
  simpa only [smul_eq_mul, one_div] using h

def cutoffSlope (F : ℝ → ℝ) (T t : ℝ) : ℝ :=
  if t ≤ 1/T then (F (T*t)-F 0)/(2*t) else 0

theorem cutoffSlope_integrable {F : ℝ → ℝ} (hF : Continuous F)
    {K : ℝ} (hK : 0 ≤ K) (hLip : ∀ x, 0 < x → |F x - F 0| ≤ K * x)
    {T : ℝ} (hT : 1 < T) :
    IntegrableOn (cutoffSlope F T) (Ioi 0) := by
  have hT0 : 0 < T := by linarith
  apply integrable_positive_of_Ioc (show 0 ≤ 1/T by positivity)
  · have hi : IntegrableOn (fun _ : ℝ => K*T/2) (Ioc 0 (1/T)) :=
      (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hm : AEStronglyMeasurable (fun t => (F (T*t)-F 0)/(2*t))
        (volume.restrict (Ioc 0 (1/T))) := by
      have hm' : Measurable (fun t => (F (T*t)-F 0)/(2*t)) :=
        ((hF.measurable.comp (by fun_prop)).sub measurable_const).div (by fun_prop)
      exact hm'.aestronglyMeasurable
    apply hi.mono' (hm.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [cutoffSlope, if_pos ht.2]))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, cutoffSlope, if_pos ht.2, abs_div,
      abs_of_pos (show 0 < 2*t by positivity)]
    exact (div_le_iff₀ (by positivity)).mpr (by
      have h := hLip (T*t) (mul_pos hT0 ht.1)
      nlinarith)
  · intro t ht; simp only [cutoffSlope, if_neg (not_le.mpr ht)]

theorem remainder_window_integrable {F : ℝ → ℝ} (hF : Continuous F)
    {K : ℝ} (hK : 0 ≤ K) (hLip : ∀ x, 0 < x → |F x - F 0| ≤ K * x)
    (hzero : ∀ x, 1 < x → F x = 0) {T : ℝ} (hT : 1 < T) :
    IntegrableOn (fun t => remainder t*F (T*t)) (Ioi 0) := by
  have hT0 : 0 < T := by linarith
  have ha1 : 1/T ≤ 1 := (div_le_one hT0).mpr hT.le
  have hTa : T*(1/T) = 1 := by field_simp
  apply integrable_positive_of_Ioc (show 0 ≤ 1/T by positivity)
  · have hi : IntegrableOn (fun _ : ℝ => |F 0|+K) (Ioc 0 (1/T)) :=
      (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    apply hi.mono' (by unfold remainder SechGammaBounds.kernel; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htx : T*t ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hT0.le]
    have hb : |remainder t| ≤ 1 := by
      have h := remainder_error_le ht.1 (ht.2.trans ha1)
      have hh := abs_add_le (remainder t-1/4) (1/4 : ℝ)
      norm_num at hh
      linarith [ht.2]
    have hf : |F (T*t)| ≤ |F 0|+K := by
      have h := hLip (T*t) (mul_pos hT0 ht.1)
      have hh := abs_add_le (F (T*t)-F 0) (F 0)
      simp only [sub_add_cancel] at hh
      nlinarith
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul hb hf (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  · intro t ht
    have hx : 1 < T*t := by nlinarith [mul_lt_mul_of_pos_left ht hT0]
    rw [hzero _ hx, mul_zero]

theorem cutoffSlope_integral (F : ℝ → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioi 0, cutoffSlope F T t) =
      -(1/2 : ℝ)*(∫ x in Ioc 0 1, (F 0-F x)/x) := by
  rw [integral_positive_eq_Ioc (show 0 ≤ 1/T by positivity)
    (fun t ht => by simp only [cutoffSlope, if_neg (not_le.mpr ht)])]
  have he : (∫ t in Ioc 0 (1/T), cutoffSlope F T t) =
      T*(∫ t in Ioc 0 (1/T), (F (T*t)-F 0)/(2*(T*t))) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    rw [cutoffSlope, if_pos ht.2]
    field_simp
  rw [he, integral_Ioc_comp_mul (fun x => (F x - F 0)/(2*x)) (by positivity) hT]
  have hTa : T*(1/T) = 1 := by field_simp
  rw [hTa, ←mul_assoc, hTa, one_mul]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  field_simp
  ring

theorem remainder_window_integral (F : ℝ → ℝ)
    (hzero : ∀ x, 1 < x → F x = 0) {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioi 0, remainder t*F (T*t)) =
      (1/T)*(∫ x in Ioc 0 1, F x*remainder (x/T)) := by
  have hTa : T*(1/T) = 1 := by field_simp
  rw [integral_positive_eq_Ioc (show 0 ≤ 1/T by positivity) (fun t ht => by
    have hx : 1 < T*t := by nlinarith [mul_lt_mul_of_pos_left ht hT]
    rw [hzero _ hx, mul_zero])]
  have he : (fun t => remainder t*F (T*t)) =
      fun t => F (T*t)*remainder ((T*t)/T) := by
    funext t
    rw [mul_div_cancel_left₀ _ hT.ne']
    ring
  rw [he, integral_Ioc_comp_mul (fun x => F x*remainder (x/T)) (by positivity) hT, hTa]

theorem regulated_rescale {F : ℝ → ℝ} (hF : Continuous F)
    {K : ℝ} (hK : 0 ≤ K) (hLip : ∀ x, 0 < x → |F x - F 0| ≤ K * x)
    (hzero : ∀ x, 1 < x → F x = 0) {T : ℝ} (hT : 1 < T) :
    (∫ t in Ioi 0, SechGammaBounds.kernel t*F (T*t)-halfCsch t*F 0) =
      -(1/2 : ℝ)*(∫ x in Ioc 0 1, (F 0-F x)/x) +
      (1/T)*(∫ x in Ioc 0 1, F x*remainder (x/T)) -
      F 0*((Real.log 2+Real.log T)/2) := by
  have hT0 : 0 < T := by linarith
  have ha1 : 1/T ≤ 1 := (div_le_one hT0).mpr hT.le
  have hj := cutoffSlope_integrable hF hK hLip hT
  have hb := remainder_window_integrable hF hK hLip hzero hT
  have hr := (cutoffCsch_integrable (show 0 < 1/T by positivity) ha1).const_mul (F 0)
  have he : (∫ t in Ioi 0, SechGammaBounds.kernel t*F (T*t)-halfCsch t*F 0) =
      ∫ t in Ioi 0, cutoffSlope F T t+remainder t*F (T*t)-F 0*cutoffCsch (1/T) t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [cutoffSlope, cutoffCsch, remainder, halfCsch]
    split_ifs with h
    · field_simp
      ring
    · have hTa : T*(1/T) = 1 := by field_simp
      have hz : F (T*t) = 0 := hzero _ (by
        have hh := mul_lt_mul_of_pos_left (lt_of_not_ge h) hT0
        linarith)
      rw [hz]
      ring
  have hsum := hj.add hb
  change Integrable (fun t => cutoffSlope F T t+remainder t*F (T*t))
      (volume.restrict (Ioi 0)) at hsum
  rw [he, integral_sub hsum hr, integral_add hj hb, integral_const_mul,
    cutoffSlope_integral _ hT0, remainder_window_integral _ hzero hT0,
    cutoffCsch_integral (show 0 < 1/T by positivity) ha1]
  simp only [one_div, Real.log_inv, sub_neg_eq_add]
end RiemannResearch.Analysis.SechGammaDiagonal

namespace RiemannResearch.Analysis.SechGammaDiagonal

def absoluteFirstMoment (F : ℝ → ℝ) : ℝ :=
  2*(∫ x in Ioc 0 1, x*|F x|)

theorem centered_window_bound (F : ℝ → ℝ) (hF : Continuous F)
    {T : ℝ} (hT : 1 < T) :
    |∫ x in Ioc 0 1, F x*(remainder (x/T)-1/4)| ≤
      11*absoluteFirstMoment F/(96*T) := by
  have hT0 : 0 < T := by linarith
  have hi : IntegrableOn (fun x : ℝ => (11/(48*T))*(x*|F x|)) (Ioc 0 1) :=
    ((by fun_prop : Continuous (fun x : ℝ =>
      (11/(48*T))*(x*|F x|))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h := norm_integral_le_of_norm_le hi (f:=fun x => F x*(remainder (x/T)-1/4)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hxt : x/T ≤ 1 := (div_le_one hT0).mpr (hx.2.trans hT.le)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |F x| * (11*(x/T)/48) :=
        mul_le_mul_of_nonneg_left (remainder_error_le (div_pos hx0 hT0) hxt) (abs_nonneg _)
      _ = _ := by ring)
  rw [Real.norm_eq_abs, integral_const_mul] at h
  calc
    _ ≤ (11/(48*T))*(∫ x in Ioc 0 1, x*|F x|) := h
    _ = _ := by unfold absoluteFirstMoment; ring

theorem centered_window_integrable (F : ℝ → ℝ) (hF : Continuous F)
    {T : ℝ} (hT : 1 < T) :
    IntegrableOn (fun x => F x*(remainder (x/T)-1/4)) (Ioc 0 1) := by
  have hT0 : 0 < T := by linarith
  have hi : IntegrableOn (fun x : ℝ => (11/(48*T))*(x*|F x|)) (Ioc 0 1) :=
    ((by fun_prop : Continuous (fun x : ℝ =>
      (11/(48*T))*(x*|F x|))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply hi.mono' (by unfold remainder SechGammaBounds.kernel; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx0 : 0 < x := hx.1
  have hxt : x/T ≤ 1 := (div_le_one hT0).mpr (hx.2.trans hT.le)
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |F x| * (11*(x/T)/48) :=
      mul_le_mul_of_nonneg_left (remainder_error_le (div_pos hx0 hT0) hxt) (abs_nonneg _)
    _ = _ := by ring

theorem window_integral_centered (F : ℝ → ℝ) (hF : Continuous F)
    (hmean : (∫ x in Ioc 0 1, F x) = 0) {T : ℝ} (hT : 1 < T) :
    (∫ x in Ioc 0 1, F x*remainder (x/T)) =
      ∫ x in Ioc 0 1, F x*(remainder (x/T)-1/4) := by
  have hi : IntegrableOn (fun x => F x*(1/4 : ℝ)) (Ioc 0 1) :=
    ((hF.mul continuous_const).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hj := centered_window_integrable F hF hT
  have he : (fun x => F x*remainder (x/T)) =
      fun x => F x*(remainder (x/T)-1/4)+F x*(1/4) := by funext x; ring
  rw [he, integral_add hj hi, integral_mul_const, hmean, zero_mul, add_zero]

theorem normalized_window_integral_bound (F : ℝ → ℝ) (hF : Continuous F)
    (hmean : (∫ x in Ioc 0 1, F x) = 0) {T : ℝ} (hT : 1 < T) :
    |-(2/(T*Real.log T))*(∫ x in Ioc 0 1, F x*remainder (x/T))| ≤
      11*absoluteFirstMoment F/(48*T^2*Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hlog := Real.log_pos hT
  rw [window_integral_centered F hF hmean hT, abs_mul, abs_neg,
    abs_of_pos (show 0 < 2/(T*Real.log T) by positivity)]
  calc
    _ ≤ (2/(T*Real.log T))*(11*absoluteFirstMoment F/(96*T)) :=
      mul_le_mul_of_nonneg_left (centered_window_bound F hF hT) (by positivity)
    _ = _ := by ring
end RiemannResearch.Analysis.SechGammaDiagonal

namespace RiemannResearch.Analysis.SechGammaDiagonal
open RiemannResearch.Analysis

theorem half_mean_eq_zero_of_window {F : ℝ → ℝ} (hF : Continuous F)
    (hs : Function.support F ⊆ Icc (-1 : ℝ) 1) (he : ∀ x, F (-x) = F x)
    (hmean : SechGammaBounds.windowMoment F 0 = 0) :
    (∫ x in Ioc 0 1, F x) = 0 := by
  have hc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  have hi : Integrable F := hF.integrable_of_hasCompactSupport hc
  have htotal : (∫ x : ℝ, F x) = 0 := by
    have hr : (∫ x in Icc (-1 : ℝ) 1, F x) = ∫ x : ℝ, F x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
        by
          by_contra h
          exact hx (hs h))
    rw [←hr]
    simpa [SechGammaBounds.windowMoment] using hmean
  have hh := integral_eq_two_smul_Ioi_of_even F hi he
  simp only [smul_eq_mul] at hh
  have hz (x : ℝ) (hx : 1 < x) : F x = 0 :=
    by
      by_contra h
      exact (not_le.mpr hx) (hs h).2
  rw [integral_positive_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1) hz, htotal] at hh
  linarith

end RiemannResearch.Analysis.SechGammaDiagonal

namespace RiemannResearch.Analysis.SechGammaDiagonal
open RiemannResearch.Analysis

/-- For an even supported window, the positive-half-line definition is the full
absolute first moment appearing in the diagonal estimate. -/
theorem absoluteFirstMoment_eq_integral {F : ℝ → ℝ} (hF : Continuous F)
    (hs : Function.support F ⊆ Icc (-1 : ℝ) 1) (he : ∀ x, F (-x) = F x) :
    absoluteFirstMoment F = ∫ x in Icc (-1 : ℝ) 1, |x| * |F x| := by
  let G : ℝ → ℝ := fun x => |x| * |F x|
  have hGc : Continuous G := by dsimp [G]; fun_prop
  have hGs : Function.support G ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    by_contra h
    have hFx : F x = 0 := by
      by_contra hxF
      exact h (hs hxF)
    exact hx (by simp [G, hFx])
  have hc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hGs
  have hi : Integrable G := hGc.integrable_of_hasCompactSupport hc
  have hr : (∫ x in Icc (-1 : ℝ) 1, G x) = ∫ x : ℝ, G x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra h
      exact hx (hGs h))
  have hh := integral_eq_two_smul_Ioi_of_even G hi (by
    intro x
    simp [G, he])
  simp only [smul_eq_mul] at hh
  have hz (x : ℝ) (hx : 1 < x) : G x = 0 := by
    by_contra h
    exact (not_le.mpr hx) (hGs h).2
  change absoluteFirstMoment F = ∫ x in Icc (-1 : ℝ) 1, G x
  rw [hr, hh, integral_positive_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1) hz]
  unfold absoluteFirstMoment
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only [G, abs_of_pos hx.1]

end RiemannResearch.Analysis.SechGammaDiagonal
