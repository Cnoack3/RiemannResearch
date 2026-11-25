import RiemannResearch.Analysis.XiHorizontalComparison
import RiemannResearch.Analysis.GammaRatioVertical
import RiemannResearch.RH.ParetoShiftedZetaCompactWindow
import RiemannResearch.RH.BurnolCriticalLine
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # A uniform high-ordinate bound for the critical-line shifted quotient

The horizontal comparison for xi supplies the zeta inequality. The elementary
quadratic prefactor decreases on one side of the critical point, and the
uniform vertical gamma estimate controls the remaining high-ordinate growth.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_re criticalPoint_ne_one criticalPoint_ne_zero)
open RiemannResearch.Analysis.XiHorizontalComparison (zeta_horizontal_comparison)
open RiemannResearch.Analysis.GammaRatioVertical

private theorem norm_arch_factor (a t : ℝ) :
    ‖Complex.Gammaℝ ((a : ℂ) + (t : ℂ) * I)‖ =
      Real.pi ^ (-(a / 2)) * ‖Gamma (((a / 2 : ℝ) : ℂ) + I * (t / 2))‖ := by
  have hre : (-((a : ℂ) + (t : ℂ) * I) / 2).re = -(a / 2) := by simp; ring
  have hv : ((a : ℂ) + (t : ℂ) * I) / 2 = (((a / 2 : ℝ) : ℂ) + I * (t / 2)) := by
    push_cast
    ring
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hre, hv]

/-- Under RH, the critical-line shifted quotient has a uniform explicit
majorant above height one for every shift in (0,1]. -/
theorem shiftedZetaQuotient_high_le_up_to_one (hRH : RiemannHypothesis) {ε t : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (ht : 1 ≤ |t|) :
    ‖shiftedZetaQuotient ε t‖ ≤ (1 + ε) * Real.pi ^ (-(ε / 2)) *
      (Real.exp (10 * ε / t ^ 2) * (|t| / 2) ^ (ε / 2)) := by
  let s := criticalPoint t
  let w := s + (ε : ℂ)
  have hs : s.re = 1/2 := criticalPoint_re t
  have hw : w.re = 1/2 + ε := by simp [w, hs]
  have hv : w = (((1/2 + ε : ℝ) : ℂ) + (t : ℂ) * I) := by
    dsimp [w, s, criticalPoint]
    push_cast
    ring
  have hv' : s = (((1/2 : ℝ) : ℂ) + (t : ℂ) * I) := by simp [s, criticalPoint]
  have hi : s.im = w.im := by simp [w]
  have hsw : s.re ≤ w.re := by rw [hs, hw]; linarith
  have hw1 : w ≠ 1 := fun h => by
    have hv₀ := congrArg Complex.im h
    have him : w.im = t := by simp [w,s,criticalPoint]
    rw [him,Complex.one_im] at hv₀
    rw [hv₀,abs_zero] at ht
    linarith
  have hz : riemannZeta w ≠ 0 := by
    rcases lt_or_ge w.re 1 with hr | hr
    · exact riemannHypothesis_iff_right_half_strip_zero_free.mp hRH w (by rw [hw]; linarith) hr
    · exact riemannZeta_ne_zero_of_one_le_re hr
  have hg : 0 < ‖Complex.Gammaℝ s‖ :=
    norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num))
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr (criticalPoint_ne_zero t)
  have hsm : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (criticalPoint_ne_one t))
  have ht' : 1 ≤ ‖s‖ := ht.trans (by simpa [s, criticalPoint] using Complex.abs_im_le_norm s)
  have hpoly₁ : ‖w‖ ≤ (1+ε) * ‖s‖ := by
    have h := norm_add_le s (ε : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at h
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_left ht' hε.le]
  have hpoly₂ : ‖w-1‖ ≤ ‖s-1‖ := by
    have hh : ‖w-1‖^2 ≤ ‖s-1‖^2 := by
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, hs, hw, hi]
      nlinarith only [mul_nonneg hε.le (show 0 ≤ 1-ε by linarith)]
    nlinarith only [hh, norm_nonneg (w-1), norm_nonneg (s-1)]
  have hpol := mul_le_mul hpoly₁ hpoly₂ (norm_nonneg _) (by positivity)
  have hP : ‖w‖ * ‖w-1‖ / (‖s‖ * ‖s-1‖) ≤ (1+ε) := by
    apply (div_le_iff₀ (mul_pos hsn hsm)).mpr
    simpa only [mul_assoc] using hpol
  have ht₂ : 1/2 ≤ |t/2| := by rw [abs_div, abs_two]; linarith
  have hG := norm_Gamma_ratio_le_of_pos (a := (1/2)/2) (b := (1/2 + ε)/2) (t := t/2)
    (by norm_num) (by norm_num) (by linarith) (by linarith) ht₂
  have hgd : (1/2 + ε)/2 - (1/2)/2 = ε/2 := by ring
  have hgr : 5 * |ε / 2| / (t / 2)^2 = 10 * ε / t^2 := by rw [abs_of_pos (by positivity : 0 < ε/2)]; ring
  rw [hgd, hgr, abs_div, abs_two] at hG
  have hA : ‖Complex.Gammaℝ w‖ / ‖Complex.Gammaℝ s‖ ≤
      Real.pi ^ (-(ε/2)) * (Real.exp (10*ε / t^2) * (|t|/2) ^ (ε/2)) := by
    rw [hv, hv', norm_arch_factor, norm_arch_factor, mul_div_mul_comm, ← Real.rpow_sub Real.pi_pos,
      show -((1/2 + ε)/2) - -((1/2)/2) = -(ε/2) by ring, ← norm_div]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg Real.pi_pos.le _)
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hG
  have hCmp := zeta_horizontal_comparison hRH hs.ge hsw hi (criticalPoint_ne_one t) hw1
  have hratio : ‖shiftedZetaQuotient ε t‖ ≤
      (‖w‖ * ‖w-1‖ / (‖s‖ * ‖s-1‖)) * (‖Complex.Gammaℝ w‖ / ‖Complex.Gammaℝ s‖) := by
    change ‖riemannZeta s / riemannZeta w‖ ≤ _
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hz)]
    field_simp [hsn.ne', hsm.ne', hg.ne']
    linarith only [hCmp]
  exact hratio.trans ((mul_le_mul hP hA (div_nonneg (norm_nonneg _) hg.le) (by linarith)).trans_eq (by ring))

/-- Under RH, the critical-line shifted quotient has a uniform explicit
majorant above height one for every shift in (0,1/4]. -/
theorem shiftedZetaQuotient_high_le (hRH : RiemannHypothesis) {ε t : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1/4) (ht : 1 ≤ |t|) :
    ‖shiftedZetaQuotient ε t‖ ≤ (1 + ε) * Real.pi ^ (-(ε / 2)) *
      (Real.exp (10 * ε / t ^ 2) * (|t| / 2) ^ (ε / 2)) :=
  shiftedZetaQuotient_high_le_up_to_one hRH hε (by linarith) ht

/-- The elementary quadratic factors in xi have no term linear in the
horizontal shift on the critical line. -/
theorem critical_polynomial_shift_exact (ε t : ℝ) :
    let s := criticalPoint t
    let w := s + (ε : ℂ)
    (‖w‖ * ‖w-1‖)^2 - (‖s‖ * ‖s-1‖)^2 = ε^2*(2*t^2 + ε^2 - 1/2) := by
  dsimp only
  simp only [mul_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, criticalPoint_re]
  simp [criticalPoint]
  ring

private theorem compact_shifted_square_bounded :
    ∃ C ≥ 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (-1 : ℝ) 1,
      boundarySquare (fun v => 1 - shiftedZetaQuotient ε v) t ≤ C := by
  classical
  choose r hr A hA hlocal using shiftedZetaQuotient_local_bound
  let U a := Metric.ball a (r a)
  have hcov : Icc (-1 : ℝ) 1 ⊆ ⋃ a, U a := fun t _ => mem_iUnion.mpr ⟨t, Metric.mem_ball_self (hr t)⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcov
  refine ⟨∑ a ∈ s, 2 * A a, Finset.sum_nonneg (fun a _ => by positivity [hA a]), ?_⟩
  have hr' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ s, ε < r a :=
    (Filter.eventually_all_finset s).mpr fun a _ => (gt_mem_nhds (hr a)).filter_mono nhdsWithin_le_nhds
  have hε' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 := (gt_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hr', hε', (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε)] with ε he h1 h0 t ht
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hs ht)
  obtain ⟨has, hat⟩ := mem_iUnion.mp ha
  change 0 < ε at h0
  have he2 : ε^2 ≤ 1 := by nlinarith [mul_nonneg h0.le (show 0 ≤ 1-ε by linarith)]
  have hd : 0 < ε^2 + (t-a)^2 := by positivity
  have hdiv : ε^2 / (ε^2 + (t-a)^2) ≤ 1 := (div_le_one hd).mpr (by nlinarith [sq_nonneg (t-a)])
  have hlocal' := (hlocal a t ε (by simpa [U, Metric.mem_ball, Real.dist_eq] using hat) h0 (he a has)).2
  apply hlocal'.trans ((mul_le_mul_of_nonneg_left (show ε^2+ε^2/(ε^2+(t-a)^2) ≤ 2 by linarith only [hdiv, he2]) (hA a)).trans _)
  rw [mul_comm (A a)]
  exact Finset.single_le_sum (f := fun b : ℝ => 2*A b) (fun b _ => mul_nonneg (by norm_num) (hA b)) has

private theorem high_shifted_square_le (hRH : RiemannHypothesis) {ε t : ℝ}
    (he : 0 < ε) (he' : ε ≤ 1/4) (ht : 1 ≤ |t|) :
    boundarySquare (fun v => 1 - shiftedZetaQuotient ε v) t ≤
      (4 * (1 + 2 * Real.exp 3)^2) * (1+‖t‖^2) ^ (-(3/2:ℝ)/2) := by
  let Q := 1 + ‖t‖^2
  have hQ₁ : 1 ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg ‖t‖]
  have hQ : 0 < Q := by linarith
  have hD : 0 < 1/4+t^2 := by positivity
  have ht₂ : 1 ≤ t^2 := by nlinarith [sq_abs t, sq_nonneg (|t|-1)]
  have hp : Real.pi ^ (-(ε/2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have he3 : Real.exp (10*ε/t^2) ≤ Real.exp 3 := Real.exp_le_exp.mpr ((div_le_iff₀ (by linarith : 0 < t^2)).mpr (by linarith))
  have hb : |t|/2 ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg (|t|-1/2)]
  have hpow : (|t|/2) ^ (ε/2) ≤ Q ^ (1/8:ℝ) :=
    (Real.rpow_le_rpow (by positivity) hb (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ₁ (by linarith))
  have hpref : (1+ε) * Real.pi ^ (-(ε/2)) ≤ 2 := by
    have := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1+ε by linarith)
    linarith
  have hq : ‖shiftedZetaQuotient ε t‖ ≤ 2 * Real.exp 3 * Q ^ (1/8:ℝ) := by
    apply (shiftedZetaQuotient_high_le hRH he he' ht).trans
    conv_rhs => rw [mul_assoc]
    exact mul_le_mul hpref (mul_le_mul he3 hpow (by positivity) (Real.exp_pos _).le) (by positivity) (by norm_num)
  have h1 : 1 ≤ Q ^ (1/8:ℝ) := Real.one_le_rpow hQ₁ (by norm_num)
  have hdef : ‖1 - shiftedZetaQuotient ε t‖ ≤ (1+2*Real.exp 3) * Q ^ (1/8:ℝ) := by
    have hn := norm_sub_le (1:ℂ) (shiftedZetaQuotient ε t)
    rw [norm_one] at hn
    linarith only [hn, hq, h1]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hdef 2
  have hqs : (Q ^ (1/8:ℝ))^2 = Q ^ (1/4:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]; norm_num
  have hQ4 : Q ≤ 4*(1/4+t^2) := by dsimp [Q]; rw [sq_abs]; nlinarith [sq_nonneg t]
  change ‖1 - shiftedZetaQuotient ε t‖ ^ 2 / (1/4+t^2) ≤ _ * Q ^ (-(3/2:ℝ)/2)
  rw [show -(3/2:ℝ)/2 = 1/4-1 by ring, Real.rpow_sub hQ, Real.rpow_one]
  apply (div_le_iff₀ hD).mpr
  apply hsq.trans
  rw [mul_pow, hqs]
  have hcomp := mul_le_mul_of_nonneg_left hQ4 (show 0 ≤ (1+2*Real.exp 3)^2 * Q^(1/4:ℝ) by positivity)
  field_simp [hQ.ne']
  nlinarith only [hQ4,hcomp]

theorem continuous_shiftedZetaQuotient_of_riemannHypothesis (hRH : RiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/4) : Continuous (shiftedZetaQuotient ε) := by
  have hcp : Continuous criticalPoint := by unfold criticalPoint; fun_prop
  have hs (t : ℝ) : (criticalPoint t + (ε:ℂ)).re = 1/2+ε := by simp
  have hne (t : ℝ) : criticalPoint t + (ε:ℂ) ≠ 1 := fun h => by
    have hh := congrArg Complex.re h; rw [hs, Complex.one_re] at hh; linarith
  have hcn : Continuous (fun t => riemannZeta (criticalPoint t)) := continuous_iff_continuousAt.mpr
    fun t => (differentiableAt_riemannZeta (criticalPoint_ne_one t)).continuousAt.comp hcp.continuousAt
  have hshift : Continuous (fun t : ℝ => criticalPoint t + (ε:ℂ)) := hcp.add continuous_const
  have hcd : Continuous (fun t => riemannZeta (criticalPoint t + (ε:ℂ))) := continuous_iff_continuousAt.mpr
    fun t => (differentiableAt_riemannZeta (hne t)).continuousAt.comp (x := t) hshift.continuousAt
  have hnz (t : ℝ) : riemannZeta (criticalPoint t + (ε:ℂ)) ≠ 0 :=
    (riemannHypothesis_iff_right_half_strip_zero_free.mp hRH) _ (by rw [hs]; linarith) (by rw [hs]; linarith)
  exact hcn.div hcd hnz

/-- Under RH the complete first weighted quotient budget in the
Balazard–de Roton splitting is integrable and tends to zero. -/
theorem shiftedZetaQuotient_budget_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (∀ᶠ ε in 𝓝[>] (0:ℝ), Integrable (boundarySquare (fun t => 1-shiftedZetaQuotient ε t))) ∧
    Tendsto (fun ε => ∫ t, boundarySquare (fun v => 1-shiftedZetaQuotient ε v) t)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  classical
  obtain ⟨C, hC, hc⟩ := compact_shifted_square_bounded
  let f (ε : ℝ) := boundarySquare (fun v => 1-shiftedZetaQuotient ε v)
  let g (t : ℝ) := (Icc (-1:ℝ) 1).indicator (fun _ => C) t +
    (4*(1+2*Real.exp 3)^2) * (1+‖t‖^2) ^ (-(3/2:ℝ)/2)
  have hg : Integrable g := ((integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (by simp))).add ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul (4*(1+2*Real.exp 3)^2))
  have he : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1/4 := (gt_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
  have hm : ∀ᶠ ε in 𝓝[>] (0:ℝ), AEStronglyMeasurable (f ε) volume := by
    filter_upwards [he, hsmall] with ε hε hε'
    have hquot := continuous_shiftedZetaQuotient_of_riemannHypothesis hRH hε hε'.le
    exact (((continuous_const.sub hquot).norm.pow 2).div (by fun_prop)
      (fun t => by positivity : ∀ t : ℝ, (1/4+t^2) ≠ 0)).aestronglyMeasurable
  have hb : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᵐ t, ‖f ε t‖ ≤ g t := by
    filter_upwards [hc, he, hsmall] with ε hloc hε hε'
    filter_upwards [] with t
    have hf : 0 ≤ f ε t := by dsimp [f, boundarySquare]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hf]
    by_cases h : t ∈ Icc (-1:ℝ) 1
    · simp only [g, Set.indicator_of_mem h]
      exact (hloc t h).trans (le_add_of_nonneg_right (by positivity))
    · simp only [g, Set.indicator_of_notMem h, zero_add]
      apply high_shifted_square_le hRH hε hε'.le
      by_contra! hh
      exact h (abs_le.mp hh.le)
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun ε => f ε t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    filter_upwards [RiemannResearch.RH.Burnol.criticalZeta_ne_zero_ae] with t ht
    change riemannZeta (criticalPoint t) ≠ 0 at ht
    have hshift : Tendsto (fun ε:ℝ => criticalPoint t + (ε:ℂ)) (𝓝 0) (𝓝 (criticalPoint t)) := by
      have hc : Continuous (fun ε : ℝ => criticalPoint t + (ε:ℂ)) := continuous_const.add Complex.continuous_ofReal
      simpa only [Complex.ofReal_zero, add_zero] using (hc.tendsto (0:ℝ))
    have hz := (differentiableAt_riemannZeta (criticalPoint_ne_one t)).continuousAt.tendsto.comp hshift
    have hq : Tendsto (fun ε => shiftedZetaQuotient ε t) (𝓝 0) (𝓝 1) := by
      simpa only [shiftedZetaQuotient, Pi.div_def, Function.comp_def, div_self ht] using (tendsto_const_nhds (x := riemannZeta (criticalPoint t))).div hz ht
    have hf := ((((tendsto_const_nhds (x := (1:ℂ))).sub hq).norm.pow 2).div_const (1/4+t^2))
    simpa only [f, boundarySquare, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div] using hf.mono_left nhdsWithin_le_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hb, hm] with ε hbound hmeas
    exact hg.mono' hmeas hbound
  · simpa using (tendsto_integral_filter_of_dominated_convergence (F := f) (f := fun _ => 0) g hm hb hg hlim)

end RiemannResearch.RH.Pareto.ResidueMellin


namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.shiftedZetaQuotient_budget_of_riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shiftedZetaQuotient_budget_of_riemannHypothesis

end RiemannResearch.RH.Pareto.ResidueMellin
