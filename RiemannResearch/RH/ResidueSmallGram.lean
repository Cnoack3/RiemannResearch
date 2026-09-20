import RiemannResearch.RH.ResidueGramDigamma

/-!
# Exact 2,3 Gram entries

Source: user-provided exact Gram coefficient formulas, 20 September 2026.
The proof differentiates Mathlib's Gamma reflection identity, following the
same standard logarithmic-derivative argument as DigammaQuarter. The needed
digamma sums are supplied by the already proved Pareto residue means.
-/

noncomputable section
open scoped BigOperators

namespace Complex

private theorem gamma_differentiable_of_pos_re {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  apply differentiableAt_Gamma z
  intro n hn
  rw [hn] at hz
  simp only [neg_re, natCast_re] at hz
  exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hz

/-- The standard digamma reflection identity on the open critical strip. -/
theorem digamma_reflection_of_pos_re (z : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1)
    (hsin : sin ((Real.pi : ℂ) * z) ≠ 0) :
    digamma z - digamma (1 - z) =
      -(Real.pi : ℂ) * cos ((Real.pi : ℂ) * z) / sin ((Real.pi : ℂ) * z) := by
  have hq : DifferentiableAt ℂ Gamma z := gamma_differentiable_of_pos_re hz
  have ht : DifferentiableAt ℂ Gamma (1 - z) :=
    gamma_differentiable_of_pos_re (by simpa only [sub_re, one_re] using sub_pos.mpr hz1)
  have hlin : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    exact (hasDerivAt_id z).const_sub 1
  have htrans : DifferentiableAt ℂ (fun w : ℂ => Gamma (1 - w)) z :=
    ht.comp z hlin.differentiableAt
  have htranslog : logDeriv (fun w : ℂ => Gamma (1 - w)) z = -digamma (1 - z) := by
    have h := logDeriv_comp (f := Gamma) (g := fun w : ℂ => 1 - w)
      (x := z) ht hlin.differentiableAt
    rw [hlin.deriv] at h
    simpa only [Function.comp_def, mul_neg, mul_one, ← digamma_def] using h
  have hleft : logDeriv (fun w : ℂ => Gamma w * Gamma (1 - w)) z =
      digamma z - digamma (1 - z) := by
    rw [logDeriv_mul (f := Gamma) (g := fun w : ℂ => Gamma (1 - w)) z
      (Gamma_ne_zero_of_re_pos hz)
      (Gamma_ne_zero_of_re_pos (by simpa only [sub_re, one_re] using sub_pos.mpr hz1))
      hq htrans, htranslog]
    rfl
  have hsd : HasDerivAt (fun w : ℂ => sin ((Real.pi : ℂ) * w))
      (cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z := by
    convert ((hasDerivAt_id z).const_mul (Real.pi : ℂ)).csin using 1 <;>
      simp only [id_eq, mul_one]
  have hright : logDeriv (fun w : ℂ => (Real.pi : ℂ) / sin ((Real.pi : ℂ) * w)) z =
      -(Real.pi : ℂ) * cos ((Real.pi : ℂ) * z) / sin ((Real.pi : ℂ) * z) := by
    rw [logDeriv_div (f := fun _ : ℂ => (Real.pi : ℂ))
      (g := fun w : ℂ => sin ((Real.pi : ℂ) * w)) z
      (by exact_mod_cast Real.pi_ne_zero) hsin
      (differentiableAt_const (Real.pi : ℂ)) hsd.differentiableAt,
      logDeriv_const, logDeriv_apply, hsd.deriv]
    simp only [Pi.zero_apply]
    ring
  have heq : (fun w : ℂ => Gamma w * Gamma (1 - w)) =
      (fun w : ℂ => (Real.pi : ℂ) / sin ((Real.pi : ℂ) * w)) :=
    funext Gamma_mul_Gamma_one_sub
  rw [← hleft, heq, hright]

end Complex

namespace RiemannResearch.RH.Pareto
open CoefficientStabilization

theorem re_digamma_thirds_difference :
    (Complex.digamma (2 / 3)).re - (Complex.digamma (1 / 3)).re =
      Real.pi / Real.sqrt 3 := by
  have harg : (Real.pi : ℂ) * (1 / 3) = ((Real.pi / 3 : ℝ) : ℂ) := by
    push_cast
    ring
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 / 3)) ≠ 0 := by
    rw [harg, ← Complex.ofReal_sin, Real.sin_pi_div_three]
    exact_mod_cast (show Real.sqrt 3 / 2 ≠ 0 by positivity)
  have h := Complex.digamma_reflection_of_pos_re (1 / 3) (by norm_num) (by norm_num) hsin
  rw [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num, harg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three] at h
  have he : -(Real.pi : ℂ) * ((1 / 2 : ℝ) : ℂ) /
      ((Real.sqrt 3 / 2 : ℝ) : ℂ) = ((-Real.pi / Real.sqrt 3 : ℝ) : ℂ) := by
    have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
      exact_mod_cast (show Real.sqrt 3 ≠ 0 by positivity)
    push_cast
    field_simp [hs]
  rw [he] at h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.ofReal_re, neg_div] at hr
  linarith

theorem re_digamma_sixths_difference :
    (Complex.digamma (5 / 6)).re - (Complex.digamma (1 / 6)).re =
      3 * Real.pi / Real.sqrt 3 := by
  have harg : (Real.pi : ℂ) * (1 / 6) = ((Real.pi / 6 : ℝ) : ℂ) := by
    push_cast
    ring
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 / 6)) ≠ 0 := by
    rw [harg, ← Complex.ofReal_sin, Real.sin_pi_div_six]
    norm_num
  have h := Complex.digamma_reflection_of_pos_re (1 / 6) (by norm_num) (by norm_num) hsin
  rw [show (1 : ℂ) - 1 / 6 = 5 / 6 by norm_num, harg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_six, Real.sin_pi_div_six] at h
  have he : -(Real.pi : ℂ) * ((Real.sqrt 3 / 2 : ℝ) : ℂ) /
      ((1 / 2 : ℝ) : ℂ) = ((-Real.pi * Real.sqrt 3 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he] at h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.ofReal_re, neg_mul] at hr
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : Real.pi * Real.sqrt 3 = 3 * Real.pi / Real.sqrt 3 := by
    apply (eq_div_iff hs).mpr
    rw [mul_assoc, ← pow_two, hsq]
    ring
  linarith

private theorem re_digamma_thirds_sum :
    (Complex.digamma (1 / 3)).re + (Complex.digamma (2 / 3)).re =
      -2 * Real.eulerMascheroniConstant - 3 * Real.log 3 := by
  have h := periodic_paretoMean 3 (by norm_num) (residue 3)
    (fun k => residue_abs_le 3 k (by norm_num))
    (residue_period_of_dvd (show 3 ∣ 3 from dvd_refl 3))
  rw [paretoMean_residue 3 (by norm_num)] at h
  norm_num [Fin.sum_univ_succ, residue] at h
  rw [progressionWeight_eq_digamma 3 1 (by norm_num) (by norm_num) (by norm_num),
    progressionWeight_eq_digamma 3 2 (by norm_num) (by norm_num) (by norm_num)] at h
  norm_num [Complex.digamma_one] at h
  linarith

set_option maxRecDepth 2000 in
private theorem re_digamma_sixths_sum :
    (Complex.digamma (1 / 6)).re + (Complex.digamma (5 / 6)).re =
      -2 * Real.eulerMascheroniConstant - 4 * Real.log 2 - 3 * Real.log 3 := by
  have h := periodic_paretoMean 6 (by norm_num) (residue 6)
    (fun k => residue_abs_le 6 k (by norm_num))
    (residue_period_of_dvd (show 6 ∣ 6 from dvd_refl 6))
  rw [paretoMean_residue 6 (by norm_num)] at h
  norm_num [Fin.sum_univ_succ, residue] at h
  rw [progressionWeight_eq_digamma 6 1 (by norm_num) (by norm_num) (by norm_num),
    progressionWeight_eq_digamma 6 2 (by norm_num) (by norm_num) (by norm_num),
    progressionWeight_eq_digamma 6 3 (by norm_num) (by norm_num) (by norm_num),
    progressionWeight_eq_digamma 6 4 (by norm_num) (by norm_num) (by norm_num),
    progressionWeight_eq_digamma 6 5 (by norm_num) (by norm_num) (by norm_num)] at h
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    simp
  have hhalf : (Complex.digamma (1 / 2)).re =
      -2 * Real.log 2 - Real.eulerMascheroniConstant := by
    have hc : Complex.digamma (1 / 2) =
        ((-2 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
      rw [Complex.digamma_one_half, hlog]
      push_cast
      ring
    simpa only [Complex.ofReal_re] using congrArg Complex.re hc
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [Complex.digamma_one] at h
  rw [hhalf, hlog6] at h
  linarith [re_digamma_thirds_sum]

/-- Exact G₂₃, with the full infinite weighted Gram entry. -/
theorem residueAtom_inner_zero_one :
    inner ℝ (residueAtom 0) (residueAtom 1) =
      Real.log 2 / 6 + Real.log 3 / 12 - Real.pi / (18 * Real.sqrt 3) := by
  have hg : inner ℝ (residueAtom 0) (residueAtom 1) =
      (progressionWeight 6 1 + 2 * progressionWeight 6 5) / 6 := by
    change inner ℝ (normalizedResidueHilbert 2 _) (normalizedResidueHilbert 3 _) = _
    rw [normalizedResidueHilbert_inner,
      periodic_paretoInner_mixed 6 (by norm_num) (residue 2) (residue 3)
        (fun k => residue_abs_le 2 k (by norm_num))
        (fun k => residue_abs_le 3 k (by norm_num))
        (residue_period_of_dvd (show 2 ∣ 6 by norm_num))
        (residue_period_of_dvd (show 3 ∣ 6 by norm_num))]
    norm_num [Fin.sum_univ_succ, residue]
    ring
  rw [progressionWeight_eq_digamma 6 1 (by norm_num) (by norm_num) (by norm_num),
    progressionWeight_eq_digamma 6 5 (by norm_num) (by norm_num) (by norm_num)] at hg
  norm_num [Complex.digamma_one] at hg
  have h3s := re_digamma_thirds_sum
  have h3d := re_digamma_thirds_difference
  have h6s := re_digamma_sixths_sum
  have h6d := re_digamma_sixths_difference
  linear_combination hg + h3s / 72 - h3d / 72 - h6s / 24 - h6d / 72

/-- Exact G₃₃, with the full infinite weighted Gram entry. -/
theorem residueAtom_one_norm_sq :
    ‖residueAtom 1‖^2 = 2 * Real.log 3 / 9 - Real.pi / (27 * Real.sqrt 3) := by
  have hg : ‖residueAtom 1‖^2 =
      (progressionWeight 3 1 + 4 * progressionWeight 3 2) / 9 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (normalizedResidueHilbert 3 _) (normalizedResidueHilbert 3 _) = _
    rw [normalizedResidueHilbert_inner,
      periodic_paretoInner_mixed 3 (by norm_num) (residue 3) (residue 3)
        (fun k => residue_abs_le 3 k (by norm_num))
        (fun k => residue_abs_le 3 k (by norm_num))
        (residue_period_of_dvd (show 3 ∣ 3 from dvd_refl 3))
        (residue_period_of_dvd (show 3 ∣ 3 from dvd_refl 3))]
    norm_num [Fin.sum_univ_succ, residue]
    ring
  rw [progressionWeight_eq_digamma 3 1 (by norm_num) (by norm_num) (by norm_num),
    progressionWeight_eq_digamma 3 2 (by norm_num) (by norm_num) (by norm_num)] at hg
  norm_num [Complex.digamma_one] at hg
  linear_combination hg - 2 * re_digamma_thirds_sum / 27 -
    re_digamma_thirds_difference / 27

end RiemannResearch.RH.Pareto
