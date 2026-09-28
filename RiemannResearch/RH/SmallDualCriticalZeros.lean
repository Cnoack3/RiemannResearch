import RiemannResearch.RH.ProjectedDualMellinWitness
import RiemannResearch.RH.CriticalLineZeros
import RiemannResearch.RH.ArithmeticConductorCommonZeros

/-!
# Common critical Mellin witnesses for columns two and three

Source: elementary algebra derived from the explicit Mellin formulas in
ProjectedDualMellinWitness. Wolfram was used to check the polynomial elimination;
the identities and deductions below are proved in Lean.

Each small dual has at most one conjugate pair of Mellin zeros on the critical
line. The imported arbitrarily high critical zeros therefore give a nonzero
Mellin witnesses for each column and common witnesses for both, above any
height. The provider provenance is in `RH/WeilExplicitFormula/PROVENANCE.md`.
No assertion about off-line zeta
zeros is made.
-/

noncomputable section



open scoped ComplexConjugate

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

private theorem two_numerator_re {x y : ℂ}
    (hx : Complex.normSq x = 1 / 2) (hy : Complex.normSq y = 1 / 3)
    (h : 4 - 10*x + 6*y = 0) : x.re = 27 / 40 := by
  have he : 6*y = 10*x-4 := by linear_combination h
  have hn := congrArg Complex.normSq he
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im] at hn hx hy
  norm_num at hn
  nlinarith

private theorem three_numerator_re {x y : ℂ}
    (hx : Complex.normSq x = 1 / 2) (hy : Complex.normSq y = 1 / 3)
    (h : 2 + 4*x - 18*y + 12*x^2 = 0) :
    24*x.re^2+16*x.re-21=0 ∧ 0 < x.re := by
  have he : 2+4*x+12*x^2 = 18*y := by linear_combination h
  have hn := congrArg Complex.normSq he
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, pow_two] at hn hx hy
  norm_num at hn
  have hp : 24*x.re^2+16*x.re-21=0 := by
    linear_combination (1/4:ℝ)*hn + 81*hy -
      (36*x.re^2+36*x.im^2+24*x.re+10)*hx
  refine ⟨hp, ?_⟩
  nlinarith [sq_nonneg x.im]

private theorem complex_eq_or_conj_of_re_normSq {x y : ℂ}
    (hr : x.re = y.re) (hn : Complex.normSq x = Complex.normSq y) :
    x = y ∨ x = conj y := by
  have hi : (x.im-y.im)*(x.im+y.im)=0 := by
    simp only [Complex.normSq_apply] at hn
    rw [hr] at hn
    nlinarith
  rcases mul_eq_zero.mp hi with hi | hi
  · left
    exact Complex.ext hr (sub_eq_zero.mp hi)
  · right
    apply Complex.ext
    · simpa using hr
    · simp only [Complex.conj_im]
      linarith

private theorem critical_cpow_normSq {s : ℂ} (hs : s.re=1/2)
    (m : ℝ) (hm : 0<m) : Complex.normSq ((m:ℂ)^(-s)) = m⁻¹ := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_cpow_eq_rpow_re_of_pos hm]
  simp only [Complex.neg_re, hs]
  rw [← Real.rpow_mul_natCast hm.le]
  norm_num [Real.rpow_neg_one]

private theorem cpow_conj_pos (m : ℝ) (hm : 0<m) (s : ℂ) :
    (m:ℂ)^(-conj s) = conj ((m:ℂ)^(-s)) := by
  have ha : Complex.arg (m:ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hm.le]
    exact Real.pi_pos.ne
  simpa only [map_neg, Complex.conj_ofReal] using
    Complex.cpow_conj (m:ℂ) (-s) ha

private theorem critical_cpow_parameter_eq_or_conj (s t : ℂ)
    (hs : s.re = 1/2) (ht : t.re = 1/2)
    (hr : ((2:ℂ)^(-s)).re = ((2:ℂ)^(-t)).re)
    (heq : (2:ℂ)^(-s) = (2:ℂ)^(-t) → (3:ℂ)^(-s) = (3:ℂ)^(-t))
    (hconj : (2:ℂ)^(-s) = conj ((2:ℂ)^(-t)) →
      (3:ℂ)^(-s) = conj ((3:ℂ)^(-t))) :
    s = t ∨ s = conj t := by
  have hn : Complex.normSq ((2:ℂ)^(-s)) = Complex.normSq ((2:ℂ)^(-t)) := by
    calc
      _ = (2:ℝ)⁻¹ := by simpa using critical_cpow_normSq hs 2 (by norm_num)
      _ = _ := by simpa using (critical_cpow_normSq ht 2 (by norm_num)).symm
  rcases complex_eq_or_conj_of_re_normSq hr hn with hx | hx
  · left
    exact ArithmeticConductorCommonZeros.two_three_cpow_neg_injective
      (Prod.ext hx (heq hx))
  · right
    apply ArithmeticConductorCommonZeros.two_three_cpow_neg_injective
    apply Prod.ext
    · change (2:ℂ)^(-s) = (2:ℂ)^(-conj t)
      have hc2 : (2:ℂ)^(-conj t) = conj ((2:ℂ)^(-t)) := by
        simpa using cpow_conj_pos 2 (by norm_num) t
      exact hx.trans hc2.symm
    · change (3:ℂ)^(-s) = (3:ℂ)^(-conj t)
      have hc3 : (3:ℂ)^(-conj t) = conj ((3:ℂ)^(-t)) := by
        simpa using cpow_conj_pos 3 (by norm_num) t
      exact (hconj hx).trans hc3.symm

private theorem critical_two_mellin_zeros_eq_or_conj (s t : ℂ)
    (hs : s.re=1/2) (ht : t.re=1/2)
    (hzs : paretoMellin (coefficientRiesz 2) s=0)
    (hzt : paretoMellin (coefficientRiesz 2) t=0) :
    s=t ∨ s=conj t := by
  have hspos : 0<s.re := by rw [hs]; norm_num
  have htpos : 0<t.re := by rw [ht]; norm_num
  have hps : 4-10*(2:ℂ)^(-s)+6*(3:ℂ)^(-s)=0 := by
    have h := coefficientRiesz_two_mellin s hspos
    rw [hzs, mul_zero] at h
    exact h.symm
  have hpt : 4-10*(2:ℂ)^(-t)+6*(3:ℂ)^(-t)=0 := by
    have h := coefficientRiesz_two_mellin t htpos
    rw [hzt, mul_zero] at h
    exact h.symm
  have hxs : Complex.normSq ((2:ℂ)^(-s)) = 1/2 := by
    convert critical_cpow_normSq hs 2 (by norm_num) using 1 <;> norm_num
  have hys : Complex.normSq ((3:ℂ)^(-s)) = 1/3 := by
    convert critical_cpow_normSq hs 3 (by norm_num) using 1 <;> norm_num
  have hxt : Complex.normSq ((2:ℂ)^(-t)) = 1/2 := by
    convert critical_cpow_normSq ht 2 (by norm_num) using 1 <;> norm_num
  have hyt : Complex.normSq ((3:ℂ)^(-t)) = 1/3 := by
    convert critical_cpow_normSq ht 3 (by norm_num) using 1 <;> norm_num
  apply critical_cpow_parameter_eq_or_conj s t hs ht
    ((two_numerator_re hxs hys hps).trans (two_numerator_re hxt hyt hpt).symm)
  · intro hx
    rw [hx] at hps
    linear_combination (1/6:ℂ)*hps - (1/6:ℂ)*hpt
  · intro hx
    have hptc := congrArg (conj : ℂ → ℂ) hpt
    simp only [map_add, map_sub, map_mul, map_ofNat, map_zero] at hptc
    rw [hx] at hps
    linear_combination (1/6:ℂ)*hps - (1/6:ℂ)*hptc

private theorem critical_three_mellin_zeros_eq_or_conj (s t : ℂ)
    (hs : s.re=1/2) (ht : t.re=1/2)
    (hzs : paretoMellin (coefficientRiesz 3) s=0)
    (hzt : paretoMellin (coefficientRiesz 3) t=0) :
    s=t ∨ s=conj t := by
  have hfour (u : ℂ) : (4:ℂ)^(-u) = ((2:ℂ)^(-u))^2 := by
    convert Complex.mul_cpow_ofReal_nonneg (a:=2) (b:=2)
      (by norm_num) (by norm_num) (-u) using 1 <;> norm_num [pow_two]
  have hspos : 0<s.re := by rw [hs]; norm_num
  have htpos : 0<t.re := by rw [ht]; norm_num
  have hps : 2+4*(2:ℂ)^(-s)-18*(3:ℂ)^(-s)+12*((2:ℂ)^(-s))^2=0 := by
    have h := coefficientRiesz_three_mellin s hspos
    rw [hzs, mul_zero, hfour] at h
    exact h.symm
  have hpt : 2+4*(2:ℂ)^(-t)-18*(3:ℂ)^(-t)+12*((2:ℂ)^(-t))^2=0 := by
    have h := coefficientRiesz_three_mellin t htpos
    rw [hzt, mul_zero, hfour] at h
    exact h.symm
  have hxs : Complex.normSq ((2:ℂ)^(-s)) = 1/2 := by
    convert critical_cpow_normSq hs 2 (by norm_num) using 1 <;> norm_num
  have hys : Complex.normSq ((3:ℂ)^(-s)) = 1/3 := by
    convert critical_cpow_normSq hs 3 (by norm_num) using 1 <;> norm_num
  have hxt : Complex.normSq ((2:ℂ)^(-t)) = 1/2 := by
    convert critical_cpow_normSq ht 2 (by norm_num) using 1 <;> norm_num
  have hyt : Complex.normSq ((3:ℂ)^(-t)) = 1/3 := by
    convert critical_cpow_normSq ht 3 (by norm_num) using 1 <;> norm_num
  obtain ⟨hpolyS, hposS⟩ := three_numerator_re hxs hys hps
  obtain ⟨hpolyT, hposT⟩ := three_numerator_re hxt hyt hpt
  have hr : ((2:ℂ)^(-s)).re = ((2:ℂ)^(-t)).re := by
    have hf : (((2:ℂ)^(-s)).re - ((2:ℂ)^(-t)).re) *
        (24*(((2:ℂ)^(-s)).re + ((2:ℂ)^(-t)).re)+16)=0 := by
      nlinarith only [hpolyS, hpolyT]
    rcases mul_eq_zero.mp hf with h | h
    · exact sub_eq_zero.mp h
    · nlinarith only [h, hposS, hposT]
  apply critical_cpow_parameter_eq_or_conj s t hs ht hr
  · intro hx
    rw [hx] at hps
    linear_combination -(1/18:ℂ)*hps + (1/18:ℂ)*hpt
  · intro hx
    have hptc := congrArg (conj : ℂ → ℂ) hpt
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero] at hptc
    rw [hx] at hps
    linear_combination -(1/18:ℂ)*hps + (1/18:ℂ)*hptc

/-- For each of the two small duals, all critical-line Mellin zeros form
at most one conjugate pair. -/
theorem coefficientRiesz_small_critical_mellin_zeros_eq_or_conj
    {d : ℕ} (hd : d=2 ∨ d=3) (s t : ℂ)
    (hs : s.re=1/2) (ht : t.re=1/2)
    (hzs : paretoMellin (coefficientRiesz d) s=0)
    (hzt : paretoMellin (coefficientRiesz d) t=0) :
    s=t ∨ s=conj t := by
  rcases hd with rfl | rfl
  · exact critical_two_mellin_zeros_eq_or_conj s t hs ht hzs hzt
  · exact critical_three_mellin_zeros_eq_or_conj s t hs ht hzs hzt

/-- Every one of columns two and three has a nonvanishing Mellin witness
among the actual critical zeta zeros, above any requested height. -/
theorem exists_small_dual_critical_mellin_witness_above
    {d : ℕ} (hd : d=2 ∨ d=3) (H : ℝ) :
    ∃ s : ℂ, riemannZeta s=0 ∧ s.re=1/2 ∧ H<s.im ∧
      Zeta23.zeroMult s = 1 ∧ paretoMellin (coefficientRiesz d) s ≠ 0 := by
  obtain ⟨s, hzs, hs, hHs, hsimple⟩ :=
    RiemannResearch.RH.exists_simple_critical_zero_above (max H 0)
  have hsH : H<s.im := (le_max_left H 0).trans_lt hHs
  have hspos : 0<s.im := (le_max_right H 0).trans_lt hHs
  by_cases hms : paretoMellin (coefficientRiesz d) s=0
  · obtain ⟨t, hzt, ht, hst, htsimple⟩ :=
      RiemannResearch.RH.exists_simple_critical_zero_above s.im
    refine ⟨t, hzt, ht, hsH.trans hst, htsimple, ?_⟩
    intro hmt
    rcases coefficientRiesz_small_critical_mellin_zeros_eq_or_conj
        hd s t hs ht hms hmt with he | he
    · rw [he] at hst
      exact lt_irrefl _ hst
    · have him := congrArg Complex.im he
      simp only [Complex.conj_im] at him
      linarith
  · exact ⟨s, hzs, hs, hsH, hsimple, hms⟩

/-- One arbitrarily high simple critical zero simultaneously detects both
small coefficient duals. -/
theorem exists_common_small_dual_critical_mellin_witness_above (H : ℝ) :
    ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = 1/2 ∧ H < s.im ∧
      Zeta23.zeroMult s = 1 ∧ paretoMellin (coefficientRiesz 2) s ≠ 0 ∧
        paretoMellin (coefficientRiesz 3) s ≠ 0 := by
  obtain ⟨s, hz, hs, hH, hsimple, h2⟩ :=
    exists_small_dual_critical_mellin_witness_above (d := 2) (Or.inl rfl) (max H 0)
  have hspos : 0 < s.im := (le_max_right H 0).trans_lt hH
  have hsH : H < s.im := (le_max_left H 0).trans_lt hH
  by_cases h3 : paretoMellin (coefficientRiesz 3) s = 0
  · obtain ⟨t, hzt, ht, hst, htsimple, ht2⟩ :=
      exists_small_dual_critical_mellin_witness_above (d := 2) (Or.inl rfl) s.im
    refine ⟨t, hzt, ht, hsH.trans hst, htsimple, ht2, ?_⟩
    intro ht3
    rcases coefficientRiesz_small_critical_mellin_zeros_eq_or_conj
      (Or.inr rfl) s t hs ht h3 ht3 with he | he
    · rw [he] at hst
      exact lt_irrefl _ hst
    · have him := congrArg Complex.im he
      simp only [Complex.conj_im] at him
      linarith
  · exact ⟨s, hz, hs, hsH, hsimple, h2, h3⟩

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
