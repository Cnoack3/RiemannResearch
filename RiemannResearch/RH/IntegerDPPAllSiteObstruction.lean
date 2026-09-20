import RiemannResearch.RH.IntegerDPPMellinObstruction
import RiemannResearch.RH.IntegerDPPKernel
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# A common Mellin zero forces holes at every arithmetic site

Source: user-provided DPP discussion, 2026-09-20, and its explicit all-site
Mellin obstruction. Here the natural index n denotes physical site n+1.
All projections and all Mellin integrals below are the actual arithmetic
objects. Probability interpretations require the separately constructed
DPP marginals; no existence or coupling is assumed for these operator
statements. Site saturation implies actual Mathlib RH. The reverse
implication from RH to residue density is not asserted by this module.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

private theorem scaled_dilation_one_mellin (m : ℕ) (hm : 0 < m)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (((m : ℝ)⁻¹) • hilbertDilation m hm hilbertOne) s =
      (m : ℂ) ^ (-s) / s := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [paretoMellin_smul, paretoMellin_dilation, paretoMellin_one s hs]
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    show (1 : ℂ) - s = 1 + (-s) by ring,
    Complex.cpow_add 1 (-s) hmC, Complex.cpow_one]
  field_simp

/-- The exact transform of each physical point, with no zeta assumption. -/
theorem point_mellin (n : ℕ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (paretoPointHilbert n) s =
      ((((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))) / s := by
  rw [paretoPoint_eq_scaled_dilation_difference]
  change paretoMellinContinuous s hs (_ - _) = _
  rw [map_sub]
  change paretoMellin _ s - paretoMellin _ s = _
  rw [scaled_dilation_one_mellin (n + 1) (by omega) s hs,
    scaled_dilation_one_mellin (n + 2) (by omega) s hs]
  ring

theorem point_mellin_ne_zero (n : ℕ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (paretoPointHilbert n) s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have ha : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hb : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hab : ((n + 1 : ℕ) : ℝ) < ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 < n + 2 by omega)
  have hpow : (((n + 2 : ℕ) : ℝ)) ^ (-s.re) <
      (((n + 1 : ℕ) : ℝ)) ^ (-s.re) := by
    rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos ha]
    exact Real.exp_lt_exp.mpr
      (mul_lt_mul_of_neg_right (Real.log_lt_log ha hab) (by linarith))
  have hnorm : ‖(((n + 2 : ℕ) : ℂ)) ^ (-s)‖ <
      ‖(((n + 1 : ℕ) : ℂ)) ^ (-s)‖ := by
    have hna := Complex.norm_cpow_eq_rpow_re_of_pos ha (-s)
    have hnb := Complex.norm_cpow_eq_rpow_re_of_pos hb (-s)
    simp only [Complex.ofReal_natCast, Complex.neg_re] at hna hnb
    rw [hna, hnb]
    exact hpow
  rw [point_mellin n s hs]
  apply div_ne_zero _ hs0
  intro he
  have h := congrArg norm (sub_eq_zero.mp he)
  exact (ne_of_lt hnorm) h.symm

def siteMellinVacancyFloor (n : ℕ) (s : ℂ) : ℝ :=
  (2 * s.re - 1) * ‖paretoMellin (paretoPointHilbert n) s‖ ^ 2 / paretoWeight n

theorem siteMellinVacancyFloor_pos (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) : 0 < siteMellinVacancyFloor n s := by
  exact div_pos
    (mul_pos (by linarith)
      (sq_pos_of_pos (norm_pos_iff.mpr (point_mellin_ne_zero n s hs))))
    (paretoWeight_pos n)

theorem siteMellinVacancyFloor_eq (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    siteMellinVacancyFloor n s =
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) * (2 * s.re - 1) *
        ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))‖ ^ 2 /
          ‖s‖ ^ 2 := by
  rw [siteMellinVacancyFloor, point_mellin n s hs, norm_div, div_pow, paretoWeight]
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  ring

/-- Normalization at every site; valid for any closed projected subspace. -/
theorem site_projection_complement (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] (n : ℕ) :
    paretoWeight n * (1 - inner ℝ (S.starProjection (countingBasis n))
      (S.starProjection (countingBasis n))) =
      ‖paretoPointHilbert n - S.starProjection (paretoPointHilbert n)‖ ^ 2 := by
  have henergy : (1 : ℝ) =
      ‖countingBasis n - S.starProjection (countingBasis n)‖ ^ 2 +
      ‖S.starProjection (countingBasis n)‖ ^ 2 := by
    have ht := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
      S bot_le (countingBasis n)
    simpa [countingBasis_norm_sq] using ht
  have hscale :
      ‖paretoPointHilbert n - S.starProjection (paretoPointHilbert n)‖ ^ 2 =
      paretoWeight n *
        ‖countingBasis n - S.starProjection (countingBasis n)‖ ^ 2 := by
    rw [paretoPoint_eq_sqrt_smul_countingBasis, map_smul, ← smul_sub,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (paretoWeight_pos n).le]
  rw [real_inner_self_eq_norm_sq, hscale]
  congr 1
  linarith

theorem siteMellinVacancyFloor_le_projection_complement
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (n : ℕ)
    (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection]
    (hS : S ≤ closedSpace) :
    siteMellinVacancyFloor n s ≤
      1 - inner ℝ (S.starProjection (countingBasis n))
        (S.starProjection (countingBasis n)) := by
  have h := closedSpace_mellin_distance_sq_lower_bound s hs hs1 hz
    (paretoPointHilbert n) (S.starProjection (paretoPointHilbert n))
    (hS (S.starProjection_apply_mem _))
  rw [← site_projection_complement S n] at h
  unfold siteMellinVacancyFloor
  apply (div_le_iff₀ (paretoWeight_pos n)).mpr
  nlinarith

theorem siteMellinVacancyFloor_le_limitingKernel_complement
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (n : ℕ) :
    siteMellinVacancyFloor n s ≤ 1 - limitingKernel n n := by
  exact siteMellinVacancyFloor_le_projection_complement s hs hs1 hz n closedSpace le_rfl

theorem siteMellinVacancyFloor_le_integerKernel_complement
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (n N : ℕ) :
    siteMellinVacancyFloor n s ≤ 1 - integerKernel N n n := by
  apply siteMellinVacancyFloor_le_projection_complement s hs hs1 hz n (finiteSpace N)
  exact (walkSpan_le residueAtom id N).trans (Submodule.le_topologicalClosure _)

/-- Saturating any chosen physical site would prove actual RH. -/
theorem riemannHypothesis_of_limitingKernel_site_one (n : ℕ)
    (h : limitingKernel n n = 1) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs h1 hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  have hf := siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz n
  rw [h, sub_self] at hf
  exact (not_le_of_gt (siteMellinVacancyFloor_pos n s hs)) hf

theorem riemannHypothesis_of_site_vacancy_tendsto_zero (n : ℕ)
    (h : Tendsto (fun N => 1 - integerKernel N n n) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have ht : Tendsto (fun N => 1 - integerKernel N n n) atTop
      (𝓝 (1 - limitingKernel n n)) :=
    tendsto_const_nhds.sub (integerKernel_tendsto n n)
  have he := tendsto_nhds_unique ht h
  apply riemannHypothesis_of_limitingKernel_site_one n
  linarith

/-- One hypothetical off-line zero supplies simultaneous, strictly positive
floors at every site and every finite stage. -/
theorem exists_common_site_vacancy_floor_of_not_RH (h : ¬ RiemannHypothesis) :
    ∃ s : ℂ, ((1 / 2 : ℝ) < s.re ∧ s.re < 1 ∧ riemannZeta s = 0) ∧
      ∀ n : ℕ, 0 < siteMellinVacancyFloor n s ∧
        siteMellinVacancyFloor n s ≤ 1 - limitingKernel n n ∧
        ∀ N : ℕ, siteMellinVacancyFloor n s ≤ 1 - integerKernel N n n := by
  have hz : ¬ (∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 → riemannZeta s ≠ 0) := by
    intro hf
    exact h (RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr hf)
  push Not at hz
  obtain ⟨s, hs, h1, hz⟩ := hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  refine ⟨s, ⟨hs, h1, hz⟩, fun n => ?_⟩
  exact ⟨siteMellinVacancyFloor_pos n s hs,
    siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz n,
    siteMellinVacancyFloor_le_integerKernel_complement s hs hs1 hz n⟩

end RiemannResearch.RH.Pareto.IntegerDPP
