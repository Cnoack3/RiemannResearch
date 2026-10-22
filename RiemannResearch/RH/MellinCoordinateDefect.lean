import Mathlib.Tactic.GCongr
import RiemannResearch.RH.IntegerDPPAllSiteObstruction
import RiemannResearch.RH.MellinFrequencyMeasure
import RiemannResearch.RH.ParetoBoundedMellinLinearity

/-!
# Physical-coordinate Mellin cutoffs and their arithmetic defect

Source: ArithmeticProjectionDPPDraft20260921.md (2026-09-21), Sections
5--7. Natural coordinate n means physical site n+1. These are coordinate
cutoffs of the completed arithmetic projection, not arithmetic-rank cutoffs.
Real and imaginary parts implement the complexification of the existing
real Pareto Hilbert space. All signed mixed terms remain in the norm sums.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace RiemannResearch.RH.Pareto.CoordinateMellin
open CoefficientStabilization IntegerDPP MellinFrequency
open RiemannResearch.Analysis.ExhaustiveWalk

def cellTransform (n : ℕ) (s : ℂ) : ℂ :=
  ((((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))) / s

def coordinateFeature (n : ℕ) (t : ℝ) : ℂ :=
  cellTransform n (criticalPoint t) / (Real.sqrt (paretoWeight n) : ℂ)

theorem cellTransform_ne_zero (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    cellTransform n s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have ha : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hb : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hab : ((n + 1 : ℕ) : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show n + 1 < n + 2 by omega)
  have hpow : (((n + 2 : ℕ) : ℝ)) ^ (-s.re) < (((n + 1 : ℕ) : ℝ)) ^ (-s.re) := by
    rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos ha]
    exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_right (Real.log_lt_log ha hab) (neg_neg_of_pos hs))
  have hnorm : ‖(((n + 2 : ℕ) : ℂ)) ^ (-s)‖ < ‖(((n + 1 : ℕ) : ℂ)) ^ (-s)‖ := by
    have hna := Complex.norm_cpow_eq_rpow_re_of_pos ha (-s)
    have hnb := Complex.norm_cpow_eq_rpow_re_of_pos hb (-s)
    simp only [Complex.ofReal_natCast, Complex.neg_re] at hna hnb
    rw [hna, hnb]
    exact hpow
  apply div_ne_zero _ hs0
  intro he
  have h := congrArg norm (sub_eq_zero.mp he)
  exact (ne_of_lt hnorm) h.symm

theorem coordinateFeature_ne_zero (n : ℕ) (t : ℝ) : coordinateFeature n t ≠ 0 := by
  apply div_ne_zero (cellTransform_ne_zero n _ (by simp))
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (paretoWeight_pos n)).ne'

theorem coordinateFeature_continuous (n : ℕ) : Continuous (coordinateFeature n) := by
  have ha : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hb : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  unfold coordinateFeature cellTransform
  simp only [Complex.cpow_def, if_neg ha, if_neg hb]
  apply Continuous.div_const
  apply Continuous.div
  · unfold criticalPoint
    fun_prop
  · unfold criticalPoint
    fun_prop
  · exact criticalPoint_ne_zero

private theorem one_mellin_of_pos (s : ℂ) (hs : 0 < s.re) :
    paretoMellin hilbertOne s = 1 / s := by
  rw [paretoMellin_eq_step_integral]
  have he : (∫ x in Set.Ioi (1 : ℝ), (hilbertSequence hilbertOne ⌊x⌋₊ : ℂ) *
      (x : ℂ)^(-s-1)) = ∫ x in Set.Ioi (1 : ℝ), (x : ℂ)^(-s-1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    have hx' : (1 : ℝ) < x := hx
    have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)).2 (by simpa using hx'.le)
    rw [hilbertOne_sequence]
    simp [zeroAnchor, show ⌊x⌋₊ ≠ 0 by omega]
  have hexp : (-s-1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [he, integral_Ioi_cpow_of_lt hexp (by norm_num)]
  simp

private theorem scaledTail_sequence (m : ℕ) (hm : 0 < m) (k : ℕ) :
    hilbertSequence (((m : ℝ)⁻¹) • hilbertDilation m hm hilbertOne) k =
      if m ≤ k then 1 else 0 := by
  rw [hilbertSequence_smul, hilbertDilation_sequence, hilbertOne_sequence]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  by_cases hmk : m ≤ k
  · have hdiv : k / m ≠ 0 := Nat.ne_of_gt (Nat.div_pos hmk hm)
    simp [dilation, zeroAnchor, hmk, hdiv, hm0]
  · have hdiv : k / m = 0 := Nat.div_eq_of_lt (by omega)
    simp [dilation, zeroAnchor, hmk, hdiv]

private theorem scaledTail_mellin (m : ℕ) (hm : 0 < m)
    (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (((m : ℝ)⁻¹) • hilbertDilation m hm hilbertOne) s =
      (m : ℂ) ^ (-s) / s := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [paretoMellin_smul, paretoMellin_dilation, one_mellin_of_pos s hs]
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    show (1 : ℂ) - s = 1 + (-s) by ring,
    Complex.cpow_add 1 (-s) hmC, Complex.cpow_one]
  field_simp

private theorem mellin_sub_of_bounded (f g : ThresholdHilbert) {Cf Cg : ℝ}
    (hf : ∀ k, |hilbertSequence f k| ≤ Cf)
    (hg : ∀ k, |hilbertSequence g k| ≤ Cg) (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (f - g) s = paretoMellin f s - paretoMellin g s := by
  simp only [paretoMellin_eq_step_integral]
  have he : (fun x : ℝ => (hilbertSequence (f - g) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) = fun x : ℝ =>
        (hilbertSequence f ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) -
        (hilbertSequence g ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) := by
    funext x
    have h := congrFun (hilbertSequenceLinear.map_sub f g) ⌊x⌋₊
    change hilbertSequence (f - g) _ = hilbertSequence f _ - hilbertSequence g _ at h
    rw [h, Complex.ofReal_sub, sub_mul]
  rw [he]
  exact integral_sub (paretoMellin_step_integrable_of_bounded f hf s hs)
    (paretoMellin_step_integrable_of_bounded g hg s hs)

/-- The coordinate formula remains the actual convergent Mellin integral
on the critical line; no boundary-identification provider is needed. -/
theorem cellTransform_eq_point_mellin_of_pos (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    cellTransform n s = paretoMellin (paretoPointHilbert n) s := by
  have hb (m : ℕ) (hm : 0 < m) :
      ∀ k, |hilbertSequence (((m : ℝ)⁻¹) • hilbertDilation m hm hilbertOne) k| ≤ (1 : ℝ) := by
    intro k
    rw [scaledTail_sequence]
    split_ifs <;> norm_num
  rw [paretoPoint_eq_scaled_dilation_difference,
    mellin_sub_of_bounded _ _ (hb (n + 1) (by omega)) (hb (n + 2) (by omega)) s hs,
    scaledTail_mellin (n + 1) (by omega) s hs,
    scaledTail_mellin (n + 2) (by omega) s hs]
  unfold cellTransform
  ring

theorem coordinateFeature_eq_mellin (n : ℕ) (t : ℝ) :
    coordinateFeature n t = paretoMellin (countingBasis n) (criticalPoint t) := by
  have h := cellTransform_eq_point_mellin_of_pos n (criticalPoint t) (by simp)
  rw [paretoPoint_eq_sqrt_smul_countingBasis, paretoMellin_smul, Complex.real_smul] at h
  unfold coordinateFeature
  rw [h]
  exact mul_div_cancel_left₀ _
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (paretoWeight_pos n)).ne')

def defect : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ContinuousLinearMap.id ℝ ThresholdHilbert - closedSpace.starProjection

def headReal (M : ℕ) (t : ℝ) : ThresholdHilbert :=
  ∑ n ∈ Finset.range M, (coordinateFeature n t).re • countingBasis n

def headImag (M : ℕ) (t : ℝ) : ThresholdHilbert :=
  ∑ n ∈ Finset.range M, (coordinateFeature n t).im • countingBasis n

def ambientIntensity (M : ℕ) (t : ℝ) : ℝ :=
  ‖headReal M t‖ ^ 2 + ‖headImag M t‖ ^ 2

def arithmeticIntensity (M : ℕ) (t : ℝ) : ℝ :=
  ‖closedSpace.starProjection (headReal M t)‖ ^ 2 +
    ‖closedSpace.starProjection (headImag M t)‖ ^ 2

def diagonalDefect (M : ℕ) (t : ℝ) : ℝ :=
  ‖defect (headReal M t)‖ ^ 2 + ‖defect (headImag M t)‖ ^ 2

theorem diagonalDefect_nonneg (M : ℕ) (t : ℝ) : 0 ≤ diagonalDefect M t := by
  unfold diagonalDefect
  positivity

theorem intensity_decomposition (M : ℕ) (t : ℝ) :
    ambientIntensity M t = arithmeticIntensity M t + diagonalDefect M t := by
  have hr := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
    closedSpace bot_le (headReal M t)
  have hi := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
    closedSpace bot_le (headImag M t)
  simp only [Submodule.starProjection_bot, zero_apply, sub_zero] at hr hi
  change ‖headReal M t‖ ^ 2 + ‖headImag M t‖ ^ 2 =
    (‖closedSpace.starProjection (headReal M t)‖ ^ 2 + ‖closedSpace.starProjection (headImag M t)‖ ^ 2) +
      (‖headReal M t - closedSpace.starProjection (headReal M t)‖ ^ 2 +
       ‖headImag M t - closedSpace.starProjection (headImag M t)‖ ^ 2)
  linarith

theorem diagonalDefect_eq_intensity_difference (M : ℕ) (t : ℝ) :
    diagonalDefect M t = ambientIntensity M t - arithmeticIntensity M t := by
  linarith [intensity_decomposition M t]

theorem diagonalDefect_continuous (M : ℕ) : Continuous (diagonalDefect M) := by
  have hr : Continuous (headReal M) := by
    unfold headReal
    exact continuous_finsetSum _ fun n _ => (Complex.continuous_re.comp (coordinateFeature_continuous n)).smul continuous_const
  have hi : Continuous (headImag M) := by
    unfold headImag
    exact continuous_finsetSum _ fun n _ => (Complex.continuous_im.comp (coordinateFeature_continuous n)).smul continuous_const
  exact (((defect.continuous.comp hr).norm).pow 2).add
    (((defect.continuous.comp hi).norm).pow 2)

theorem defect_eq_zero_of_top (h : closedSpace = ⊤) (v : ThresholdHilbert) :
    defect v = 0 := by
  change v - closedSpace.starProjection v = 0
  rw [Submodule.starProjection_eq_self_iff.mpr (by rw [h]; trivial), sub_self]

theorem diagonalDefect_zero_of_top (h : closedSpace = ⊤) (M : ℕ) (t : ℝ) :
    diagonalDefect M t = 0 := by simp [diagonalDefect, defect_eq_zero_of_top h]

theorem defect_countingBasis_zero_norm_sq : ‖defect (countingBasis 0)‖ ^ 2 = limitingVacancy := by
  have h := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
    closedSpace bot_le (countingBasis 0)
  simp only [Submodule.starProjection_bot, zero_apply, sub_zero,
    countingBasis_norm_sq] at h
  rw [limitingVacancy_eq_kernel_complement, limitingKernel, real_inner_self_eq_norm_sq]
  change ‖countingBasis 0 - closedSpace.starProjection (countingBasis 0)‖ ^ 2 = _
  linarith

theorem diagonalDefect_one (t : ℝ) :
    diagonalDefect 1 t = limitingVacancy * ‖coordinateFeature 0 t‖ ^ 2 := by
  simp only [diagonalDefect, headReal, headImag, Finset.range_one, Finset.sum_singleton,
    map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    defect_countingBasis_zero_norm_sq]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The extended nonnegative unscaled frequency-window deficit. -/
def windowDeficit (M : ℕ) (I : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in I, ENNReal.ofReal (diagonalDefect M t) ∂frequencyMeasure

def firstModeMass (I : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in I, ENNReal.ofReal (‖coordinateFeature 0 t‖ ^ 2) ∂frequencyMeasure

theorem windowDeficit_one (I : Set ℝ) :
    windowDeficit 1 I = ENNReal.ofReal limitingVacancy * firstModeMass I := by
  unfold windowDeficit firstModeMass
  simp_rw [diagonalDefect_one, ENNReal.ofReal_mul limitingVacancy_nonneg]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem firstModeMass_pos (I : Set ℝ) (hI : 0 < frequencyMeasure I) :
    0 < firstModeMass I := by
  have hm : Measurable (fun t => ENNReal.ofReal (‖coordinateFeature 0 t‖ ^ 2)) :=
    ((coordinateFeature_continuous 0).norm.pow 2).measurable.ennreal_ofReal
  have hs : Function.support (fun t => ENNReal.ofReal (‖coordinateFeature 0 t‖ ^ 2)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr (coordinateFeature_ne_zero 0 t)))).ne'
  unfold firstModeMass
  rw [lintegral_pos_iff_support hm, hs]
  simpa using hI

theorem windowDeficit_zero_of_top (h : closedSpace = ⊤) (M : ℕ) (I : Set ℝ) :
    windowDeficit M I = 0 := by simp [windowDeficit, diagonalDefect_zero_of_top h]

theorem first_window_zero_iff_density (I : Set ℝ) (hI : 0 < frequencyMeasure I) :
    windowDeficit 1 I = 0 ↔ closedSpace = ⊤ := by
  constructor
  · intro h
    rw [windowDeficit_one] at h
    have hz : ENNReal.ofReal limitingVacancy = 0 :=
      (mul_eq_zero.mp h).resolve_right (firstModeMass_pos I hI).ne'
    exact limitingVacancy_zero_iff_top.mp
      (le_antisymm (ENNReal.ofReal_eq_zero.mp hz) limitingVacancy_nonneg)
  · intro h
    exact windowDeficit_zero_of_top h 1 I

/-- This implication to actual Mathlib RH has no analytic profile provider. -/
theorem riemannHypothesis_of_first_window_zero (I : Set ℝ)
    (hI : 0 < frequencyMeasure I) (h : windowDeficit 1 I = 0) : RiemannHypothesis := by
  apply riemannHypothesis_of_vacancy_tendsto_zero
  exact vacancy_tendsto_zero_iff_top.mpr ((first_window_zero_iff_density I hI).mp h)

/-- An off-critical zero imposes a quantitative positive lower bound on every
first-coordinate Mellin window. No zero-profile provider is assumed. -/
theorem first_window_deficit_ge_zero_floor
    (I : Set ℝ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ENNReal.ofReal (siteMellinVacancyFloor 0 s) * firstModeMass I ≤
      windowDeficit 1 I := by
  rw [windowDeficit_one]
  gcongr
  rw [limitingVacancy_eq_kernel_complement]
  exact siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz 0

end RiemannResearch.RH.Pareto.CoordinateMellin
