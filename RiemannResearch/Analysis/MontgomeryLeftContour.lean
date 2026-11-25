import RiemannResearch.Analysis.ActualLandauLeftLine
import RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
import RiemannResearch.Analysis.VonMangoldtVerticalIntegral
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.StirlingVert
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Hardy.EFContour.Analytic

/-! # The logarithmic derivative in the positive-cutoff Montgomery formula

The left contour of Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Lemma 1
(<https://doi.org/10.4064/aa230612-20-3>), is Re(s) = −1/2. After one Gamma
recurrence the two digamma arguments are conjugate. Removing the exact
rational term leaves a real Stirling remainder of order t⁻². The reflected
zeta logarithmic derivative is bounded by an absolutely convergent series.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped BigOperators ArithmeticFunction Topology ComplexConjugate

namespace RiemannResearch.Analysis.MontgomeryLeftContour
open Zeta23.XiPrime Zeta23.XiPrime.Hardy MontgomeryPrimeCrossIntegral

/-- The point on the left contour of the positive-cutoff explicit formula. -/
def leftPoint (t : ℝ) : ℂ := -(1/2 : ℂ) + t * I

private theorem leftPoint_re (t : ℝ) : (leftPoint t).re = -(1/2 : ℝ) := by
  simp [leftPoint]

private theorem leftPoint_im (t : ℝ) : (leftPoint t).im = t := by simp [leftPoint]

private theorem leftPoint_reflected (t : ℝ) : 1-leftPoint t = (3/2 : ℂ) - t*I := by
  dsimp [leftPoint]
  ring

private theorem left_zeta_ne_zero (t : ℝ) : riemannZeta (leftPoint t) ≠ 0 := by
  let s := leftPoint t
  have hs : s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    change (leftPoint t).re = (0:ℂ).re at hr
    rw [leftPoint_re] at hr
    norm_num at hr
  have h1 : 1 < (1-s).re := by simp [s, leftPoint_re]
  have h1s : 1-s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1; norm_num at h1
  have hG := Zeta23.XiPrime.Hardy.EFContour.Gammaℝ_ne_zero_of_re
    (s := s) (by change -2 < (leftPoint t).re; rw [leftPoint_re]; norm_num) hs
  have hz := riemannZeta_ne_zero_of_one_lt_re h1
  rw [riemannZeta_def_of_ne_zero h1s] at hz
  have hΛ := (div_ne_zero_iff.mp hz).1
  rw [completedRiemannZeta_one_sub] at hΛ
  rw [riemannZeta_def_of_ne_zero hs]
  exact div_ne_zero hΛ hG

/-- At Re(s) = −1/2 the shifted Gamma arguments are exact conjugates. -/
theorem chi_left_reflected_digamma {t : ℝ} (ht : t ≠ 0) :
    logDeriv chiFE (leftPoint t) =
      ((Real.log Real.pi - (Complex.digamma (((3/4 : ℝ) : ℂ) + I * (t/2))).re : ℝ) : ℂ)
        + 1 / leftPoint t := by
  let s := leftPoint t
  let q : ℂ := (((3/4 : ℝ) : ℂ) + I * (t/2))
  have hs : s.im ≠ 0 := by rwa [show s.im = t by exact leftPoint_im t]
  have he₁ : (1-s)/2 = conj q := by
    dsimp only [q, s, leftPoint]
    simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have he₂ : (s+2)/2 = q := by dsimp [q, s, leftPoint]; push_cast; ring
  change logDeriv chiFE s = ((Real.log Real.pi - (Complex.digamma q).re : ℝ) : ℂ) + 1/s
  rw [logDeriv_chiFE hs, logDeriv_Gammaℝ_shift hs,
    Zeta23.WeilEF.logDeriv_Gammaℝ (s := 1-s) (by norm_num [s,leftPoint_re]),
    Zeta23.WeilEF.logDeriv_Gammaℝ (s := s+2) (by norm_num [s,leftPoint_re]),
    he₁, he₂, Zeta23.digamma_conj]
  apply Complex.ext <;> simp <;> ring

/-- The reflected prime term and exact rational term are retained. The remaining
error is real and bounded by 20/t² for t ≥ 1. -/
theorem left_zeta_signed_remainder {t : ℝ} (ht : 1 ≤ t) :
    ∃ r : ℝ, |r| ≤ 20/t^2 ∧
      -logDeriv riemannZeta (leftPoint t) =
        (Real.log (t/(2*Real.pi)) : ℂ) + logDeriv riemannZeta (1-leftPoint t)
          - 1 / leftPoint t + r := by
  have ht0 : 0 < t := by linarith
  let q : ℂ := (((3/4 : ℝ) : ℂ) + I * (t/2))
  let r := (Complex.digamma q).re - Real.log (t/2)
  refine ⟨r, ?_, ?_⟩
  · have h := Zeta23.StirlingVert.re_digamma_stirling' (a := 3/4) (t := t/2)
      (by norm_num) (by norm_num) (by rw [abs_of_pos (by positivity : 0 < t/2)]; linarith)
    rw [abs_of_pos (by positivity : 0 < t/2)] at h
    have he : 5/(t/2)^2 = 20/t^2 := by ring
    simpa only [r, q, Complex.ofReal_div, Complex.ofReal_ofNat, he] using h
  · rw [Zeta23.logDeriv_riemannZeta_functional (by simpa [leftPoint_im] using ht0.ne')
      (riemannZeta_ne_zero_of_one_lt_re (by simp [leftPoint_re])),
      chi_left_reflected_digamma ht0.ne']
    have hl : Real.log (t/(2*Real.pi)) = Real.log (t/2) - Real.log Real.pi := by
      rw [show t/(2*Real.pi) = (t/2)/Real.pi by ring, Real.log_div (by positivity) Real.pi_ne_zero]
    rw [hl]
    dsimp [r,q]
    push_cast
    ring

/-- The actual reflected zeta logarithmic derivative is uniformly bounded by
the absolutely convergent von Mangoldt series at 3/2. -/
theorem norm_reflected_logDeriv_le (t : ℝ) :
    ‖logDeriv riemannZeta (1-leftPoint t)‖ ≤ ∑' n : ℕ, mangoldtThreeHalves n := by
  let z := (((3/2 : ℝ) : ℂ) + (-t : ℝ)*I)
  have hz : z = 1-leftPoint t := by rw [leftPoint_reflected]; dsimp [z]; push_cast; ring
  have hsum := VonMangoldtVerticalIntegral.neg_logDeriv_eq_LSeries
    (σ := 3/2) (by norm_num) (-t)
  rw [← hz, ← norm_neg, hsum]
  have hsn : Summable (fun n => ‖LSeries.term (fun j => (Λ j : ℂ)) z n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num [z] : 1 < z.re))
  apply (norm_tsum_le_tsum_norm hsn).trans_eq
  apply tsum_congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases h : n = 0
  · simp [h,mangoldtThreeHalves]
  · simp [h,z,mangoldtThreeHalves,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- The actual centered left logarithmic derivative in the third signal. -/
def centeredLeft (t : ℝ) : ℂ := -logDeriv riemannZeta (leftPoint t) - (Real.log (t+2) : ℂ)

private theorem continuousOn_centeredLeft : ContinuousOn centeredLeft (Ici 0) := by
  intro t ht
  have hs : leftPoint t ≠ 1 := fun h => by
    have hr := congrArg Complex.re h; rw [leftPoint_re, Complex.one_re] at hr; norm_num at hr
  have hc := Zeta23.XiPrime.ZeroCount.continuousAt_logDeriv_of_analyticAt
    (_root_.analyticAt_riemannZeta hs) (left_zeta_ne_zero t)
  have hcp : Continuous leftPoint := by unfold leftPoint; fun_prop
  have hlog : ContinuousAt (fun v : ℝ => Real.log (v+2)) t :=
    ContinuousAt.comp (g := Real.log) (f := fun v : ℝ => v+2)
      (Real.continuousAt_log (by have ht0 : 0 ≤ t := ht; change t+2 ≠ 0; linarith))
      (by fun_prop)
  exact (((hc.comp hcp.continuousAt).neg).sub
    (Complex.continuous_ofReal.continuousAt.comp hlog)).continuousWithinAt

theorem exists_centeredLeft_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ‖centeredLeft t‖ ≤ C := by
  obtain ⟨a,ha,hm⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMaxOn
    ⟨0, by simp⟩ (continuousOn_centeredLeft.norm.mono (fun _ ht => ht.1))
  let K := (∑' n : ℕ, mangoldtThreeHalves n) + 23 + |Real.log Real.pi| + |Real.log 2|
  refine ⟨max ‖centeredLeft a‖ K, (norm_nonneg _).trans (le_max_left _ _), fun t ht => ?_⟩
  by_cases ht1 : t ≤ 1
  · exact (hm ⟨ht,ht1⟩).trans (le_max_left _ _)
  apply le_trans _ (le_max_right _ _)
  have ht' : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hs := Complex.abs_im_le_norm (leftPoint t)
  rw [leftPoint_im, abs_of_nonneg ht] at hs
  have hsi : ‖1/leftPoint t‖ ≤ 1 := by
    rw [norm_div,norm_one]
    exact (div_le_one (ht0.trans_le hs)).mpr (ht'.trans hs)
  obtain ⟨r,hr,he⟩ := left_zeta_signed_remainder ht'
  have hr1 : |r| ≤ 20 := hr.trans ((div_le_iff₀ (sq_pos_of_pos ht0)).mpr (by nlinarith [sq_nonneg (t-1)]))
  have hd : 0 ≤ Real.log (t+2) - Real.log t := by
    exact sub_nonneg.mpr (Real.log_le_log ht0 (by linarith))
  have hd' : Real.log (t+2) - Real.log t ≤ 2 := by
    rw [← Real.log_div (by linarith : t+2 ≠ 0) ht0.ne']
    apply (Real.log_le_sub_one_of_pos (by positivity)).trans
    have hrat : (t+2)/t ≤ 3 := (div_le_iff₀ ht0).mpr (by linarith)
    linarith
  have hcenter : centeredLeft t = logDeriv riemannZeta (1-leftPoint t) -
      1/leftPoint t + r - ((Real.log (t+2) - Real.log t : ℝ) : ℂ) -
      ((Real.log 2 + Real.log Real.pi : ℝ) : ℂ) := by
    dsimp only [centeredLeft]; rw [he, Real.log_div ht0.ne' (by positivity),
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero]; push_cast; ring
  rw [hcenter]
  have hab := norm_sub_le (logDeriv riemannZeta (1-leftPoint t)) (1/leftPoint t)
  have habc := norm_add_le (logDeriv riemannZeta (1-leftPoint t) - 1/leftPoint t) (r:ℂ)
  have habcd := norm_sub_le (logDeriv riemannZeta (1-leftPoint t) - 1/leftPoint t + r)
    ((Real.log (t+2)-Real.log t : ℝ) : ℂ)
  have habcde := norm_sub_le (logDeriv riemannZeta (1-leftPoint t) - 1/leftPoint t + r -
    ((Real.log (t+2)-Real.log t : ℝ) : ℂ)) ((Real.log 2 + Real.log Real.pi : ℝ) : ℂ)
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd] at habc habcd habcde
  dsimp [K]
  linarith only [hab,habc,habcd,habcde, norm_reflected_logDeriv_le t, hsi, hr1, hd',
    abs_add_le (Real.log 2) (Real.log Real.pi)]

/-- The full left-contour contribution to the third-signal energy is O(T/x²),
uniformly down to height zero and for every positive frequency cutoff. -/
theorem centeredLeft_mean_square_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T x : ℝ, 0 ≤ T → 0 < x →
      (∫ t in (0:ℝ)..T, ‖centeredLeft t / (x:ℂ)‖^2) ≤ C * T/x^2 := by
  obtain ⟨J,hJ,h⟩ := exists_centeredLeft_uniform_bound
  refine ⟨J^2,sq_nonneg _,fun T x hT hx => ?_⟩
  have hi : IntervalIntegrable (fun t => ‖centeredLeft t / (x:ℂ)‖^2) volume 0 T :=
    ((continuousOn_centeredLeft.div_const (x:ℂ)).norm.pow 2).mono
      (show uIcc 0 T ⊆ Ici 0 by rw [uIcc_of_le hT]; exact fun _ ht => ht.1) |>.intervalIntegrable
  have hb := intervalIntegral.integral_mono_on hT hi (intervalIntegrable_const (c := (J/x)^2))
    (fun t ht => by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (h t ht.1) hx.le) 2)
  rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul,div_pow] at hb
  exact hb.trans_eq (by ring)

end RiemannResearch.Analysis.MontgomeryLeftContour
