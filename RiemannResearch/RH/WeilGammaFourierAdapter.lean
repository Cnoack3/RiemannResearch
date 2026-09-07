import RiemannResearch.RH.GammaLaplaceInversion
import RiemannResearch.Analysis.EvenIntegralHalfLine
import RiemannResearch.RH.WeilGammaLimits
import RiemannResearch.RH.DigammaQuarter
import RiemannResearch.RH.WeilEnergyNormalization

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual frequency-to-space gamma adapter

The finite rational increments are transported by the proved Fourier inversion
theorem. The two dominated-convergence theorems then identify the actual
digamma integral with the spatial Weil gamma displacement integral.
Only the real part of the test is required to be even, as for an actual
complex autocorrelation.
-/

open MeasureTheory Set Filter Complex
open scoped BigOperators Topology FourierTransform

namespace RiemannResearch.RH.SignedWeilCorrelation

open RiemannResearch.Analysis
open RiemannResearch.Analysis.GammaLaplaceKernel

noncomputable section

theorem re_integral_paperFT_mul_gammaIncrement_eq
    {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k) (hFk : Integrable (𝓕 k))
    (heven : ∀ t, (k (-t)).re = (k t).re) {b : ℝ} (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r *
        ((1 / b - b / (b ^ 2 + (r / 2) ^ 2) : ℝ) : ℂ))).re =
      2 * (∫ t, Real.exp (-(2 * b) * t) * ((k 0).re - (k t).re)
        ∂positiveMeasure) := by
  have hweight : Integrable (fun u => k u * evenExponential (2 * b) u) := by
    apply hki.mul_bdd (c := 1) (by unfold evenExponential; fun_prop)
    apply ae_of_all
    intro u
    simp only [evenExponential, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [abs_nonneg u]
  have hrint := Complex.reCLM.integral_comp_comm hweight
  change (∫ u, (k u * evenExponential (2 * b) u).re) =
    (∫ u, k u * evenExponential (2 * b) u).re at hrint
  simp only [evenExponential, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hrint
  have hireal := Complex.reCLM.integrable_comp hweight
  change Integrable (fun u => (k u * evenExponential (2 * b) u).re) at hireal
  simp only [evenExponential, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hireal
  have hhalf := integral_eq_two_smul_Ioi_of_even
    (fun u => (k u).re * Real.exp (-(2 * b) * |u|)) hireal
    (fun u => by rw [heven, abs_neg])
  simp only [smul_eq_mul] at hhalf
  have hh : (∫ t in Ioi 0, (k t).re * Real.exp (-(2 * b) * |t|)) =
      ∫ t, Real.exp (-(2 * b) * t) * (k t).re ∂positiveMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_pos (show 0 < t from ht)]
    ring
  rw [hh] at hhalf
  have hiprod : Integrable (fun t => Real.exp (-(2 * b) * t) * (k t).re)
      positiveMeasure := by
    apply hireal.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_pos (show 0 < t from ht)]
    ring
  have hie : Integrable (fun t : ℝ => Real.exp (-(2 * b) * t)) positiveMeasure :=
    integrableOn_exp_mul_Ioi (by linarith : -(2 * b) < 0) 0
  have heint : (∫ t, Real.exp (-(2 * b) * t) ∂positiveMeasure) = 1 / (2 * b) := by
    have h := integral_exp_mul_Ioi (by linarith : -(2 * b) < 0) 0
    simpa using h
  have hdisp : (∫ t, Real.exp (-(2 * b) * t) * ((k 0).re - (k t).re)
        ∂positiveMeasure) =
      1 / (2 * b) * (k 0).re -
        ∫ t, Real.exp (-(2 * b) * t) * (k t).re ∂positiveMeasure := by
    simp_rw [mul_sub]
    rw [integral_sub (hie.mul_const _) hiprod, integral_mul_const, heint]
  have h := congrArg Complex.re (integral_paperFT_mul_gammaIncrement hk hki hFk hb)
  simp only [evenExponential] at h
  rw [Complex.sub_re, ← hrint, hhalf] at h
  have hcoef : ((1 / (b : ℂ)) * k 0).re = 1 / b * (k 0).re := by
    rw [show (1 / (b : ℂ)) = ((1 / b : ℝ) : ℂ) by
      simp only [Complex.ofReal_div, Complex.ofReal_one]]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hcoef] at h
  rw [hdisp]
  calc
    _ = 1 / b * (k 0).re -
      2 * (∫ t, Real.exp (-(2 * b) * t) * (k t).re ∂positiveMeasure) := h
    _ = _ := by field_simp [ne_of_gt hb]

theorem re_integral_paperFT_mul_digammaIncrement_partial_sum
    {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k) (hFk : Integrable (𝓕 k))
    (heven : ∀ t, (k (-t)).re = (k t).re)
    (K : ℝ) (hK : 0 ≤ K) (hLip : ∀ t, 0 < t → |(k t).re - (k 0).re| ≤ K * t)
    (N : ℕ) :
    ((1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r *
        ((∑ n ∈ Finset.range N, digammaIncrementTerm (1 / 4) (r / 2) n : ℝ) : ℂ))).re =
      2 * (∫ t, (∑ n ∈ Finset.range N, Real.exp (-(2 * (n : ℝ) + 1 / 2) * t)) *
        ((k 0).re - (k t).re) ∂positiveMeasure) := by
  have hfreq (n : ℕ) : Integrable (fun r : ℝ => Zeta23.paperFT k r *
      (digammaIncrementTerm (1 / 4) (r / 2) n : ℂ)) := by
    exact integrable_paperFT_mul_gammaIncrement hFk (by positivity : 0 < (n : ℝ) + 1 / 4)
  have hspatial (n : ℕ) : Integrable (fun t => Real.exp (-(2 * (n : ℝ) + 1 / 2) * t) *
      ((k 0).re - (k t).re)) positiveMeasure :=
    integrable_weilGammaKernel_summand_displacement (fun t => (k t).re)
      (Complex.continuous_re.comp hk) K hK hLip n
  have he : (fun r : ℝ => Zeta23.paperFT k r *
        ((∑ n ∈ Finset.range N, digammaIncrementTerm (1 / 4) (r / 2) n : ℝ) : ℂ)) =
      (fun r : ℝ => ∑ n ∈ Finset.range N, Zeta23.paperFT k r *
        (digammaIncrementTerm (1 / 4) (r / 2) n : ℂ)) := by
    funext r
    simp only [Complex.ofReal_sum, Finset.mul_sum]
  rw [he, integral_finset_sum _ (fun n _ => hfreq n), Finset.mul_sum]
  have hre : (∑ n ∈ Finset.range N, (1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r *
        (digammaIncrementTerm (1 / 4) (r / 2) n : ℂ))).re =
      ∑ n ∈ Finset.range N, ((1 / (2 * Real.pi) : ℂ) *
        (∫ r : ℝ, Zeta23.paperFT k r *
          (digammaIncrementTerm (1 / 4) (r / 2) n : ℂ))).re :=
    map_sum Complex.reAddGroupHom _ _
  rw [hre]
  have hterm (n : ℕ) : ((1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r *
        (digammaIncrementTerm (1 / 4) (r / 2) n : ℂ))).re =
      2 * (∫ t, Real.exp (-(2 * (n : ℝ) + 1 / 2) * t) *
        ((k 0).re - (k t).re) ∂positiveMeasure) := by
    have h := re_integral_paperFT_mul_gammaIncrement_eq hk hki hFk heven
      (by positivity : 0 < (n : ℝ) + 1 / 4)
    simpa only [digammaIncrementTerm,
      show 2 * ((n : ℝ) + 1 / 4) = 2 * (n : ℝ) + 1 / 2 by ring] using h
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← integral_finset_sum _ (fun n _ => hspatial n)]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  exact (Finset.sum_mul _ _ _).symm

/-- The actual frequency digamma increment is identified with the spatial
gamma displacement by the two proved dominated limits. -/
theorem re_integral_paperFT_mul_digammaIncrement_eq
    {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k) (hFk : Integrable (𝓕 k))
    (heven : ∀ t, (k (-t)).re = (k t).re)
    (hHc : Continuous (fun r : ℝ => Zeta23.paperFT k r))
    (A : ℝ) (hA : 0 ≤ A)
    (hdec : ∀ r : ℝ, ‖Zeta23.paperFT k r‖ ≤ A / (1 + r ^ 2))
    (K : ℝ) (hK : 0 ≤ K) (hLip : ∀ t, 0 < t → |(k t).re - (k 0).re| ≤ K * t) :
    ((1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r * (digammaIncrement r : ℂ))).re =
      2 * (∫ t, weilGammaKernel t * ((k 0).re - (k t).re) ∂positiveMeasure) := by
  have hi := integrable_norm_mul_digammaIncrement_of_decay
    (fun r : ℝ => Zeta23.paperFT k r) hHc
    (Zeta23.EF.integrable_paperFT_ofReal hFk) A hA hdec
  have hfreq := (tendsto_integral_digammaIncrement_partial_sums _ hHc hi).const_mul
    (1 / (2 * Real.pi) : ℂ)
  have hfreqR := Complex.continuous_re.tendsto _ |>.comp hfreq
  have hspatial := (tendsto_integral_weilGammaKernel_partial_sums
    (fun t => (k t).re) (Complex.continuous_re.comp hk) K hK hLip).const_mul 2
  have heq : (fun N : ℕ => ((1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r *
        ((∑ n ∈ Finset.range N, digammaIncrementTerm (1 / 4) (r / 2) n : ℝ) : ℂ))).re) =
      (fun N : ℕ => 2 * (∫ t,
        (∑ n ∈ Finset.range N, Real.exp (-(2 * (n : ℝ) + 1 / 2) * t)) *
          ((k 0).re - (k t).re) ∂positiveMeasure)) := by
    funext N
    exact re_integral_paperFT_mul_digammaIncrement_partial_sum hk hki hFk heven K hK hLip N
  change Tendsto (fun N : ℕ => ((1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r *
        ((∑ n ∈ Finset.range N, digammaIncrementTerm (1 / 4) (r / 2) n : ℝ) : ℂ))).re)
      atTop _ at hfreqR
  rw [heq] at hfreqR
  exact tendsto_nhds_unique hfreqR hspatial

/-- Full identification of the actual frequency digamma term with the
original spatial gamma integral, including the exact diagonal constant. -/
theorem re_integral_paperFT_gammaBracket_eq_regulated
    {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k) (hFk : Integrable (𝓕 k))
    (heven : ∀ t, (k (-t)).re = (k t).re)
    (hHc : Continuous (fun r : ℝ => Zeta23.paperFT k r))
    (A : ℝ) (hA : 0 ≤ A)
    (hdec : ∀ r : ℝ, ‖Zeta23.paperFT k r‖ ≤ A / (1 + r ^ 2))
    (K : ℝ) (hK : 0 ≤ K) (hLip : ∀ t, 0 < t → |(k t).re - (k 0).re| ≤ K * t) :
    ((1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ))).re =
      -(Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) * (k 0).re -
        2 * (∫ t, weilGammaKernel t * ((k t).re - weilRegulator t * (k 0).re)
          ∂positiveMeasure) := by
  let q : ℝ := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi
  have hbr (r : ℝ) : Zeta23.EF.gammaBracket r = digammaIncrement r + q := by
    have harg : (1 / 4 : ℂ) + Complex.I * (r : ℂ) / 2 =
        (1 / 4 : ℂ) + Complex.I * (r / 2 : ℝ) := by push_cast; ring
    unfold Zeta23.EF.gammaBracket digammaIncrement q
    rw [harg]
    ring
  have hHi := Zeta23.EF.integrable_paperFT_ofReal hFk
  have hI := integrable_mul_digammaIncrement_of_decay
    (fun r : ℝ => Zeta23.paperFT k r) hHc hHi A hA hdec
  have he : (fun r : ℝ => Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ)) =
      (fun r : ℝ => Zeta23.paperFT k r * (digammaIncrement r : ℂ) +
        Zeta23.paperFT k r * (q : ℂ)) := by
    funext r
    rw [hbr]
    push_cast
    ring
  have hz := Zeta23.EF.paper_inversion hk hki hFk 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hz
  have hsplit : (1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ)) =
      (1 / (2 * Real.pi) : ℂ) *
        (∫ r : ℝ, Zeta23.paperFT k r * (digammaIncrement r : ℂ)) + k 0 * (q : ℂ) := by
    rw [he, integral_add hI (hHi.mul_const _), Zeta23.EF.cintegral_mul_const]
    calc
      _ = (1 / (2 * Real.pi) : ℂ) *
          (∫ r : ℝ, Zeta23.paperFT k r * (digammaIncrement r : ℂ)) +
        ((1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r) * (q : ℂ) := by ring
      _ = _ := by rw [← hz]
  have hqre : (k 0 * (q : ℂ)).re = (k 0).re * q := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hsplit, Complex.add_re, hqre]
  rw [re_integral_paperFT_mul_digammaIncrement_eq hk hki hFk heven hHc A hA hdec K hK hLip]
  rw [integral_weilGammaKernel_regulated_eq_displacement (fun t => (k t).re)
    (Complex.continuous_re.comp hk) K hK hLip]
  have hlog : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt Real.pi_pos)]
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) (2 : ℕ)
      norm_num only [pow_two] at h
      exact h
    rw [hfour]
  dsimp only [q]
  rw [RiemannResearch.RH.re_digamma_one_quarter, hlog]
  ring

end
end RiemannResearch.RH.SignedWeilCorrelation
