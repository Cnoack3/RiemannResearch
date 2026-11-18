/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomerySharpPolynomialCriterion
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.MarkedIntegralCauchy
import RiemannResearch.Analysis.CrossCorrelationRegularity
import RiemannResearch.Analysis.SuperexponentialLaplace
import RiemannResearch.RH.WeilSingleZeroTest
import RiemannResearch.RH.WeilSpectralPairing
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring

/-! # A Weil separator for the complex Montgomery energy

The complex form factor is the one studied by Baluyot, Goldston, Suriajaya
and Turnage-Butterbaugh, https://doi.org/10.4064/aa230612-20-3. The
preexisting actual-zero Weil test gives a cutoff-independent separator.
-/

noncomputable section

open MeasureTheory MeasureTheory.BilateralLaplace Zeta23
open RiemannResearch.RH.WeilExplicitFormula RiemannResearch.RH.SignedWeilCorrelation
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryHorizontalTransfer

open ActualZeroOrdinate MontgomeryFormFactor

/-- The Weil test at `1 - ρ` isolates `ρ` in the weighted Landau signal. -/
theorem fixedRightZeroSharpSeparator : FixedRightZeroSharpSeparator := by
  classical
  intro H ρ hρ _
  obtain ⟨hzero, hpos, _⟩ := mem_cutoff.mp hρ
  let ρ' : zetaZeroConfig.carrier := ⟨ρ, hzero⟩
  obtain ⟨g, hg, htest, htest0⟩ :=
    exists_smooth_single_actual_zero_test (actualZeroOneSub ρ')
  let q : ℝ → ℂ := fun s => star ((Real.exp |s| : ℂ) * g s)
  have hqcont : Continuous q :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_abs)).mul
      hg.1.continuous).star
  have hqdecay : SuperexponentialDecay q := by
    intro a ha
    obtain ⟨C, hC, hCdecay⟩ := hg.decay (a + 1) (by linarith)
    refine ⟨C, hC, fun s => ?_⟩
    calc
      ‖q s‖ = Real.exp |s| * ‖g s‖ := by
        simp only [q, norm_star, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp |s| * (C * Real.exp (-(a + 1) * |s|)) :=
        mul_le_mul_of_nonneg_left (hCdecay s) (Real.exp_nonneg _)
      _ = C * Real.exp (-a * |s|) := by
        rw [show Real.exp |s| * (C * Real.exp (-(a + 1) * |s|)) =
          C * (Real.exp |s| * Real.exp (-(a + 1) * |s|)) by ring, ← Real.exp_add]
        congr 2
        ring
  have hq : MemLp q 2 (volume : Measure ℝ) := by
    apply (memLp_two_iff_integrable_sq_norm hqcont.aestronglyMeasurable).mpr
    have hi := (hqdecay.integrable_crossCorrelation hqdecay hqcont hqcont 0).norm
    simpa only [add_zero, norm_mul, norm_star, pow_two] using hi
  let ℓ : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ := innerSL ℂ (hq.toLp q)
  refine ⟨ℓ, (zeroMult ρ : ℝ), ?_, ?_⟩
  · exact_mod_cast multiplicity_pos hρ
  intro T u _ hγ _
  have hρT : ρ ∈ cutoff T := mem_cutoff.mpr ⟨hzero, hpos, hγ⟩
  have heval : ℓ ((weightedLandau_memLp T u).toLp (weightedLandau T u)) =
      ∫ s : ℝ, g s * landauSum T (u + s) := by
    change inner ℂ (hq.toLp q) ((weightedLandau_memLp T u).toLp (weightedLandau T u)) = _
    rw [← MarkedIntegralCauchy.integral_mul_star_eq_inner (weightedLandau_memLp T u) hq]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    simp only [weightedLandau, q, star_star]
    have hcancel : (Real.exp (-|s|) : ℂ) * (Real.exp |s| : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
    calc
      _ = ((Real.exp (-|s|) : ℂ) * (Real.exp |s| : ℂ)) *
          (g s * landauSum T (u + s)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  let coeff : ℂ → ℂ := fun σ => (zeroMult σ : ℂ) * Complex.exp ((u : ℂ) * (σ - 1 / 2))
  have hsignal (s : ℝ) : g s * landauSum T (u + s) =
      ∑ σ ∈ cutoff T, coeff σ * (g s * kernel ((1 - σ) - 1 / 2) s) := by
    have hshift (σ : ℂ) : Complex.exp (((u + s : ℝ) : ℂ) * (σ - 1 / 2)) =
        Complex.exp ((u : ℂ) * (σ - 1 / 2)) * kernel ((1 - σ) - 1 / 2) s := by
      rw [kernel, ← Complex.exp_add, Complex.ofReal_add]
      congr 1
      ring
    unfold landauSum ActualZeroOrdinate.sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    change g s * ((zeroMult σ : ℂ) * Complex.exp (((u + s : ℝ) : ℂ) * (σ - 1 / 2))) = _
    rw [hshift]
    dsimp [coeff]
    ring
  have hem := hg.decay.hasExponentialMoments hg.1.continuous
  rw [heval]
  simp_rw [hsignal]
  rw [integral_finsetSum (cutoff T) (fun σ _ =>
    (integrable_integrand hem (((1 : ℂ) - σ) - 1 / 2)).const_mul (coeff σ))]
  simp_rw [integral_const_mul]
  change ‖∑ σ ∈ cutoff T, coeff σ * centeredTransform g (1 - σ)‖ =
    (zeroMult ρ : ℝ) * Real.exp ((ρ.re - 1 / 2) * u)
  rw [Finset.sum_eq_single ρ]
  · have htest' : centeredTransform g (1 - ρ) = 1 := htest
    rw [htest', mul_one]
    dsimp [coeff]
    have hexp : ((u : ℂ) * (ρ - 1 / 2)).re = (ρ.re - 1 / 2) * u := by
      have hhalf : (ρ - 1 / 2 : ℂ).re = ρ.re - 1 / 2 := by norm_num
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hhalf]
      ring
    rw [norm_mul, Complex.norm_natCast, Complex.norm_exp, hexp]
  · intro σ hσ hne
    let σ' : zetaZeroConfig.carrier := ⟨σ, (mem_cutoff.mp hσ).1⟩
    have hne' : actualZeroOneSub σ' ≠ actualZeroOneSub ρ' := by
      intro heq
      exact hne (congrArg Subtype.val (actualZeroOneSub.injective heq))
    have hz : centeredTransform g (1 - σ) = 0 := htest0 _ hne'
    rw [hz, mul_zero]
  · intro hmiss
    exact (hmiss hρT).elim

theorem fixedRightZeroSharpIntegralLower : FixedRightZeroSharpIntegralLower :=
  fixedRightZeroSharpIntegralLower_of_separator fixedRightZeroSharpSeparator

/-- Under RH the horizontal correction vanishes in the energy identity. -/
theorem sharpIntegral_eq_rawIntegral_of_riemannHypothesis
    (hRH : RiemannHypothesis) (T u : ℝ) : sharpIntegral T u = rawIntegral T u := by
  have hsum (v : ℝ) : landauSum T v = ordinateSum T v := by
    rw [landauSum_eq_cosh, ordinateSum]
    unfold ActualZeroOrdinate.sum
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hcrit := Zeta23.RH_implies_on_line hRH (mem_cutoff.mp hρ).1
    simp [hcrit]
  simp only [sharpIntegral, rawIntegral, hsum]

/-- On RH the complex energy is O(T log² T), uniformly in frequency. -/
theorem exists_sharpIntegral_le_height_log_sq_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ T u : ℝ, 9 ≤ T →
      sharpIntegral T u ≤ C * T * Real.log T ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := MontgomeryLocalMass.exists_formFactor_le_log
  refine ⟨C / (2 * Real.pi), by positivity, ?_⟩
  intro T u hT
  have ht1 : 1 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos ht1
  let D : ℝ := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D := by dsimp [D]; positivity
  have hraw := hbound T (u / Real.log T) hT
  rw [formFactor_eq_rawIntegral, div_mul_cancel₀ u hlog.ne',
    ← sharpIntegral_eq_rawIntegral_of_riemannHypothesis hRH T u] at hraw
  calc
    _ ≤ (C * Real.log T) * D := (div_le_iff₀ hD).mp hraw
    _ = _ := by dsimp [D]; ring

/-- RH supplies the cofinal upper estimate with common exponent two. -/
theorem cofinalSharpPolynomialUpper_of_riemannHypothesis (hRH : RiemannHypothesis) :
    CofinalSharpPolynomialUpper := by
  obtain ⟨C, hC, hbound⟩ := exists_sharpIntegral_le_height_log_sq_of_riemannHypothesis hRH
  refine ⟨2, ?_⟩
  intro A
  refine ⟨4 * C, by positivity, ?_⟩
  intro Y
  let T := max Y 9
  have h9 : 9 ≤ T := le_max_right Y 9
  have hT : 1 < T := by linarith
  have hT0 : 0 < T := zero_lt_one.trans hT
  refine ⟨T, A, le_max_left Y 9, hT, le_rfl, ?_⟩
  have hlog : Real.log T ≤ 2 * Real.sqrt T := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hT0)
    rw [Real.log_sqrt hT0.le] at h
    linarith
  have hsquare : Real.log T ^ 2 ≤ 4 * T := by
    calc
      _ ≤ (2 * Real.sqrt T) ^ 2 := pow_le_pow_left₀ (Real.log_nonneg hT.le) hlog 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hT0.le]; norm_num
  calc
    _ ≤ C * T * Real.log T ^ 2 := hbound T _ h9
    _ ≤ C * T * (4 * T) := mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = 4 * C * Real.exp (2 * Real.log T) := by
      simp only [two_mul, Real.exp_add, Real.exp_log hT0]
      ring

/-- The cofinal polynomial growth criterion for the complex energy
is equivalent to RH. -/
theorem cofinalSharpPolynomialUpper_iff_riemannHypothesis :
    CofinalSharpPolynomialUpper ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_cofinal_sharpPolynomialUpper fixedRightZeroSharpIntegralLower,
    cofinalSharpPolynomialUpper_of_riemannHypothesis⟩

end RiemannResearch.Analysis.MontgomeryHorizontalTransfer
