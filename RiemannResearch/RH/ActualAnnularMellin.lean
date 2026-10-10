import RiemannResearch.RH.ActualRieszTwoMellin
import RiemannResearch.RH.ActualRieszTwoAnnularCutoff
import RiemannResearch.RH.AnnularPrimePairTargets
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Mellin identity of the actual annular prime signal

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

All prime powers and all real cutoffs are retained. The finite annular cutoff
identity and the unconditional actual second-Riesz Mellin bridge close the
arithmetic identity on Re(s)>1. No RH, zero enumeration, spectral formula, or
analytic identity provider is used.

Dilation is applied only to the uncentered sum, which vanishes below 1.
The centered sum would have a boundary integral on (1/b,1); its linear term is
integrated separately by the existing `linear_mellin_integral` theorem.

Mellin dilation and positive-base complex-power APIs are source-reviewed at
mathlib revision 51e6992efd06126df61a496bebf8f49482a4e129.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.ActualAnnularMellin
open ActualRieszTwo ChebyshevMellin AnnularPrimePair
open RiemannResearch.Analysis.AnnularMellin

private def qComplex (x : ℝ) : ℂ := (uncenteredRieszTwo x : ℂ)

private theorem qComplex_zero {x : ℝ} (hx : x ≤ 1) : qComplex x = 0 := by
  simp [qComplex, uncenteredRieszTwo_eq_zero_of_le_one hx]

private theorem q_mellin_zero_extension (s : ℂ) :
    mellin qComplex (-s) =
      ∫ x in Ioi (1 : ℝ), (uncenteredRieszTwo x : ℂ) *
        (x : ℂ) ^ (-(s + 1)) := by
  simp only [mellin, smul_eq_mul, show -s - 1 = -(s + 1) by ring]
  calc
    _ = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-(s + 1)) * qComplex x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
      intro x hx
      simp [qComplex_zero (le_of_not_gt hx.2)]
    _ = _ := by simp only [qComplex, mul_comm]

private theorem q_mellin_zero_extension_integrable {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent qComplex (-s) := by
  have hi : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(s + 1)) * qComplex x) (Ioi 1) := by
    simpa only [qComplex, mul_comm] using uncenteredRieszTwo_mellin_integrable hs
  have hz : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(s + 1)) * qComplex x) (Ioi 0) :=
    hi.of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => by
      simp [qComplex_zero (le_of_not_gt hx.2)])
  simpa only [MellinConvergent, smul_eq_mul,
    show -s - 1 = -(s + 1) by ring] using hz

/-- Integrability is preserved by every positive dilation, even when b<1. -/
theorem scaledRieszTwo_mellin_integrable {s : ℂ} {b : ℝ}
    (hs : 1 < s.re) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => (uncenteredRieszTwo (x / b) : ℂ) *
      (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hi := (MellinConvergent.comp_mul_left (inv_pos.mpr hb)).2
    (q_mellin_zero_extension_integrable hs)
  have hi' : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(s + 1)) * qComplex (b⁻¹ * x)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul,
      show -s - 1 = -(s + 1) by ring] using hi
  apply (hi'.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun
  · intro x hx
    simp only [qComplex, div_eq_mul_inv, mul_comm]
  · exact measurableSet_Ioi

/-- The boundary-free formula requires b≥1; it is applied to the uncentered sum. -/
theorem scaledRieszTwo_mellin {s : ℂ} {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in Ioi (1 : ℝ), (uncenteredRieszTwo (x / b) : ℂ) *
      (x : ℂ) ^ (-(s + 1))) =
      (b : ℂ) ^ (-s) *
        ∫ x in Ioi (1 : ℝ), (uncenteredRieszTwo x : ℂ) *
          (x : ℂ) ^ (-(s + 1)) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hext : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(s + 1)) * qComplex (b⁻¹ * x)) =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-(s + 1)) * qComplex (b⁻¹ * x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    intro x hx
    have hx1 : x ≤ 1 := le_of_not_gt hx.2
    have hxb : b⁻¹ * x ≤ 1 := by
      have hxb' : x / b ≤ 1 := (div_le_iff₀ hb0).mpr
        (by simpa only [one_mul] using hx1.trans hb)
      simpa only [div_eq_mul_inv, mul_comm] using hxb'
    simp [qComplex_zero hxb]
  calc
    _ = mellin (fun x => qComplex (b⁻¹ * x)) (-s) := by
      simp only [mellin, smul_eq_mul, show -s - 1 = -(s + 1) by ring]
      rw [hext]
      simp only [qComplex, div_eq_mul_inv, mul_comm]
    _ = ((b⁻¹ : ℝ) : ℂ) ^ s * mellin qComplex (-s) := by
      simpa only [neg_neg, smul_eq_mul] using
        mellin_comp_mul_left qComplex (-s) (inv_pos.mpr hb0)
    _ = _ := by
      rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hb0.le,
        ← Complex.cpow_neg, q_mellin_zero_extension]

/-- Exact polynomial in the geometric dilation factor. -/
private def dilationPolynomial (s : ℂ) : ℂ :=
  1 - (7 / 4 : ℂ) * (2 : ℂ) ^ (-s) +
    (7 / 8 : ℂ) * (4 : ℂ) ^ (-s) - (1 / 8 : ℂ) * (8 : ℂ) ^ (-s)

private theorem dilationFactor_cpow (a : ℝ) (s : ℂ) :
    dilationFactor 2 a s = 1 - (2 : ℂ) ^ (-(s + (a : ℂ))) := by
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  unfold dilationFactor
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), hlog]
  congr 2
  ring

private theorem dilationPolynomial_eq_product (s : ℂ) :
    dilationPolynomial s =
      dilationFactor 2 0 s * dilationFactor 2 1 s * dilationFactor 2 2 s := by
  have h4 : (4 : ℂ) ^ (-s) = ((2 : ℂ) ^ (-s)) ^ (2 : ℕ) := by
    have h := Complex.natCast_mul_natCast_cpow 2 2 (-s)
    norm_num at h
    rw [h]
    ring
  have h8 : (8 : ℂ) ^ (-s) = ((2 : ℂ) ^ (-s)) ^ (3 : ℕ) := by
    have h := Complex.natCast_mul_natCast_cpow 4 2 (-s)
    norm_num at h
    rw [h, h4]
    ring
  have h0 : dilationFactor 2 0 s = 1 - (2 : ℂ) ^ (-s) := by
    simp only [dilationFactor_cpow, Complex.ofReal_zero, add_zero]
  have h1 : dilationFactor 2 1 s = 1 - (2 : ℂ) ^ (-s) / 2 := by
    rw [dilationFactor_cpow]
    simp only [Complex.ofReal_one]
    rw [show -(s + 1) = -s + (-1) by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num [Complex.cpow_neg, div_eq_mul_inv]
  have h2 : dilationFactor 2 2 s = 1 - (2 : ℂ) ^ (-s) / 4 := by
    rw [dilationFactor_cpow]
    simp only [Complex.ofReal_ofNat]
    rw [show -(s + 2) = -s + (-2) by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num [Complex.cpow_neg, div_eq_mul_inv]
  rw [dilationPolynomial, h4, h8, h0, h1, h2]
  ring

/-- The finite arithmetic annular combination retains the full linear centering. -/
theorem actualPrimeSignal_eq_scaledRieszTwo {x : ℝ} (hx : 0 < x) :
    actualPrimeSignal x =
      uncenteredRieszTwo x - (7 / 4 : ℝ) * uncenteredRieszTwo (x / 2) +
        (7 / 8 : ℝ) * uncenteredRieszTwo (x / 4) -
        (1 / 8 : ℝ) * uncenteredRieszTwo (x / 8) - (7 / 64 : ℝ) * x := by
  unfold actualPrimeSignal annularPrimeFinite indices
  rw [uncenteredAnnular_eq_scaledRieszTwo hx]

private def scaledIntegrand (s : ℂ) (b : ℝ) (x : ℝ) : ℂ :=
  (uncenteredRieszTwo (x / b) : ℂ) * (x : ℂ) ^ (-(s + 1))

/-- Integrability of the actual centered annular signal on its initial half-plane. -/
theorem actualPrimeSignal_mellin_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (actualPrimeSignal x : ℂ) *
      (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hi0 := uncenteredRieszTwo_mellin_integrable hs
  have hi2 := scaledRieszTwo_mellin_integrable hs (by norm_num : (0 : ℝ) < 2)
  have hi4 := scaledRieszTwo_mellin_integrable hs (by norm_num : (0 : ℝ) < 4)
  have hi8 := scaledRieszTwo_mellin_integrable hs (by norm_num : (0 : ℝ) < 8)
  have hil := linear_mellin_integrable hs
  apply ((((hi0.sub (hi2.const_mul (7 / 4 : ℂ))).add
    (hi4.const_mul (7 / 8 : ℂ))).sub (hi8.const_mul (1 / 8 : ℂ))).sub
    (hil.const_mul (7 / 64 : ℂ))).congr_fun
  · intro x hx
    dsimp only
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [actualPrimeSignal_eq_scaledRieszTwo (lt_trans zero_lt_one hx)]
    push_cast
    ring
  · exact measurableSet_Ioi

/-- The physical arithmetic identity, proved on Re(s)>1 without RH. -/
theorem actualPrimeSignal_mellin_identity {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), (actualPrimeSignal x : ℂ) *
      (x : ℂ) ^ (-(s + 1))) =
      -multiplier s * logDeriv riemannZeta s - (7 / 64 : ℂ) / (s - 1) := by
  have hi0 := uncenteredRieszTwo_mellin_integrable hs
  have hi2 := scaledRieszTwo_mellin_integrable hs (by norm_num : (0 : ℝ) < 2)
  have hi4 := scaledRieszTwo_mellin_integrable hs (by norm_num : (0 : ℝ) < 4)
  have hi8 := scaledRieszTwo_mellin_integrable hs (by norm_num : (0 : ℝ) < 8)
  have hil := linear_mellin_integrable hs
  calc
    _ = ∫ x in Ioi (1 : ℝ),
        ((uncenteredRieszTwo x : ℂ) * (x : ℂ) ^ (-(s + 1)) -
          (7 / 4 : ℂ) * scaledIntegrand s 2 x +
          (7 / 8 : ℂ) * scaledIntegrand s 4 x -
          (1 / 8 : ℂ) * scaledIntegrand s 8 x) -
          (7 / 64 : ℂ) * ((x : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [actualPrimeSignal_eq_scaledRieszTwo (lt_trans zero_lt_one hx)]
      simp only [scaledIntegrand]
      push_cast
      ring
    _ = (∫ x in Ioi (1 : ℝ), (uncenteredRieszTwo x : ℂ) *
        (x : ℂ) ^ (-(s + 1))) -
        (7 / 4 : ℂ) * (∫ x in Ioi (1 : ℝ), scaledIntegrand s 2 x) +
        (7 / 8 : ℂ) * (∫ x in Ioi (1 : ℝ), scaledIntegrand s 4 x) -
        (1 / 8 : ℂ) * (∫ x in Ioi (1 : ℝ), scaledIntegrand s 8 x) -
        (7 / 64 : ℂ) * (∫ x in Ioi (1 : ℝ),
          (x : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
      simp only [scaledIntegrand]
      have hsub2 := integral_sub hi0 (hi2.const_mul (7 / 4 : ℂ))
      have hadd4 := integral_add (hi0.sub (hi2.const_mul (7 / 4 : ℂ)))
        (hi4.const_mul (7 / 8 : ℂ))
      have hsub8 := integral_sub
        ((hi0.sub (hi2.const_mul (7 / 4 : ℂ))).add (hi4.const_mul (7 / 8 : ℂ)))
        (hi8.const_mul (1 / 8 : ℂ))
      have hsubl := integral_sub
        (((hi0.sub (hi2.const_mul (7 / 4 : ℂ))).add (hi4.const_mul (7 / 8 : ℂ))).sub
          (hi8.const_mul (1 / 8 : ℂ)))
        (hil.const_mul (7 / 64 : ℂ))
      simp only [Pi.sub_apply, Pi.add_apply] at hsub2 hadd4 hsub8 hsubl
      rw [hsubl, hsub8, hadd4, hsub2]
      simp only [integral_const_mul]
    _ = dilationPolynomial s *
        (∫ x in Ioi (1 : ℝ), (uncenteredRieszTwo x : ℂ) *
          (x : ℂ) ^ (-(s + 1))) - (7 / 64 : ℂ) / (s - 1) := by
      simp only [scaledIntegrand]
      rw [scaledRieszTwo_mellin (by norm_num : (1 : ℝ) ≤ 2),
        scaledRieszTwo_mellin (by norm_num : (1 : ℝ) ≤ 4),
        scaledRieszTwo_mellin (by norm_num : (1 : ℝ) ≤ 8), linear_mellin_integral hs]
      simp only [Complex.ofReal_ofNat]
      unfold dilationPolynomial
      ring
    _ = _ := by
      rw [uncenteredRieszTwo_mellin_identity hs, dilationPolynomial_eq_product,
        multiplier, secondRieszDenominator, logDeriv_apply]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The previously open arithmetic identity is supplied by an actual proof. -/
theorem actualAnnularMellinIdentity : ActualAnnularMellinIdentity := by
  intro s hs
  simpa only [show -s - 1 = -(s + 1) by ring] using actualPrimeSignal_mellin_identity hs

end RiemannResearch.RH.ActualAnnularMellin
