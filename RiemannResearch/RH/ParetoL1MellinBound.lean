import RiemannResearch.RH.ParetoMellinFunctional
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Weighted L1 accuracy and the full Mellin energy obstruction

Source: user-provided argument,
RH_Canonical_Correlations_and_Spectral_Obstruction_20260912 (1).md,
Sections 6 and 13, and its analytic continuation of 12 September 2026.
The source supplies the setting and proof strategy. This module proves the
actual discrete L1/integral identity and a literal head/tail cutoff estimate.
It does not assume an arithmetic nullity provider or an approximation sequence.

For 1/2 < Re(s) < 1, a vector e with Mellin value 1/s and sufficiently small
positive L1 norm satisfies
  mellinL1Constant s <= norm(e)^2 * hilbertL1(e)^(mellinL1Exponent s).
The exponent is (2 Re(s)-1)/(1-Re(s)); the positive constant is the one
defined below. The stronger optimized-clipping constant in the companion
research note is not asserted by this module. All norms include the full
infinite Pareto energy.
-/

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- The full weighted L1 norm, with the existing zero-coordinate convention. -/
def hilbertL1 (f : ThresholdHilbert) : ℝ :=
  ∑' k, positiveWeight k * |hilbertSequence f k|

/-- Finite Hilbert energy gives summability of the actual weighted absolute values. -/
theorem hilbertL1_summable (f : ThresholdHilbert) :
    Summable (fun k => positiveWeight k * |hilbertSequence f k|) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg k) (abs_nonneg _))
    (fun k => ?_) ((hilbertSequence_square_summable f).add positiveWeight_summable)
  have h : |hilbertSequence f k| ≤ hilbertSequence f k ^ 2 + 1 := by
    nlinarith [sq_nonneg (|hilbertSequence f k| - 1), sq_abs (hilbertSequence f k)]
  have hm := mul_le_mul_of_nonneg_left h (positiveWeight_nonneg k)
  linarith

/-- The weighted L1 norm is nonnegative. -/
theorem hilbertL1_nonneg (f : ThresholdHilbert) : 0 ≤ hilbertL1 f :=
  tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k) (abs_nonneg _))

/-- The continuous physical L1 density is integrable over the complete half-line. -/
theorem hilbertL1_integrable (f : ThresholdHilbert) :
    IntegrableOn (fun x : ℝ => |hilbertSequence f ⌊x⌋₊| / x ^ 2) (Ioi 1) := by
  have hs : Summable (fun k => positiveWeight k *
      (Real.sqrt |hilbertSequence f k|) ^ 2) := by
    simpa only [Real.sq_sqrt (abs_nonneg _)] using hilbertL1_summable f
  simpa only [Real.sq_sqrt (abs_nonneg _)] using
    paretoStepEnergy_integrable (fun k => Real.sqrt |hilbertSequence f k|) hs

/-- The continuous and discrete weighted L1 norms agree exactly. -/
theorem hilbertL1_eq_integral (f : ThresholdHilbert) :
    hilbertL1 f = ∫ x in Ioi (1 : ℝ), |hilbertSequence f ⌊x⌋₊| / x ^ 2 := by
  have hs : Summable (fun k => positiveWeight k *
      (Real.sqrt |hilbertSequence f k|) ^ 2) := by
    simpa only [Real.sq_sqrt (abs_nonneg _)] using hilbertL1_summable f
  simpa only [Real.sq_sqrt (abs_nonneg _), hilbertL1] using
    (paretoStep_energy_identity (fun k => Real.sqrt |hilbertSequence f k|) hs).symm

/-- Exact norm of the physical Mellin integrand before a cutoff is imposed. -/
theorem mellin_integrand_norm (f : ThresholdHilbert) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    ‖mellinWeightedStep f x * paretoMellinKernel s x‖ =
      (|hilbertSequence f ⌊x⌋₊| / x ^ 2) * x ^ (1 - s.re) := by
  rw [norm_mul, mellinWeightedStep, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx,
    paretoMellinKernel, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  rw [show 1 - s.re = 1 + (-s.re) by ring, Real.rpow_add hx, Real.rpow_one]
  field_simp

/-- L1 control of the actual finite head of the Mellin integral. -/
theorem paretoMellin_head_l1_bound (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re ≤ 1)
    {b : ℝ} (hb : 1 ≤ b) :
    ‖∫ x in (1 : ℝ)..b, mellinWeightedStep f x * paretoMellinKernel s x‖ ≤
      b ^ (1 - s.re) * hilbertL1 f := by
  let q : ℝ → ℝ := fun x => |hilbertSequence f ⌊x⌋₊| / x ^ 2
  have hq : IntegrableOn q (Ioi 1) := hilbertL1_integrable f
  have hi := (paretoMellin_integrable f s hs).mono_set
    (show Ioc (1 : ℝ) b ⊆ Ioi 1 from fun _ hx => hx.1)
  rw [intervalIntegral.integral_of_le hb]
  calc
    _ ≤ ∫ x in Ioc (1 : ℝ) b, ‖mellinWeightedStep f x * paretoMellinKernel s x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioc (1 : ℝ) b, b ^ (1 - s.re) * q x := by
      apply integral_mono_ae hi.norm
        ((hq.mono_set (fun _ hx => hx.1)).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [mellin_integrand_norm f s (by linarith [hx.1])]
      have hr := Real.rpow_le_rpow (by linarith [hx.1] : (0 : ℝ) ≤ x)
        hx.2 (by linarith : 0 ≤ 1 - s.re)
      have hqn : 0 ≤ q x := div_nonneg (abs_nonneg _) (sq_nonneg _)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr hqn
    _ ≤ b ^ (1 - s.re) * hilbertL1 f := by
      rw [integral_const_mul, hilbertL1_eq_integral]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
      exact integral_mono_measure
        (Measure.restrict_mono (fun _ hx => hx.1) le_rfl)
        (Filter.Eventually.of_forall (fun x => div_nonneg (abs_nonneg _) (sq_nonneg _))) hq

/-- The actual tail is controlled by the full, untruncated Hilbert norm. -/
theorem paretoMellin_tail_full_energy_bound (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) {b : ℝ} (hb : 1 ≤ b) :
    ‖∫ x in Ioi b, mellinWeightedStep f x * paretoMellinKernel s x‖ ^ 2 ≤
      ‖f‖ ^ 2 * (b ^ (1 - 2 * s.re) / (2 * s.re - 1)) := by
  apply (paretoMellin_tail_norm_sq_le f s hs hb).trans
  apply mul_le_mul_of_nonneg_right _
    (div_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ b) _) (by linarith))
  rw [← mellinWeightedStep_energy]
  exact integral_mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi hb) le_rfl)
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    (mellinWeightedStep_memLp f).norm.integrable_sq

/-- A small head forces a quantitative amount of complete quadratic energy. -/
theorem paretoMellin_l1_cutoff_lower (e : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re ≤ 1)
    (he : paretoMellin e s = 1 / s) {b : ℝ} (hb : 1 ≤ b)
    (hsmall : b ^ (1 - s.re) * hilbertL1 e ≤ 1 / (2 * ‖s‖)) :
    (2 * s.re - 1) / (4 * ‖s‖ ^ 2) * b ^ (2 * s.re - 1) ≤ ‖e‖ ^ 2 := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hc : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hb0 : 0 < b := by linarith
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (paretoMellin_integrable e s hs)
    ((paretoMellin_integrable e s hs).mono_set (Ioi_subset_Ioi hb))
  change _ + _ = paretoMellin e s at hsplit
  rw [he] at hsplit
  have ht := norm_add_le
    (∫ x in (1 : ℝ)..b, mellinWeightedStep e x * paretoMellinKernel s x)
    (∫ x in Ioi b, mellinWeightedStep e x * paretoMellinKernel s x)
  rw [hsplit, norm_div, norm_one] at ht
  have hh := (paretoMellin_head_l1_bound e s hs hs1 hb).trans hsmall
  have htlow : 1 / (2 * ‖s‖) ≤
      ‖∫ x in Ioi b, mellinWeightedStep e x * paretoMellinKernel s x‖ := by
    have hid : 1 / ‖s‖ = 2 * (1 / (2 * ‖s‖)) := by ring
    rw [hid] at ht
    linarith
  have hsq := sq_le_sq₀ (by positivity : 0 ≤ 1 / (2 * ‖s‖))
    (norm_nonneg (∫ x in Ioi b, mellinWeightedStep e x * paretoMellinKernel s x))
  have ht2 := (hsq.mpr htlow).trans (paretoMellin_tail_full_energy_bound e s hs hb)
  have hp : 0 < b ^ (2 * s.re - 1) := Real.rpow_pos_of_pos hb0 _
  have hm := mul_le_mul_of_nonneg_left ht2 (mul_nonneg hd.le hp.le)
  have hexp : b ^ (1 - 2 * s.re) = (b ^ (2 * s.re - 1))⁻¹ := by
    rw [show 1 - 2 * s.re = -(2 * s.re - 1) by ring, Real.rpow_neg hb0.le]
  rw [hexp] at hm
  have hr : (2 * s.re - 1) * b ^ (2 * s.re - 1) *
      (‖e‖ ^ 2 * ((b ^ (2 * s.re - 1))⁻¹ / (2 * s.re - 1))) = ‖e‖ ^ 2 := by
    field_simp
  have hl : (2 * s.re - 1) * b ^ (2 * s.re - 1) * (1 / (2 * ‖s‖)) ^ 2 =
      (2 * s.re - 1) / (4 * ‖s‖ ^ 2) * b ^ (2 * s.re - 1) := by ring
  rwa [hr, hl] at hm

/-- The positive blow-up power associated to a point in the right half-strip. -/
def mellinL1Exponent (s : ℂ) : ℝ := (2 * s.re - 1) / (1 - s.re)

/-- Explicit cutoff constant; no optimality claim is made. -/
def mellinL1Constant (s : ℂ) : ℝ :=
  (2 * s.re - 1) / (4 * ‖s‖ ^ 2) * (1 / (2 * ‖s‖)) ^ mellinL1Exponent s

/-- The exponent is positive precisely in the relevant open half-strip. -/
theorem mellinL1Exponent_pos (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re < 1) : 0 < mellinL1Exponent s := by
  unfold mellinL1Exponent
  exact div_pos (by linarith) (by linarith)

/-- The cutoff constant is strictly positive in the continuity half-plane. -/
theorem mellinL1Constant_pos (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    0 < mellinL1Constant s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hc : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  unfold mellinL1Constant
  apply mul_pos
  · exact div_pos (by linarith) (by positivity)
  · exact Real.rpow_pos_of_pos (by positivity) _

/-- A nonzero normalized Mellin value forces a polynomial energy cost as L1 error shrinks. -/
theorem paretoMellin_l1_power_lower (e : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1)
    (he : paretoMellin e s = 1 / s)
    (hε : 0 < hilbertL1 e) (hsmall : hilbertL1 e ≤ 1 / (2 * ‖s‖)) :
    mellinL1Constant s ≤ ‖e‖ ^ 2 * (hilbertL1 e) ^ mellinL1Exponent s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hc : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hβ : 0 < 1 - s.re := by linarith
  let t : ℝ := 1 / (2 * ‖s‖ * hilbertL1 e)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : 1 ≤ t := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * ‖s‖ * hilbertL1 e)).2
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * ‖s‖)).mp hsmall
    nlinarith
  let b : ℝ := t ^ (1 / (1 - s.re))
  have hb : 1 ≤ b := Real.one_le_rpow ht1 (by positivity)
  have hbβ : b ^ (1 - s.re) = t := by
    dsimp only [b]
    rw [← Real.rpow_mul ht0.le]
    have hcancel : (1 / (1 - s.re)) * (1 - s.re) = 1 := by
      field_simp
    rw [hcancel, Real.rpow_one]
  have hcut : b ^ (1 - s.re) * hilbertL1 e ≤ 1 / (2 * ‖s‖) := by
    rw [hbβ]
    dsimp [t]
    field_simp
    exact le_rfl
  have hl := paretoMellin_l1_cutoff_lower e s hs hs1.le he hb hcut
  have hp : 0 ≤ (hilbertL1 e) ^ mellinL1Exponent s :=
    Real.rpow_nonneg hε.le _
  have hmul := mul_le_mul_of_nonneg_right hl hp
  have hid : b ^ (2 * s.re - 1) * (hilbertL1 e) ^ mellinL1Exponent s =
      (1 / (2 * ‖s‖)) ^ mellinL1Exponent s := by
    dsimp only [b]
    rw [← Real.rpow_mul ht0.le]
    have hex : 1 / (1 - s.re) * (2 * s.re - 1) = mellinL1Exponent s := by
      unfold mellinL1Exponent
      ring
    rw [hex, ← Real.mul_rpow ht0.le hε.le]
    congr 1
    dsimp [t]
    field_simp
  rw [mul_assoc, hid] at hmul
  exact hmul

/-- The weighted L1 norm separates actual Hilbert vectors. -/
theorem hilbertL1_eq_zero_iff (f : ThresholdHilbert) : hilbertL1 f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply hilbertSequence_injective
    change hilbertSequenceLinear f = hilbertSequenceLinear 0
    rw [map_zero]
    funext k
    change hilbertSequence f k = 0
    cases k with
    | zero => exact hilbertSequence_zero f
    | succ k =>
      have hi := (hilbertL1_summable f).le_tsum (k + 1)
        (fun j _ => mul_nonneg (positiveWeight_nonneg j) (abs_nonneg _))
      change positiveWeight (k + 1) * |hilbertSequence f (k + 1)| ≤ hilbertL1 f at hi
      rw [h] at hi
      have hw : 0 < positiveWeight (k + 1) := by
        rw [positiveWeight_succ]
        unfold paretoWeight
        positivity
      have hz : |hilbertSequence f (k + 1)| ≤ 0 := by
        nlinarith [abs_nonneg (hilbertSequence f (k + 1))]
      exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  · rintro rfl
    unfold hilbertL1
    have hz : hilbertSequence (0 : ThresholdHilbert) = 0 := hilbertSequenceLinear.map_zero
    rw [hz]
    simp

/-- A vector with normalized nonzero Mellin moment has positive L1 norm. -/
theorem hilbertL1_pos_of_mellin_value (e : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (he : paretoMellin e s = 1 / s) :
    0 < hilbertL1 e := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  by_contra hn
  have he0 := (hilbertL1_eq_zero_iff e).mp
    (le_antisymm (le_of_not_gt hn) (hilbertL1_nonneg e))
  have hz : paretoMellin (0 : ThresholdHilbert) s = 0 :=
    (paretoMellinContinuous s hs).map_zero
  rw [he0, hz] at he
  exact one_div_ne_zero hs0 he.symm

/-- A squared-energy exponent a corresponds to the displayed zero-free boundary. -/
theorem mellinL1Exponent_gt_iff (s : ℂ) (hs1 : s.re < 1)
    (a : ℝ) (ha : 0 ≤ a) :
    a < mellinL1Exponent s ↔ (a + 1) / (a + 2) < s.re := by
  unfold mellinL1Exponent
  rw [lt_div_iff₀ (by linarith : 0 < 1 - s.re),
    div_lt_iff₀ (by linarith : 0 < a + 2)]
  constructor <;> intro h <;> nlinarith

end
end RiemannResearch.RH.Pareto
