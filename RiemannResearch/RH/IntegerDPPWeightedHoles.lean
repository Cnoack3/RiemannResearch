import RiemannResearch.RH.IntegerDPPAllSiteObstruction
import RiemannResearch.Analysis.PowerCellEnergy
import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.Analysis.PSeries

/-!
# Weighted hole summability is sufficient for RH

Source: user-provided all-site Mellin obstruction, 2026-09-20. The stronger
uniform harmonic obstruction below follows by comparing the exact real
power integrals with the reciprocal-power integral. Thus no asymptotic
expansion of the complex power difference is needed.

The statements use the actual limiting arithmetic kernel. The final
probability formulation applies to any genuine DPP having this kernel;
its DPP realization remains an explicit hypothesis of that corollary.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.PowerCellEnergy

/-- On x ≥ 1 and for 0 < β ≤ 1, the power gap dominates β times the
reciprocal gap. This follows from exact integral comparison. -/
theorem reciprocal_gap_le_power_gap {a b β : ℝ}
    (ha1 : 1 ≤ a) (hab : a < b) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    β * (a⁻¹ - b⁻¹) ≤ a ^ (-β) - b ^ (-β) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hint (r : ℝ) : IntervalIntegrable (fun x : ℝ => x ^ r) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    rw [uIcc_of_le hab.le] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hcompare : powerIntervalWeight a b 1 ≤ powerIntervalWeight a b β := by
    rw [powerIntervalWeight_eq_integral (s := 1) ha hab (by norm_num),
      powerIntervalWeight_eq_integral (s := β) ha hab hβ]
    apply intervalIntegral.integral_mono_on hab.le (hint _) (hint _)
    intro x hx
    exact Real.rpow_le_rpow_of_exponent_le (ha1.trans hx.1) (by linarith)
  unfold powerIntervalWeight at hcompare
  norm_num only [Real.rpow_neg_one, div_one] at hcompare
  have hm := (le_div_iff₀ hβ).mp hcompare
  nlinarith

end RiemannResearch.Analysis.PowerCellEnergy

namespace RiemannResearch.RH.Pareto.IntegerDPP

private theorem complex_power_gap_norm_lower {a b : ℝ}
    (ha1 : 1 ≤ a) (hab : a < b) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    s.re * (a⁻¹ - b⁻¹) ≤ ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := ha.trans hab
  have h := RiemannResearch.Analysis.PowerCellEnergy.reciprocal_gap_le_power_gap
    ha1 hab hs hs1
  have hr := norm_sub_norm_le ((a : ℂ) ^ (-s)) ((b : ℂ) ^ (-s))
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.norm_cpow_eq_rpow_re_of_pos hb] at hr
  simp only [Complex.neg_re] at hr
  exact h.trans hr

/-- A uniform lower bound for every site's exact complex numerator. -/
theorem site_mellin_numerator_lower (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re ≤ 1) :
    s.re * paretoWeight n ≤
      ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))‖ := by
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) + 2 := by positivity
  have h := complex_power_gap_norm_lower
    (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith) s (by linarith) hs1
  have he : s.re * (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) =
      s.re * paretoWeight n := by
    unfold paretoWeight
    field_simp [ha.ne', hb.ne'] <;> ring
  rw [he] at h
  simpa using h

def mellinHoleMassConstant (s : ℂ) : ℝ :=
  (2 * s.re - 1) * s.re ^ 2 / ‖s‖ ^ 2

theorem mellinHoleMassConstant_pos (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    0 < mellinHoleMassConstant s := by
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  unfold mellinHoleMassConstant
  exact div_pos (mul_pos (by linarith) (sq_pos_of_pos (by linarith)))
    (sq_pos_of_pos (norm_pos_iff.mpr hs0))

/-- The exact all-site floor dominates a positive multiple of the Pareto mass. -/
theorem mellinHoleMassConstant_mul_weight_le_site_floor (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re ≤ 1) :
    mellinHoleMassConstant s * paretoWeight n ≤ siteMellinVacancyFloor n s := by
  have hw := paretoWeight_pos n
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hn0 : ‖s‖ ≠ 0 := (norm_pos_iff.mpr hs0).ne'
  have hβ : 0 < s.re := by linarith
  have hden : 0 < 2 * s.re - 1 := by linarith
  have hnum := site_mellin_numerator_lower n s hs hs1
  have hnonneg : 0 ≤ s.re * paretoWeight n := by positivity
  have hsq : (s.re * paretoWeight n) ^ 2 ≤
      ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))‖ ^ 2 := by
    nlinarith [norm_nonneg ((((n + 1 : ℕ) : ℂ) ^ (-s)) -
      (((n + 2 : ℕ) : ℂ) ^ (-s)))]
  let A : ℝ := (2 * s.re - 1) / (‖s‖ ^ 2 * paretoWeight n)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hm := mul_le_mul_of_nonneg_left hsq hA
  have heL : A * (s.re * paretoWeight n) ^ 2 =
      mellinHoleMassConstant s * paretoWeight n := by
    dsimp [A, mellinHoleMassConstant]
    field_simp [hw.ne', hn0] <;> ring
  have heR : A *
      ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))‖ ^ 2 =
      siteMellinVacancyFloor n s := by
    rw [siteMellinVacancyFloor, point_mellin n s hs, norm_div, div_pow]
    dsimp [A]
    field_simp [hw.ne', hn0] <;> ring
  rw [heL, heR] at hm
  exact hm

theorem mellinHoleMassConstant_mul_weight_le_limiting_hole
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) (n : ℕ) :
    mellinHoleMassConstant s * paretoWeight n ≤ 1 - limitingKernel n n := by
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  exact (mellinHoleMassConstant_mul_weight_le_site_floor n s hs h1.le).trans
    (siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz n)

/-- The site index is shifted: physical mass n+1 multiplies hole probability. -/
def weightedLimitingHole (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (1 - limitingKernel n n)

theorem weightedLimitingHole_harmonic_lower
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) (n : ℕ) :
    mellinHoleMassConstant s / ((n : ℝ) + 2) ≤ weightedLimitingHole n := by
  have h := mellinHoleMassConstant_mul_weight_le_limiting_hole s hs h1 hz n
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) + 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left h ha.le
  change _ ≤ ((n : ℝ) + 1) * (1 - limitingKernel n n)
  calc
    _ = ((n : ℝ) + 1) * (mellinHoleMassConstant s * paretoWeight n) := by
      unfold paretoWeight
      field_simp [ha.ne', hb.ne'] <;> ring
    _ ≤ _ := hm

theorem weightedLimitingHole_not_summable_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : ¬ Summable weightedLimitingHole := by
  intro hsum
  have hc := mellinHoleMassConstant_pos s hs
  have hsmall : Summable (fun n : ℕ => mellinHoleMassConstant s / ((n : ℝ) + 2)) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (weightedLimitingHole_harmonic_lower s hs h1 hz) hsum
  have hinv : Summable (fun n : ℕ => ((n : ℝ) + 2)⁻¹) := by
    simpa [div_eq_mul_inv, ← mul_assoc, ne_of_gt hc] using
      hsmall.mul_left (mellinHoleMassConstant s)⁻¹
  have hshift : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hinv
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 2).mp hshift)

theorem weightedLimitingHole_not_summable_of_not_RH
    (h : ¬ RiemannHypothesis) : ¬ Summable weightedLimitingHole := by
  obtain ⟨s, ⟨hs, h1, hz⟩, _⟩ := exists_common_site_vacancy_floor_of_not_RH h
  exact weightedLimitingHole_not_summable_of_zeta_zero s hs h1 hz

/-- This requires only summable weighted holes, not pointwise saturation. -/
theorem riemannHypothesis_of_weightedLimitingHole_summable
    (h : Summable weightedLimitingHole) : RiemannHypothesis := by
  by_contra hn
  exact weightedLimitingHole_not_summable_of_not_RH hn h

/-- A probability formulation for any genuine realization of the actual
limiting arithmetic kernel. No unrelated diagonal or probability law is used. -/
theorem riemannHypothesis_of_summable_weighted_hole_probabilities
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Set ℕ)
    (hDPP : RiemannResearch.Probability.DPP.IsDPP μ X limitingKernel)
    (h : Summable (fun n : ℕ => ((n : ℝ) + 1) * μ.real {ω | n ∉ X ω})) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_weightedLimitingHole_summable
  change Summable (fun n : ℕ => ((n : ℝ) + 1) * (1 - limitingKernel n n))
  simpa only [hDPP.vacancy] using h

end RiemannResearch.RH.Pareto.IntegerDPP
