import RiemannResearch.RH.IntegerDPPWeightedHoles

/-!
# The critical power-weighted vacancy obstruction

Source: user-provided catalogue of consequences of not RH, groups 22--23,
2026-09-21.  The proof below sharpens the previously formalized harmonic
bound for linearly weighted holes.  It uses the actual arithmetic kernel
and an actual right-half-strip zeta zero.  The physical site associated
with index n is n+1; the weight n+2 is its right endpoint.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.PowerCellEnergy

/-- Endpoint derivative comparison, retaining the real power exponent. -/
theorem power_gap_endpoint_lower {a b β : ℝ}
    (ha : 0 < a) (hab : a < b) (hβ : 0 < β) :
    β * ((b - a) * b ^ (-β - 1)) ≤ a ^ (-β) - b ^ (-β) := by
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-β - 1)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    rw [uIcc_of_le hab.le] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hc : (∫ x in a..b, b ^ (-β - 1)) ≤
      ∫ x in a..b, x ^ (-β - 1) := by
    apply intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hint
    intro x hx
    exact Real.rpow_le_rpow_of_nonpos (ha.trans_le hx.1) hx.2 (by linarith)
  rw [intervalIntegral.integral_const,
    ← powerIntervalWeight_eq_integral ha hab hβ] at hc
  simp only [smul_eq_mul, powerIntervalWeight] at hc
  have hm := (le_div_iff₀ hβ).mp hc
  nlinarith

end RiemannResearch.Analysis.PowerCellEnergy

namespace RiemannResearch.RH.Pareto.IntegerDPP

theorem site_mellin_numerator_power_lower (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    s.re * ((n : ℝ) + 2) ^ (-s.re - 1) ≤
      ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))‖ := by
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) + 2 := by positivity
  have hp := RiemannResearch.Analysis.PowerCellEnergy.power_gap_endpoint_lower
    (a := (n : ℝ) + 1) (b := (n : ℝ) + 2) ha (by linarith)
    (show 0 < s.re by linarith)
  have hr := norm_sub_norm_le (((((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s))
    (((((n : ℝ) + 2) : ℝ) : ℂ) ^ (-s))
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.norm_cpow_eq_rpow_re_of_pos hb] at hr
  simp only [Complex.neg_re] at hr
  have hgap : (n : ℝ) + 2 - ((n : ℝ) + 1) = 1 := by ring
  rw [hgap, one_mul] at hp
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat] using hp.trans hr

/-- The zero's critical exponent times the exact floor dominates a harmonic
term. The constant is positive for every actual right-half-strip zero. -/
theorem critical_weight_mul_site_floor_lower (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    mellinHoleMassConstant s / (2 * ((n : ℝ) + 2)) ≤
      ((n : ℝ) + 2) ^ (2 * s.re - 1) * siteMellinVacancyFloor n s := by
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) + 2 := by positivity
  have hw := paretoWeight_pos n
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hn0 : ‖s‖ ≠ 0 := (norm_pos_iff.mpr hs0).ne'
  have hh := site_mellin_numerator_power_lower n s hs
  have hnonneg : 0 ≤ s.re * ((n : ℝ) + 2) ^ (-s.re - 1) := by positivity
  have hsq : (s.re * ((n : ℝ) + 2) ^ (-s.re - 1)) ^ 2 ≤
      ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))‖ ^ 2 := by
    nlinarith [norm_nonneg ((((n + 1 : ℕ) : ℂ) ^ (-s)) -
      (((n + 2 : ℕ) : ℂ) ^ (-s)))]
  let A : ℝ := ((n : ℝ) + 2) ^ (2 * s.re - 1) *
    (2 * s.re - 1) / (‖s‖ ^ 2 * paretoWeight n)
  have hbeta : 0 < 2 * s.re - 1 := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hm := mul_le_mul_of_nonneg_left hsq hA
  have heR : A *
      ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 2 : ℕ) : ℂ) ^ (-s))‖ ^ 2 =
      ((n : ℝ) + 2) ^ (2 * s.re - 1) * siteMellinVacancyFloor n s := by
    rw [siteMellinVacancyFloor, point_mellin n s hs, norm_div, div_pow]
    dsimp [A]
    field_simp [hw.ne', hn0]
  have hpow : ((n : ℝ) + 2) ^ (2 * s.re - 1) *
      (((n : ℝ) + 2) ^ (-s.re - 1)) ^ 2 = ((n : ℝ) + 2) ^ (-3 : ℝ) := by
    rw [pow_two, ← mul_assoc, ← Real.rpow_add hb, ← Real.rpow_add hb]
    congr 1
    ring
  have heL : A * (s.re * ((n : ℝ) + 2) ^ (-s.re - 1)) ^ 2 =
      mellinHoleMassConstant s * ((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2 := by
    calc
      _ = ((2 * s.re - 1) * s.re ^ 2 / (‖s‖ ^ 2 * paretoWeight n)) *
          (((n : ℝ) + 2) ^ (2 * s.re - 1) *
            (((n : ℝ) + 2) ^ (-s.re - 1)) ^ 2) := by
        dsimp [A]
        ring
      _ = ((2 * s.re - 1) * s.re ^ 2 / (‖s‖ ^ 2 * paretoWeight n)) *
          ((n : ℝ) + 2) ^ (-3 : ℝ) := by rw [hpow]
      _ = _ := by
        have hcube : ((n : ℝ) + 2) ^ (-3 : ℝ) =
            (((n : ℝ) + 2) ^ (3 : ℕ))⁻¹ := by
          rw [Real.rpow_neg hb.le]
          exact congrArg Inv.inv (Real.rpow_natCast ((n : ℝ) + 2) 3)
        rw [hcube]
        unfold mellinHoleMassConstant paretoWeight
        field_simp [ha.ne', hb.ne', hn0]
  rw [heL, heR] at hm
  apply le_trans _ hm
  have hratio : (1 : ℝ) / (2 * ((n : ℝ) + 2)) ≤
      ((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 2))
      (sq_pos_of_pos hb)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
  simpa only [← mul_div_assoc, mul_one] using
    mul_le_mul_of_nonneg_left hratio (mellinHoleMassConstant_pos s hs).le

/-- Endpoint power-weighted hole probabilities are already nonsummable. -/
theorem critical_power_weighted_holes_not_summable_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    ¬ Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (2 * s.re - 1) *
      (1 - limitingKernel n n)) := by
  intro hsum
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  have hc := mellinHoleMassConstant_pos s hs
  have hsmall : Summable (fun n : ℕ =>
      mellinHoleMassConstant s / (2 * ((n : ℝ) + 2))) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
    intro n
    exact (critical_weight_mul_site_floor_lower n s hs).trans
      (mul_le_mul_of_nonneg_left
        (siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz n)
        (by positivity))
  have hinv : Summable (fun n : ℕ => ((n : ℝ) + 2)⁻¹) := by
    apply (hsmall.mul_left (2 / mellinHoleMassConstant s)).congr
    intro n
    field_simp [hc.ne']
  have hshift : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hinv
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 2).mp hshift)

/-- The conventional physical-site weight (n+1)^α has the same obstruction,
including the exact critical endpoint α = 2 Re(s)-1. -/
theorem power_weighted_holes_not_summable_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) (α : ℝ) (hα : 2 * s.re - 1 ≤ α) :
    ¬ Summable (fun n : ℕ => ((n : ℝ) + 1) ^ α *
      (1 - limitingKernel n n)) := by
  intro hsum
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  apply critical_power_weighted_holes_not_summable_of_zeta_zero s hs h1 hz
  apply Summable.of_nonneg_of_le _ _ (hsum.mul_left ((2 : ℝ) ^ α))
  · intro n
    have hv := (siteMellinVacancyFloor_pos n s hs).le.trans
      (siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz n)
    exact mul_nonneg (by positivity) hv
  · intro n
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have hb : 1 ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hv := (siteMellinVacancyFloor_pos n s hs).le.trans
      (siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz n)
    have hpow : ((n : ℝ) + 2) ^ (2 * s.re - 1) ≤
        (2 : ℝ) ^ α * ((n : ℝ) + 1) ^ α := by
      calc
        _ ≤ ((n : ℝ) + 2) ^ α :=
          Real.rpow_le_rpow_of_exponent_le hb hα
        _ ≤ (2 * ((n : ℝ) + 1)) ^ α :=
          Real.rpow_le_rpow (by positivity)
            (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
        _ = _ := Real.mul_rpow (by norm_num) ha.le
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpow hv

/-- One common actual zero forces all supercritical weighted series to fail. -/
theorem exists_common_critical_hole_exponent_of_not_RH (h : ¬ RiemannHypothesis) :
    ∃ s : ℂ, ((1 / 2 : ℝ) < s.re ∧ s.re < 1 ∧ riemannZeta s = 0) ∧
      ∀ α : ℝ, 2 * s.re - 1 ≤ α →
        ¬ Summable (fun n : ℕ => ((n : ℝ) + 1) ^ α *
          (1 - limitingKernel n n)) := by
  obtain ⟨s, ⟨hs, h1, hz⟩, _⟩ := exists_common_site_vacancy_floor_of_not_RH h
  exact ⟨s, ⟨hs, h1, hz⟩,
    fun α hα => power_weighted_holes_not_summable_of_zeta_zero s hs h1 hz α hα⟩

end RiemannResearch.RH.Pareto.IntegerDPP
