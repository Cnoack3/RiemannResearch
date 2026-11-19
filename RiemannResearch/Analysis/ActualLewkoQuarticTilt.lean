/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualLewkoCriticalWeight

/-!
# Far contribution to the fourth horizontal moment with exponential tilt

At an ordinate frequency u the relevant weight is d⁴ exp(2|u|d), where d is
the absolute horizontal displacement of a copy. The theorem bounds its full
strict far subsum normalized by T, the normalization used for the raw Gram
error. The permitted b in 2|u| ≤ b log T is optimized at both endpoints of
the finite quasi-Riemann support. This leaves the complementary near subsum
as a separate analytic question.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def lewkoTiltExcess (b σ : ℝ) : ℝ := 3 / (2 * σ) * (1 - σ) + b * (σ - 1 / 2) - 1
def lewkoTiltBudget (b σ₀ B : ℝ) : ℝ := max (lewkoTiltExcess b σ₀) (lewkoTiltExcess b B)
def lewkoTiltThreshold (σ : ℝ) : ℝ := (5 * σ - 3) / (σ * (2 * σ - 1))

private theorem lewkoTiltExcess_diff (b : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    lewkoTiltExcess b y - lewkoTiltExcess b x = (y - x) * (b - 3 / (2 * x * y)) := by
  unfold lewkoTiltExcess
  field_simp [hx.ne', hy.ne']; ring

theorem lewkoTiltExcess_le_budget {b σ₀ σ B : ℝ}
    (hb : 0 ≤ b) (h₀ : 0 < σ₀) (hσ : σ ∈ Icc σ₀ B) :
    lewkoTiltExcess b σ ≤ lewkoTiltBudget b σ₀ B := by
  have hp := h₀.trans_le hσ.1
  have hB := hp.trans_le hσ.2
  by_cases hsq : 2 * b * σ * σ ≤ 3
  · have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hσ.1 hp.le) (show 0 ≤ 2 * b by positivity)
    have hc : b - 3 / (2 * σ₀ * σ) ≤ 0 := by
      apply sub_nonpos.mpr ((le_div_iff₀ (by positivity)).mpr ?_)
      linarith only [hm, hsq]
    have hd := lewkoTiltExcess_diff b h₀ hp
    have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hσ.1) hc
    exact (show lewkoTiltExcess b σ ≤ lewkoTiltExcess b σ₀ by linarith only [h, hd]).trans
      (le_max_left _ _)
  · have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hσ.2 hp.le) (show 0 ≤ 2 * b by positivity)
    have hc : 0 ≤ b - 3 / (2 * σ * B) := by
      apply sub_nonneg.mpr ((div_le_iff₀ (by positivity)).mpr ?_)
      linarith only [hm, lt_of_not_ge hsq]
    have hd := lewkoTiltExcess_diff b hp hB
    have h := mul_nonneg (sub_nonneg.mpr hσ.2) hc
    exact (show lewkoTiltExcess b σ ≤ lewkoTiltExcess b B by linarith only [hd, h]).trans
      (le_max_right _ _)

theorem lewkoTiltExcess_neg_iff {b σ : ℝ} (hσ : 1 / 2 < σ) :
    lewkoTiltExcess b σ < 0 ↔ b < lewkoTiltThreshold σ := by
  have hp : 0 < σ := by linarith
  have hd : 0 < σ * (2 * σ - 1) := mul_pos hp (by linarith)
  have he : lewkoTiltExcess b σ = (b * σ * (2 * σ - 1) - (5 * σ - 3)) / (2 * σ) := by
    unfold lewkoTiltExcess
    field_simp [hp.ne']; ring
  rw [he, div_lt_iff₀ (by positivity), zero_mul, lewkoTiltThreshold, lt_div_iff₀ hd]
  constructor <;> intro h <;> linarith only [h]

theorem lewkoTiltBudget_neg_iff {b σ₀ B : ℝ} (h₀ : 1 / 2 < σ₀) (hB : σ₀ ≤ B) :
    lewkoTiltBudget b σ₀ B < 0 ↔ b < min (lewkoTiltThreshold σ₀) (lewkoTiltThreshold B) := by
  simp only [lewkoTiltBudget, max_lt_iff, lt_min_iff, lewkoTiltExcess_neg_iff h₀,
    lewkoTiltExcess_neg_iff (h₀.trans_le hB)]

private theorem lewkoTilt_count (hL : LewkoDensityHypothesis) {σ₀ B b ε : ℝ}
    (hb : 0 ≤ b) (h₀ : 3 / 4 < σ₀) (_h₀B : σ₀ ≤ B) (hB : B ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Icc σ₀ B,
      rightInclusiveCount T σ * T ^ (b * (σ - 1 / 2)) ≤
        C * T ^ (1 + (lewkoTiltBudget b σ₀ B + ε)) := by
  obtain ⟨C, hC, hc⟩ := uniform_lewko_density_away_from_boundary hL (sub_pos.mpr h₀) hε
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ
  have hTp : 0 < T := by linarith
  have hgt := h₀.trans_le hσ.1
  have h := hc σ ⟨by linarith only [hgt], hσ.2.trans hB⟩
    (Or.inr (by linarith only [hσ.1])) T hT
  have h₁ : ¬ σ ≤ 9 / 13 := by linarith only [hgt]
  have h₂ : ¬ σ ≤ 5 / 7 := by linarith only [hgt]
  simp only [lewkoDensityCoefficient, if_neg h₁, if_neg h₂, if_neg (not_le.mpr hgt)] at h
  have hx := lewkoTiltExcess_le_budget hb (by linarith only [h₀]) hσ
  change 3 / (2 * σ) * (1 - σ) + b * (σ - 1 / 2) - 1 ≤ lewkoTiltBudget b σ₀ B at hx
  calc
    _ ≤ (C * T ^ (3 / (2 * σ) * (1 - σ) + ε)) * T ^ (b * (σ - 1 / 2)) :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hTp.le _)
    _ = C * T ^ ((3 / (2 * σ) * (1 - σ) + ε) + b * (σ - 1 / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hTp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith)
      (by linarith only [hx])) hC.le

private theorem badExp_compact_le {b B σ₀ T K : ℝ} (hZ : ZetaZeroFreeHalfPlane B) (hb : 0 ≤ b)
    (h₀ : 1 / 2 ≤ σ₀) (h₀B : σ₀ ≤ B) (hT : 2 ≤ T)
    (hc : ∀ σ ∈ Icc σ₀ B, rightInclusiveCount T σ * T ^ (b * (σ - 1 / 2)) ≤ K) :
    badWeightedSum T (σ₀ - 1 / 2) (fun t => Real.exp (b * Real.log T * t)) ≤
      2 * K * (1 + b * Real.log T * (B - σ₀)) := by
  have hTp : 0 < T := by linarith
  let ℓ := b * Real.log T
  have hℓ : 0 ≤ ℓ := mul_nonneg hb (Real.log_nonneg (by linarith))
  let δ := σ₀ - 1 / 2
  let D := B - 1 / 2
  have hδ : δ ≤ D := sub_le_sub_right h₀B _
  have hderiv (t : ℝ) : HasDerivAt (fun v => Real.exp (ℓ * v)) (ℓ * Real.exp (ℓ * t)) t := by
    simpa only [Function.comp_def, one_mul, mul_one, mul_comm] using
      (Real.hasDerivAt_exp (ℓ * t)).comp t ((hasDerivAt_id t).const_mul ℓ)
  have ht (t : ℝ) (ht : t ∈ Icc δ D) : strictTail T t * Real.exp (ℓ * t) ≤ 2 * K := by
    have hσ : 1 / 2 + t ∈ Icc σ₀ B := ⟨by dsimp [δ] at ht; linarith only [ht.1],
      by dsimp [D] at ht; linarith only [ht.2]⟩
    have h := hc _ hσ
    rw [show 1 / 2 + t - 1 / 2 = t by ring, Real.rpow_def_of_pos hTp] at h
    have h' := mul_le_mul_of_nonneg_right
      (strictTail_le_twice_inclusive T t (by dsimp [δ] at ht; linarith only [ht.1, h₀]))
      (Real.exp_pos (ℓ * t)).le
    rw [show ℓ * t = Real.log T * (b * t) by dsimp [ℓ]; ring] at h' ⊢
    linarith only [h', h]
  have hI : IntervalIntegrable (fun t => strictTail T t * (ℓ * Real.exp (ℓ * t))) volume δ D :=
    FiniteStrictTail.intervalIntegrable_tail_mul _ _ _ (by fun_prop) _ _
  have hint : (∫ t in δ..D, strictTail T t * (ℓ * Real.exp (ℓ * t))) ≤ ∫ _ in δ..D, ℓ * (2 * K) := by
    apply intervalIntegral.integral_mono_on hδ hI intervalIntegrable_const
    intro t ht'
    calc
      _ = ℓ * (strictTail T t * Real.exp (ℓ * t)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (ht _ ht') hℓ
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hleft := ht δ ⟨le_rfl, hδ⟩
  change badWeightedSum T δ (fun t => Real.exp (ℓ * t)) ≤ 2 * K * (1 + ℓ * (B - σ₀))
  rw [badWeightedSum_layerCake_of_zeroFreeHalfPlane hZ T δ _ _ hδ (by fun_prop) hderiv]
  change _ ≤ (D - δ) * (ℓ * (2 * K)) at hint
  dsimp only [D, δ] at hint hleft ⊢
  linarith only [hint, hleft]

private theorem quarticTilt_le_exp {T σ₀ B b u : ℝ} (hZ : ZetaZeroFreeHalfPlane B)
    (hu : 2 * |u| ≤ b * Real.log T) :
    badWeightedSum T (σ₀ - 1 / 2) (fun t => t ^ 4 * Real.exp (2 * |u| * t)) ≤
      (B - 1 / 2) ^ 4 * badWeightedSum T (σ₀ - 1 / 2) (fun t => Real.exp (b * Real.log T * t)) := by
  classical
  unfold badWeightedSum FiniteStrictTail.badSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hd : 0 ≤ copyDisplacement T c := abs_nonneg _
  have hbd : copyDisplacement T c ≤ B - 1 / 2 := displacement_le_of_zeroFreeHalfPlane hZ c.1.2
  by_cases h : σ₀ - 1 / 2 < copyDisplacement T c
  · simp only [if_pos h]
    exact mul_le_mul (pow_le_pow_left₀ hd hbd 4)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu hd)) (Real.exp_pos _).le
      (pow_nonneg (hd.trans hbd) _)
  · simp only [if_neg h, mul_zero, le_refl]

/-- Every frequency in the allowed window is covered by the same source
constant. The upper horizontal support supplies the fourth power; the
interval length B − σ₀ and the lower endpoint supply the other two terms. -/
theorem farQuarticTilt_over_height_of_lewko (hL : LewkoDensityHypothesis)
    {σ₀ B b ε : ℝ} (hZ : ZetaZeroFreeHalfPlane B) (hb : 0 ≤ b)
    (h₀ : 3 / 4 < σ₀) (h₀B : σ₀ ≤ B) (hB : B ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ u : ℝ, 2 * |u| ≤ b * Real.log T →
      badWeightedSum T (σ₀ - 1 / 2) (fun t => t ^ 4 * Real.exp (2 * |u| * t)) / T ≤
        C * (B - 1 / 2) ^ 4 * T ^ (lewkoTiltBudget b σ₀ B + ε) *
          (1 + b * Real.log T * (B - σ₀)) := by
  obtain ⟨C, hC, hc⟩ := lewkoTilt_count hL hb h₀ h₀B hB hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro T hT u hu
  have hTp : 0 < T := by linarith
  let e := lewkoTiltBudget b σ₀ B + ε
  have h₁ := badExp_compact_le hZ hb (show 1 / 2 ≤ σ₀ by linarith) h₀B hT (hc T hT)
  have h₂ := quarticTilt_le_exp (σ₀ := σ₀) hZ hu
  apply (div_le_iff₀ hTp).mpr
  calc
    _ ≤ _ := h₂.trans (mul_le_mul_of_nonneg_left h₁ (by positivity))
    _ = (2 * C) * (B - 1 / 2) ^ 4 * T ^ e * (1 + b * Real.log T * (B - σ₀)) * T := by
      change (B - 1 / 2) ^ 4 * (2 * (C * T ^ (1 + e)) * (1 + b * Real.log T * (B - σ₀))) = _
      rw [Real.rpow_add hTp, Real.rpow_one]
      ring

/-- In particular the raw Gram's strict far subsum decays by every
power below the two-endpoint margin, uniformly for all frequencies in
the window. No asymptotic constant depends on the frequency. -/
theorem farQuarticTilt_over_height_power_saving (hL : LewkoDensityHypothesis)
    {σ₀ B b : ℝ} (hZ : ZetaZeroFreeHalfPlane B) (hb : 0 ≤ b)
    (h₀ : 3 / 4 < σ₀) (h₀B : σ₀ ≤ B) (hB : B ≤ 1)
    (hthreshold : b < min (lewkoTiltThreshold σ₀) (lewkoTiltThreshold B)) :
    0 < -lewkoTiltBudget b σ₀ B ∧ ∀ η : ℝ, 0 < η → η < -lewkoTiltBudget b σ₀ B →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, 2 * |u| ≤ b * Real.log T →
        badWeightedSum T (σ₀ - 1 / 2) (fun t => t ^ 4 * Real.exp (2 * |u| * t)) / T ≤
          C * T ^ (-η) := by
  let E := lewkoTiltBudget b σ₀ B
  have hE : E < 0 := (lewkoTiltBudget_neg_iff (by linarith only [h₀]) h₀B).mpr hthreshold
  refine ⟨neg_pos.mpr hE, ?_⟩
  intro η _hη hη
  let ε := (-E - η) / 2
  have hε : 0 < ε := div_pos (sub_pos.mpr hη) (by norm_num)
  obtain ⟨C, hC, hc⟩ := farQuarticTilt_over_height_of_lewko hL hZ hb h₀ h₀B hB hε
  let m := b * (B - σ₀)
  have hm : 0 ≤ m := mul_nonneg hb (sub_nonneg.mpr h₀B)
  have hD : 0 < B - 1 / 2 := by linarith only [h₀, h₀B]
  refine ⟨C * (B - 1 / 2) ^ 4 * (1 + m), by positivity, ?_⟩
  have hlog := (isLittleO_log_rpow_atTop hε).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with T hlogT hT
  have hTp : 0 < T := by linarith
  have hT₁ : 1 ≤ T := by linarith
  have hp := Real.one_le_rpow hT₁ hε.le
  change ‖Real.log T‖ ≤ 1 * ‖T ^ ε‖ at hlogT
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT₁),
    abs_of_pos (Real.rpow_pos_of_pos hTp _)] at hlogT
  have hfac : 1 + b * Real.log T * (B - σ₀) ≤ (1 + m) * T ^ ε := by
    have h := mul_le_mul_of_nonneg_left hlogT hm
    change b * (B - σ₀) * Real.log T ≤ b * (B - σ₀) * T ^ ε at h
    dsimp [m]
    linarith only [h, hp]
  intro u hu
  calc
    _ ≤ _ := hc T hT u hu
    _ ≤ C * (B - 1 / 2) ^ 4 * T ^ (E + ε) * ((1 + m) * T ^ ε) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = C * (B - 1 / 2) ^ 4 * (1 + m) * (T ^ (E + ε) * T ^ ε) := by ring
    _ = _ := by
      rw [← Real.rpow_add hTp, show E + ε + ε = -η by dsimp [ε]; ring]

/-- Concrete frequency threshold at the abscissa 4/5. -/
theorem lewkoTiltThreshold_four_fifths : lewkoTiltThreshold (4 / 5) = 25 / 12 := by
  norm_num [lewkoTiltThreshold]

/-- Rational enclosure of the limiting far-support weight. The root itself
is isolated to forty decimals in ActualQuasiRiemannSupport. -/
theorem lewkoTiltThreshold_continuumContact_bounds :
    (2095824456292 / 10^12 : ℝ) < lewkoTiltThreshold continuumContact ∧
      lewkoTiltThreshold continuumContact < (2095824456293 / 10^12 : ℝ) := by
  let lo := (8733458561067185768 / 10^19 : ℝ)
  let hi := (8733458561067185769 / 10^19 : ℝ)
  have hl : lo ≤ continuumContact := by
    rw [continuumContact, ContinuumContact.contact_eq]
    have h := ContinuumContact.theta_isolated.1
    dsimp [lo, ContinuumContact.lower] at *
    linarith only [h]
  have hu : continuumContact ≤ hi := by
    have h := continuumContact_lt_rational
    dsimp [hi]
    linarith only [h]
  have hℓ : 0 ≤ lo := by norm_num [lo]
  have hθ := hℓ.trans hl
  have hlow := mul_self_le_mul_self hℓ hl
  have hupp := mul_self_le_mul_self hθ hu
  have hd : 0 < continuumContact * (2 * continuumContact - 1) := by
    have h := continuumContact_mem.1
    exact mul_pos (by linarith only [h]) (by linarith only [h])
  unfold lewkoTiltThreshold
  rw [lt_div_iff₀ hd, div_lt_iff₀ hd]
  dsimp [lo, hi] at hl hu hlow hupp
  constructor <;> nlinarith only [hl, hu, hlow, hupp]

theorem lewkoTiltFrequency_four_fifths :
    min (lewkoTiltThreshold (4 / 5)) (lewkoTiltThreshold continuumContact) / 2 = 25 / 24 := by
  have h := lewkoTiltThreshold_continuumContact_bounds.1
  rw [lewkoTiltThreshold_four_fifths, min_eq_left (by linarith only [h])]
  norm_num

end RiemannResearch.Analysis.ActualZeroOrdinate
