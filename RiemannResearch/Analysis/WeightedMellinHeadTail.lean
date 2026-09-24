import RiemannResearch.Analysis.WeightedMellinEnergy
import Mathlib.Tactic.FieldSimp

/-!
# Exact weighted head-tail identities and logarithmic scheduling

Source: the user's September 24, 2026 request to quantify the moving Hardy
bound after commit e2518b1. These elementary integral identities refine the
existing exact-head argument. No arithmetic or RH assumption is used.
The defect records exactly the loss from freezing the tail weight at the cutoff.
The RH consumer is `RH/ExactHeadWeightedEnergy` and its moving-boundary assembly.
-/


set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace MeasureTheory.WeightedMellin

/-- Exact energy removed by a head on which the function equals one. -/
theorem energy_sub_tail_of_exact_head {f : ℝ → ℂ} {b u : ℝ}
    (hf : FiniteEnergy f 1) (hb : 1 ≤ b) (hu : 1 ≤ u)
    (hhead : ∀ᵐ x ∂volume.restrict (Ioc 1 b), f x = 1) :
    energy f u - (∫ x in Ioi b, ‖f x‖ ^ 2 * x ^ (-u - 1)) =
      (1 - b ^ (-u)) / u := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (-u - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hpow (a : ℝ) (ha : 0 < a) :
      (∫ x in Ioi a, x ^ (-u - 1)) = a ^ (-u) / u := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -u - 1 < -1) ha]
    rw [show -u - 1 + 1 = -u by ring]
    ring
  have heq : (∫ x in (1 : ℝ)..b, ‖f x‖ ^ 2 * x ^ (-u - 1)) =
      ∫ x in (1 : ℝ)..b, x ^ (-u - 1) := by
    rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb]
    apply integral_congr_ae
    filter_upwards [hhead] with x hx
    simp only [hx, norm_one, one_pow, one_mul]
  calc
    _ = ∫ x in (1 : ℝ)..b, ‖f x‖ ^ 2 * x ^ (-u - 1) :=
      intervalIntegral.integral_Ioi_sub_Ioi (finiteEnergy_mono hf hu).2 hb
    _ = ∫ x in (1 : ℝ)..b, x ^ (-u - 1) := heq
    _ = (∫ x in Ioi (1 : ℝ), x ^ (-u - 1)) -
        ∫ x in Ioi b, x ^ (-u - 1) :=
      (intervalIntegral.integral_Ioi_sub_Ioi hp hb).symm
    _ = _ := by rw [hpow 1 zero_lt_one, hpow b (lt_of_lt_of_le zero_lt_one hb),
        Real.one_rpow]; ring

/-- The complete critical tail controls every more strongly weighted tail. -/
theorem energy_tail_le_power_mul {f : ℝ → ℂ} {b u : ℝ}
    (hf : FiniteEnergy f 1) (hb : 1 ≤ b) (hu : 1 ≤ u) :
    (∫ x in Ioi b, ‖f x‖ ^ 2 * x ^ (-u - 1)) ≤
      b ^ (1 - u) * (∫ x in Ioi b, ‖f x‖ ^ 2 * x ^ (-(1 : ℝ) - 1)) := by
  have hsub : Ioi b ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi hb
  rw [← integral_const_mul]
  apply integral_mono_ae ((finiteEnergy_mono hf hu).2.mono_set hsub)
    ((hf.2.mono_set hsub).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hx0 : 0 < x := hb0.trans hx
  have hr : x ^ (1 - u) ≤ b ^ (1 - u) :=
    Real.rpow_le_rpow_of_nonpos hb0 hx.le (by linarith)
  calc
    _ = (‖f x‖ ^ 2 * x ^ (-(1 : ℝ) - 1)) * x ^ (1 - u) := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2 <;> ring
    _ ≤ (‖f x‖ ^ 2 * x ^ (-(1 : ℝ) - 1)) * b ^ (1 - u) :=
      mul_le_mul_of_nonneg_left hr
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx0.le _))
    _ = _ := by ring

/-- Sharp head-tail estimate: the exact head costs its actual power integral. -/
theorem energy_le_exact_head_add_power_tail {f : ℝ → ℂ} {b u : ℝ}
    (hf : FiniteEnergy f 1) (hb : 1 ≤ b) (hu : 1 ≤ u)
    (hhead : ∀ᵐ x ∂volume.restrict (Ioc 1 b), f x = 1) :
    energy f u ≤ (1 - b ^ (-u)) / u +
      b ^ (1 - u) * (energy f 1 - 1 + 1 / b) := by
  have h1 := energy_sub_tail_of_exact_head hf hb (le_refl (1 : ℝ)) hhead
  have hu' := energy_sub_tail_of_exact_head hf hb hu hhead
  have ht := energy_tail_le_power_mul hf hb hu
  have he1 : (∫ x in Ioi b, ‖f x‖ ^ 2 * x ^ (-(1 : ℝ) - 1)) =
      energy f 1 - 1 + 1 / b := by
    simp only [Real.rpow_neg_one, div_one] at h1
    rw [one_div]
    linarith
  rw [he1] at ht
  linarith

/-- Exact nonnegative loss incurred by replacing every tail weight by its
value at the cutoff. -/
def headTailWeightDefect (f : ℝ → ℂ) (b u : ℝ) : ℝ :=
  ∫ x in Ioi b, b ^ (1 - u) * (‖f x‖ ^ 2 * x ^ (-(1 : ℝ) - 1)) -
    ‖f x‖ ^ 2 * x ^ (-u - 1)

theorem headTailWeightDefect_eq {f : ℝ → ℂ} {b u : ℝ}
    (hf : FiniteEnergy f 1) (hb : 1 ≤ b) (hu : 1 ≤ u) :
    headTailWeightDefect f b u =
      b ^ (1 - u) * (∫ x in Ioi b, ‖f x‖ ^ 2 * x ^ (-(1 : ℝ) - 1)) -
        ∫ x in Ioi b, ‖f x‖ ^ 2 * x ^ (-u - 1) := by
  have hsub : Ioi b ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi hb
  rw [headTailWeightDefect, integral_sub ((hf.2.mono_set hsub).const_mul _)
    ((finiteEnergy_mono hf hu).2.mono_set hsub), integral_const_mul]

theorem headTailWeightDefect_nonneg {f : ℝ → ℂ} {b u : ℝ}
    (hf : FiniteEnergy f 1) (hb : 1 ≤ b) (hu : 1 ≤ u) :
    0 ≤ headTailWeightDefect f b u := by
  rw [headTailWeightDefect_eq hf hb hu]
  exact sub_nonneg.mpr (energy_tail_le_power_mul hf hb hu)

/-- Exact equality refining the sharp head-tail inequality. -/
theorem energy_eq_exact_head_add_power_tail_sub_defect {f : ℝ → ℂ} {b u : ℝ}
    (hf : FiniteEnergy f 1) (hb : 1 ≤ b) (hu : 1 ≤ u)
    (hhead : ∀ᵐ x ∂volume.restrict (Ioc 1 b), f x = 1) :
    energy f u = (1 - b ^ (-u)) / u +
      b ^ (1 - u) * (energy f 1 - 1 + 1 / b) - headTailWeightDefect f b u := by
  have h1 := energy_sub_tail_of_exact_head hf hb (le_refl (1 : ℝ)) hhead
  have hu' := energy_sub_tail_of_exact_head hf hb hu hhead
  simp only [Real.rpow_neg_one, div_one] at h1
  have he1 : (∫ x in Ioi b, ‖f x‖ ^ 2 * x ^ (-(1 : ℝ) - 1)) =
      energy f 1 - 1 + 1 / b := by
    rw [one_div]
    linarith
  rw [headTailWeightDefect_eq hf hb hu, he1]
  linarith

end MeasureTheory.WeightedMellin


noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace MeasureTheory.WeightedMellin

theorem energy_le_power_mul_of_zero_head {f : ℝ → ℂ}
    (hf : FiniteEnergy f 1) {u b : ℝ} (hu : 1 ≤ u) (hb : 1 ≤ b)
    (hhead : ∀ x, 1 < x → x < b → f x = 0) :
    energy f u ≤ b ^ (1-u) * energy f 1 := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hi := (finiteEnergy_mono hf hu).2
  have hj := hf.2.const_mul (b ^ (1-u))
  calc
    energy f u ≤ ∫ x in Ioi (1 : ℝ),
        b ^ (1-u) * (‖f x‖^2 * x^(-(1 : ℝ)-1)) := by
      apply integral_mono_ae hi hj
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      by_cases hxb : x < b
      · simp [hhead x hx hxb]
      · have hp : x^(1-u) ≤ b^(1-u) :=
          Real.rpow_le_rpow_of_nonpos hb0 (le_of_not_gt hxb) (by linarith)
        have he : x^(-u-1) = x^(1-u) * x^(-(1 : ℝ)-1) := by
          rw [← Real.rpow_add hx0]
          congr 1
          ring
        rw [he]
        nlinarith [mul_le_mul_of_nonneg_right hp
          (mul_nonneg (sq_nonneg ‖f x‖) (Real.rpow_nonneg hx0.le (-(1 : ℝ)-1)))]
    _ = b ^ (1-u) * energy f 1 := by rw [integral_const_mul]; rfl
end MeasureTheory.WeightedMellin



set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace MeasureTheory.WeightedMellin

/-- Exact logarithmic scheduling of the cutoff suppression factor. -/
theorem cutoff_power_log_schedule {b q θ : ℝ} (hb : 1 < b) (hq : 0 < q) :
    b ^ (1 - (2 + θ * Real.log q / Real.log b)) = b⁻¹ * q ^ (-θ) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hl : Real.log b ≠ 0 := (Real.log_pos hb).ne'
  calc
    _ = Real.exp (-Real.log b + Real.log q * (-θ)) := by
      rw [Real.rpow_def_of_pos hb0]
      congr 1
      field_simp [hl]
      <;> ring
    _ = _ := by
      rw [Real.exp_add, Real.exp_neg, Real.exp_log hb0, Real.rpow_def_of_pos hq]

/-- A ceiling q between 1/b and 1 places the scheduled energy exponent
between the critical exponent 1 and the known endpoint exponent 2. -/
theorem log_schedule_mem_Icc {b q θ : ℝ} (hb : 1 < b)
    (hq0 : 0 < q) (hql : b⁻¹ ≤ q) (hqu : q ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 ≤ 2 + θ * Real.log q / Real.log b ∧
      2 + θ * Real.log q / Real.log b ≤ 2 := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hl : 0 < Real.log b := Real.log_pos hb
  have hlq : Real.log q ≤ 0 := Real.log_nonpos hq0.le hqu
  have hlo : -Real.log b ≤ Real.log q := by
    simpa only [Real.log_inv] using Real.log_le_log (inv_pos.mpr hb0) hql
  have hm : -Real.log b ≤ θ * Real.log q := by
    have hmul := mul_le_mul_of_nonpos_right hθ1 hlq
    linarith
  constructor
  · have hd : -1 ≤ θ * Real.log q / Real.log b :=
      (le_div_iff₀ hl).2 (by linarith)
    linarith
  · have hd : θ * Real.log q / Real.log b ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hθ0 hlq) hl.le
    linarith

/-- A normalized energy ceiling q converts exactly to a fractional-power
ceiling at the logarithmically scheduled exponent. -/
theorem cutoff_power_times_energy_le {b q θ E : ℝ}
    (hb : 1 < b) (hq : 0 < q) (hE : E ≤ b * q) :
    b ^ (1 - (2 + θ * Real.log q / Real.log b)) * E ≤ q ^ (1 - θ) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  rw [cutoff_power_log_schedule hb hq]
  calc
    _ ≤ (b⁻¹ * q ^ (-θ)) * (b * q) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = q ^ (-θ) * q := by field_simp [hb0.ne']
    _ = q ^ (-θ) * q ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = q ^ (1 - θ) := by
      rw [← Real.rpow_add hq]
      congr 1
      ring

end MeasureTheory.WeightedMellin
