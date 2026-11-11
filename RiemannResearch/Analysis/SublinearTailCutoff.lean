import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A sublinear physical cutoff for a decreasing tail envelope

Source: user-provided short-head localization argument, 10 November 2026.
The envelope tends to zero; no rate and no vanishing total residual are assumed.
All floor, ceiling, and small-head conventions are explicit.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.SublinearTailCutoff

def baseHead (H : ℕ) : ℕ := ⌊Real.sqrt (H : ℝ)⌋₊

def cutoff (ρ : ℕ → ℝ) (H : ℕ) : ℕ :=
  ⌈max (Real.sqrt (H : ℝ)) ((H : ℝ) * Real.sqrt (ρ (baseHead H)))⌉₊

@[simp] theorem cutoff_zero (ρ : ℕ → ℝ) : cutoff ρ 0 = 0 := by
  simp [cutoff]

theorem sqrt_le_cutoff (ρ : ℕ → ℝ) (H : ℕ) :
    Real.sqrt (H : ℝ) ≤ (cutoff ρ H : ℝ) :=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem scaled_sqrt_le_cutoff (ρ : ℕ → ℝ) (H : ℕ) :
    (H : ℝ) * Real.sqrt (ρ (baseHead H)) ≤ (cutoff ρ H : ℝ) :=
  (le_max_right _ _).trans (Nat.le_ceil _)

theorem baseHead_le_cutoff (ρ : ℕ → ℝ) (H : ℕ) :
    baseHead H ≤ cutoff ρ H := by
  exact_mod_cast (Nat.floor_le (Real.sqrt_nonneg (H : ℝ))).trans
    (sqrt_le_cutoff ρ H)

theorem cutoff_pos (ρ : ℕ → ℝ) {H : ℕ} (hH : 0 < H) :
    0 < cutoff ρ H := by
  have h := (Real.sqrt_pos.mpr (show (0 : ℝ) < H by exact_mod_cast hH)).trans_le
    (sqrt_le_cutoff ρ H)
  exact_mod_cast h

theorem cutoff_upper (ρ : ℕ → ℝ) (H : ℕ) :
    (cutoff ρ H : ℝ) ≤ Real.sqrt H +
      (H : ℝ) * Real.sqrt (ρ (baseHead H)) + 1 := by
  have hm : 0 ≤ max (Real.sqrt (H : ℝ))
      ((H : ℝ) * Real.sqrt (ρ (baseHead H))) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hc := (Nat.ceil_lt_add_one hm).le
  have hmax : max (Real.sqrt (H : ℝ))
      ((H : ℝ) * Real.sqrt (ρ (baseHead H))) ≤
      Real.sqrt H + (H : ℝ) * Real.sqrt (ρ (baseHead H)) :=
    max_le (le_add_of_nonneg_right (by positivity))
      (le_add_of_nonneg_left (Real.sqrt_nonneg _))
  exact hc.trans (add_le_add hmax le_rfl)

theorem baseHead_tendsto : Tendsto baseHead atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

private theorem sqrt_ratio (H : ℕ) :
    Real.sqrt (H : ℝ) / H = (Real.sqrt (H : ℝ))⁻¹ := by
  by_cases hH : H = 0
  · simp [hH]
  have hp : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hs := Real.sq_sqrt hp.le
  field_simp [ne_of_gt hp, ne_of_gt (Real.sqrt_pos.mpr hp)]
  nlinarith

theorem cutoff_sublinear (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop (𝓝 0)) :
    Tendsto (fun H => (cutoff ρ H : ℝ) / H) atTop (𝓝 0) := by
  have hs : Tendsto (fun H : ℕ => Real.sqrt (H : ℝ) / H) atTop (𝓝 0) := by
    simp_rw [sqrt_ratio]
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hr : Tendsto (fun H => Real.sqrt (ρ (baseHead H))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hρ.comp baseHead_tendsto)
  have hi : Tendsto (fun H : ℕ => (1 : ℝ) / H) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hu := (hs.add hr).add hi
  simp only [zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall (fun H => by positivity)) _ hu
  filter_upwards [eventually_ge_atTop 1] with H hH
  have hp : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH)
  calc
    (cutoff ρ H : ℝ) / H ≤
        (Real.sqrt H + (H : ℝ) * Real.sqrt (ρ (baseHead H)) + 1) / H :=
      div_le_div_of_nonneg_right (cutoff_upper ρ H) hp.le
    _ = _ := by field_simp

theorem cutoff_eventually_le_head (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∀ᶠ H in atTop, cutoff ρ H ≤ H := by
  filter_upwards [(cutoff_sublinear ρ hρ).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with H hcut hH
  have hp : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH)
  have h := (div_lt_iff₀ hp).mp hcut
  exact_mod_cast (by linarith : (cutoff ρ H : ℝ) ≤ H)

theorem cutoff_tendsto (ρ : ℕ → ℝ) :
    Tendsto (cutoff ρ) atTop atTop :=
  tendsto_atTop_mono (baseHead_le_cutoff ρ) baseHead_tendsto

/-- The precise normalized tail factor, including the H=0 convention. -/
theorem normalized_tail_le (ρ : ℕ → ℝ)
    (hρ0 : ∀ A, 0 ≤ ρ A) (hρmono : Antitone ρ) (H : ℕ) :
    (H : ℝ) * ρ (cutoff ρ H) /
        Real.sqrt (((cutoff ρ H : ℝ) + 1) * ((cutoff ρ H : ℝ) + 2)) ≤
      Real.sqrt (ρ (baseHead H)) := by
  have hr := hρmono (baseHead_le_cutoff ρ H)
  have hs := Real.sq_sqrt (hρ0 (baseHead H))
  have ha := scaled_sqrt_le_cutoff ρ H
  have hd : (cutoff ρ H : ℝ) ≤
      Real.sqrt (((cutoff ρ H : ℝ) + 1) * ((cutoff ρ H : ℝ) + 2)) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    nlinarith [show (0 : ℝ) ≤ cutoff ρ H by positivity]
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    (H : ℝ) * ρ (cutoff ρ H) ≤ (H : ℝ) * ρ (baseHead H) :=
      mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg H)
    _ = ((H : ℝ) * Real.sqrt (ρ (baseHead H))) *
        Real.sqrt (ρ (baseHead H)) := by rw [mul_assoc, ← pow_two, hs]
    _ ≤ (cutoff ρ H : ℝ) * Real.sqrt (ρ (baseHead H)) :=
      mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)
    _ ≤ _ := by
      have hh := mul_le_mul hd le_rfl (Real.sqrt_nonneg (ρ (baseHead H)))
        (by positivity : (0 : ℝ) ≤ Real.sqrt (((cutoff ρ H : ℝ) + 1) * ((cutoff ρ H : ℝ) + 2)))
      nlinarith

theorem normalized_tail_tendsto_zero (ρ : ℕ → ℝ)
    (hρ0 : ∀ A, 0 ≤ ρ A) (hρmono : Antitone ρ)
    (hρ : Tendsto ρ atTop (𝓝 0)) :
    Tendsto (fun H : ℕ => (H : ℝ) * ρ (cutoff ρ H) /
      Real.sqrt (((cutoff ρ H : ℝ) + 1) * ((cutoff ρ H : ℝ) + 2)))
      atTop (𝓝 0) := by
  have hr : Tendsto (fun H => Real.sqrt (ρ (baseHead H))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hρ.comp baseHead_tendsto)
  exact squeeze_zero (fun H => div_nonneg
    (mul_nonneg (Nat.cast_nonneg H) (hρ0 _)) (Real.sqrt_nonneg _))
    (normalized_tail_le ρ hρ0 hρmono) hr

end RiemannResearch.Analysis.SublinearTailCutoff
