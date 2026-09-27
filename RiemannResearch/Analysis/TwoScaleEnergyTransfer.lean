/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Transfer of normalized energy through two cutoffs

An approximation at conductor cutoff M has vanishing normalized energy.
Its scalar error on physical head H is at most C * H * M^(-q).
Choosing M = k * (H + 1) + H first with fixed k, then increasing k, transfers
the normalized limit to the actual head energy.

Source: the explicit elementary two-scale argument developed in this
session. The arithmetic consumer is DampedMobiusCenteredHeadGrowth.
No mathematical novelty claim is made.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis

/-- The scalar error at a multiple of the head scale has an exact normalization. -/
theorem linear_inverse_power_normalization {x k : ℝ}
    (hx : 0 < x) (hk : 0 < k) (q : ℝ) :
    x * (k * x) ^ (-q) / x ^ (1 - q) = k ^ (-q) := by
  rw [Real.mul_rpow hk.le hx.le]
  have he : x * x ^ (-q) = x ^ (1 - q) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ (-q) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx]; congr 1
  calc
    _ = k ^ (-q) * (x * x ^ (-q)) / x ^ (1 - q) := by ring
    _ = k ^ (-q) := by rw [he]; field_simp

/-- A fixed affine dilation of the cutoff preserves vanishing normalized growth. -/
theorem affine_cutoff_normalized_tendsto
    (A : ℕ → ℝ) (p : ℝ)
    (hA : Tendsto (fun M : ℕ => A M / ((M + 1 : ℕ) : ℝ) ^ p) atTop (𝓝 0))
    (k : ℕ) :
    Tendsto (fun H : ℕ => A (k * (H + 1) + H) /
      ((H + 1 : ℕ) : ℝ) ^ p) atTop (𝓝 0) := by
  have hM : Tendsto (fun H : ℕ => k * (H + 1) + H) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop n] with H hH
    omega
  have h := (hA.comp hM).const_mul (((k + 1 : ℕ) : ℝ) ^ p)
  simp only [mul_zero] at h
  convert h using 1
  funext H
  change A (k * (H + 1) + H) / ((H + 1 : ℕ) : ℝ) ^ p =
    ((k + 1 : ℕ) : ℝ) ^ p *
      (A (k * (H + 1) + H) / (((k * (H + 1) + H) + 1 : ℕ) : ℝ) ^ p)
  have hid : (((k * (H + 1) + H) + 1 : ℕ) : ℝ) =
      ((k + 1 : ℕ) : ℝ) * ((H + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hid, Real.mul_rpow (by positivity) (by positivity)]
  field_simp

/-- A two-scale approximation transfers vanishing normalized cutoff energy
to the target head energy. Only the scalar approximation error is assumed. -/
theorem two_scale_energy_tendsto_zero
    (E A : ℕ → ℝ) {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q)
    (hE : ∀ H, 0 ≤ E H)
    (hA : Tendsto (fun M : ℕ => A M /
      ((M + 1 : ℕ) : ℝ) ^ (1 - q)) atTop (𝓝 0))
    (hcompare : ∀ H M : ℕ, H ≤ M → 1 ≤ M →
      E H ≤ A M + C * (H : ℝ) * (M : ℝ) ^ (-q)) :
    Tendsto (fun H : ℕ => E H /
      ((H + 1 : ℕ) : ℝ) ^ (1 - q)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun H => ha.trans_le
      (div_nonneg (hE H) (Real.rpow_nonneg (by positivity) _)))
  · intro η hη
    have hkLim : Tendsto (fun k : ℕ => C * (k : ℝ) ^ (-q)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero] using
        ((tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop).const_mul C
    obtain ⟨k, hk, hsmall⟩ := ((eventually_ge_atTop (1 : ℕ)).and
      ((tendsto_order.mp hkLim).2 (η / 2) (by positivity))).exists
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hs := affine_cutoff_normalized_tendsto A (1 - q) hA k
    filter_upwards [(tendsto_order.mp hs).2 (η / 2) (by positivity),
      eventually_ge_atTop (1 : ℕ)] with H hH hH1
    have hM1 : 1 ≤ k * (H + 1) + H := by omega
    have hHM : H ≤ k * (H + 1) + H := by omega
    have hx : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
    have hbase : (k : ℝ) * ((H + 1 : ℕ) : ℝ) ≤
        ((k * (H + 1) + H : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) H]
    have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hk0 hx) hbase (by linarith : -q ≤ 0)
    have herr : C * (H : ℝ) * ((k * (H + 1) + H : ℕ) : ℝ) ^ (-q) /
        ((H + 1 : ℕ) : ℝ) ^ (1 - q) ≤ C * (k : ℝ) ^ (-q) := by
      calc
        _ ≤ C * ((H + 1 : ℕ) : ℝ) *
            ((k : ℝ) * ((H + 1 : ℕ) : ℝ)) ^ (-q) /
              ((H + 1 : ℕ) : ℝ) ^ (1 - q) := by
          apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ H) hC
          · exact hpow
          · exact Real.rpow_nonneg (by positivity) _
          · positivity
        _ = C * (k : ℝ) ^ (-q) := by
          rw [mul_assoc, mul_div_assoc, linear_inverse_power_normalization hx hk0]
    have hb := div_le_div_of_nonneg_right (hcompare H _ hHM hM1)
      (Real.rpow_nonneg hx.le (1 - q))
    rw [add_div] at hb
    linarith

end RiemannResearch.Analysis
