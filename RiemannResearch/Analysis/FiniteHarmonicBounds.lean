/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite harmonic interval and fixed-ratio cutoff bounds

Source: the elementary finite harmonic-sum estimates used in the resonance-cell
continuation of Christian Noack's RH research. These bounds provide uniform
arithmetic remainders without invoking any limiting zero-distribution claim.
-/
namespace RiemannResearch.Analysis
open Filter
open scoped BigOperators Topology

/-- The real harmonic sum in its zero-based finite form. -/
theorem harmonic_cast_range (n : ℕ) :
    (harmonic n:ℝ) = ∑ j ∈ Finset.range n, 1/((j:ℝ)+1) := by
  simp [harmonic, one_div]

/-- The whole finite interval has the elementary reciprocal lower-end bound. -/
theorem harmonic_interval_bounds (m n : ℕ) (hmn : m ≤ n) :
    0 ≤ (harmonic n:ℝ)-(harmonic m:ℝ) ∧
    (harmonic n:ℝ)-(harmonic m:ℝ) ≤ ((n-m:ℕ):ℝ)/((m:ℝ)+1) := by
  have he : (harmonic n:ℝ)-(harmonic m:ℝ) =
      ∑ j ∈ Finset.range (n-m), 1/(((m+j:ℕ):ℝ)+1) := by
    rw [harmonic_cast_range n, harmonic_cast_range m]
    conv_lhs => rw [show n=m+(n-m) by omega, Finset.sum_range_add]
    ring
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun j _ => by positivity)
  · calc
      _ ≤ ∑ _j ∈ Finset.range (n-m), 1/((m:ℝ)+1) := by
        apply Finset.sum_le_sum
        intro j hj
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith [Nat.cast_nonneg (α:=ℝ) j]
      _ = _ := by simp [div_eq_mul_inv]

theorem harmonic_nonnegative (n : ℕ) : 0 ≤ (harmonic n:ℝ) := by
  rw [harmonic_cast_range]
  exact Finset.sum_nonneg (fun j _ => by positivity)

theorem harmonic_le_index (n : ℕ) : (harmonic n:ℝ) ≤ (n:ℝ) := by
  simpa [harmonic] using (harmonic_interval_bounds 0 n (by omega)).2

/-- The fixed cutoff used in the finite resonance calculations loses at most12. -/
theorem harmonic_twelfth_gap (k : ℕ) :
    |(harmonic k:ℝ)-(harmonic (k/12):ℝ)| ≤ 12 := by
  have ht : k/12 ≤ k := by omega
  have h := harmonic_interval_bounds (k/12) k ht
  rw [abs_of_nonneg h.1]
  apply h.2.trans
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(k/12:ℕ)+1)).mpr
  have hn : k-k/12 ≤ 12*(k/12+1) := by omega
  exact_mod_cast hn

/-- A bounded dilation ratio loses at most that ratio in harmonic mass. -/
theorem harmonic_bounded_ratio_gap (k m a : ℕ) (hkm : k ≤ m) (hma : m ≤ a*k) :
    |(harmonic m:ℝ)-(harmonic k:ℝ)| ≤ (a:ℝ) := by
  have h := harmonic_interval_bounds k m hkm
  rw [abs_of_nonneg h.1]
  apply h.2.trans
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+1)).mpr
  have hn : m-k ≤ a*(k+1) :=
    (Nat.sub_le m k).trans (hma.trans (Nat.mul_le_mul_left a (Nat.le_succ k)))
  exact_mod_cast hn

/-- The accumulated reciprocal weights remain negligible against the
square-root accuracy supplied by the certified arithmetic cutoffs. -/
theorem harmonic_over_sqrt_succ_tendsto_zero :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.sqrt ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ =>
      Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (show 0 < (1 / (2 : ℝ)) by norm_num)).tendsto_div_nhds_zero).comp hn
  have hinv : Tendsto (fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have hupper : Tendsto (fun n : ℕ =>
      (1 + Real.log ((n : ℝ) + 1)) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hinv.add hlog
  apply squeeze_zero _ _ hupper
  · intro n
    have hh : 0 ≤ (harmonic n : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      positivity
    exact div_nonneg hh (Real.sqrt_nonneg _)
  · intro n
    have hmono : (harmonic n : ℝ) ≤ (harmonic (n + 1) : ℝ) := by
      rw [harmonic_succ, Rat.cast_add]
      exact le_add_of_nonneg_right (by positivity)
    have hb : (harmonic n : ℝ) ≤ 1 + Real.log ((n : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hmono.trans (harmonic_le_one_add_log (n + 1))
    exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg _)


end RiemannResearch.Analysis
