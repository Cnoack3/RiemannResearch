/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ScalarPrefixDensityTail
import RiemannResearch.RH.ArithmeticFloorPowerConvergence
import RiemannResearch.RH.ArithmeticFloorLogConvergence

/-!
# Full Hilbert convergence from one scalar cancellation estimate

The independent density-tail estimate in the power and critical logarithmic
criteria is derived by reciprocal Abel summation. The scalar signed prefix
bound remains an OPEN arithmetic input at every subhalf damping.
-/

noncomputable section
open Filter RiemannResearch.Analysis
open scoped Topology
namespace RiemannResearch.RH.Pareto

/-- A single signed prefix power bound gives full natural-order Hilbert
convergence. Reciprocal Abel supplies the entire missing density estimate. -/
theorem arithmeticFloorHilbertPartial_tendsto_of_prefix_power
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m+1)/((m+1 : ℕ) : ℝ)) C)
    {W B ε a : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (ha : 0 ≤ a) (haε : a < ε)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W*(t : ℝ)^(-ε))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤ B*(t : ℝ)^a) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = arithmeticFloorPrefix w n-(n : ℝ)*C) ∧
      Tendsto (arithmeticFloorHilbertPartial w) atTop (𝓝 f) := by
  have ha1 : a < 1 := by linarith
  have hp : 0 < 1-a := by linarith
  apply arithmeticFloorHilbertPartial_tendsto_of_prefix_density_powers
    w hw0 C hdensity (d := 1-a) (D := (2+1/(1-a))*B)
    hW hB (by positivity) hε hεhalf ha haε (by linarith) hw hP
  intro t ht
  simpa only [show -(1-a) = a-1 by ring] using
    reciprocal_density_tail_bound_of_prefix_power w hw0 C hdensity hB ha ha1 hP ht

/-- At the critical power, one logarithmic prefix saving exceeding one
suffices; the complementary density logarithm is a conclusion. -/
theorem arithmeticFloorHilbertPartial_tendsto_of_critical_prefix_log
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m+1)/((m+1 : ℕ) : ℝ)) C)
    {W B ε b c : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hb : 1 < b)
    (hc : 6 ≤ c) (hbc : b ≤ ε*c)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W*(t : ℝ)^(-ε))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B*(t : ℝ)^ε/(c+Real.log (t : ℝ))^b) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = arithmeticFloorPrefix w n-(n : ℝ)*C) ∧
      Tendsto (arithmeticFloorHilbertPartial w) atTop (𝓝 f) := by
  have hε1 : ε < 1 := by linarith
  have hp : 0 < 1-ε := by linarith
  apply arithmeticFloorHilbertPartial_tendsto_of_critical_log_bounds
    w hw0 C hdensity (D := (2+1/(1-ε))*B)
    hW hB (by positivity) hε hεhalf hb hc hbc hw hP
  intro t ht
  exact reciprocal_density_tail_bound_of_prefix_log w hw0 C hdensity
    hB hε.le hε1 (by linarith) (by linarith) hbc hP ht

/-- Möbius specialization with one OPEN scalar prefix-power input. -/
theorem dampedMobius_cutoffs_converge_of_prefix_power
    {ε a B : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (ha : 0 ≤ a) (haε : a < ε) (hB : 0 ≤ B)
    (hP : ∀ t : ℕ, 0 < t →
      |positiveArithmeticPrefix (dampedMobiusWeight ε) t| ≤ B*(t : ℝ)^a) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = dampedMobiusPrefix ε n-
        (n : ℝ)*(1/riemannZeta (1+(ε : ℂ))).re) ∧
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  apply arithmeticFloorHilbertPartial_tendsto_of_prefix_power
    (dampedMobiusWeight ε) (dampedMobiusWeight_zero ε) _
    (dampedMobius_density_hasSum hε) (W := 1)
    (by norm_num) hB hε hεhalf ha haε _ hP
  intro t ht
  rw [dampedMobiusWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := t)))
    (Real.rpow_nonneg (Nat.cast_nonneg t) _)

/-- Möbius specialization with one OPEN critical logarithmic prefix input. -/
theorem dampedMobius_cutoffs_converge_of_critical_prefix_log
    {ε b c B : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (hb : 1 < b) (hc : 6 ≤ c) (hbc : b ≤ ε*c) (hB : 0 ≤ B)
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix (dampedMobiusWeight ε) t| ≤
      B*(t : ℝ)^ε/(c+Real.log (t : ℝ))^b) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = dampedMobiusPrefix ε n-
        (n : ℝ)*(1/riemannZeta (1+(ε : ℂ))).re) ∧
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  apply arithmeticFloorHilbertPartial_tendsto_of_critical_prefix_log
    (dampedMobiusWeight ε) (dampedMobiusWeight_zero ε) _
    (dampedMobius_density_hasSum hε) (W := 1)
    (by norm_num) hB hε hεhalf hb hc hbc _ hP
  intro t ht
  rw [dampedMobiusWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := t)))
    (Real.rpow_nonneg (Nat.cast_nonneg t) _)

end RiemannResearch.RH.Pareto
