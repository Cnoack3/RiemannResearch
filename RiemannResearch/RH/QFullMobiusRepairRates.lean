/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullReciprocalRepairBudget
import RiemannResearch.RH.QMobiusStretchedEnergy
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.LogFloorConvolution
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic logarithmic savings for the explicit reciprocal repair

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 3.
All inputs are the repository's established complete Möbius-head energy
providers. The estimates hold for every input vector, with one constant
depending only on the chosen logarithmic exponent. They are growth bounds;
the actual residual-tail product remains an additional open obligation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFullDilatedMobiusRepair
open ZetaTwoHilbert ZetaTwoProbability QMobiusExactHead
open RiemannResearch.Analysis.LogFloorConvolution

/-- Exact agreement between the indexed repair budget and its arithmetic floor convolution. -/
theorem dilationBudget_eq_floorConvolution (N : ℕ) :
    dilationBudget N = floorConvolution (fun n => ‖exactHead n‖ ^ 2) N := by
  classical
  unfold dilationBudget floorConvolution
  apply Finset.sum_bij (fun k _ => k + 1)
  · intro k hk
    simp only [Finset.mem_range] at hk
    exact Finset.mem_Icc.mpr ⟨Nat.succ_pos k, by omega⟩
  · intro k hk j hj hkj
    omega
  · intro j hj
    obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
    refine ⟨j - 1, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro k hk
    rfl

/-- A global envelope for complete Möbius exact-head energy.
The additive constant and initial stages of the eventual provider are absorbed. -/
theorem exactHead_global_log_power_energy (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ‖exactHead n‖ ^ 2 ≤ C * (n : ℝ) / logWeight n ^ A := by
  obtain ⟨C, hC, hbound⟩ := QMobiusStretchedEnergy.exactHead_eventual_log_power_energy A
  have hzero : ‖exactHead 0‖ ^ 2 = 0 := by
    simp [exactHead, Pareto.mobiusReciprocalSum]
  exact global_envelope_of_eventual (fun n => ‖exactHead n‖ ^ 2)
    (fun n => sq_nonneg _) hzero A
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 6) zetaTwo_pos.le) hC hbound

/-- All logarithmic savings transfer to the full dilation budget, uniformly in N. -/
theorem dilationBudget_global_log_power (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      dilationBudget N ≤ C * (N : ℝ) / logWeight N ^ A := by
  obtain ⟨C, hC, hbound⟩ := exactHead_global_log_power_energy A
  refine ⟨C * ∑' k, majorant A k,
    mul_nonneg hC (tsum_nonneg (majorant_nonneg A)), ?_⟩
  intro N
  rw [dilationBudget_eq_floorConvolution]
  exact floorConvolution_le _ A hC hbound N

/-- Every logarithmic saving transfers to complete reciprocal repair energy.
The constant is independent of the vector f. -/
theorem reciprocalRepair_global_log_power_energy (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N (f : QHilbert),
      ‖reciprocalRepair N f‖ ^ 2 ≤
        C * (N : ℝ) / logWeight N ^ A * ‖f‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := dilationBudget_global_log_power A
  have hZ := zetaTwo_pos
  refine ⟨4 * zetaTwo * C, by positivity, ?_⟩
  intro N f
  calc
    ‖reciprocalRepair N f‖ ^ 2 ≤
        4 * zetaTwo * ‖f‖ ^ 2 * dilationBudget N :=
      reciprocalRepair_norm_sq_le_dilationBudget N f
    _ ≤ 4 * zetaTwo * ‖f‖ ^ 2 * (C * (N : ℝ) / logWeight N ^ A) :=
      mul_le_mul_of_nonneg_left (hbound N) (by positivity)
    _ = _ := by ring

/-- Complete repair norms have any fixed logarithmic saving over sqrt(N).
No uniform boundedness or actual-tail decay is inferred. -/
theorem reciprocalRepair_global_log_power_norm (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N (f : QHilbert),
      ‖reciprocalRepair N f‖ ≤
        C * Real.sqrt (N : ℝ) / logWeight N ^ A * ‖f‖ := by
  obtain ⟨C, hC, hbound⟩ := reciprocalRepair_global_log_power_energy (2 * A)
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro N f
  have hL := logWeight_pos N
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖reciprocalRepair N f‖ ^ 2 ≤
        C * (N : ℝ) / logWeight N ^ (2 * A) * ‖f‖ ^ 2 := hbound N f
    _ = (Real.sqrt C * Real.sqrt (N : ℝ) / logWeight N ^ A * ‖f‖) ^ 2 := by
      simp only [mul_pow, div_pow, Real.sq_sqrt hC,
        Real.sq_sqrt (Nat.cast_nonneg N), ← pow_mul]
      rw [Nat.mul_comm A 2]

end RiemannResearch.RH.QFullDilatedMobiusRepair
