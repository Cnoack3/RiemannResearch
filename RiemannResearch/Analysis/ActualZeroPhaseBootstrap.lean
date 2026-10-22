/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroPhaseOperators

/-!
# Deterministic bootstrap for the actual finite phase-Gram operator

The actual diagonal, positive even moments and complete signed correction
identity discharge the algebraic providers of HorizontalPhaseBootstrap.
Only explicit Landau-operator and bad-correction norm estimates remain.
Source: the user-provided phase-Gram argument and
RH/GrowingPhaseGramBootstrapAudit20261005.md.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments

open HorizontalPhaseBootstrap

set_option maxHeartbeats 800000 in
/-- The actual finite Gram bootstrap, with its moment and operator identity
providers discharged. The two analytic norm bounds remain explicit. -/
theorem phaseGram_norm_sub_one_le
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ) (α β : ℝ)
    (hH : ‖landauGram T d - 1‖ ≤ α)
    (hB : ‖badCorrection T d δ‖ ≤ β)
    (hε : (Real.cosh (δ * Real.log (d : ℝ)) - 1) / 2 < 1) :
    ‖phaseGram T d - 1‖ ≤
      (α + β + (Real.cosh (δ * Real.log (d : ℝ)) - 1) / 2) /
        (1 - (Real.cosh (δ * Real.log (d : ℝ)) - 1) / 2) := by
  letI : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd)⟩
  exact norm_sub_one_bound_of_evenCorrection
    (logDiagonal d) (goodMoment T d δ) (phaseGram T d) (landauGram T d)
    (badCorrection T d δ) (Real.log (d : ℝ)) δ α β
    (two_mul_logDiagonal_norm_le d hd)
    (fun k => goodMoment_center_norm_le T d δ hδ (k + 1)) hH hB
    (landauGram_sub_phaseGram T d hd δ hδ) hε

set_option maxHeartbeats 800000 in
/-- A strict finite frame gap makes the actual Gram operator invertible.
No exact-identity or centered-moment premise remains. -/
theorem phaseGram_isUnit
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ) (α β : ℝ)
    (hH : ‖landauGram T d - 1‖ ≤ α)
    (hB : ‖badCorrection T d δ‖ ≤ β)
    (hsmall : α + β + Real.cosh (δ * Real.log (d : ℝ)) < 2) :
    IsUnit (phaseGram T d) := by
  letI : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd)⟩
  exact isUnit_of_evenCorrection
    (logDiagonal d) (goodMoment T d δ) (phaseGram T d) (landauGram T d)
    (badCorrection T d δ) (Real.log (d : ℝ)) δ α β
    (two_mul_logDiagonal_norm_le d hd)
    (fun k => goodMoment_center_norm_le T d δ hδ (k + 1)) hH hB
    (landauGram_sub_phaseGram T d hd δ hδ) hsmall

end RiemannResearch.Analysis.ActualZeroPhaseMoments
