/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.AdjacentPacketNormBounds
import RiemannResearch.RH.TwoThreePacketRefit
import RiemannResearch.RH.TwoThreeHilbertBudget

/-!
# An unconditional logarithmic source-gain bound for the actual resonance cell

Source: continuation of RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md.
The complete digit covariance bounds prove the actual packet diagonal
estimates. The exact Hilbert trace inequality then controls every mixed
term and every old-space refit. The coefficient 7 is a fully proved upper
bound; the sharper coefficient 7/3 has a separate covariance obligation.
No lower bound for the actual source size is assumed or concluded.
-/

namespace RiemannResearch.RH.Pareto.AdjacentPacket
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ResonanceCellRefit
open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
noncomputable section

/-- A fixed explicit constant, independent of the dilation budget and old space. -/
def packetTraceConstant : ℝ :=
  3*(2*‖digitHilbert 2 1 (by omega) (by omega)‖^2+87) +
    2*(2*‖digitHilbert 3 1 (by omega) (by omega)‖^2+249) +
    3*Real.log 5+4*Real.log 3

theorem packetTraceConstant_pos : 0 < packetTraceConstant := by
  have h5 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 5)
  have h3 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  unfold packetTraceConstant
  nlinarith [sq_nonneg ‖digitHilbert 2 1 (by omega) (by omega)‖,
    sq_nonneg ‖digitHilbert 3 1 (by omega) (by omega)‖]

/-- The trace estimate is for the five actual infinite-tail Hilbert columns. -/
theorem packet_trace_log_bound (k : ℕ) (hk : 0 < k) :
    trace (packetColumns k hk) ≤ 7*Real.log (k:ℝ)+packetTraceConstant := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hb (m : ℕ) (hm : 0 < m) (hmk : m ≤ 5*k) :
      ‖packet 2 m (by omega) hm‖^2 ≤ Real.log (k:ℝ)+Real.log 5+
        (2*‖digitHilbert 2 1 (by omega) (by omega)‖^2+87) := by
    have he := (abs_le.mp (binary_packet_log_bound m hm)).2
    have hl : Real.log (m:ℝ) ≤ Real.log ((5:ℝ)*k) :=
      Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmk)
    rw [Real.log_mul (by norm_num) (ne_of_gt hk0)] at hl
    linarith
  have ht (m : ℕ) (hm : 0 < m) (hmk : m ≤ 3*k) :
      ‖packet 3 m (by omega) hm‖^2 ≤ 2*Real.log (k:ℝ)+2*Real.log 3+
        (2*‖digitHilbert 3 1 (by omega) (by omega)‖^2+249) := by
    have he := (abs_le.mp (ternary_packet_log_bound m hm)).2
    have hl : Real.log (m:ℝ) ≤ Real.log ((3:ℝ)*k) :=
      Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmk)
    rw [Real.log_mul (by norm_num) (ne_of_gt hk0)] at hl
    linarith
  have b0 := hb (3*k) (by omega) (by omega)
  have b1 := hb (3*k+1) (by omega) (by omega)
  have b2 := hb (3*k+2) (by omega) (by omega)
  have t0 := ht (2*k) (by omega) (by omega)
  have t1 := ht (2*k+1) (by omega) (by omega)
  unfold trace packetColumns packetTraceConstant
  dsimp
  linarith

/-- Unconditional logarithmic gain after fully refitting the actual old/new spaces.
All assumptions are explicit memberships and projection availability. -/
theorem packet_cell_log_gain_unconditional (P W : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hPW : P ≤ W) (k : ℕ) (hk : 0 < k)
    (h2 : packet 2 k (by omega) hk ∈ P)
    (h3 : packet 3 k (by omega) hk ∈ P)
    (hu : ColumnsIn W (packetColumns k hk)) :
    sizeSq (cellSource (residual P hilbertOne) k hk) /
        (7*Real.log (k:ℝ)+packetTraceConstant) ≤
      ‖residual P hilbertOne‖^2 - ‖residual W hilbertOne‖^2 := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hlog := Real.log_nonneg hk1
  have hC : 0 < 7*Real.log (k:ℝ)+packetTraceConstant := by
    linarith [packetTraceConstant_pos]
  apply packet_cell_gain_lower P W hPW k hk h2 h3 hu hC
  intro a _ha
  have hs : 0 ≤ sizeSq a := by unfold sizeSq; positivity
  exact (screened_synthesis_norm_sq_le_trace P (packetColumns k hk) a).trans
    (mul_le_mul_of_nonneg_right (packet_trace_log_bound k hk) hs)

end
end RiemannResearch.RH.Pareto.AdjacentPacket

namespace RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
open AdjacentPacket RamanujanLaguerre
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ResonanceCellRefit
open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
noncomputable section

/-- The entire actual resonance cell belongs to the doubled ordinary budget. -/
theorem packetColumns_mem_doubled_budget (M k : ℕ) (hk : 0 < k)
    (hcell : 3*k+3 ≤ 2*M) :
    ColumnsIn (budgetHilbert (2*M)) (packetColumns k hk) :=
  new_cell_packets_mem M k hk hcell

/-- An unconditional logarithmic gain for the original finite-budget problem.
The source is the actual projection residual, and all old/new coefficients
are refitted by the projection onto the doubled ordinary budget. -/
theorem ordinary_budget_log_gain (M k : ℕ) (hk : 0 < k)
    (hcell : 3*k+3 ≤ 2*M) :
    sizeSq (cellSource (residual (budgetHilbert M) hilbertOne) k hk) /
        (7*Real.log (k:ℝ)+packetTraceConstant) ≤
      ‖residual (budgetHilbert M) hilbertOne‖^2 -
        ‖residual (budgetHilbert (2*M)) hilbertOne‖^2 := by
  have hkM : k+1 ≤ M := by omega
  obtain ⟨h2, h3⟩ := old_cell_packets_mem M k hk hkM
  have hPW : budgetHilbert M ≤ budgetHilbert (2*M) := budgetHilbert_mono (by omega)
  exact packet_cell_log_gain_unconditional (budgetHilbert M) (budgetHilbert (2*M))
    hPW k hk h2 h3 (packetColumns_mem_doubled_budget M k hk hcell)

end
end RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
