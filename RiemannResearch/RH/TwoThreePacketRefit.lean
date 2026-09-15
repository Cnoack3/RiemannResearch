/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ResonanceCellRefit
import RiemannResearch.RH.TwoThreePacketRelations

/-!
# Quantitative refitting of the actual two-three packet cell

Source: Christian Noack,
`RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md`,
actual packet covariance and residual-gain continuation.

The five columns and their correlations below are the actual Pareto Hilbert
vectors. The analytic covariance bound is displayed as a hypothesis, so these
results do not infer an unconditional source lower bound or an RH conclusion.
-/

namespace RiemannResearch.RH.Pareto.AdjacentPacket

open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ResonanceCellRefit
open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell

noncomputable section

/-- The actual five adjacent packets at a two-three resonance. -/
def packetColumns (k : ℕ) (hk : 0 < k) : CellColumns ThresholdHilbert :=
  ⟨packet 2 (3*k) (by omega) (by omega),
    packet 2 (3*k+1) (by omega) (by omega),
    packet 2 (3*k+2) (by omega) (by omega),
    packet 3 (2*k) (by omega) (by omega),
    packet 3 (2*k+1) (by omega) (by omega)⟩

/-- The generic refitting source is definitionally the arithmetic cell source. -/
theorem source_packetColumns (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (b : ThresholdHilbert) (k : ℕ) (hk : 0 < k) :
    source P b (packetColumns k hk) = cellSource (residual P b) k hk := rfl

/-- The actual old cycle gives exactly the compatibility used in the norm bound. -/
theorem packetColumns_source_compatible (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (k : ℕ) (hk : 0 < k)
    (h2 : packet 2 k (by omega) hk ∈ P)
    (h3 : packet 3 k (by omega) hk ∈ P) :
    Compatible (source P hilbertOne (packetColumns k hk)) := by
  rw [source_packetColumns]
  exact projection_cellSource_compatible P k hk h2 h3

/-- A genuine screened Gram upper bound implies a genuine finite projection gain. -/
theorem packet_cell_gain_lower (P W : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hPW : P ≤ W) (k : ℕ) (hk : 0 < k)
    (h2 : packet 2 k (by omega) hk ∈ P)
    (h3 : packet 3 k (by omega) hk ∈ P)
    (hu : ColumnsIn W (packetColumns k hk))
    {C : ℝ} (hC : 0 < C)
    (hcov : ∀ a : CellVector, Compatible a →
      ‖residual P (synthesis (packetColumns k hk) a)‖^2 ≤ C*sizeSq a) :
    sizeSq (cellSource (residual P hilbertOne) k hk)/C ≤
      ‖residual P hilbertOne‖^2 - ‖residual W hilbertOne‖^2 := by
  simpa only [source_packetColumns] using
    enlarged_gain_lower P W hPW hilbertOne (packetColumns k hk) hu
      (packetColumns_source_compatible P k hk h2 h3) hC hcov

/-- The coefficient `7/3` survives all old-space refitting and all mixed terms.
The stated covariance hypothesis remains the required analytic provider. -/
theorem packet_cell_log_gain_lower (P W : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hPW : P ≤ W) (k : ℕ) (hk : 0 < k)
    (h2 : packet 2 k (by omega) hk ∈ P)
    (h3 : packet 3 k (by omega) hk ∈ P)
    (hu : ColumnsIn W (packetColumns k hk))
    {K : ℝ} (hK : 0 < (7:ℝ)/3*Real.log (k:ℝ)+K)
    (hcov : ∀ a : CellVector, Compatible a →
      ‖residual P (synthesis (packetColumns k hk) a)‖^2 ≤
        Real.log (k:ℝ)*energy a + K*sizeSq a) :
    sizeSq (cellSource (residual P hilbertOne) k hk) /
        ((7:ℝ)/3*Real.log (k:ℝ)+K) ≤
      ‖residual P hilbertOne‖^2 - ‖residual W hilbertOne‖^2 := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hk)
  simpa only [source_packetColumns] using
    enlarged_gain_lower_of_leading_bound P W hPW hilbertOne (packetColumns k hk) hu
      (packetColumns_source_compatible P k hk h2 h3) (Real.log_nonneg hk1) hK hcov

/-- An unconditional cell gain with the exact trace of the five actual columns.
No covariance hypothesis or old-cycle membership is needed for this bound. -/
theorem packet_cell_gain_trace (P W : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hPW : P ≤ W) (k : ℕ) (hk : 0 < k)
    (hu : ColumnsIn W (packetColumns k hk)) :
    sizeSq (cellSource (residual P hilbertOne) k hk) / trace (packetColumns k hk) ≤
      ‖residual P hilbertOne‖^2 - ‖residual W hilbertOne‖^2 := by
  simpa only [source_packetColumns] using
    enlarged_gain_trace P W hPW hilbertOne (packetColumns k hk) hu

end
end RiemannResearch.RH.Pareto.AdjacentPacket
