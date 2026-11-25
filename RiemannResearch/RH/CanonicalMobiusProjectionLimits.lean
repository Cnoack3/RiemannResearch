import RiemannResearch.RH.CanonicalMobiusCovarianceDecay
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.MellinFrequencyRegularization
import RiemannResearch.RH.ResidueProjectionL1

/-! # Two cutoff orders for the projection and canonical Möbius residuals

Take the complete signed inner product of the finite projection residual with
the canonical Möbius residual. Sending the Möbius cutoff to infinity first
gives zero. Sending the projection cutoff to infinity first gives the limiting
projection energy. Both limits refer to the same finite array.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Complete signed residual pairing with independent projection and Möbius cutoffs. -/
def projectionMobiusPairing (M N : ℕ) : ℝ :=
  inner ℝ (hilbertOne - projection M) (hilbertOne - canonicalMobiusHilbert N)

/-- Every canonical vector up to the projection cutoff is annihilated exactly. -/
theorem projectionMobiusPairing_eq_energy {M N : ℕ} (hNM : N ≤ M) :
    projectionMobiusPairing M N = energy M := by
  have hmem : canonicalMobiusHilbert N ∈ finiteSpace M :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hNM
      (canonicalMobiusHilbert_mem_finiteSpace N)
  have hz : inner ℝ (hilbertOne - projection M) (canonicalMobiusHilbert N) = 0 :=
    Submodule.starProjection_inner_eq_zero hilbertOne _ hmem
  rw [projectionMobiusPairing, inner_sub_right, hz, sub_zero, real_inner_comm]
  exact ProjectionSchur.inner_one_residual_eq_energy M

/-- Each fixed finite projection residual is a bounded physical probe. -/
theorem projectionMobiusPairing_row (M : ℕ) :
    Tendsto (projectionMobiusPairing M) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := MellinFrequency.finiteSpace_sequence_bounded M (projection M)
    ((finiteSpace M).starProjection_apply_mem hilbertOne)
  apply canonicalResidual_inner_tendsto_zero_of_bounded _ (1 + C)
  · have := (abs_nonneg _).trans (hC 0)
    linarith
  · intro n hn
    rw [hilbertSequence_sub, Pi.sub_apply, hilbertOne_sequence]
    calc
      |zeroAnchor (fun _ => 1) n - hilbertSequence (projection M) n| ≤
          |zeroAnchor (fun _ => 1) n| + |hilbertSequence (projection M) n| := abs_sub _ _
      _ ≤ 1 + C := by simpa [zeroAnchor, hn.ne'] using hC n

/-- In the opposite order the entire column has the limiting projection energy. -/
theorem projectionMobiusPairing_column (N : ℕ) :
    Tendsto (fun M => projectionMobiusPairing M N) atTop (𝓝 limitEnergy) := by
  apply energy_tendsto.congr'
  filter_upwards [eventually_ge_atTop N] with M hM
  exact (projectionMobiusPairing_eq_energy hM).symm

/-- Interchanging the two cutoff limits is equivalent to natural approximation
in the closed residue space. -/
theorem projectionMobiusPairing_common_iterated_limit_iff :
    (∃ L : ℝ, (∀ M, Tendsto (projectionMobiusPairing M) atTop (𝓝 L)) ∧
      (∀ N, Tendsto (fun M => projectionMobiusPairing M N) atTop (𝓝 L))) ↔
      hilbertOne ∈ closedSpace := by
  constructor
  · rintro ⟨L, hrow, hcol⟩
    exact limitEnergy_zero_iff_mem.mp ((tendsto_nhds_unique (projectionMobiusPairing_column 0)
      (hcol 0)).trans (tendsto_nhds_unique (hrow 0) (projectionMobiusPairing_row 0)))
  · intro hmem
    refine ⟨0, projectionMobiusPairing_row, fun N => ?_⟩
    simpa only [limitEnergy_zero_iff_mem.mpr hmem] using projectionMobiusPairing_column N

end RiemannResearch.RH.Pareto.CoefficientStabilization
