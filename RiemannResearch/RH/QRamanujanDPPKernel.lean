import RiemannResearch.RH.QRamanujanCanonicalOptimizer
import RiemannResearch.RH.IntegerDPPExistence
import RiemannResearch.Analysis.ProjectionDPPKernel
import Mathlib.Topology.Instances.Matrix

/-!
# Actual complete-Q Ramanujan projection kernels

Source: sixth Ramanujan transfer program, 24 October 2026. The projection-DPP
terminology follows Lyons, https://arxiv.org/abs/math/0204325. Every kernel
below uses the genuine Q orthogonal projection and Q packet inverse Gram.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QRamanujanDPP
open Pareto ZetaTwoHilbert QRamanujanCanonicalOptimizer
open Pareto.IntegerDPP (countingBasis countingBasis_inner countingBasis_norm_sq)
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionDPP

def kernel (n : ℕ) : ℕ → ℕ → ℝ :=
  RiemannResearch.Analysis.ProjectionDPP.kernel (QFullResidueProjection.stage n) countingBasis

def limitKernel : ℕ → ℕ → ℝ :=
  RiemannResearch.Analysis.ProjectionDPP.kernel QFullResidueProjection.closure countingBasis

def holeKernel (n : ℕ) : ℕ → ℕ → ℝ :=
  RiemannResearch.Analysis.ProjectionDPP.holeKernel (QFullResidueProjection.stage n) countingBasis

def limitHoleKernel : ℕ → ℕ → ℝ :=
  RiemannResearch.Analysis.ProjectionDPP.holeKernel QFullResidueProjection.closure countingBasis

theorem kernel_inverseGram (n i j : ℕ) :
    kernel n i j = dotProduct (cross (packetFamily n) (countingBasis i))
      ((packetGram n)⁻¹.mulVec (cross (packetFamily n) (countingBasis j))) := by
  simpa only [RiemannResearch.RH.QRamanujanDPP.kernel,
    RiemannResearch.Analysis.ProjectionDPP.kernel, packet_span_eq_stage, packetGram] using
    projection_inner_eq_inverseGram (packet_independent n) (countingBasis i) (countingBasis j)

theorem kernel_matrix {ι : Type*} [Fintype ι] (n : ℕ) (a : ι → ℕ) :
    Matrix.of (fun i j => kernel n (a i) (a j)) =
      observationMatrix (packetFamily n) (fun i => countingBasis (a i)) *
        (packetGram n)⁻¹ *
        (observationMatrix (packetFamily n) (fun i => countingBasis (a i))).transpose := by
  simpa only [RiemannResearch.RH.QRamanujanDPP.kernel,
    RiemannResearch.Analysis.ProjectionDPP.kernel, packet_span_eq_stage, packetGram] using
    projection_kernel_matrix (packet_independent n) (fun i => countingBasis (a i))

theorem kernel_symmetric (n i j : ℕ) : kernel n i j = kernel n j i :=
  real_inner_comm _ _

theorem limitKernel_symmetric (i j : ℕ) : limitKernel i j = limitKernel j i :=
  real_inner_comm _ _

theorem holeKernel_eq (n i j : ℕ) :
    holeKernel n i j = (if i = j then 1 else 0) - kernel n i j := by
  exact (RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq
    (QFullResidueProjection.stage n) countingBasis i j).trans
      (by rw [countingBasis_inner]; rfl)

theorem limitHoleKernel_eq (i j : ℕ) :
    limitHoleKernel i j = (if i = j then 1 else 0) - limitKernel i j := by
  exact (RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq
    QFullResidueProjection.closure countingBasis i j).trans
      (by rw [countingBasis_inner]; rfl)

theorem kernel_diagonal_bounds (n i : ℕ) : 0 ≤ kernel n i i ∧ kernel n i i ≤ 1 :=
  diagonal_bounds (QFullResidueProjection.stage n) countingBasis i (countingBasis_norm_sq i)

theorem limitKernel_diagonal_bounds (i : ℕ) : 0 ≤ limitKernel i i ∧ limitKernel i i ≤ 1 :=
  diagonal_bounds QFullResidueProjection.closure countingBasis i (countingBasis_norm_sq i)

theorem kernel_principal_posSemidef {ι : Type*} [Finite ι] (n : ℕ) (a : ι → ℕ) :
    (Matrix.of (fun i j => kernel n (a i) (a j))).PosSemidef :=
  principal_posSemidef (QFullResidueProjection.stage n) countingBasis a

theorem limitKernel_principal_posSemidef {ι : Type*} [Finite ι] (a : ι → ℕ) :
    (Matrix.of (fun i j => limitKernel (a i) (a j))).PosSemidef :=
  principal_posSemidef QFullResidueProjection.closure countingBasis a

theorem kernel_complement_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (a : ι ↪ ℕ) :
    (1 - Matrix.of (fun i j => kernel n (a i) (a j))).PosSemidef := by
  apply identity_sub_principal_posSemidef (QFullResidueProjection.stage n) countingBasis a
  intro i j
  simp [countingBasis_inner, a.injective.eq_iff]

theorem limitKernel_complement_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι ↪ ℕ) :
    (1 - Matrix.of (fun i j => limitKernel (a i) (a j))).PosSemidef := by
  apply identity_sub_principal_posSemidef QFullResidueProjection.closure countingBasis a
  intro i j
  simp [countingBasis_inner, a.injective.eq_iff]

theorem kernel_tendsto (i j : ℕ) :
    Tendsto (fun n => kernel n i j) atTop (𝓝 (limitKernel i j)) := by
  exact (walkProjection_tendsto (fun i => qResidue (i + 2)) id
    Function.surjective_id (countingBasis i)).inner
      (walkProjection_tendsto (fun i => qResidue (i + 2)) id
        Function.surjective_id (countingBasis j))

theorem holeKernel_tendsto (i j : ℕ) :
    Tendsto (fun n => holeKernel n i j) atTop (𝓝 (limitHoleKernel i j)) := by
  simpa only [holeKernel_eq, limitHoleKernel_eq] using
    (tendsto_const_nhds.sub (kernel_tendsto i j))

theorem principal_det_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) :
    Tendsto (fun n => (Matrix.of (fun i j => kernel n (a i) (a j))).det) atTop
      (𝓝 ((Matrix.of (fun i j => limitKernel (a i) (a j))).det)) :=
  (continuous_id.matrix_det.tendsto _).comp
    (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => kernel_tendsto (a i) (a j))

end RiemannResearch.RH.QRamanujanDPP
