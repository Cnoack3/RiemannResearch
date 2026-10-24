import RiemannResearch.RH.QRamanujanDPPKernel
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.QRamanujanSaturationCriteria
import RiemannResearch.Analysis.NonnegativeErrorConvergence

/-!
# Recovering the full Q target defect from the complementary kernel

Source: sixth transfer program, 24 October 2026. Physical heads below are only
an exhaustion used to reconstruct the complete Hilbert error. Every signed
cross term of the complementary kernel is retained. No diagonal-vacancy sum
is substituted for the target error.
-/

noncomputable section
open Filter
open scoped BigOperators Classical Topology
namespace RiemannResearch.RH.QRamanujanDPP
open Pareto ZetaTwoHilbert QRamanujanCanonicalOptimizer
open Pareto.IntegerDPP (countingBasis)
open RiemannResearch.Analysis.NonnegativeErrorConvergence

def physicalHead (f : QHilbert) (M : ℕ) : QHilbert :=
  ∑ i : Fin M, f i • countingBasis i

theorem physicalHead_apply (f : QHilbert) (M k : ℕ) :
    physicalHead f M k = if k < M then f k else 0 := by
  classical
  simp only [physicalHead]
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp [lp.coeFn_smul, countingBasis, lp.single_apply, Pi.single_apply,
    Fin.sum_univ_eq_sum_range, mul_ite, eq_comm]
  by_cases hk : k < M
  · rw [if_pos hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin M)]
    · simp
    · intro b _ hb
      have hne : k ≠ (b : ℕ) := by
        intro he
        exact hb (Fin.ext he.symm)
      simp [hne]
    · simp
  · rw [if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hne : k ≠ (b : ℕ) := by
      intro he
      exact hk (he.symm ▸ b.isLt)
    simp [hne]

theorem physicalHead_error (f : QHilbert) (M : ℕ) :
    ‖f - physicalHead f M‖ ^ 2 = ‖hilbertTailShift f M‖ ^ 2 := by
  have h := (hilbert_coordinate_square_summable (f - physicalHead f M)).sum_add_tsum_nat_add M
  have hz : (∑ k ∈ Finset.range M, ((f - physicalHead f M : QHilbert) k) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    change (f k - physicalHead f M k) ^ 2 = 0
    simp [physicalHead_apply, Finset.mem_range.mp hk]
  rw [hz, zero_add] at h
  rw [hilbert_norm_sq, hilbert_norm_sq, ← h]
  apply tsum_congr
  intro k
  change (f (k + M) - physicalHead f M (k + M)) ^ 2 = (f (k + M)) ^ 2
  simp [physicalHead_apply, show ¬ k + M < M by omega]

theorem physicalHead_tendsto (f : QHilbert) :
    Tendsto (physicalHead f) atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply (norm_zero_iff_square (fun M => physicalHead f M - f)).mpr
  simpa only [norm_sub_rev, physicalHead_error] using hilbertTailShift_energy_tendsto_zero f

/-- A finite head is evaluated by the entire signed complementary principal matrix. -/
theorem hole_quadratic_head (n M : ℕ) (f : QHilbert) :
    ‖physicalHead f M - (QFullResidueProjection.stage n).starProjection (physicalHead f M)‖ ^ 2 =
      ∑ i : Fin M, ∑ j : Fin M, f i * f j * holeKernel n i j := by
  have he : physicalHead f M - (QFullResidueProjection.stage n).starProjection (physicalHead f M) =
      ∑ i : Fin M, f i • (countingBasis i -
        (QFullResidueProjection.stage n).starProjection (countingBasis i)) := by
    simp [physicalHead, smul_sub, Finset.sum_sub_distrib]
  rw [he, ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  change f i * (f j * holeKernel n i j) = _
  ring

theorem limitHole_quadratic_head (M : ℕ) (f : QHilbert) :
    ‖physicalHead f M - QFullResidueProjection.closure.starProjection (physicalHead f M)‖ ^ 2 =
      ∑ i : Fin M, ∑ j : Fin M, f i * f j * limitHoleKernel i j := by
  have he : physicalHead f M - QFullResidueProjection.closure.starProjection (physicalHead f M) =
      ∑ i : Fin M, f i • (countingBasis i -
        QFullResidueProjection.closure.starProjection (countingBasis i)) := by
    simp [physicalHead, smul_sub, Finset.sum_sub_distrib]
  rw [he, ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  change f i * (f j * limitHoleKernel i j) = _
  ring

/-- Complete reconstruction for every target, not only the normalized constant. -/
theorem hole_head_tendsto (n : ℕ) (f : QHilbert) :
    Tendsto (fun M => ∑ i : Fin M, ∑ j : Fin M, f i * f j * holeKernel n i j) atTop
      (𝓝 (‖f - (QFullResidueProjection.stage n).starProjection f‖ ^ 2)) := by
  simp only [← hole_quadratic_head]
  exact ((physicalHead_tendsto f).sub
    ((QFullResidueProjection.stage n).starProjection.continuous.tendsto f |>.comp
      (physicalHead_tendsto f))).norm.pow 2

theorem limitHole_head_tendsto (f : QHilbert) :
    Tendsto (fun M => ∑ i : Fin M, ∑ j : Fin M, f i * f j * limitHoleKernel i j) atTop
      (𝓝 (‖f - QFullResidueProjection.closure.starProjection f‖ ^ 2)) := by
  simp only [← limitHole_quadratic_head]
  exact ((physicalHead_tendsto f).sub
    (QFullResidueProjection.closure.starProjection.continuous.tendsto f |>.comp
      (physicalHead_tendsto f))).norm.pow 2

/-- First take the arithmetic projection limit, keeping the physical head fixed. -/
theorem hole_fixed_head_tendsto (M : ℕ) (f : QHilbert) :
    Tendsto (fun n => ∑ i : Fin M, ∑ j : Fin M, f i * f j * holeKernel n i j) atTop
      (𝓝 (∑ i : Fin M, ∑ j : Fin M, f i * f j * limitHoleKernel i j)) := by
  apply tendsto_finset_sum
  intro i _
  apply tendsto_finset_sum
  intro j _
  exact (holeKernel_tendsto i j).const_mul _

/-- The full target error is exactly the physical-head limit of the limiting hole kernel. -/
theorem target_hole_energy_tendsto :
    Tendsto (fun M => ∑ i : Fin M, ∑ j : Fin M, qOne i * qOne j * limitHoleKernel i j)
      atTop (𝓝 packetLimitEnergy) := limitHole_head_tendsto qOne

theorem target_hole_energy_zero_iff_closure :
    Tendsto (fun M => ∑ i : Fin M, ∑ j : Fin M, qOne i * qOne j * limitHoleKernel i j)
      atTop (𝓝 0) ↔ qOne ∈ QFullResidueProjection.closure := by
  rw [← packetLimitEnergy_zero_iff_closure]
  constructor
  · exact fun h => tendsto_nhds_unique target_hole_energy_tendsto h
  · intro h
    simpa only [h] using target_hole_energy_tendsto

end RiemannResearch.RH.QRamanujanDPP
