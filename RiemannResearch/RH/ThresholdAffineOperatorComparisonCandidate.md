# ThresholdAffineOperatorComparison — unverified candidate

**Not verified by Lean.** No theorem in this candidate is claimed proved. See [attempt report](ThresholdOperatorComparisonAttempt.md).

```lean
import RiemannResearch.RH.ThresholdUniformAffineOperator
import RiemannResearch.RH.ThresholdAffinePhaseLimit

/-!
# Actual infinite affine discrepancy and exact standard-basis energy

Source: independently developed from Christian Noack's RH_Two_Seed_Threshold.tex
(8 September 2026), Section 11.2. We identify actual normalized dilation
coordinates, adjoint columns, signed projection entries, and complete
standard-basis squared energy. The positive-block regrouping explicitly
accounts for the finite exceptional head and proves summability first.
The existing arithmetic phase bound is then applied to this actual operator.
No legal density, RH, or matrix-realization provider is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem hilbert_raw_coordinate (f : ThresholdHilbert) (k : ℕ) (hk : 0 < k) :
    f (k-1) = Real.sqrt (positiveWeight k) * hilbertSequence f k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [positiveWeight_succ, hilbertSequence_succ]
  have hp : 0 < paretoWeight n := by unfold paretoWeight; positivity
  have hs : Real.sqrt (paretoWeight n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  simp only [Nat.add_sub_cancel]
  field_simp

theorem affineBranchCoefficient_sqrt_ratio (m r j : ℕ) :
    affineBranchCoefficient m r j =
      Real.sqrt (m : ℝ) * Real.sqrt (positiveWeight (affineBranch m r j)) /
        Real.sqrt (positiveWeight j) := by
  unfold affineBranchCoefficient affineBranchWeight
  rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg m) (positiveWeight_nonneg _)),
    Real.sqrt_mul (Nat.cast_nonneg m)]

theorem hilbertNormalizedDilation_branch (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (j r : ℕ) (hr : r < m) :
    hilbertNormalizedDilation m hm f (m*(j+1)+r-1) =
      affineBranchCoefficient m r (j+1) * f j := by
  have hk : 0 < m*(j+1)+r := by positivity
  have hd : (m*(j+1)+r)/m = j+1 := by
    simp [Nat.add_div, Nat.div_eq_of_lt hr, hm.ne']
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hs : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hmR)
  rw [hilbert_raw_coordinate _ _ hk]
  change Real.sqrt (positiveWeight (m*(j+1)+r)) *
    hilbertSequence ((1 / Real.sqrt (m:ℝ)) • hilbertDilation m hm f)
      (m*(j+1)+r) = _
  rw [hilbertSequence_smul, hilbertDilation_sequence]
  simp only [Pi.smul_apply, smul_eq_mul, dilation, hd, hilbertSequence_succ]
  rw [affineBranchCoefficient_sqrt_ratio, positiveWeight_succ]
  unfold affineBranch
  have hscale : (1 / Real.sqrt (m:ℝ)) * (m:ℝ) = Real.sqrt (m:ℝ) := by
    rw [one_div_mul_eq_div]
    apply (div_eq_iff hs).2
    nlinarith [Real.sq_sqrt (le_of_lt hmR)]
  calc
    _ = ((1 / Real.sqrt (m:ℝ)) * (m:ℝ)) *
        Real.sqrt (positiveWeight (m*(j+1)+r)) / Real.sqrt (paretoWeight j) * f j := by ring
    _ = _ := by rw [hscale]

theorem hilbertNormalizedDilation_head (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (n : ℕ) (hn : n+1 < m) :
    hilbertNormalizedDilation m hm f n = 0 := by
  have h := hilbert_raw_coordinate (hilbertNormalizedDilation m hm f) (n+1)
    (Nat.succ_pos n)
  change _ = Real.sqrt (positiveWeight (n+1)) *
    hilbertSequence ((1 / Real.sqrt (m:ℝ)) • hilbertDilation m hm f) (n+1) at h
  rw [hilbertSequence_smul, hilbertDilation_sequence] at h
  simpa [dilation, Nat.div_eq_of_lt hn] using h


theorem hilbert_inner_single_right (f : ThresholdHilbert) (j : ℕ) :
    inner ℝ f (lp.single 2 j (1:ℝ)) = f j := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_single j (fun k hk => by simp [lp.single_apply, Pi.single_apply, hk])]
  simp [lp.single_apply]

theorem hilbert_single_norm (j : ℕ) :
    ‖(lp.single 2 j (1:ℝ) : ThresholdHilbert)‖ = 1 := by
  have h : ‖(lp.single 2 j (1:ℝ) : ThresholdHilbert)‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hilbert_inner_single_right]
    simp [lp.single_apply]
  nlinarith [norm_nonneg (lp.single 2 j (1:ℝ) : ThresholdHilbert)]

def hilbertNormalizedAdjoint (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (1 / Real.sqrt (m:ℝ)) • hilbertDilationAdjoint m hm

theorem hilbertNormalizedAdjoint_inner (m : ℕ) (hm : 0 < m)
    (f g : ThresholdHilbert) :
    inner ℝ f (hilbertNormalizedAdjoint m hm g) =
      inner ℝ (hilbertNormalizedDilation m hm f) g := by
  change inner ℝ f ((1 / Real.sqrt (m:ℝ)) • hilbertDilationAdjoint m hm g) =
    inner ℝ ((1 / Real.sqrt (m:ℝ)) • hilbertDilation m hm f) g
  rw [real_inner_smul_right, real_inner_smul_left]
  congr 1
  exact ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous m hm) f g

theorem hilbertNormalizedAdjoint_single_branch (m : ℕ) (hm : 0 < m)
    (j r : ℕ) (hr : r < m) :
    hilbertNormalizedAdjoint m hm (lp.single 2 (m*(j+1)+r-1) (1:ℝ)) =
      affineBranchCoefficient m r (j+1) • (lp.single 2 j (1:ℝ)) := by
  apply ext_inner_left ℝ
  intro f
  rw [hilbertNormalizedAdjoint_inner, hilbert_inner_single_right,
    hilbertNormalizedDilation_branch m hm f j r hr,
    real_inner_smul_right, hilbert_inner_single_right]

theorem hilbertBlockProjection_normalized (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertBlockProjection m hm f =
      hilbertNormalizedDilation m hm (hilbertNormalizedAdjoint m hm f) := by
  rw [hilbertBlockProjection_apply]
  change (1 / (m:ℝ)) • hilbertDilation m hm (hilbertDilationAdjoint m hm f) =
    (1 / Real.sqrt (m:ℝ)) • hilbertDilation m hm
      ((1 / Real.sqrt (m:ℝ)) • hilbertDilationAdjoint m hm f)
  rw [hilbertDilation_smul, smul_smul, uniformBranchCoefficient_product]

theorem hilbertBlockProjection_single_branch (m : ℕ) (hm : 0 < m)
    (j r : ℕ) (hr : r < m) :
    hilbertBlockProjection m hm (lp.single 2 (m*(j+1)+r-1) (1:ℝ)) =
      affineBranchCoefficient m r (j+1) •
        hilbertNormalizedDilation m hm (lp.single 2 j (1:ℝ)) := by
  rw [hilbertBlockProjection_normalized, hilbertNormalizedAdjoint_single_branch m hm j r hr,
    map_smul]

end
end RiemannResearch.RH.Pareto

/-! Coordinator-only candidate. The generic lemmas here are helpers for the
actual operator identification; they must be specialized to constructed S,L
and their derived coordinates before presenting the result as that target. -/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem uniformAffineColumn_inner_range (m j : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    inner ℝ f (uniformAffineColumn m j) =
      (1 / Real.sqrt (m : ℝ)) *
        ∑ r ∈ Finset.range m, f (m*(j+1)+r-1) := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := uniformAffineBlock m j) (fun n hn => by
    simp [uniformAffineColumn_apply, hn])]
  have he : ∑ n ∈ uniformAffineBlock m j,
      inner ℝ (f n) (uniformAffineColumn m j n) =
      (1 / Real.sqrt (m : ℝ)) * ∑ n ∈ uniformAffineBlock m j, f n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [uniformAffineColumn_apply, if_pos hn]
    simp [RCLike.inner_apply, mul_comm]
  rw [he]
  congr 1
  unfold uniformAffineBlock
  rw [Finset.sum_Ico_eq_sum_range]
  have hp : 0 < m*(j+1) := Nat.mul_pos hm (by omega)
  have hsize : m*(j+2)-1 - (m*(j+1)-1) = m := by
    have hh : m*(j+2) = m*(j+1)+m := by ring
    rw [hh]
    omega
  rw [hsize]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  omega

theorem uniformAffineColumn_inner_of_coordinates (m j : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert)
    (hf : ∀ r < m, f (m*(j+1)+r-1) = affineBranchCoefficient m r (j+1)) :
    inner ℝ f (uniformAffineColumn m j) = affineBranchOverlap m (j+1) := by
  rw [uniformAffineColumn_inner_range m j hm f]
  unfold affineBranchOverlap
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact hf r (Finset.mem_range.mp hr)

theorem norm_smul_sub_smul_sq_unit (u v : ThresholdHilbert)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (c d : ℝ) :
    ‖c • u - d • v‖^2 = c^2 + d^2 - 2*c*d*inner ℝ u v := by
  rw [norm_sub_sq_real, norm_smul, norm_smul, hu, hv,
    real_inner_smul_left, real_inner_smul_right]
  simp only [mul_one, Real.norm_eq_abs, sq_abs]
  ring

theorem affineProjection_block_norm_sum_of_inner (m j : ℕ)
    (hm : 0 < m) (hj : 0 < j) (u v : ThresholdHilbert)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = affineBranchOverlap m j) :
    (∑ r ∈ Finset.range m,
      ‖affineBranchCoefficient m r j • u -
        (1 / Real.sqrt (m : ℝ)) • v‖^2) = affineProjectionBlockEnergy m j := by
  rw [affineProjectionBlockEnergy_exact m j hm hj]
  calc
    _ = ∑ r ∈ Finset.range m,
        (affineBranchCoefficient m r j)^2 + (1 / Real.sqrt (m : ℝ))^2 -
        (2 * (1 / Real.sqrt (m : ℝ)) * affineBranchOverlap m j) *
          affineBranchCoefficient m r j := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_smul_sub_smul_sq_unit u v hu hv, huv]
      ring
    _ = (∑ r ∈ Finset.range m, affineBranchCoefficient m r j ^ 2) +
        (∑ _r ∈ Finset.range m, (1 / Real.sqrt (m : ℝ))^2) -
        (2 * (1 / Real.sqrt (m : ℝ)) * affineBranchOverlap m j) *
          ∑ r ∈ Finset.range m, affineBranchCoefficient m r j := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
      rw [affineBranchCoefficient_sq_sum m j hm hj,
        uniformBranchCoefficient_sq_sum m hm]
      unfold affineBranchOverlap
      ring

end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Group all raw l2 coordinates into their actual positive affine blocks.
The exceptional finite head is explicitly zero, not discarded in a bound. -/
theorem affine_positive_block_partial_sum (m : ℕ) (hm : 0 < m)
    (b : ℕ → ℝ) (hhead : ∀ n, n+1 < m → b n = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (m*(N+1)-1), b n) =
      ∑ j ∈ Finset.range N, ∑ r ∈ Finset.range m, b (m*(j+1)+r-1) := by
  induction N with
  | zero =>
    simp only [Nat.zero_add, Nat.mul_one, Finset.sum_range_zero]
    apply Finset.sum_eq_zero
    intro n hn
    apply hhead n
    have hn' := Finset.mem_range.mp hn
    omega
  | succ N ih =>
    have hp : 0 < m*(N+1) := Nat.mul_pos hm (by omega)
    have hmul : m*(N+1+1) = m*(N+1)+m := by ring
    have he : m*(N+1+1)-1 = (m*(N+1)-1)+m := by omega
    simp only [Nat.succ_eq_add_one]
    rw [he, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    omega

theorem affine_positive_block_summable (m : ℕ) (hm : 0 < m)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hhead : ∀ n, n+1 < m → b n = 0)
    (hs : Summable (fun j => ∑ r ∈ Finset.range m, b (m*(j+1)+r-1))) :
    Summable b := by
  apply summable_of_sum_range_le hb
    (c := ∑' j, ∑ r ∈ Finset.range m, b (m*(j+1)+r-1))
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range (m*(N+1)-1), b n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply Finset.range_mono
        have h := Nat.le_mul_of_pos_left (N+1) hm
        omega
      · intro n hn hn'
        exact hb n
    _ = ∑ j ∈ Finset.range N, ∑ r ∈ Finset.range m, b (m*(j+1)+r-1) :=
      affine_positive_block_partial_sum m hm b hhead N
    _ ≤ _ := Summable.sum_le_tsum (Finset.range N)
      (fun j _ => Finset.sum_nonneg (fun r _ => hb _)) hs

/-- Exact infinite regrouping after proving full-coordinate summability.
No conditional Fubini step and no assumed Hilbert--Schmidt provider. -/
theorem affine_positive_block_tsum (m : ℕ) (hm : 0 < m)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hhead : ∀ n, n+1 < m → b n = 0)
    (hs : Summable (fun j => ∑ r ∈ Finset.range m, b (m*(j+1)+r-1))) :
    (∑' n, b n) = ∑' j, ∑ r ∈ Finset.range m, b (m*(j+1)+r-1) := by
  have hfull := affine_positive_block_summable m hm b hb hhead hs
  have hpn : Filter.Tendsto (fun N : ℕ => m*(N+1)-1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun N => ?_) Filter.tendsto_id
    have h := Nat.le_mul_of_pos_left (N+1) hm
    omega
  have hleft := hfull.hasSum.tendsto_sum_nat.comp hpn
  have hright := hs.hasSum.tendsto_sum_nat
  have heq : (fun N => ∑ n ∈ Finset.range (m*(N+1)-1), b n) =
      (fun N => ∑ j ∈ Finset.range N, ∑ r ∈ Finset.range m, b (m*(j+1)+r-1)) := by
    funext N
    exact affine_positive_block_partial_sum m hm b hhead N
  simp only [Function.comp_def] at hleft
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem uniformAffineBlock_branch_mem (m j r : ℕ) (hm : 0 < m) (hr : r < m) :
    m*(j+1)+r-1 ∈ uniformAffineBlock m j := by
  have hp : 0 < m*(j+1) := by positivity
  have he : m*(j+2) = m*(j+1)+m := by ring
  simp only [uniformAffineBlock, Finset.mem_Ico]
  omega

theorem hilbertUniformAffineAdjoint_single_branch (m : ℕ) (hm : 0 < m)
    (j r : ℕ) (hr : r < m) :
    (hilbertUniformAffineContinuous m hm).adjoint
      (lp.single 2 (m*(j+1)+r-1) (1:ℝ)) =
        (1 / Real.sqrt (m:ℝ)) • (lp.single 2 j (1:ℝ)) := by
  apply ext_inner_left ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right, hilbert_inner_single_right,
    real_inner_smul_right, hilbert_inner_single_right]
  change hilbertUniformAffine m hm f (m*(j+1)+r-1) = _
  rw [hilbertUniformAffine_block_coordinate m hm f j _
    (uniformAffineBlock_branch_mem m j r hm hr)]
  ring

theorem hilbertUniformBlockProjection_single_branch (m : ℕ) (hm : 0 < m)
    (j r : ℕ) (hr : r < m) :
    hilbertUniformBlockProjection m hm (lp.single 2 (m*(j+1)+r-1) (1:ℝ)) =
      (1 / Real.sqrt (m:ℝ)) • uniformAffineColumn m j := by
  change hilbertUniformAffine m hm
    ((hilbertUniformAffineContinuous m hm).adjoint
      (lp.single 2 (m*(j+1)+r-1) (1:ℝ))) = _
  rw [hilbertUniformAffineAdjoint_single_branch m hm j r hr, map_smul,
    hilbertUniformAffine_single, one_smul]

def hilbertAffineDiscrepancy (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  hilbertBlockProjection m hm - hilbertUniformBlockProjection m hm

theorem hilbertAffineDiscrepancy_single_branch (m : ℕ) (hm : 0 < m)
    (j r : ℕ) (hr : r < m) :
    hilbertAffineDiscrepancy m hm (lp.single 2 (m*(j+1)+r-1) (1:ℝ)) =
      affineBranchCoefficient m r (j+1) •
        hilbertNormalizedDilation m hm (lp.single 2 j (1:ℝ)) -
      (1 / Real.sqrt (m:ℝ)) • uniformAffineColumn m j := by
  change hilbertBlockProjection m hm _ - hilbertUniformBlockProjection m hm _ = _
  rw [hilbertBlockProjection_single_branch m hm j r hr,
    hilbertUniformBlockProjection_single_branch m hm j r hr]

theorem hilbertAffineDiscrepancy_single_head (m : ℕ) (hm : 0 < m)
    (n : ℕ) (hn : n+1 < m) :
    hilbertAffineDiscrepancy m hm (lp.single 2 n (1:ℝ)) = 0 := by
  have hs : hilbertNormalizedAdjoint m hm (lp.single 2 n (1:ℝ)) = 0 := by
    apply ext_inner_left ℝ
    intro f
    rw [hilbertNormalizedAdjoint_inner, hilbert_inner_single_right, inner_zero_right]
    exact hilbertNormalizedDilation_head m hm f n hn
  have hl : (hilbertUniformAffineContinuous m hm).adjoint (lp.single 2 n (1:ℝ)) = 0 := by
    apply ext_inner_left ℝ
    intro f
    rw [ContinuousLinearMap.adjoint_inner_right, hilbert_inner_single_right, inner_zero_right]
    exact hilbertUniformAffine_head_coordinate m hm f n hn
  change hilbertBlockProjection m hm _ - hilbertUniformBlockProjection m hm _ = _
  rw [hilbertBlockProjection_normalized, hs, map_zero]
  change 0 - hilbertUniformAffine m hm
    ((hilbertUniformAffineContinuous m hm).adjoint (lp.single 2 n (1:ℝ))) = 0
  rw [hl, map_zero, sub_self]

theorem hilbertAffineDiscrepancy_block_energy (m : ℕ) (hm : 0 < m) (j : ℕ) :
    (∑ r ∈ Finset.range m,
      ‖hilbertAffineDiscrepancy m hm (lp.single 2 (m*(j+1)+r-1) (1:ℝ))‖^2) =
        affineProjectionBlockEnergy m (j+1) := by
  have hu : ‖hilbertNormalizedDilation m hm (lp.single 2 j (1:ℝ))‖ = 1 := by
    rw [(hilbertNormalizedDilation m hm).norm_map, hilbert_single_norm]
  have huv : inner ℝ (hilbertNormalizedDilation m hm (lp.single 2 j (1:ℝ)))
      (uniformAffineColumn m j) = affineBranchOverlap m (j+1) := by
    apply uniformAffineColumn_inner_of_coordinates m j hm
    intro r hr
    rw [hilbertNormalizedDilation_branch m hm _ j r hr]
    simp [lp.single_apply]
  calc
    _ = ∑ r ∈ Finset.range m,
        ‖affineBranchCoefficient m r (j+1) •
          hilbertNormalizedDilation m hm (lp.single 2 j (1:ℝ)) -
          (1 / Real.sqrt (m:ℝ)) • uniformAffineColumn m j‖^2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hilbertAffineDiscrepancy_single_branch m hm j r (Finset.mem_range.mp hr)]
    _ = _ := affineProjection_block_norm_sum_of_inner m (j+1) hm (Nat.succ_pos j)
      _ _ hu (uniformAffineColumn_norm m j hm) huv

theorem hilbertAffineDiscrepancy_blocks_summable (m : ℕ) (hm : 0 < m) :
    Summable (fun j => ∑ r ∈ Finset.range m,
      ‖hilbertAffineDiscrepancy m hm (lp.single 2 (m*(j+1)+r-1) (1:ℝ))‖^2) := by
  simp only [hilbertAffineDiscrepancy_block_energy]
  simpa using affineProjectionBlockEnergy_shift_summable m 0 hm

theorem hilbertAffineDiscrepancy_basis_summable (m : ℕ) (hm : 0 < m) :
    Summable (fun n => ‖hilbertAffineDiscrepancy m hm (lp.single 2 n (1:ℝ))‖^2) := by
  apply affine_positive_block_summable m hm _ (fun n => sq_nonneg _) ?_
    (hilbertAffineDiscrepancy_blocks_summable m hm)
  intro n hn
  rw [hilbertAffineDiscrepancy_single_head m hm n hn, norm_zero]
  norm_num

theorem hilbertAffineDiscrepancy_basis_energy (m : ℕ) (hm : 0 < m) :
    (∑' n, ‖hilbertAffineDiscrepancy m hm (lp.single 2 n (1:ℝ))‖^2) =
      affineProjectionEnergyTail m 0 := by
  have hhead : ∀ n, n+1 < m →
      ‖hilbertAffineDiscrepancy m hm (lp.single 2 n (1:ℝ))‖^2 = 0 := by
    intro n hn
    rw [hilbertAffineDiscrepancy_single_head m hm n hn, norm_zero]
    norm_num
  have h := affine_positive_block_tsum m hm _ (fun n => sq_nonneg _) hhead
    (hilbertAffineDiscrepancy_blocks_summable m hm)
  simpa only [hilbertAffineDiscrepancy_block_energy, affineProjectionEnergyTail,
    Nat.add_zero] using h


/-- The arithmetic phase estimate now applies to the actual infinite operator. -/
theorem hilbertAffineDiscrepancy_phase_gap_rate (m : ℕ) (hm : 0 < m) :
    0 ≤ 2 * TwoSeedThreshold.universalPhaseConstant -
      (∑' n, ‖hilbertAffineDiscrepancy m hm (lp.single 2 n (1:ℝ))‖^2) ∧
    2 * TwoSeedThreshold.universalPhaseConstant -
      (∑' n, ‖hilbertAffineDiscrepancy m hm (lp.single 2 n (1:ℝ))‖^2) ≤
        2 / (3 * (m:ℝ)^2) := by
  rw [hilbertAffineDiscrepancy_basis_energy]
  exact affineProjection_phase_gap_rate m hm

/-- The full standard-basis discrepancy is uniformly bounded, with no discarded head. -/
theorem hilbertAffineDiscrepancy_energy_le (m : ℕ) (hm : 0 < m) :
    (∑' n, ‖hilbertAffineDiscrepancy m hm (lp.single 2 n (1:ℝ))‖^2) ≤ 1/6 := by
  rw [hilbertAffineDiscrepancy_basis_energy]
  exact affineProjectionEnergyTotal_le m hm

end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Actual signed matrix entries of P_m-Q_m, before taking a square or sum. -/
theorem hilbertAffineDiscrepancy_matrix_branch (m : ℕ) (hm : 0 < m)
    (j r t : ℕ) (hr : r < m) (ht : t < m) :
    hilbertAffineDiscrepancy m hm (lp.single 2 (m*(j+1)+t-1) (1:ℝ))
      (m*(j+1)+r-1) =
        affineBranchCoefficient m r (j+1) * affineBranchCoefficient m t (j+1) -
          1 / (m:ℝ) := by
  rw [hilbertAffineDiscrepancy_single_branch m hm j t ht]
  change affineBranchCoefficient m t (j+1) *
      hilbertNormalizedDilation m hm (lp.single 2 j (1:ℝ)) (m*(j+1)+r-1) -
      (1 / Real.sqrt (m:ℝ)) * uniformAffineColumn m j (m*(j+1)+r-1) = _
  rw [hilbertNormalizedDilation_branch m hm _ j r hr,
    uniformAffineColumn_apply, if_pos (uniformAffineBlock_branch_mem m j r hm hr)]
  simp only [lp.single_apply_self, mul_one, uniformBranchCoefficient_product]
  ring

/-- Distinct positive blocks have exactly zero mixed matrix entries. -/
theorem hilbertAffineDiscrepancy_matrix_distinct_blocks (m : ℕ) (hm : 0 < m)
    (j k r t : ℕ) (hr : r < m) (ht : t < m) (hjk : j ≠ k) :
    hilbertAffineDiscrepancy m hm (lp.single 2 (m*(j+1)+t-1) (1:ℝ))
      (m*(k+1)+r-1) = 0 := by
  rw [hilbertAffineDiscrepancy_single_branch m hm j t ht]
  change affineBranchCoefficient m t (j+1) *
      hilbertNormalizedDilation m hm (lp.single 2 j (1:ℝ)) (m*(k+1)+r-1) -
      (1 / Real.sqrt (m:ℝ)) * uniformAffineColumn m j (m*(k+1)+r-1) = 0
  have hn : m*(k+1)+r-1 ∉ uniformAffineBlock m j := by
    intro hn
    exact hjk (uniformAffineBlock_unique m j k _ hm hn
      (uniformAffineBlock_branch_mem m k r hm hr))
  rw [hilbertNormalizedDilation_branch m hm _ k r hr,
    uniformAffineColumn_apply, if_neg hn]
  simp [lp.single_apply, Pi.single_apply, hjk, Ne.symm hjk]

end
end RiemannResearch.RH.Pareto
```
