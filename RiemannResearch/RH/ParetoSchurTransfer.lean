import RiemannResearch.RH.OptimizedResidueHilbert
import RiemannResearch.RH.ParetoPacketCoordinates
import RiemannResearch.RH.OptimizedPacketRecursion
import RiemannResearch.RH.ParetoHaarCoordinates
import RiemannResearch.LinearAlgebra.SchurTransferSharpBound

/-!
# The exact sharp amplification of the actual Pareto packet transfer

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 7, formula (34). The permitted vectors lie in the actual mean-zero
future-coordinate Hilbert subspace. All dimensional and packet hypotheses
of the sharp amplification theorem are supplied here concretely.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

def paretoFutureSubspace (N : ℕ) : Submodule ℝ ThresholdHilbert where
  carrier := {f | inner ℝ f hilbertOne = 0 ∧
    ∀ j, j ≤ N → inner ℝ f (tailBasisHilbert j) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_⟩
    · simp [inner_add_left, hf.1, hg.1]
    · intro j hj
      simp [inner_add_left, hf.2 j hj, hg.2 j hj]
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · simp [inner_smul_left, hf.1]
    · intro j hj
      simp [inner_smul_left, hf.2 j hj]

theorem tailBasis_mem_paretoFutureSubspace (N j : ℕ) (hj : N < j) :
    tailBasisHilbert j ∈ paretoFutureSubspace N := by
  refine ⟨tailBasis_inner_one j, ?_⟩
  intro k hk
  rw [tailBasis_inner, if_neg (by omega)]

def optimizedFutureTransferVector (n : ℕ) : ThresholdHilbert :=
  ((n : ℝ) + 1) • optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n) -
    tailBasisHilbert n

theorem optimizedCorrection_first_coefficient (n : ℕ) :
    inner ℝ (((n : ℝ) + 1) •
      optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n)) (tailBasisHilbert n) = 1 := by
  apply tailBasis_coefficient_normalized_repair
  · exact optimizedCorrectionHilbert_mean _ _
  · intro k hk
    rw [hilbertGibbsPhysical_eq]
    exact optimizedCorrectionHilbert_below (n + 1) (k + 1) (Nat.succ_pos n) (by omega)
  · rw [hilbertGibbsPhysical_eq]
    exact optimizedCorrectionHilbert_at _ _

theorem optimizedFutureTransferVector_mem (n : ℕ) :
    optimizedFutureTransferVector n ∈ paretoFutureSubspace n := by
  refine ⟨?_, ?_⟩
  · simp [optimizedFutureTransferVector, inner_sub_left, inner_smul_left,
      optimizedCorrectionHilbert_mean, tailBasis_inner_one]
  · intro j hj
    unfold optimizedFutureTransferVector
    rw [inner_sub_left]
    by_cases he : j = n
    · subst j
      rw [optimizedCorrection_first_coefficient, tailBasis_inner_self]
      norm_num
    · have hlt : j < n := by omega
      have hz : inner ℝ (optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n))
          (tailBasisHilbert j) = 0 := by
        apply tailBasis_coefficient_before_head _ n j
          (optimizedCorrectionHilbert_mean _ _) _ hlt
        intro k hk
        rw [hilbertGibbsPhysical_eq]
        exact optimizedCorrectionHilbert_below (n + 1) (k + 1) (Nat.succ_pos n) (by omega)
      rw [inner_smul_left, RCLike.conj_to_real, hz, tailBasis_inner,
        if_neg (by omega)]
      ring

/-- Every future transfer coefficient is a finite expression in the actual
packet values, with the infinite mean-zero tail already evaluated exactly. -/
theorem optimizedFutureTransferVector_coordinate (n j : ℕ) (hj : n < j) :
    paretoHaarCoordinates (optimizedFutureTransferVector n) (some j) =
      ((n : ℝ) + 1) *
        ((∑ k ∈ Finset.range j, paretoWeight k *
          hilbertGibbsPhysical (optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n)) k) +
          hilbertGibbsPhysical (optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n)) j /
            ((j : ℝ) + 1)) := by
  rw [paretoHaarCoordinates_some, optimizedFutureTransferVector, inner_sub_left,
    inner_smul_left, RCLike.conj_to_real, tailBasis_inner, if_neg (by omega), sub_zero,
    tailBasis_coefficient_of_mean_zero _ j (optimizedCorrectionHilbert_mean _ _)]

theorem complementaryCorrection_mem_paretoFutureSubspace (n : ℕ) :
    complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n) ∈ paretoFutureSubspace n := by
  refine ⟨complementaryCorrectionHilbert_mean _ _, ?_⟩
  intro j hj
  rw [tailBasis_coefficient_at_first _ j (complementaryCorrectionHilbert_mean _ _) ?_]
  · rw [hilbertGibbsPhysical_eq,
      complementaryCorrectionHilbert_through (n + 1) (j + 1) (Nat.succ_pos n) (by omega),
      zero_div]
  · intro k hk
    rw [hilbertGibbsPhysical_eq]
    exact complementaryCorrectionHilbert_through (n + 1) (k + 1) (Nat.succ_pos n) (by omega)

/-- The future subspace has an explicit two-dimensional orthonormal pair,
so even the degenerate transfer case has a nonzero perpendicular witness. -/
theorem paretoFutureSubspace_orthogonal_witness (n : ℕ) (d : ThresholdHilbert) :
    ∃ w : ThresholdHilbert, w ∈ paretoFutureSubspace n ∧ w ≠ 0 ∧ inner ℝ w d = 0 := by
  apply LinearAlgebra.exists_nonzero_orthogonal_in_submodule
    (paretoFutureSubspace n) (tailBasisHilbert (n + 1)) (tailBasisHilbert (n + 2)) d
  · exact tailBasis_mem_paretoFutureSubspace n (n + 1) (by omega)
  · exact tailBasis_mem_paretoFutureSubspace n (n + 2) (by omega)
  · rw [← real_inner_self_eq_norm_sq, tailBasis_inner_self]
  · rw [← real_inner_self_eq_norm_sq, tailBasis_inner_self]
  · rw [tailBasis_inner, if_neg (by omega)]

def optimizedPacketTransferEnergy (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 *
    (‖optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n)‖ ^ 2 -
      (inner ℝ (optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n))
        (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n))) ^ 2 /
          ‖complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n)‖ ^ 2)

/-- Exact squared operator norm of the actual scalar/future transfer,
expressed as the sharp universal energy constant for the Hilbert sum norm.
No positivity, support, or dimensional hypothesis remains unproved. -/
theorem optimizedPacketTransfer_sharp_energy_iff (n : ℕ) (C : ℝ) :
    LinearAlgebra.SchurTransferEnergyBoundOn (paretoFutureSubspace n)
      (optimizedFutureTransferVector n)
      (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n)) C ↔
      optimizedPacketTransferEnergy n ≤ C := by
  unfold optimizedPacketTransferEnergy
  rw [LinearAlgebra.schurTransfer_sharp_iff _ _ _ C
    (complementaryCorrectionHilbert_ne_zero _ _)
    (optimizedFutureTransferVector_mem n)
    (complementaryCorrection_mem_paretoFutureSubspace n)
    (paretoFutureSubspace_orthogonal_witness n _)]
  have hh : ‖tailBasisHilbert n‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, tailBasis_inner_self]
  have hu : ((n : ℝ) + 1) *
      inner ℝ (optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n))
        (tailBasisHilbert n) = 1 := by
    simpa only [inner_smul_left, RCLike.conj_to_real] using
      optimizedCorrection_first_coefficient n
  have hd : inner ℝ (tailBasisHilbert n)
      (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n)) = 0 := by
    rw [real_inner_comm]
    exact (complementaryCorrection_mem_paretoFutureSubspace n).2 n le_rfl
  unfold optimizedFutureTransferVector
  rw [LinearAlgebra.normalized_repair_schur_tail_energy _ _ _ _
    (complementaryCorrectionHilbert_ne_zero _ _) hh hu hd]

def optimizedPacketFutureError (n : ℕ) : ThresholdHilbert :=
  (optimizedPacketIterate n - hilbertOne) -
    (inner ℝ (optimizedPacketIterate n - hilbertOne) (tailBasisHilbert n)) •
      tailBasisHilbert n

theorem optimizedPacketFutureError_mem (n : ℕ) :
    optimizedPacketFutureError n ∈ paretoFutureSubspace n := by
  refine ⟨?_, ?_⟩
  · simp [optimizedPacketFutureError, inner_sub_left, inner_smul_left,
      optimizedPacketIterate_mean, tailBasis_inner_one,
      real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  · intro j hj
    unfold optimizedPacketFutureError
    rw [inner_sub_left, inner_smul_left, RCLike.conj_to_real]
    by_cases he : j = n
    · subst j
      rw [tailBasis_inner_self]
      ring
    · rw [optimizedPacketIterate_error_coefficients_before n j (by omega),
        tailBasis_inner, if_neg (by omega)]
      ring

/-- The precise causal transfer identity for the specified arithmetic orbit,
before choosing coordinates. The whole future error and both projected packet
terms remain present. -/
theorem optimizedPacketIterate_error_transfer (n : ℕ) :
    optimizedPacketIterate (n + 1) - hilbertOne =
      LinearAlgebra.schurRemove
        (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n))
        (optimizedPacketFutureError n) -
      (inner ℝ (optimizedPacketIterate n - hilbertOne) (tailBasisHilbert n)) •
        LinearAlgebra.schurRemove
          (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n))
          (optimizedFutureTransferVector n) := by
  have horth : inner ℝ hilbertOne
      (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n)) = 0 := by
    rw [real_inner_comm, complementaryCorrectionHilbert_mean]
  rw [optimizedPacketIterate, paretoPacketStep, LinearAlgebra.schurRepair_error
    _ _ _ _ _ horth]
  have hv (e u h : ThresholdHilbert) (a b : ℝ) :
      e + (-(b * a)) • u = (e - a • h) - a • (b • u - h) := by
    simp only [neg_smul, smul_sub, smul_smul]
    rw [mul_comm b a]
    abel
  have he :
      (optimizedPacketIterate n - hilbertOne) +
        (1 - hilbertSequence (optimizedPacketIterate n) (n + 1)) •
          optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n) =
      optimizedPacketFutureError n -
        (inner ℝ (optimizedPacketIterate n - hilbertOne) (tailBasisHilbert n)) •
          optimizedFutureTransferVector n := by
    change (optimizedPacketIterate n - hilbertOne) + optimizedPacketResidual n •
      optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n) = _
    rw [optimizedPacketResidual_tail_coefficient]
    rw [neg_mul]
    exact hv _ _ _ _ _
  rw [he, LinearAlgebra.schurRemove_sub, LinearAlgebra.schurRemove_smul]

/-- Formula (30) in a complete bundled coordinate space. The mean-zero and
already-corrected coordinates vanish exactly, so this is the same tail orbit. -/
theorem optimizedPacketIterate_coordinate_transfer (n : ℕ) :
    paretoHaarCoordinates (optimizedPacketIterate (n + 1) - hilbertOne) =
      paretoHaarCoordinates (LinearAlgebra.schurRemove
        (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n))
        (optimizedPacketFutureError n)) -
      (paretoHaarCoordinates (optimizedPacketIterate n - hilbertOne) (some n)) •
        paretoHaarCoordinates (LinearAlgebra.schurRemove
          (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n))
          (optimizedFutureTransferVector n)) := by
  rw [optimizedPacketIterate_error_transfer, map_sub, map_smul,
    paretoHaarCoordinates_some]

end
end RiemannResearch.RH.Pareto
