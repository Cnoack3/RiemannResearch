import RiemannResearch.RH.ParetoParityAdjointHeads

/-! Complete error of the consecutive-conductor Möbius lift of the adjoint
parity profile. On the head the error vanishes. A telescoping sum of the
positive profile jumps bounds the whole remaining physical tail. -/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

private def adjointJumpAt (k : ℕ) : ℝ :=
  hilbertSequence parityAdjointPacket k - hilbertSequence parityAdjointPacket (k-1)

private theorem adjointJumpAt_nonneg {k : ℕ} (hk : 0 < k) :
    0 ≤ adjointJumpAt k := by
  unfold adjointJumpAt
  rw [parityAdjointPacket_jump k hk]
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

private theorem sum_adjointJumpAt (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, adjointJumpAt k = hilbertSequence parityAdjointPacket N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, adjointJumpAt]
    simp only [Nat.add_sub_cancel]
    ring

/-- Every physical coordinate, including those beyond the prescribed head. -/
theorem parityAdjointMobiusHead_site_bound (N j : ℕ) :
    |hilbertSequence (mobiusHeadInterpolation N parityAdjointPacket) j| ≤ (N:ℝ) := by
  have he : hilbertSequence (mobiusHeadInterpolation N parityAdjointPacket) j =
      ∑ k ∈ (Finset.Icc 1 N).attach, adjointJumpAt k *
        hilbertSequence (mobiusHeadStep N k
          (by have := (Finset.mem_Icc.mp k.property).1; omega)) j := by
    change hilbertSequenceLinear (mobiusHeadInterpolation N parityAdjointPacket) j = _
    unfold mobiusHeadInterpolation
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [he]
  calc
    _ ≤ ∑ k ∈ (Finset.Icc 1 N).attach,
        |adjointJumpAt k * hilbertSequence (mobiusHeadStep N k _) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.Icc 1 N).attach, adjointJumpAt k * (2*(N:ℝ)+1) := by
      apply Finset.sum_le_sum
      intro k hmem
      have hk : 0 < (k:ℕ) := (Finset.mem_Icc.mp k.property).1
      have hkR : (1:ℝ) ≤ ((k:ℕ):ℝ) := by exact_mod_cast hk
      rw [abs_mul, abs_of_nonneg (adjointJumpAt_nonneg hk)]
      apply mul_le_mul_of_nonneg_left _ (adjointJumpAt_nonneg hk)
      apply (mobiusHeadStep_sequence_abs_le N k hk (Finset.mem_Icc.mp k.property).2 j).trans
      apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hkR)).mpr
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hkR (show 0 ≤ 2*(N:ℝ)+1 by positivity)
    _ = (N:ℝ) := by
      rw [Finset.sum_attach (Finset.Icc 1 N) (fun k : ℕ => adjointJumpAt k * (2*(N:ℝ)+1)),
        ← Finset.sum_mul, sum_adjointJumpAt, parityAdjointPacket_coordinate]
      exact div_mul_cancel₀ _ (by positivity)

/-- The bound is for the original stage N vector supported on conductors through N+1. -/
theorem parityAdjointMobiusHead_error_sq_le (N : ℕ) :
    ‖parityAdjointPacket - mobiusHeadInterpolation N parityAdjointPacket‖^2 ≤
      ((N:ℝ)+1/2)^2 / ((N:ℝ)+1) := by
  let e := parityAdjointPacket - mobiusHeadInterpolation N parityAdjointPacket
  have hzero : compactHead N e = 0 := by
    rw [show e = parityAdjointPacket - mobiusHeadInterpolation N parityAdjointPacket from rfl,
      compactHead_sub, compactHead_mobiusHeadInterpolation, sub_self]
  have hb (j : ℕ) : |hilbertSequence e j| ≤ (N:ℝ)+1/2 := by
    have hg : |hilbertSequence parityAdjointPacket j| ≤ 1/2 := by
      rw [parityAdjointPacket_coordinate, abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    change |hilbertSequence (parityAdjointPacket - mobiusHeadInterpolation N parityAdjointPacket) j| ≤ _
    rw [hilbertSequence_sub, Pi.sub_apply]
    calc
      _ ≤ |hilbertSequence parityAdjointPacket j| +
          |hilbertSequence (mobiusHeadInterpolation N parityAdjointPacket) j| :=
        abs_sub _ _
      _ ≤ 1/2+(N:ℝ) := add_le_add hg (parityAdjointMobiusHead_site_bound N j)
      _ = _ := add_comm _ _
  have h := compactHead_complete_tail_norm_sq_le_of_sequence_bound N e ((N:ℝ)+1/2) hb
  rwa [hzero, sub_zero] at h

end RiemannResearch.RH.Pareto.PrimePowerSchur
