import RiemannResearch.RH.ThresholdStepTruncation
import RiemannResearch.RH.DyadicRegularizedBoundaryCoefficients
import RiemannResearch.RH.DyadicBoundaryUniformCriterion

/-!
# Signed residue step approximations and complete boundary error

Source: user-provided DyadicSignedBoundaryAbelVerification20260910(1).md
and the retained DyadicBoundaryFourierResearchNote20260910.md, September 10, 2026.
The present proofs establish the stated bounded continuation targets.

The fixed-conductor error is bounded by (a-1)^2/(K+1), including the full
infinite boundary square sum. The dependence on a is explicit and does not
supply a uniform conductor-and-damping arithmetic estimate.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem hilbertResidue_stepJumpPrefix_error_sq_le (a : ℕ) (ha : 0 < a) (K : ℕ) :
    ‖hilbertStepJumpPrefix (hilbertResidue a ha) K - hilbertResidue a ha‖^2 ≤
      ((a : ℝ)-1)^2 / (K+1 : ℝ) := by
  apply hilbertStepJumpPrefix_error_sq_le
  intro n
  rw [hilbertResidue_sequence]
  simp only [residue]
  have hK := Nat.mod_lt K ha
  have hn := Nat.mod_lt n ha
  have hKr : ((K % a : ℕ) : ℝ)+1 ≤ a := by exact_mod_cast (Nat.succ_le_of_lt hK)
  have hnr : ((n % a : ℕ) : ℝ)+1 ≤ a := by exact_mod_cast (Nat.succ_le_of_lt hn)
  rw [abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ (K % a : ℕ) by positivity,
    show (0 : ℝ) ≤ (n % a : ℕ) by positivity]

theorem hilbertStepJumpPrefix_boundaryCoordinate (f : ThresholdHilbert) (K i : ℕ) :
    dyadicBoundaryCoordinate (hilbertStepJumpPrefix f K) i =
      ∑ j ∈ Finset.range K,
        ((hilbertSequence f (j+1) - hilbertSequence f j) / (j+1 : ℝ)) *
          dyadicBoundaryCoordinate (dyadicProjectedStep (j+1) (by positivity)) i := by
  unfold hilbertStepJumpPrefix dyadicBoundaryCoordinate
  rw [inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_smul_right]
  have hp := dyadicBoundaryCoordinate_projection
    (hilbertDilation (j+1) (by positivity) hilbertOne) i
  dsimp [dyadicProjectedStep, dyadicBoundaryCoordinate] at hp ⊢
  rw [hp]
  ring

open Filter

theorem hilbertResidue_stepJumpPrefix_tendsto (a : ℕ) (ha : 0 < a) :
    Tendsto (hilbertStepJumpPrefix (hilbertResidue a ha)) atTop
      (nhds (hilbertResidue a ha)) := by
  apply hilbertStepJumpPrefix_tendsto_of_bounded _ (a : ℝ)
  intro n
  rw [hilbertResidue_sequence]
  exact residue_abs_le a n ha

theorem hilbertResidue_stepJumpPrefix_boundary_error_le
    (a : ℕ) (ha : 0 < a) (K : ℕ) :
    (∑' i : ℕ, (1/4 : ℝ) *
      (dyadicBoundaryCoordinate (hilbertStepJumpPrefix (hilbertResidue a ha) K) i -
        dyadicBoundaryCoordinate (hilbertResidue a ha) i)^2) ≤
      ((a : ℝ)-1)^2 / (K+1 : ℝ) := by
  have hb := dyadicBoundaryCoordinate_square_tsum_le_norm_sq
    (hilbertStepJumpPrefix (hilbertResidue a ha) K - hilbertResidue a ha)
  simp only [dyadicBoundaryCoordinate_sub] at hb
  exact hb.trans (hilbertResidue_stepJumpPrefix_error_sq_le a ha K)

/-- The exact residue jump, including its negative reset at each multiple. -/
theorem natResidue_cast_jump (a k : ℕ) (ha : 0 < a) :
    (((k + 1) % a : ℕ) : ℝ) - ((k % a : ℕ) : ℝ) =
      1 - if a ∣ k + 1 then (a : ℝ) else 0 := by
  by_cases ha1 : a = 1
  · subst a
    simp
  have h1 : 1 < a := by omega
  have hk : k % a < a := Nat.mod_lt _ ha
  have hmod : (k + 1) % a = (k % a + 1) % a := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt h1]
  by_cases hwrap : k % a + 1 = a
  · have hz : (k + 1) % a = 0 := by rw [hmod, hwrap, Nat.mod_self]
    have hd : a ∣ k + 1 := Nat.dvd_of_mod_eq_zero hz
    rw [if_pos hd, hz]
    have hc : ((k % a : ℕ) : ℝ) + 1 = (a : ℝ) := by exact_mod_cast hwrap
    simp only [Nat.cast_zero]
    linarith
  · have hlt : k % a + 1 < a := by omega
    have hval : (k + 1) % a = k % a + 1 := by
      rw [hmod, Nat.mod_eq_of_lt hlt]
    have hd : ¬ a ∣ k + 1 := by
      intro h
      have hz := Nat.mod_eq_zero_of_dvd h
      rw [hval] at hz
      omega
    rw [if_neg hd, hval]
    push_cast
    ring

/-- The complete finite arithmetic jump sum, including every negative reset. -/
theorem hilbertResidue_stepJumpPrefix_signed_boundary
    (a : ℕ) (ha : 0 < a) (K i : ℕ) :
    dyadicBoundaryCoordinate (hilbertStepJumpPrefix (hilbertResidue a ha) K) i =
      ∑ j ∈ Finset.range K,
        ((1 - if a ∣ j+1 then (a : ℝ) else 0) / (j+1 : ℝ)) *
          dyadicBoundaryCoordinate (dyadicProjectedStep (j+1) (by positivity)) i := by
  rw [hilbertStepJumpPrefix_boundaryCoordinate]
  simp only [hilbertResidue_sequence, residue, natResidue_cast_jump a _ ha]

end
end RiemannResearch.RH.Pareto
