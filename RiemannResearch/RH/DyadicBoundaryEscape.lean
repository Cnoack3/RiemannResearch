import RiemannResearch.RH.DyadicBoundaryLegalRecovery

/-!
# Boundary energy can escape every finite prefix

Source: user-provided DyadicGramPrefixVerification20260910(1).md,
September 10, 2026, continuation; the example is an elementary consequence
of the established physical boundary orthogonality and exact Parseval identity.

These are actual physical vectors with exact mean one, zero complementary
energy, and uniformly bounded norm. Every fixed boundary coordinate eventually
vanishes, while the complete boundary energy and approximation error remain one.
No membership in the two-seed legal space is asserted. Thus the example isolates
a norm-convergence gap; it does not refute any arithmetic density claim.
-/

namespace RiemannResearch.RH.Pareto
open Filter
open scoped BigOperators Topology
noncomputable section

/-- One normalized boundary detail moves to index n+1. -/
def dyadicBoundaryEscape (n : ℕ) : ThresholdHilbert :=
  hilbertOne + (2 : ℝ) • dyadicQuotientProjection
    (dyadicStepBoundary (n+1) (by positivity))

theorem dyadicBoundaryEscape_mean (n : ℕ) :
    inner ℝ hilbertOne (dyadicBoundaryEscape n) = 1 := by
  have hb : inner ℝ hilbertOne (dyadicQuotientProjection
      (dyadicStepBoundary (n+1) (by positivity))) = 0 := by
    rw [real_inner_comm, dyadicProjectedBoundary_inner_one]
  simp only [dyadicBoundaryEscape, inner_add_right, real_inner_smul_right,
    hb, mul_zero, add_zero, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]

theorem dyadicBoundaryEscape_projection (n : ℕ) :
    dyadicQuotientProjection (dyadicBoundaryEscape n) = dyadicBoundaryEscape n := by
  simp only [dyadicBoundaryEscape, map_add, map_smul,
    dyadicQuotientProjection_one, dyadicQuotientProjection_idempotent]

theorem dyadicBoundaryEscape_complement_norm_sq (n : ℕ) :
    ‖dyadicBoundaryEscape n - dyadicQuotientProjection (dyadicBoundaryEscape n)‖^2 =
      (0 : ℝ) := by
  rw [dyadicBoundaryEscape_projection, sub_self, norm_zero]
  norm_num

theorem dyadicBoundaryEscape_error_norm_sq (n : ℕ) :
    ‖hilbertOne - dyadicBoundaryEscape n‖^2 = (1 : ℝ) := by
  have he : hilbertOne - dyadicBoundaryEscape n =
      -((2 : ℝ) • dyadicQuotientProjection
        (dyadicStepBoundary (n+1) (by positivity))) := by
    unfold dyadicBoundaryEscape
    abel
  rw [he, norm_neg, norm_smul, mul_pow, dyadicProjectedBoundary_norm_sq]
  norm_num

/-- The entire physical sequence is bounded, not only its quotient coordinates. -/
theorem dyadicBoundaryEscape_norm_sq (n : ℕ) :
    ‖dyadicBoundaryEscape n‖^2 = (2 : ℝ) := by
  have hb : inner ℝ hilbertOne (dyadicQuotientProjection
      (dyadicStepBoundary (n+1) (by positivity))) = 0 := by
    rw [real_inner_comm, dyadicProjectedBoundary_inner_one]
  rw [dyadicBoundaryEscape, norm_add_sq_real, hilbertOne_norm_sq,
    real_inner_smul_right, hb, norm_smul, mul_pow, dyadicProjectedBoundary_norm_sq]
  norm_num

/-- The exact coordinate, including its one nonzero location. -/
theorem dyadicBoundaryEscape_pairing (k n : ℕ) :
    inner ℝ (dyadicQuotientProjection
      (dyadicStepBoundary (k+1) (by positivity))) (dyadicBoundaryEscape n) =
        if k = n then (1/2 : ℝ) else 0 := by
  rw [dyadicBoundaryEscape, inner_add_right, dyadicProjectedBoundary_inner_one,
    zero_add, real_inner_smul_right]
  by_cases h : k = n
  · subst n
    rw [real_inner_self_eq_norm_sq, dyadicProjectedBoundary_norm_sq]
    norm_num
  · rw [dyadicProjectedBoundary_inner_boundary (k+1) (n+1)
      (by positivity) (by positivity) (by omega)]
    simp only [h, if_false, mul_zero]

theorem dyadicBoundaryEscape_pairing_eventually_zero (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      inner ℝ (dyadicQuotientProjection
        (dyadicStepBoundary (k+1) (by positivity))) (dyadicBoundaryEscape n) = 0 := by
  filter_upwards [eventually_ge_atTop (k+1)] with n hn
  rw [dyadicBoundaryEscape_pairing, if_neg (by omega : k ≠ n)]

theorem dyadicBoundaryEscape_pairing_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => inner ℝ (dyadicQuotientProjection
      (dyadicStepBoundary (k+1) (by positivity))) (dyadicBoundaryEscape n))
      atTop (𝓝 (0 : ℝ)) := by
  exact (tendsto_congr' (dyadicBoundaryEscape_pairing_eventually_zero k)).mpr
    tendsto_const_nhds

/-- Every finite boundary-energy test is identically zero after its cutoff. -/
theorem dyadicBoundaryEscape_prefixEnergy_eq_zero (N n : ℕ) (hN : N ≤ n) :
    (∑ k ∈ Finset.range N, 4 * (inner ℝ (dyadicQuotientProjection
      (dyadicStepBoundary (k+1) (by positivity))) (dyadicBoundaryEscape n))^2) =
        (0 : ℝ) := by
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k ≠ n := Nat.ne_of_lt ((Finset.mem_range.mp hk).trans_le hN)
  simp only [dyadicBoundaryEscape_pairing, hkn, if_false, zero_pow
    (by norm_num : 2 ≠ 0), mul_zero]

/-- Full infinite boundary energy does not follow the finite-prefix tests to zero. -/
theorem dyadicBoundaryEscape_detailEnergy (n : ℕ) :
    dyadicBoundaryDetailEnergy (dyadicBoundaryEscape n) = (1 : ℝ) := by
  have he := dyadicBoundary_full_error_sq (dyadicBoundaryEscape n)
  change ‖hilbertOne - dyadicBoundaryEscape n‖^2 =
    (1 - inner ℝ hilbertOne (dyadicBoundaryEscape n))^2 +
      dyadicBoundaryDetailEnergy (dyadicBoundaryEscape n) +
      ‖dyadicBoundaryEscape n - dyadicQuotientProjection (dyadicBoundaryEscape n)‖^2 at he
  rw [dyadicBoundaryEscape_error_norm_sq, dyadicBoundaryEscape_mean,
    dyadicBoundaryEscape_complement_norm_sq] at he
  nlinarith

/-- Failure of convergence is exact, despite mean and all fixed-coordinate tests. -/
theorem dyadicBoundaryEscape_not_tendsto_one :
    ¬Tendsto dyadicBoundaryEscape atTop (𝓝 hilbertOne) := by
  intro h
  have hb := ((dyadicBoundary_tendsto_one_iff dyadicBoundaryEscape).mp h).2.1
  have h1 : Tendsto (fun n => dyadicBoundaryDetailEnergy (dyadicBoundaryEscape n))
      atTop (𝓝 (1 : ℝ)) := by
    simp only [dyadicBoundaryEscape_detailEnergy]
    exact tendsto_const_nhds
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique h1 hb
  norm_num at h10

end
end RiemannResearch.RH.Pareto
