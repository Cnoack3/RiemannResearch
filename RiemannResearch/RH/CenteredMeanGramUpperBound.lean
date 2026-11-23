import RiemannResearch.RH.CenteredMeanDyadicGram
import RiemannResearch.RH.ParetoConductor241Covariance
import RiemannResearch.RH.ParetoProjectionOvershoot

/-!
# A uniform finite upper bound for the first-site Gram solve

Pair the upper residual with the dyadic dilation of a lower residual. The
conductor-241 signed covariance certificate bounds the lower energy at
stage 240. Its dilation is admissible at every stage starting with 481.
-/

noncomputable section
open scoped Matrix
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

open CoefficientStabilization MixedConductorBasis RamanujanCanonicalOptimizer PacketGramBoundary

/-- Every upper Gram solve is bounded in terms of the actual energy at a
lower cutoff whose doubled span is already present. -/
theorem firstSiteGramCoordinates_upper_of_doubleStage_le (k n : ℕ) (hn : doubleStage k ≤ n) :
    let p := firstSiteGramCoordinates n
    p.2 ≤ (2 - Real.sqrt 2) * p.1 + firstSiteQuadraticAllowance * p.1^2 +
      2 * Real.sqrt 2 * energy k := by
  rw [firstSiteGramCoordinates_eq, ← projectionResidual_first_eq_one_sub_projection]
  dsimp only
  let b := hilbertSequence (projectionResidual n) 1
  have hk : 0 ≤ energy k := sq_nonneg _
  have hnk : energy n ≤ energy k := energy_antitone (by
    dsimp [doubleStage] at hn
    omega)
  have hg := finite_endpoint_gram_of_le k n hn
  change (energy n - b / 2)^2 ≤ energy k / 2 * (energy n - b^2 / 2) at hg
  have hprod := mul_le_mul_of_nonneg_left
    (show energy n - b^2 / 2 ≤ energy k by linarith only [hnk, sq_nonneg b])
    (show 0 ≤ energy k / 2 by positivity)
  have hs : (Real.sqrt 2 * energy k)^2 = 2 * (energy k)^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsq : (b - 2 * energy n)^2 ≤ (Real.sqrt 2 * energy k)^2 := by
    rw [hs]
    nlinarith only [hg.trans hprod]
  have hupper : b - 2 * energy n ≤ Real.sqrt 2 * energy k := by
    by_contra! h
    exact (not_lt_of_ge hsq) (by
      simpa only [pow_two] using
        mul_self_lt_mul_self (mul_nonneg (Real.sqrt_nonneg _) hk) h)
  have hallow : 0 ≤ firstSiteQuadraticAllowance * (energy n)^2 :=
    mul_nonneg (by linarith only [half_lt_firstSiteQuadraticAllowance]) (sq_nonneg _)
  change b ≤ _
  nlinarith only [hupper, hallow, mul_le_mul_of_nonneg_left hnk (Real.sqrt_nonneg 2)]

/-- The conductor-241 trial gives a uniform one-sided Gram bound at every
stage from 481 on. All quantities in the solve are the actual packet data. -/
theorem quadratic_gram_solve_le_one_fortieth (n : ℕ) (hn : 481 ≤ n) :
    let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
    let e := 1 - dotProduct (meanVector n) c
    1 + dotProduct (finiteMoebiusSource n) c ≤
      (2 - Real.sqrt 2) * e + firstSiteQuadraticAllowance * e^2 + 1/40 := by
  have h := firstSiteGramCoordinates_upper_of_doubleStage_le 240 n hn
  have hE := RiemannResearch.RH.GroupedResidueMass.Conductor241.energy_le_conductor_241_covariance
  have hs : Real.sqrt 2 ≤ 99/70 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      sq_nonneg (Real.sqrt 2 - 99/70)]
  have hbound : 2 * Real.sqrt 2 * energy 240 ≤ 1/40 := by
    calc
      _ ≤ 2 * Real.sqrt 2 * (2093945167971946997/238620217000000000000) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ 2 * (99/70) * (2093945167971946997/238620217000000000000) := by
        gcongr
      _ ≤ _ := by norm_num
  exact h.trans (add_le_add le_rfl hbound)

/-- A cofinal witness at every tolerance at least one fortieth. -/
theorem cofinal_quadratic_gram_solve_of_one_fortieth_le {ε : ℝ} (hε : 1/40 ≤ ε) (N : ℕ) :
    ∃ n ≥ N,
      let p := firstSiteGramCoordinates n
      p.2 ≤ (2 - Real.sqrt 2) * p.1 + firstSiteQuadraticAllowance * p.1^2 + ε := by
  refine ⟨max N 481, le_max_left _ _, ?_⟩
  exact (quadratic_gram_solve_le_one_fortieth _ (le_max_right _ _)).trans
    (add_le_add le_rfl hε)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
