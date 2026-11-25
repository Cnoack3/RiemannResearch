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

/-- A rational certificate for the two-stage Gram inequality. The slope
`2 - 99/70 + 1/120` comes from a tangent to the quadratic allowance.
The signed polynomial identity retains the full square after shifting to the
conductor-241 upper endpoint. -/
private theorem firstSite_conductor241_polynomial_bound {e b : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 8776 / 1000000)
    (hg : (b - 2*e)^2 + (8776/1000000 : ℝ)*b^2 ≤ 2*(8776/1000000 : ℝ)*e) :
    b ≤ (2 - Real.sqrt 2)*e + firstSiteQuadraticAllowance*e^2 + 49/2000 := by
  let r : ℝ := 8776/1000000
  let m : ℝ := 2 - 99/70 + 1/120
  let h : ℝ := 49/2000 - 1/28800
  let g (x : ℝ) := (h+(m-2)*x)^2 + r*(h+m*x)^2 - 2*r*x
  let A := (m-2)^2 + r*m^2
  let B := 2*r - 2*(m-2)*(h+(m-2)*r) - 2*r*m*(h+m*r)
  have hr : 0 ≤ r := by norm_num [r]
  have hA : 0 ≤ A := by norm_num [A, r, m]
  have hB : 0 ≤ B := by norm_num [B, r, m, h]
  have hend : 0 < g r := by norm_num [g, r, m, h]
  have hexact : g e = g r + B*(r-e) + A*(r-e)^2 := by
    dsimp only [g, A, B]
    ring
  have hgpos : 0 < g e := by
    rw [hexact]
    have hre : 0 ≤ r - e := sub_nonneg.mpr he
    linarith only [hend, mul_nonneg hB hre, mul_nonneg hA (sq_nonneg (r-e))]
  have hs : Real.sqrt 2 ≤ 99/70 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), sq_nonneg (Real.sqrt 2 - 99/70)]
  by_contra! hgt
  have hline : h + m*e < b := by
    dsimp only [h, m]
    nlinarith only [hgt, mul_le_mul_of_nonneg_right hs he0, sq_nonneg (e-1/120),
      mul_le_mul_of_nonneg_right half_lt_firstSiteQuadraticAllowance.le (sq_nonneg e)]
  have hd : 0 ≤ h + (m-2)*e := calc
    0 ≤ h + (m-2)*r := by norm_num [h, m, r]
    _ ≤ h + (m-2)*e := by
      exact add_le_add le_rfl (mul_le_mul_of_nonpos_left (show e ≤ r from he)
        (by norm_num [m] : m-2 ≤ 0))
  have ha : 0 ≤ h + m*e := by linarith only [hd, he0]
  have hsq₁ := mul_self_le_mul_self hd
    (show h + (m-2)*e ≤ b - 2*e by linarith only [hline.le])
  have hsq₂ := mul_self_le_mul_self ha hline.le
  have hscaled := mul_le_mul_of_nonneg_left hsq₂ hr
  change (b - 2*e)^2 + r*b^2 ≤ 2*r*e at hg
  dsimp only [g] at hgpos
  nlinarith only [hg, hgpos, hsq₁, hscaled]

/-- Every actual packet Gram solve from stage 481 satisfies the quadratic
first-site estimate at tolerance 49/2000. This uses the cross-stage Gram
bound before discarding its signed first-site correction. -/
theorem quadratic_gram_solve_le_forty_nine_two_thousandths (n : ℕ) (hn : 481 ≤ n) :
    let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
    let e := 1 - dotProduct (meanVector n) c
    1 + dotProduct (finiteMoebiusSource n) c ≤
      (2 - Real.sqrt 2) * e + firstSiteQuadraticAllowance * e^2 + 49/2000 := by
  change (firstSiteGramCoordinates n).2 ≤ (2 - Real.sqrt 2) * (firstSiteGramCoordinates n).1 +
    firstSiteQuadraticAllowance * (firstSiteGramCoordinates n).1^2 + 49/2000
  rw [firstSiteGramCoordinates_eq, ← projectionResidual_first_eq_one_sub_projection]
  dsimp only
  let e := energy n
  let b := hilbertSequence (projectionResidual n) 1
  have hR : energy 240 ≤ (8776/1000000 : ℝ) :=
    RiemannResearch.RH.GroupedResidueMass.Conductor241.energy_le_conductor_241_covariance.trans
      (by norm_num)
  have he : e ≤ (8776/1000000 : ℝ) :=
    (energy_antitone (by omega : 240 ≤ n)).trans hR
  have hr : 0 ≤ e - b^2/2 := by
    have h := remove_firstPoint_norm_sq (projectionResidual n)
    change ‖projectionResidual n - b • paretoPointHilbert 0‖^2 = e - b^2/2 at h
    rw [← h]
    exact sq_nonneg _
  have hg := finite_endpoint_gram_of_le 240 n hn
  change (e - b/2)^2 ≤ (energy 240 / 2) * (e - b^2/2) at hg
  apply firstSite_conductor241_polynomial_bound (sq_nonneg _) he
  have hu := mul_le_mul_of_nonneg_right
    (show energy 240 / 2 ≤ (8776/1000000 : ℝ) / 2 by linarith only [hR]) hr
  change (b - 2*e)^2 + (8776/1000000 : ℝ)*b^2 ≤ 2*(8776/1000000 : ℝ)*e
  nlinarith only [hg.trans hu]

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
