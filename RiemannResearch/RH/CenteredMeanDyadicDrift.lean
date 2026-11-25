import RiemannResearch.RH.CenteredMeanDriftCutoffs
import RiemannResearch.Analysis.StretchedExponentialBounds

/-!
# An explicit dyadic range of uniformly small later Gram solves

At horizon `2^j`, the physical cutoff `2^(2(qj)^11)` makes the cubic
head-interpolation bound exponentially small in `j`. The estimate is
simultaneous over all ordered base and later solve cutoffs within the horizon
and retains their exact reciprocal-mass gain.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open RamanujanCanonicalOptimizer RiemannResearch.Analysis

/-- The physical cutoff for a dyadic later-solve horizon at index `j`. -/
def dyadicDriftCutoff (q j : ℕ) : ℕ := 2 ^ (2 * (q * j) ^ 11)

private theorem dyadic_damping_le (b : ℝ) (hb : 0 < b) (q j : ℕ) (hq : 4 ≤ b * (q : ℝ)) :
    sectionTailDamping b (dyadicDriftCutoff q j) ≤ Real.exp (-4 * (j : ℝ)) := by
  let N := dyadicDriftCutoff q j
  let X := 6 + Real.log (N : ℝ)
  let t := (q : ℝ) * (j : ℝ)
  have hlog : Real.log (N : ℝ) = 2 * t ^ 11 * Real.log 2 := by
    simp only [N, dyadicDriftCutoff, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow,
      Nat.cast_mul, t]
  have htwo : 1 ≤ 2 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsix : 6 ≤ X := by
    dsimp only [X]
    rw [hlog]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    apply le_add_of_nonneg_right
    positivity
  have hbase : t ^ 11 ≤ X * Real.log X := by
    have hx : t ^ 11 ≤ X := by
      dsimp only [X]
      rw [hlog]
      linarith only [mul_le_mul_of_nonneg_right htwo (pow_nonneg ht 11)]
    exact hx.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (one_le_log_of_six_le hsix) (by linarith : 0 ≤ X))
  have hpow : (t ^ (11 : ℕ)) ^ (1 / 11 : ℝ) = t := by
    rw [← Real.rpow_natCast_mul ht]
    norm_num
  have hphi : t ≤ logProductPower (1 / 11) X := by
    simpa only [hpow, logProductPower] using
      Real.rpow_le_rpow (pow_nonneg ht 11) hbase (by norm_num : (0 : ℝ) ≤ 1 / 11)
  change Real.exp (-b * logProductPower (1 / 11) X) ≤ _
  apply Real.exp_le_exp.mpr
  change (q : ℝ) * (j : ℝ) ≤ _ at hphi
  linarith only [mul_le_mul_of_nonneg_left hphi hb.le,
    mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (α := ℝ) j)]

private theorem dyadic_amplification_le (A j : ℕ) (hAj : A ≤ 2 ^ j) :
    gramCutoffAmplification A ≤ 200 * ((2 : ℝ) ^ j) ^ 3 := by
  let t := (2 : ℝ) ^ j
  have ht : 1 ≤ t := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ))
  have ha : (A : ℝ) ≤ t := by dsimp only [t]; exact_mod_cast hAj
  have h₁ : (A : ℝ) + 1 ≤ 2 * t := by linarith
  have h₂ : 2 * ((A : ℝ) + 1) + 1 ≤ 5 * t := by linarith
  calc
    gramCutoffAmplification A ≤ 4 * (5 * t) ^ 2 * (2 * t) := by
      unfold gramCutoffAmplification
      gcongr
    _ = 200 * t ^ 3 := by ring

private theorem dyadic_damped_amplification_le (b : ℝ) (hb : 0 < b) (q j A : ℕ)
    (hq : 4 ≤ b * (q : ℝ)) (hA : A ≤ 2 ^ j) :
    sectionTailDamping b (dyadicDriftCutoff q j) * gramCutoffAmplification A ≤
      200 * Real.exp (-(j : ℝ)) := by
  have hpos : 0 ≤ gramCutoffAmplification A := by unfold gramCutoffAmplification; positivity
  have hlog : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]
  have hpow : (2 : ℝ) ^ j ≤ Real.exp (j : ℝ) := by
    calc
      _ = Real.exp ((j : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
      _ ≤ Real.exp (j : ℝ) := Real.exp_le_exp.mpr (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) j))
  calc
    _ ≤ Real.exp (-4 * (j : ℝ)) * (200 * (Real.exp (j : ℝ)) ^ 3) := by
      apply mul_le_mul (dyadic_damping_le b hb q j hq) _ hpos (Real.exp_pos _).le
      exact (dyadic_amplification_le A j hA).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpow 3) (by norm_num))
    _ = 200 * Real.exp (-(j : ℝ)) := by
      have he : Real.exp (j : ℝ) ^ 3 = Real.exp (3 * (j : ℝ)) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (j : ℝ) 3).symm
      calc
        _ = 200 * (Real.exp (-4 * (j : ℝ)) * Real.exp (3 * (j : ℝ))) := by rw [he]; ring
        _ = _ := by rw [← Real.exp_add, show -4 * (j : ℝ) + 3 * j = -j by ring]

/-- A single physical cutoff controls all actual later solves through the dyadic
horizon. Its prefactor decays exponentially in the horizon index, and the
remaining factor is exactly the complete reciprocal-mass gain of the two solves. -/
theorem dyadic_finiteSectionTailDrift_le (b : ℝ) (hb : 0 < b) (q j B A : ℕ)
    (hq : 4 ≤ b * (q : ℝ)) (hBA : B ≤ A) (hA : A ≤ 2 ^ j) :
    (dyadicDriftCutoff q j : ℝ) * sectionTailDamping b (dyadicDriftCutoff q j) *
      finiteSectionTailDrift B A (dyadicDriftCutoff q j) ≤
        200 * Real.exp (-(j : ℝ)) * ((packetMass (B + 1))⁻¹ - (packetMass (A + 1))⁻¹) := by
  have h := finiteSectionTailDrift_scaled_le_cutoffGain b B A (dyadicDriftCutoff q j) hBA
  have hg : 0 ≤ (packetMass (B + 1))⁻¹ - (packetMass (A + 1))⁻¹ := by
    rw [← packetUnitMean_nested_distance B A hBA]
    exact sq_nonneg _
  exact h.trans (mul_le_mul_of_nonneg_right (dyadic_damped_amplification_le b hb q j A hq hA) hg)

/-- Base costs obey the same uniform exponential budget over the dyadic
later-solve horizon. No estimate of a least common multiple enters either bound. -/
theorem dyadic_finiteSectionTailCost_le (b : ℝ) (hb : 0 < b) (q j B : ℕ)
    (hq : 4 ≤ b * (q : ℝ)) (hB : B ≤ 2 ^ j) :
    (dyadicDriftCutoff q j : ℝ) * sectionTailDamping b (dyadicDriftCutoff q j) *
      finiteSectionTailCost B (dyadicDriftCutoff q j) ≤
        (2 + 400 * (packetMass (B + 1))⁻¹) * Real.exp (-(j : ℝ)) := by
  apply (finiteSectionTailCost_scaled_le_cutoffMass b B (dyadicDriftCutoff q j)).trans
  have h₁ := (dyadic_damping_le b hb q j hq).trans
    (Real.exp_le_exp.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) j] :
      -4 * (j : ℝ) ≤ -(j : ℝ)))
  have hm : 0 ≤ (packetMass (B + 1))⁻¹ := (inv_pos.mpr (packetMass_pos _ (Nat.succ_pos _))).le
  have h₂ := mul_le_mul_of_nonneg_right (dyadic_damped_amplification_le b hb q j B hq hB) hm
  linarith only [h₁, h₂]

/-- info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection.dyadic_finiteSectionTailDrift_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dyadic_finiteSectionTailDrift_le

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
