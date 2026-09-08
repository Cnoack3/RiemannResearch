import RiemannResearch.RH.ThresholdAffineTailBounds
import RiemannResearch.RH.ThresholdPhaseTail

/-!
# Quantitative nonzero phase limit of the actual affine matrix discrepancies

Source: independently developed from the exact branch and phase quantities
in Christian Noack's RH_Two_Seed_Threshold.tex (8 September 2026, Section 11.2).
The paper supplies the motivating comparison; the explicit rate below is
proved from the actual finite weights and existing logarithmic certificates.

This module proves a uniform O(m^-2) numerical rate directly from the
Pareto weights and logarithmic telescoping. The infinite sum consists of
the actual finite-block squared-entry discrepancies. No identification
with a separately constructed infinite Hilbert-space operator is assumed.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto

open TwoSeedThreshold

noncomputable section

def affineLogGap (k : ℕ) : ℝ :=
  1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) - Real.log (1 + 1 / (k : ℝ))

theorem affineLogGap_nonneg {k : ℕ} (hk : 0 < k) : 0 ≤ affineLogGap k := by
  exact sub_nonneg.mpr (affine_log_le_inverse_sqrt hk)

theorem affine_inverse_sqrt_sq {k : ℕ} (hk : 0 < k) :
    (1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1))) ^ 2 = positiveWeight k := by
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  rfl

/-- Exact difference-of-squares identity, before any estimate is applied. -/
theorem affineLogGap_exact {k : ℕ} (hk : 0 < k) :
    affineLogGap k *
      (1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) +
        Real.log (1 + 1 / (k : ℝ))) = phaseDelta k * positiveWeight k := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  calc
    _ = (1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1))) ^ 2 -
        Real.log (1 + 1 / (k : ℝ)) ^ 2 := by unfold affineLogGap; ring
    _ = _ := by
      rw [affine_inverse_sqrt_sq hk]
      unfold phaseDelta positiveWeight
      field_simp

theorem affineLogGap_le_phase_inverse_sqrt {k : ℕ} (hk : 0 < k) :
    affineLogGap k ≤ phaseDelta k *
      (1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1))) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha0 : 0 < 1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) := by positivity
  have hb0 : 0 ≤ Real.log (1 + 1 / (k : ℝ)) := by
    apply Real.log_nonneg
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have he := affineLogGap_exact hk
  have ha2 := affine_inverse_sqrt_sq hk
  have hprod := mul_nonneg (affineLogGap_nonneg hk) hb0
  have hmul := congrArg (fun x : ℝ => phaseDelta k * x) ha2
  apply (mul_le_mul_iff_right₀ ha0).1
  nlinarith

theorem affineLogGap_le_weight_div {k : ℕ} (hk : 0 < k) :
    affineLogGap k ≤ positiveWeight k / (12 * (k : ℝ)) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs0 := Real.sqrt_nonneg ((k : ℝ) * ((k : ℝ) + 1))
  have hs2 := Real.sq_sqrt (show 0 ≤ (k : ℝ) * ((k : ℝ) + 1) by positivity)
  have hks : (k : ℝ) ≤ Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) := by nlinarith
  have ha : 1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) ≤ 1 / (k : ℝ) :=
    one_div_le_one_div_of_le hk0 hks
  calc
    _ ≤ phaseDelta k * (1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1))) :=
      affineLogGap_le_phase_inverse_sqrt hk
    _ ≤ (positiveWeight k / 12) * (1 / (k : ℝ)) :=
      mul_le_mul (phaseDelta_le_twelfth_weight hk) ha
        (by positivity) (div_nonneg (positiveWeight_nonneg k) (by norm_num))
    _ = _ := by field_simp

def affineContinuumOverlap (j : ℕ) : ℝ :=
  Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) * Real.log (1 + 1 / (j : ℝ))

theorem affineContinuumOverlap_nonneg {j : ℕ} (hj : 0 < j) :
    0 ≤ affineContinuumOverlap j := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  unfold affineContinuumOverlap
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply Real.log_nonneg
  have : 0 ≤ 1 / (j : ℝ) := by positivity
  linarith

theorem affineContinuumOverlap_sq (j : ℕ) :
    affineContinuumOverlap j ^ 2 = 1 - phaseDelta j := by
  unfold affineContinuumOverlap phaseDelta
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

theorem affineContinuumOverlap_le_branch (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    affineContinuumOverlap j ≤ affineBranchOverlap m j :=
  affineBranchOverlap_log_lower m j hm hj

theorem affineBranchOverlap_le_one (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    affineBranchOverlap m j ≤ 1 := by
  have h := affineColumnEnergy_nonneg m j
  rw [affineColumnEnergy_exact m j hm hj] at h
  linarith

theorem affineBranchOverlap_gap_exact (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    affineBranchOverlap m j - affineContinuumOverlap j =
      Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) *
        ∑ r ∈ Finset.range m, affineLogGap (affineBranch m r j) := by
  have hc : affineBranchOverlap m j =
      Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) *
        ∑ r ∈ Finset.range m,
          1 / Real.sqrt ((affineBranch m r j : ℝ) *
            ((affineBranch m r j : ℝ) + 1)) := by
    unfold affineBranchOverlap
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    calc
      _ = affineBranchCoefficient m r j / Real.sqrt (m : ℝ) := by ring
      _ = _ := by rw [affineBranchCoefficient_normalized m r j hm hj]; ring
  rw [hc]
  unfold affineContinuumOverlap affineLogGap
  rw [← affine_branch_log_sum m j hm hj, Finset.sum_sub_distrib]
  ring

theorem affineBranchWeight_unscaled_sum (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑ r ∈ Finset.range m, positiveWeight (affineBranch m r j)) =
      positiveWeight j / m := by
  have h := positiveWeight_block m j hm hj
  rw [Finset.sum_Ico_eq_sum_range] at h
  simpa [affineBranch, Nat.mul_add, Nat.add_sub_cancel_left] using h

theorem affineBranchOverlap_gap_le (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    affineBranchOverlap m j - affineContinuumOverlap j ≤
      positiveWeight j / (6 * (m : ℝ) ^ 2) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hsum : (∑ r ∈ Finset.range m, affineLogGap (affineBranch m r j)) ≤
      (positiveWeight j / m) / (12 * (m : ℝ) * j) := by
    calc
      _ ≤ ∑ r ∈ Finset.range m,
          positiveWeight (affineBranch m r j) / (12 * (m : ℝ) * j) := by
        apply Finset.sum_le_sum
        intro r hr
        have hk0 : 0 < affineBranch m r j := affineBranch_positive hm hj r
        have hge : (m : ℝ) * j ≤ (affineBranch m r j : ℝ) := by
          simp only [affineBranch, Nat.cast_add, Nat.cast_mul]
          nlinarith [Nat.cast_nonneg (α := ℝ) r]
        have hi : 1 / (12 * (affineBranch m r j : ℝ)) ≤
            1 / (12 * (m : ℝ) * j) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith)
        calc
          _ ≤ positiveWeight (affineBranch m r j) /
              (12 * (affineBranch m r j : ℝ)) := affineLogGap_le_weight_div hk0
          _ ≤ _ := by
            simpa only [mul_one_div] using
              mul_le_mul_of_nonneg_left hi (positiveWeight_nonneg _)
      _ = _ := by rw [← Finset.sum_div, affineBranchWeight_unscaled_sum m j hm hj]
  have hs0 := Real.sqrt_nonneg ((j : ℝ) * ((j : ℝ) + 1))
  have hs2 := Real.sq_sqrt (show 0 ≤ (j : ℝ) * ((j : ℝ) + 1) by positivity)
  have hsle : Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) ≤ 2 * (j : ℝ) := by nlinarith
  rw [affineBranchOverlap_gap_exact m j hm hj]
  calc
    _ ≤ Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) *
        ((positiveWeight j / m) / (12 * (m : ℝ) * j)) :=
      mul_le_mul_of_nonneg_left hsum hs0
    _ ≤ (2 * (j : ℝ)) * ((positiveWeight j / m) / (12 * (m : ℝ) * j)) :=
      mul_le_mul_of_nonneg_right hsle (by unfold positiveWeight; positivity)
    _ = _ := by field_simp; ring

/-- Exact signed difference from the limiting phase summand. -/
theorem affineProjectionBlock_phase_gap_exact (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    2 * phaseDelta j - affineProjectionBlockEnergy m j =
      2 * (affineBranchOverlap m j - affineContinuumOverlap j) *
        (affineBranchOverlap m j + affineContinuumOverlap j) := by
  rw [affineProjectionBlockEnergy_exact m j hm hj]
  have h := affineContinuumOverlap_sq j
  nlinarith

theorem affineProjectionBlock_phase_gap_bounds (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    0 ≤ 2 * phaseDelta j - affineProjectionBlockEnergy m j ∧
      2 * phaseDelta j - affineProjectionBlockEnergy m j ≤
        2 * positiveWeight j / (3 * (m : ℝ) ^ 2) := by
  constructor
  · exact sub_nonneg.mpr (affineProjectionBlockEnergy_le_phase m j hm hj)
  · have hl := affineContinuumOverlap_le_branch m j hm hj
    have hu := affineBranchOverlap_le_one m j hm hj
    have hgap := affineBranchOverlap_gap_le m j hm hj
    have hprod := mul_le_mul_of_nonneg_left
      (show affineBranchOverlap m j + affineContinuumOverlap j ≤ 2 by linarith)
      (show 0 ≤ 2 * (affineBranchOverlap m j - affineContinuumOverlap j) by linarith)
    rw [affineProjectionBlock_phase_gap_exact m j hm hj]
    have he : 4 * (positiveWeight j / (6 * (m : ℝ) ^ 2)) =
        2 * positiveWeight j / (3 * (m : ℝ) ^ 2) := by field_simp; ring
    calc
      _ ≤ 4 * (affineBranchOverlap m j - affineContinuumOverlap j) := by nlinarith
      _ ≤ 4 * (positiveWeight j / (6 * (m : ℝ) ^ 2)) := by linarith
      _ = _ := he

theorem affineProjection_phase_gap_summable (m : ℕ) (hm : 0 < m) :
    Summable (fun k : ℕ =>
      2 * phaseDelta (k + 1) - affineProjectionBlockEnergy m (k + 1)) := by
  have hp := phaseDelta_summable
  have hE : Summable (fun k : ℕ => affineProjectionBlockEnergy m (k + 1)) := by
    simpa using affineProjectionBlockEnergy_shift_summable m 0 hm
  simpa only [two_mul] using (hp.add hp).sub hE

theorem affineProjection_phase_gap_tsum (m : ℕ) (hm : 0 < m) :
    (∑' k : ℕ, (2 * phaseDelta (k + 1) - affineProjectionBlockEnergy m (k + 1))) =
      2 * universalPhaseConstant - affineProjectionEnergyTail m 0 := by
  have hp := phaseDelta_summable
  have hE : Summable (fun k : ℕ => affineProjectionBlockEnergy m (k + 1)) := by
    simpa using affineProjectionBlockEnergy_shift_summable m 0 hm
  calc
    _ = ∑' k : ℕ,
        ((phaseDelta (k + 1) + phaseDelta (k + 1)) -
          affineProjectionBlockEnergy m (k + 1)) := by
      apply tsum_congr
      intro k
      ring
    _ = (∑' k : ℕ, (phaseDelta (k + 1) + phaseDelta (k + 1))) -
        ∑' k : ℕ, affineProjectionBlockEnergy m (k + 1) := (hp.add hp).tsum_sub hE
    _ = _ := by
      rw [hp.tsum_add hp]
      simp only [universalPhaseConstant, affineProjectionEnergyTail, Nat.add_zero]
      ring

/-- Numerical convergence to the nonzero phase constant, with an explicit rate. -/
theorem affineProjection_phase_gap_rate (m : ℕ) (hm : 0 < m) :
    0 ≤ 2 * universalPhaseConstant - affineProjectionEnergyTail m 0 ∧
      2 * universalPhaseConstant - affineProjectionEnergyTail m 0 ≤
        2 / (3 * (m : ℝ) ^ 2) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hw : Summable (fun k : ℕ => positiveWeight (k + 1)) :=
    positiveWeight_summable.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel h)
  have hwle : (∑' k : ℕ, positiveWeight (k + 1)) ≤ 1 := by
    have he : (∑' k : ℕ, positiveWeight (k + 1)) = progressionWeight 1 1 := by
      unfold progressionWeight
      apply tsum_congr
      intro k
      simp [Nat.add_comm]
    rw [he]
    simpa using progressionWeight_tail_upper 1 0 (by norm_num)
  rw [← affineProjection_phase_gap_tsum m hm]
  constructor
  · exact tsum_nonneg (fun k => (affineProjectionBlock_phase_gap_bounds m (k + 1) hm (by omega)).1)
  · have ht := hw.div_const (3 * (m : ℝ) ^ 2)
    have hc := Summable.tsum_le_tsum
      (fun k => show 2 * phaseDelta (k + 1) - affineProjectionBlockEnergy m (k + 1) ≤
        positiveWeight (k + 1) / (3 * (m : ℝ) ^ 2) +
          positiveWeight (k + 1) / (3 * (m : ℝ) ^ 2) by
            have h := (affineProjectionBlock_phase_gap_bounds m (k + 1) hm (by omega)).2
            simpa only [two_mul, add_div] using h)
      (affineProjection_phase_gap_summable m hm) (ht.add ht)
    rw [ht.tsum_add ht] at hc
    simp only [tsum_div_const] at hc
    have hd := div_le_div_of_nonneg_right hwle
      (show 0 ≤ 3 * (m : ℝ) ^ 2 by positivity)
    have he : 1 / (3 * (m : ℝ) ^ 2) + 1 / (3 * (m : ℝ) ^ 2) =
        2 / (3 * (m : ℝ) ^ 2) := by ring
    linarith

theorem affineProjectionEnergyTotal_rational_bounds (m : ℕ) (hm : 0 < m) :
    (11 : ℝ) / 72 - 2 / (3 * (m : ℝ) ^ 2) ≤ affineProjectionEnergyTail m 0 ∧
      affineProjectionEnergyTail m 0 ≤ 1 / 6 := by
  have h := (affineProjection_phase_gap_rate m hm).2
  have hs := universalPhaseConstant_rational_bounds.1
  constructor
  · linarith
  · exact affineProjectionEnergyTotal_le m hm

theorem affineProjectionEnergyTotal_positive_floor {m : ℕ} (hm : 3 ≤ m) :
    (17 : ℝ) / 216 ≤ affineProjectionEnergyTail m 0 := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hb := (affineProjectionEnergyTotal_rational_bounds m (by omega)).1
  have hi : 1 / (3 * (m : ℝ) ^ 2) ≤ (1 : ℝ) / 27 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have he : 2 / (3 * (m : ℝ) ^ 2) = 2 * (1 / (3 * (m : ℝ) ^ 2)) := by ring
  rw [he] at hb
  linarith

/-- The full numerical discrepancy tends to the nonzero phase constant, with
the preceding theorem providing an explicit one-sided quadratic rate. -/
theorem affineProjectionEnergyTotal_tendsto :
    Filter.Tendsto (fun m : ℕ => affineProjectionEnergyTail m 0)
      Filter.atTop (nhds (2 * universalPhaseConstant)) := by
  have hi : Filter.Tendsto (fun m : ℕ => ((m : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hr : Filter.Tendsto (fun m : ℕ => 2 / (3 * (m : ℝ)^2))
      Filter.atTop (nhds 0) := by
    have h := (hi.pow 2).const_mul ((2 : ℝ) / 3)
    convert h using 1
    · funext m
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    · norm_num
  have hb : ∀ᶠ m : ℕ in Filter.atTop,
      0 ≤ 2 * universalPhaseConstant - affineProjectionEnergyTail m 0 ∧
      2 * universalPhaseConstant - affineProjectionEnergyTail m 0 ≤
        2 / (3 * (m : ℝ)^2) :=
    (Filter.eventually_ge_atTop 1).mono (fun m hm =>
      affineProjection_phase_gap_rate m (by omega))
  have hg : Filter.Tendsto
      (fun m : ℕ => 2 * universalPhaseConstant - affineProjectionEnergyTail m 0)
      Filter.atTop (nhds 0) :=
    squeeze_zero' (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2)) hr
  have hc : Filter.Tendsto (fun _ : ℕ => 2 * universalPhaseConstant)
      Filter.atTop (nhds (2 * universalPhaseConstant)) := tendsto_const_nhds
  have h := hc.sub hg
  simpa only [sub_sub_cancel, sub_zero] using h

end
end RiemannResearch.RH.Pareto
