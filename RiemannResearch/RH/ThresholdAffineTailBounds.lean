import RiemannResearch.RH.ThresholdAffineProjectionBlocks
import RiemannResearch.RH.ThresholdPhaseSharpBound

/-!
# Uniform summable tails for the actual affine projection blocks

Source: independently developed from the exact branch formulas in Christian
Noack's RH_Two_Seed_Threshold.tex (8 September 2026, Section 11.2), reusing
the verified logarithmic phase bounds. This citation supplies the motivating
objects and target; no claim of mathematical novelty is made.

The exact normalized Pareto branch overlap dominates its logarithmic
continuum expression. Consequently its squared projection discrepancy is
dominated by twice the already-constructed phase summand, uniformly in
every positive integer dilation. No infinite operator construction or RH
claim is made here.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto

open TwoSeedThreshold

noncomputable section

theorem affine_log_le_inverse_sqrt {k : ℕ} (hk : 0 < k) :
    Real.log (1 + 1 / (k : ℝ)) ≤
      1 / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hK : 0 < (k : ℝ) * ((k : ℝ) + 1) := by positivity
  have hs : 0 < Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) := Real.sqrt_pos.2 hK
  have hl : 0 ≤ Real.log (1 + 1 / (k : ℝ)) := by
    apply Real.log_nonneg
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have hp := phaseDelta_pos hk
  unfold phaseDelta at hp
  have he : (Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) *
      Real.log (1 + 1 / (k : ℝ))) ^ 2 =
      (k : ℝ) * ((k : ℝ) + 1) * Real.log (1 + 1 / (k : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hK)]
  have hm : Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) *
      Real.log (1 + 1 / (k : ℝ)) ≤ 1 := by nlinarith
  apply (le_div_iff₀ hs).2
  simpa only [mul_comm] using hm

theorem affineBranchCoefficient_normalized (m r j : ℕ)
    (hm : 0 < m) (hj : 0 < j) :
    affineBranchCoefficient m r j / Real.sqrt (m : ℝ) =
      Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) /
        Real.sqrt ((affineBranch m r j : ℝ) *
          ((affineBranch m r j : ℝ) + 1)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have hk0 : 0 < (affineBranch m r j : ℝ) := by
    exact_mod_cast affineBranch_positive hm hj r
  have hn1 : 0 ≤ affineBranchCoefficient m r j / Real.sqrt (m : ℝ) := by
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hn2 : 0 ≤ Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) /
      Real.sqrt ((affineBranch m r j : ℝ) *
        ((affineBranch m r j : ℝ) + 1)) := by positivity
  apply (sq_eq_sq₀ hn1 hn2).1
  rw [div_pow, affineBranchCoefficient_sq,
    Real.sq_sqrt (Nat.cast_nonneg m), div_pow,
    Real.sq_sqrt (by positivity : 0 ≤ (j : ℝ) * ((j : ℝ) + 1)),
    Real.sq_sqrt (by positivity : 0 ≤ (affineBranch m r j : ℝ) *
      ((affineBranch m r j : ℝ) + 1))]
  unfold affineBranchWeight positiveWeight
  field_simp

theorem affine_log_reciprocal_range_sum (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∑ r ∈ Finset.range n, Real.log (1 + 1 / (a + r))) =
      Real.log ((a + n) / a) := by
  induction n with
  | zero => simp [ne_of_gt ha]
  | succ n ih =>
    have hn : 0 < a + (n : ℝ) := by positivity
    have hs : 0 < a + ((n + 1 : ℕ) : ℝ) := by positivity
    have he : 1 + 1 / (a + (n : ℝ)) =
        (a + ((n + 1 : ℕ) : ℝ)) / (a + n) := by
      push_cast
      field_simp
      ring
    rw [Finset.sum_range_succ, ih, he,
      Real.log_div (ne_of_gt hn) (ne_of_gt ha),
      Real.log_div (ne_of_gt hs) (ne_of_gt hn),
      Real.log_div (ne_of_gt hs) (ne_of_gt ha)]
    ring

theorem affine_branch_log_sum (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑ r ∈ Finset.range m,
      Real.log (1 + 1 / (affineBranch m r j : ℝ))) =
      Real.log (1 + 1 / (j : ℝ)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have h := affine_log_reciprocal_range_sum ((m : ℝ) * j) (by positivity) m
  have he : ((m : ℝ) * j + m) / ((m : ℝ) * j) =
      1 + 1 / (j : ℝ) := by
    field_simp
  rw [he] at h
  simpa only [affineBranch, Nat.cast_add, Nat.cast_mul] using h

def affineBranchOverlap (m j : ℕ) : ℝ :=
  (1 / Real.sqrt (m : ℝ)) *
    ∑ r ∈ Finset.range m, affineBranchCoefficient m r j

theorem affineBranchOverlap_nonneg (m j : ℕ) : 0 ≤ affineBranchOverlap m j := by
  unfold affineBranchOverlap
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun r _ => Real.sqrt_nonneg _)

theorem affineBranchOverlap_log_lower (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) *
      Real.log (1 + 1 / (j : ℝ)) ≤ affineBranchOverlap m j := by
  rw [← affine_branch_log_sum m j hm hj, Finset.mul_sum]
  calc
    _ ≤ ∑ r ∈ Finset.range m,
        affineBranchCoefficient m r j / Real.sqrt (m : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [affineBranchCoefficient_normalized m r j hm hj]
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left
          (affine_log_le_inverse_sqrt (affineBranch_positive hm hj r))
          (Real.sqrt_nonneg ((j : ℝ) * ((j : ℝ) + 1)))
    _ = affineBranchOverlap m j := by
      rw [← Finset.sum_div]
      unfold affineBranchOverlap
      ring

/-- The full finite squared-entry discrepancy, retaining every cross entry. -/
def affineProjectionBlockEnergy (m j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range m, ∑ t ∈ Finset.range m,
    (affineBranchCoefficient m r j * affineBranchCoefficient m t j -
      1 / (m : ℝ)) ^ 2

theorem affineProjectionBlockEnergy_nonneg (m j : ℕ) :
    0 ≤ affineProjectionBlockEnergy m j := by
  exact Finset.sum_nonneg (fun r _ =>
    Finset.sum_nonneg (fun t _ => sq_nonneg _))

theorem affineProjectionBlockEnergy_exact (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    affineProjectionBlockEnergy m j = 2 * (1 - affineBranchOverlap m j ^ 2) := by
  exact affineProjection_block_discrepancy m j hm hj

theorem affineProjectionBlockEnergy_le_phase (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    affineProjectionBlockEnergy m j ≤ 2 * phaseDelta j := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have hl : 0 ≤ Real.log (1 + 1 / (j : ℝ)) := by
    apply Real.log_nonneg
    have : 0 ≤ 1 / (j : ℝ) := by positivity
    linarith
  have hL0 : 0 ≤ Real.sqrt ((j : ℝ) * ((j : ℝ) + 1)) *
      Real.log (1 + 1 / (j : ℝ)) := mul_nonneg (Real.sqrt_nonneg _) hl
  have hsq := (sq_le_sq₀ hL0 (affineBranchOverlap_nonneg m j)).2
    (affineBranchOverlap_log_lower m j hm hj)
  rw [mul_pow, Real.sq_sqrt (by positivity :
    0 ≤ (j : ℝ) * ((j : ℝ) + 1))] at hsq
  rw [affineProjectionBlockEnergy_exact m j hm hj]
  unfold phaseDelta
  nlinarith

theorem affineProjectionBlockEnergy_le_sixth_weight (m j : ℕ)
    (hm : 0 < m) (hj : 0 < j) :
    affineProjectionBlockEnergy m j ≤ positiveWeight j / 6 := by
  have h := affineProjectionBlockEnergy_le_phase m j hm hj
  have hp := phaseDelta_le_twelfth_weight hj
  linarith

theorem affineProjectionBlockEnergy_shift_summable (m N : ℕ) (hm : 0 < m) :
    Summable (fun k : ℕ => affineProjectionBlockEnergy m (k + N + 1)) := by
  apply Summable.of_nonneg_of_le
    (fun k => affineProjectionBlockEnergy_nonneg m (k + N + 1))
    (fun k => show affineProjectionBlockEnergy m (k + N + 1) ≤
      phaseDelta (k + N + 1) + phaseDelta (k + N + 1) by
        have h := affineProjectionBlockEnergy_le_phase m (k + N + 1) hm (by omega)
        linarith)
  exact (phaseDelta_shift_summable N).add (phaseDelta_shift_summable N)

def affineProjectionEnergyTail (m N : ℕ) : ℝ :=
  ∑' k : ℕ, affineProjectionBlockEnergy m (k + N + 1)

theorem affineProjectionEnergyTail_le_phaseTail (m N : ℕ) (hm : 0 < m) :
    affineProjectionEnergyTail m N ≤ 2 * phaseTail N := by
  have hp := phaseDelta_shift_summable N
  have h := Summable.tsum_le_tsum
    (fun k => show affineProjectionBlockEnergy m (k + N + 1) ≤
      phaseDelta (k + N + 1) + phaseDelta (k + N + 1) by
        have h := affineProjectionBlockEnergy_le_phase m (k + N + 1) hm (by omega)
        linarith)
    (affineProjectionBlockEnergy_shift_summable m N hm) (hp.add hp)
  rw [hp.tsum_add hp] at h
  change affineProjectionEnergyTail m N ≤ phaseTail N + phaseTail N at h
  linarith

/-- All positive integer dilations share the same explicit infinite-tail majorant. -/
theorem affineProjectionEnergyTail_le (m N : ℕ) (hm : 0 < m) :
    affineProjectionEnergyTail m N ≤ 1 / (6 * ((N : ℝ) + 1)) := by
  have h := affineProjectionEnergyTail_le_phaseTail m N hm
  have hp := phaseTail_le_twelfth N
  have he : 2 * (1 / (12 * ((N : ℝ) + 1))) =
      1 / (6 * ((N : ℝ) + 1)) := by field_simp; ring
  calc
    _ ≤ 2 * phaseTail N := h
    _ ≤ 2 * (1 / (12 * ((N : ℝ) + 1))) := by linarith
    _ = _ := he

theorem affineProjectionEnergyTotal_le (m : ℕ) (hm : 0 < m) :
    affineProjectionEnergyTail m 0 ≤ 1 / 6 := by
  simpa using affineProjectionEnergyTail_le m 0 hm

/-- The actual squared Euclidean defect of one weighted branch column. -/
def affineColumnEnergy (m j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range m,
    (affineBranchCoefficient m r j - 1 / Real.sqrt (m : ℝ)) ^ 2

theorem affineColumnEnergy_nonneg (m j : ℕ) : 0 ≤ affineColumnEnergy m j := by
  exact Finset.sum_nonneg (fun r _ => sq_nonneg _)

theorem affineColumnEnergy_exact (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    affineColumnEnergy m j = 2 * (1 - affineBranchOverlap m j) := by
  exact affineBranchCoefficient_uniform_defect m j hm hj

/-- This comparison retains the mixed overlap factor exactly. -/
theorem affineColumnEnergy_mul_overlap (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    affineColumnEnergy m j * (1 + affineBranchOverlap m j) =
      affineProjectionBlockEnergy m j := by
  rw [affineColumnEnergy_exact m j hm hj,
    affineProjectionBlockEnergy_exact m j hm hj]
  ring

theorem affineBranchOverlap_half_le (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (1 : ℝ) / 2 ≤ affineBranchOverlap m j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw : positiveWeight j ≤ (1 : ℝ) / 2 := by
    unfold positiveWeight
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hE := affineProjectionBlockEnergy_le_sixth_weight m j hm hj
  rw [affineProjectionBlockEnergy_exact m j hm hj] at hE
  have hn := affineBranchOverlap_nonneg m j
  by_contra h
  have hlt : affineBranchOverlap m j < (1 : ℝ) / 2 := lt_of_not_ge h
  have hp := mul_nonneg hn
    (show 0 ≤ (1 : ℝ) / 2 - affineBranchOverlap m j by linarith)
  nlinarith

theorem affineColumnEnergy_le_ninth_weight (m j : ℕ)
    (hm : 0 < m) (hj : 0 < j) :
    affineColumnEnergy m j ≤ positiveWeight j / 9 := by
  have hE := affineProjectionBlockEnergy_le_sixth_weight m j hm hj
  have he := affineColumnEnergy_mul_overlap m j hm hj
  have hh := affineBranchOverlap_half_le m j hm hj
  have hp := mul_nonneg (affineColumnEnergy_nonneg m j)
    (show 0 ≤ affineBranchOverlap m j - (1 : ℝ) / 2 by linarith)
  nlinarith

/-- Uniform arithmetic column bound required by the compact-tail argument. -/
theorem affineColumnEnergy_le_quarter_successor_sq (m j : ℕ)
    (hm : 0 < m) (hj : 0 < j) :
    affineColumnEnergy m j ≤ 1 / (4 * ((j : ℝ) + 1) ^ 2) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have he : positiveWeight j / 9 = 1 / (9 * (j : ℝ) * ((j : ℝ) + 1)) := by
    unfold positiveWeight
    field_simp
  apply (affineColumnEnergy_le_ninth_weight m j hm hj).trans
  rw [he]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

end
end RiemannResearch.RH.Pareto
