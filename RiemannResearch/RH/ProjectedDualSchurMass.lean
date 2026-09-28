import RiemannResearch.RH.ProjectedDualColumnConcentration
import RiemannResearch.RH.ResidueProjectionSchur

/-!
# Accumulated Schur control of projected inverse-column mass

Source: the existing Schur and orthonormal identities, assembled for the user's
28 September 2026 inverse-column audit. All statements are unconditional finite
bounds or identities. The accumulated Schur envelope is explicit, not bounded
at a sub-stretched rate. Its absolute-value Bessel majorant contains a mode
amplification energy that is at least the stage n. Signed cancellation or an
additional quantitative concentration estimate is still needed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

open RiemannResearch.Analysis.FiniteHilbertGram
open ProjectionSchur

/-- Exact signed mode representation for every projected coefficient. -/
theorem projectedDualColumn_eq_mode_sum (n d : ℕ) (k : Fin n) :
    projectedDualColumn n d k =
      ∑ j : Fin n, modeCoefficient d j.val * modeCoefficient (k.val + 2) j.val := by
  have hn : Orthonormal ℝ (fun j : Fin n => residueMode j.val) :=
    residueMode_orthonormal.comp (fun j : Fin n => j.val) Fin.val_injective
  have hp := projection_eq_orthonormal_sum hn (coefficientRiesz d)
  simp only [residueMode_finiteSpace] at hp
  have hi (j : Fin n) : inner ℝ (residueMode j.val) (coefficientRiesz d) =
      modeCoefficient d j.val := by
    rw [real_inner_comm, coefficientRiesz_inner]
    rfl
  simp only [hi] at hp
  unfold projectedDualColumn
  rw [hp, map_sum]
  simp only [map_smul, smul_eq_mul, modeCoefficient]

/-- The old inverse-column coordinates receive a rank-one mode update. -/
theorem projectedDualColumn_succ_old (n d : ℕ) (k : Fin n) :
    projectedDualColumn (n+1) d k.castSucc = projectedDualColumn n d k +
      modeCoefficient d n * modeCoefficient (k.val+2) n := by
  simp only [projectedDualColumn_eq_mode_sum, Fin.sum_univ_castSucc,
    Fin.val_castSucc, Fin.val_last]

/-- The new inverse-column coordinate is the last rank-one mode term. -/
theorem projectedDualColumn_succ_new (n d : ℕ) :
    projectedDualColumn (n+1) d (Fin.last n) =
      modeCoefficient d n * modeCoefficient (n+2) n := by
  rw [projectedDualColumn_eq_mode_sum, Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin n, modeCoefficient d j.val *
      modeCoefficient (n+2) j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [modeCoefficient_eq_zero_of_lt j.isLt, mul_zero]
  simp only [Fin.val_castSucc, Fin.val_last, hz, zero_add]

/-- The complete l1 coefficient mass of one normalized Gram--Schmidt mode. -/
def residueModeCoefficientMass (n : ℕ) : ℝ :=
  ∑ k : Fin (n+1), |modeCoefficient (k.val+2) n|

/-- Taking absolute values costs the full mode coefficient mass. -/
theorem projectedDualCoefficientMass_succ_le (n d : ℕ) :
    projectedDualCoefficientMass (n+1) d ≤ projectedDualCoefficientMass n d +
      |modeCoefficient d n| * residueModeCoefficientMass n := by
  change (∑ k : Fin (n+1), |projectedDualColumn (n+1) d k|) ≤ _
  rw [Fin.sum_univ_castSucc, projectedDualColumn_succ_new]
  simp only [projectedDualColumn_succ_old]
  calc
    _ ≤ (∑ k : Fin n, (|projectedDualColumn n d k| +
        |modeCoefficient d n * modeCoefficient (k.val+2) n|)) +
        |modeCoefficient d n * modeCoefficient (n+2) n| :=
      add_le_add (Finset.sum_le_sum (fun k _ => abs_add_le _ _)) le_rfl
    _ = _ := by
      simp only [residueModeCoefficientMass, Fin.sum_univ_castSucc,
        Fin.val_castSucc, Fin.val_last, Finset.sum_add_distrib, abs_mul,
        ← Finset.mul_sum, projectedDualCoefficientMass, projectedDualColumn, mul_add, add_assoc]

/-- Exact Schur amplification: scale squared is schurSigma. -/
theorem residueModeCoefficientMass_eq_schur (n : ℕ) :
    residueModeCoefficientMass n =
      (1 + ∑ k : Fin n, |eliminated n k|) / residueModeScale n := by
  have hs := residueModeScale_pos n
  have hold (k : Fin n) :
      residueModeScale n * modeCoefficient (k.val+2) n = -eliminated n k := by
    have h := innovation_old_coefficient n k
    rw [innovation_eq_scale_mode, map_smul] at h
    exact h
  have hlast : residueModeScale n * modeCoefficient (n+2) n = 1 := by
    rw [mul_comm, modeCoefficient_mul_scale]
  apply (eq_div_iff hs.ne').mpr
  rw [residueModeCoefficientMass, Fin.sum_univ_castSucc, add_mul, Finset.sum_mul]
  simp only [Fin.val_castSucc, Fin.val_last]
  have ha (k : Fin n) : |modeCoefficient (k.val+2) n| * residueModeScale n =
      |eliminated n k| := by
    have h := congrArg abs (hold k)
    simpa only [abs_mul, abs_of_pos hs, abs_neg, mul_comm] using h
  have hb : |modeCoefficient (n+2) n| * residueModeScale n = 1 := by
    have h := congrArg abs hlast
    simpa only [abs_mul, abs_of_pos hs, abs_one, mul_comm] using h
  simp only [ha, hb, add_comm]

/-- An unconditional accumulated Schur envelope. No growth bound on this envelope is asserted. -/
theorem projectedDualCoefficientMass_le_accumulated_schur (n d : ℕ) :
    projectedDualCoefficientMass n d ≤
      ∑ j ∈ Finset.range n, |modeCoefficient d j| *
        ((1 + ∑ k : Fin j, |eliminated j k|) / residueModeScale j) := by
  induction n with
  | zero => simp [projectedDualCoefficientMass]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (projectedDualCoefficientMass_succ_le n d).trans
      (by rw [residueModeCoefficientMass_eq_schur]; exact add_le_add ih le_rfl)


/-- Bessel summability controls the fixed-dual factor, leaving the complete mode-amplification energy. -/
theorem projectedDualCoefficientMass_sq_le_bessel_schur (n d : ℕ) :
    projectedDualCoefficientMass n d ^ 2 ≤
      (∑' j : ℕ, modeCoefficient d j ^ 2) *
        ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2 := by
  have hm := projectedDualCoefficientMass_le_accumulated_schur n d
  simp_rw [← residueModeCoefficientMass_eq_schur] at hm
  have hm0 : 0 ≤ projectedDualCoefficientMass n d :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs0 : 0 ≤ ∑ j ∈ Finset.range n,
      |modeCoefficient d j| * residueModeCoefficientMass j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun j => |modeCoefficient d j|) residueModeCoefficientMass
  simp only [sq_abs] at hcs
  exact ((sq_le_sq₀ hm0 hs0).mpr hm).trans (hcs.trans
    (mul_le_mul_of_nonneg_right
      (Summable.sum_le_tsum (Finset.range n) (fun _ _ => sq_nonneg _)
        (modeCoefficient_sq_summable d))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

/-- Every normalized mode has coefficient mass at least one, since every residue atom has norm at most one. -/
theorem residueModeCoefficientMass_one_le (n : ℕ) :
    1 ≤ residueModeCoefficientMass n := by
  have hatom (k : ℕ) : ‖residueAtom k‖ ≤ 1 := by
    have ht := residueAtom_tail_norm_sq_le k 0
    have he : hilbertTailShift (residueAtom k) 0 = residueAtom k := by
      ext j
      simp [hilbertTailShift]
    rw [he] at ht
    norm_num at ht
    nlinarith [norm_nonneg (residueAtom k)]
  calc
    1 = ‖residueMode n‖ := (residueMode_orthonormal.1 n).symm
    _ = ‖∑ k : Fin (n+1), modeCoefficient (k.val+2) n • residueAtom k.val‖ := by
      rw [← residueMode_expansion]
    _ ≤ ∑ k : Fin (n+1), ‖modeCoefficient (k.val+2) n • residueAtom k.val‖ :=
      norm_sum_le _ _
    _ ≤ residueModeCoefficientMass n := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hatom k.val) (abs_nonneg _)).trans_eq (mul_one _)

/-- The amplification factor left by absolute-value Cauchy--Schwarz grows at least linearly. This does not lower-bound the actual inverse-column mass. -/
theorem schur_amplification_energy_ge_stage (n : ℕ) :
    (n : ℝ) ≤ ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2 := by
  have h : (∑ j ∈ Finset.range n, (1 : ℝ)) ≤
      ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    nlinarith [residueModeCoefficientMass_one_le j]
  simpa using h

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
