import RiemannResearch.RH.ParetoInitialIntervalCriterion
import RiemannResearch.RH.ParetoTailCapacity
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.RH.ParetoLegalApproximationClosure
import RiemannResearch.RH.ParetoExhaustiveWalk
import RiemannResearch.RH.ThresholdSeedPowerInfinite5040
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Complete Pareto certificates for initial intervals

The period-twelve trial is chosen for the singleton target. Its norm uses the
repository's exact periodic Pareto regrouping and two-term progression bound.
The period-5040 comparison uses the published two-seed witness for the constant.
Source: Christian Noack's November 17, 2026 initial-interval question.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.TwoSeedThreshold

private theorem singleton_head_eq_point : compactHead 1 hilbertOne = paretoPointHilbert 0 := by
  rw [compactHead_one_eq_dilationDifference]
  exact firstPoint_eq_dilation_difference.symm

/-- Every exact finite first-site capacity is a global distance certificate. -/
theorem one_infDist_le_of_tailCapacity (n : ℕ) :
    Metric.infDist hilbertOne (closedSpace : Set ThresholdHilbert) ≤
      Real.sqrt (1 / (TailCapacity.tailCapacity n + 2)) / (1 - 1 / Real.sqrt 2) := by
  let p := (finiteSpace n).starProjection (paretoPointHilbert 0)
  have h := one_infDist_le_of_compactHead_finiteTrial 1 (by decide) n
    (q := p) ((finiteSpace n).starProjection_apply_mem _)
  have he : Real.sqrt (1 / (TailCapacity.tailCapacity n + 2)) = ‖paretoPointHilbert 0 - p‖ := by
    rw [← TailCapacity.pointError_eq_inv_capacity, TailCapacity.pointError, walkError,
      Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  simpa only [singleton_head_eq_point, Nat.cast_one, one_add_one_eq_two] using h

/-- Four conductor atoms with period twelve, chosen to approximate the singleton. -/
def singletonTrialTwelve : ThresholdHilbert :=
  (7 / 4 : ℝ) • residueAtom 0 + residueAtom 1 - (1 / 2 : ℝ) • residueAtom 2 - residueAtom 4

theorem singletonTrialTwelve_mem : singletonTrialTwelve ∈ finiteSpace 5 := by
  have ha (i : ℕ) (hi : i < 5) : residueAtom i ∈ finiteSpace 5 :=
    Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  exact (finiteSpace 5).sub_mem ((finiteSpace 5).sub_mem
    ((finiteSpace 5).add_mem ((finiteSpace 5).smul_mem _ (ha 0 (by decide))) (ha 1 (by decide)))
    ((finiteSpace 5).smul_mem _ (ha 2 (by decide)))) (ha 4 (by decide))

private def trialValue (n : ℕ) : ℝ :=
  (7 / 4) * residueFraction 2 n + residueFraction 3 n -
    (1 / 2) * residueFraction 4 n - residueFraction 6 n

private theorem singletonTrialTwelve_sequence :
    hilbertSequence singletonTrialTwelve = trialValue := by
  funext n
  change hilbertSequenceLinear singletonTrialTwelve n = _
  simp only [singletonTrialTwelve, map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change (7 / 4 : ℝ) * hilbertSequence (residueAtom 0) n + hilbertSequence (residueAtom 1) n -
    (1 / 2 : ℝ) * hilbertSequence (residueAtom 2) n - hilbertSequence (residueAtom 4) n = _
  simp [residueAtom, normalizedResidueHilbert_sequence, trialValue]

private theorem trialValue_periodic : Function.Periodic trialValue 12 := by
  intro n
  simp only [trialValue, residueFraction, show (n+12)%2 = n%2 by omega,
    show (n+12)%3 = n%3 by omega, show (n+12)%4 = n%4 by omega, show (n+12)%6 = n%6 by omega]

private theorem trialValue_bound (n : ℕ) : |trialValue n| ≤ 1 := by
  rw [← trialValue_periodic.map_mod_nat n]
  have hn : n % 12 < 12 := Nat.mod_lt _ (by decide)
  generalize n % 12 = r at *
  interval_cases r <;> norm_num [trialValue, residueFraction]

/-- Exact squared singleton error with the signed first-site pairing and all twelve
complete progression weights. -/
theorem singletonTrialTwelve_error_sq_eq :
    ‖compactHead 1 hilbertOne - singletonTrialTwelve‖ ^ 2 =
      1 / 2 - hilbertSequence singletonTrialTwelve 1 +
        ∑ r : Fin 12, progressionWeight 12 (r.val + 1) *
          (hilbertSequence singletonTrialTwelve (r.val + 1)) ^ 2 := by
  have hnorm : ‖singletonTrialTwelve‖ ^ 2 =
      ∑ r : Fin 12, progressionWeight 12 (r.val + 1) *
        (hilbertSequence singletonTrialTwelve (r.val + 1)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted, singletonTrialTwelve_sequence]
    exact periodic_paretoInner 12 (by decide) trialValue trialValue_bound trialValue_periodic
  rw [singleton_head_eq_point, norm_sub_sq_real, TailCapacity.firstPoint_norm_sq,
    ← real_inner_comm (paretoPointHilbert 0) singletonTrialTwelve, TailCapacity.inner_firstPoint,
    anchoredEvaluationCLM_apply, hnorm]
  ring

/-- Rational upper endpoint including the infinite tail of every residue class. -/
theorem singletonTrialTwelve_error_sq_le :
    ‖compactHead 1 hilbertOne - singletonTrialTwelve‖ ^ 2 ≤
      (9500632951 : ℝ) / 165216205440 := by
  let U (r : ℕ) : ℝ := positiveWeight r + positiveWeight (r + 12) +
    1 / (12 * ((r : ℝ) + 12 + 1))
  rw [singletonTrialTwelve_error_sq_eq, singletonTrialTwelve_sequence]
  calc
    _ ≤ 1 / 2 - trialValue 1 + ∑ r : Fin 12, U (r.val + 1) * (trialValue (r.val + 1)) ^ 2 := by
      exact add_le_add le_rfl (Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right
        (progressionWeight_upper_two 12 (r.val + 1) (by decide)) (sq_nonneg _))
    _ = _ := by norm_num [Fin.sum_univ_succ, U, positiveWeight, trialValue, residueFraction]

/-- The singleton trial alone transfers an explicit complete-tail bound to the constant. -/
theorem one_infDist_le_of_singletonTrialTwelve :
    Metric.infDist hilbertOne (closedSpace : Set ThresholdHilbert) ≤
      Real.sqrt (9500632951 / 165216205440) / (1 - 1 / Real.sqrt 2) := by
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
  have hd : 0 < 1 - 1 / Real.sqrt 2 := sub_pos.mpr ((div_lt_one (by linarith)).2 hs)
  have h := one_infDist_le_of_compactHead_finiteTrial 1 (by decide) 5 singletonTrialTwelve_mem
  simp only [Nat.cast_one, one_add_one_eq_two] at h
  apply h.trans (div_le_div_of_nonneg_right _ hd.le)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using
    Real.sqrt_le_sqrt singletonTrialTwelve_error_sq_le

private theorem legalPacket_mem_residueClosure (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (i : LegalPacketIndex A) : legalPacket A hA i ∈ closedSpace := by
  let a := i.val.1
  have ha : 0 < a := hA _ i.property.1
  have hf : (a : ℝ) • normalizedResidueHilbert a ha ∈ closedSpace :=
    closedSpace.smul_mem _
      ((Submodule.le_topologicalClosure _) (normalizedResidue_mem_atomSpan a ha))
  have he : legalPacket A hA i =
      hilbertDilation i.val.2 i.property.2 ((a : ℝ) • normalizedResidueHilbert a ha) := by
    apply hilbertSequence_injective
    rw [legalPacket_sequence, hilbertDilation_sequence, hilbertSequence_smul,
      normalizedResidueHilbert_sequence]
    congr 1
    funext n
    change ((n % a : ℕ) : ℝ) = (a : ℝ) * (((n % a : ℕ) : ℝ) / (a : ℝ))
    field_simp [ne_of_gt (Nat.cast_pos.mpr ha : (0 : ℝ) < a)]
  rw [he]
  exact closedSpace_dilation hf _ _

/-- The previously certified period-5040 constant witness in the full residue closure. -/
theorem one_infDist_lt_of_period5040 :
    Metric.infDist hilbertOne (closedSpace : Set ThresholdHilbert) < Real.sqrt (39 / 1000) := by
  let A : Set ℕ := {2, 3}
  have hA : ∀ a ∈ A, 0 < a := by intro a ha; simp [A] at ha; rcases ha with rfl | rfl <;> decide
  obtain ⟨f, hf, hs⟩ := legalSeedSpan_exists_hilbert A hA legalWitness5040_mem_legalSeedSpan
  have hsub : hilbertLegalSubspace A ≤ closedSpace := by
    rw [← span_legalPacket A hA]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact legalPacket_mem_residueClosure A hA i)
  have hnorm : ‖hilbertOne - f‖ ^ 2 =
      ∑' k : ℕ, positiveWeight (k + 1) * (1 - legalWitness5040 (k + 1)) ^ 2 := by
    have hseq : hilbertSequence (hilbertOne - f) = hilbertSequence hilbertOne - hilbertSequence f :=
      hilbertSequenceLinear.map_sub _ _
    rw [hilbert_norm_weighted_sq,
      (hilbertSequence_square_summable (hilbertOne - f)).tsum_eq_zero_add]
    simp only [hilbertSequence_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
    apply tsum_congr
    intro k
    rw [hseq, hilbertOne_sequence, hs]
    simp [zeroAnchor]
  have herr : ‖hilbertOne - f‖ ^ 2 < (39 : ℝ) / 1000 :=
    hnorm.trans_lt legalWitness5040_full_error_lt
  have hnear := Metric.infDist_le_dist_of_mem (x := hilbertOne) (hsub hf)
  rw [dist_eq_norm] at hnear
  apply hnear.trans_lt
  simpa only [Real.sqrt_sq (norm_nonneg _)] using (Real.sqrt_lt_sqrt (sq_nonneg _) herr)

/-- The older global certificate also supplies a numerical bound for every head. -/
theorem compactHead_one_infDist_lt_of_period5040 (m : ℕ) :
    Metric.infDist (compactHead m hilbertOne) (closedSpace : Set ThresholdHilbert) <
      (1 + 1 / Real.sqrt ((m : ℝ) + 1)) * Real.sqrt (39 / 1000) :=
  (compactHead_one_infDist_bounds m).2.trans_lt
    (mul_lt_mul_of_pos_left one_infDist_lt_of_period5040 (by positivity))

end RiemannResearch.RH.Pareto.CoefficientStabilization
