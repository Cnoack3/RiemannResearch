import RiemannResearch.RH.DerivativeMobiusAggregate
/-!
# Uniform cancellation of the complete Möbius CRT intersections

Source: user-directed continuation from 10cb52f2 on 30 September 2026,
using the current descendant 8dbde6f and its exact derivative CRT, raw PNT,
Möbius derivative convergence, and aggregate reconstruction theorems.
This is a repository assembly; no literature novelty claim is made.

Including conductor one, the actual lcm-intersection sum has an exact
signed Hilbert-pairing remainder. It tends to zero uniformly over every
optimization stage, without an inverse-Gram l1 estimate. This discharges
that particular CRT cancellation obligation, not the one-sided lower
bound on the aggregate: the reciprocal correction remains present.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
open GramMobiusCorrection ArithmeticCumulative
private theorem derivativeAtom_mean (i : ℕ) :
    inner ℝ (derivativeAtom i) hilbertOne =
      1 / ((i + 2 : ℕ) : ℝ) - divisorMass (i + 2) := by
  rw [hilbert_inner_weighted, paretoInner]
  have he : (∑' k : ℕ, positiveWeight k *
      (hilbertSequence (derivativeAtom i) k * hilbertSequence hilbertOne k)) =
      ∑' k : ℕ, (positiveWeight k / ((i + 2 : ℕ) : ℝ) -
        positiveWeight k * divisorIndicator (i + 2) k) := by
    apply tsum_congr
    intro k
    by_cases hk : k = 0
    · subst k
      simp [positiveWeight]
    · rw [derivativeAtom_sequence_positive i k (Nat.pos_of_ne_zero hk),
          hilbertOne_sequence]
      simp [zeroAnchor, hk]
      ring
  rw [he, (positiveWeight_summable.div_const _).tsum_sub (divisorMass_summable _)]
  simp only [tsum_div_const, positiveWeight_tsum, divisorMass]


def correctionDivisorSynthesis (n : ℕ) : ThresholdHilbert :=
  correctionReciprocalMoment n • hilbertOne -
    hilbertDifference (correctionSynthesis n)

private theorem hilbertOne_norm_eq_one : ‖hilbertOne‖ = 1 := by
  nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]

theorem correctionDivisorMoment_eq_inner (n : ℕ) :
    correctionDivisorMoment n = inner ℝ hilbertOne (correctionDivisorSynthesis n) := by
  have hh : inner ℝ hilbertOne (hilbertDifference (correctionSynthesis n)) =
      correctionReciprocalMoment n - correctionDivisorMoment n := by
    rw [real_inner_comm, derivative_correction_synthesis, Fintype.linearCombination_apply, sum_inner]
    simp only [real_inner_smul_left, derivativeFamily]
    simp_rw [derivativeAtom_mean]
    unfold correctionReciprocalMoment correctionDivisorMoment
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold correctionDivisorSynthesis
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hilbertOne_norm_sq, hh]
  ring

def mobiusDivisorMoment (m : ℕ) : ℝ :=
  ∑ i : Fin m, mobiusVector m i * divisorMass (i.val + 2)

/-- Includes d=1: this term is exactly correctionDivisorMoment. -/
def completeMobiusCRTIntersection (m n : ℕ) : ℝ :=
  correctionDivisorMoment n +
    ∑ i : Fin m, mobiusVector m i * correctionCRTIntersection n i.val


/-- Actual full conductor sum, including every lcm intersection and d=1. -/
theorem completeMobiusCRTIntersection_eq_lcm_sum (m n : ℕ) :
    completeMobiusCRTIntersection m n =
      ∑ d ∈ Finset.Icc 1 (m + 1), (ArithmeticFunction.moebius d : ℝ) *
        (∑ j : Fin n, correctionVector n j *
          divisorMass (Nat.lcm d (j.val + 2))) := by
  induction m with
  | zero =>
    simp [completeMobiusCRTIntersection, correctionDivisorMoment]
  | succ m ih =>
    have hs : completeMobiusCRTIntersection (m + 1) n =
        completeMobiusCRTIntersection m n +
          (ArithmeticFunction.moebius (m + 2) : ℝ) * correctionCRTIntersection n m := by
      unfold completeMobiusCRTIntersection
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, mobiusVector]
      ring
    rw [hs, ih]
    conv_rhs => rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_assoc]
    rfl

theorem mobiusDivisorMoment_eq_raw_mean (m : ℕ) :
    mobiusDivisorMoment m = mobiusReciprocalSum (m + 1) - 1 / 2 -
      inner ℝ (rawMobiusDerivativeResidual (m + 1)) hilbertOne := by
  have ha : inner ℝ (hilbertAtom 1 (by decide)) hilbertOne = (1 / 2 : ℝ) := by
    rw [hilbertAtom_inner, hilbertOne_sequence]
    norm_num [positiveWeight, zeroAnchor]
  have hi : inner ℝ (rawMobiusDerivativeResidual (m + 1)) hilbertOne =
      1 / 2 + (∑ i : Fin m, mobiusVector m i / ((i.val + 2 : ℕ) : ℝ)) -
        mobiusDivisorMoment m := by
    rw [rawMobiusDerivativeResidual_eq_mobiusResidual, mobiusResidual, map_add,
      hilbertDifference_hilbertOne, derivative_mobius_synthesis,
      Fintype.linearCombination_apply, inner_add_left, ha, sum_inner]
    simp only [real_inner_smul_left, derivativeFamily]
    simp_rw [derivativeAtom_mean]
    unfold mobiusDivisorMoment
    simp only [mul_sub, Finset.sum_sub_distrib]
    have he : (∑ i : Fin m, mobiusVector m i * (1 / ((i.val + 2 : ℕ) : ℝ))) =
        ∑ i : Fin m, mobiusVector m i / ((i.val + 2 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he]
    ring
  have hs := reciprocalMobius_dot m
  change 1 + (∑ i : Fin m,
    (1 / ((i.val + 2 : ℕ) : ℝ)) * mobiusVector m i) =
      mobiusReciprocalSum (m + 1) at hs
  have he : (∑ i : Fin m, mobiusVector m i / ((i.val + 2 : ℕ) : ℝ)) =
      mobiusReciprocalSum (m + 1) - 1 := by
    have hh : (∑ i : Fin m,
        (1 / ((i.val + 2 : ℕ) : ℝ)) * mobiusVector m i) =
        ∑ i : Fin m, mobiusVector m i / ((i.val + 2 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hh] at hs
    linarith
  rw [he] at hi
  linarith

theorem mobiusRowAggregate_complete_crt (m n : ℕ) :
    mobiusRowAggregate m n =
      (mobiusDivisorMoment m - mobiusReciprocalSum (m + 1) + 1) *
        correctionReciprocalMoment n +
      mobiusReciprocalSum (m + 1) * correctionDivisorMoment n -
        completeMobiusCRTIntersection m n := by
  have he : mobiusRowAggregate m n =
      (∑ i : Fin m, mobiusVector m i * divisorMass (i.val + 2)) *
        correctionReciprocalMoment n -
      (∑ i : Fin m, mobiusVector m i / ((i.val + 2 : ℕ) : ℝ)) *
        correctionReciprocalMoment n +
      (∑ i : Fin m, mobiusVector m i / ((i.val + 2 : ℕ) : ℝ)) *
        correctionDivisorMoment n -
      ∑ i : Fin m, mobiusVector m i * correctionCRTIntersection n i.val := by
    unfold mobiusRowAggregate
    rw [← Finset.sum_neg_distrib]
    simp_rw [signedCorrectionRow_eq_crt]
    unfold correctionCRTRow
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hs := reciprocalMobius_dot m
  change 1 + (∑ i : Fin m,
    (1 / ((i.val + 2 : ℕ) : ℝ)) * mobiusVector m i) =
      mobiusReciprocalSum (m + 1) at hs
  have hh : (∑ i : Fin m, (1 / ((i.val + 2 : ℕ) : ℝ)) * mobiusVector m i) =
      ∑ i : Fin m, mobiusVector m i / ((i.val + 2 : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hh] at hs
  unfold mobiusDivisorMoment completeMobiusCRTIntersection
  rw [he]
  have hsum : (∑ i : Fin m, mobiusVector m i / ((i.val + 2 : ℕ) : ℝ)) =
      mobiusReciprocalSum (m + 1) - 1 := by linarith
  rw [hsum]
  ring

/-- All lcm terms collapse to a signed Hilbert pairing, with the scalar source retained. -/
theorem completeMobiusCRTIntersection_exact (m n : ℕ) :
    completeMobiusCRTIntersection m n =
      mobiusReciprocalSum (m + 1) * correctionDivisorMoment n -
        inner ℝ (rawMobiusDerivativeResidual (m + 1)) (correctionDivisorSynthesis n) := by
  have ht := mobiusRowAggregate_complete_crt m n
  rw [mobiusDivisorMoment_eq_raw_mean] at ht
  have hu := mobiusRowAggregate_exact m n
  unfold mobiusRowRemainder at hu
  unfold correctionDivisorSynthesis
  rw [inner_sub_right, real_inner_smul_right]
  nlinarith

theorem completeMobiusCRTIntersection_bound (m n : ℕ) :
    |completeMobiusCRTIntersection m n| ≤
      (|mobiusReciprocalSum (m + 1)| +
        ‖rawMobiusDerivativeResidual (m + 1)‖) * ‖correctionDivisorSynthesis n‖ := by
  have hd : |correctionDivisorMoment n| ≤ ‖correctionDivisorSynthesis n‖ := by
    rw [correctionDivisorMoment_eq_inner]
    simpa only [hilbertOne_norm_eq_one, one_mul] using
      abs_real_inner_le_norm hilbertOne (correctionDivisorSynthesis n)
  rw [completeMobiusCRTIntersection_exact]
  calc
    _ ≤ |mobiusReciprocalSum (m + 1) * correctionDivisorMoment n| +
        |inner ℝ (rawMobiusDerivativeResidual (m + 1)) (correctionDivisorSynthesis n)| :=
      abs_sub _ _
    _ ≤ |mobiusReciprocalSum (m + 1)| * ‖correctionDivisorSynthesis n‖ +
        ‖rawMobiusDerivativeResidual (m + 1)‖ * ‖correctionDivisorSynthesis n‖ := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
        (abs_real_inner_le_norm _ _)
    _ = _ := by ring

theorem correctionDivisorSynthesis_uniform_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖correctionDivisorSynthesis n‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := GeometricMoments.correction_derivative_uniform_norm_bound
  refine ⟨(1 + 2 * ‖hilbertAtom 1 (by decide)‖) * C, by positivity, ?_⟩
  intro n
  have hq : |correctionReciprocalMoment n| ≤
      2 * ‖hilbertAtom 1 (by decide)‖ *
        ‖hilbertDifference (correctionSynthesis n)‖ := by
    have h := abs_real_inner_le_norm (hilbertAtom 1 (by decide))
      (hilbertDifference (correctionSynthesis n))
    rw [← correctionReciprocalMoment_half, abs_div,
      show |(2 : ℝ)| = 2 by norm_num] at h
    linarith
  have hn : ‖correctionDivisorSynthesis n‖ ≤
      |correctionReciprocalMoment n| +
        ‖hilbertDifference (correctionSynthesis n)‖ := by
    exact (norm_sub_le _ _).trans (by
      rw [norm_smul, Real.norm_eq_abs, hilbertOne_norm_eq_one, mul_one])
  have hm := mul_le_mul_of_nonneg_left (hb n)
    (show 0 ≤ 1 + 2 * ‖hilbertAtom 1 (by decide)‖ by positivity)
  nlinarith

/-- Uniform in every optimization stage: no coefficient l1 bound is used. -/
theorem completeMobiusCRTIntersection_uniform_approximation :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ≥ M, ∀ n : ℕ,
      |completeMobiusCRTIntersection m n| < ε := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := correctionDivisorSynthesis_uniform_norm_bound
  have ht : Tendsto (fun m =>
      (|mobiusReciprocalSum (m + 1)| +
        ‖rawMobiusDerivativeResidual (m + 1)‖) * C) atTop (𝓝 0) := by
    simpa using
      ((mobiusReciprocalSum_tendsto_zero.comp (tendsto_add_atTop_nat 1)).abs.add
        (rawMobiusDerivativeResidual_norm_tendsto_zero.comp
          (tendsto_add_atTop_nat 1))).mul_const C
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually_lt_const hε)
  refine ⟨M, ?_⟩
  intro m hm n
  apply (completeMobiusCRTIntersection_bound m n).trans_lt
  exact (mul_le_mul_of_nonneg_left (hb n) (by positivity)).trans_lt (hM m hm)

/-- The optimization cutoff may be arbitrary, even fixed or oscillating. -/
theorem completeMobiusCRTIntersection_tendsto_zero (m n : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun k => completeMobiusCRTIntersection (m k) (n k)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := correctionDivisorSynthesis_uniform_norm_bound
  have he : ∀ k, ‖completeMobiusCRTIntersection (m k) (n k)‖ ≤
      (|mobiusReciprocalSum (m k + 1)| +
        ‖rawMobiusDerivativeResidual (m k + 1)‖) * C := by
    intro k
    simpa only [Real.norm_eq_abs] using
      (completeMobiusCRTIntersection_bound (m k) (n k)).trans
        (mul_le_mul_of_nonneg_left (hb (n k)) (by positivity))
  apply squeeze_zero_norm he
  simpa using
    (((mobiusReciprocalSum_tendsto_zero.comp
      ((tendsto_add_atTop_nat 1).comp hm)).abs).add
      (rawMobiusDerivativeResidual_norm_tendsto_zero.comp
        ((tendsto_add_atTop_nat 1).comp hm))).mul_const C

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
