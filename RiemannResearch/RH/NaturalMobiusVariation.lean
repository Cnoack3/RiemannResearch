import RiemannResearch.RH.NaturalMobiusPhysicalTests

/-!
# Exact jumps and uniform weighted variation of the raw Möbius residual

Source: `ReciprocalCharge_DilationAndPeriodicSource_20260924.md`, Section 7.
The residue jump is the existing arithmetic primitive identity specialized to
consecutive coordinates. All bounds concern the actual physical Hilbert
coordinates, and the cutoff is positive where needed.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- The exact signed jump includes every truncated divisor contribution. -/
theorem rawMobiusResidual_jump (N k : ℕ) (hk : 0 < k) :
    hilbertSequence (hilbertOne - rawMobiusHilbert N) (k + 1) -
      hilbertSequence (hilbertOne - rawMobiusHilbert N) k =
    mobiusReciprocalSum N - ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d (k + 1) := by
  have hres (d : ℕ) (hd : 0 < d) :
      residueFraction d (k + 1) - residueFraction d k =
        1 / (d : ℝ) - divisorIndicator d (k + 1) := by
    have h := cumulative_balancedDivisor d (k + 1) hd
    rw [cumulative_succ, cumulative_balancedDivisor d k hd] at h
    unfold balancedDivisor at h
    linarith
  rw [rawMobiusResidual_sequence N (k + 1) (by omega),
    rawMobiusResidual_sequence N k hk]
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
        (residueFraction d (k + 1) - residueFraction d k) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    _ = ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) -
        (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d (k + 1)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hres d (Finset.mem_Icc.mp hd).1]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib]; rfl

/-- The truncated signed divisor sum has absolute value at most the full divisor count. -/
theorem truncated_mobius_divisor_sum_abs_le (N n : ℕ) (hn : 0 < n) :
    |∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d n| ≤
        (n.divisors.card : ℝ) := by
  classical
  let s := (Finset.Icc 1 N).filter (fun d => d ∣ n)
  have hsub : s ⊆ n.divisors := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    exact Nat.mem_divisors.mpr ⟨hd'.2, ne_of_gt hn⟩
  have he : (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d n) =
      ∑ d ∈ s, (ArithmeticFunction.moebius d : ℝ) := by
    simp only [divisorIndicator, mul_ite, mul_one, mul_zero]
    exact (Finset.sum_filter _ _).symm
  rw [he]
  calc
    _ ≤ ∑ d ∈ s, |(ArithmeticFunction.moebius d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = (s.card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- A cutoff-independent bound for the actual residual jump. -/
theorem rawMobiusResidual_jump_abs_le (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 0 < k) :
    |hilbertSequence (hilbertOne - rawMobiusHilbert N) (k + 1) -
      hilbertSequence (hilbertOne - rawMobiusHilbert N) k| ≤
        1 + ((k + 1).divisors.card : ℝ) := by
  rw [rawMobiusResidual_jump N k hk]
  have ht := abs_sub_le (mobiusReciprocalSum N) 0
    (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d (k + 1))
  simp only [sub_zero, zero_sub, abs_neg] at ht
  exact ht.trans (add_le_add (mobiusReciprocalSum_abs_le_one N hN)
    (truncated_mobius_divisor_sum_abs_le N (k + 1) (by omega)))

/-- Pareto-weighted physical coordinates, used in ordinary Abel summation. -/
def rawMobiusWeightedCoordinate (N k : ℕ) : ℝ :=
  positiveWeight k * hilbertSequence (hilbertOne - rawMobiusHilbert N) k

/-- The weighted jump identity retains its signed derivative and exact correction. -/
theorem rawMobiusWeightedCoordinate_jump (N k : ℕ) (hk : 0 < k) :
    rawMobiusWeightedCoordinate N (k + 1) - rawMobiusWeightedCoordinate N k =
      (hilbertSequence (hilbertOne - rawMobiusHilbert N) (k + 1) -
        hilbertSequence (hilbertOne - rawMobiusHilbert N) k) /
          (((k : ℝ) + 1) * ((k : ℝ) + 2)) -
      2 * hilbertSequence (hilbertOne - rawMobiusHilbert N) k /
        ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  unfold rawMobiusWeightedCoordinate positiveWeight
  push_cast
  field_simp
  <;> ring

/-- Uniform summable-variation majorant. Summability is a separate elementary
    divisor-count theorem; no RH-strength estimate is used. -/
theorem rawMobiusWeightedCoordinate_variation_le (N : ℕ) (hN : 0 < N)
    (k : ℕ) (hk : 0 < k) :
    |rawMobiusWeightedCoordinate N (k + 1) - rawMobiusWeightedCoordinate N k| ≤
      (3 + ((k + 1).divisors.card : ℝ)) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  rw [rawMobiusWeightedCoordinate_jump N k hk]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have hk2 : 0 < (k : ℝ) + 2 := by positivity
  have hA : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  have hB : 0 < (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  have hj := rawMobiusResidual_jump_abs_le N hN k hk
  have hb := rawMobiusResidual_abs_le_index N hN k
  calc
    _ ≤ |(hilbertSequence (hilbertOne - rawMobiusHilbert N) (k + 1) -
          hilbertSequence (hilbertOne - rawMobiusHilbert N) k) /
            (((k : ℝ) + 1) * ((k : ℝ) + 2))| +
        |2 * hilbertSequence (hilbertOne - rawMobiusHilbert N) k /
          ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2))| := by
          simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le _ (0 : ℝ) _)
    _ ≤ (1 + ((k + 1).divisors.card : ℝ)) /
          (((k : ℝ) + 1) * ((k : ℝ) + 2)) +
        (2 * (k : ℝ)) / ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      rw [abs_div, abs_div, abs_of_pos hA, abs_of_pos hB, abs_mul,
        show |(2 : ℝ)| = 2 by norm_num]
      exact add_le_add (div_le_div_of_nonneg_right hj hA.le)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hB.le)
    _ = _ := by field_simp [ne_of_gt hkR, ne_of_gt hk1, ne_of_gt hk2]; ring

end RiemannResearch.RH.Pareto
