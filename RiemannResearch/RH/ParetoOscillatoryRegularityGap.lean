import RiemannResearch.RH.ResidueTailAdditiveCancellation
import RiemannResearch.RH.ParetoPrimitiveRegularity
import Mathlib.Analysis.PSeries

/-!
# A strict separation of primitive and absolute first-moment regularity

Source: user-provided argument, Section 26 of
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`.
This formalizes the alpha = 0 example: zero at physical coordinate one,
and (-1)^n thereafter. It has finite Pareto energy and summable signed
primitives, whereas its absolute first moment diverges. It is an example
separating hypotheses, not a candidate certificate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

def alternatingTailSequence (n : ℕ) : ℝ :=
  if 2 ≤ n then (-1 : ℝ) ^ n else 0

@[simp] theorem alternatingTailSequence_one : alternatingTailSequence 1 = 0 := by
  norm_num [alternatingTailSequence]

theorem alternatingTailSequence_abs_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    |alternatingTailSequence n| = 1 := by
  simp [alternatingTailSequence, hn, abs_pow]

theorem alternatingTailSequence_abs_le (n : ℕ) :
    |alternatingTailSequence n| ≤ 1 := by
  by_cases hn : 2 ≤ n
  · rw [alternatingTailSequence_abs_of_two_le n hn]
  · simp [alternatingTailSequence, hn]

/-- Membership in the actual weighted Pareto l² domain. -/
theorem alternatingTailSequence_square_summable :
    Summable (fun k => positiveWeight k * alternatingTailSequence k ^ 2) := by
  apply positiveWeight_summable.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))]
  have ha := alternatingTailSequence_abs_le k
  have hsq : alternatingTailSequence k ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (alternatingTailSequence k)]
  simpa using mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg k)

/-- The actual signed prefix sums have an elementary exact formula. -/
theorem alternatingTailSequence_partialSum_succ (n : ℕ) :
    additivePartialSum alternatingTailSequence (n + 1) =
      (1 + (-1 : ℝ) ^ (n + 1)) / 2 := by
  induction n with
  | zero => norm_num [additivePartialSum, alternatingTailSequence]
  | succ n ih =>
      change additivePartialSum alternatingTailSequence (n + 1 + 1) =
        (1 + (-1 : ℝ) ^ (n + 1 + 1)) / 2
      rw [additivePartialSum_succ, ih]
      have hn : 2 ≤ n + 1 + 1 := by omega
      simp only [alternatingTailSequence, if_pos hn, pow_succ]
      ring

theorem alternatingTailSequence_partialSum_abs_le (n : ℕ) :
    |additivePartialSum alternatingTailSequence n| ≤ 1 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [alternatingTailSequence_partialSum_succ]
      have hp : |(-1 : ℝ) ^ (n + 1)| = 1 := by simp [abs_pow]
      have hb := abs_le.mp hp.le
      apply abs_le.mpr
      constructor <;> linarith

/-- The ordinary signed partial sums meet the additive cancellation criterion. -/
theorem alternatingTailSequence_additiveCancellation :
    Summable (fun n : ℕ =>
      |additivePartialSum alternatingTailSequence n| / ((n : ℝ) + 1) ^ 2) := by
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply hp.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right
    (alternatingTailSequence_partialSum_abs_le n) (sq_nonneg _)

/-- Primitive l¹ allows cancellation inside each tail, and holds here. -/
theorem alternatingTailSequence_signedTail_summable :
    Summable (anchoredSignedTail alternatingTailSequence) :=
  anchoredSignedTail_summable_of_additiveCancellation alternatingTailSequence
    alternatingTailSequence_square_summable alternatingTailSequence_additiveCancellation

/-- The older absolute first-moment requirement fails for the same sequence. -/
theorem alternatingTailSequence_not_summable_firstMoment :
    ¬ Summable (fun n : ℕ => |alternatingTailSequence n| / ((n : ℝ) + 1)) := by
  intro hs
  have ht := (summable_nat_add_iff 2).mpr hs
  have hi : Summable (fun n : ℕ => (((n + 3 : ℕ) : ℝ))⁻¹) := by
    apply ht.congr
    intro n
    rw [alternatingTailSequence_abs_of_two_le (n + 2) (by omega)]
    simp only [Nat.cast_add, Nat.cast_ofNat, one_div]
    congr 1
    ring
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 3).mp hi)

/-- Strict separation occurs inside the anchored tail Hilbert domain itself. -/
theorem exists_tail_summable_primitive_not_firstMoment :
    ∃ z : ℕ → ℝ, z 1 = 0 ∧
      Summable (fun n => positiveWeight n * z n ^ 2) ∧
      Summable (anchoredSignedTail z) ∧
      ¬ Summable (fun n : ℕ => |z n| / ((n : ℝ) + 1)) :=
  ⟨alternatingTailSequence, alternatingTailSequence_one,
    alternatingTailSequence_square_summable,
    alternatingTailSequence_signedTail_summable,
    alternatingTailSequence_not_summable_firstMoment⟩

/-- The constant physical sequence has finite actual Pareto energy. -/
theorem constantOne_square_summable :
    Summable (fun n : ℕ => positiveWeight n * (1 : ℝ) ^ 2) := by
  simpa using positiveWeight_summable

/-- Its integrated sequence is exactly the harmonic sequence. -/
theorem constantOne_signedTail (n : ℕ) (hn : 0 < n) :
    signedTail (fun _ => (1 : ℝ)) n = 1 / (n : ℝ) := by
  simp only [signedTail, signedCoefficient, mul_one]
  exact positiveWeight_tail_tsum n hn

/-- Automatic Hilbert regularity does not, by itself, provide primitive l¹. -/
theorem constantOne_not_summable_signedTail :
    ¬ Summable (anchoredSignedTail (fun _ => (1 : ℝ))) := by
  intro hs
  have ht := (summable_nat_add_iff 1).mpr hs
  have hi : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) := by
    apply ht.congr
    intro n
    rw [anchoredSignedTail_pos _ (Nat.succ_pos n),
      constantOne_signedTail (n + 1) (Nat.succ_pos n)]
    simp only [one_div]
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp hi)

end RiemannResearch.RH.Pareto
