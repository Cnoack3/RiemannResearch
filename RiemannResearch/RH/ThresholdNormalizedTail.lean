import RiemannResearch.RH.ThresholdJointAdjointTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Normalized weighted tails of the actual Pareto Hilbert space

Source: user-provided argument, `RH_Iff_Two_Seed_Approximation_20260914.md`,
Section 3. These are the actual weighted tails. The summability result below
states its ordinary tail-square summability input explicitly; the companion
`ThresholdDyadicTailSummability` discharges that input from actual dyadic
adjoint fixedness.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Actual absolutely convergent weighted tail, with zero-index mass zero. -/
def hilbertWeightedTail (f : ThresholdHilbert) (n : ℕ) : ℝ :=
  ∑' k, if n ≤ k then positiveWeight k * hilbertSequence f k else 0

/-- The multiplicatively invariant coefficient forced by adjoint fixedness. -/
def hilbertNormalizedTail (f : ThresholdHilbert) (n : ℕ) : ℝ :=
  (n : ℝ) * hilbertWeightedTail f n

theorem hilbertWeightedTail_eq_inner (f : ThresholdHilbert)
    (n : ℕ) (hn : 0 < n) :
    hilbertWeightedTail f n = inner ℝ (hilbertTail n hn) f :=
  (hilbertTail_inner_series f n hn).symm

theorem hilbertNormalizedTail_eq_adjoint_inner (f : ThresholdHilbert)
    (n : ℕ) (hn : 0 < n) :
    hilbertNormalizedTail f n =
      inner ℝ hilbertOne (hilbertDilationAdjoint n hn f) := by
  rw [hilbertNormalizedTail, hilbertWeightedTail_eq_inner f n hn,
    hilbertTail, real_inner_smul_left]
  have he := ContinuousLinearMap.adjoint_inner_right
    (hilbertDilationContinuous n hn) hilbertOne f
  change inner ℝ hilbertOne (hilbertDilationAdjoint n hn f) =
    inner ℝ (hilbertDilation n hn hilbertOne) f at he
  rw [he]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

theorem hilbertNormalizedTail_scaling (f : ThresholdHilbert)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hfix : hilbertDilationAdjoint m hm f = f) :
    hilbertNormalizedTail f (m * n) = hilbertNormalizedTail f n := by
  unfold hilbertNormalizedTail
  rw [hilbertWeightedTail_eq_inner f (m*n) (Nat.mul_pos hm hn),
    hilbertWeightedTail_eq_inner f n hn]
  have he := hilbertTail_inner_scaling f m n hm hn hfix
  have hs := congrArg (fun x : ℝ => (n : ℝ) * x) he
  simpa only [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hs

theorem hilbertWeightedTail_successor (f : ThresholdHilbert)
    (n : ℕ) (hn : 0 < n) :
    hilbertWeightedTail f n - hilbertWeightedTail f (n+1) =
      positiveWeight n * hilbertSequence f n := by
  rw [hilbertWeightedTail_eq_inner f n hn,
    hilbertWeightedTail_eq_inner f (n+1) (by omega)]
  exact hilbertTail_inner_successor f n hn

/-- Exact signed difference; no independent treatment of mixed terms. -/
theorem hilbertNormalizedTail_increment (f : ThresholdHilbert)
    (n : ℕ) (hn : 0 < n) :
    hilbertNormalizedTail f (n+1) - hilbertNormalizedTail f n =
      hilbertWeightedTail f (n+1) - hilbertSequence f n / ((n : ℝ)+1) := by
  have he := hilbertWeightedTail_successor f n hn
  have hw : (n : ℝ) * positiveWeight n = 1 / ((n : ℝ)+1) := by
    unfold positiveWeight
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hs := congrArg (fun x : ℝ => (n : ℝ) * x) he
  rw [← mul_assoc, hw] at hs
  unfold hilbertNormalizedTail
  push_cast
  simp only [div_eq_mul_inv, one_mul] at hs ⊢
  nlinarith only [hs]

/-- Constant normalized tails recover a constant actual Hilbert vector. -/
theorem eq_smul_hilbertOne_of_normalizedTail_constant
    (f : ThresholdHilbert) (c : ℝ)
    (hc : ∀ n : ℕ, 0 < n → hilbertNormalizedTail f n = c) :
    f = c • hilbertOne := by
  apply hilbertSequence_injective
  funext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    rw [hilbert_coordinate_recovery f n hp,
      ← hilbertNormalizedTail_eq_adjoint_inner f n hp,
      ← hilbertNormalizedTail_eq_adjoint_inner f (n+1) (by omega),
      hc n hp, hc (n+1) (by omega)]
    simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul,
      hilbertOne_sequence, zeroAnchor, if_neg hn]
    ring

theorem hilbertSequence_div_successor_square_summable (f : ThresholdHilbert) :
    Summable (fun n => (hilbertSequence f n / ((n : ℝ)+1))^2) := by
  apply (hilbertSequence_square_summable f).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hn : n = 0
  · subst n
    simp
  · have hp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold positiveWeight
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hp
    have hs0 : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
    nlinarith [sq_nonneg (hilbertSequence f n)]

/-- Square-summable tails imply square-summable normalized-tail increments.
The companion dyadic-block estimate supplies tail summability in the application. -/
theorem hilbertNormalizedTail_increment_square_summable
    (f : ThresholdHilbert)
    (ht : Summable (fun n => hilbertWeightedTail f n ^ 2)) :
    Summable (fun n => (hilbertNormalizedTail f (n+1) -
      hilbertNormalizedTail f n)^2) := by
  apply (summable_nat_add_iff 1).mp
  have ht' := (summable_nat_add_iff 2).mpr ht
  have hh := (summable_nat_add_iff 1).mpr
    (hilbertSequence_div_successor_square_summable f)
  apply ((ht'.mul_left 2).add (hh.mul_left 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hilbertNormalizedTail_increment f (n+1) (by omega)]
  have hs := sq_nonneg (hilbertWeightedTail f (n+2) +
    hilbertSequence f (n+1) / (((n+1 : ℕ) : ℝ)+1))
  have he : (n+1)+1 = n+2 := by omega
  rw [he]
  nlinarith

end
end RiemannResearch.RH.Pareto
