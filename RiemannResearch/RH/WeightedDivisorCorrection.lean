import RiemannResearch.NumberTheory.WeightedDivisorTransform
import RiemannResearch.RH.DerivativeSignedCorrection

/-!
# Finite energy control of the weighted Mobius correction

Source: the user-requested three-route synthesis. The finite Cauchy--Schwarz
budget and exact divisor extraction feed the infinite weighted-mass theorem.
Every physical coordinate uses the anchored Pareto weight.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.WeightedDivisorCorrection
open RiemannResearch.NumberTheory.WeightedDivisorTransform

/-- The complete finite Cauchy--Schwarz budget. At the zero coordinate all
reciprocal weights are exactly zero; no coordinate is silently discarded. -/
theorem finite_squareWeight_cauchy (x : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), |x k| / (k : ℝ) ^ 2) ^ 2 ≤
      (∑ k ∈ Finset.range (N + 1), positiveWeight k * (x k) ^ 2) *
        ∑ k ∈ Finset.range (N + 1),
          (1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) ^ 3) := by
  let a : ℕ → ℝ := fun k => |x k| / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1))
  let b : ℕ → ℝ := fun k => Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) / (k : ℝ)^2
  have hab (k : ℕ) : a k * b k = |x k| / (k : ℝ)^2 := by
    by_cases hk : k = 0
    · simp [a, b, hk]
    have hkR : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hs : Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    dsimp [a, b]
    field_simp
  have ha2 (k : ℕ) : (a k)^2 = positiveWeight k * (x k)^2 := by
    dsimp [a]
    rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
    simp [positiveWeight, div_eq_mul_inv, mul_comm]
  have hb2 (k : ℕ) : (b k)^2 = 1 / (k : ℝ)^2 + 1 / (k : ℝ)^3 := by
    by_cases hk : k = 0
    · simp [b, hk]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    dsimp [b]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp

  simpa only [hab, ha2, hb2] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + 1)) a b

theorem finite_mobius_squareWeight_energy_bound (x : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ)) x n|)^2 ≤
      (∑ k ∈ Finset.range (N + 1), squareWeight k)^2 *
        (∑ k ∈ Finset.range (N + 1), positiveWeight k * (x k)^2) *
          ∑ k ∈ Finset.range (N + 1),
            (1 / (k : ℝ)^2 + 1 / (k : ℝ)^3) := by
  have hconv := finite_mobius_squareWeight_bound x N
  have hcs := finite_squareWeight_cauchy x N
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range (N + 1), squareWeight k := by
    apply Finset.sum_nonneg
    intro k hk
    exact one_div_nonneg.mpr (sq_nonneg _)
  have hl : 0 ≤ ∑ k ∈ Finset.range (N + 1), squareWeight k * |x k| := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (one_div_nonneg.mpr (sq_nonneg _)) (abs_nonneg _)
  have hm : 0 ≤ ∑ n ∈ Finset.range (N + 1), squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ)) x n| := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (one_div_nonneg.mpr (sq_nonneg _)) (abs_nonneg _)
  have hsq := (sq_le_sq₀ hm (mul_nonneg hl hnonneg)).mpr hconv
  have hcs' :
      (∑ k ∈ Finset.range (N + 1), squareWeight k * |x k|)^2 ≤
        (∑ k ∈ Finset.range (N + 1), positiveWeight k * (x k)^2) *
          ∑ k ∈ Finset.range (N + 1),
            (1 / (k : ℝ)^2 + 1 / (k : ℝ)^3) := by
    simpa only [squareWeight, one_div, div_eq_mul_inv, mul_comm, mul_one] using hcs
  calc
    _ ≤ ((∑ k ∈ Finset.range (N + 1), squareWeight k * |x k|) *
        ∑ k ∈ Finset.range (N + 1), squareWeight k)^2 := hsq
    _ = (∑ k ∈ Finset.range (N + 1), squareWeight k * |x k|)^2 *
        (∑ k ∈ Finset.range (N + 1), squareWeight k)^2 := by ring
    _ ≤ ((∑ k ∈ Finset.range (N + 1), positiveWeight k * (x k)^2) *
          ∑ k ∈ Finset.range (N + 1),
            (1 / (k : ℝ)^2 + 1 / (k : ℝ)^3)) *
        (∑ k ∈ Finset.range (N + 1), squareWeight k)^2 :=
      mul_le_mul_of_nonneg_right hcs' (sq_nonneg _)
    _ = _ := by ring

/-- Exact source-backed extraction through the anchored derivative. -/
theorem mobiusDifference_eq_derivative_divisorTransform
    (d : ℕ) (f : ThresholdHilbert) :
    mobiusDifferenceCLM d f =
      divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ))
        (hilbertSequence (hilbertDifference f)) d := by
  rw [mobiusDifferenceCLM_apply, divisorTransform]
  rw [Nat.sum_divisorsAntidiagonal (f := fun k l =>
    (ArithmeticFunction.moebius l : ℝ) * hilbertSequence (hilbertDifference f) k)]
  rw [hilbertDifference_sequence]
  rfl

end RiemannResearch.RH.Pareto.WeightedDivisorCorrection
