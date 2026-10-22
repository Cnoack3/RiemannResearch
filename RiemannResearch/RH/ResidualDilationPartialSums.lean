import RiemannResearch.RH.MobiusResidualFirstCoordinate

/-!
# Exact ordinary residual sums as quadratic dilation correlations

Source: direct continuation of the project's first-coordinate energy identity,
24 September 2026. No mathematical novelty is claimed.

The identities and estimates below concern the actual limiting orthogonal
residual and preserve all signed dilation correlations. The resulting bound
grows with the cutoff. It does not prove bounded ordinary partial sums and
does not assert RH.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

theorem paretoPoint_eq_adjacent_dilation_difference (k : ℕ) :
    paretoPointHilbert k =
      (1 / ((k + 1 : ℕ) : ℝ)) •
        hilbertDilation (k + 1) (by omega) hilbertOne -
      (1 / ((k + 2 : ℕ) : ℝ)) •
        hilbertDilation (k + 2) (by omega) hilbertOne := by
  apply hilbertSequence_injective
  change hilbertSequence (paretoPointHilbert k) = hilbertSequenceLinear (_ - _)
  rw [map_sub, map_smul, map_smul]
  change hilbertSequence (paretoPointHilbert k) =
    (1 / ((k + 1 : ℕ) : ℝ)) •
      hilbertSequence (hilbertDilation (k + 1) _ hilbertOne) -
    (1 / ((k + 2 : ℕ) : ℝ)) •
      hilbertSequence (hilbertDilation (k + 2) _ hilbertOne)
  rw [hilbertSequence_paretoPoint, hilbertDilation_sequence,
    hilbertDilation_sequence, hilbertOne_sequence]
  funext n
  by_cases hn0 : n = 0
  · subst n
    simp [paretoPointSequence, dilation, zeroAnchor]
  by_cases hnk : n = k + 1
  · subst n
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hdiv : (k + 1) / (k + 2) = 0 := Nat.div_eq_of_lt (by omega)
    simp [paretoPointSequence, dilation, zeroAnchor, hdiv, hk1]
  by_cases hlt : n < k + 1
  · have hdiv1 : n / (k + 1) = 0 := Nat.div_eq_of_lt hlt
    have hdiv2 : n / (k + 2) = 0 := Nat.div_eq_of_lt (by omega)
    simp [paretoPointSequence, dilation, zeroAnchor, hdiv1, hdiv2, hnk]
  · have hdiv1 : n / (k + 1) ≠ 0 :=
      ne_of_gt (Nat.div_pos (by omega) (by omega))
    have hdiv2 : n / (k + 2) ≠ 0 :=
      ne_of_gt (Nat.div_pos (by omega) (by omega))
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    simp [paretoPointSequence, dilation, zeroAnchor, hdiv1, hdiv2, hnk, hk1, hk2]

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Each physical residual coordinate is an exact signed quadratic expression. -/
theorem residual_coordinate_dilation_identity (k : ℕ) :
    hilbertSequence limitResidual (k + 1) =
      ((k : ℝ) + 2) *
        inner ℝ limitResidual (hilbertDilation (k + 1) (by omega) limitResidual) -
      ((k : ℝ) + 1) *
        inner ℝ limitResidual (hilbertDilation (k + 2) (by omega) limitResidual) := by
  have h := congrArg (fun f => inner ℝ limitResidual f)
    (paretoPoint_eq_adjacent_dilation_difference k)
  rw [inner_paretoPoint, hilbertGibbsPhysical_eq, inner_sub_right,
    inner_smul_right, inner_smul_right,
    limitResidual_inner_dilation_one, limitResidual_inner_dilation_one] at h
  simp only [paretoWeight, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat] at h
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hk1, hk2] at h
  nlinarith [h]

theorem residual_dilation_pairing_abs_le (m : ℕ) (hm : 0 < m) :
    |inner ℝ limitResidual (hilbertDilation m hm limitResidual)| ≤
      Real.sqrt (m : ℝ) * limitEnergy := by
  have h := norm_inner_le_norm (𝕜 := ℝ) limitResidual
    (hilbertDilation m hm limitResidual)
  rw [hilbertDilation_norm, Real.norm_eq_abs] at h
  calc
    _ ≤ ‖limitResidual‖ * (Real.sqrt (m : ℝ) * ‖limitResidual‖) := h
    _ = Real.sqrt (m : ℝ) * limitEnergy := by
      change _ = Real.sqrt (m : ℝ) * ‖limitResidual‖ ^ 2
      ring

/-- Exact ordinary partial sums, with all signed correlations retained. -/
theorem residual_partial_sum_dilation_identity (N : ℕ) :
    (∑ k ∈ Finset.range N, hilbertSequence limitResidual (k + 1)) =
      2 * (∑ k ∈ Finset.range N,
        inner ℝ limitResidual (hilbertDilation (k + 1) (by omega) limitResidual)) -
      (N : ℝ) *
        inner ℝ limitResidual (hilbertDilation (N + 1) (by omega) limitResidual) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, residual_coordinate_dilation_identity,
      Finset.sum_range_succ]
    push_cast
    ring

/-- An unconditional bound linear in the full limiting residual energy.
    Its cutoff-dependent factor does not supply the missing boundedness premise. -/
theorem residual_partial_sum_abs_le (N : ℕ) :
    |∑ k ∈ Finset.range N, hilbertSequence limitResidual (k + 1)| ≤
      limitEnergy *
        (2 * (∑ k ∈ Finset.range N, Real.sqrt ((k + 1 : ℕ) : ℝ)) +
          (N : ℝ) * Real.sqrt ((N + 1 : ℕ) : ℝ)) := by
  have hs :
      |∑ k ∈ Finset.range N,
        inner ℝ limitResidual (hilbertDilation (k + 1) (by omega) limitResidual)| ≤
      limitEnergy * ∑ k ∈ Finset.range N, Real.sqrt ((k + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          |inner ℝ limitResidual
            (hilbertDilation (k + 1) (by omega) limitResidual)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, Real.sqrt ((k + 1 : ℕ) : ℝ) * limitEnergy := by
        apply Finset.sum_le_sum
        intro k hk
        exact residual_dilation_pairing_abs_le (k + 1) (by omega)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hl := residual_dilation_pairing_abs_le (N + 1) (by omega)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlo := mul_le_mul_of_nonneg_left (abs_le.mp hl).1 hN
  have hhi := mul_le_mul_of_nonneg_left (abs_le.mp hl).2 hN
  rw [residual_partial_sum_dilation_identity]
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hs).1, (abs_le.mp hs).2, hlo, hhi]

end RiemannResearch.RH.Pareto.CoefficientStabilization
