import RiemannResearch.RH.TailCapacityDilationCorrection

/-!
# Finite legal synthesis of the constant from a point approximant

Source: user-provided
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Sections 4, 5 and 19, for the construction and proof strategy.
The dilation here is unscaled physical pullback, so its exact norm factor
is sqrt(2)/2. The theorem retains the explicit maximum-modulus budget.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

def dyadicContraction : ℝ := Real.sqrt 2 / 2

theorem dyadicContraction_nonneg : 0 ≤ dyadicContraction := by
  unfold dyadicContraction
  positivity

theorem dyadicContraction_lt_one : dyadicContraction < 1 := by
  unfold dyadicContraction
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem unscaledResidueDilation_two_norm (f : ThresholdHilbert) :
    ‖unscaledResidueDilation 2 (by omega) f‖ = dyadicContraction * ‖f‖ := by
  change ‖(1 / 2 : ℝ) • hilbertDilation 2 (by omega) f‖ = _
  rw [norm_smul, hilbertDilation_norm]
  norm_num [dyadicContraction] <;> ring

/-- `J` terms of the geometric dilation sum, in recursive form. -/
def pointDilationSynthesis (q : ThresholdHilbert) : ℕ → ThresholdHilbert
  | 0 => 0
  | J + 1 => q + unscaledResidueDilation 2 (by omega) (pointDilationSynthesis q J)

/-- Exact error recursion, before any norm estimate is taken. -/
theorem pointDilationSynthesis_residual_step (q : ThresholdHilbert) (J : ℕ) :
    hilbertOne - pointDilationSynthesis q (J + 1) =
      (paretoPointHilbert 0 - q) +
        unscaledResidueDilation 2 (by omega) (hilbertOne - pointDilationSynthesis q J) := by
  have he : paretoPointHilbert 0 = hilbertOne - unscaledResidueDilation 2 (by omega) hilbertOne :=
    firstPoint_eq_dilation_difference
  simp only [pointDilationSynthesis, map_sub]
  rw [he]
  abel

/-- The finite geometric synthesis estimate, with its exact geometric factor. -/
theorem pointDilationSynthesis_error (q : ThresholdHilbert) (J : ℕ) :
    ‖hilbertOne - pointDilationSynthesis q J‖ ≤
      dyadicContraction ^ J +
        (1 - dyadicContraction ^ J) / (1 - dyadicContraction) *
          ‖paretoPointHilbert 0 - q‖ := by
  have hden : 1 - dyadicContraction ≠ 0 :=
    ne_of_gt (sub_pos.mpr dyadicContraction_lt_one)
  induction J with
  | zero =>
    have hone : ‖hilbertOne‖ = 1 := by
      nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
    simp [pointDilationSynthesis, hone]
  | succ J ih =>
    rw [pointDilationSynthesis_residual_step]
    calc
      _ ≤ ‖paretoPointHilbert 0 - q‖ +
          ‖unscaledResidueDilation 2 (by omega) (hilbertOne - pointDilationSynthesis q J)‖ :=
        norm_add_le _ _
      _ = ‖paretoPointHilbert 0 - q‖ +
          dyadicContraction * ‖hilbertOne - pointDilationSynthesis q J‖ := by
        rw [unscaledResidueDilation_two_norm]
      _ ≤ ‖paretoPointHilbert 0 - q‖ + dyadicContraction *
          (dyadicContraction ^ J +
            (1 - dyadicContraction ^ J) / (1 - dyadicContraction) *
              ‖paretoPointHilbert 0 - q‖) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left ih dyadicContraction_nonneg)
      _ = _ := by
        rw [pow_succ]
        field_simp [hden]
        ring

/-- All terms are legal together at the exact largest modulus `2^J * M`. -/
theorem pointDilationSynthesis_mem (M : ℕ) (hM : 2 ≤ M)
    (q : ThresholdHilbert) (hq : q ∈ finiteSpace (M - 1)) (J : ℕ) :
    pointDilationSynthesis q (J + 1) ∈ finiteSpace (2 ^ J * M - 1) := by
  induction J with
  | zero => simpa [pointDilationSynthesis] using hq
  | succ J ih =>
    have hpow : 0 < 2 ^ J := pow_pos (by omega) J
    have hMle : M ≤ 2 ^ J * M := Nat.le_mul_of_pos_left M hpow
    have hlarge : 2 ≤ 2 ^ J * M := hM.trans hMle
    have hdouble : 2 * (2 ^ J * M) = 2 ^ (J + 1) * M := by
      rw [pow_succ]
      ring
    have hindex : 2 ^ J * M - 1 + 1 = 2 ^ J * M := by omega
    have hd := unscaledResidueDilation_mem_finiteSpace (2 ^ J * M - 1) 2 (by omega)
      (pointDilationSynthesis q (J + 1)) ih
    rw [hindex, hdouble] at hd
    change q + unscaledResidueDilation 2 (by omega) (pointDilationSynthesis q (J + 1)) ∈ _
    apply Submodule.add_mem
    · apply (walkSpan_mono residueAtom id (show M - 1 ≤ 2 ^ (J + 1) * M - 1 by
        rw [← hdouble]
        omega)) hq
    · exact hd

private theorem norm_sub_finite_projection_le (n : ℕ) (x q : ThresholdHilbert)
    (hq : q ∈ finiteSpace n) :
    ‖x - (finiteSpace n).starProjection x‖ ≤ ‖x - q‖ := by
  have ho : inner ℝ (x - (finiteSpace n).starProjection x)
      ((finiteSpace n).starProjection x - q) = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal x) _
      ((finiteSpace n).sub_mem ((finiteSpace n).starProjection_apply_mem x) hq)
  have he : x - q = (x - (finiteSpace n).starProjection x) +
      ((finiteSpace n).starProjection x - q) := by abel
  have hsq : ‖x - (finiteSpace n).starProjection x‖ ^ 2 ≤ ‖x - q‖ ^ 2 := by
    rw [he, norm_add_sq_real, ho]
    nlinarith [sq_nonneg ‖(finiteSpace n).starProjection x - q‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Section 5.7 for the actual finite projection errors, including the exact
modulus budget needed for the Section 19 logarithmic transfer. -/
theorem finite_point_to_one_error (N J : ℕ) (hN : 2 ≤ N) :
    Real.sqrt (energy (2 ^ J * N - 1)) ≤
      dyadicContraction ^ (J + 1) +
        (1 - dyadicContraction ^ (J + 1)) / (1 - dyadicContraction) *
          Real.sqrt (walkError residueAtom id (paretoPointHilbert 0) (N - 1)) := by
  let q := (finiteSpace (N - 1)).starProjection (paretoPointHilbert 0)
  have hq : q ∈ finiteSpace (N - 1) :=
    (finiteSpace (N - 1)).starProjection_apply_mem _
  have hmem := pointDilationSynthesis_mem N hN q hq J
  have hmin := norm_sub_finite_projection_le (2 ^ J * N - 1)
    hilbertOne (pointDilationSynthesis q (J + 1)) hmem
  have hb := pointDilationSynthesis_error q (J + 1)
  have h := hmin.trans hb
  simpa only [energy, walkError, finiteSpace, q, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using h

end RiemannResearch.RH.Pareto.CoefficientStabilization
