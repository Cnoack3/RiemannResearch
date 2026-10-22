import RiemannResearch.RH.OptimalTwoCoefficientCriterion
import RiemannResearch.RH.CanonicalMobiusFullEnergy

/-!
# Two adjacent error decreases for the actual optimal Pareto projections

Source: continuation of the user's exact optimal-Gram convergence request,
2026-09-22. This independently derived estimate preserves the actual
unconstrained projections; no modified candidate family is substituted.

For the scaled dilation Df(j)=2f(floor(j/2)), the correction
W=-4I-13D+3D^2 has squared norm at most 5425/12.
Orthogonality gives an exact pairing between two successive projection
increments. Its square is bounded by 5425/12 times the product of the
two actual full-error decreases. Project stage n means atoms through n+1.

These are unconditional finite identities. They do not establish zero
limiting error, saturation of the Schur-gain sum, or RH.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
set_option backward.isDefEq.respectTransparency false

def optimalProjectionDilationCorrection : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (-4 : ℝ) • ContinuousLinearMap.id ℝ ThresholdHilbert -
    (13 : ℝ) • doubleDilation + (3 : ℝ) • doubleDilation.comp doubleDilation

theorem dilationCorrection_apply (x : ThresholdHilbert) :
    optimalProjectionDilationCorrection x = (-4 : ℝ) • x - (13 : ℝ) • doubleDilation x +
      (3 : ℝ) • doubleDilation (doubleDilation x) := rfl

theorem dilationCorrection_norm_identity (x : ThresholdHilbert) :
    ‖optimalProjectionDilationCorrection x‖ ^ 2 +
      24 * ‖x + (13 / 24 : ℝ) • doubleDilation x +
        (1 / 2 : ℝ) • doubleDilation (doubleDilation x)‖ ^ 2 =
      (5425 / 12 : ℝ) * ‖x‖ ^ 2 := by
  rw [dilationCorrection_apply]
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    doubleDilation_inner]
  rw [real_inner_comm x (doubleDilation x),
    real_inner_comm x (doubleDilation (doubleDilation x))]
  ring

theorem dilationCorrection_norm_sq_le (x : ThresholdHilbert) :
    ‖optimalProjectionDilationCorrection x‖ ^ 2 ≤ (5425 / 12 : ℝ) * ‖x‖ ^ 2 := by
  have h := dilationCorrection_norm_identity x
  nlinarith [sq_nonneg ‖x + (13 / 24 : ℝ) • doubleDilation x +
    (1 / 2 : ℝ) • doubleDilation (doubleDilation x)‖]

def projectionResidual (n : ℕ) : ThresholdHilbert := hilbertOne - projection n
def quadrupleStage (n : ℕ) : ℕ := 4 * n + 3

theorem projectionResidual_inner_mem (n : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace n) : inner ℝ (projectionResidual n) f = 0 := by
  rw [real_inner_comm]
  exact ((finiteSpace n).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal hilbertOne) _ hf

theorem projection_gap_sq {m n : ℕ} (h : m ≤ n) :
    ‖projection n - projection m‖ ^ 2 = energy m - energy n := by
  have hE := nested_projection_energy (finiteSpace m) (finiteSpace n)
    (walkSpan_mono residueAtom id h) hilbertOne
  change energy m = energy n + ‖projection n - projection m‖ ^ 2 at hE
  linarith

theorem hilbertDilation_mem_quadruple {n : ℕ} {x : ThresholdHilbert}
    (hx : x ∈ finiteSpace n) (m : ℕ) (hm : 0 < m) (hm4 : m ≤ 4) :
    hilbertDilation m hm x ∈ finiteSpace (quadrupleStage n) := by
  classical
  obtain ⟨a, rfl⟩ := finiteSpace_expansion n x hx
  change hilbertDilationContinuous m hm (∑ i : Fin n, a i • residueAtom i.val) ∈ _
  rw [map_sum]
  apply (finiteSpace (quadrupleStage n)).sum_mem
  intro i hi
  rw [map_smul]
  apply (finiteSpace (quadrupleStage n)).smul_mem
  change hilbertDilation m hm (residueAtom i.val) ∈ _
  rw [hilbertDilation_residueAtom]
  apply (finiteSpace (quadrupleStage n)).sub_mem
  · apply (finiteSpace (quadrupleStage n)).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    have hiN : i.val + 2 ≤ n + 1 := by omega
    have hmul := Nat.mul_le_mul hm4 hiN
    simp only [quadrupleStage]
    nlinarith
  · apply (finiteSpace (quadrupleStage n)).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    simp only [quadrupleStage]
    omega

theorem dilationCorrection_mem_quadruple {n : ℕ} {x : ThresholdHilbert}
    (hx : x ∈ finiteSpace n) :
    optimalProjectionDilationCorrection x ∈ finiteSpace (quadrupleStage n) := by
  rw [dilationCorrection_apply, doubleDilation_twice]
  apply (finiteSpace (quadrupleStage n)).add_mem
  · apply (finiteSpace (quadrupleStage n)).sub_mem
    · exact (finiteSpace (quadrupleStage n)).smul_mem _
        (walkSpan_mono residueAtom id (by unfold quadrupleStage; omega) hx)
    · apply (finiteSpace (quadrupleStage n)).smul_mem
      exact hilbertDilation_mem_quadruple hx 2 (by decide) (by decide)
  · apply (finiteSpace (quadrupleStage n)).smul_mem
    exact hilbertDilation_mem_quadruple hx 4 (by decide) (by decide)

theorem dilationCorrection_two_gap (m : ℕ) :
    inner ℝ (projectionResidual (quadrupleStage m))
        (optimalProjectionDilationCorrection (projection (quadrupleStage m))) =
      inner ℝ (projection (quadrupleStage (quadrupleStage m)) -
          projection (quadrupleStage m))
        (optimalProjectionDilationCorrection (projection (quadrupleStage m) - projection m)) := by
  let n := quadrupleStage m
  let k := quadrupleStage n
  have hm : projection m ∈ finiteSpace m := (finiteSpace m).starProjection_apply_mem _
  have hn : projection n ∈ finiteSpace n := (finiteSpace n).starProjection_apply_mem _
  have hmn : m ≤ n := by dsimp [n, quadrupleStage]; omega
  have hv : optimalProjectionDilationCorrection (projection m) ∈ finiteSpace n :=
    dilationCorrection_mem_quadruple hm
  have h0 := projectionResidual_inner_mem n _ hv
  have hdiff : projection n - projection m ∈ finiteSpace n :=
    (finiteSpace n).sub_mem hn (walkSpan_mono residueAtom id hmn hm)
  have h1 := projectionResidual_inner_mem k _
    (dilationCorrection_mem_quadruple hdiff)
  change inner ℝ (projectionResidual n) (optimalProjectionDilationCorrection (projection n)) =
    inner ℝ (projection k - projection n)
      (optimalProjectionDilationCorrection (projection n - projection m))
  have he : projectionResidual n =
      projectionResidual k + (projection k - projection n) := by
    unfold projectionResidual
    abel
  calc
    _ = inner ℝ (projectionResidual n)
        (optimalProjectionDilationCorrection (projection n - projection m)) := by
      rw [map_sub, inner_sub_right, h0, sub_zero]
    _ = _ := by rw [he, inner_add_left, h1, zero_add]

theorem dilationCorrection_two_gap_sq_bound (m : ℕ) :
    (inner ℝ (projectionResidual (quadrupleStage m))
      (optimalProjectionDilationCorrection (projection (quadrupleStage m)))) ^ 2 ≤
    (5425 / 12 : ℝ) *
      (energy (quadrupleStage m) - energy (quadrupleStage (quadrupleStage m))) *
      (energy m - energy (quadrupleStage m)) := by
  rw [dilationCorrection_two_gap]
  let a := projection (quadrupleStage (quadrupleStage m)) - projection (quadrupleStage m)
  let b := projection (quadrupleStage m) - projection m
  have h := norm_inner_le_norm (𝕜 := ℝ) a (optimalProjectionDilationCorrection b)
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  rw [Real.norm_eq_abs] at hs
  have hv := dilationCorrection_norm_sq_le b
  have hmul := mul_le_mul_of_nonneg_left hv (sq_nonneg ‖a‖)
  have ha : ‖a‖ ^ 2 =
      energy (quadrupleStage m) - energy (quadrupleStage (quadrupleStage m)) :=
    projection_gap_sq (by unfold quadrupleStage; omega)
  have hb : ‖b‖ ^ 2 = energy m - energy (quadrupleStage m) :=
    projection_gap_sq (by unfold quadrupleStage; omega)
  change (inner ℝ a (optimalProjectionDilationCorrection b)) ^ 2 ≤ _
  rw [← ha, ← hb]
  nlinarith [sq_abs (inner ℝ a (optimalProjectionDilationCorrection b))]

end RiemannResearch.RH.Pareto.CoefficientStabilization
