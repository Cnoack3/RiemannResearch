import RiemannResearch.Analysis.NestedProjectionPairing
import RiemannResearch.RH.ResidueGramCorrectionPairing

/-!
# Dimension-independent covariance control of inverse-Gram corrections

Source: user-requested control of the actual inverse-Gram Mobius correction,
28 September 2026. These proofs combine the existing coefficient Riesz duals
and full inverse-Gram identities with orthogonal projection Cauchy--Schwarz.
No mathematical novelty is asserted for the Hilbert-space estimates.

Stage n uses conductors 2,...,n+1. The covariance bound retains signed
combinations and the full dual residual Gram matrix, with constant one.
The stabilization bound uses two vanishing projection gaps, yielding a
little-o improvement over the earlier fixed-dual-norm multiplier.

Established without RH: all the estimates in this module.
Open: the limiting correction is zero for every conductor. Its remaining
bound involves limitEnergy and the uncaptured limiting dual energy; neither
is assumed to vanish. See RH/InverseGramCorrectionCovariance20260928.md.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
open RiemannResearch.Analysis.NestedProjectionEnergy
open RiemannResearch.Analysis.NestedProjectionPairing
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The correction is a test of the optimal, rather than natural, residual. -/
theorem correction_eq_neg_residual_pairing (n i : ℕ) :
    correction n (i + 2) =
      -inner ℝ (hilbertOne - projection n) (coefficientDual i) := by
  rw [coefficientDual_inner, correction_eq_residual_coordinate n (i+2) (by omega)]
  simp only [coefficientCLM, neg_apply, neg_neg]

/-- A single correction is controlled by energy times the inverse-diagonal deficit. -/
theorem correction_sq_le_inverse_diagonal_defect (n : ℕ) (i : Fin n) :
    correctionVector n i ^ 2 ≤ energy n *
      (‖coefficientDual i.val‖ ^ 2 - residueInverseEntry n i i) := by
  rw [correctionVector_apply, correction_eq_neg_residual_pairing, neg_sq]
  have h := residual_pairing_sq_le (finiteSpace n) hilbertOne (coefficientDual i.val)
  rw [residueInverseEntry_projection, real_inner_self_eq_norm_sq]
  exact h

/-- The full signed quadratic form is the Gram form of the missed duals. -/
theorem dualResidual_synthesis_norm_sq (n : ℕ) (a : Fin n → ℝ) :
    ‖∑ i : Fin n, a i • dualResidual n i.val‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, a i * a j *
        (inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
          residueInverseEntry n i j) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [dualResidual, dualResidual, residueInverseEntry_residual]
  ring

/-- Dimension-independent covariance bound, for every signed test vector. -/
theorem correction_quadratic_le_residual_covariance (n : ℕ) (a : Fin n → ℝ) :
    (∑ i : Fin n, a i * correctionVector n i)^2 ≤ energy n *
      (∑ i : Fin n, ∑ j : Fin n, a i * a j *
        (inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
          residueInverseEntry n i j)) := by
  rw [← dualResidual_synthesis_norm_sq]
  have ho (i : Fin n) : inner ℝ (hilbertOne - projection n)
      ((finiteSpace n).starProjection (coefficientDual i.val)) = 0 :=
    Submodule.starProjection_inner_eq_zero hilbertOne _
      ((finiteSpace n).starProjection_apply_mem _)
  have he : (∑ i : Fin n, a i * correctionVector n i) =
      -inner ℝ (hilbertOne - projection n)
        (∑ i : Fin n, a i • dualResidual n i.val) := by
    simp only [inner_sum, real_inner_smul_right, dualResidual, inner_sub_right,
      ho, sub_zero, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [correctionVector_apply, correction_eq_neg_residual_pairing]
    ring
  rw [he, neg_sq]
  exact real_pairing_sq_le _ _

/-- Remaining energy of a fixed coefficient dual inside the limiting legal space. -/
def dualProjectionGap (n i : ℕ) : ℝ :=
  ‖closedSpace.starProjection (coefficientDual i) -
    (finiteSpace n).starProjection (coefficientDual i)‖ ^ 2

/-- This gap always vanishes; the complementary dual defect need not vanish. -/
theorem dualProjectionGap_tendsto_zero (i : ℕ) :
    Tendsto (fun n => dualProjectionGap n i) atTop (𝓝 0) := by
  have hc : Tendsto
      (fun _ : ℕ => closedSpace.starProjection (coefficientDual i)) atTop
      (𝓝 (closedSpace.starProjection (coefficientDual i))) := tendsto_const_nhds
  have h := (hc.sub
    (walkProjection_tendsto residueAtom id Function.surjective_id (coefficientDual i))).norm.pow 2
  simpa only [dualProjectionGap, finiteSpace, closedSpace, sub_self, norm_zero,
    zero_pow (by decide : (2:ℕ) ≠ 0)] using h

/-- Stabilization is controlled by the product of primal and dual projection gaps. -/
theorem correction_error_sq_le_two_gaps (n i : ℕ) :
    (correction n (i + 2) -
      (limitCoefficient (i + 2) + (ArithmeticFunction.moebius (i + 2) : ℝ)))^2 ≤
      (energy n - limitEnergy) * dualProjectionGap n i := by
  have hle : finiteSpace n ≤ closedSpace :=
    (walkSpan_le residueAtom id n).trans
      (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
  have h := nested_pairing_sq_le hle hilbertOne (coefficientDual i)
  have hi : inner ℝ (limitProjection - projection n) (coefficientDual i) =
      limitCoefficient (i+2) - coefficient n (i+2) := by
    rw [coefficientDual_inner, map_sub]
    rfl
  change (inner ℝ (limitProjection - projection n) (coefficientDual i))^2 ≤
    ‖limitProjection - projection n‖^2 * dualProjectionGap n i at h
  rw [hi] at h
  have he : energy n - limitEnergy = ‖limitProjection - projection n‖^2 := by
    linarith [energy_eq_limit_add n]
  rw [he]
  have hc : correction n (i+2) -
      (limitCoefficient (i+2) + (ArithmeticFunction.moebius (i+2) : ℝ)) =
      -(limitCoefficient (i+2) - coefficient n (i+2)) := by
    unfold correction
    ring
  rw [hc, neg_sq]
  exact h

/-- A vanishing multiplier improves the earlier constant-norm error bound. -/
theorem correction_error_sq_isLittleO_energy_excess (i : ℕ) :
    (fun n => (correction n (i+2) -
      (limitCoefficient (i+2) + (ArithmeticFunction.moebius (i+2) : ℝ)))^2)
      =o[atTop] (fun n => energy n - limitEnergy) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [(dualProjectionGap_tendsto_zero i).eventually_lt_const hε] with n hn
  have he : 0 ≤ energy n - limitEnergy := by
    linarith [energy_eq_limit_add n, sq_nonneg ‖limitProjection - projection n‖]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg he]
  exact (correction_error_sq_le_two_gaps n i).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hn.le he])

/-- The dual gap is the remaining inverse-diagonal increase to its actual limit. -/
theorem dualProjectionGap_eq_inverse_excess (n : ℕ) (i : Fin n) :
    dualProjectionGap n i.val =
      ‖closedSpace.starProjection (coefficientDual i.val)‖ ^ 2 -
        residueInverseEntry n i i := by
  have hle : finiteSpace n ≤ closedSpace :=
    (walkSpan_le residueAtom id n).trans
      (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
  have h := captured_energy_eq_add_gap hle (coefficientDual i.val)
  rw [residueInverseEntry_projection, real_inner_self_eq_norm_sq]
  unfold dualProjectionGap
  linarith

/-- The limiting correction is bounded, but is not asserted equal to zero. -/
theorem correction_limit_sq_le_dual_defect (i : ℕ) :
    (limitCoefficient (i+2) + (ArithmeticFunction.moebius (i+2) : ℝ))^2 ≤
      limitEnergy * (‖coefficientDual i‖^2 -
        ‖closedSpace.starProjection (coefficientDual i)‖^2) := by
  have h := residual_pairing_sq_le closedSpace hilbertOne (coefficientDual i)
  change (inner ℝ limitResidual (coefficientDual i))^2 ≤ _ at h
  rw [coefficientDual_inner] at h
  have hc := limitCoefficient_eq_residual (i+2) (by omega)
  simp only [coefficientCLM, neg_apply, neg_sq] at h
  change _ ≤ ‖limitResidual‖^2 * _ at h
  change _ ≤ ‖limitResidual‖^2 * _
  have hcm : limitCoefficient (i+2) +
      (ArithmeticFunction.moebius (i+2) : ℝ) =
      mobiusDifferenceCLM (i+2) limitResidual := by linarith [hc]
  rw [hcm]
  exact h
/-- An explicit signed two-coordinate bound, uniform in the cutoff. -/
theorem correction_two_three_linear_bound (n : ℕ) (u v : ℝ) :
    (u * correction n 2 + v * correction n 3)^2 ≤
      energy n * (14 * u^2 - 4 * u * v + 20 * v^2) := by
  have hp := real_pairing_sq_le (hilbertOne - projection n)
    (u • coefficientDual 0 + v • coefficientDual 1)
  have he : inner ℝ (hilbertOne - projection n)
      (u • coefficientDual 0 + v • coefficientDual 1) =
      -(u * correction n 2 + v * correction n 3) := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      correction_eq_neg_residual_pairing n 0,
      correction_eq_neg_residual_pairing n 1]
    ring
  have hn : ‖u • coefficientDual 0 + v • coefficientDual 1‖^2 =
      14 * u^2 - 4 * u * v + 20 * v^2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      coefficientDual_two_norm_sq, coefficientDual_three_norm_sq,
      real_inner_smul_left, real_inner_smul_right, coefficientDual_two_three_inner]
    ring
  rw [he, neg_sq, hn] at hp
  exact hp

/-- The exact ellipse obtained from the two coefficient-dual Gram matrix. -/
theorem correction_two_three_ellipse (n : ℕ) :
    20 * correction n 2 ^ 2 + 4 * correction n 2 * correction n 3 +
      14 * correction n 3 ^ 2 ≤ 276 * energy n := by
  let x := correction n 2
  let y := correction n 3
  let q := 20 * x^2 + 4 * x * y + 14 * y^2
  have hq : 0 ≤ q := by
    dsimp [q]
    nlinarith [sq_nonneg (x+y), sq_nonneg x, sq_nonneg y]
  have h := correction_two_three_linear_bound n (20*x+2*y) (2*x+14*y)
  change ((20*x+2*y)*x+(2*x+14*y)*y)^2 ≤
    energy n * (14*(20*x+2*y)^2 - 4*(20*x+2*y)*(2*x+14*y) +
      20*(2*x+14*y)^2) at h
  have hl : (20*x+2*y)*x+(2*x+14*y)*y = q := by dsimp [q]; ring
  have hr : 14*(20*x+2*y)^2 - 4*(20*x+2*y)*(2*x+14*y) +
      20*(2*x+14*y)^2 = 276*q := by dsimp [q]; ring
  rw [hl, hr] at h
  change q ≤ 276 * energy n
  have he : 0 ≤ energy n := sq_nonneg _
  rcases eq_or_lt_of_le hq with hz | hz
  · rw [← hz]; positivity
  · nlinarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
