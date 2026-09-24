import RiemannResearch.Analysis.ShiftedLiftApproximation
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.LinearCombination

/-!
# Exact inverse matrices for regularized shifted lifts

Source: continuation of the user-provided
RH_Finite_Arithmetic_Shifted_Lifts_2026-09-24 handoff.
The arguments combine the existing finite Hilbert Gram identities with
the shifted-lift completion formula. No mathematical novelty is asserted.

For an independent finite dictionary u, the matrix
Gram(Du) + t^2 Gram(u) is positive definite for t > 0. Its actual inverse
provides the normal solution and the exact full-norm minimum. No normal
solution, invertibility, density, or RH hypothesis is postulated.
The concrete arithmetic consumer is RH/NoorRegularizedGram.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ShiftedLift
open FiniteHilbertGram
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def regularizedGram (S : H →ₗ[ℝ] H) (u : ι → H) (t : ℝ) : Matrix ι ι ℝ :=
  gramMatrix (fun i => difference S (u i)) + t^2 • gramMatrix u

omit [DecidableEq ι] in
theorem difference_linearCombination (S : H →ₗ[ℝ] H) (u : ι → H) (c : ι → ℝ) :
    difference S (Fintype.linearCombination ℝ u c) =
      Fintype.linearCombination ℝ (fun i => difference S (u i)) c := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smul]

omit [DecidableEq ι] in
theorem regularizedGram_mulVec (S : H →ₗ[ℝ] H) (u : ι → H) (t : ℝ) (c : ι → ℝ) (i : ι) :
    (regularizedGram S u t).mulVec c i =
      inner ℝ (difference S (u i)) (difference S (Fintype.linearCombination ℝ u c)) +
        t^2 * inner ℝ (u i) (Fintype.linearCombination ℝ u c) := by
  simp only [regularizedGram, Matrix.add_mulVec, Matrix.smul_mulVec, gramMatrix_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, gram, LinearMap.coe_mk, AddHom.coe_mk,
    difference_linearCombination]

omit [DecidableEq ι] in
theorem regularizedGram_quadratic (S : H →ₗ[ℝ] H) (u : ι → H) (t : ℝ) (c : ι → ℝ) :
    dotProduct c ((regularizedGram S u t).mulVec c) =
      ‖difference S (Fintype.linearCombination ℝ u c)‖^2 +
        t^2 * ‖Fintype.linearCombination ℝ u c‖^2 := by
  rw [difference_linearCombination, gram_quadratic, gram_quadratic]
  simp only [regularizedGram, Matrix.add_mulVec, Matrix.smul_mulVec,
    gramMatrix_mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] in
theorem regularizedGram_posDef (S : H →ₗ[ℝ] H) {u : ι → H}
    (hu : LinearIndependent ℝ u) (t : ℝ) (ht : 0 < t) :
    (regularizedGram S u t).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [regularizedGram, Matrix.conjTranspose_apply, gramMatrix, real_inner_comm]
  · intro c hc
    have hn : Fintype.linearCombination ℝ u c ≠ 0 := by
      intro hz
      apply hc
      apply hu.fintypeLinearCombination_injective
      simpa using hz
    simpa only [star_trivial, regularizedGram_quadratic] using
      add_pos_of_nonneg_of_pos (sq_nonneg ‖difference S (Fintype.linearCombination ℝ u c)‖)
        (mul_pos (sq_pos_of_pos ht) (sq_pos_of_pos (norm_pos_iff.mpr hn)))

def regularizedCoefficients (S : H →ₗ[ℝ] H) (u : ι → H) (a : H) (t : ℝ) : ι → ℝ :=
  (regularizedGram S u t)⁻¹.mulVec (cross (fun i => difference S (u i)) a)

theorem regularizedCoefficients_normal (S : H →ₗ[ℝ] H) {u : ι → H}
    (hu : LinearIndependent ℝ u) (a : H) (t : ℝ) (ht : 0 < t) :
    ∀ w ∈ synthesisSpan u,
      inner ℝ (difference S (Fintype.linearCombination ℝ u (regularizedCoefficients S u a t)) - a)
        (difference S w) +
        t^2 * inner ℝ (Fintype.linearCombination ℝ u (regularizedCoefficients S u a t)) w = 0 := by
  have hsolve : (regularizedGram S u t).mulVec (regularizedCoefficients S u a t) =
      cross (fun i => difference S (u i)) a := by
    rw [regularizedCoefficients, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (ne_of_gt (regularizedGram_posDef S hu t ht).det_pos)),
      Matrix.one_mulVec]
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    have hi := congrFun hsolve i
    rw [regularizedGram_mulVec] at hi
    simp only [cross] at hi
    simp only [inner_sub_left, real_inner_comm] at hi ⊢
    linarith
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [map_add, inner_add_right]
    linarith
  | smul r x hx ih =>
    simp only [map_smul, inner_smul_right]
    linear_combination r * ih

theorem regularizedInf_eq_inverseGram (S : H →ₗ[ℝ] H) {u : ι → H}
    (hu : LinearIndependent ℝ u) (a : H) (t : ℝ) (ht : 0 < t) :
    regularizedInf S a t (synthesisSpan u) =
      ‖a‖^2 - dotProduct (cross (fun i => difference S (u i)) a)
        (regularizedCoefficients S u a t) := by
  rw [regularizedInf_eq_norm_sq_sub_pairing S a t (synthesisSpan u)
    (Fintype.linearCombination ℝ u (regularizedCoefficients S u a t))
    (synthesis_mem u _) (regularizedCoefficients_normal S hu a t ht)]
  rw [difference_linearCombination, inner_synthesis_left]
  congr 1
  simp only [dotProduct, cross, mul_comm]

end RiemannResearch.Analysis.ShiftedLift
