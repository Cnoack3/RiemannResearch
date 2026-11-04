/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ClosedInvariantCalculus
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QSquarefreeDisplacementEnergy
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.RH.QSquarefreePrimeProductCriterion
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QSquarefreeResidualTail
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
/-!
# Actual displacement inverse and Schur operator

The Neumann inverse is constructed in operator norm, not postulated.
With P the legal projection and N = I-P, let A=PBP, R=(I-A)^{-1},
L=RPB and K=NB(N+LN). Then d=Lr and Kr is the actual orthogonal witness.

Source for Schur/shorted-operator terminology and block-elimination strategy:
W. N. Anderson and G. E. Trapp, "Shorted Operators. II", SIAM J. Appl. Math.
28 (1975), 60-71, https://doi.org/10.1137/0128007.
Here I-K is the Schur complement of I-B on the normal space.
The concrete arithmetic application is derived from the repository's
Q/P normal equation, not asserted by that published paper.

The boundedness premise in the final criterion is Open. Operator norm
boundedness of K does not give a uniform physical bound on (Kr)(n).
-/

noncomputable section
open scoped Topology
open RiemannResearch.RH
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeDisplacementRigidity QSquarefreeDisplacementResolvent
open QSquarefreeSmoothedProjection QSquarefreeResidualTail
open QSquarefreeBoundary QSquarefreeDisplacementEnergy
open RiemannResearch.Analysis.ClosedInvariantCalculus
namespace RiemannResearch.RH.QSquarefreeSchurOperator
def compressedB : QHilbert →L[ℝ] QHilbert :=
  closure.starProjection * B * closure.starProjection
theorem compressedB_norm_le : ‖compressedB‖ ≤ (1 / 2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  exact (Submodule.norm_starProjection_apply_le closure _).trans
    ((B_norm_le_half _).trans
      (mul_le_mul_of_nonneg_left
        (Submodule.norm_starProjection_apply_le closure x) (by norm_num)))
theorem compressedB_powers_summable : Summable (fun n : ℕ => compressedB ^ n) :=
  summable_geometric_of_norm_lt_one (lt_of_le_of_lt compressedB_norm_le (by norm_num))
def inverseCompression : QHilbert →L[ℝ] QHilbert := neumann compressedB
theorem inverseCompression_mul :
    inverseCompression * (1 - compressedB) = 1 :=
  neumann_mul_one_sub compressedB_powers_summable
theorem mul_inverseCompression :
    (1 - compressedB) * inverseCompression = 1 :=
  one_sub_mul_neumann compressedB_powers_summable
theorem displacement_equation :
    (1 - compressedB) displacement = correction := by
  have h := displacement_fixed_point
  have hp := Submodule.starProjection_eq_self_iff.mpr displacement_mem
  change displacement -
    closure.starProjection (B (closure.starProjection displacement)) = correction
  rw [hp]
  exact sub_eq_iff_eq_add.mpr h
theorem displacement_eq_inverseCompression :
    displacement = inverseCompression correction := by
  rw [← displacement_equation]
  change displacement = (inverseCompression * (1 - compressedB)) displacement
  rw [inverseCompression_mul, one_apply_eq_self]

theorem inverseCompression_preserves {x : QHilbert} (hx : x ∈ closure) :
    inverseCompression x ∈ closure := by
  apply neumann_apply_mem closure QSquarefreeBoundary.closure_isClosed
    (T := compressedB) ?_ hx
  intro y hy
  exact closure.starProjection_apply_mem _
def response : QHilbert →L[ℝ] QHilbert :=
  inverseCompression * closure.starProjection * B
theorem response_mem (x : QHilbert) : response x ∈ closure :=
  inverseCompression_preserves (closure.starProjection_apply_mem _)
theorem response_equation (x : QHilbert) :
    response x - closure.starProjection (B (response x)) =
      closure.starProjection (B x) := by
  have hi := congrArg (fun T : QHilbert →L[ℝ] QHilbert =>
    T (closure.starProjection (B x))) mul_inverseCompression
  have hp := Submodule.starProjection_eq_self_iff.mpr (response_mem x)
  change response x - closure.starProjection (B (closure.starProjection (response x))) =
    closure.starProjection (B x) at hi
  rwa [hp] at hi
theorem response_normal (x : QHilbert) :
    closure.starProjection (B (x + response x)) = response x := by
  rw [map_add, map_add]
  have h := response_equation x
  exact (sub_eq_iff_eq_add.mp h).symm
theorem response_residual : response limitingResidual = displacement :=
  displacement_eq_inverseCompression.symm
def schurOperator : QHilbert →L[ℝ] QHilbert :=
  closureᗮ.starProjection * B *
    (closureᗮ.starProjection + response * closureᗮ.starProjection)
theorem schurOperator_residual : schurOperator limitingResidual = witness := by
  have hr : closureᗮ.starProjection limitingResidual = limitingResidual :=
    Submodule.starProjection_eq_self_iff.mpr limitingResidual_mem_squarefree_orthogonal
  change closureᗮ.starProjection
    (B (closureᗮ.starProjection limitingResidual +
      response (closureᗮ.starProjection limitingResidual))) = witness
  rw [hr, response_residual, ← pResidual_eq_residual_add_displacement,
    Submodule.starProjection_orthogonal_val,
    ← displacement_eq_projected_pResidual]
  rfl
theorem inner_normal_projection (x y : QHilbert) (hx : x ∈ closureᗮ) :
    inner ℝ x (closureᗮ.starProjection y) = inner ℝ x y := by
  rw [Submodule.starProjection_orthogonal_val, inner_sub_right]
  have h : inner ℝ x (closure.starProjection y) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (closure.starProjection_apply_mem _) hx
  rw [h, sub_zero]
theorem schur_energy_exact (x : QHilbert) (hx : x ∈ closureᗮ) :
    inner ℝ x (schurOperator x) =
      inner ℝ x (B x) + ‖response x‖ ^ 2 -
        inner ℝ (response x) (B (response x)) := by
  have hp : closureᗮ.starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  have hn := Submodule.inner_right_of_mem_orthogonal (response_mem x)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure)
      (B (x + response x)))
  rw [response_normal, inner_sub_right, map_add, inner_add_right,
    real_inner_self_eq_norm_sq] at hn
  have hs : inner ℝ (response x) (B x) = inner ℝ x (B (response x)) := by
    rw [← B_symmetric, real_inner_comm]
  change inner ℝ x (closureᗮ.starProjection
    (B (closureᗮ.starProjection x + response (closureᗮ.starProjection x)))) = _
  rw [hp, inner_normal_projection x _ hx, map_add, inner_add_right]
  linarith [hs]
theorem schur_energy_lower (x : QHilbert) (hx : x ∈ closureᗮ) :
    inner ℝ x (B x) + (1017 / 2000 : ℝ) * ‖response x‖ ^ 2 ≤
      inner ℝ x (schurOperator x) := by
  rw [schur_energy_exact x hx]
  have h := B_inner_le_four_site_983_2000
    (fourSiteFunctional_zero_on_closure (response_mem x))
  linarith
theorem schur_faithful (x : QHilbert) (hx : x ∈ closureᗮ)
    (hz : inner ℝ x (schurOperator x) = 0) : x = 0 := by
  have h := schur_energy_lower x hx
  have hb := B_positive x
  apply B_faithful x
  nlinarith [sq_nonneg ‖response x‖]
theorem residual_zero_of_schur_physically_bounded
    (C : ℝ) (h : ∀ n, |qSequence (schurOperator limitingResidual) n| ≤ C) :
    limitingResidual = 0 := by
  rw [schurOperator_residual] at h
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 0)
  exact residual_eq_zero_of_witness_mean_zero
    (bounded_annihilator_mean_eq_zero
      witness witness_mem_orthogonal C hC h)
theorem prime_products_of_schur_physically_bounded
    (C : ℝ) (h : ∀ n, |qSequence (schurOperator limitingResidual) n| ≤ C) :
    QSquarefreePrimeProductCriterion.DisplacementPrimeProductsLegal :=
  QSquarefreePrimeProductCriterion.residual_zero_iff_displacement_prime_products.mp
    (residual_zero_of_schur_physically_bounded C h)
theorem schur_variational_identity (x : QHilbert) (hx : x ∈ closureᗮ)
    (y : QHilbert) (hy : y ∈ closure) :
    inner ℝ (x + y) (B (x + y)) - ‖y‖ ^ 2 =
      inner ℝ x (schurOperator x) -
        (‖y - response x‖ ^ 2 - inner ℝ (y - response x) (B (y - response x))) := by
  have hn := Submodule.inner_right_of_mem_orthogonal hy
    (Submodule.sub_starProjection_mem_orthogonal (K := closure)
      (B (x + response x)))
  rw [response_normal, inner_sub_right, map_add, inner_add_right] at hn
  have hxy : inner ℝ x (B y) = inner ℝ y (B x) := by
    rw [← B_symmetric, real_inner_comm]
  have hzy : inner ℝ (response x) (B y) = inner ℝ y (B (response x)) := by
    rw [← B_symmetric, real_inner_comm]
  rw [schur_energy_exact x hx]
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, norm_sub_sq_real]
  nlinarith
theorem schur_variational_gap (x : QHilbert) (hx : x ∈ closureᗮ)
    (y : QHilbert) (hy : y ∈ closure) :
    (1017 / 2000 : ℝ) * ‖y - response x‖ ^ 2 ≤
      inner ℝ x (schurOperator x) -
        (inner ℝ (x + y) (B (x + y)) - ‖y‖ ^ 2) := by
  rw [schur_variational_identity x hx y hy]
  have h := B_inner_le_four_site_983_2000
    (fourSiteFunctional_zero_on_closure (closure.sub_mem hy (response_mem x)))
  linarith
theorem response_unique_maximizer (x : QHilbert) (hx : x ∈ closureᗮ)
    (y : QHilbert) (hy : y ∈ closure) :
    inner ℝ (x + y) (B (x + y)) - ‖y‖ ^ 2 = inner ℝ x (schurOperator x) ↔
      y = response x := by
  constructor
  · intro he
    have h := schur_variational_gap x hx y hy
    rw [he, sub_self] at h
    have hz : ‖y - response x‖ = 0 := by nlinarith [norm_nonneg (y - response x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro he
    rw [schur_variational_identity x hx y hy, he, sub_self]
    simp
theorem inverseCompression_mem_closed_algebra
    (S : Subalgebra ℝ (QHilbert →L[ℝ] QHilbert))
    (hS : IsClosed (S : Set (QHilbert →L[ℝ] QHilbert)))
    (hp : closure.starProjection ∈ S) (hb : B ∈ S) :
    inverseCompression ∈ S := by
  have ha : compressedB ∈ S := S.mul_mem (S.mul_mem hp hb) hp
  change (∑' n : ℕ, compressedB ^ n) ∈ S
  exact tsum_mem hS (fun n => S.pow_mem ha n)
theorem schurOperator_mem_closed_algebra
    (S : Subalgebra ℝ (QHilbert →L[ℝ] QHilbert))
    (hS : IsClosed (S : Set (QHilbert →L[ℝ] QHilbert)))
    (hp : closure.starProjection ∈ S) (hb : B ∈ S) :
    schurOperator ∈ S := by
  have hR := inverseCompression_mem_closed_algebra S hS hp hb
  have hL : response ∈ S := S.mul_mem (S.mul_mem hR hp) hb
  have he : closureᗮ.starProjection = 1 - closure.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    exact Submodule.starProjection_orthogonal_val (K := closure) x
  have hN : closureᗮ.starProjection ∈ S := by
    rw [he]
    exact S.sub_mem S.one_mem hp
  exact S.mul_mem (S.mul_mem hN hb) (S.add_mem hN (S.mul_mem hL hN))
theorem schur_bilinear_exact (x y : QHilbert)
    (hx : x ∈ closureᗮ) (hy : y ∈ closureᗮ) :
    inner ℝ x (schurOperator y) = inner ℝ x (B y) +
      inner ℝ (response x) (response y) -
        inner ℝ (response x) (B (response y)) := by
  have hn := Submodule.inner_right_of_mem_orthogonal (response_mem y)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure)
      (B (x + response x)))
  rw [response_normal, inner_sub_right, map_add, inner_add_right] at hn
  have hxy : inner ℝ (response y) (B x) = inner ℝ x (B (response y)) := by
    rw [← B_symmetric, real_inner_comm]
  have hrr : inner ℝ (response y) (B (response x)) =
      inner ℝ (response x) (B (response y)) := by
    rw [← B_symmetric, real_inner_comm]
  have hp : closureᗮ.starProjection y = y :=
    Submodule.starProjection_eq_self_iff.mpr hy
  change inner ℝ x (closureᗮ.starProjection
    (B (closureᗮ.starProjection y + response (closureᗮ.starProjection y)))) = _
  rw [hp, inner_normal_projection x _ hx, map_add, inner_add_right]
  have hr := real_inner_comm (response x) (response y)
  linarith
theorem schur_symmetric_on_normal (x y : QHilbert)
    (hx : x ∈ closureᗮ) (hy : y ∈ closureᗮ) :
    inner ℝ (schurOperator x) y = inner ℝ x (schurOperator y) := by
  have hc : inner ℝ (schurOperator x) y = inner ℝ y (schurOperator x) :=
    real_inner_comm _ _
  rw [hc, schur_bilinear_exact y x hy hx, schur_bilinear_exact x y hx hy]
  have hxy : inner ℝ y (B x) = inner ℝ x (B y) := by
    rw [← B_symmetric, real_inner_comm]
  have hrr : inner ℝ (response y) (B (response x)) =
      inner ℝ (response x) (B (response y)) := by
    rw [← B_symmetric, real_inner_comm]
  have hr := real_inner_comm (response x) (response y)
  linarith
end RiemannResearch.RH.QSquarefreeSchurOperator
