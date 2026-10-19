/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.RH.QTriangularRieszEnergy
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QConductorLimits
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Triangular charge in a finite inverse-Gram direction

Source: the ordinary finite projection argument in
BalazardTriangularResearch20261019.md, extending the dual system of
Michel Balazard, arXiv:1812.04309, Propositions 6--7.

The triangular dual estimate bounds the inverse-Gram quadratic form in
`v_d = 1 - 1/d` for every finite distinct legal dictionary below `N`.
The exact identity retains projection, variance and metric remainders.
The mixed target-direction inequalities do not prove squarefree closure.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.LinearAlgebra.CenteredNormalEquations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem charge_qSynthesis (N : ℕ) (d : ι → ℕ) (c : ι → ℝ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ N) :
    charge N (qSynthesis d c) =
      (N : ℝ)⁻¹ * ∑ i, c i * (1 - 1 / (d i : ℝ)) := by
  unfold charge qSynthesis
  change inner ℝ (triangularChargeRiesz N)
    (toParetoLinear (∑ i, c i • qResidue (d i))) = _
  rw [map_sum, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, real_inner_smul_right]
  change c i * charge N (qResidue (d i)) = _
  rw [charge_qResidue N (d i) (hd i).1 (hd i).2]
  ring

/-- The actual inverse-Gram bound for the collective direction 1-1/d.
Distinct squarefree dictionaries and primorial divisor dictionaries satisfy
these hypotheses, but squarefreeness itself is unnecessary for this estimate. -/
theorem inverseGram_direction_le (N : ℕ) (hN : 0 < N) (d : ι → ℕ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ N) (hinj : Function.Injective d) :
    dotProduct (fun i => 1 - 1 / (d i : ℝ))
      ((residueGramMatrix d)⁻¹.mulVec (fun i => 1 - 1 / (d i : ℝ))) ≤
        zetaTwo * (N : ℝ) ^ 2 * reciprocalMobiusCesaroEnergy N := by
  let v : ι → ℝ := fun i => 1 - 1 / (d i : ℝ)
  let u : ι → ℝ := (residueGramMatrix d)⁻¹.mulVec v
  let A : ℝ := dotProduct v u
  let K : ℝ := zetaTwo * (N : ℝ) ^ 2 * reciprocalMobiusCesaroEnergy N
  change A ≤ K
  have hdet : IsUnit (residueGramMatrix d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt
      (qGram_posDef d (fun i => by have := (hd i).1; omega) hinj).det_pos)
  have hn : (residueGramMatrix d).mulVec u = v := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have he : ‖qSynthesis d u‖ ^ 2 = A := by
    rw [qSynthesis_norm_sq]
    change dot u ((residueGramMatrix d).mulVec u) = A
    rw [hn]
    exact dot_comm u v
  have hc : charge N (qSynthesis d u) = (N : ℝ)⁻¹ * A := by
    rw [charge_qSynthesis N d u hd]
    congr 1
    change dot u v = dot v u
    exact dot_comm u v
  have hA : 0 ≤ A := by rw [← he]; exact sq_nonneg _
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg zetaTwo_pos.le (sq_nonneg _))
      (reciprocalMobiusCesaroEnergy_nonneg N)
  have hb := charge_sq_le N (qSynthesis d u)
  rw [hc, sq_abs, mul_pow, he] at hb
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (N : ℝ))
  field_simp [hN0] at hm
  have hAA : A ^ 2 ≤ K * A := by dsimp [K]; nlinarith
  by_cases ha : A = 0
  · simpa only [ha] using hK
  · have hp : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [pow_two, mul_comm] using hAA)

end RiemannResearch.RH.QTriangularCharge

namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.LinearAlgebra.CenteredNormalEquations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The collective direction controlled by triangular charge. -/
def direction (d : ι → ℕ) : ι → ℝ := fun i => 1 - 1 / (d i : ℝ)

def directionFit (d : ι → ℕ) : QHilbert :=
  qSynthesis d ((residueGramMatrix d)⁻¹.mulVec (direction d))

def directionCapacity (d : ι → ℕ) : ℝ :=
  dotProduct (direction d) ((residueGramMatrix d)⁻¹.mulVec (direction d))

private theorem gram_inverse_normal (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) (b : ι → ℝ) :
    (residueGramMatrix d).mulVec ((residueGramMatrix d)⁻¹.mulVec b) = b := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (qGram_posDef d hd hinj).det_pos)),
    Matrix.one_mulVec]

theorem directionFit_norm_sq (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    ‖directionFit d‖ ^ 2 = directionCapacity d := by
  rw [directionFit, qSynthesis_norm_sq]
  change dot _ ((residueGramMatrix d).mulVec _) = _
  rw [gram_inverse_normal d hd hinj]
  exact dot_comm _ _

theorem directionFit_charge (N : ℕ) (d : ι → ℕ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ N) :
    charge N (directionFit d) = (N : ℝ)⁻¹ * directionCapacity d := by
  rw [directionFit, charge_qSynthesis N d _ hd]
  congr 1
  exact dot_comm _ _

/-- The explicit scaled inverse-Gram fit is the actual orthogonal fit of
the triangular Q vector to this finite dictionary. -/
theorem direction_residual_orthogonal (N : ℕ) (d : ι → ℕ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ N) (hinj : Function.Injective d) (c : ι → ℝ) :
    inner ℝ (riesz N - (N : ℝ)⁻¹ • directionFit d) (qSynthesis d c) = 0 := by
  have hn := gram_inverse_normal d (fun i => by have := (hd i).1; omega)
    hinj (direction d)
  unfold qSynthesis
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [real_inner_smul_right, inner_sub_left, real_inner_smul_left,
    riesz_inner, charge_qResidue N (d i) (hd i).1 (hd i).2]
  have hfit : inner ℝ (directionFit d) (qResidue (d i)) = direction d i := by
    rw [real_inner_comm, directionFit, qGram_synthesis]
    exact congrFun hn i
  rw [hfit]
  change c i * ((N : ℝ)⁻¹ * (1 - 1 / (d i : ℝ)) -
    (N : ℝ)⁻¹ * (1 - 1 / (d i : ℝ))) = 0
  ring

/-- Exact inverse-Gram projection remainder, before discarding anything. -/
theorem direction_projection_energy (N : ℕ) (hN : 0 < N) (d : ι → ℕ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ N) (hinj : Function.Injective d) :
    (N : ℝ)^2 * ‖riesz N‖^2 = directionCapacity d +
      (N : ℝ)^2 * ‖riesz N - (N : ℝ)⁻¹ • directionFit d‖^2 := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, riesz_inner, directionFit_charge N d hd,
    directionFit_norm_sq d (fun i => by have := (hd i).1; omega) hinj]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp [hNR]
  ring

/-- The native-Q inverse-Gram equality retains the projection, variance,
and metric-change remainders separately. -/
theorem inverseGram_energy_identity (n : ℕ) (d : ι → ℕ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ n + 1) (hinj : Function.Injective d) :
    zetaTwo * (n + 1 : ℝ)^2 * reciprocalMobiusCesaroEnergy (n + 1) =
      directionCapacity d +
        (n + 1 : ℝ)^2 *
          ‖riesz (n + 1) - (n + 1 : ℝ)⁻¹ • directionFit d‖^2 +
        zetaTwo * (n + 1 : ℝ)^2 * triangularChargeVariance n +
        zetaTwo * (n + 1 : ℝ)^2 * metricRemainder (n + 1) := by
  have he := riesz_energy_identity n
  have hp := direction_projection_energy (n + 1) (Nat.succ_pos n) d hd hinj
  push_cast at hp
  nlinarith

/-- The improved finite bound subtracts the two exact nonnegative defects. -/
theorem inverseGram_direction_le_exact (n : ℕ) (d : ι → ℕ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ n + 1) (hinj : Function.Injective d) :
    directionCapacity d ≤ zetaTwo * (n + 1 : ℝ)^2 *
      (reciprocalMobiusCesaroEnergy (n + 1) -
        triangularChargeVariance n - metricRemainder (n + 1)) := by
  have he := inverseGram_energy_identity n d hd hinj
  nlinarith [mul_nonneg (sq_nonneg (n + 1 : ℝ))
    (sq_nonneg ‖riesz (n + 1) - (n + 1 : ℝ)⁻¹ • directionFit d‖)]

/-- The actual target-mean fit uses b, rather than the charge direction. -/
def targetFit (d : ι → ℕ) : QHilbert :=
  qSynthesis d ((residueGramMatrix d)⁻¹.mulVec (qMean d))

theorem target_residual_orthogonal (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) (c : ι → ℝ) :
    inner ℝ (qOne - targetFit d) (qSynthesis d c) = 0 := by
  have hn := gram_inverse_normal d hd hinj (qMean d)
  unfold qSynthesis
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [real_inner_smul_right, inner_sub_left]
  have hfit : inner ℝ (targetFit d) (qResidue (d i)) = qMean d i := by
    rw [real_inner_comm, targetFit, qGram_synthesis]
    exact congrFun hn i
  rw [hfit]
  change c i * (qMean d i - qMean d i) = 0
  ring

theorem target_residual_energy (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    ‖qOne - targetFit d‖ ^ 2 =
      1 - dotProduct (qMean d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)) := by
  apply qError_gram_solution
  intro i
  exact congrFun (gram_inverse_normal d hd hinj (qMean d)) i

/-- A residual test yields a LOWER certificate for target error.
The remaining factor is exactly the orthogonal dual remainder energy. -/
theorem target_charge_residual_certificate (N : ℕ) (hN : 0 < N) (d : ι → ℕ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ N) (hinj : Function.Injective d) :
    ((N : ℝ) * charge N qOne -
      dotProduct (direction d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)))^2 ≤
      ‖qOne - targetFit d‖^2 *
        ((N : ℝ)^2 * ‖riesz N‖^2 - directionCapacity d) := by
  let r : QHilbert := qOne - targetFit d
  let t : QHilbert := riesz N - (N : ℝ)⁻¹ • directionFit d
  have ho : inner ℝ (directionFit d) r = 0 := by
    rw [real_inner_comm]
    exact target_residual_orthogonal d (fun i => by have := (hd i).1; omega)
      hinj _
  have hc : inner ℝ t r =
      charge N qOne - (N : ℝ)⁻¹ *
        dotProduct (direction d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)) := by
    dsimp [t, r]
    rw [inner_sub_left, real_inner_smul_left]
    change inner ℝ (riesz N) (qOne - targetFit d) -
      (N : ℝ)⁻¹ * inner ℝ (directionFit d) r = _
    rw [ho, mul_zero, sub_zero, inner_sub_right, riesz_inner, riesz_inner]
    rw [targetFit, charge_qSynthesis N d _ hd]
    congr 2
    exact dot_comm _ _
  have hp := direction_projection_energy N hN d hd hinj
  change (N : ℝ)^2 * ‖riesz N‖^2 =
    directionCapacity d + (N : ℝ)^2 * ‖t‖^2 at hp
  have hcs := real_inner_mul_inner_self_le t r
  rw [← pow_two, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hc] at hcs
  have hm := mul_le_mul_of_nonneg_left hcs (sq_nonneg (N : ℝ))
  have hid : (N : ℝ)^2 *
      (charge N qOne - (N : ℝ)⁻¹ *
        dotProduct (direction d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)))^2 =
      ((N : ℝ) * charge N qOne -
        dotProduct (direction d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)))^2 := by
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    field_simp [hNR]
  rw [hid] at hm
  dsimp [r] at hm
  nlinarith



theorem targetFit_norm_sq (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    ‖targetFit d‖ ^ 2 =
      dotProduct (qMean d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)) := by
  rw [targetFit, qSynthesis_norm_sq]
  change dot _ ((residueGramMatrix d).mulVec _) = _
  rw [gram_inverse_normal d hd hinj]
  exact dot_comm _ _

theorem direction_target_inner (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    inner ℝ (directionFit d) (targetFit d) =
      dotProduct (direction d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)) := by
  have hn := gram_inverse_normal d hd hinj (direction d)
  unfold targetFit qSynthesis
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_smul_right]
  have hf : inner ℝ (directionFit d) (qResidue (d i)) = direction d i := by
    rw [real_inner_comm, directionFit, qGram_synthesis]
    exact congrFun hn i
  rw [hf]
  ring

/-- The mixed inverse-Gram correlation gives a genuine lower bound on target
captured energy if its ratio to directionCapacity is controlled from below.
Triangular dual convergence by itself supplies no such lower control. -/
theorem direction_target_gram_cauchy (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    (dotProduct (direction d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)))^2 ≤
      directionCapacity d *
        dotProduct (qMean d) ((residueGramMatrix d)⁻¹.mulVec (qMean d)) := by
  have h := real_inner_mul_inner_self_le (directionFit d) (targetFit d)
  rw [← pow_two, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    direction_target_inner d hd hinj, directionFit_norm_sq d hd hinj,
    targetFit_norm_sq d hd hinj] at h
  exact h

/-- Each target mean vanishes along escaping conductors, in contrast to v_d. -/
theorem target_mean_tendsto_zero (d : ℕ → ℕ)
    (hd : Filter.Tendsto d Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => inner ℝ qOne (qResidue (d j)))
      Filter.atTop (nhds 0) := by
  have hc : Continuous (fun x : QHilbert => inner ℝ qOne x) :=
    continuous_const.inner continuous_id
  simpa only [Function.comp_def, inner_zero_right] using
    (hc.tendsto (0 : QHilbert)).comp (qResidue_tendsto_zero d hd)

theorem direction_tendsto_one (d : ℕ → ℕ)
    (hd : Filter.Tendsto d Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => 1 - 1 / (d j : ℝ))
      Filter.atTop (nhds 1) := by
  simpa using (tendsto_const_nhds.sub
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hd))

/-- No nonzero fixed scalar identifies b_d with v_d along escaping conductors.
This rules out that simple identification, not every inverse-metric comparison. -/
theorem scalar_identification_forces_zero (d : ℕ → ℕ)
    (hd : Filter.Tendsto d Filter.atTop Filter.atTop) (a : ℝ)
    (he : ∀ j, inner ℝ qOne (qResidue (d j)) = a * (1 - 1 / (d j : ℝ))) :
    a = 0 := by
  have hb := target_mean_tendsto_zero d hd
  have ha := (direction_tendsto_one d hd).const_mul a
  simp only [mul_one] at ha
  simp_rw [he] at hb
  exact (tendsto_nhds_unique hb ha).symm

end RiemannResearch.RH.QTriangularCharge
