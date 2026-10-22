/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MobiusTriangularEnergy
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Triangular reciprocal-charge bounds in the actual squarefree Q geometry

Source: the triangular-dual refinement of Michel Balazard,
arXiv:1812.04309, Propositions 6--7, developed in
BalazardTriangularResearch20261019.md. The imported concrete energy
identity is unconditional.

The functional uses the unchanged physical sequence under Q-to-P transport.
No equality of P and Q orthogonal projections is used. The coefficient
inequality controls the direction 1-1/d, not the target mean direction.
This module therefore does not establish squarefree closure or RH.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open SquarefreeMobiusProjection

def charge (N : ℕ) (h : QHilbert) : ℝ :=
  inner ℝ (triangularChargeRiesz N) (toPareto h)

theorem charge_eq_sum (N : ℕ) (h : QHilbert) :
    charge N h = ∑ d ∈ Finset.Icc 1 N,
      (1 - (d : ℝ) / (N : ℝ)) * mobiusDifferenceCLM d (toPareto h) / (d : ℝ) :=
  triangularChargeRiesz_inner N (toPareto h)

theorem charge_eq_coefficient_sum (N : ℕ) (h : QHilbert) :
    charge N h = -(∑ d ∈ Finset.Icc 1 N,
      (1 - (d : ℝ) / (N : ℝ)) * qCoefficientCLM d h / (d : ℝ)) := by
  rw [charge_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  change (1 - (d : ℝ) / (N : ℝ)) * mobiusDifferenceCLM d (toPareto h) / (d : ℝ) =
    -((1 - (d : ℝ) / (N : ℝ)) * (-mobiusDifferenceCLM d (toPareto h)) / (d : ℝ))
  ring

/-- Sharp Q/P comparison factor; the entire Q norm is present. -/
theorem charge_sq_le (N : ℕ) (h : QHilbert) :
    |charge N h| ^ 2 ≤ zetaTwo * reciprocalMobiusCesaroEnergy N * ‖h‖ ^ 2 := by
  have hc : charge N h ^ 2 ≤
      ‖triangularChargeRiesz N‖ ^ 2 * ‖toPareto h‖ ^ 2 := by
    have hc := real_inner_mul_inner_self_le (triangularChargeRiesz N) (toPareto h)
    simpa only [charge, ← pow_two, real_inner_self_eq_norm_sq] using hc
  calc
    |charge N h| ^ 2 = charge N h ^ 2 := sq_abs _
    _ ≤ ‖triangularChargeRiesz N‖ ^ 2 * ‖toPareto h‖ ^ 2 := hc
    _ ≤ reciprocalMobiusCesaroEnergy N * (zetaTwo * ‖h‖ ^ 2) :=
      mul_le_mul (triangularChargeRiesz_norm_sq_le N) (toPareto_norm_sq_le h)
        (sq_nonneg _) (reciprocalMobiusCesaroEnergy_nonneg N)
    _ = _ := by ring

/-- Bounded moving tests need no strong convergence, and no cofinality of
their optimizer stage. Only the conductor cutoff tends to infinity. -/
theorem charge_moving_tendsto_zero (h : ℕ → QHilbert) (B : ℝ)
    (hb : ∀ N, ‖h N‖ ≤ B) :
    Tendsto (fun N => charge N (h N)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N =>
      ‖triangularChargeRiesz N‖ * (Real.sqrt zetaTwo * B)) atTop (𝓝 0) := by
    simpa only [norm_zero, zero_mul] using
      triangularChargeRiesz_tendsto_zero.norm.mul_const (Real.sqrt zetaTwo * B)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro N
  apply (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (toPareto_norm_le (h N)).trans
    (mul_le_mul_of_nonneg_left (hb N) (Real.sqrt_nonneg _))

private theorem stage_energy (n : ℕ) :
    1 = ‖ZetaTwoOptimizerStage.residual n‖ ^ 2 +
      ‖ZetaTwoOptimizerStage.optimizer n‖ ^ 2 := by
  have hz : ZetaTwoOptimizerStage.optimizer 0 = 0 := by
    simp [ZetaTwoOptimizerStage.optimizer, ZetaTwoOptimizerStage.stage,
      RiemannResearch.Analysis.ExhaustiveWalk.walkSpan]
  have he := RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
    (ZetaTwoOptimizerStage.stage 0) (ZetaTwoOptimizerStage.stage n)
    (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono
      ZetaTwoOptimizerStage.squarefreeAtom id (Nat.zero_le n)) qOne
  change ‖qOne - ZetaTwoOptimizerStage.optimizer 0‖ ^ 2 =
    ‖ZetaTwoOptimizerStage.residual n‖ ^ 2 +
      ‖ZetaTwoOptimizerStage.optimizer n - ZetaTwoOptimizerStage.optimizer 0‖ ^ 2 at he
  simpa only [hz, sub_zero, qOne_norm_sq] using he

theorem optimizer_norm_le_one (n : ℕ) : ‖ZetaTwoOptimizerStage.optimizer n‖ ≤ 1 := by
  have he := stage_energy n
  nlinarith [sq_nonneg ‖ZetaTwoOptimizerStage.residual n‖,
    norm_nonneg (ZetaTwoOptimizerStage.optimizer n)]

theorem residual_norm_le_one (n : ℕ) : ‖ZetaTwoOptimizerStage.residual n‖ ≤ 1 := by
  have he := stage_energy n
  nlinarith [sq_nonneg ‖ZetaTwoOptimizerStage.optimizer n‖,
    norm_nonneg (ZetaTwoOptimizerStage.residual n)]

theorem optimizer_charge_tendsto_zero (s : ℕ → ℕ) :
    Tendsto (fun N => charge N (ZetaTwoOptimizerStage.optimizer (s N)))
      atTop (𝓝 0) :=
  charge_moving_tendsto_zero _ 1 (fun N => optimizer_norm_le_one (s N))

theorem residual_charge_tendsto_zero (s : ℕ → ℕ) :
    Tendsto (fun N => charge N (ZetaTwoOptimizerStage.residual (s N)))
      atTop (𝓝 0) :=
  charge_moving_tendsto_zero _ 1 (fun N => residual_norm_le_one (s N))

private theorem mobius_qResidue (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) :
    mobiusDifferenceCLM n (toPareto (qResidue d)) =
      (if n = 1 then 1 / (d : ℝ) else 0) - (if n = d then 1 else 0) := by
  by_cases h1 : n = 1
  · subst n
    rw [mobiusDifferenceCLM_apply, toPareto_sequence, qSequence_qResidue]
    simp [Pareto.mobiusDifference, ArithmeticCumulative.residueFraction,
      Nat.mod_eq_of_lt (show 1 < d by omega), show 1 ≠ d by omega]
  · rw [toPareto_qResidue d (by omega)]
    simp only [Pareto.BaezDuarte.residueVector, dif_pos (show 0 < d by omega)]
    rw [mobius_normalizedResidue n d (by omega)]
    split_ifs <;> norm_num

/-- Exact legal atom evaluation; no squarefree assumption is needed. -/
theorem charge_qResidue (N d : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N) :
    charge N (qResidue d) = (N : ℝ)⁻¹ * (1 - 1 / (d : ℝ)) := by
  rw [charge_eq_sum]
  have hsum : (∑ n ∈ Finset.Icc 1 N,
      (1 - (n : ℝ) / (N : ℝ)) * mobiusDifferenceCLM n (toPareto (qResidue d)) /
        (n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N,
        ((if n = 1 then (1 - 1 / (N : ℝ)) / (d : ℝ) else 0) -
          (if n = d then (1 - (d : ℝ) / (N : ℝ)) / (d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [mobius_qResidue n d (Finset.mem_Icc.mp hn).1 hd]
    by_cases h1 : n = 1
    · subst n
      simp [show 1 ≠ d by omega, div_eq_mul_inv]
    · by_cases hnd : n = d
      · subst n
        simp [show d ≠ 1 by omega]
        ring
      · simp [h1, hnd]
  rw [hsum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc, Nat.le_refl,
    show 1 ≤ N by omega, show 1 ≤ d by omega, hdN, and_self, ite_true]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp [hd0, hN0]
  ring

/-- The collective coefficient direction is evaluated exactly before estimation. -/
theorem charge_finite_sum (N : ℕ) (D : Finset ℕ) (c : ℕ → ℝ)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ N) :
    charge N (∑ d ∈ D, c d • qResidue d) =
      (N : ℝ)⁻¹ * ∑ d ∈ D, c d * (1 - 1 / (d : ℝ)) := by
  unfold charge
  change inner ℝ (triangularChargeRiesz N)
    (toParetoLinear (∑ d ∈ D, c d • qResidue d)) = _
  rw [map_sum, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul, real_inner_smul_right]
  change c d * charge N (qResidue d) = _
  rw [charge_qResidue N d (hD d hd).1 (hD d hd).2]
  ring

/-- Concrete unconditional coefficient bound, valid in particular for squarefree
and primorial divisor dictionaries. It is not a bound on target approximation error. -/
theorem coefficient_direction_sq_le (N : ℕ) (hN : 0 < N)
    (D : Finset ℕ) (c : ℕ → ℝ) (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ N) :
    (∑ d ∈ D, c d * (1 - 1 / (d : ℝ))) ^ 2 ≤
      zetaTwo * (N : ℝ) ^ 2 * reciprocalMobiusCesaroEnergy N *
        ‖∑ d ∈ D, c d • qResidue d‖ ^ 2 := by
  have hb := charge_sq_le N (∑ d ∈ D, c d • qResidue d)
  rw [charge_finite_sum N D c hD, sq_abs, mul_pow] at hb
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (N : ℝ))
  field_simp [hN0] at hm
  nlinarith

end RiemannResearch.RH.QTriangularCharge
