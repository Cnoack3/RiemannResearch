/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FiniteHilbertNormalUniqueness
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSmoothedResidueAsymptotic
import Mathlib.Tactic.Linarith
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Signed finite normal equations for the actual squarefree correction

Source: user-provided measure-change regularity handoff, A1 and A3.
All matrices use the masked dictionary, including zero columns. Solutions
exist and their synthesized vectors are unique without any inverse assumption.
The signed forcing and full Schur subtraction are kept intact.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeSignedNormal
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeSmoothedProjection QSquarefreeCorrectionKernel
open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis.ResidualizedProjectionKernel

def synthesis (N : ℕ) (c : Fin N → ℝ) : QHilbert :=
  finiteSchurCombination (fun i : Fin N => squarefreeAtom i) c

def gram (N : ℕ) (i j : Fin N) : ℝ := inner ℝ (squarefreeAtom i) (squarefreeAtom j)
def moment (N : ℕ) (i : Fin N) : ℝ := inner ℝ (squarefreeAtom i) qOne
def shiftedGram (N : ℕ) (i j : Fin N) : ℝ :=
  inner ℝ (squarefreeAtom i) (B (squarefreeAtom j))
def shiftedMoment (N : ℕ) (i : Fin N) : ℝ := inner ℝ (squarefreeAtom i) (B qOne)
def twiceShiftedGram (N : ℕ) (i j : Fin N) : ℝ :=
  inner ℝ (B (squarefreeAtom i)) (B (squarefreeAtom j))

def Normal (N : ℕ) (y : QHilbert) (c : Fin N → ℝ) : Prop :=
  ∀ i, ∑ j, gram N i j * c j = inner ℝ (squarefreeAtom i) y

def forcing (N : ℕ) (c : Fin N → ℝ) (i : Fin N) : ℝ :=
  shiftedMoment N i - ∑ j, shiftedGram N i j * c j

theorem synthesis_inner (N : ℕ) (c : Fin N → ℝ) (i : Fin N) :
    inner ℝ (squarefreeAtom i) (synthesis N c) = ∑ j, gram N i j * c j := by
  simp [synthesis, finiteSchurCombination, inner_sum, real_inner_smul_right,
    gram, mul_comm]

theorem synthesis_B_inner (N : ℕ) (c : Fin N → ℝ) (i : Fin N) :
    inner ℝ (squarefreeAtom i) (B (synthesis N c)) =
      ∑ j, shiftedGram N i j * c j := by
  simp [synthesis, finiteSchurCombination, map_sum, map_smul, inner_sum,
    real_inner_smul_right, shiftedGram, mul_comm]

theorem normal_inner {N : ℕ} {y : QHilbert} {c : Fin N → ℝ}
    (hc : Normal N y c) (i : Fin N) :
    inner ℝ (squarefreeAtom i) (synthesis N c) = inner ℝ (squarefreeAtom i) y := by
  rw [synthesis_inner]
  exact hc i

theorem exists_projection_coefficients (N : ℕ) (y : QHilbert) :
    ∃ c : Fin N → ℝ, synthesis N c = (stage N).starProjection y ∧ Normal N y c := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    ((stage N).starProjection_apply_mem y)
  have hs : synthesis N c = (stage N).starProjection y := hc
  refine ⟨c, hs, ?_⟩
  intro i
  have hi : squarefreeAtom i ∈ stage N := Submodule.subset_span ⟨i, rfl⟩
  have ho := ((stage N).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal y) _ hi
  rw [inner_sub_right] at ho
  rw [← synthesis_inner, hs]
  exact (sub_eq_zero.mp ho).symm

theorem synthesis_eq_projection {N : ℕ} {y : QHilbert} {c : Fin N → ℝ}
    (hc : Normal N y c) : synthesis N c = (stage N).starProjection y := by
  obtain ⟨d, hd, hdn⟩ := exists_projection_coefficients N y
  rw [← hd]
  exact finiteSchurCombination_eq_of_normal y (fun i : Fin N => squarefreeAtom i)
    c d (normal_inner hc) (normal_inner hdn)

theorem synthesis_choice_independent {N : ℕ} {y : QHilbert} {c d : Fin N → ℝ}
    (hc : Normal N y c) (hd : Normal N y d) : synthesis N c = synthesis N d := by
  rw [synthesis_eq_projection hc, synthesis_eq_projection hd]

theorem synthesis_eq_optimizer {N : ℕ} {c : Fin N → ℝ}
    (hc : Normal N qOne c) : synthesis N c = optimizer N := synthesis_eq_projection hc

theorem forcing_eq {N : ℕ} {c : Fin N → ℝ}
    (hc : Normal N qOne c) (i : Fin N) :
    forcing N c i = inner ℝ (squarefreeAtom i) (B (residual N)) := by
  rw [forcing, ← synthesis_B_inner, synthesis_eq_optimizer hc]
  simp only [ZetaTwoOptimizerStage.residual, map_sub, inner_sub_right, shiftedMoment]

theorem forcing_choice_independent {N : ℕ} {c d : Fin N → ℝ}
    (hc : Normal N qOne c) (hd : Normal N qOne d) : forcing N c = forcing N d := by
  funext i
  rw [forcing_eq hc, forcing_eq hd]

theorem correction_synthesis {N : ℕ} {c a : Fin N → ℝ}
    (hc : Normal N qOne c)
    (ha : ∀ i, ∑ j, gram N i j * a j = forcing N c i) :
    synthesis N a = movingCorrection N := by
  apply synthesis_eq_projection
  intro i
  rw [ha i, forcing_eq hc]

/-- Solvable masked systems Gc=m and Gα=h−Hc, with identified syntheses. -/
theorem exists_signed_system (N : ℕ) :
    ∃ c a : Fin N → ℝ,
      Normal N qOne c ∧
      (∀ i, ∑ j, gram N i j * a j = forcing N c i) ∧
      synthesis N c = optimizer N ∧ synthesis N a = movingCorrection N := by
  obtain ⟨c, hc, hcn⟩ := exists_projection_coefficients N qOne
  obtain ⟨a, ha, han⟩ := exists_projection_coefficients N (B (residual N))
  refine ⟨c, a, hcn, ?_, hc, ha⟩
  intro i
  rw [forcing_eq hcn]
  exact han i

theorem synthesis_physical (N : ℕ) (c : Fin N → ℝ) (n : ℕ) :
    qSequence (synthesis N c) n = ∑ i, c i * qSequence (squarefreeAtom i) n := by
  rw [← inner_evaluation]
  simp [synthesis, finiteSchurCombination, sum_inner, real_inner_smul_left,
    inner_evaluation]

theorem correction_physical {N : ℕ} {c a : Fin N → ℝ}
    (hc : Normal N qOne c)
    (ha : ∀ i, ∑ j, gram N i j * a j = forcing N c i) (n : ℕ) :
    qSequence (movingCorrection N) n = ∑ i, a i * qSequence (squarefreeAtom i) n := by
  rw [← correction_synthesis hc ha]
  exact synthesis_physical N a n

/-- The signed finite sum is the exact arithmetic obligation; no inverse or
coefficient bound is inserted into the reduction. -/
theorem riemannHypothesis_of_signed_normal_head_bound (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ N, ∃ c a : Fin N → ℝ, Normal N qOne c ∧
      (∀ i, ∑ j, gram N i j * a j = forcing N c i) ∧
      ∀ n : ℕ, 0 < n → n ≤ N →
        |∑ i, a i * qSequence (squarefreeAtom i) n| ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_moving_head_bound C hC
  intro N n hn hnN
  obtain ⟨c, a, hc, ha, hbound⟩ := hb N
  rw [correction_physical hc ha]
  exact hbound n hn hnN

theorem kernel_synthesis {N n : ℕ} {x : Fin N → ℝ}
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n) :
    synthesis N x = kernel N n := by
  apply synthesis_eq_projection
  intro i
  rw [inner_evaluation]
  exact hx i

/-- Exact signed scalar xᵀ(h−Hc), independent of all coefficient choices. -/
theorem correction_signed_scalar {N n : ℕ} {c x : Fin N → ℝ}
    (hc : Normal N qOne c)
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n) :
    qSequence (movingCorrection N) n = ∑ i, x i * forcing N c i := by
  calc
    _ = inner ℝ ((stage N).starProjection (B (residual N))) (evaluation n) :=
      (inner_evaluation _ _).symm
    _ = inner ℝ (B (residual N)) (kernel N n) :=
      projection_inner (stage N) _ _
    _ = inner ℝ (synthesis N x) (B (residual N)) := by
      rw [kernel_synthesis hx, real_inner_comm]
    _ = ∑ i, x i * forcing N c i := by
      simp [synthesis, finiteSchurCombination, sum_inner, real_inner_smul_left,
        forcing_eq hc]

theorem error_signed {N : ℕ} {c : Fin N → ℝ} (hc : Normal N qOne c) :
    error N = 1 - ∑ i, c i * moment N i := by
  have h := finiteSchurResidual_norm_sq qOne (fun i : Fin N => squarefreeAtom i)
    c (normal_inner hc)
  change ‖qOne - synthesis N c‖ ^ 2 = _ at h
  rw [synthesis_eq_optimizer hc, qOne_norm_sq] at h
  exact h

theorem synthesis_norm_sq (N : ℕ) (c : Fin N → ℝ) :
    ‖synthesis N c‖ ^ 2 = ∑ i, ∑ j, c i * c j * gram N i j := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [synthesis, finiteSchurCombination, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, gram,
    mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm]

theorem synthesis_B_norm_sq (N : ℕ) (c : Fin N → ℝ) :
    ‖B (synthesis N c)‖ ^ 2 = ∑ i, ∑ j, c i * c j * twiceShiftedGram N i j := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [synthesis, finiteSchurCombination, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, twiceShiftedGram,
    mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm]

theorem kernel_smoothed_synthesis {N n : ℕ} {x z : Fin N → ℝ}
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n)
    (hz : ∀ i, ∑ j, gram N i j * z j = ∑ j, shiftedGram N i j * x j) :
    synthesis N z = (stage N).starProjection (B (kernel N n)) := by
  apply synthesis_eq_projection
  intro i
  rw [hz i, ← synthesis_B_inner, kernel_synthesis hx]

theorem exists_kernel_system (N n : ℕ) :
    ∃ x z : Fin N → ℝ,
      (∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n) ∧
      (∀ i, ∑ j, gram N i j * z j = ∑ j, shiftedGram N i j * x j) := by
  obtain ⟨x, hxs, hxn⟩ := exists_projection_coefficients N (evaluation n)
  have hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n := by
    intro i
    rw [← inner_evaluation]
    exact hxn i
  obtain ⟨z, hzs, hzn⟩ := exists_projection_coefficients N (B (kernel N n))
  refine ⟨x, z, hx, ?_⟩
  intro i
  rw [hzn i, ← kernel_synthesis hx, synthesis_B_inner]

/-- Exact singular-design Schur difference xᵀJx−zᵀGz. -/
theorem kernelEnergy_signed {N n : ℕ} {x z : Fin N → ℝ}
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n)
    (hz : ∀ i, ∑ j, gram N i j * z j = ∑ j, shiftedGram N i j * x j) :
    kernelEnergy N n =
      (∑ i, ∑ j, x i * x j * twiceShiftedGram N i j) -
      (∑ i, ∑ j, z i * z j * gram N i j) := by
  rw [kernelEnergy_exact, ← kernel_smoothed_synthesis hx hz,
    ← kernel_synthesis hx, synthesis_B_norm_sq, synthesis_norm_sq]

theorem signed_scalar_sq_le {N n : ℕ} {c x z : Fin N → ℝ}
    (hc : Normal N qOne c)
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n)
    (hz : ∀ i, ∑ j, gram N i j * z j = ∑ j, shiftedGram N i j * x j) :
    (∑ i, x i * forcing N c i) ^ 2 ≤ (1 - ∑ i, c i * moment N i) *
      ((∑ i, ∑ j, x i * x j * twiceShiftedGram N i j) -
        (∑ i, ∑ j, z i * z j * gram N i j)) := by
  rw [← correction_signed_scalar hc hx, ← error_signed hc,
    ← kernelEnergy_signed hx hz]
  exact movingCorrection_sq_le N n


/-- Exact metric relation for the shifted Gram entries. -/
theorem shiftedGram_metric (N : ℕ) (i j : Fin N) :
    ZetaTwoProbability.zetaTwo * shiftedGram N i j =
      ZetaTwoProbability.zetaTwo * gram N i j -
        inner ℝ (ZetaTwoParetoTransfer.toPareto (squarefreeAtom i))
          (ZetaTwoParetoTransfer.toPareto (squarefreeAtom j)) := by
  have h := pareto_inner_identity (squarefreeAtom i) (squarefreeAtom j)
  dsimp [shiftedGram, gram]
  linarith

theorem shiftedMoment_metric (N : ℕ) (i : Fin N) :
    ZetaTwoProbability.zetaTwo * shiftedMoment N i =
      ZetaTwoProbability.zetaTwo * moment N i -
        inner ℝ (ZetaTwoParetoTransfer.toPareto (squarefreeAtom i))
          (ZetaTwoParetoTransfer.toPareto qOne) := by
  have h := pareto_inner_identity (squarefreeAtom i) qOne
  dsimp [shiftedMoment, moment]
  linarith

/-- The second shifted Gram identity, with both signed metric terms retained.
The middle Q-inner product is the complete shifted-weight Gram entry. -/
theorem twiceShiftedGram_metric (N : ℕ) (i j : Fin N) :
    ZetaTwoProbability.zetaTwo * twiceShiftedGram N i j =
      ZetaTwoProbability.zetaTwo *
        (gram N i j + inner ℝ (squarefreeAtom i - B (squarefreeAtom i))
          (squarefreeAtom j - B (squarefreeAtom j))) -
      2 * inner ℝ (ZetaTwoParetoTransfer.toPareto (squarefreeAtom i))
        (ZetaTwoParetoTransfer.toPareto (squarefreeAtom j)) := by
  have h := pareto_inner_identity (squarefreeAtom i) (squarefreeAtom j)
  dsimp [twiceShiftedGram, gram]
  simp only [inner_sub_left, inner_sub_right, B_symmetric]
  nlinarith

/-- Arithmetic decay of the actual signed squarefree normal forcing. -/
theorem forcing_rank_one_bound {N : ℕ} {c : Fin N → ℝ}
    (hc : Normal N qOne c) (i : Fin N) (hi : Squarefree (i.val + 2)) :
    ZetaTwoProbability.zetaTwo * ((i.val + 2 : ℕ) : ℝ) *
      (((i.val + 2 : ℕ) : ℝ) * forcing N c i -
        inner ℝ (residual N) QSmoothedResidueAsymptotic.leading) ^ 2 ≤ 2 * error N := by
  have he : inner ℝ (squarefreeAtom i) (B (residual N)) =
      inner ℝ (residual N) (B (qResidue (i.val + 2))) := by
    rw [squarefreeAtom, if_pos hi, ← B_symmetric, real_inner_comm]
  rw [forcing_eq hc, he]
  exact QSmoothedResidueAsymptotic.signed_forcing_sq_bound (residual N)
    (i.val + 2) (by omega)

end RiemannResearch.RH.QSquarefreeSignedNormal
