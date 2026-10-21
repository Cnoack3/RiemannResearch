/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParityBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QSquarefreeDilationObstruction
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.PrimePowerTargetMellin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QPrimePowerParityBasis
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
/-!
# Five actual squarefree legal orthonormal directions

Source: user-provided legal Gram–Schmidt research direction, 21 October 2026.
The new directions are normalized innovations of g3, g5 and g6 after constants
and parity. Finite-coordinate witnesses prove nondegeneracy. Exact complete-Q
energy and least-squares identities retain every residual. Membership in the
infinite legal closure for the two logarithmic targets remains open.
-/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace RiemannResearch.RH.QSquarefreeLegalBasis
open ZetaTwoHilbert ZetaTwoParitySignal PrimePowerTarget ArithmeticCumulative

private theorem seq_add (f g : QHilbert) (n : ℕ) :
    qSequence (f + g) n = qSequence f n + qSequence g n := by
  change qSequenceLinear (f + g) n = _
  rw [map_add]
  rfl

private theorem seq_sub (f g : QHilbert) (n : ℕ) :
    qSequence (f - g) n = qSequence f n - qSequence g n := by
  change qSequenceLinear (f - g) n = _
  rw [map_sub]
  rfl

private theorem seq_smul (a : ℝ) (f : QHilbert) (n : ℕ) :
    qSequence (a • f) n = a * qSequence f n := by
  change qSequenceLinear (a • f) n = _
  rw [map_smul]
  rfl

private theorem seq_zero (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by
  change qSequenceLinear (0 : QHilbert) n = 0
  rw [map_zero]
  rfl

def remainder3 : QHilbert := qResidue 3 - parityApproximation (qResidue 3)

theorem remainder3_ne_zero : remainder3 ≠ 0 := by
  intro h
  have h1 := congrArg (fun f => qSequence f 1) h
  have h3 := congrArg (fun f => qSequence f 3) h
  simp only [remainder3, parityApproximation, parityUnit, parityCentered,
    seq_sub, seq_add, seq_smul, qSequence_qResidue, qSequence_qOne,
    qSequence_qEven, seq_zero] at h1 h3
  norm_num [qOneSequence, residueFraction] at h1 h3
  linarith

def unit3 : QHilbert := ‖remainder3‖⁻¹ • remainder3

theorem remainder3_inner_one : inner ℝ remainder3 qOne = 0 := by
  simp only [remainder3, parityApproximation, inner_sub_left, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, qOne_norm_sq,
    parityUnit_inner_one, mul_one, mul_zero, add_zero, sub_self]

theorem remainder3_inner_parity : inner ℝ remainder3 parityUnit = 0 := by
  have h : inner ℝ qOne parityUnit = 0 := by
    rw [real_inner_comm, parityUnit_inner_one]
  simp only [remainder3, parityApproximation, inner_sub_left, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, parityUnit_norm_sq,
    h, mul_one, mul_zero, zero_add, sub_self]

theorem unit3_norm : ‖unit3‖ = 1 := by
  rw [unit3, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr remainder3_ne_zero)]

theorem unit3_inner_one : inner ℝ unit3 qOne = 0 := by
  simp [unit3, real_inner_smul_left, remainder3_inner_one]

theorem unit3_inner_parity : inner ℝ unit3 parityUnit = 0 := by
  simp [unit3, real_inner_smul_left, remainder3_inner_parity]

theorem inner_unit3 (f : QHilbert) :
    inner ℝ f unit3 =
      (inner ℝ f (qResidue 3) -
        inner ℝ (qResidue 3) qOne * inner ℝ f qOne -
        inner ℝ (qResidue 3) parityUnit * inner ℝ f parityUnit) / ‖remainder3‖ := by
  simp only [unit3, remainder3, parityApproximation, inner_sub_right,
    inner_add_right, real_inner_smul_right]
  ring

theorem one_inner_unit3 : inner ℝ qOne unit3 = 0 := by
  rw [real_inner_comm, unit3_inner_one]

theorem parity_inner_unit3 : inner ℝ parityUnit unit3 = 0 := by
  rw [real_inner_comm, unit3_inner_parity]

def approximation3 (f : QHilbert) : QHilbert :=
  parityApproximation f + (inner ℝ f unit3) • unit3

def remainder5 : QHilbert := qResidue 5 - approximation3 (qResidue 5)

theorem remainder5_ne_zero : remainder5 ≠ 0 := by
  intro h
  have h1 := congrArg (fun f => qSequence f 1) h
  have h7 := congrArg (fun f => qSequence f 7) h
  simp only [remainder5, approximation3, unit3, remainder3,
    parityApproximation, parityUnit, parityCentered, seq_sub, seq_add, seq_smul,
    qSequence_qResidue, qSequence_qOne, qSequence_qEven, seq_zero] at h1 h7
  norm_num [qOneSequence, residueFraction] at h1 h7
  linarith

def unit5 : QHilbert := ‖remainder5‖⁻¹ • remainder5

private theorem one_inner_parity : inner ℝ qOne parityUnit = 0 := by
  rw [real_inner_comm, parityUnit_inner_one]

theorem remainder5_inner_one : inner ℝ remainder5 qOne = 0 := by
  simp [remainder5, approximation3, parityApproximation, inner_sub_left,
    inner_add_left, real_inner_smul_left, qOne_norm_sq, parityUnit_inner_one, unit3_inner_one]

theorem unit5_inner_one : inner ℝ unit5 qOne = 0 := by
  simp [unit5, real_inner_smul_left, remainder5_inner_one]

theorem one_inner_unit5 : inner ℝ qOne unit5 = 0 := by
  rw [real_inner_comm, unit5_inner_one]

theorem remainder5_inner_parity : inner ℝ remainder5 parityUnit = 0 := by
  simp [remainder5, approximation3, parityApproximation, inner_sub_left,
    inner_add_left, real_inner_smul_left, one_inner_parity, parityUnit_norm_sq, unit3_inner_parity]

theorem unit5_inner_parity : inner ℝ unit5 parityUnit = 0 := by
  simp [unit5, real_inner_smul_left, remainder5_inner_parity]

theorem parity_inner_unit5 : inner ℝ parityUnit unit5 = 0 := by
  rw [real_inner_comm, unit5_inner_parity]

theorem remainder5_inner_unit3 : inner ℝ remainder5 unit3 = 0 := by
  simp [remainder5, approximation3, parityApproximation, inner_sub_left,
    inner_add_left, real_inner_smul_left, one_inner_unit3, parity_inner_unit3, unit3_norm]

theorem unit5_inner_unit3 : inner ℝ unit5 unit3 = 0 := by
  simp [unit5, real_inner_smul_left, remainder5_inner_unit3]

theorem unit3_inner_unit5 : inner ℝ unit3 unit5 = 0 := by
  rw [real_inner_comm, unit5_inner_unit3]

theorem unit5_norm : ‖unit5‖ = 1 := by
  rw [unit5, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr remainder5_ne_zero)]

def approximation5 (f : QHilbert) : QHilbert :=
  approximation3 f + (inner ℝ f unit5) • unit5

def remainder6 : QHilbert := qResidue 6 - approximation5 (qResidue 6)

theorem remainder6_ne_zero : remainder6 ≠ 0 := by
  intro h
  have h1 := congrArg (fun f => qSequence f 1) h
  have h3 := congrArg (fun f => qSequence f 3) h
  have h5 := congrArg (fun f => qSequence f 5) h
  have h7 := congrArg (fun f => qSequence f 7) h
  simp only [remainder6, approximation5, unit5, remainder5, approximation3,
    unit3, remainder3, parityApproximation, parityUnit, parityCentered,
    seq_sub, seq_add, seq_smul, qSequence_qResidue, qSequence_qOne,
    qSequence_qEven, seq_zero] at h1 h3 h5 h7
  norm_num [qOneSequence, residueFraction] at h1 h3 h5 h7
  have hab : (1 : ℝ) = 0 := by
    linear_combination h5 + h3 - h1 - h7
  norm_num at hab

def unit6 : QHilbert := ‖remainder6‖⁻¹ • remainder6

theorem remainder6_inner_one : inner ℝ remainder6 qOne = 0 := by
  simp [remainder6, approximation5, approximation3, parityApproximation, inner_sub_left,
    inner_add_left, real_inner_smul_left, qOne_norm_sq, parityUnit_inner_one, unit3_inner_one,
    unit5_inner_one]

theorem unit6_inner_one : inner ℝ unit6 qOne = 0 := by
  simp [unit6, real_inner_smul_left, remainder6_inner_one]

theorem one_inner_unit6 : inner ℝ qOne unit6 = 0 := by
  rw [real_inner_comm, unit6_inner_one]

theorem remainder6_inner_parity : inner ℝ remainder6 parityUnit = 0 := by
  simp [remainder6, approximation5, approximation3, parityApproximation, inner_sub_left,
    inner_add_left, real_inner_smul_left, one_inner_parity, parityUnit_norm_sq, unit3_inner_parity,
    unit5_inner_parity]

theorem unit6_inner_parity : inner ℝ unit6 parityUnit = 0 := by
  simp [unit6, real_inner_smul_left, remainder6_inner_parity]

theorem parity_inner_unit6 : inner ℝ parityUnit unit6 = 0 := by
  rw [real_inner_comm, unit6_inner_parity]

theorem remainder6_inner_unit3 : inner ℝ remainder6 unit3 = 0 := by
  simp [remainder6, approximation5, approximation3, parityApproximation, inner_sub_left,
    inner_add_left, real_inner_smul_left, one_inner_unit3, parity_inner_unit3, unit3_norm,
    unit5_inner_unit3]

theorem unit6_inner_unit3 : inner ℝ unit6 unit3 = 0 := by
  simp [unit6, real_inner_smul_left, remainder6_inner_unit3]

theorem unit3_inner_unit6 : inner ℝ unit3 unit6 = 0 := by
  rw [real_inner_comm, unit6_inner_unit3]

theorem remainder6_inner_unit5 : inner ℝ remainder6 unit5 = 0 := by
  simp [remainder6, approximation5, approximation3, parityApproximation, inner_sub_left,
    inner_add_left, real_inner_smul_left, one_inner_unit5, parity_inner_unit5, unit3_inner_unit5,
    unit5_norm]

theorem unit6_inner_unit5 : inner ℝ unit6 unit5 = 0 := by
  simp [unit6, real_inner_smul_left, remainder6_inner_unit5]

theorem unit5_inner_unit6 : inner ℝ unit5 unit6 = 0 := by
  rw [real_inner_comm, unit6_inner_unit5]

theorem unit6_norm : ‖unit6‖ = 1 := by
  rw [unit6, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr remainder6_ne_zero)]

def legalFrame : Fin 5 → QHilbert := ![qOne, parityUnit, unit3, unit5, unit6]

theorem legalFrame_orthonormal : Orthonormal ℝ legalFrame := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [legalFrame, qOne_norm_sq, parityUnit_norm_sq, parityUnit_inner_one,
      one_inner_parity, unit3_norm, unit3_inner_one, unit3_inner_parity,
      one_inner_unit3, parity_inner_unit3, unit5_norm, unit5_inner_one,
      unit5_inner_parity, unit5_inner_unit3, one_inner_unit5, parity_inner_unit5,
      unit3_inner_unit5, unit6_norm, unit6_inner_one, unit6_inner_parity,
      unit6_inner_unit3, unit6_inner_unit5, one_inner_unit6, parity_inner_unit6,
      unit3_inner_unit6, unit5_inner_unit6]

theorem qResidue_mem_closureWithConstants (d : ℕ) (hd : 2 ≤ d) (hs : Squarefree d) :
    qResidue d ∈ closureWithConstants := by
  apply closure_le_closureWithConstants
  change qResidue d ∈
    (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨d - 2, ?_⟩
  simp [ZetaTwoOptimizerStage.squarefreeAtom, Nat.sub_add_cancel hd, hs]

theorem unit3_mem_closureWithConstants : unit3 ∈ closureWithConstants :=
  closureWithConstants.smul_mem _ (closureWithConstants.sub_mem
    (qResidue_mem_closureWithConstants 3 (by norm_num) Nat.prime_three.squarefree)
    (parityApproximation_mem_closureWithConstants _))

theorem approximation3_mem (f : QHilbert) : approximation3 f ∈ closureWithConstants :=
  closureWithConstants.add_mem (parityApproximation_mem_closureWithConstants _)
    (closureWithConstants.smul_mem _ unit3_mem_closureWithConstants)

theorem unit5_mem_closureWithConstants : unit5 ∈ closureWithConstants :=
  closureWithConstants.smul_mem _ (closureWithConstants.sub_mem
    (qResidue_mem_closureWithConstants 5 (by norm_num)
      (show Nat.Prime 5 from by norm_num).squarefree) (approximation3_mem _))

theorem approximation5_mem (f : QHilbert) : approximation5 f ∈ closureWithConstants :=
  closureWithConstants.add_mem (approximation3_mem _)
    (closureWithConstants.smul_mem _ unit5_mem_closureWithConstants)

theorem unit6_mem_closureWithConstants : unit6 ∈ closureWithConstants :=
  closureWithConstants.smul_mem _ (closureWithConstants.sub_mem
    (qResidue_mem_closureWithConstants 6 (by norm_num)
      ((Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).2
        ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩)) (approximation5_mem _))

theorem legalFrame_mem (i : Fin 5) : legalFrame i ∈ closureWithConstants := by
  fin_cases i
  · exact qOne_mem_closureWithConstants
  · exact parityUnit_mem_closureWithConstants
  · exact unit3_mem_closureWithConstants
  · exact unit5_mem_closureWithConstants
  · exact unit6_mem_closureWithConstants


def approximation6 (f : QHilbert) : QHilbert :=
  approximation5 f + (inner ℝ f unit6) • unit6

theorem approximation6_mem (f : QHilbert) : approximation6 f ∈ closureWithConstants :=
  closureWithConstants.add_mem (approximation5_mem _)
    (closureWithConstants.smul_mem _ unit6_mem_closureWithConstants)

theorem approximation6_eq_frame_sum (f : QHilbert) :
    approximation6 f = ∑ i : Fin 5, (inner ℝ f (legalFrame i)) • legalFrame i := by
  simp [Fin.sum_univ_succ, legalFrame, approximation6, approximation5,
    approximation3, parityApproximation, add_assoc]

/-- Full complete-Q Pythagoras for the five actual legal directions. -/
theorem approximation6_energy_exact (f : QHilbert) :
    ‖f‖ ^ 2 = (∑ i : Fin 5, (inner ℝ f (legalFrame i)) ^ 2) +
      ‖f - approximation6 f‖ ^ 2 := by
  let c : Fin 5 → ℝ := fun i => inner ℝ f (legalFrame i)
  have hn : ‖∑ i : Fin 5, c i • legalFrame i‖ ^ 2 = ∑ i : Fin 5, c i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, legalFrame_orthonormal.inner_sum c c Finset.univ]
    simp [pow_two]
  have hi : inner ℝ f (∑ i : Fin 5, c i • legalFrame i) = ∑ i : Fin 5, c i ^ 2 := by
    rw [inner_sum]
    simp only [real_inner_smul_right, c, pow_two]
  rw [approximation6_eq_frame_sum]
  change ‖f‖ ^ 2 = (∑ i : Fin 5, c i ^ 2) + ‖f - ∑ i : Fin 5, c i • legalFrame i‖ ^ 2
  rw [norm_sub_sq_real, hn, hi]
  ring

theorem approximation6_captured_le (f : QHilbert) :
    (∑ i : Fin 5, (inner ℝ f (legalFrame i)) ^ 2) ≤ ‖f‖ ^ 2 := by
  have h := approximation6_energy_exact f
  linarith [sq_nonneg ‖f - approximation6 f‖]

/-- An exact finite-period certificate; it does not concern the infinite closure. -/
theorem approximation6_same_at_one_thirtyone (f : QHilbert) :
    qSequence (approximation6 f) 1 = qSequence (approximation6 f) 31 := by
  simp only [approximation6, unit6, remainder6, approximation5,
    unit5, remainder5, approximation3, unit3, remainder3, parityApproximation,
    parityUnit, parityCentered, seq_sub, seq_add, seq_smul,
    qSequence_qResidue, qSequence_qOne, qSequence_qEven]
  norm_num [qOneSequence, residueFraction]

theorem remainder6_ne_zero_of_endpoints (f : QHilbert)
    (h : qSequence f 1 ≠ qSequence f 31) : f - approximation6 f ≠ 0 := by
  intro he
  apply h
  have hf := sub_eq_zero.mp he
  rw [hf]
  exact approximation6_same_at_one_thirtyone f

theorem qTarget_two_remainder6_ne_zero :
    qTarget 2 (by norm_num) - approximation6 (qTarget 2 (by norm_num)) ≠ 0 := by
  apply remainder6_ne_zero_of_endpoints
  rw [qTarget_sequence]
  norm_num [show Nat.log 2 1 = 0 from by decide, show Nat.log 2 31 = 4 from by decide]

theorem qTarget_three_remainder6_ne_zero :
    qTarget 3 (by norm_num) - approximation6 (qTarget 3 (by norm_num)) ≠ 0 := by
  apply remainder6_ne_zero_of_endpoints
  rw [qTarget_sequence]
  norm_num [show Nat.log 3 1 = 0 from by decide, show Nat.log 3 31 = 3 from by decide]


theorem inner_unit5 (f : QHilbert) :
    inner ℝ f unit5 =
      (inner ℝ f (qResidue 5) -
        inner ℝ (qResidue 5) qOne * inner ℝ f qOne -
        inner ℝ (qResidue 5) parityUnit * inner ℝ f parityUnit -
        inner ℝ (qResidue 5) unit3 * inner ℝ f unit3) / ‖remainder5‖ := by
  simp only [unit5, remainder5, approximation3, parityApproximation, inner_sub_right,
    inner_add_right, real_inner_smul_right]
  ring

theorem inner_unit6 (f : QHilbert) :
    inner ℝ f unit6 =
      (inner ℝ f (qResidue 6) -
        inner ℝ (qResidue 6) qOne * inner ℝ f qOne -
        inner ℝ (qResidue 6) parityUnit * inner ℝ f parityUnit -
        inner ℝ (qResidue 6) unit3 * inner ℝ f unit3 -
        inner ℝ (qResidue 6) unit5 * inner ℝ f unit5) / ‖remainder6‖ := by
  simp only [unit6, remainder6, approximation5, approximation3, parityApproximation,
    inner_sub_right, inner_add_right, real_inner_smul_right]
  ring

/-- Exact least-squares gap within the actual five-dimensional legal space. -/
theorem finite_error_energy_exact (f : QHilbert) (c : Fin 5 → ℝ) :
    ‖f - ∑ i : Fin 5, c i • legalFrame i‖ ^ 2 =
      ‖f - approximation6 f‖ ^ 2 +
        ∑ i : Fin 5, (c i - inner ℝ f (legalFrame i)) ^ 2 := by
  have hn : ‖∑ i : Fin 5, c i • legalFrame i‖ ^ 2 = ∑ i : Fin 5, c i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, legalFrame_orthonormal.inner_sum c c Finset.univ]
    simp [pow_two]
  have hi : inner ℝ f (∑ i : Fin 5, c i • legalFrame i) =
      ∑ i : Fin 5, c i * inner ℝ f (legalFrame i) := by
    simp only [inner_sum, real_inner_smul_right]
  have hs : (∑ i : Fin 5, (c i - inner ℝ f (legalFrame i)) ^ 2) =
      (∑ i : Fin 5, c i ^ 2) + (∑ i : Fin 5, (inner ℝ f (legalFrame i)) ^ 2) -
        2 * ∑ i : Fin 5, c i * inner ℝ f (legalFrame i) := by
    calc
      _ = ∑ i : Fin 5, (c i ^ 2 + (inner ℝ f (legalFrame i)) ^ 2 -
          2 * (c i * inner ℝ f (legalFrame i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [norm_sub_sq_real, hn, hi, hs, approximation6_energy_exact f]
  ring

theorem finite_error_minimal (f : QHilbert) (c : Fin 5 → ℝ) :
    ‖f - approximation6 f‖ ^ 2 ≤ ‖f - ∑ i : Fin 5, c i • legalFrame i‖ ^ 2 := by
  rw [finite_error_energy_exact]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end RiemannResearch.RH.QSquarefreeLegalBasis
