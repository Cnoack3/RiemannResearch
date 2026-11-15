/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullMobiusRepairConductors
import RiemannResearch.RH.QFullReciprocalRepairBudget
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.ReciprocalSquareRootSum
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A fixed-dictionary triangular Möbius right inverse

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 2.
The triangular kernels use the same compensating atom g_(N+1). They reproduce
the physical step functions through N and belong to the dictionary with
conductors at most N+1. Complete Q norms, including all sites above N, satisfy
the stated square-root growth bound. The reciprocal multiplier is R in prose;
its existing implementation is `QShiftedReciprocal.B`, not the density dQ/dP.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFullTriangularMobiusRepair
open ZetaTwoHilbert ZetaTwoProbability QMobiusExactHead QFloorDilation
open QFullDilatedMobiusRepair
open RiemannResearch.Analysis

def triangularStep (N k : ℕ) : QHilbert :=
  -(∑ d ∈ Finset.Icc 1 (N / (k + 1)),
    (ArithmeticFunction.moebius d : ℝ) • qResidue ((k + 1) * d)) +
  ((((N + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
    Pareto.mobiusReciprocalSum (N / (k + 1))) • qResidue (N + 1)

theorem triangularStep_sequence (N k n : ℕ) :
    qSequence (triangularStep N k) n =
      -(∑ d ∈ Finset.Icc 1 (N / (k + 1)),
        (ArithmeticFunction.moebius d : ℝ) * qSequence (qResidue ((k + 1) * d)) n) +
      ((((N + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        Pareto.mobiusReciprocalSum (N / (k + 1))) * qSequence (qResidue (N + 1)) n := by
  change qSequenceLinear (_ + _) n = _
  simp only [map_add, map_neg, map_sum, map_smul,
    Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- The different compensating atom changes no requested physical head coordinate. -/
theorem triangularStep_head (N k n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (triangularStep N k) n = if k < n then 1 else 0 := by
  have hhigh : N < (k + 1) * (N / (k + 1) + 1) := by
    have hmod := Nat.mod_lt N (Nat.succ_pos k)
    have heq := Nat.mod_add_div N (k + 1)
    nlinarith
  have hmR : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hrR : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hdR : (((k + 1) * (N / (k + 1) + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hcomp :
      ((((N + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        Pareto.mobiusReciprocalSum (N / (k + 1))) * qSequence (qResidue (N + 1)) n =
      (((N / (k + 1) + 1 : ℕ) : ℝ) *
        Pareto.mobiusReciprocalSum (N / (k + 1))) *
          qSequence (qResidue ((k + 1) * (N / (k + 1) + 1))) n := by
    rw [qSequence_qResidue, qSequence_qResidue]
    unfold ArithmeticCumulative.residueFraction
    rw [Nat.mod_eq_of_lt (by omega : n < N + 1),
      Nat.mod_eq_of_lt (hnN.trans_lt hhigh)]
    push_cast
    field_simp [hmR, hrR, hdR]
    <;> ring
  calc
    qSequence (triangularStep N k) n = qSequence (dilatedMobiusStep N k) n := by
      rw [triangularStep_sequence, hcomp, dilatedMobiusStep, floorDilation_exactHead_atoms]
      change _ = qSequenceLinear (_ + _) n
      simp only [map_add, map_neg, map_sum, map_smul, Pi.add_apply, Pi.neg_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    _ = _ := dilatedMobiusStep_head N k n hn hnN

theorem triangularStep_mem_bounded_span (N k : ℕ) :
    triangularStep N k ∈ Submodule.span ℝ (qResidue '' Set.Icc 1 (N + 1)) := by
  unfold triangularStep
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    apply Submodule.smul_mem
    apply Submodule.subset_span
    apply Set.mem_image_of_mem
    exact ⟨Nat.mul_pos (Nat.succ_pos k) (Finset.mem_Icc.mp hd).1,
      (dilatedMobiusStep_main_conductor_le N k d (Finset.mem_Icc.mp hd).2).trans
        (Nat.le_succ N)⟩
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_image_of_mem _ ⟨Nat.succ_pos N, le_rfl⟩

def triangularRepair (N : ℕ) (u : ℕ → ℝ) : QHilbert :=
  ∑ k ∈ Finset.range N, (u (k + 1) - u k) • triangularStep N k

theorem triangularRepair_mem_bounded_span (N : ℕ) (u : ℕ → ℝ) :
    triangularRepair N u ∈ Submodule.span ℝ (qResidue '' Set.Icc 1 (N + 1)) := by
  unfold triangularRepair
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (triangularStep_mem_bounded_span N k)

theorem triangularRepair_mem_legalSpan (N : ℕ) (u : ℕ → ℝ) :
    triangularRepair N u ∈ QFullResidueProjection.legalSpan := by
  have hle : Submodule.span ℝ (qResidue '' Set.Icc 1 (N + 1)) ≤
      QFullResidueProjection.legalSpan := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    exact QFloorDilation.qResidue_mem_legalSpan d hd.1
  exact hle (triangularRepair_mem_bounded_span N u)

theorem triangularRepair_head (N : ℕ) (u : ℕ → ℝ) (hu : u 0 = 0)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (triangularRepair N u) n = u n := by
  classical
  change qSequenceLinear (∑ k ∈ Finset.range N,
    (u (k + 1) - u k) • triangularStep N k) n = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ k ∈ Finset.range N,
    (u (k + 1) - u k) * qSequence (triangularStep N k) n) = u n
  simp_rw [triangularStep_head N _ n hn hnN]
  simp only [mul_ite, mul_one, mul_zero]
  have hfilter : (Finset.range N).filter (fun k => k < n) = Finset.range n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]
  have htel : ∀ m, (∑ k ∈ Finset.range m, (u (k + 1) - u k)) = u m - u 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  simpa only [hu, sub_zero] using htel n

private theorem qResidue_norm_sq_le_two_div_pos (d : ℕ) (hd : 0 < d) :
    ‖qResidue d‖ ^ 2 ≤ 2 / (zetaTwo * (d : ℝ)) := by
  by_cases h1 : d = 1
  · subst d
    simp only [qResidue_one, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact div_nonneg (by norm_num) (mul_nonneg zetaTwo_pos.le (Nat.cast_nonneg _))
  · exact qResidue_norm_sq_le_two_div d (by omega)

private theorem atom_norm_le_factor (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    ‖qResidue (m * d)‖ ≤ Real.sqrt (2 / (zetaTwo * (m : ℝ))) /
      Real.sqrt (d : ℝ) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hZ := zetaTwo_pos
  have hsq : (Real.sqrt (2 / (zetaTwo * (m : ℝ))) / Real.sqrt (d : ℝ)) ^ 2 =
      2 / (zetaTwo * ((m * d : ℕ) : ℝ)) := by
    rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / (zetaTwo * (m : ℝ))),
      Real.sq_sqrt hdR.le]
    push_cast
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hsq]
  exact qResidue_norm_sq_le_two_div_pos _ (Nat.mul_pos hm hd)

private theorem mobius_sum_atom_norm_le (N k : ℕ) :
    ‖∑ d ∈ Finset.Icc 1 (N / (k + 1)),
      (ArithmeticFunction.moebius d : ℝ) • qResidue ((k + 1) * d)‖ ≤
      2 * Real.sqrt (2 * (N : ℝ)) / (Real.sqrt zetaTwo * ((k + 1 : ℕ) : ℝ)) := by
  have hZ := zetaTwo_pos
  have hmR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hM : 0 ≤ ((N / (k + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul : ((N / (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (show (N / (k + 1)) * (k + 1) ≤ N by
      simpa only [Nat.mul_comm] using Nat.mul_div_le N (k + 1))
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / (k + 1)),
        |(ArithmeticFunction.moebius d : ℝ)| * ‖qResidue ((k + 1) * d)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le
        (Finset.Icc 1 (N / (k + 1)))
        (fun d => (ArithmeticFunction.moebius d : ℝ) • qResidue ((k + 1) * d))
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / (k + 1)),
        Real.sqrt (2 / (zetaTwo * ((k + 1 : ℕ) : ℝ))) / Real.sqrt (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hnorm := atom_norm_le_factor (k + 1) d
        (Nat.succ_pos k) (Finset.mem_Icc.mp hd).1
      exact (mul_le_mul_of_nonneg_right hmu (norm_nonneg _)).trans
        (by simpa only [one_mul] using hnorm)
    _ = Real.sqrt (2 / (zetaTwo * ((k + 1 : ℕ) : ℝ))) *
        (∑ d ∈ Finset.Icc 1 (N / (k + 1)), 1 / Real.sqrt (d : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ Real.sqrt (2 / (zetaTwo * ((k + 1 : ℕ) : ℝ))) *
        (2 * Real.sqrt ((N / (k + 1) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_sqrt_Icc_le _) (Real.sqrt_nonneg _)
    _ ≤ _ := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      simp only [mul_pow, div_pow,
        Real.sq_sqrt (by positivity : 0 ≤ 2 / (zetaTwo * ((k + 1 : ℕ) : ℝ))),
        Real.sq_sqrt hM, Real.sq_sqrt hZ.le,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * (N : ℝ))]
      rw [show (2 / (zetaTwo * ((k + 1 : ℕ) : ℝ))) *
          (2 ^ 2 * ((N / (k + 1) : ℕ) : ℝ)) =
          8 * ((N / (k + 1) : ℕ) : ℝ) / (zetaTwo * ((k + 1 : ℕ) : ℝ)) by ring,
        show (2 ^ 2 * (2 * (N : ℝ))) /
          (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2) =
          8 * (N : ℝ) / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2) by ring]
      apply (div_le_div_iff₀ (mul_pos hZ hmR) (mul_pos hZ (sq_pos_of_pos hmR))).mpr
      nlinarith [mul_le_mul_of_nonneg_left hmul
        (by positivity : 0 ≤ 8 * zetaTwo * ((k + 1 : ℕ) : ℝ))]

private theorem triangular_compensator_norm_le (N k : ℕ) :
    ‖((((N + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
      Pareto.mobiusReciprocalSum (N / (k + 1))) • qResidue (N + 1)‖ ≤
      Real.sqrt (2 * ((N + 1 : ℕ) : ℝ)) /
        (Real.sqrt zetaTwo * ((k + 1 : ℕ) : ℝ)) := by
  have hZ := zetaTwo_pos
  have hmR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hrR : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hmu : |Pareto.mobiusReciprocalSum (N / (k + 1))| ≤ 1 := by
    by_cases hM : N / (k + 1) = 0
    · simp [hM, Pareto.mobiusReciprocalSum]
    · exact Pareto.mobiusReciprocalSum_abs_le_one _ (Nat.pos_of_ne_zero hM)
  calc
    _ = ((((N + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        |Pareto.mobiusReciprocalSum (N / (k + 1))|) * ‖qResidue (N + 1)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (((N + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        Real.sqrt (2 / (zetaTwo * ((N + 1 : ℕ) : ℝ))) := by
      have hnorm := Real.le_sqrt_of_sq_le
        (qResidue_norm_sq_le_two_div_pos (N + 1) (Nat.succ_pos N))
      have hh := mul_le_mul_of_nonneg_left hmu
        (show 0 ≤ ((N + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) by positivity)
      simpa only [mul_one] using mul_le_mul hh hnorm (norm_nonneg _) (by positivity)
    _ = _ := by
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      simp only [mul_pow, div_pow, Real.sq_sqrt (by positivity :
        0 ≤ 2 / (zetaTwo * ((N + 1 : ℕ) : ℝ))),
        Real.sq_sqrt hZ.le,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * ((N + 1 : ℕ) : ℝ))]
      field_simp [hZ.ne', hmR.ne', hrR.ne']
      <;> ring

def growthConstant (N : ℕ) : ℝ :=
  2 * Real.sqrt (2 * (N : ℝ)) + Real.sqrt (2 * ((N + 1 : ℕ) : ℝ))

theorem growthConstant_nonneg (N : ℕ) : 0 ≤ growthConstant N := by
  unfold growthConstant
  positivity

theorem triangularStep_norm_le (N k : ℕ) :
    ‖triangularStep N k‖ ≤
      growthConstant N / (Real.sqrt zetaTwo * ((k + 1 : ℕ) : ℝ)) := by
  unfold triangularStep growthConstant
  calc
    _ ≤ ‖-(∑ d ∈ Finset.Icc 1 (N / (k + 1)),
          (ArithmeticFunction.moebius d : ℝ) • qResidue ((k + 1) * d))‖ +
        ‖((((N + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
          Pareto.mobiusReciprocalSum (N / (k + 1))) • qResidue (N + 1)‖ := norm_add_le _ _
    _ ≤ 2 * Real.sqrt (2 * (N : ℝ)) /
          (Real.sqrt zetaTwo * ((k + 1 : ℕ) : ℝ)) +
        Real.sqrt (2 * ((N + 1 : ℕ) : ℝ)) /
          (Real.sqrt zetaTwo * ((k + 1 : ℕ) : ℝ)) := by
      rw [norm_neg]
      exact add_le_add (mobius_sum_atom_norm_le N k) (triangular_compensator_norm_le N k)
    _ = _ := by ring

private theorem reciprocal_square_sum_le_zetaTwo (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 / ((k + 1 : ℕ) : ℝ)) ^ 2) ≤ zetaTwo := by
  have hs := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have h := hs.sum_le_tsum (Finset.range (N + 1)) (fun n _ => by positivity)
  rw [Finset.sum_range_succ', ← zetaTwo_eq_nat_sum] at h
  simpa only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), div_zero, add_zero,
    div_pow, one_pow] using h

theorem triangularRepair_norm_le (N : ℕ) (u : ℕ → ℝ) :
    ‖triangularRepair N u‖ ≤ growthConstant N *
      Real.sqrt (∑ k ∈ Finset.range N, (u (k + 1) - u k) ^ 2) := by
  have hZ := zetaTwo_pos
  have hsZ : 0 < Real.sqrt zetaTwo := Real.sqrt_pos.mpr hZ
  let E := ∑ k ∈ Finset.range N, (u (k + 1) - u k) ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun k => |u (k + 1) - u k|) (fun k => 1 / ((k + 1 : ℕ) : ℝ))
  simp only [sq_abs] at hCS
  have hweighted : (∑ k ∈ Finset.range N,
      |u (k + 1) - u k| / ((k + 1 : ℕ) : ℝ)) ≤ Real.sqrt zetaTwo * Real.sqrt E := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun k _ => by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hZ.le, Real.sq_sqrt hE]
    have hrecip := reciprocal_square_sum_le_zetaTwo N
    have hmul := mul_le_mul_of_nonneg_left hrecip hE
    have heq : (∑ k ∈ Finset.range N,
        |u (k + 1) - u k| * (1 / ((k + 1 : ℕ) : ℝ))) =
        ∑ k ∈ Finset.range N, |u (k + 1) - u k| / ((k + 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [heq] at hCS
    exact hCS.trans (by simpa only [mul_comm] using hmul)
  calc
    ‖triangularRepair N u‖ ≤
        ∑ k ∈ Finset.range N, |u (k + 1) - u k| * ‖triangularStep N k‖ := by
      simpa only [triangularRepair, norm_smul, Real.norm_eq_abs] using
        norm_sum_le (Finset.range N) (fun k => (u (k + 1) - u k) • triangularStep N k)
    _ ≤ ∑ k ∈ Finset.range N, |u (k + 1) - u k| *
        (growthConstant N / (Real.sqrt zetaTwo * ((k + 1 : ℕ) : ℝ))) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
        (triangularStep_norm_le N k) (abs_nonneg _)
    _ = (growthConstant N / Real.sqrt zetaTwo) *
        (∑ k ∈ Finset.range N, |u (k + 1) - u k| / ((k + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (growthConstant N / Real.sqrt zetaTwo) *
        (Real.sqrt zetaTwo * Real.sqrt E) :=
      mul_le_mul_of_nonneg_left hweighted (div_nonneg (growthConstant_nonneg N) hsZ.le)
    _ = _ := by dsimp only [E]; field_simp [hsZ.ne']

/-- The explicit fixed-dictionary repair of the reciprocal target. -/
def triangularReciprocalRepair (N : ℕ) (f : QHilbert) : QHilbert :=
  triangularRepair N (qSequence (QShiftedReciprocal.B f))

theorem triangularReciprocalRepair_mem (N : ℕ) (f : QHilbert) :
    triangularReciprocalRepair N f ∈ QFullResidueProjection.legalSpan :=
  triangularRepair_mem_legalSpan N _

theorem triangularReciprocalRepair_physical_head (N : ℕ) (f : QHilbert)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (triangularReciprocalRepair N f) n =
      qSequence (QShiftedReciprocal.B f) n :=
  triangularRepair_head N _ (qSequence_zero _) n hn hnN

theorem triangularReciprocalRepair_head (N : ℕ) (f : QHilbert)
    (n : ℕ) (hn : n < N) :
    triangularReciprocalRepair N f n = QShiftedReciprocal.B f n := by
  have hp := triangularReciprocalRepair_physical_head N f (n + 1)
    (Nat.succ_pos n) (by omega)
  simp only [qSequence_succ] at hp
  exact (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))).mp hp

theorem triangularReciprocalRepair_norm_le (N : ℕ) (f : QHilbert) :
    ‖triangularReciprocalRepair N f‖ ≤
      (2 * Real.sqrt zetaTwo * growthConstant N) * ‖f‖ := by
  have hZ := zetaTwo_pos
  have hE : 0 ≤ ∑ k ∈ Finset.range N,
      (qSequence (QShiftedReciprocal.B f) (k + 1) - qSequence (QShiftedReciprocal.B f) k) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsqrt : Real.sqrt (∑ k ∈ Finset.range N,
      (qSequence (QShiftedReciprocal.B f) (k + 1) - qSequence (QShiftedReciprocal.B f) k) ^ 2) ≤
      2 * Real.sqrt zetaTwo * ‖f‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hE, mul_pow, mul_pow, Real.sq_sqrt hZ.le]
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, mul_assoc] using
      reciprocal_forward_difference_square_sum_le f N
  calc
    ‖triangularReciprocalRepair N f‖ ≤ growthConstant N * Real.sqrt
        (∑ k ∈ Finset.range N,
          (qSequence (QShiftedReciprocal.B f) (k + 1) - qSequence (QShiftedReciprocal.B f) k) ^ 2) :=
      triangularRepair_norm_le N _
    _ ≤ growthConstant N * (2 * Real.sqrt zetaTwo * ‖f‖) :=
      mul_le_mul_of_nonneg_left hsqrt (growthConstant_nonneg N)
    _ = _ := by ring

/-- The explicit constant in the paper's reciprocal triangular estimate. -/
theorem triangularReciprocalRepair_norm_le_explicit (N : ℕ) (f : QHilbert) :
    ‖triangularReciprocalRepair N f‖ ≤
      (4 * Real.sqrt (2 * zetaTwo * (N : ℝ)) +
        2 * Real.sqrt (2 * zetaTwo * ((N + 1 : ℕ) : ℝ))) * ‖f‖ := by
  have h := triangularReciprocalRepair_norm_le N f
  have hZ := zetaTwo_pos
  have heq : 2 * Real.sqrt zetaTwo * growthConstant N =
      4 * Real.sqrt (2 * zetaTwo * (N : ℝ)) +
        2 * Real.sqrt (2 * zetaTwo * ((N + 1 : ℕ) : ℝ)) := by
    rw [show 2 * zetaTwo * (N : ℝ) = zetaTwo * (2 * (N : ℝ)) by ring,
      show 2 * zetaTwo * ((N + 1 : ℕ) : ℝ) =
        zetaTwo * (2 * ((N + 1 : ℕ) : ℝ)) by ring,
      Real.sqrt_mul hZ.le, Real.sqrt_mul hZ.le]
    unfold growthConstant
    ring
  simpa only [heq] using h

end RiemannResearch.RH.QFullTriangularMobiusRepair
