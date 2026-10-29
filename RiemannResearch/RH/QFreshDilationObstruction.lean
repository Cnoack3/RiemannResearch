/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.DivisorComponentJumpRow
import RiemannResearch.RH.SmoothHeadBoundaryFlux
import RiemannResearch.RH.ZetaTwoCoordinateDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.FiniteSeedComponentCharge
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.PositiveSeedCone
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.NormNum

/-!
# Finite divisor charges obstruct corrections using new dilation factors

Source: the user's exact-head energy handoff, Section 9.B, 28 October 2026,
for the correction search. The finite charge, its totient jump row, and
its target signal are reused from FiniteSeedComponentCharge,
DivisorComponentJumpRow, and SmoothHeadBoundaryFlux. The dilation
obstruction and Q energy extraction are developed in this continuation.

For fixed L>0, the charge annihilates the old divisor stage and every
floorDilation m of an arbitrary Q vector when m does not divide L.
Its kernel is closed and excludes an exact head through L. The
period-six specialization has a complete error floor 2/(37*zetaTwo),
with the entire squared-norm remainder retained.

This obstructs a restricted correction space, not the full enlarged
squarefree dictionary. Compensated residues outside the old period
change the charge. No RH conclusion is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFreshDilationObstruction
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets QFloorDilation
open FiniteSeedComponentCharge DivisorComponentJumpRow Pareto

def cutWitness (L : ℕ) : QHilbert :=
  ∑ k ∈ Finset.range L, componentRow L.divisors k • qSiteRiesz (k + 1)

theorem cutWitness_inner (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    inner ℝ (cutWitness L) f = componentCharge L.divisors (qSequence f) := by
  rw [componentCharge_eq_row L.divisors L
    (fun n hn => ⟨Nat.pos_of_mem_divisors hn,
      Nat.le_of_dvd hL (Nat.dvd_of_mem_divisors hn)⟩) _ (qSequence_zero f)]
  simp only [cutWitness, sum_inner, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro k hk
  rw [qSiteRiesz_inner (k + 1) (by omega)]

def cutFunctional (L : ℕ) : QHilbert →L[ℝ] ℝ := innerSL ℝ (cutWitness L)

theorem cutFunctional_apply (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    cutFunctional L f = componentCharge L.divisors (qSequence f) :=
  cutWitness_inner L hL f

private theorem componentCharge_scale (S : Finset ℕ) (c : ℝ) (f : ℕ → ℝ) :
    componentCharge S (fun n => c * f n) = c * componentCharge S f := by
  unfold componentCharge mobiusDifference
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The exact charge of every residue, including conductors outside the old period. -/
theorem cutFunctional_qResidue_value (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    cutFunctional L (qResidue d) = (1 / (d : ℝ)) * (1 - if d ∣ L then 1 else 0) := by
  rw [cutFunctional_apply L hL, qSequence_qResidue]
  have he : ArithmeticCumulative.residueFraction d =
      fun n => (1 / (d : ℝ)) * TwoSeedThreshold.certificateGenerator d 1 n := by
    funext n
    simp [ArithmeticCumulative.residueFraction, TwoSeedThreshold.certificateGenerator,
      Nat.mod_one, div_eq_mul_inv, mul_comm]
  rw [he, componentCharge_scale,
    componentCharge_generator L.divisors d 1
      (fun n hn => Nat.pos_of_mem_divisors hn) hd (by omega)]
  simp [Nat.mem_divisors, ne_of_gt hL]

theorem cutFunctional_qResidue (L d : ℕ) (hL : 0 < L) (hd : d ∣ L) :
    cutFunctional L (qResidue d) = 0 := by
  rw [cutFunctional_qResidue_value L d hL (Nat.pos_of_dvd_of_pos hd hL)]
  simp [hd]

/-- A compensated residue outside the old period changes the conserved charge. -/
theorem cutFunctional_compensatedResidue (L d : ℕ) (hL : 0 < L) (hd : 0 < d)
    (hnot : ¬d ∣ L) : cutFunctional L (compensatedResidue d L) = 1 / (d : ℝ) := by
  rw [compensatedResidue, map_sub, map_smul,
    cutFunctional_qResidue_value L d hL hd, cutFunctional_qResidue L L hL (dvd_refl L)]
  simp [hnot]

theorem cutFunctional_divisorStage (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : f ∈ divisorStage L) : cutFunctional L f = 0 := by
  have hle : divisorStage L ≤ (cutFunctional L).ker := by
    apply Submodule.span_le.mpr
    rintro g ⟨d, hd, rfl⟩
    exact cutFunctional_qResidue L d hL hd
  exact hle hf

private theorem quotient_pred_of_not_dvd (m n : ℕ) (hm : 0 < m)
    (hn : 0 < n) (hnot : ¬m ∣ n) : (n - 1) / m = n / m := by
  apply Nat.le_antisymm (Nat.div_le_div_right (Nat.sub_le n 1))
  apply (Nat.le_div_iff_mul_le hm).mpr
  have hr : 0 < n % m := Nat.pos_of_ne_zero (fun h => hnot (Nat.dvd_of_mod_eq_zero h))
  have he := Nat.mod_add_div n m
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  nlinarith

theorem cutFunctional_floorDilation (L m : ℕ) (hL : 0 < L) (hm : 0 < m)
    (hnot : ¬m ∣ L) (f : QHilbert) :
    cutFunctional L (floorDilation m hm f) = 0 := by
  rw [cutFunctional_apply L hL, componentCharge_eq_totient_jumps L hL]
  apply Finset.sum_eq_zero
  intro d hd
  simp only [floorDilation_sequence]
  rw [quotient_pred_of_not_dvd m d hm (Nat.pos_of_mem_divisors hd)
      (fun h => hnot (dvd_trans h (Nat.dvd_of_mem_divisors hd)))]
  ring

theorem cutFunctional_qOne (L : ℕ) (hL : 0 < L) :
    cutFunctional L qOne = (Nat.totient L : ℝ) / L := by
  rw [cutFunctional_apply L hL]
  apply exact_head_divisor_charge L hL _ (qSequence_zero qOne)
  intro k hk hkL
  simp [qSequence_qOne, qOneSequence, ne_of_gt hk]

def freshSpan (L : ℕ) : Submodule ℝ QHilbert :=
  divisorStage L ⊔ Submodule.span ℝ
    {g | ∃ (m : ℕ) (hm : 0 < m) (f : QHilbert),
      ¬m ∣ L ∧ g = floorDilation m hm f}

theorem freshSpan_le_kernel (L : ℕ) (hL : 0 < L) :
    freshSpan L ≤ (cutFunctional L).ker := by
  apply sup_le
  · exact fun f hf => cutFunctional_divisorStage L hL f hf
  · apply Submodule.span_le.mpr
    rintro g ⟨m, hm, f, hnot, rfl⟩
    exact cutFunctional_floorDilation L m hL hm hnot f

theorem closure_freshSpan_le_kernel (L : ℕ) (hL : 0 < L) :
    (freshSpan L).topologicalClosure ≤ (cutFunctional L).ker :=
  (freshSpan L).topologicalClosure_minimal
    (freshSpan_le_kernel L hL) (cutFunctional L).isClosed_ker

theorem freshSpan_no_exact_head (L : ℕ) (hL : 0 < L) (f : QHilbert)
    (hf : f ∈ (freshSpan L).topologicalClosure) :
    ¬∀ n, 0 < n → n ≤ L → qSequence f n = 1 := by
  intro hh
  have hz : cutFunctional L f = 0 := closure_freshSpan_le_kernel L hL hf
  rw [cutFunctional_apply L hL,
    exact_head_divisor_charge L hL _ (qSequence_zero f) hh] at hz
  have hp : 0 < (Nat.totient L : ℝ) / (L : ℝ) :=
    div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hL)) (Nat.cast_pos.mpr hL)
  linarith


theorem cutWitness_ne_zero (L : ℕ) (hL : 0 < L) : cutWitness L ≠ 0 := by
  intro hz
  have he := cutFunctional_qOne L hL
  change inner ℝ (cutWitness L) qOne = _ at he
  rw [hz, inner_zero_left] at he
  have hp : 0 < (Nat.totient L : ℝ) / (L : ℝ) :=
    div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hL)) (Nat.cast_pos.mpr hL)
  linarith

theorem freshSpan_error_exact (L : ℕ) (hL : 0 < L) (f : QHilbert)
    (hf : f ∈ (freshSpan L).topologicalClosure) :
    ‖qOne - f‖ ^ 2 = ((Nat.totient L : ℝ) / L) ^ 2 / ‖cutWitness L‖ ^ 2 +
      ‖qOne - f - (((Nat.totient L : ℝ) / L) / ‖cutWitness L‖ ^ 2) •
        cutWitness L‖ ^ 2 := by
  have hD : ‖cutWitness L‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (cutWitness_ne_zero L hL))
  have hz : cutFunctional L f = 0 := closure_freshSpan_le_kernel L hL hf
  have hi : inner ℝ (qOne - f) (cutWitness L) = (Nat.totient L : ℝ) / L := by
    rw [real_inner_comm]
    change cutFunctional L (qOne - f) = _
    rw [map_sub, cutFunctional_qOne L hL, hz, sub_zero]
  rw [norm_sub_sq_real (qOne - f) _, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi]
  field_simp [hD]
  ring

theorem cutFunctional_six (f : QHilbert) :
    cutFunctional 6 f =
      (qSequence f 2 + qSequence f 3 - qSequence f 5 + qSequence f 6) / 6 := by
  rw [cutFunctional_apply 6 (by decide), componentCharge_eq_totient_jumps 6 (by decide)]
  have ht6 : Nat.totient 6 = 2 := by decide
  have ht3 : Nat.totient 3 = 2 := by decide
  norm_num [show (6 : ℕ).divisors = {1, 2, 3, 6} from by decide,
    Finset.sum_insert, Finset.sum_singleton, ht6, ht3]
  ring

def sixWitness : QHilbert := qSiteRiesz 2 + qSiteRiesz 3 - qSiteRiesz 5 + qSiteRiesz 6

theorem sixWitness_inner (f : QHilbert) :
    inner ℝ sixWitness f =
      qSequence f 2 + qSequence f 3 - qSequence f 5 + qSequence f 6 := by
  simp only [sixWitness, inner_add_left, inner_sub_left,
    qSiteRiesz_inner 2 (by decide), qSiteRiesz_inner 3 (by decide),
    qSiteRiesz_inner 5 (by decide), qSiteRiesz_inner 6 (by decide)]

theorem sixWitness_norm_sq : ‖sixWitness‖ ^ 2 = 74 * zetaTwo := by
  rw [← real_inner_self_eq_norm_sq, sixWitness_inner]
  have ha (x y : QHilbert) (n : ℕ) :
      qSequence (x + y) n = qSequence x n + qSequence y n :=
    congrFun (qSequenceLinear.map_add x y) n
  have hs (x y : QHilbert) (n : ℕ) :
      qSequence (x - y) n = qSequence x n - qSequence y n :=
    congrFun (qSequenceLinear.map_sub x y) n
  simp only [sixWitness, ha, hs, qSequence_qSiteRiesz 2 (by decide),
    qSequence_qSiteRiesz 3 (by decide), qSequence_qSiteRiesz 5 (by decide),
    qSequence_qSiteRiesz 6 (by decide)]
  norm_num [positiveQWeight]
  ring

theorem freshSpan_six_error_exact (f : QHilbert)
    (hf : f ∈ (freshSpan 6).topologicalClosure) :
    ‖qOne - f‖ ^ 2 = 2 / (37 * zetaTwo) +
      ‖qOne - f - (1 / (37 * zetaTwo)) • sixWitness‖ ^ 2 := by
  have hz : cutFunctional 6 f = 0 := closure_freshSpan_le_kernel 6 (by decide) hf
  rw [cutFunctional_six, div_eq_zero_iff] at hz
  have hz' := hz.resolve_right (by norm_num)
  have hi : inner ℝ (qOne - f) sixWitness = 2 := by
    rw [real_inner_comm, inner_sub_right, sixWitness_inner, sixWitness_inner, hz']
    rw [qSequence_qOne]
    norm_num [qOneSequence]
  rw [norm_sub_sq_real (qOne - f) _, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, sixWitness_norm_sq]
  field_simp [ne_of_gt zetaTwo_pos]
  ring

theorem freshSpan_six_error_lower (f : QHilbert)
    (hf : f ∈ (freshSpan 6).topologicalClosure) :
    2 / (37 * zetaTwo) ≤ ‖qOne - f‖ ^ 2 := by
  rw [freshSpan_six_error_exact f hf]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.QFreshDilationObstruction
