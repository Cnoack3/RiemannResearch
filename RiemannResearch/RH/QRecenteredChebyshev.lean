/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDisplacementPolylogHeadMeans
import RiemannResearch.RH.QSquarefreeChebyshevAveraging
import RiemannResearch.RH.QSquarefreeDisplacementEnergy
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic.Module

/-!
# Arithmetic recentering of the Chebyshev displacement iteration
The four-site certificate restricts the compressed reciprocal to [0, 983/2000].
Choose a rational Chebyshev growth factor 119 / 20, whose square exceeds 35.
The polynomial recurrence is the classical semi-iteration of Golub and Varga,
*Chebyshev semi-iterative methods*, I (1961), §2.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeChebyshev.Arithmetic
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeBoundary QSquarefreeDisplacementEnergy QSquarefreeDisplacementRigidity
open QSquarefreeDisplacementResolvent QSquarefreeSmoothedProjection QMeanSquareDisplacement
open RiemannResearch.Analysis.ChebyshevEnergy

/-- The shift is (r+1/r)/2 with r=119 / 20. Taking this rational value
slightly inside the certified interval makes every recurrence rational. -/
def shift : ℝ := 14561 / 4760

def op : QHilbert →L[ℝ] QHilbert :=
  (shift + 1) • (closure.starProjection.comp (B.comp closure.starProjection)) -
    closure.starProjection

theorem op_mem (x : QHilbert) : op x ∈ closure :=
  closure.sub_mem (closure.smul_mem _ (closure.starProjection_apply_mem _))
    (closure.starProjection_apply_mem _)

theorem op_symmetric (x y : QHilbert) :
    inner ℝ (op x) y = inner ℝ x (op y) := by
  have hb : inner ℝ (closure.starProjection (B (closure.starProjection x))) y =
      inner ℝ x (closure.starProjection (B (closure.starProjection y))) := by
    rw [projection_symmetric, B_symmetric, projection_symmetric]
  change inner ℝ ((shift + 1) • closure.starProjection (B (closure.starProjection x)) -
      closure.starProjection x) y =
    inner ℝ x ((shift + 1) • closure.starProjection (B (closure.starProjection y)) -
      closure.starProjection y)
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hb, projection_symmetric]

theorem op_quadratic_bound (x : QHilbert) : |inner ℝ (op x) x| ≤ ‖x‖ ^ 2 := by
  let p := closure.starProjection x
  have hp : p ∈ closure := closure.starProjection_apply_mem x
  have ho := Submodule.inner_right_of_mem_orthogonal hp
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) x)
  rw [inner_sub_right] at ho
  have hpx : inner ℝ p x = ‖p‖ ^ 2 := by
    change inner ℝ p x - inner ℝ p p = 0 at ho
    rw [← real_inner_self_eq_norm_sq]
    exact sub_eq_zero.mp ho
  have hpn : ‖p‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖closure.starProjection‖ * ‖x‖ := closure.starProjection.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le closure) (norm_nonneg x)
      _ = _ := one_mul _
  have hs := mul_self_le_mul_self (norm_nonneg p) hpn
  have hb := B_inner_le_four_site_983_2000 (fourSiteFunctional_zero_on_closure hp)
  have hpos := B_positive p
  have he : inner ℝ (op x) x = (shift + 1) * inner ℝ p (B p) - ‖p‖ ^ 2 := by
    change inner ℝ ((shift + 1) • closure.starProjection (B p) - p) x = _
    rw [inner_sub_left, real_inner_smul_left, projection_symmetric, hpx]
    rw [real_inner_comm (B p) p]
  rw [he, abs_le]
  dsimp [shift]
  constructor <;> nlinarith [sq_nonneg ‖p‖]

theorem op_contracts (x : QHilbert) : ‖op x‖ ≤ ‖x‖ := by
  have hn : ‖op‖ ≤ 1 := by
    have hs : op.IsSymmetric := by
      intro y z
      exact op_symmetric y z
    rw [op.norm_eq_iSup_rayleighQuotient hs]
    apply ciSup_le
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · change |inner ℝ (op y) y / ‖y‖ ^ 2| ≤ 1
      rw [abs_div, abs_of_nonneg (sq_nonneg ‖y‖),
        div_le_one (sq_pos_of_pos (norm_pos_iff.mpr hy))]
      exact op_quadratic_bound y
  calc
    _ ≤ ‖op‖ * ‖x‖ := op.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg x)
    _ = _ := one_mul _

theorem op_displacement : op displacement =
    shift • displacement - (shift + 1) • correction := by
  have hp : closure.starProjection displacement = displacement :=
    Submodule.starProjection_eq_self_iff.mpr displacement_mem
  have hb : closure.starProjection (B displacement) = displacement - correction := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact displacement_fixed_point.symm
  change (shift + 1) • closure.starProjection (B (closure.starProjection displacement)) -
    closure.starProjection displacement = _
  rw [hp, hb]
  module

def denom (j : ℕ) : ℝ := ((119 / 20 : ℝ) ^ j + (20 / 119 : ℝ) ^ j) / 2

theorem denom_pos (j : ℕ) : 0 < denom j := by
  unfold denom
  positivity

theorem denom_step (j : ℕ) : denom (j + 2) = (2 * shift) * denom (j + 1) - denom j := by
  simp only [denom, shift, pow_add, pow_one]
  ring

def num : ℕ → QHilbert
  | 0 => 0
  | 1 => (shift + 1) • correction
  | j + 2 => (2 : ℝ) • op (num (j + 1)) - num j +
      (2 * (shift + 1) * denom (j + 1)) • correction

def iter (j : ℕ) : QHilbert := (denom j)⁻¹ • num j

theorem iter_mem (j : ℕ) : iter j ∈ closure := by
  have hc : correction ∈ closure := closure.starProjection_apply_mem _
  apply closure.smul_mem
  induction j using Nat.twoStepInduction with
  | zero => exact closure.zero_mem
  | one => exact closure.smul_mem _ hc
  | more j ih _ =>
    exact closure.add_mem (closure.sub_mem (closure.smul_mem _ (op_mem _)) ih)
      (closure.smul_mem _ hc)

theorem num_remainder (j : ℕ) :
    denom j • displacement - num j = firstKind op displacement j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [denom, num, firstKind_zero]
  | one =>
    have h : denom 1 = shift := by norm_num [denom, shift]
    simpa only [h, num, firstKind_one] using op_displacement.symm
  | more j ih0 ih1 =>
    rw [firstKind_recurrence, ← ih1, ← ih0]
    simp only [denom_step, num, map_sub, map_smul, op_displacement]
    module

theorem iter_remainder (j : ℕ) :
    displacement - iter j = (denom j)⁻¹ • firstKind op displacement j := by
  rw [← num_remainder j, smul_sub, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (denom_pos j)), one_smul]
  rfl

theorem iter_exact_energy (j : ℕ) :
    (denom j) ^ 2 * ‖displacement - iter j‖ ^ 2 +
      ‖secondKind op displacement j‖ ^ 2 -
      ‖op (secondKind op displacement j)‖ ^ 2 = ‖displacement‖ ^ 2 := by
  rw [iter_remainder, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (denom_pos j))]
  have hne := ne_of_gt (denom_pos j)
  have he := exact_energy op op_symmetric displacement j
  field_simp
  nlinarith

theorem iter_error (j : ℕ) :
    ‖displacement - iter j‖ ≤ ‖displacement‖ / denom j := by
  rw [iter_remainder, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (denom_pos j)), div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (firstKind_norm_le op op_symmetric op_contracts displacement j)
    (inv_nonneg.mpr (denom_pos j).le)

/-- Each head costs at most four times the squared norm of the displacement. -/
theorem head35_error (j : ℕ) :
    ((35 ^ j : ℕ) : ℝ) * ‖displacement - iter j‖ ^ 2 ≤ 4 * ‖displacement‖ ^ 2 := by
  have hb := (le_div_iff₀ (denom_pos j)).mp (iter_error j)
  have hs := mul_self_le_mul_self
    (mul_nonneg (norm_nonneg _) (denom_pos j).le) hb
  have hl : (119 / 20 : ℝ) ^ j ≤ 2 * denom j := by
    unfold denom
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 20 / 119) j]
  have hsq := mul_self_le_mul_self (pow_nonneg (by norm_num : (0 : ℝ) ≤ 119 / 20) j) hl
  have hbase := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 35)
    (by norm_num : (35 : ℝ) ≤ (119 / 20 : ℝ) ^ 2) j
  have heq : ((119 / 20 : ℝ) ^ 2) ^ j = ((119 / 20 : ℝ) ^ j) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm 2 j, pow_mul]
  rw [heq] at hbase
  have hh : ((35 ^ j : ℕ) : ℝ) ≤ 4 * (denom j) ^ 2 := by
    push_cast
    nlinarith
  have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖displacement - iter j‖)
  nlinarith

theorem riemannHypothesis_of_head35_mean_square (C : ℝ) (hC : 0 ≤ C)
    (hmean : ∀ j, headEnergy (35 ^ j) (iter j) ≤ C * ((35 ^ j : ℕ) : ℝ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_geometric_head_means 35 (by norm_num) iter C
    (4 * ‖displacement‖ ^ 2) hC (by positivity) hmean head35_error

/-- On the recentered heads an arbitrary fixed polylogarithmic mean budget suffices. -/
theorem riemannHypothesis_of_head35_polylog_mean_square (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hmean : ∀ j, headEnergy (35 ^ j) (iter j) ≤ C * ((35 ^ j : ℕ) : ℝ) *
      (6 + Real.log ((35 ^ j : ℕ) : ℝ)) ^ (2 * m)) : RiemannHypothesis := by
  refine riemannHypothesis_of_covered_polylog_head_means (fun j => 35 ^ j) iter 35 C
    (4 * ‖displacement‖ ^ 2) m (by norm_num) hC (by positivity) ?_ hmean head35_error
  intro N hN
  obtain ⟨j, hj, hmax⟩ := geometric_head_cover 35 N (by norm_num) hN
  exact ⟨j, hj, by exact_mod_cast hmax⟩

end RiemannResearch.RH.QSquarefreeChebyshev.Arithmetic
