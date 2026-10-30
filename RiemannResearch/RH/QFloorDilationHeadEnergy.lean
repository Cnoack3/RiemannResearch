/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFloorDilationEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ParetoDilation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Exact-head improvement of complete Q floor-dilation energy

Source: the user's full squarefree research handoff of 30 October 2026 and
its request to retain exact signed energy identities. The existing complete
block-defect identity is split into the known head and the entire remaining
tail. No pointwise sign condition on the vector outside its head is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFloorDilation
open ZetaTwoHilbert

/-- The complete sharp-bound defect has a summable weighted square series. -/
theorem qBlockDefectEnergy_summable (p : ℕ) (hp : 0 < p) (f : QHilbert) :
    Summable (fun k => qBlockDefect p k * (qSequence f k) ^ 2) := by
  apply (((qSequence_square_summable f).div_const (p : ℝ)).sub
    (qBlockEnergy_summable p hp f)).congr
  intro k
  unfold qBlockDefect
  ring

theorem qBlockDefectEnergy_nonneg (p : ℕ) (hp : 0 < p) (f : QHilbert) (k : ℕ) :
    0 ≤ qBlockDefect p k * (qSequence f k) ^ 2 := by
  by_cases hk : k = 0
  · simp [hk]
  · exact mul_nonneg (qBlockDefect_nonneg p k hp (Nat.pos_of_ne_zero hk)) (sq_nonneg _)

/-- Explicit, optimizer-independent defect forced by an exact head of ones. -/
def headBlockDefect (p H : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 H, qBlockDefect p k

theorem headBlockDefect_nonneg (p H : ℕ) (hp : 0 < p) :
    0 ≤ headBlockDefect p H := by
  apply Finset.sum_nonneg
  intro k hk
  exact qBlockDefect_nonneg p k hp (by have := (Finset.mem_Icc.mp hk).1; omega)

/-- Every quotient block past the imposed head is retained. -/
def tailBlockDefect (p H : ℕ) (f : QHilbert) : ℝ :=
  ∑' k : ℕ, qBlockDefect p (k + (H + 1)) *
    (qSequence f (k + (H + 1))) ^ 2

theorem tailBlockDefect_nonneg (p H : ℕ) (hp : 0 < p) (f : QHilbert) :
    0 ≤ tailBlockDefect p H f :=
  tsum_nonneg (fun k => qBlockDefectEnergy_nonneg p hp f (k + (H + 1)))

private theorem sum_defect_exact_head (p H : ℕ) (f : QHilbert)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 1) :
    (∑ k ∈ Finset.range (H + 1), qBlockDefect p k * (qSequence f k) ^ 2) =
      headBlockDefect p H := by
  have hr : Finset.range (H + 1) = insert 0 (Finset.Icc 1 H) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp)]
  simp only [qSequence_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hhead k (by have := (Finset.mem_Icc.mp hk).1; omega) (Finset.mem_Icc.mp hk).2]
  simp

/-- Exact head-plus-tail version of the sharp complete-Q norm identity. -/
theorem floorDilation_norm_sq_head_defect (p H : ℕ) (hp : 0 < p) (f : QHilbert)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 1) :
    ‖floorDilation p hp f‖ ^ 2 =
      ‖f‖ ^ 2 / (p : ℝ) - headBlockDefect p H - tailBlockDefect p H f := by
  have hs := Summable.sum_add_tsum_nat_add (H + 1) (qBlockDefectEnergy_summable p hp f)
  rw [sum_defect_exact_head p H f hhead] at hs
  have hd := floorDilation_norm_sq_defect p hp f
  change headBlockDefect p H + tailBlockDefect p H f = _ at hs
  linarith

/-- The known head gives a strictly stronger usable denominator when its defect is positive. -/
theorem floorDilation_norm_sq_le_head (p H : ℕ) (hp : 0 < p) (f : QHilbert)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 1) :
    ‖floorDilation p hp f‖ ^ 2 ≤ ‖f‖ ^ 2 / (p : ℝ) - headBlockDefect p H := by
  rw [floorDilation_norm_sq_head_defect p H hp f hhead]
  exact sub_le_self _ (tailBlockDefect_nonneg p H hp f)

/-- The refined denominator is automatically nonnegative, without a separate energy premise. -/
theorem headAdjustedEnergy_nonneg (p H : ℕ) (hp : 0 < p) (f : QHilbert)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 1) :
    0 ≤ ‖f‖ ^ 2 / (p : ℝ) - headBlockDefect p H :=
  (sq_nonneg _).trans (floorDilation_norm_sq_le_head p H hp f hhead)

end RiemannResearch.RH.QFloorDilation

namespace RiemannResearch.RH.QFloorDilation
open ZetaTwoHilbert

/-- A head containing the first site makes every positive floor dilation nonzero. -/
theorem floorDilation_ne_zero_of_head_one (p : ℕ) (hp : 0 < p) (f : QHilbert)
    (hhead : qSequence f 1 = 1) : floorDilation p hp f ≠ 0 := by
  intro hz
  have hh : qSequence (floorDilation p hp f) p = 1 := by
    simpa only [floorDilation_sequence, Nat.div_self hp] using hhead
  have hzero : qSequence (0 : QHilbert) p = 0 := by
    change qSequenceLinear 0 p = 0
    simp
  rw [hz, hzero] at hh
  norm_num at hh

/-- Thus the refined trial denominator is positive for every nonempty exact head. -/
theorem headAdjustedEnergy_pos (p H : ℕ) (hp : 0 < p) (hH : 0 < H) (f : QHilbert)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 1) :
    0 < ‖f‖ ^ 2 / (p : ℝ) - headBlockDefect p H := by
  have hn := floorDilation_ne_zero_of_head_one p hp f (hhead 1 (by omega) (by omega))
  exact (sq_pos_of_pos (norm_pos_iff.mpr hn)).trans_le
    (floorDilation_norm_sq_le_head p H hp f hhead)

end RiemannResearch.RH.QFloorDilation

namespace RiemannResearch.RH.QFloorDilation
open ZetaTwoHilbert ZetaTwoProbability Pareto
open scoped BigOperators

/-- The existing Pareto comparison gives an explicit lower defect at each site. -/
theorem qBlockDefect_ge_pareto_gap (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    ((positiveQWeight k - positiveWeight k / zetaTwo) -
      (positiveQWeight k - positiveWeight k / zetaTwo) / (p : ℝ)) / (p : ℝ) ≤
        qBlockDefect p k := by
  have h := qBlockWeight_pareto_defect_le p k hp hk
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have he : qBlockDefect p k =
      ((positiveQWeight k - positiveWeight k / zetaTwo) -
        ((p : ℝ) * qBlockWeight p k - positiveWeight k / zetaTwo)) / (p : ℝ) := by
    unfold qBlockDefect
    field_simp [hp0]
    ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- A positive, finite-head-only defect lower bound, free of optimizer tails. -/
theorem headBlockDefect_ge_pareto_gap (p H : ℕ) (hp : 0 < p) :
    ((∑ k ∈ Finset.Icc 1 H, (positiveQWeight k - positiveWeight k / zetaTwo)) -
      (∑ k ∈ Finset.Icc 1 H, (positiveQWeight k - positiveWeight k / zetaTwo)) /
        (p : ℝ)) / (p : ℝ) ≤ headBlockDefect p H := by
  unfold headBlockDefect
  rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  exact qBlockDefect_ge_pareto_gap p k hp (by have := (Finset.mem_Icc.mp hk).1; omega)

end RiemannResearch.RH.QFloorDilation
