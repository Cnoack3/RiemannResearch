/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalCoprimeTail
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Rational surrogate weights and the complete Q metric

Source: user-provided RH/CRT research handoff, 20 October 2026, Section 8.
The midpoint telescoping argument proves the exact proposed majorant. Its
positive remainder is retained before estimating. The reverse comparison
is uniform in both the period and the residual: no coefficient bound or
RH-strength convergence hypothesis is required.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoProbability ZetaTwoHilbert Pareto

def midpointBoundary (L a : ℝ) (j : ℕ) : ℝ :=
  2 / (L * (2 * a + (2 * (j : ℝ) + 1) * L))

def midpointDefect (L x : ℝ) : ℝ :=
  L ^ 2 / (x ^ 2 * (4 * x ^ 2 - L ^ 2))

/-- Exact one-step midpoint identity, retaining its positive defect. -/
theorem midpoint_step_exact {L x : ℝ} (hL : 0 < L) (hx : L < x) :
    1 / x ^ 2 + midpointDefect L x =
      2 / (L * (2 * x - L)) - 2 / (L * (2 * x + L)) := by
  have hx0 : 0 < x := hL.trans hx
  have hm : 0 < 2 * x - L := by linarith
  have hp : 0 < 2 * x + L := by positivity
  have hd : 0 < 4 * x ^ 2 - L ^ 2 := by nlinarith [sq_pos_of_pos hL]
  unfold midpointDefect
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hx0)
  have hxd : x ^ 2 * (4 * x ^ 2 - L ^ 2) ≠ 0 :=
    mul_ne_zero hx2 (ne_of_gt hd)
  have hlm : L * (2 * x - L) ≠ 0 := mul_ne_zero (ne_of_gt hL) (ne_of_gt hm)
  have hlp : L * (2 * x + L) ≠ 0 := mul_ne_zero (ne_of_gt hL) (ne_of_gt hp)
  rw [div_add_div 1 (L ^ 2) hx2 hxd, div_sub_div 2 2 hlm hlp]
  apply (div_eq_div_iff (mul_ne_zero hx2 hxd) (mul_ne_zero hlm hlp)).mpr
  ring

theorem midpointDefect_nonneg {L x : ℝ} (hL : 0 < L) (hx : L < x) :
    0 ≤ midpointDefect L x := by
  have hd : 0 < 4 * x ^ 2 - L ^ 2 := by nlinarith [sq_pos_of_pos hL]
  unfold midpointDefect
  positivity

/-- Exact finite partial sum, including both endpoint and defect remainders. -/
theorem midpoint_partial_exact {L a : ℝ} (hL : 0 < L) (ha : 0 < a)
    (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (a + ((j : ℝ) + 1) * L) ^ 2) +
        midpointBoundary L a N +
        (∑ j ∈ Finset.range N, midpointDefect L (a + ((j : ℝ) + 1) * L)) =
      midpointBoundary L a 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hx : L < a + ((N : ℝ) + 1) * L := by
        have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith
      have hs := midpoint_step_exact hL hx
      have hb : midpointBoundary L a N - midpointBoundary L a (N + 1) =
          2 / (L * (2 * (a + ((N : ℝ) + 1) * L) - L)) -
          2 / (L * (2 * (a + ((N : ℝ) + 1) * L) + L)) := by
        unfold midpointBoundary
        push_cast
        have he1 : 2 * a + (2 * (N : ℝ) + 1) * L =
            2 * (a + ((N : ℝ) + 1) * L) - L := by ring
        have he2 : 2 * a + (2 * ((N : ℝ) + 1) + 1) * L =
            2 * (a + ((N : ℝ) + 1) * L) + L := by ring
        rw [he1, he2]
      rw [← hb] at hs
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

/-- Passing the finite upper bound to the complete arithmetic progression. -/
theorem residueSquareWeight_le_rational {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    zetaTwo * residuePowerWeight 0 L a ≤
      1 / a ^ 2 + 2 / (L * (2 * a + L)) := by
  have hs : Summable (fun j : ℕ => 1 / (a + ((j : ℝ) + 1) * L) ^ 2) := by
    have h := (residuePowerWeight_summable 0 hL (show 0 < a + L by positivity)).mul_left zetaTwo
    exact h.congr (fun j => by
      simp only [Nat.zero_add]
      rw [show a + L + (j : ℝ) * L = a + ((j : ℝ) + 1) * L by ring]
      field_simp [ne_of_gt zetaTwo_pos])
  have hbound (N : ℕ) :
      (∑ j ∈ Finset.range N, 1 / (a + ((j : ℝ) + 1) * L) ^ 2) ≤
        2 / (L * (2 * a + L)) := by
    have he := midpoint_partial_exact hL ha N
    have hb : 0 ≤ midpointBoundary L a N := by
      unfold midpointBoundary
      positivity
    unfold midpointBoundary at hb
    have hd : 0 ≤ ∑ j ∈ Finset.range N,
        midpointDefect L (a + ((j : ℝ) + 1) * L) := by
      apply Finset.sum_nonneg
      intro j hj
      apply midpointDefect_nonneg hL
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    simp only [midpointBoundary, Nat.cast_zero, mul_zero, zero_add, one_mul] at he
    linarith
  have ht : (∑' j : ℕ, 1 / (a + ((j : ℝ) + 1) * L) ^ 2) ≤
      2 / (L * (2 * a + L)) :=
    le_of_tendsto hs.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall hbound)
  have he : zetaTwo * residuePowerWeight 0 L (a + L) =
      ∑' j : ℕ, 1 / (a + ((j : ℝ) + 1) * L) ^ 2 := by
    unfold residuePowerWeight
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    simp only [Nat.zero_add]
    rw [show a + L + (j : ℝ) * L = a + ((j : ℝ) + 1) * L by ring]
    field_simp [ne_of_gt zetaTwo_pos]
  rw [residuePowerWeight_shift 0 hL ha, mul_add, he]
  have hc : zetaTwo * (1 / (zetaTwo * a ^ (0 + 2))) = 1 / a ^ 2 := by
    field_simp [ne_of_gt zetaTwo_pos]
  rw [hc]
  linarith

theorem weight_le_five_thirds (L a : ℕ) (ha : 0 < a) (haL : a ≤ L) :
    weight L a ≤ (5 / 3 : ℝ) * (1 / (a : ℝ)^2) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haLR : (a : ℝ) ≤ L := by exact_mod_cast haL
  have hLR : (0 : ℝ) < L := haR.trans_le haLR
  have hd : 0 < (L : ℝ) * (2 * (a : ℝ) + L) := by positivity
  have hs : 3 * (a : ℝ)^2 ≤ (L : ℝ) * (2 * (a : ℝ) + L) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haLR) (show 0 ≤ (L : ℝ) + 3 * a by positivity)]
  have ht : 2 / ((L : ℝ) * (2 * (a : ℝ) + L)) ≤
      (2 / 3 : ℝ) * (1 / (a : ℝ)^2) := by
    calc
      2 / ((L : ℝ) * (2 * (a : ℝ) + L)) ≤
          2 / (3 * (a : ℝ)^2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hs
      _ = _ := by ring
  unfold weight
  linarith

/-- Uniform two-sided comparison against the actual complete residue weight. -/
theorem weight_complete_comparison (L a : ℕ) (ha : 0 < a) (haL : a ≤ L) :
    zetaTwo * residuePowerWeight 0 L a ≤ weight L a ∧
      weight L a ≤ (5 / 3 : ℝ) * zetaTwo * residuePowerWeight 0 L a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hLR : (0 : ℝ) < L := by exact_mod_cast ha.trans_le haL
  constructor
  · exact residueSquareWeight_le_rational hLR haR
  · have hlow := residueSquareWeight_lower hLR haR
    have h := mul_le_mul_of_nonneg_left hlow zetaTwo_pos.le
    have he : zetaTwo * (1 / (zetaTwo * (a : ℝ)^2)) = 1 / (a : ℝ)^2 := by
      field_simp [ne_of_gt zetaTwo_pos]
    rw [he] at h
    exact (weight_le_five_thirds L a ha haL).trans
      (by nlinarith)

theorem sum_positive_representatives (L : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ sites L, f a) = ∑ a : Fin L, f (a.val + 1) := by
  classical
  unfold sites
  change (∑ a ∈ Finset.Icc 1 L, f a) =
    ∑ a : Fin L, (fun k : ℕ => f (k + 1)) a.val
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k + 1)) L]
  symm
  refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k hk j hj he
    omega
  · intro a ha
    obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp ha
    exact ⟨a - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    rfl

/-- Every periodic residual is controlled in both directions, with its entire
infinite Q tail included. The bound may vary with the period. -/
theorem periodic_rationalError_comparison (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (hp : ∀ n, f (n + L) = f n) :
    zetaTwo * inversePowerMean 0 (fun n => (1 - f n)^2) ≤ rationalError L f ∧
      rationalError L f ≤ (5 / 3 : ℝ) * zetaTwo *
        inversePowerMean 0 (fun n => (1 - f n)^2) := by
  have hr (n : ℕ) : |1 - f n| ≤ 1 + C := by
    calc
      |1 - f n| ≤ 1 + |f n| := by
        simpa [sub_eq_add_neg] using abs_add_le (1 : ℝ) (-f n)
      _ ≤ 1 + C := add_le_add (le_refl _) (hf n)
  have hsq (n : ℕ) : |(1 - f n)^2| ≤ (1 + C)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp (hr n)]
  rw [periodic_inversePowerMean 0 L hL _ hsq (by intro n; rw [hp])]
  unfold rationalError RiemannResearch.Analysis.FiniteWeightedTailCharge.energy
  rw [sum_positive_representatives]
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro a ha
    have hw := (weight_complete_comparison L (a.val + 1) (by omega)
      (by omega)).1
    convert mul_le_mul_of_nonneg_right hw (sq_nonneg (1 - f (a.val + 1))) using 1
      <;> push_cast <;> ring
  · apply Finset.sum_le_sum
    intro a ha
    have hw := (weight_complete_comparison L (a.val + 1) (by omega)
      (by omega)).2
    convert mul_le_mul_of_nonneg_right hw (sq_nonneg (1 - f (a.val + 1))) using 1
      <;> push_cast <;> ring

theorem periodic_qError_rational_comparison (L : ℕ) (hL : 0 < L)
    (f : QHilbert) {C : ℝ} (hf : ∀ n, |qSequence f n| ≤ C)
    (hp : ∀ n, qSequence f (n + L) = qSequence f n) :
    zetaTwo * ‖qOne - f‖^2 ≤ rationalError L (qSequence f) ∧
      rationalError L (qSequence f) ≤ (5 / 3 : ℝ) * zetaTwo * ‖qOne - f‖^2 := by
  rw [qError_eq_inversePowerMean]
  exact periodic_rationalError_comparison L hL (qSequence f) hf hp

/-- Exact finite discrepancy between the rational and complete-Q objectives. -/
def rationalGap (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ sites L,
    (weight L a - zetaTwo * residuePowerWeight 0 L a) * (1 - f a)^2

/-- No tail is omitted: the complete-Q objective and the nonnegative weight
discrepancy add exactly to the rational objective. -/
theorem rationalError_exact_gap (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {B : ℝ} (hr : ∀ n, |1 - f n| ≤ B)
    (hp : ∀ n, f (n + L) = f n) :
    rationalError L f =
      zetaTwo * inversePowerMean 0 (fun n => (1 - f n)^2) + rationalGap L f := by
  have hsq (n : ℕ) : |(1 - f n)^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp (hr n)]
  rw [periodic_inversePowerMean 0 L hL _ hsq (by intro n; rw [hp])]
  unfold rationalError RiemannResearch.Analysis.FiniteWeightedTailCharge.energy rationalGap
  rw [sum_positive_representatives, sum_positive_representatives]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  push_cast
  ring

theorem weight_gap_bounds (L a : ℕ) (ha : 0 < a) (haL : a ≤ L) :
    0 ≤ weight L a - zetaTwo * residuePowerWeight 0 L a ∧
      weight L a - zetaTwo * residuePowerWeight 0 L a ≤ 2 / (L : ℝ)^2 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hLR : (0 : ℝ) < L := by exact_mod_cast ha.trans_le haL
  constructor
  · exact sub_nonneg.mpr (weight_complete_comparison L a ha haL).1
  · have hlow := mul_le_mul_of_nonneg_left
      (residueSquareWeight_lower hLR haR) zetaTwo_pos.le
    have he : zetaTwo * (1 / (zetaTwo * (a : ℝ)^2)) = 1 / (a : ℝ)^2 := by
      field_simp [ne_of_gt zetaTwo_pos]
    rw [he] at hlow
    have ht : 2 / ((L : ℝ) * (2 * (a : ℝ) + L)) ≤ 2 / (L : ℝ)^2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hLR)
      nlinarith
    unfold weight
    linarith

/-- A fixed bounded competitor has an explicit vanishing discrepancy as
the representation period grows; this is not a bound on optimizer sizes. -/
theorem rationalGap_bounds (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {B : ℝ} (hr : ∀ n, |1 - f n| ≤ B) :
    0 ≤ rationalGap L f ∧ rationalGap L f ≤ 2 * B^2 / (L : ℝ) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsq (n : ℕ) : (1 - f n)^2 ≤ B^2 := by
    nlinarith [abs_le.mp (hr n)]
  constructor
  · unfold rationalGap
    apply Finset.sum_nonneg
    intro a ha
    obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp ha
    exact mul_nonneg (weight_gap_bounds L a (by omega) haL).1 (sq_nonneg _)
  · calc
      rationalGap L f ≤ ∑ a ∈ sites L, (2 / (L : ℝ)^2) * B^2 := by
        unfold rationalGap
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp ha
        exact mul_le_mul (weight_gap_bounds L a (by omega) haL).2 (hsq a)
          (sq_nonneg _) (by positivity)
      _ = (L : ℝ) * ((2 / (L : ℝ)^2) * B^2) := by
        simp [sites, Nat.card_Icc]
      _ = 2 * B^2 / (L : ℝ) := by
        field_simp [ne_of_gt hLR]
        <;> ring

theorem rationalError_fixed_competitor_bound (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {B : ℝ} (hr : ∀ n, |1 - f n| ≤ B)
    (hp : ∀ n, f (n + L) = f n) :
    rationalError L f ≤
      zetaTwo * inversePowerMean 0 (fun n => (1 - f n)^2) + 2 * B^2 / (L : ℝ) := by
  rw [rationalError_exact_gap L hL f hr hp]
  exact add_le_add (le_refl _) (rationalGap_bounds L hL f hr).2

end RiemannResearch.RH.QRationalCoprimeTail
