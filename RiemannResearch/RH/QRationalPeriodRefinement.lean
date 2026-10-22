/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalWeightComparison
import RiemannResearch.RH.QRationalCoprimeTail
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Quantitative rational-weight refinement

Source: independent development from the user-provided continuation agenda,
20 October 2026. The first exact midpoint defect is retained. It bounds the
entire coarse weight gap below and gives a uniform contraction when the
representation period is multiplied by a sufficiently large integer.
The bounds apply to every periodic vector, with no coefficient-size bound.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoProbability

/-- The first positive midpoint defect is part of the complete weight gap. -/
theorem midpointDefect_le_weight_gap (L a : ℕ) (ha : 0 < a) (haL : a ≤ L) :
    midpointDefect L ((a : ℝ) + L) ≤
      weight L a - zetaTwo * residuePowerWeight 0 L a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hLR : (0 : ℝ) < L := by exact_mod_cast ha.trans_le haL
  have hs := residueSquareWeight_le_rational hLR (show 0 < (a : ℝ) + L by positivity)
  have hm := midpoint_step_exact hLR (show (L : ℝ) < a + L by linarith)
  have hshift := residuePowerWeight_shift 0 hLR haR
  have hz : zetaTwo * (1 / (zetaTwo * (a : ℝ) ^ (0 + 2))) =
      1 / (a : ℝ)^2 := by field_simp [ne_of_gt zetaTwo_pos]
  rw [show 2 * ((a : ℝ) + L) - L = 2 * a + L by ring] at hm
  rw [hshift, mul_add, hz]
  unfold weight
  linarith

/-- A simple explicit lower bound for the retained first defect. -/
theorem midpointDefect_lower {L a : ℝ} (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L) :
    1 / (60 * L^2) ≤ midpointDefect L (a + L) := by
  have hx : 0 < a + L := by positivity
  have hxL : L < a + L := by linarith
  have hx2 : (a + L)^2 ≤ 4 * L^2 := by nlinarith
  have hd : 0 < 4 * (a + L)^2 - L^2 := by nlinarith [sq_pos_of_pos hL]
  have hdub : 4 * (a + L)^2 - L^2 ≤ 15 * L^2 := by nlinarith
  have hprod : (a + L)^2 * (4 * (a + L)^2 - L^2) ≤
      (4 * L^2) * (15 * L^2) :=
    mul_le_mul hx2 hdub hd.le (by positivity)
  unfold midpointDefect
  apply (div_le_div_iff₀ (by positivity : 0 < 60 * L^2)
    (by positivity : 0 < (a + L)^2 * (4 * (a + L)^2 - L^2))).mpr
  nlinarith

theorem weight_gap_lower (L a : ℕ) (ha : 0 < a) (haL : a ≤ L) :
    1 / (60 * (L : ℝ)^2) ≤
      weight L a - zetaTwo * residuePowerWeight 0 L a := by
  exact (midpointDefect_lower (by exact_mod_cast ha.trans_le haL)
    (by exact_mod_cast ha) (by exact_mod_cast haL)).trans
      (midpointDefect_le_weight_gap L a ha haL)

private theorem sites_sum_eq_range (L : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ sites L, f a) = ∑ a ∈ Finset.range L, f (a + 1) := by
  rw [sum_positive_representatives]
  exact Fin.sum_univ_eq_sum_range (fun a : ℕ => f (a + 1)) L

/-- Exact replication of one complete positive residue block. -/
theorem periodic_sites_sum_mul (L k : ℕ) (f : ℕ → ℝ)
    (hp : ∀ n, f (n + L) = f n) :
    (∑ a ∈ sites (L * k), f a) = (k : ℝ) * ∑ a ∈ sites L, f a := by
  have hrep (j n : ℕ) : f (n + L * j) = f n := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]
  simp only [sites_sum_eq_range]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have hs : (∑ a ∈ Finset.range L, f (L * k + a + 1)) =
          ∑ a ∈ Finset.range L, f (a + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [show L * k + a + 1 = (a + 1) + L * k by omega, hrep]
      rw [hs]
      push_cast
      ring

/-- The exact unweighted energy on one positive residue block. -/
def residualHeadEnergy (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ sites L, (1 - f a)^2

theorem rationalGap_head_bounds (L : ℕ) (f : ℕ → ℝ) :
    (1 / (60 * (L : ℝ)^2)) * residualHeadEnergy L f ≤ rationalGap L f ∧
      rationalGap L f ≤ (2 / (L : ℝ)^2) * residualHeadEnergy L f := by
  unfold rationalGap residualHeadEnergy
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro a ha
    obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp ha
    exact mul_le_mul_of_nonneg_right
      (weight_gap_lower L a (by omega) haL) (sq_nonneg _)
  · apply Finset.sum_le_sum
    intro a ha
    obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp ha
    exact mul_le_mul_of_nonneg_right
      (weight_gap_bounds L a (by omega) haL).2 (sq_nonneg _)

/-- Uniform relative control of the entire weight discrepancy, valid for
every periodic vector, including vectors whose coefficients vary. -/
theorem rationalGap_mul_le (L k : ℕ) (hL : 0 < L) (hk : 0 < k)
    (f : ℕ → ℝ) (hp : ∀ n, f (n + L) = f n) :
    rationalGap (L * k) f ≤ (120 / (k : ℝ)) * rationalGap L f := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlo := (rationalGap_head_bounds L f).1
  have hup := (rationalGap_head_bounds (L * k) f).2
  have hrep : residualHeadEnergy (L * k) f =
      (k : ℝ) * residualHeadEnergy L f :=
    periodic_sites_sum_mul L k (fun n => (1 - f n)^2) (by intro n; rw [hp])
  calc
    rationalGap (L * k) f ≤
        (2 / ((L * k : ℕ) : ℝ)^2) * residualHeadEnergy (L * k) f := hup
    _ = (120 / (k : ℝ)) *
        ((1 / (60 * (L : ℝ)^2)) * residualHeadEnergy L f) := by
      rw [hrep, Nat.cast_mul]
      field_simp
      ring
    _ ≤ (120 / (k : ℝ)) * rationalGap L f :=
      mul_le_mul_of_nonneg_left hlo (by positivity)

theorem rationalGap_mul_le_self (L k : ℕ) (hL : 0 < L) (hk : 120 ≤ k)
    (f : ℕ → ℝ) (hp : ∀ n, f (n + L) = f n) :
    rationalGap (L * k) f ≤ rationalGap L f := by
  have hkR : (120 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < k := by omega
  have hc : 120 / (k : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hkR
  have hg : 0 ≤ rationalGap L f := by
    have h := (rationalGap_head_bounds L f).1
    have hh : 0 ≤ residualHeadEnergy L f :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact (mul_nonneg (by positivity) hh).trans h
  exact (rationalGap_mul_le L k hL hk0 f hp).trans
    (by simpa using mul_le_mul_of_nonneg_right hc hg)

theorem rationalGap_mul_le_half (L k : ℕ) (hL : 0 < L) (hk : 240 ≤ k)
    (f : ℕ → ℝ) (hp : ∀ n, f (n + L) = f n) :
    rationalGap (L * k) f ≤ rationalGap L f / 2 := by
  have hkR : (240 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < k := by omega
  have hc : 120 / (k : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k)).mpr
    linarith
  have hg : 0 ≤ rationalGap L f := by
    have h := (rationalGap_head_bounds L f).1
    have hh : 0 ≤ residualHeadEnergy L f :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact (mul_nonneg (by positivity) hh).trans h
  exact (rationalGap_mul_le L k hL hk0 f hp).trans
    (by nlinarith [mul_le_mul_of_nonneg_right hc hg])

end RiemannResearch.RH.QRationalCoprimeTail
