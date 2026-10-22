/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoNoiseSignal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complete physical obstruction at ordinary period mean one

Source: finite weighted affine refinement developed in the user-directed
continuation of `CriticalZeroMeanOneAdvance20261008.md`, Sections 4 and 5.
The complete-weight realization reuses `ParetoPeriodicRegrouping`.

Every weight is the full progression mass. The exact affine square is
retained before any lower bound is taken. The displayed rational floor
vanishes with L; this module proves finite identities and inequalities,
not a limiting defect theorem.
-/

namespace RiemannResearch.RH.Pareto.MeanOnePeriodObstruction
noncomputable section
open scoped BigOperators

/-- Exact affine square completion with a sum constraint -1. -/
theorem weighted_affine_completion {ι : Type*} (s : Finset ι)
    (w e : ι → ℝ) (hw : ∀ i ∈ s, w i ≠ 0)
    (H : ℝ) (hH : H ≠ 0) (hHsum : H = ∑ i ∈ s, 1 / w i)
    (he : (∑ i ∈ s, e i) = -1) :
    (∑ i ∈ s, w i * (e i) ^ 2) = 1 / H +
      ∑ i ∈ s, w i * (e i + 1 / (H * w i)) ^ 2 := by
  have hcell (i : ι) (hi : i ∈ s) :
      w i * (e i + 1 / (H * w i)) ^ 2 =
        w i * (e i) ^ 2 + (2 / H) * e i + (1 / H ^ 2) * (1 / w i) := by
    field_simp [hH, hw i hi]
    ring
  have hsum : (∑ i ∈ s, w i * (e i + 1 / (H * w i)) ^ 2) =
      (∑ i ∈ s, w i * (e i) ^ 2) + (2 / H) * (-1) + (1 / H ^ 2) * H := by
    calc
      _ = ∑ i ∈ s, (w i * (e i) ^ 2 + (2 / H) * e i +
          (1 / H ^ 2) * (1 / w i)) := Finset.sum_congr rfl hcell
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, he, ← hHsum]
  rw [hsum]
  field_simp [hH]
  ring

theorem weighted_affine_lower_bound {ι : Type*} (s : Finset ι)
    (w e : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (H : ℝ) (hH : 0 < H) (hHsum : H = ∑ i ∈ s, 1 / w i)
    (he : (∑ i ∈ s, e i) = -1) :
    1 / H ≤ ∑ i ∈ s, w i * (e i) ^ 2 := by
  rw [weighted_affine_completion s w e (fun i hi => ne_of_gt (hw i hi))
    H (ne_of_gt hH) hHsum he]
  exact le_add_of_nonneg_right (Finset.sum_nonneg
    (fun i hi => mul_nonneg (hw i hi).le (sq_nonneg _)))

/-- Reciprocal full progression masses away from the zero class. -/
def reciprocalMass (L : ℕ) : ℝ :=
  ∑ i : Fin (L - 1), 1 / progressionWeight L (i.val + 1)

theorem reciprocalMass_pos (L : ℕ) (hL : 1 < L) : 0 < reciprocalMass L := by
  classical
  unfold reciprocalMass
  apply Finset.sum_pos
  · intro i hi
    exact one_div_pos.mpr (progressionWeight_pos L (i.val + 1) (by omega) (by omega))
  · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

theorem sum_range_successor_quadratic (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * ((i : ℝ) + 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem reciprocal_progressionWeight_le (L r : ℕ) (hL : 0 < L) (hr : 0 < r) :
    1 / progressionWeight L r ≤ (r : ℝ) * ((r : ℝ) + 1) := by
  have hw := progressionWeight_pos L r hL hr
  have hp : (0 : ℝ) < (r : ℝ) * ((r : ℝ) + 1) := by positivity
  have h := positiveWeight_le_progressionWeight L r hL
  unfold positiveWeight at h
  have hh := (div_le_iff₀ hp).mp h
  apply (div_le_iff₀ hw).mpr
  nlinarith only [hh]

/-- Full-tail weights improve each reciprocal over its first-site envelope. -/
theorem reciprocalMass_le_cubic (L : ℕ) (hL : 1 < L) :
    reciprocalMass L ≤ (L : ℝ) * ((L : ℝ) ^ 2 - 1) / 3 := by
  have hs : reciprocalMass L ≤
      ∑ i : Fin (L - 1), ((i.val : ℝ) + 1) * ((i.val : ℝ) + 2) := by
    unfold reciprocalMass
    apply Finset.sum_le_sum
    intro i hi
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 1 = 2 by norm_num] using
      reciprocal_progressionWeight_le L (i.val + 1) (by omega) (by omega)
  apply hs.trans
  have he : (∑ i : Fin (L - 1), ((i.val : ℝ) + 1) * ((i.val : ℝ) + 2)) =
      ((L - 1 : ℕ) : ℝ) * (((L - 1 : ℕ) : ℝ) + 1) *
        (((L - 1 : ℕ) : ℝ) + 2) / 3 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i : ℝ) + 1) * ((i : ℝ) + 2))]
    exact sum_range_successor_quadratic (L - 1)
  rw [he, Nat.cast_sub (by omega : 1 ≤ L)]
  push_cast
  nlinarith

/-- The error residual away from the common-period class has sum exactly -1. -/
theorem meanOne_period_residual_sum (L : ℕ) (hL : 1 < L) (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hp : ∀ k, f (k + L) = f k)
    (hm : (∑ i : Fin L, f (i.val + 1)) = (L : ℝ)) :
    (∑ i : Fin (L - 1), (1 - f (i.val + 1))) = -1 := by
  cases L with
  | zero => omega
  | succ n =>
    change (∑ i : Fin n, (1 - f (i.val + 1))) = -1
    have hz : f (n + 1) = 0 := by simpa [hf0] using hp 0
    rw [Fin.sum_univ_castSucc] at hm
    simp only [Fin.val_castSucc, Fin.val_last, hz, add_zero] at hm
    simp only [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hm]
    push_cast
    ring

/-- Complete period regrouping, separating the forced common-period zero. -/
theorem period_error_split (L : ℕ) (hL : 1 < L) (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0) (hp : ∀ k, f (k + L) = f k) :
    paretoError f = progressionWeight L L +
      ∑ i : Fin (L - 1), progressionWeight L (i.val + 1) * (1 - f (i.val + 1)) ^ 2 := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  change paretoInner (fun k => 1 - f k) (fun k => 1 - f k) = _
  rw [periodic_paretoInner L (by omega) (fun k => 1 - f k)
    (bounded_sub h1 hf) (by intro k; rw [hp])]
  cases L with
  | zero => omega
  | succ n =>
    have hz : f (n + 1) = 0 := by simpa [hf0] using hp 0
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, hz, sub_zero, one_pow, mul_one]
    exact add_comm _ _

/-- Exact physical mean-one completion. Every complete progression weight and
the full nonnegative correction square remain visible. -/
theorem physical_meanOne_completion (L : ℕ) (hL : 1 < L) (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0) (hp : ∀ k, f (k + L) = f k)
    (hm : (∑ i : Fin L, f (i.val + 1)) = (L : ℝ)) :
    paretoError f = progressionWeight L L + 1 / reciprocalMass L +
      ∑ i : Fin (L - 1), progressionWeight L (i.val + 1) *
        (1 - f (i.val + 1) +
          1 / (reciprocalMass L * progressionWeight L (i.val + 1))) ^ 2 := by
  rw [period_error_split L hL f hf hf0 hp,
    weighted_affine_completion Finset.univ
      (fun i : Fin (L - 1) => progressionWeight L (i.val + 1))
      (fun i : Fin (L - 1) => 1 - f (i.val + 1))
      (fun i hi => ne_of_gt (progressionWeight_pos L (i.val + 1) (by omega) (by omega)))
      (reciprocalMass L) (ne_of_gt (reciprocalMass_pos L hL)) rfl
      (meanOne_period_residual_sum L hL f hf0 hp hm)]
  ring

theorem physical_meanOne_lower_bound (L : ℕ) (hL : 1 < L) (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0) (hp : ∀ k, f (k + L) = f k)
    (hm : (∑ i : Fin L, f (i.val + 1)) = (L : ℝ)) :
    progressionWeight L L + 1 / reciprocalMass L ≤ paretoError f := by
  rw [physical_meanOne_completion L hL f hf hf0 hp hm]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi =>
    mul_nonneg (progressionWeight_pos L (i.val + 1) (by omega) (by omega)).le
      (sq_nonneg _)))

/-- Explicit strict improvement over the common-period mass alone. -/
theorem physical_meanOne_explicit_lower_bound (L : ℕ) (hL : 1 < L)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0)
    (hp : ∀ k, f (k + L) = f k)
    (hm : (∑ i : Fin L, f (i.val + 1)) = (L : ℝ)) :
    progressionWeight L L + 3 / ((L : ℝ) * ((L : ℝ) ^ 2 - 1)) ≤ paretoError f := by
  have hH := reciprocalMass_pos L hL
  have hLr : (1 : ℝ) < L := by exact_mod_cast hL
  have hsq : 0 < (L : ℝ) ^ 2 - 1 := by nlinarith
  have hden : 0 < (L : ℝ) * ((L : ℝ) ^ 2 - 1) :=
    mul_pos (by linarith) hsq
  have hrec : 3 / ((L : ℝ) * ((L : ℝ) ^ 2 - 1)) ≤ 1 / reciprocalMass L := by
    apply (div_le_div_iff₀ hden hH).mpr
    have hc := reciprocalMass_le_cubic L hL
    nlinarith
  exact (add_le_add_right hrec (progressionWeight L L)).trans
    (physical_meanOne_lower_bound L hL f hf hf0 hp hm)

end
end RiemannResearch.RH.Pareto.MeanOnePeriodObstruction
