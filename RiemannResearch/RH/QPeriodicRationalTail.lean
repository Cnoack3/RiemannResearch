/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ArithmeticProgressionSquareSeries
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational complete-tail bounds for actual periodic Q energies

The source is elementary rational telescoping followed by the existing exact
residue regrouping. The imported residue weight is used solely through its
defining arithmetic-progression series and exact shift identity. No special-
function asymptotics or RH assumption is involved.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoProbability
open ZetaTwoHilbert
open RiemannResearch.Analysis.ArithmeticProgressionSquareTail

theorem residueSquareWeight_sharp_tail_upper (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    residuePowerWeight 0 L (a + L) ≤ 1 / (zetaTwo * L * a) := by
  have heq : residuePowerWeight 0 L (a + L) =
      (∑' k : ℕ, 1 / (a + ((k + 1 : ℕ) : ℝ) * L) ^ 2) / zetaTwo := by
    rw [residuePowerWeight, ← tsum_div_const]
    apply tsum_congr
    intro k
    have harg : a + L + (k : ℝ) * L = a + ((k + 1 : ℕ) : ℝ) * L := by
      push_cast
      ring
    simp only [Nat.zero_add, harg]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  rw [heq]
  calc
    _ ≤ (1 / (L * a)) / zetaTwo :=
      div_le_div_of_nonneg_right (complete_tail_bound a L ha hL) zetaTwo_pos.le
    _ = _ := by ring

theorem residueSquareWeight_two_head_upper (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    residuePowerWeight 0 L a ≤
      (1 / a ^ 2 + 1 / (a + L) ^ 2 + 1 / (L * (a + L))) / zetaTwo := by
  have h0 := residuePowerWeight_shift 0 hL ha
  have h1 := residuePowerWeight_shift 0 hL (add_pos ha hL)
  have ht := residueSquareWeight_sharp_tail_upper (a + L) L (add_pos ha hL) hL
  simp only [Nat.zero_add] at h0 h1
  calc
    residuePowerWeight 0 L a = 1 / (zetaTwo * a ^ 2) +
        1 / (zetaTwo * (a + L) ^ 2) + residuePowerWeight 0 L (a + L + L) := by
      rw [h0, h1]
      ring
    _ ≤ 1 / (zetaTwo * a ^ 2) + 1 / (zetaTwo * (a + L) ^ 2) +
        1 / (zetaTwo * L * (a + L)) := by linarith only [ht]
    _ = _ := by
      field_simp [ne_of_gt zetaTwo_pos, ne_of_gt ha, ne_of_gt hL,
        ne_of_gt (add_pos ha hL)]
      <;> ring

/-- A full Q energy certificate using exactly two periods and a rational bound
for every omitted residue tail. -/
theorem periodic_qEnergy_two_head_upper (L : ℕ) (hL : 0 < L)
    (R : ℕ → ℝ) {C : ℝ} (hR : ∀ n, |R n| ≤ C)
    (hp : ∀ n, R (n + L) = R n) :
    inversePowerMean 0 (fun n => R n ^ 2) ≤
      (∑ a : Fin L, R (a.val + 1) ^ 2 *
        (1 / ((a.val : ℝ) + 1) ^ 2 +
         1 / ((a.val : ℝ) + 1 + (L : ℝ)) ^ 2 +
         1 / ((L : ℝ) * ((a.val : ℝ) + 1 + (L : ℝ))))) / zetaTwo := by
  have hsq : ∀ n, |R n ^ 2| ≤ C ^ 2 := by
    intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp (hR n)]
  rw [periodic_inversePowerMean 0 L hL _ hsq (by intro n; rw [hp])]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  have hw := residueSquareWeight_two_head_upper ((a.val : ℝ) + 1) (L : ℝ)
    (by positivity) (by exact_mod_cast hL)
  have hh := mul_le_mul_of_nonneg_right hw (sq_nonneg (R (a.val + 1)))
  convert hh using 1 <;> push_cast <;> ring

/-- The same rational bound for the actual Hilbert approximation error. -/
theorem periodic_qError_two_head_upper (L : ℕ) (hL : 0 < L)
    (f : QHilbert) {C : ℝ} (hf : ∀ n, |qSequence f n| ≤ C)
    (hp : ∀ n, qSequence f (n + L) = qSequence f n) :
    ‖qOne - f‖ ^ 2 ≤
      (∑ a : Fin L, (1 - qSequence f (a.val + 1)) ^ 2 *
        (1 / ((a.val : ℝ) + 1) ^ 2 +
         1 / ((a.val : ℝ) + 1 + (L : ℝ)) ^ 2 +
         1 / ((L : ℝ) * ((a.val : ℝ) + 1 + (L : ℝ))))) / zetaTwo := by
  rw [qError_eq_inversePowerMean]
  apply periodic_qEnergy_two_head_upper L hL
  · intro n
    calc
      |1 - qSequence f n| ≤ 1 + |qSequence f n| := by
        simpa [sub_eq_add_neg] using abs_add_le (1 : ℝ) (-qSequence f n)
      _ ≤ 1 + C := add_le_add le_rfl (hf n)
  · intro n
    rw [hp]

end RiemannResearch.RH.ZetaTwoProbability
