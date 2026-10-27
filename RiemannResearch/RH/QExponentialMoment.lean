/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exponential moments give pointwise logarithmic envelopes under Q

Source: the user's prime-resampling agenda, with an atomwise proof developed
here. The positive Q mass at each integer supplies the bound directly.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QExponentialMoment
open ZetaTwoHilbert ZetaTwoProbability

/-- A positive exponential moment gives a pointwise logarithmic envelope,
because every positive integer is a positive atom of the inverse-square law.
The proof requires neither an Orlicz theorem nor a change-of-measure provider. -/
theorem exists_log_envelope_of_sequence_exponentialMoment_summable
    (f : ℕ → ℝ) (hf0 : f 0 = 0) (κ : ℝ) (hκ : 0 < κ)
    (hs : Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |f n|))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |f n| ≤ C * (6 + Real.log (n : ℝ)) := by
  let M : ℝ := ∑' n : ℕ,
    positiveQWeight n * Real.exp (κ * |f n|)
  have hterm (n : ℕ) :
      0 ≤ positiveQWeight n * Real.exp (κ * |f n|) :=
    mul_nonneg (positiveQWeight_nonneg n) (Real.exp_pos _).le
  have hM : 0 ≤ M := tsum_nonneg hterm
  let A : ℝ := M * zetaTwo
  have hA : 0 ≤ A := mul_nonneg hM zetaTwo_pos.le
  let C : ℝ := (A + 2) / κ
  have hC : 0 ≤ C := div_nonneg (by linarith) hκ.le
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [hf0, abs_zero, Nat.cast_zero, Real.log_zero, add_zero]
    positivity
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hmass : positiveQWeight n * Real.exp (κ * |f n|) ≤ M :=
    hs.le_tsum n (fun j _ => hterm j)
  have hd : 0 < zetaTwo * (n : ℝ) ^ 2 :=
    mul_pos zetaTwo_pos (sq_pos_of_pos hn0)
  have hdiv : Real.exp (κ * |f n|) /
      (zetaTwo * (n : ℝ) ^ 2) ≤ M := by
    simpa only [positiveQWeight, one_div, div_eq_mul_inv, mul_comm, mul_one] using hmass
  have hexp : Real.exp (κ * |f n|) ≤ A * (n : ℝ) ^ 2 := by
    have hh := (div_le_iff₀ hd).mp hdiv
    dsimp only [A]
    nlinarith
  have hAexp : A ≤ Real.exp A := by
    linarith [Real.add_one_le_exp A]
  have hexplog : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
    rw [show 2 * Real.log (n : ℝ) =
      Real.log (n : ℝ) + Real.log (n : ℝ) by ring, Real.exp_add]
    simp only [Real.exp_log hn0]
    ring
  have hmajor : A * (n : ℝ) ^ 2 ≤
      Real.exp (A + 2 * Real.log (n : ℝ)) := by
    rw [Real.exp_add, hexplog]
    exact mul_le_mul_of_nonneg_right hAexp (sq_nonneg _)
  have hlogbound : κ * |f n| ≤ A + 2 * Real.log (n : ℝ) :=
    Real.exp_le_exp.mp (hexp.trans hmajor)
  suffices hf : κ * |f n| ≤ κ * (C * (6 + Real.log (n : ℝ))) by
    nlinarith only [hf, hκ]
  calc
    κ * |f n| ≤ A + 2 * Real.log (n : ℝ) := hlogbound
    _ ≤ (A + 2) * (6 + Real.log (n : ℝ)) := by
      nlinarith [mul_nonneg hA hln]
    _ = κ * (C * (6 + Real.log (n : ℝ))) := by
      dsimp only [C]
      field_simp [hκ.ne']

/-- Every positive stretched exponential moment gives some integer
polylogarithmic physical envelope. -/
theorem exists_polylog_envelope_of_stretchedExponentialMoment_summable
    (u : QHilbert) (α κ : ℝ) (hα : 0 < α) (hκ : 0 < κ)
    (hs : Summable (fun n : ℕ => positiveQWeight n *
      Real.exp (κ * (|qSequence u n| ^ α)))) :
    ∃ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      |qSequence u n| ≤ D * (6 + Real.log (n : ℝ)) ^ m := by
  let f : ℕ → ℝ := fun n => |qSequence u n| ^ α
  have hf (n : ℕ) : 0 ≤ f n := Real.rpow_nonneg (abs_nonneg _) _
  have hf0 : f 0 = 0 := by
    simp only [f, qSequence_zero, abs_zero, Real.zero_rpow hα.ne']
  have hs' : Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |f n|)) := by
    simpa only [abs_of_nonneg (hf _)] using hs
  obtain ⟨C, hC, hbound⟩ :=
    exists_log_envelope_of_sequence_exponentialMoment_summable f hf0 κ hκ hs'
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / α)
  have hαm : (1 : ℝ) ≤ α * (m : ℝ) := by
    have h := (div_lt_iff₀ hα).mp hm
    nlinarith
  refine ⟨m, 1 + C ^ m, by positivity, ?_⟩
  intro n
  have hL : 1 ≤ 6 + Real.log (n : ℝ) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      linarith [Real.log_nonneg hn1]
  have hraw : f n ≤ C * (6 + Real.log (n : ℝ)) := by
    simpa only [abs_of_nonneg (hf n)] using hbound n
  have hbase : |qSequence u n| ≤ 1 + (f n) ^ m := by
    by_cases hsmall : |qSequence u n| ≤ 1
    · linarith [pow_nonneg (hf n) m]
    · have hx : 1 ≤ |qSequence u n| := (lt_of_not_ge hsmall).le
      have hr := Real.rpow_le_rpow_of_exponent_le hx hαm
      rw [Real.rpow_one, Real.rpow_mul (abs_nonneg _), Real.rpow_natCast] at hr
      change |qSequence u n| ≤ (f n) ^ m at hr
      linarith
  have hp : (f n) ^ m ≤ (C * (6 + Real.log (n : ℝ))) ^ m :=
    pow_le_pow_left₀ (hf n) hraw m
  rw [mul_pow] at hp
  have hLm : 1 ≤ (6 + Real.log (n : ℝ)) ^ m := one_le_pow₀ hL
  nlinarith

/-- Physical boundedness gives all real exponential moments under Q. -/
theorem exponentialMoment_summable_of_physical_bound
    (u : QHilbert) (C : ℝ) (hbound : ∀ n : ℕ, |qSequence u n| ≤ C) (κ : ℝ) :
    Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence u n|)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveQWeight_nonneg n) (Real.exp_pos _).le)
    _ (positiveQWeight_summable.mul_right (Real.exp (|κ| * C)))
  intro n
  apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
  apply Real.exp_le_exp.mpr
  calc
    κ * |qSequence u n| ≤ |κ| * |qSequence u n| :=
      mul_le_mul_of_nonneg_right (le_abs_self κ) (abs_nonneg _)
    _ ≤ |κ| * C := mul_le_mul_of_nonneg_left (hbound n) (abs_nonneg κ)

end RiemannResearch.RH.QExponentialMoment
