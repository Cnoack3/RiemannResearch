import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite incidence inversion and signed tail charge

Source: user-provided `CRT Carries and Squarefree Residual Exhaustion`,
19 October 2026, Sections 8 and 12. The intended arithmetic application
uses positions k in 1,...,L, labels gcd(k,L), divisor incidence, and its
finite Mobius inverse. The module proves generic finite inversion and
retains both positive and negative parts of the signed charge.

No analytic exhaustion estimate is claimed by this file.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteIncidenceTailCharge

/-- A left inverse of the finite incidence matrix extracts every label
class from the incidence-weighted charge equations. The left-inverse
hypothesis is finite algebra, not an asymptotic analytic assumption. -/
theorem extract_class_charge {α β γ : Type*} [DecidableEq β] [Fintype γ]
    (s : Finset α) (label : α → β) (x : α → ℝ)
    (incidence : γ → β → ℝ) (inverse : β → γ → ℝ) (rhs : γ → ℝ)
    (hleft : ∀ b c, (∑ j, inverse b j * incidence j c) =
      if b = c then 1 else 0)
    (heq : ∀ j, (∑ a ∈ s, incidence j (label a) * x a) = rhs j)
    (b : β) :
    (∑ a ∈ s, if label a = b then x a else 0) =
      ∑ j, inverse b j * rhs j := by
  classical
  symm
  calc
    (∑ j, inverse b j * rhs j) =
        ∑ j, ∑ a ∈ s, inverse b j * incidence j (label a) * x a := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← heq j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = ∑ a ∈ s, (∑ j, inverse b j * incidence j (label a)) * x a := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
    _ = ∑ a ∈ s, if label a = b then x a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hleft]
      by_cases h : label a = b
      · simp [h]
      · simp [h, Ne.symm h]

/-- Positive charge is kept separately from negative charge. -/
def positiveCharge {α : Type*} (s : Finset α) (x : α → ℝ) : ℝ :=
  ∑ a ∈ s, max (x a) 0

/-- Magnitude of the negative charge, not a sign restriction on x. -/
def negativeCharge {α : Type*} (s : Finset α) (x : α → ℝ) : ℝ :=
  ∑ a ∈ s, max (-x a) 0

/-- Exact Jordan decomposition of a finite signed charge. -/
theorem positive_sub_negative {α : Type*} (s : Finset α) (x : α → ℝ) :
    positiveCharge s x - negativeCharge s x = ∑ a ∈ s, x a := by
  unfold positiveCharge negativeCharge
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rcases le_total 0 (x a) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

/-- Removing the distinguished energy term leaves an exact negative
mass budget. In the coprime class, x(1)=E and the total is the small
boundary term; persistent E forces negative mass to persist as well. -/
theorem negative_charge_after_erase {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) (a : α) (ha : a ∈ s) (E t : ℝ)
    (hE : x a = E) (ht : (∑ k ∈ s, x k) = t) :
    negativeCharge (s.erase a) x =
      E - t + positiveCharge (s.erase a) x := by
  have he := Finset.sum_erase_add (s := s) (f := x) ha
  have hj := positive_sub_negative (s.erase a) x
  rw [hE, ht] at he
  linarith

/-- A lower bound on the amount of negative charge. Dropping the
nonnegative positive charge gives only this one-sided consequence. -/
theorem energy_sub_boundary_le_negative_charge {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) (a : α) (ha : a ∈ s) (E t : ℝ)
    (hE : x a = E) (ht : (∑ k ∈ s, x k) = t) :
    E - t ≤ negativeCharge (s.erase a) x := by
  rw [negative_charge_after_erase s x a ha E t hE ht]
  have hp : 0 ≤ positiveCharge (s.erase a) x := by
    exact Finset.sum_nonneg (fun k hk => le_max_right (x k) 0)
  linarith

/-- Centering by the exact class average leaves zero total fluctuation.
The arithmetic application takes each gcd class separately. -/
theorem centered_charge_zero {α : Type*} (s : Finset α) (x : α → ℝ) (c : ℝ)
    (hmean : (∑ a ∈ s, x a) = (s.card : ℝ) * c) :
    (∑ a ∈ s, (x a - c)) = 0 := by
  rw [Finset.sum_sub_distrib, hmean]
  simp only [Finset.sum_const, nsmul_eq_mul, sub_self]

/-- Exact square decomposition around the common average. Every
within-class fluctuation square is retained. -/
theorem sum_sq_eq_mean_sq_add_centered_sq {α : Type*}
    (s : Finset α) (x : α → ℝ) (c : ℝ)
    (hmean : (∑ a ∈ s, x a) = (s.card : ℝ) * c) :
    (∑ a ∈ s, (x a) ^ 2) =
      (s.card : ℝ) * c ^ 2 + ∑ a ∈ s, (x a - c) ^ 2 := by
  have hz := centered_charge_zero s x c hmean
  have he : (∑ a ∈ s, (x a) ^ 2) =
      (s.card : ℝ) * c ^ 2 + 2 * c * (∑ a ∈ s, (x a - c)) +
        ∑ a ∈ s, (x a - c) ^ 2 := by
    calc
      _ = ∑ a ∈ s, (c ^ 2 + 2 * c * (x a - c) + (x a - c) ^ 2) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  simpa only [hz, mul_zero, add_zero] using he

end RiemannResearch.Analysis.FiniteIncidenceTailCharge
