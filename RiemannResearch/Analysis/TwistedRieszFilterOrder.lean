import RiemannResearch.Analysis.TwistedRieszFilterAlgebra
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Residue bounds at every finite Riesz order

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

This strengthens the second-order filter algebra to every
finite smoothing order. It does not assert an analytic explicit formula or
permit an interchange with an order-growing limit.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.TwistedRieszFilter

def realDenominator (r : ℕ) (β : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (r + 1), (β + (j : ℝ))

def realAmplitude (r : ℕ) (β : ℝ) : ℝ :=
  (r.factorial : ℝ) / realDenominator r β

theorem realDenominator_pos (r : ℕ) {β : ℝ} (hβ : 0 < β) :
    0 < realDenominator r β := by
  unfold realDenominator
  apply Finset.prod_pos
  intro j hj
  positivity

theorem realAmplitude_pos (r : ℕ) {β : ℝ} (hβ : 0 < β) :
    0 < realAmplitude r β := by
  unfold realAmplitude
  exact div_pos (by exact_mod_cast Nat.factorial_pos r) (realDenominator_pos r hβ)

theorem realDenominator_mono (r : ℕ) {β γ : ℝ}
    (hβ : 0 ≤ β) (h : β ≤ γ) :
    realDenominator r β ≤ realDenominator r γ := by
  unfold realDenominator
  apply Finset.prod_le_prod
  · intro j hj
    positivity
  · intro j hj
    linarith

theorem realAmplitude_antitone (r : ℕ) {β γ : ℝ}
    (hβ : 0 < β) (h : β ≤ γ) :
    realAmplitude r γ ≤ realAmplitude r β := by
  have hγ : 0 < γ := lt_of_lt_of_le hβ h
  have hd := realDenominator_mono r hβ.le h
  unfold realAmplitude
  apply (div_le_div_iff₀ (realDenominator_pos r hγ)
    (realDenominator_pos r hβ)).mpr
  exact mul_le_mul_of_nonneg_left hd (by positivity)

theorem realDenominator_one (r : ℕ) :
    realDenominator r 1 = ((r + 1).factorial : ℝ) := by
  have hnat : (∏ j ∈ Finset.range (r + 1), (j + 1)) = (r + 1).factorial :=
    Finset.prod_range_add_one_eq_factorial (r + 1)
  unfold realDenominator
  calc
    (∏ j ∈ Finset.range (r + 1), (1 + (j : ℝ))) =
        ∏ j ∈ Finset.range (r + 1), ((j + 1 : ℕ) : ℝ) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = ((r + 1).factorial : ℝ) := by rw [← Nat.cast_prod, hnat]

theorem realAmplitude_one (r : ℕ) :
    realAmplitude r 1 = 1 / ((r : ℝ) + 1) := by
  unfold realAmplitude
  rw [realDenominator_one, Nat.factorial_succ]
  push_cast
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hr : (r : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hf, hr]
  <;> ring

/-- No finite smoothing order has a vanishing peak amplitude on the full
right half of the critical strip. The lower bound is uniform in ordinate. -/
theorem realAmplitude_strip_bounds (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (hβ' : β ≤ 1) :
    1 / ((r : ℝ) + 1) ≤ realAmplitude r β ∧
      realAmplitude r β ≤ realAmplitude r (1 / 2) := by
  have hb : 0 < β := by linarith
  constructor
  · have h := realAmplitude_antitone r hb hβ'
    rwa [realAmplitude_one] at h
  · exact realAmplitude_antitone r (by norm_num) hβ

end RiemannResearch.Analysis.TwistedRieszFilter
