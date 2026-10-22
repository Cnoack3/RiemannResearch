import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Two exact signed summation-by-parts formulas

Source: user-provided `AnthropicRHBridges20260928.md`, section 1,
for the discrete signed strategy. These elementary finite identities do not
require signs, smooth interpolation, or asymptotic hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.SignedAbel

def primitive (a : ℕ → ℝ) (M : ℕ) : ℝ := ∑ k ∈ Finset.range M, a k

def difference (b : ℕ → ℝ) (k : ℕ) : ℝ := b (k+1) - b k

def value (a b : ℕ → ℝ) (M : ℕ) : ℝ :=
  primitive a M * b M -
    ∑ k ∈ Finset.range M, primitive a (k+1) * difference b k

def secondValue (a b : ℕ → ℝ) (M : ℕ) : ℝ :=
  primitive a M * b M -
    primitive (fun k => primitive a (k+1)) M * difference b M +
    ∑ k ∈ Finset.range M,
      primitive (fun j => primitive a (j+1)) (k+1) * difference (difference b) k

theorem sum_eq_value (a b : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.range M, a k * b k) = value a b M := by
  induction M with
  | zero => simp [value, primitive]
  | succ M ih =>
    simp only [value, difference] at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [primitive, Finset.sum_range_succ]
    ring

theorem value_eq_secondValue (a b : ℕ → ℝ) (M : ℕ) :
    value a b M = secondValue a b M := by
  have h := sum_eq_value (fun k => primitive a (k+1)) (difference b) M
  unfold value at h ⊢
  rw [h]
  unfold secondValue
  ring

theorem sum_eq_secondValue (a b : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.range M, a k * b k) = secondValue a b M :=
  (sum_eq_value a b M).trans (value_eq_secondValue a b M)

theorem second_difference (b : ℕ → ℝ) (k : ℕ) :
    difference (difference b) k = b (k+2) - 2*b (k+1) + b k := by
  simp only [difference]
  ring

/-- The same real primitive paired with a complex kernel, retaining the endpoint. -/
def complexValue (a : ℕ → ℝ) (b : ℕ → ℂ) (M : ℕ) : ℂ :=
  (primitive a M : ℂ) * b M -
    ∑ k ∈ Finset.range M, (primitive a (k + 1) : ℂ) * (b (k + 1) - b k)

theorem sum_eq_complexValue (a : ℕ → ℝ) (b : ℕ → ℂ) (M : ℕ) :
    (∑ k ∈ Finset.range M, (a k : ℂ) * b k) = complexValue a b M := by
  induction M with
  | zero => simp [complexValue, primitive]
  | succ M ih =>
    simp only [complexValue] at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [primitive, Finset.sum_range_succ, Complex.ofReal_add]
    ring

end RiemannResearch.Analysis.SignedAbel
