import RiemannResearch.LinearAlgebra.FiniteCumulativeCellEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite cumulative Gram operator and its tridiagonal inverse

Source: user-provided `V_vector_space_RH.pdf`, Section 7, for
K = Lᵀ diag(w) L. Here L is finite cumulative summation; its transpose
is suffix summation. The right-hand side is extended by b(N)=0.
The exact boundary identity is stated before imposing that condition.

The inverse formulas require only nonzero cell weights. Positive integral
weights in the Chebyshev application meet this hypothesis. This module
does not bound the actual arithmetic discrepancy.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.CumulativeCellEnergy

/-- Finite cumulative Gram action; for i ≤ N this is the suffix sum
of w(k) times the cumulative jump vector. -/
def gramAction (w a : ℕ → ℝ) (N i : ℕ) : ℝ :=
  cumulative (fun k => w k * cumulative a (k + 1)) N -
    cumulative (fun k => w k * cumulative a (k + 1)) i


/-- The finite-head Gram action is exactly suffix summation after weighting. -/
theorem gramAction_eq_suffix (w a : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    gramAction w a N i =
      ∑ k ∈ Finset.range (N - i), w (i + k) * cumulative a (i + k + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
  simp only [Nat.add_sub_cancel_left, gramAction, cumulative, Finset.sum_range_add]
  ring

def precisionLevel (w b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => (b i - b (i + 1)) / w i

/-- A first difference of a weighted backward difference. -/
def precisionAction (w b : ℕ → ℝ) (i : ℕ) : ℝ :=
  precisionLevel w b (i + 1) - precisionLevel w b i

theorem cumulative_precisionAction (w b : ℕ → ℝ) (n : ℕ) :
    cumulative (precisionAction w b) n = precisionLevel w b n := by
  unfold cumulative precisionAction
  rw [cumulative_difference]
  simp [precisionLevel]

theorem gramAction_boundary (w a : ℕ → ℝ) (N : ℕ) :
    gramAction w a N N = 0 := by
  simp [gramAction]

theorem gramAction_difference (w a : ℕ → ℝ) (N i : ℕ) :
    gramAction w a N i - gramAction w a N (i + 1) =
      w i * cumulative a (i + 1) := by
  simp only [gramAction, cumulative, Finset.sum_range_succ]
  ring

theorem precisionAction_gramAction (w a : ℕ → ℝ) (N i : ℕ)
    (hi : i < N) (hw : ∀ j < N, w j ≠ 0) :
    precisionAction w (gramAction w a N) i = a i := by
  have hl (n : ℕ) (hn : n ≤ N) :
      precisionLevel w (gramAction w a N) n = cumulative a n := by
    cases n with
    | zero => simp [precisionLevel, cumulative]
    | succ n =>
      simp only [precisionLevel, gramAction_difference]
      exact mul_div_cancel_left₀ (cumulative a (n + 1)) (hw n (by omega))
  rw [precisionAction, hl (i + 1) (by omega), hl i (by omega)]
  simp only [cumulative, Finset.sum_range_succ]
  ring

theorem weighted_cumulative_precisionAction (w b : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, w i ≠ 0) :
    cumulative (fun i => w i * cumulative (precisionAction w b) (i + 1)) n =
      b 0 - b n := by
  unfold cumulative
  have he : (∑ i ∈ Finset.range n,
      w i * (∑ j ∈ Finset.range (i + 1), precisionAction w b j)) =
      ∑ i ∈ Finset.range n, (b i - b (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    change w i * cumulative (precisionAction w b) (i + 1) = _
    rw [cumulative_precisionAction, precisionLevel]
    field_simp [hw i (Finset.mem_range.mp hi)]
  rw [he]
  have hn : (∑ i ∈ Finset.range n, (b i - b (i + 1))) =
      -(∑ i ∈ Finset.range n, (b (i + 1) - b i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hn, cumulative_difference]
  ring

/-- The exact inverse identity retains the right endpoint before it is set to zero. -/
theorem gramAction_precisionAction_boundary (w b : ℕ → ℝ) (N i : ℕ)
    (hi : i ≤ N) (hw : ∀ j < N, w j ≠ 0) :
    gramAction w (precisionAction w b) N i = b i - b N := by
  rw [gramAction, weighted_cumulative_precisionAction w b N hw,
    weighted_cumulative_precisionAction w b i (fun j hj => hw j (lt_of_lt_of_le hj hi))]
  ring

theorem gramAction_precisionAction (w b : ℕ → ℝ) (N i : ℕ)
    (hi : i ≤ N) (hw : ∀ j < N, w j ≠ 0) (hb : b N = 0) :
    gramAction w (precisionAction w b) N i = b i := by
  rw [gramAction_precisionAction_boundary w b N i hi hw, hb, sub_zero]

theorem precisionAction_zero (w b : ℕ → ℝ) :
    precisionAction w b 0 = (b 0 - b 1) / w 0 := by
  simp [precisionAction, precisionLevel]

/-- Interior precision rows have exactly three neighboring coordinates. -/
theorem precisionAction_tridiagonal (w b : ℕ → ℝ) (i : ℕ) :
    precisionAction w b (i + 1) =
      -b i / w i + (1 / w i + 1 / w (i + 1)) * b (i + 1) -
        b (i + 2) / w (i + 1) := by
  simp only [precisionAction, precisionLevel]
  ring

end RiemannResearch.LinearAlgebra.CumulativeCellEnergy
