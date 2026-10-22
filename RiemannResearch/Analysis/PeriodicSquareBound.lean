import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Real.Basic

/-! A finite uniform bound for the squared error of a periodic sequence. -/
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- Each squared error is bounded by the sum over one complete period.
The sequence is an abstract parameter, so elaboration does not unfold any
arithmetic witness used later in applications. -/
theorem periodic_square_error_bound (F : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hp : Function.Periodic F M) (k : ℕ) :
    (1-F k)^2 ≤ ∑ r : Fin M, (1-F r.val)^2 := by
  rw [← hp.map_mod_nat k]
  let r : Fin M := ⟨k % M, Nat.mod_lt k hM⟩
  exact Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) =>
    sq_nonneg (1-F i.val)) (Finset.mem_univ r)

end RiemannResearch.Analysis
